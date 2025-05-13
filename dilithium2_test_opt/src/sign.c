#include <stdint.h>
#include "params.h"
#include "sign.h"
#include "packing.h"
#include "polyvec.h"
#include "poly.h"
#include "randombytes.h"
#include "symmetric.h"
#include "fips202.h"

static polyvecl precomputed_s1;
static polyveck precomputed_s2, precomputed_t0;
static polyvecl precomputed_mat[K];

/*************************************************
* Inline & Unrolled Fonksiyonlar
**************************************************/
/*static inline void poly_add(poly *r, const poly *a, const poly *b) {
  int i;
  for (i = 0; i < N; i += 8) {
    r->coeffs[i]   = a->coeffs[i]   + b->coeffs[i];
    r->coeffs[i+1] = a->coeffs[i+1] + b->coeffs[i+1];
    r->coeffs[i+2] = a->coeffs[i+2] + b->coeffs[i+2];
    r->coeffs[i+3] = a->coeffs[i+3] + b->coeffs[i+3];
    r->coeffs[i+4] = a->coeffs[i+4] + b->coeffs[i+4];
    r->coeffs[i+5] = a->coeffs[i+5] + b->coeffs[i+5];
    r->coeffs[i+6] = a->coeffs[i+6] + b->coeffs[i+6];
    r->coeffs[i+7] = a->coeffs[i+7] + b->coeffs[i+7];
  }
  // Kalan katsayılar (N % 8 != 0 ise)
  for (; i < N; ++i) {
    r->coeffs[i] = a->coeffs[i] + b->coeffs[i];
  }
}*/

static inline void poly_freeze(poly *a) {
  for (int i = 0; i < N; ++i) {
    a->coeffs[i] = a->coeffs[i] % Q;
  }
}

/*************************************************
* Name:        crypto_sign_keypair
*
* Description: Generates public and private key.
*
* Arguments:   - uint8_t *pk: pointer to output public key (allocated
*                             array of CRYPTO_PUBLICKEYBYTES bytes)
*              - uint8_t *sk: pointer to output private key (allocated
*                             array of CRYPTO_SECRETKEYBYTES bytes)
*
* Returns 0 (success)
**************************************************/

int crypto_sign_keypair(uint8_t *pk, uint8_t *sk) {
  uint8_t seedbuf[2*SEEDBYTES + CRHBYTES];
  uint8_t tr[TRBYTES];
  const uint8_t *rho, *rhoprime, *key;
  polyvecl s1, s1hat;
  polyveck s2, t1, t0;

  /* Get randomness for rho, rhoprime and key */
  randombytes(seedbuf, SEEDBYTES);
  seedbuf[SEEDBYTES+0] = K;
  seedbuf[SEEDBYTES+1] = L;
  shake256(seedbuf, 2*SEEDBYTES + CRHBYTES, seedbuf, SEEDBYTES+2);
  rho = seedbuf;
  rhoprime = rho + SEEDBYTES;
  key = rhoprime + CRHBYTES;

  /* Expand matrix ve ön hesaplama (Senaryo-2) */
  polyvec_matrix_expand(precomputed_mat, rho);

  /* Sample short vectors s1 ve s2 */
  polyvecl_uniform_eta(&s1, rhoprime, 0);
  polyveck_uniform_eta(&s2, rhoprime, L);

  /* Matrix-vector multiplication */
  s1hat = s1;
  polyvecl_ntt(&s1hat);
  polyvec_matrix_pointwise_montgomery(&t1, precomputed_mat, &s1hat);
  polyveck_reduce(&t1);
  polyveck_invntt_tomont(&t1);

  /* Add error vector s2 */
  polyveck_add(&t1, &t1, &s2);

  /* Extract t1 ve public key yaz */
  polyveck_caddq(&t1);
  polyveck_power2round(&t1, &t0, &t1);
  pack_pk(pk, rho, &t1);

  /* Compute H(rho, t1) ve secret key yaz */
  shake256(tr, TRBYTES, pk, CRYPTO_PUBLICKEYBYTES);
  pack_sk(sk, rho, tr, key, &t0, &s1, &s2);

  /* Önceden hesaplanmış değerleri sakla (Senaryo-2) */
  precomputed_s1 = s1;
  precomputed_s2 = s2;
  precomputed_t0 = t0;

  return 0;
}

/*************************************************
* Name:        crypto_sign_signature_internal
*
* Description: Computes signature. Internal API.
*
* Arguments:   - uint8_t *sig:   pointer to output signature (of length CRYPTO_BYTES)
*              - size_t *siglen: pointer to output length of signature
*              - uint8_t *m:     pointer to message to be signed
*              - size_t mlen:    length of message
*              - uint8_t *pre:   pointer to prefix string
*              - size_t prelen:  length of prefix string
*              - uint8_t *rnd:   pointer to random seed
*              - uint8_t *sk:    pointer to bit-packed secret key
*
* Returns 0 (success)
**************************************************/

int crypto_sign_signature_internal(uint8_t *sig,
                                   size_t *siglen,
                                   const uint8_t *m,
                                   size_t mlen,
                                   const uint8_t *pre,
                                   size_t prelen,
                                   const uint8_t rnd[RNDBYTES],
                                   const uint8_t *sk)
{
  unsigned int n;
  uint8_t seedbuf[2*SEEDBYTES + TRBYTES + 2*CRHBYTES];
  uint8_t *rho, *tr, *key, *mu, *rhoprime;
  uint16_t nonce = 0;
  polyvecl mat[K], s1, y, z;
  polyveck t0, s2, w1, w0, h;
  poly cp;
  keccak_state state;

  rho = seedbuf;
  tr = rho + SEEDBYTES;
  key = tr + TRBYTES;
  mu = key + SEEDBYTES;
  rhoprime = mu + CRHBYTES;
  unpack_sk(rho, tr, key, &t0, &s1, &s2, sk);

  /* Compute mu = CRH(tr, pre, msg) */
  shake256_init(&state);
  shake256_absorb(&state, tr, TRBYTES);
  shake256_absorb(&state, pre, prelen);
  shake256_absorb(&state, m, mlen);
  shake256_finalize(&state);
  shake256_squeeze(mu, CRHBYTES, &state);

  /* Compute rhoprime = CRH(key, rnd, mu) */
  shake256_init(&state);
  shake256_absorb(&state, key, SEEDBYTES);
  shake256_absorb(&state, rnd, RNDBYTES);
  shake256_absorb(&state, mu, CRHBYTES);
  shake256_finalize(&state);
  shake256_squeeze(rhoprime, CRHBYTES, &state);

  /* Expand matrix and transform vectors */
  polyvec_matrix_expand(mat, rho);
  polyvecl_ntt(&s1);
  polyveck_ntt(&s2);
  polyveck_ntt(&t0);

rej:
  /* Sample intermediate vector y */
  polyvecl_uniform_gamma1(&y, rhoprime, nonce++);

  /* Matrix-vector multiplication */
  z = y;
  polyvecl_ntt(&z);
  polyvec_matrix_pointwise_montgomery(&w1, mat, &z);
  polyveck_reduce(&w1);
  polyveck_invntt_tomont(&w1);

  /* Decompose w and call the random oracle */
  polyveck_caddq(&w1);
  polyveck_decompose(&w1, &w0, &w1);
  polyveck_pack_w1(sig, &w1);

  shake256_init(&state);
  shake256_absorb(&state, mu, CRHBYTES);
  shake256_absorb(&state, sig, K*POLYW1_PACKEDBYTES);
  shake256_finalize(&state);
  shake256_squeeze(sig, CTILDEBYTES, &state);
  poly_challenge(&cp, sig);
  poly_ntt(&cp);

  /* Compute z, reject if it reveals secret (Early-Eval Optimized) */
  polyvecl_pointwise_poly_montgomery(&z, &cp, &s1);
  polyvecl_invntt_tomont(&z);
  polyvecl_add(&z, &z, &y);
  polyvecl_reduce(&z);
  
  int reject = 0;
  for (int i = 0; i < L; ++i) {
    if (poly_chknorm(&z.vec[i], GAMMA1 - BETA) > 0) {
      reject = 1;
      break;
    }
  }
  if (reject) goto rej;

  /* Check subtracting cs2 (Early-Eval Optimized) */
  polyveck_pointwise_poly_montgomery(&h, &cp, &s2);
  polyveck_invntt_tomont(&h);
  polyveck_sub(&w0, &w0, &h);
  polyveck_reduce(&w0);
  
  reject = 0;
  for (int i = 0; i < K; ++i) {
    if (poly_chknorm(&w0.vec[i], GAMMA2 - BETA) > 0) {
      reject = 1;
      break;
    }
  }
  if (reject) goto rej;

  /* Compute hints for w1 (Early-Eval Optimized) */
  polyveck_pointwise_poly_montgomery(&h, &cp, &t0);
  polyveck_invntt_tomont(&h);
  polyveck_reduce(&h);
  
  reject = 0;
  for (int i = 0; i < K; ++i) {
    if (poly_chknorm(&h.vec[i], GAMMA2) > 0) {
      reject = 1;
      break;
    }
  }
  if (reject) goto rej;

  polyveck_add(&w0, &w0, &h);
  n = polyveck_make_hint(&h, &w0, &w1);
  if(n > OMEGA) goto rej;

  /* Write signature */
  pack_sig(sig, sig, &z, &h);
  *siglen = CRYPTO_BYTES;
  return 0;
}


/*************************************************
* Name:        crypto_sign_signature
*
* Description: Computes signature.
*
* Arguments:   - uint8_t *sig:   pointer to output signature (of length CRYPTO_BYTES)
*              - size_t *siglen: pointer to output length of signature
*              - uint8_t *m:     pointer to message to be signed
*              - size_t mlen:    length of message
*              - uint8_t *ctx:   pointer to contex string
*              - size_t ctxlen:  length of contex string
*              - uint8_t *sk:    pointer to bit-packed secret key
*
* Returns 0 (success) or -1 (context string too long)
**************************************************/
int crypto_sign_signature(uint8_t *sig,
                          size_t *siglen,
                          const uint8_t *m,
                          size_t mlen,
                          const uint8_t *ctx,
                          size_t ctxlen,
                          const uint8_t *sk)
{
  size_t i;
  uint8_t pre[257];
  uint8_t rnd[RNDBYTES];

  if(ctxlen > 255)
    return -1;

  /* Prepare pre = (0, ctxlen, ctx) */
  pre[0] = 0;
  pre[1] = ctxlen;
  for(i = 0; i < ctxlen; i++)
    pre[2 + i] = ctx[i];

#ifdef DILITHIUM_RANDOMIZED_SIGNING
  randombytes(rnd, RNDBYTES);
#else
  for(i=0;i<RNDBYTES;i++)
    rnd[i] = 0;
#endif

  crypto_sign_signature_internal(sig,siglen,m,mlen,pre,2+ctxlen,rnd,sk);
  return 0;
}

/*************************************************
* Name:        crypto_sign
*
* Description: Compute signed message.
*
* Arguments:   - uint8_t *sm: pointer to output signed message (allocated
*                             array with CRYPTO_BYTES + mlen bytes),
*                             can be equal to m
*              - size_t *smlen: pointer to output length of signed
*                               message
*              - const uint8_t *m: pointer to message to be signed
*              - size_t mlen: length of message
*              - const uint8_t *ctx: pointer to context string
*              - size_t ctxlen: length of context string
*              - const uint8_t *sk: pointer to bit-packed secret key
*
* Returns 0 (success) or -1 (context string too long)
**************************************************/
int crypto_sign(uint8_t *sm,
                size_t *smlen,
                const uint8_t *m,
                size_t mlen,
                const uint8_t *ctx,
                size_t ctxlen,
                const uint8_t *sk)
{
  int ret;
  size_t i;

  for(i = 0; i < mlen; ++i)
    sm[CRYPTO_BYTES + mlen - 1 - i] = m[mlen - 1 - i];
  ret = crypto_sign_signature(sm, smlen, sm + CRYPTO_BYTES, mlen, ctx, ctxlen, sk);
  *smlen += mlen;
  return ret;
}

/*************************************************
* Name:        crypto_sign_verify_internal
*
* Description: Verifies signature. Internal API.
*
* Arguments:   - uint8_t *m: pointer to input signature
*              - size_t siglen: length of signature
*              - const uint8_t *m: pointer to message
*              - size_t mlen: length of message
*              - const uint8_t *pre: pointer to prefix string
*              - size_t prelen: length of prefix string
*              - const uint8_t *pk: pointer to bit-packed public key
*
* Returns 0 if signature could be verified correctly and -1 otherwise
**************************************************/
int crypto_sign_verify_internal(const uint8_t *sig,
                                size_t siglen,
                                const uint8_t *m,
                                size_t mlen,
                                const uint8_t *pre,
                                size_t prelen,
                                const uint8_t *pk)
{
  unsigned int i;
  uint8_t buf[K*POLYW1_PACKEDBYTES];
  uint8_t rho[SEEDBYTES];
  uint8_t mu[CRHBYTES];
  uint8_t c[CTILDEBYTES];
  uint8_t c2[CTILDEBYTES];
  poly cp;
  polyvecl mat[K], z;
  polyveck t1, w1, h;
  keccak_state state;

  if(siglen != CRYPTO_BYTES)
    return -1;

  unpack_pk(rho, &t1, pk);
  if(unpack_sig(c, &z, &h, sig))
    return -1;
  if(polyvecl_chknorm(&z, GAMMA1 - BETA))
    return -1;

  /* Compute CRH(H(rho, t1), pre, msg) */
  shake256(mu, TRBYTES, pk, CRYPTO_PUBLICKEYBYTES);
  shake256_init(&state);
  shake256_absorb(&state, mu, TRBYTES);
  shake256_absorb(&state, pre, prelen);
  shake256_absorb(&state, m, mlen);
  shake256_finalize(&state);
  shake256_squeeze(mu, CRHBYTES, &state);

  /* Matrix-vector multiplication; compute Az - c2^dt1 */
  poly_challenge(&cp, c);
  polyvec_matrix_expand(mat, rho);

  polyvecl_ntt(&z);
  polyvec_matrix_pointwise_montgomery(&w1, mat, &z);

  poly_ntt(&cp);
  polyveck_shiftl(&t1);
  polyveck_ntt(&t1);
  polyveck_pointwise_poly_montgomery(&t1, &cp, &t1);

  polyveck_sub(&w1, &w1, &t1);
  polyveck_reduce(&w1);
  polyveck_invntt_tomont(&w1);

  /* Reconstruct w1 */
  polyveck_caddq(&w1);
  polyveck_use_hint(&w1, &w1, &h);
  polyveck_pack_w1(buf, &w1);

  /* Call random oracle and verify challenge */
  shake256_init(&state);
  shake256_absorb(&state, mu, CRHBYTES);
  shake256_absorb(&state, buf, K*POLYW1_PACKEDBYTES);
  shake256_finalize(&state);
  shake256_squeeze(c2, CTILDEBYTES, &state);
  for(i = 0; i < CTILDEBYTES; ++i)
    if(c[i] != c2[i])
      return -1;

  return 0;
}

/*************************************************
* Name:        crypto_sign_verify
*
* Description: Verifies signature.
*
* Arguments:   - uint8_t *m: pointer to input signature
*              - size_t siglen: length of signature
*              - const uint8_t *m: pointer to message
*              - size_t mlen: length of message
*              - const uint8_t *ctx: pointer to context string
*              - size_t ctxlen: length of context string
*              - const uint8_t *pk: pointer to bit-packed public key
*
* Returns 0 if signature could be verified correctly and -1 otherwise
**************************************************/
int crypto_sign_verify(const uint8_t *sig,
                       size_t siglen,
                       const uint8_t *m,
                       size_t mlen,
                       const uint8_t *ctx,
                       size_t ctxlen,
                       const uint8_t *pk)
{
  size_t i;
  uint8_t pre[257];

  if(ctxlen > 255)
    return -1;

  pre[0] = 0;
  pre[1] = ctxlen;
  for(i = 0; i < ctxlen; i++)
    pre[2 + i] = ctx[i];

  return crypto_sign_verify_internal(sig,siglen,m,mlen,pre,2+ctxlen,pk);
}

/*************************************************
* Name:        crypto_sign_open
*
* Description: Verify signed message.
*
* Arguments:   - uint8_t *m: pointer to output message (allocated
*                            array with smlen bytes), can be equal to sm
*              - size_t *mlen: pointer to output length of message
*              - const uint8_t *sm: pointer to signed message
*              - size_t smlen: length of signed message
*              - const uint8_t *ctx: pointer to context tring
*              - size_t ctxlen: length of context string
*              - const uint8_t *pk: pointer to bit-packed public key
*
* Returns 0 if signed message could be verified correctly and -1 otherwise
**************************************************/
int crypto_sign_open(uint8_t *m,
                     size_t *mlen,
                     const uint8_t *sm,
                     size_t smlen,
                     const uint8_t *ctx,
                     size_t ctxlen,
                     const uint8_t *pk)
{
  size_t i;

  if(smlen < CRYPTO_BYTES)
    goto badsig;

  *mlen = smlen - CRYPTO_BYTES;
  if(crypto_sign_verify(sm, CRYPTO_BYTES, sm + CRYPTO_BYTES, *mlen, ctx, ctxlen, pk))
    goto badsig;
  else {
    /* All good, copy msg, return 0 */
    for(i = 0; i < *mlen; ++i)
      m[i] = sm[CRYPTO_BYTES + i];
    return 0;
  }

badsig:
  /* Signature verification failed */
  *mlen = 0;
  for(i = 0; i < smlen; ++i)
    m[i] = 0;

  return -1;
}
