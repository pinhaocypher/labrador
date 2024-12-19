#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdio.h>
#include "randombytes.h"
#include "malloc.h"
#include "aesctr.h"
#include "fips202.h"
#include "data.h"
#include "poly.h"
#include "polx.h"
#include "polz.h"
#include "sparsemat.h"
#include "jlproj.h"
#include "labrador.h"

size_t comkey_len = 0;
// polx is a polynomial extension, can use NTT to speed up
// typedef struct {
//   poly vec[K];
// } polx;
// K is determined by data.h
polx *comkey = NULL;

//TODO: not figure out 
// triangular matrix 
// used to efficiently store symmetric matrix
// i, j are indices of the matrix
// r is the rank of the matrix
static size_t triangularidx(size_t i,size_t j,size_t r) {
  if(i>j) {  // swap
    j ^= i;
    i ^= j;
    j ^= i;
  }
  i = i*r - (i*i+i)/2 + j;
  return i;
}

// short integer solution secure
// TODO: 
// 1. Why maxlog is 2*sqrt(LOGQ*LOGDELTA*N)*sqrt(rank)?
// 2. And why this is secure?
int sis_secure(size_t rank, double norm) {
  double maxlog;

  maxlog = 2*sqrt(LOGQ*LOGDELTA*N)*sqrt(rank);
  maxlog = MIN(LOGQ,maxlog);
  if(log2(norm) < maxlog)
    return 1;
  else
    return 0;
}

/**
 * Initialize or extend the commitment key to the specified length.
 * The commitment key is used for ajtai commitment and is stored in chunks
 * of 32 polynomial vectors.
 *
 * @param target_length The desired length of the commitment key
 */
void init_comkey(size_t target_length) {
    /* If current length is sufficient, no action needed */
    if (comkey_len >= target_length) {
        return;
    }

    /* Calculate number of 32-polynomial chunks needed */
    size_t num_chunks = (target_length + 31) / 32;
    
    /* Allocate new buffer with 64-byte alignment for optimal performance */
    __attribute__((aligned(16))) uint8_t random_seed[16] = {};
    polx* new_buffer = _aligned_alloc(64, num_chunks * 32 * sizeof(polx));

    /* Copy existing commitment key if it exists */
    if (comkey_len) {
        polxvec_copy(new_buffer, comkey, comkey_len);
    }
    free(comkey);
    comkey = new_buffer;

    /* Generate new polynomial vectors using almost uniform distribution */
    for (size_t chunk_idx = comkey_len/32; chunk_idx < num_chunks; chunk_idx++) {
        polxvec_almostuniform(&comkey[32 * chunk_idx], 32, random_seed, chunk_idx);
    }

    comkey_len = num_chunks * 32;
}

void free_comkey(void) {
  free(comkey);
  comkey = NULL;
  comkey_len = 0;
}

/**
 * Initialize proof parameters for labrador proof.
 * This function sets up various parameters needed for generating proofs,
 * including commitment ranks, decomposition parameters, and security checks.
 *
 * @param pi         Pointer to proof structure to initialize
 * @param wt         Pointer to witness structure containing input parameters
 * @param quadratic  Type of proof (0: constant, 1: liear, 2: quadratic)
 * @param tail       Flag indicating if tail recursion optimization should be used
 * @return          0 on success, error code on failure
 */
int init_proof(proof *pi, const witness *wt, int quadratic, int tail) {
    /* Parameter initialization */
    comparams *cpp = pi->cpp;
    size_t proof_rank = (quadratic == 2) ? 2 * wt->r + 1 : wt->r;
    pi->r = proof_rank;
    pi->tail = tail;

    /* Allocate memory for norm squares and dimension arrays */
    uint64_t normsq[proof_rank];
    void *memory_buffer = _malloc(2 * proof_rank * sizeof(size_t));
    pi->n = (size_t*)memory_buffer;
    pi->nu = (size_t*)&pi->n[proof_rank];

    /* Initialize dimensions and norms based on proof type */
    if (quadratic == 2) {
        init_double_quadratic_params(pi, wt, normsq);
    } else {
        init_linear_or_simple_quadratic_params(pi, wt, normsq, quadratic);
    }

    /* Find optimal decomposition parameters */
    for (int k = 15; k > 0; k--) {
        size_t max_dimension = compute_rank_decomposition(pi);
        size_t total_rank = compute_total_rank(pi);
        
        /* Calculate variance and determine decomposition strategy */
        double variance_z = compute_variance_z(pi, normsq, max_dimension);
        bool needs_decomposition = should_decompose(variance_z, tail);
        
        if (needs_decomposition) {
            cpp->f = 2;
            cpp->b = round((log2(12) + log2(variance_z)) / 4);  // log2(sqrt(12*var))
        } else {
            cpp->f = 1;
            cpp->b = round((log2(12) + log2(variance_z)) / 2);
        }

        /* Set uniform decomposition parameters */
        if (!tail) {
            cpp->fu = (LOGQ + 2 * cpp->b / 3) / cpp->b;  // t_1
            cpp->bu = (LOGQ + cpp->fu / 2) / cpp->fu;    // b_1
        } else {
            cpp->fu = 1;
            cpp->bu = LOGQ;
        }

        /* Configure quadratic garbage parameters */
        configure_quadratic_params(cpp, pi, normsq, quadratic, tail, max_dimension);

        /* Find secure commitment ranks */
        if (!find_secure_commitment_ranks(pi, cpp, total_rank, variance_z, tail, quadratic)) {
            break;
        }
    }

    /* Allocate memory for proof vectors */
    void *proof_buffer = _aligned_alloc(64, (cpp->u1len + cpp->u2len + LIFTS) * sizeof(polz));
    pi->u1 = (polz*)proof_buffer;
    pi->u2 = (polz*)&pi->u1[cpp->u1len];
    pi->bb = (polz*)&pi->u2[cpp->u2len];

    /* Validate security parameters */
    if (cpp->kappa > 32) {
        fprintf(stderr, "ERROR in init_proof(): Cannot make inner commitments secure!\n");
        free_proof(pi);
        return 1;
    }
    if (cpp->kappa1 > 32) {
        fprintf(stderr, "ERROR in init_proof(): Cannot make outer commitments secure!\n");
        free_proof(pi);
        return 2;
    }

    return 0;
}

/**
 * Initialize parameters for double quadratic proofs (quadratic == 2)
 */
static void init_double_quadratic_params(proof *pi, const witness *wt, uint64_t *normsq) {
    for (size_t i = 0; i < wt->r; i++) {
        /* Set dimensions */
        pi->n[i] = wt->n[i];
        pi->n[wt->r + 1 + i] = wt->n[i];  // sigmam1 / flip
        
        /* Set norm squares */
        normsq[i] = wt->normsq[i];
        normsq[wt->r + 1 + i] = (TAU1 + 4 * TAU2) * wt->normsq[i];
    }
    
    /* Set Zq to Rq lifting parameters */
    pi->n[wt->r] = (LOGQ + 9) / 10 * wt->r;
    normsq[wt->r] = ldexp(1, 20) / 12 * pi->n[wt->r] * N;

    /* Initialize nu array */
    for (size_t i = 0; i < pi->r; i++) {
        pi->nu[i] = 0;
    }
    pi->nu[wt->r - 1] = -(size_t)1;
    pi->nu[wt->r] = -(size_t)1;
    pi->nu[2 * wt->r] = -(size_t)1;
}

/**
 * Initialize parameters for linear (quadratic == 0) or simple quadratic (quadratic == 1) proofs
 */
static void init_linear_or_simple_quadratic_params(proof *pi, const witness *wt, uint64_t *normsq, int quadratic) {
    for (size_t i = 0; i < pi->r; i++) {
        pi->n[i] = wt->n[i];
        normsq[i] = wt->normsq[i];
        pi->nu[i] = quadratic ? -(size_t)1 : 0;
    }
    pi->nu[pi->r - 1] = -(size_t)1;
}

/**
 * Compute rank decomposition and return maximum dimension
 */
static size_t compute_rank_decomposition(proof *pi) {
    size_t max_dimension = 0;
    size_t total = 0;
    
    for (size_t i = 0; i < pi->r; i++) {
        total += pi->n[i];
        if (pi->nu[i]) {
            pi->nu[i] = total;
            max_dimension = MAX(max_dimension, total);
            total = 0;
        }
    }
    
    return max_dimension;
}

/**
 * Compute total rank from nu array
 */
static size_t compute_total_rank(proof *pi) {
    size_t total_rank = 0;
    for (size_t i = 0; i < pi->r; i++) {
        if (pi->nu[i]) {
            total_rank++;
        }
    }
    return total_rank;
}

/**
 * Compute variance Z parameter
 */
static double compute_variance_z(const proof *pi, const uint64_t *normsq, size_t max_dimension) {
    double variance = 0;
    for (size_t i = 0; i < pi->r; i++) {
        variance += normsq[i];
    }
    variance /= max_dimension * N;
    variance *= TAU1 + 4 * TAU2;
    return variance;
}

/**
 * Determine if decomposition is needed based on variance and security parameters
 */
static bool should_decompose(double variance_z, int tail) {
    if (tail) {
        return false;
    }
    bool security_requires_decomp = !sis_secure(13, 6 * T * SLACK * sqrt(2 * (TAU1 + 4 * TAU2) * variance_z));
    bool variance_requires_decomp = 64 * variance_z > (1 << 28);
    return security_requires_decomp || variance_requires_decomp;
}

/**
 * Configure quadratic garbage parameters
 */
static void configure_quadratic_params(comparams *cpp, const proof *pi, const uint64_t *normsq,
                                     int quadratic, int tail, size_t max_dimension) {
    cpp->bg = cpp->b;
    
    if (!quadratic) {
        cpp->fg = 0;
        return;
    }
    
    if (tail) {
        cpp->fg = 1;
        return;
    }
    
    double max_variance = compute_max_quadratic_variance(pi, normsq, max_dimension);
    cpp->fg = ceil((log2(12) + log2(max_variance)) / (2 * cpp->b));
    cpp->fg = MAX(1, cpp->fg);
}

/**
 * Find secure commitment ranks
 * Returns true if parameters need to be adjusted, false if secure parameters found
 */
static bool find_secure_commitment_ranks(proof *pi, comparams *cpp, size_t total_rank,
                                       double variance_z, int tail, int quadratic) {
    /* Find secure inner commitment rank */
    for (cpp->kappa = 1; cpp->kappa <= 32; cpp->kappa++) {
        compute_proof_norm_square(pi, cpp, total_rank, variance_z, tail, quadratic);
        
        if (sis_secure(cpp->kappa, 6 * T * SLACK * ldexp(1, (cpp->f - 1) * cpp->b) * sqrt(pi->normsq))) {
            break;
        }
    }

    if (tail) {
        return configure_tail_parameters(cpp, total_rank, variance_z);
    } else {
        return configure_non_tail_parameters(cpp, pi, total_rank);
    }
}

void free_proof(proof *pi) {
  free(pi->n);  // one buffer for n,nu
  free(pi->u1);  // one buffer for u1,u2,bb
  pi->n = NULL;
  pi->u1 = NULL;
}

void init_constraint_raw(constraint *cnst, size_t r, size_t n, size_t deg, int quadratic) {
  size_t len;
  void *buf;

  cnst->deg = deg;

  buf = _aligned_alloc(64,r*extlen(n,deg)*sizeof(polx));
  cnst->phi = (polx*)buf;
  buf = _aligned_alloc(64,deg*sizeof(polx));
  cnst->b = (polx*)buf;

  cnst->a->len = 0;
  if(quadratic) {
    len = (r*r+r)/2;
    buf = _malloc(2*len*sizeof(size_t));
    cnst->a->rows = (size_t*)buf;
    cnst->a->cols = &cnst->a->rows[len];

    buf = _aligned_alloc(64,extlen(len,deg)*sizeof(polx));
    cnst->a->coeffs = (polx*)buf;
  }
  else {
    cnst->a->rows = NULL;
    cnst->a->cols = NULL;
    cnst->a->coeffs = NULL;
  }
}

void init_constraint(constraint *cnst, const statement *st) {
  init_constraint_raw(cnst,st->r,st->n,1,st->cpp->fg != 0);
}

void free_constraint(constraint *cnst) {
  free(cnst->phi);  // one buffer for phi (will be realloced)
  free(cnst->b);  // one buffer for b
  free(cnst->a->rows);  // one buffer for rows,cols
  free(cnst->a->coeffs);  // one buffer for coeffs (will be realloced)
  cnst->phi = cnst->b = cnst->a->coeffs = NULL;
  cnst->a->rows = NULL;
}

void init_statement(statement *st, const proof *pi, const uint8_t h[16]) {
  size_t i;
  size_t nn;
  void *buf;

  st->cpp = pi->cpp;
  st->tail = pi->tail;

  st->r = 0;
  for(i=0;i<pi->r;i++)
    st->r += pi->nu[i];

  nn = st->n = 0;
  for(i=0;i<pi->r;i++) {
    nn += pi->n[i];
    if(!pi->nu[i]) continue;
    nn = (nn+pi->nu[i]-1)/pi->nu[i];
    st->n = MAX(st->n,nn);
    nn = 0;
  }

  st->m  = st->r * st->cpp->fu * st->cpp->kappa;  // inner commitments
  st->m += (st->cpp->fu + st->cpp->fg)*(st->r*st->r + st->r)/2;  // garbage

  buf = _aligned_alloc(64,(st->cpp->u1len + st->cpp->u2len + st->r)*sizeof(polx));
  st->u1 = (polx*)buf;
  st->u2 = &st->u1[st->cpp->u1len];
  st->c = &st->u2[st->cpp->u2len];

  nn = st->r*extlen(st->cpp->fu*st->cpp->kappa,st->cpp->kappa1);
  nn += st->cpp->fg*(st->r*st->r + st->r)/2;
  nn = MAX(nn,st->cpp->fu*(st->r*st->r + st->r)/2);
  nn = MAX(nn,st->n);
  init_comkey(nn);
  init_constraint(st->cnst,st);
  memcpy(st->h,h,16);
}

void free_statement(statement *st) {
  free(st->u1);  // one buffer for u1,u2,c,b
  free_constraint(st->cnst);
  st->u1 = NULL;
}

void init_witness_raw(witness *wt, size_t r, const size_t n[r]) {
  size_t i, len;
  void *buf;

  wt->r = r;

  buf = _malloc(r*(sizeof(size_t) + sizeof(uint64_t) + sizeof(poly*)));
  wt->n = (size_t*)buf;
  wt->normsq = (uint64_t*)&wt->n[r];
  wt->s = (poly**)&wt->normsq[r];

  len = 0;
  for(i=0;i<r;i++) {
    wt->n[i] = n[i];
    len += n[i];
  }

  buf = _aligned_alloc(64,len*sizeof(poly));
  for(i=0;i<r;i++) {
    wt->s[i] = (poly*)buf;
    buf = (poly*)buf + n[i];
  }
}

void init_witness(witness *wt, const statement *st) {
  size_t i;
  const size_t r = st->cpp->f + !st->tail;
  size_t n[r];

  for(i=0;i<st->cpp->f;i++)
    n[i] = st->n;
  if(!st->tail)
    n[st->cpp->f] = st->m;

  init_witness_raw(wt,r,n);
}

void witness_merge(witness *wt1, const witness *wt2) {
  size_t i;
  void *buf;
  witness tmp[1];

  tmp->r = wt1->r + wt2->r;

  buf = _malloc(tmp->r*(sizeof(size_t) + sizeof(uint64_t) + sizeof(poly*)));
  tmp->n = (size_t*)buf;
  tmp->normsq = (uint64_t*)&tmp->n[tmp->r];
  tmp->s = (poly**)&tmp->normsq[tmp->r];

  for(i=0;i<wt1->r;i++) {
    tmp->n[i] = wt1->n[i];
    tmp->normsq[i] = wt1->normsq[i];
    tmp->s[i] = wt1->s[i];
  }
  for(i=0;i<wt2->r;i++) {
    tmp->n[wt1->r+i] = wt2->n[i];
    tmp->normsq[wt1->r+i] = wt2->normsq[i];
    tmp->s[wt1->r+i] = wt2->s[i];
  }

  free(wt1->n);
  *wt1 = *tmp;
}

int set_witness_vector_raw(witness *wt, size_t i, size_t n, size_t deg, const int64_t s[n*deg*N]) {
  if(i >= wt->r) {
    fprintf(stderr,"ERROR in set_witness_vector_raw(): Witness vector %zu does not exist\n",i);
    return 1;
  }
  if(n*deg != wt->n[i]) {
    fprintf(stderr,"ERROR in set_witness_vector_raw(): Mismatch of witness vector length\n");
    return 2;
  }

  polyvec_fromint64vec(wt->s[i],n,deg,s);
  wt->normsq[i] = polyvec_sprodz(wt->s[i],wt->s[i],n*deg);
  return 0;
}

void free_witness(witness *wt) {
  if(!wt->n) return;
  free(wt->s[0]);  // one buffer for *s
  free(wt->n);  // one buffer for n,s,normsq
  wt->n = NULL;
}

double print_proof_pp(const proof *pi) {
  size_t i;
  double s;
  const comparams *cpp = pi->cpp;

  printf("Proof:\n");
  printf("  Witness multiplicity: %zu\n",pi->r);
  printf("  Witness ranks: ");
  for(i=0;i<MIN(pi->r,10);i++) {
    printf("%zu",pi->n[i]);
    if(i<pi->r-1) printf(", ");
  }
  printf("\n");
  printf("  Witness decomposition: ");
  for(i=0;i<MIN(pi->r,10);i++) {
    printf("%zu",pi->nu[i]);
    if(i<pi->r-1) printf(", ");
  }
  printf("\n");

  printf("  Johnson-Lindenstrauss projection matrix nonce: %zu\n",pi->jlnonce);
  s = sqrt(jlproj_normsq(pi->p));
  printf("  Projection norm: %.2f\n",s);
  printf("  Commitment ranks: kappa = %zu; kappa1 = %zu\n",cpp->kappa,cpp->kappa1);
  printf("  Decomposition bases: b = %llu; bu = %llu; bg = %llu\n",1ULL << cpp->b,1ULL << cpp->bu,1ULL << cpp->bg);
  printf("  Expansion factors: f = %zu; fu = %zu; fg = %zu\n",cpp->f,cpp->fu,cpp->fg);
  s  = (log2(s)-4+2.05)*256;
  s += (cpp->u1len+cpp->u2len+LIFTS)*N*LOGQ;
  s /= 8192;
  printf("  Proof size: %.2f KB\n",s);
  printf("\n");
  return s;
}

void print_statement_pp(const statement *st) {
  size_t i;

  printf("Labrador statement ");
  if(st->tail)
    printf("(tail) ");
  for(i=0;i<5;i++)
    printf("%02hhX",st->h[i]);
  printf(":\n");

  printf("  Total amortized multiplicity: %zu\n",st->r);
  printf("  Rank of amortized opening: %zu\n",st->n);
  printf("  Rank of outer commitment openings (inner coms, garbage): %zu\n",st->m);
  printf("  Number of non-zero coefficients in matrix a for quadratic constraint term: %zu\n",st->cnst->a->len);
  printf("  Norm constraint: %.2f\n",sqrt(st->betasq));
  printf("\n");
}

double print_witness_pp(const witness *wt) {
  size_t i;
  double s;

  printf("Witness:\n");
  printf("  Witness parts: %zu\n",wt->r);
  printf("  Witness part lengths: ");
  for(i=0;i<MIN(wt->r,10);i++) {
    printf("%zu",wt->n[i]);
    if(i<wt->r-1) printf(", ");
  }
  printf("\n");
  printf("  Witness part norms: ");
  for(i=0;i<MIN(wt->r,10);i++) {
    printf("%.2f",sqrt(wt->normsq[i]));
    if(i<wt->r-1) printf(", ");
  }
  printf("\n");

  s = 0;
  for(i=0;i<wt->r;i++)
    s += (log2((double)wt->normsq[i]/(N*wt->n[i]))/2+2.05)*N*wt->n[i];  // FIXME: not necessarily gaussian
  s /= 8192;
  printf("  Witness size: %.2f KB\n",s);
  printf("\n");
  return s;
}

size_t commit_raw(polx *u, poly *t, size_t r, size_t n, const polx s[r][n],
                  size_t off, const comparams *cpp, int tail)
{
  size_t i;
  const size_t l = cpp->fu*cpp->kappa;
  polx tx[l];

  if(tail) {
    for(i=0;i<r;i++)
      polxvec_mul_extension(&u[off+i*l],comkey,s[i],n,cpp->kappa,1);
    return off+r*l;
  }

  for(i=0;i<r;i++) {
    /* inner commitment */
    polxvec_mul_extension(tx,comkey,s[i],n,cpp->kappa,1);
    polxvec_decompose(&t[i*l],tx,cpp->kappa,cpp->fu,cpp->bu);

    /* outer commitment */
    polxvec_frompolyvec(tx,&t[i*l],l);
    off += polxvec_mul_extension(tx,&comkey[off],tx,l,cpp->kappa1,1);
    polxvec_add(u,u,tx,cpp->kappa1);
  }

  return off;
}

size_t qugarbage_raw(polx *u, poly *g, size_t r, size_t n, const polx s[r][n],
                     size_t off, const comparams *cpp, int tail)
{
  size_t i,j,k,l;
  const size_t len = (r*r+r)/2;
  polx buf[MAX(cpp->fg*len,cpp->kappa1)];
  polx *gx = (tail) ? u+off : buf;

  if(!cpp->fg)
    return off;

// garbage polynomial g
  polxvec_setzero(gx,len);
  for(l=0;l<n;l++) {
    k = 0;
    for(i=0;i<r;i++)
      for(j=i;j<r;j++)
        polx_mul_add(&gx[k++],&s[i][l],&s[j][l]);
  }

  if(!tail) {
    polxvec_decompose(g,gx,len,cpp->fg,cpp->bg);
    polxvec_frompolyvec(gx,g,cpp->fg*len);
    off += polxvec_mul_extension(gx,&comkey[off],gx,cpp->fg*len,cpp->kappa1,1);
    polxvec_add(u,u,gx,cpp->kappa1);
  }

  return off;
}

void commit(statement *ost, witness *owt, proof *pi, polx sx[ost->r][ost->n], const witness *iwt) {
  const size_t r = iwt->r;
  const size_t *n = iwt->n;
  const comparams *cpp = ost->cpp;

  /* offsets in aux witness vector v */
  const size_t t = 0;
  const size_t g = t + ost->r*cpp->fu*cpp->kappa;

  size_t i,j,k,l;
  __attribute__((aligned(16)))
  uint8_t hashbuf[16+cpp->u1len*N*QBYTES];
  poly *v = (pi->tail) ? NULL : owt->s[cpp->f];

  polxvec_setzero(ost->u1,cpp->kappa1);

  /* transform and commit to input witness */
  j = k = l = 0;
  for(i=0;i<r;i++) {
    polxvec_frompolyvec(&sx[j][k],iwt->s[i],n[i]);
    k += n[i];
    if(pi->nu[i]) {
      polxvec_setzero(&sx[j][k],pi->nu[i]*ost->n - k);
      l = commit_raw(ost->u1,&v[t+j*cpp->fu*cpp->kappa],pi->nu[i],ost->n,&sx[j],l,cpp,pi->tail);
      j += pi->nu[i];
      k = 0;
    }
  }

  qugarbage_raw(ost->u1,&v[g],ost->r,ost->n,sx,l,cpp,pi->tail);
  polzvec_frompolxvec(pi->u1,ost->u1,cpp->u1len);
  memcpy(hashbuf,ost->h,16);
  polzvec_bitpack(&hashbuf[16],pi->u1,cpp->u1len);
  shake128(ost->h,16,hashbuf,sizeof(hashbuf));
}

void reduce_commit(statement *ost, const proof *pi) {
  __attribute__((aligned(16)))
  uint8_t hashbuf[16+pi->cpp->u1len*N*QBYTES];

  /* first outer commitment resp inner comms + quadratic garbage */
  polzvec_topolxvec(ost->u1,pi->u1,pi->cpp->u1len);
  memcpy(hashbuf,ost->h,16);
  polzvec_bitpack(&hashbuf[16],pi->u1,pi->cpp->u1len);
  shake128(ost->h,16,hashbuf,sizeof(hashbuf));
}

static uint64_t next2power(uint64_t a) {
  a -= 1;
  a |= a >>  1;
  a |= a >>  2;
  a |= a >>  4;
  a |= a >>  8;
  a |= a >> 16;
  a |= a >> 32;
  a += 1;
  return a;
}

int project(statement *ost, proof *pi, uint8_t jlmat[][ost->n][256*N/8], const witness *iwt) {
  const size_t r = iwt->r;
  const size_t *n = iwt->n;

  size_t i,j,k,rep;
  uint64_t normsq = 0, test;
  __attribute__((aligned(16)))
  uint8_t hashbuf[16+1024];
  aes128ctr_ctx aesctx;

  for(i=0;i<r;i++)
    normsq += iwt->normsq[i];
  if(normsq > JLMAXNORMSQ) {
    fprintf(stderr,"ERROR: Total witness norm too big for JL Projection\n");
    return 1;
  }
  test = next2power(4*sqrt(normsq));
  normsq *= 256;
  shake128(hashbuf,32,ost->h,16);
  aes128ctr_init(&aesctx,&hashbuf[16],0);
  pi->jlnonce = 0;
  do {
    aes128ctr_select(&aesctx,++pi->jlnonce);
    memset(pi->p,0,256*sizeof(int32_t));
    j = k = 0;
    for(i=0;i<r;i++) {
      // AES128CTR_BLOCKBYTES = 512
      aes128ctr_squeezeblocks(jlmat[j][k],n[i]*256*N/8/AES128CTR_BLOCKBYTES,&aesctx);
      polyvec_jlproj_add(pi->p,iwt->s[i],n[i],jlmat[j][k]);
      k += n[i];
      if(pi->nu[i]) {
        memset(jlmat[j][k],0,(pi->nu[i]*ost->n-k)*256*N/8);
        j += pi->nu[i];
        k = 0;
      }
    }
    rep = 0;
    for(i=0;i<256;i++)  // TODO: vectorize
      if((uint64_t)labs(pi->p[i]) >= test)
        rep = 1;
  } while(rep || jlproj_normsq(pi->p) > normsq);

  memcpy(&hashbuf[16],pi->p,1024);
  shake128(ost->h,16,hashbuf,16+1024);
  return 0;
}

int reduce_project(statement *ost, uint8_t jlmat[][ost->n][256*N/8], const proof *pi, size_t r, uint64_t betasq) {
  size_t i,j,k;
  __attribute__((aligned(16)))
  uint8_t hashbuf[16+1024];
  aes128ctr_ctx aesctx;

  if(jlproj_normsq(pi->p) > 256*MIN(JLMAXNORMSQ,betasq)) {
    fprintf(stderr,"ERROR in reduce_project(): Witness projection longer than bound\n");
    return 1;
  }

  shake128(hashbuf,32,ost->h,16);
  aes128ctr_init(&aesctx,&hashbuf[16],pi->jlnonce);
  memcpy(&hashbuf[16],pi->p,1024);
  shake128(ost->h,16,hashbuf,sizeof(hashbuf));

  /* JL Matrix */
  j = k = 0;
  for(i=0;i<r;i++) {
    aes128ctr_squeezeblocks(jlmat[j][k],pi->n[i]*256*N/8/AES128CTR_BLOCKBYTES,&aesctx);
    k += pi->n[i];
    if(pi->nu[i]) {
      memset(jlmat[j][k],0,(pi->nu[i]*ost->n-k)*256*N/8);
      j += pi->nu[i];
      k = 0;
    }
  }

  return 0;
}

void collaps_jlproj_raw(constraint *cnst, size_t r, size_t n, uint8_t h[16], const int32_t p[256],
                       const uint8_t jlmat[r][n][256*N/8])
{
  __attribute__((aligned(32)))
  uint8_t hashbuf[32+QBYTES*256+24];  // additional 24 bytes because of vector loads
  int64_t x;

  shake128(hashbuf,sizeof(hashbuf),h,16);
  memcpy(h,hashbuf,16);
  polxvec_jlproj_collapsmat(cnst->phi,**jlmat,r*n,&hashbuf[32]);
  x = jlproj_collapsproj(p,&hashbuf[32]);
  polx_monomial(cnst->b,x,0);
}

void collaps_jlproj(constraint *cnst, statement *st, const proof *pi, const uint8_t jlmat[st->r][st->n][256*N/8]) {
  collaps_jlproj_raw(cnst,st->r,st->n,st->h,pi->p,jlmat);
}

void lift_aggregate_zqcnst(statement *ost, proof *pi, size_t i, constraint *cnst, const polx sx[ost->r][ost->n]) {
  __attribute__((aligned(16)))
  uint8_t hashbuf[16+N*QBYTES];
  polx alpha[1];

  polxvec_sprod(cnst->b,cnst->phi,*sx,ost->r*ost->n);
  polz_frompolx(&pi->bb[i],cnst->b);
  polz_setcoeff_fromint64(&pi->bb[i],0,0);
  memcpy(hashbuf,ost->h,16);
  polz_bitpack(&hashbuf[16],&pi->bb[i]);
  shake128(hashbuf,32,hashbuf,sizeof(hashbuf));
  memcpy(ost->h,hashbuf,16);
  polxvec_quarternary(alpha,1,&hashbuf[16],0);
  if(!i) {
    polxvec_polx_mul(ost->cnst->phi,alpha,cnst->phi,ost->r*ost->n);
    polx_mul(ost->cnst->b,alpha,cnst->b);
    sparsemat_polx_mul(ost->cnst->a,alpha,cnst->a);
  }
  else {
    polxvec_polx_mul_add(ost->cnst->phi,alpha,cnst->phi,ost->r*ost->n);
    polx_mul_add(ost->cnst->b,alpha,cnst->b);
    sparsemat_polx_mul_add(ost->cnst->a,alpha,cnst->a);
  }
}

void reduce_lift_aggregate_zqcnst(statement *ost, const proof *pi, size_t i, const constraint *cnst) {
  __attribute__((aligned(16)))
  uint8_t hashbuf[16+N*QBYTES];
  polz b[1];
  polx alpha[1];
  zz c0[1];

  polz_frompolx(b,cnst->b);
  polz_getcoeff(c0,b,0);
  polzvec_copy(b,&pi->bb[i],1);
  polz_setcoeff(b,c0,0);
  polz_topolx(cnst->b,b);

  memcpy(hashbuf,ost->h,16);
  polzvec_bitpack(&hashbuf[16],&pi->bb[i]);
  shake128(hashbuf,32,hashbuf,sizeof(hashbuf));
  memcpy(ost->h,hashbuf,16);
  polxvec_quarternary(alpha,1,&hashbuf[16],0);
  if(!i) {
    polxvec_polx_mul(ost->cnst->phi,alpha,cnst->phi,ost->r*ost->n);
    polx_mul(ost->cnst->b,alpha,cnst->b);
    sparsemat_polx_mul(ost->cnst->a,alpha,cnst->a);
  }
  else {
    polxvec_polx_mul_add(ost->cnst->phi,alpha,cnst->phi,ost->r*ost->n);
    polx_mul_add(ost->cnst->b,alpha,cnst->b);
    sparsemat_polx_mul_add(ost->cnst->a,alpha,cnst->a);
  }
}

static void aggregate(statement *ost, const proof *pi, const statement *ist) {
  const size_t n = ist->n;
  const size_t m = ist->m;
  const size_t r = ist->r;
  const comparams *cpp = ist->cpp;

  const size_t l = cpp->fu*cpp->kappa;
  /* offsets in aux witness vector v */
  const size_t t = 0;
  const size_t g = t + r*l;
  const size_t h = g + cpp->fg*(r*r+r)/2;

  size_t i,j,k;
  polx *tmp = (polx*)_aligned_alloc(64,MAX(n,m)*sizeof(polx));
  polx (*phi)[ost->n] = (polx(*)[ost->n])ost->cnst->phi;
  j = k = 0;
  for(i=0;i<cpp->f;i++) {
    j += pi->nu[i];
    k  = (pi->nu[i]) ? 0 : k+n;
  }
  polx *phiv = &phi[j][k];

  __attribute__((aligned(16)))
  uint8_t hashbuf[32];
  polx chalbuf[2*cpp->kappa1+cpp->kappa+2];
  const polx *alpha = chalbuf;
  const polx *beta = &alpha[cpp->kappa1];
  const polx *gamma = &beta[cpp->kappa1];
  const polx *delta = &gamma[cpp->kappa];

  shake128(hashbuf,32,ost->h,16);
  memcpy(ost->h,hashbuf,16);
  polxvec_quarternary(chalbuf,sizeof(chalbuf)/sizeof(polx),&hashbuf[16],0);

  /* Bv1 = u1 */
  j = 0;
  for(i=0;i<r;i++)
    j += polxvec_collaps_add_extension(&phiv[t+i*l],alpha,&comkey[j],l,cpp->kappa1,1);
  polxvec_collaps_add_extension(&phiv[g],alpha,&comkey[j],h-g,cpp->kappa1,1);
  polxvec_sprod_add(ost->cnst->b,alpha,ist->u1,cpp->kappa1);

  /* Bv2 = u2 */
  polxvec_collaps_add_extension(&phiv[h],beta,comkey,m-h,cpp->kappa1,1);
  polxvec_sprod_add(ost->cnst->b,beta,ist->u2,cpp->kappa1);

  /*    gamma:         - Az      + \sum_i  c_i t_i                 = 0 */
  /* delta[0]: - <z,z>           + \sum_ij c_i c_j g_ij            = 0 */
  /*        1:         - <phi,z> + \sum_ij c_i c_j h_ij            = 0 */
  /* delta[1]:                   + \sum_ij a_ij g_ij + \sum_i h_ii = b */

  /* -Az, -<phi,z> */
  polxvec_copy(tmp,ist->cnst->phi,n);
  polxvec_collaps_add_extension(tmp,gamma,comkey,n,cpp->kappa,1);
  j = k = 0;
  for(i=0;i<cpp->f;i++) {
    if(i) polxvec_scale(tmp,tmp,n,(int64_t)1 << cpp->b);
    polxvec_sub(&phi[j][k],&phi[j][k],tmp,n);
    j += pi->nu[i];
    k = (pi->nu[i]) ? 0 : k+n;
  }

  /* \sum_i c_i t_i */
  for(i=0;i<r;i++) {
    polxvec_polx_mul(tmp,&ist->c[i],gamma,cpp->kappa);
    for(j=0;j<cpp->fu;j++) {
      if(j) polxvec_scale(tmp,tmp,cpp->kappa,(int64_t)1 << j*cpp->bu);
      polxvec_add(&phiv[t+i*l+j*cpp->kappa],&phiv[t+i*l+j*cpp->kappa],tmp,cpp->kappa);
    }
  }

  /* \sum_ij c_i c_j h_ij */
  k = 0;
  for(i=0;i<r;i++)
    for(j=i;j<r;j++)
      polx_mul(&tmp[k++],&ist->c[i],&ist->c[j]);

  if(ist->cnst->a->len) {
    /* \sum_ij c_i c_j g_ij */
    polx_scale(chalbuf,&delta[0],2);
    j = 0;
    for(i=0;i<r;i++) {
      polx_mul(&tmp[k+j],&delta[0],&tmp[j]);
      polxvec_polx_mul(&tmp[k+j+1],chalbuf,&tmp[j+1],r-i-1);
      j += r-i;
    }

    /* \sum_ij a_ij g_ij */
    for(i=0;i<ist->cnst->a->len;i++) {
      j = triangularidx(ist->cnst->a->rows[i],ist->cnst->a->cols[i],r);
      polx_mul_add(&tmp[k+j],&delta[1],&ist->cnst->a->coeffs[i]);
    }
  }

  /* \sum_i h_ii */
  j = 0;
  for(i=0;i<r;i++) {
    polx_add(&tmp[j],&delta[1],&tmp[j]);
    j += r-i;
  }

  for(i=0;i<cpp->fg;i++) {
    if(i) polxvec_scale(&tmp[k],&tmp[k],k,(int64_t)1 << cpp->bg);
    polxvec_add(&phiv[g+i*k],&phiv[g+i*k],&tmp[k],k);
  }
  for(i=0;i<cpp->fu;i++) {
    if(i) polxvec_scale(&tmp[0],&tmp[0],k,(int64_t)1 << cpp->bu);
    polxvec_add(&phiv[h+i*k],&phiv[h+i*k],&tmp[0],k);
  }

  /* b */
  polx_mul_add(ost->cnst->b,&delta[1],ist->cnst->b);

  /* a */
  /* Recall: ost->r = cpp->f*pi->nu[0] + pi->nu[cpp->f] */
  if(ist->cnst->a->len) {
    for(i=0;i<cpp->f;i++) {
      for(j=0;j<pi->nu[0];j++) {
        for(k=i;k<cpp->f;k++) {
          int64_t s = (k==i) ? -1 : -2;
          s <<= (i+k)*cpp->b;
          polx_scale(&ost->cnst->a->coeffs[ost->cnst->a->len],&delta[0],s);
          ost->cnst->a->rows[ost->cnst->a->len] = i*pi->nu[0]+j;
          ost->cnst->a->cols[ost->cnst->a->len] = k*pi->nu[0]+j;
          ost->cnst->a->len += 1;
        }
      }
    }
    // reducing size; alignment should be preserved
    ost->cnst->a->coeffs = realloc(ost->cnst->a->coeffs,ost->cnst->a->len*sizeof(polx));
  }

  free(tmp);
}

static void amortize_tail(statement *ost, witness *owt, proof *pi, polx sx[ost->r][ost->n]) {
  const size_t r = ost->r;
  const size_t n = ost->n;
  const comparams *cpp = ost->cpp;

  size_t i;
  __attribute__((aligned(16)))
  uint8_t hashbuf[16+2*N*QBYTES];
  polx (*phi)[n] = (polx(*)[n])ost->cnst->phi;
  polx *hx = ost->u2;
  polz *hz = pi->u2;

  polxvec_sprod(&hx[0],phi[0],sx[0],n);
  polz_frompolx(&hz[0],&hx[0]);

  memcpy(hashbuf,ost->h,16);
  polzvec_bitpack(&hashbuf[16],&hz[0],1);
  shake128(hashbuf,32,hashbuf,16+N*QBYTES);

  // compute challenge parapeters
  polxvec_challenge(&ost->c[0],1,&hashbuf[16],0);

  polxvec_polx_mul(sx[0],&ost->c[0],sx[0],n);
  polxvec_polx_mul(phi[0],&ost->c[0],phi[0],n);

  for(i=1;i<r;i++) {
    polxvec_sprod(&hx[2*i-1],phi[i],sx[0],n);
    polxvec_sprod_add(&hx[2*i-1],phi[0],sx[i],n);
    polxvec_sprod(&hx[2*i],phi[i],sx[i],n);
    polzvec_frompolxvec(&hz[2*i-1],&hx[2*i-1],2);
    polzvec_bitpack(&hashbuf[16],&hz[2*i-1],2);
    shake128(hashbuf,32,hashbuf,16+2*N*QBYTES);
    polxvec_challenge(&ost->c[i],1,&hashbuf[16],0);
    polxvec_polx_mul_add(sx[0],&ost->c[i],sx[i],n);
    polxvec_polx_mul_add(phi[0],&ost->c[i],phi[i],n);
  }

  memcpy(ost->h,hashbuf,16);
  polxvec_decompose(owt->s[0],sx[0],n,cpp->f,cpp->b);

  ost->betasq = 0;
  for(i=0;i<cpp->f;i++) {
    owt->normsq[i] = polyvec_sprodz(owt->s[i],owt->s[i],n);
    ost->betasq += owt->normsq[i];
  }
  pi->normsq = ost->betasq;

  ost->cnst->phi = realloc(ost->cnst->phi,n*sizeof(polx));
}

void amortize(statement *ost, witness *owt, proof *pi, polx sx[ost->r][ost->n]) {
  const size_t r = ost->r;
  const size_t n = ost->n;
  const size_t m = ost->m;
  const comparams *cpp = ost->cpp;

  const size_t t = 0;
  const size_t g = t + r*cpp->fu*cpp->kappa;
  const size_t h = g + cpp->fg*(r*r+r)/2;

  if(pi->tail) {
    amortize_tail(ost,owt,pi,sx);
    return;
  }

  size_t i,j,k,l;
  poly *vh = (poly*)&owt->s[cpp->f][h];
  polx (*phi)[n] = (polx(*)[n])ost->cnst->phi;
  polx *hx = (polx*)_aligned_alloc(64,(m-h)*sizeof(polx));

  /* linear garbage */
  polxvec_setzero(hx,(r*r+r)/2);
  for(l=0;l<n;l++) {
    k = 0;
    for(i=0;i<r;i++) {
      polx_mul_add(&hx[k++],&phi[i][l],&sx[i][l]);
      for(j=i+1;j<r;j++) {
        polx_mul_add(&hx[k],&phi[i][l],&sx[j][l]);
        polx_mul_add(&hx[k++],&phi[j][l],&sx[i][l]);
      }
    }
  }
  polxvec_decompose(vh,hx,(r*r+r)/2,cpp->fu,cpp->bu);
  polxvec_frompolyvec(hx,vh,m-h);

  /* second outer commitment */
  polxvec_mul_extension(ost->u2,comkey,hx,m-h,cpp->kappa1,1);
  polzvec_frompolxvec(pi->u2,ost->u2,cpp->u2len);

  /* amortization */
  __attribute__((aligned(16)))
  uint8_t hashbuf[16+cpp->kappa1*N*QBYTES];
  memcpy(hashbuf,ost->h,16);
  polzvec_bitpack(&hashbuf[16],pi->u2,cpp->kappa1);
  shake128(hashbuf,32,hashbuf,sizeof(hashbuf));
  memcpy(ost->h,hashbuf,16);
  polxvec_challenge(ost->c,r,&hashbuf[16],0);

  polxvec_polx_mul(sx[0],&ost->c[0],sx[0],n);
  polxvec_polx_mul(phi[0],&ost->c[0],phi[0],n);
  for(i=1;i<r;i++) {
    polxvec_polx_mul_add(sx[0],&ost->c[i],sx[i],n);
    polxvec_polx_mul_add(phi[0],&ost->c[i],phi[i],n);
  }
  polxvec_decompose(owt->s[0],sx[0],n,cpp->f,cpp->b);

  ost->betasq = 0;
  for(i=0;i<cpp->f;i++) {
    owt->normsq[i] = polyvec_sprodz(owt->s[i],owt->s[i],n);
    ost->betasq += owt->normsq[i];
  }
  owt->normsq[cpp->f] = polyvec_sprodz(owt->s[cpp->f],owt->s[cpp->f],m);
  ost->betasq += owt->normsq[cpp->f];
  pi->normsq = ost->betasq;

  ost->cnst->phi = realloc(ost->cnst->phi,n*sizeof(polx));
  free(hx);
}

int reduce_amortize(statement *ost, const proof *pi) {
  const size_t r = ost->r;
  const size_t n = ost->n;
  const comparams *cpp = ost->cpp;

  size_t i;
  polx (*phi)[n] = (polx(*)[n])ost->cnst->phi;

  ost->betasq = pi->normsq;
  if(!sis_secure(cpp->kappa,6*T*SLACK*ldexp(1,(cpp->f-1)*cpp->b)*sqrt(ost->betasq))) {
    fprintf(stderr,"ERROR in reduce_amortize(): Inner commitments not secure\n");
    return 1;
  }
  if(!pi->tail && !sis_secure(cpp->kappa1,2*SLACK*sqrt(ost->betasq))) {
    fprintf(stderr,"ERROR in reduce_amortize(): Outer commitments not secure\n");
    return 2;
  }

  /* second outer commitment resp garbage terms */
  polzvec_topolxvec(ost->u2,pi->u2,cpp->u2len);

  __attribute__((aligned(16)))
  uint8_t hashbuf[16+cpp->u2len*N*QBYTES];
  memcpy(hashbuf,ost->h,16);

  if(pi->tail) {
    polzvec_bitpack(&hashbuf[16],pi->u2,1);
    shake128(hashbuf,32,hashbuf,16+N*QBYTES);
    polxvec_challenge(&ost->c[0],1,&hashbuf[16],0);
    for(i=1;i<r;i++) {
      polzvec_bitpack(&hashbuf[16],&pi->u2[2*i-1],2);
      shake128(hashbuf,32,hashbuf,16+2*N*QBYTES);
      polxvec_challenge(&ost->c[i],1,&hashbuf[16],0);
    }
  }
  else {
    polzvec_bitpack(&hashbuf[16],pi->u2,cpp->u2len);
    shake128(hashbuf,32,hashbuf,sizeof(hashbuf));
    polxvec_challenge(ost->c,r,&hashbuf[16],0);
  }
  memcpy(ost->h,hashbuf,16);

  polxvec_polx_mul(phi[0],&ost->c[0],phi[0],n);
  for(i=1;i<r;i++)
    polxvec_polx_mul_add(phi[0],&ost->c[i],phi[i],n);

  ost->cnst->phi = realloc(ost->cnst->phi,n*sizeof(polx));
  return 0;
}

int prove(statement *ost, witness *owt, proof *pi, const statement *ist, const witness *iwt, int tail) {
  int ret;
  size_t i;
  constraint cnst[1] = {};
  void *buf = NULL;

  ret = 
  (pi,iwt,ist->cpp->fg != 0,tail);
  if(ret) // commitments not secure (1/2)
    return ret;
  init_statement(ost,pi,ist->h);
  init_witness(owt,ost);
  printf("Predicted witness norm: %.2f\n\n",sqrt(pi->normsq));

  {
    buf = _aligned_alloc(64,ost->r*ost->n*(sizeof(polx)+256*N/8));
    polx (*sx)[ost->n] = (polx(*)[ost->n])buf;
    uint8_t (*jlmat)[ost->n][256*N/8] = (uint8_t(*)[ost->n][256*N/8])sx[ost->r];
    commit(ost,owt,pi,sx,iwt);
    ret = project(ost,pi,jlmat,iwt);
    if(ret) {
      ret += 10;
      goto err;
    }

    init_constraint_raw(cnst,ost->r,ost->n,1,0);
    for(i=0;i<LIFTS;i++) {
      collaps_jlproj(cnst,ost,pi,jlmat);
      lift_aggregate_zqcnst(ost,pi,i,cnst,sx);
    }
    free_constraint(cnst);

    aggregate(ost,pi,ist);
    amortize(ost,owt,pi,sx);
    free(buf);
    buf = NULL;
  }

  polx_refresh(ost->cnst->b);
  polxvec_refresh(ost->cnst->phi,ost->n);
  return 0;

err:
  free_proof(pi);
  free_statement(ost);
  free_witness(owt);
  free(buf);
  free_constraint(cnst);
  return ret;
}

int reduce(statement *ost, const proof *pi, const statement *ist) {
  size_t i;
  int ret;
  uint8_t (*jlmat)[ost->n][256*N/8];
  constraint cnst[1];

  init_statement(ost,pi,ist->h);
  init_constraint(cnst,ost);
  jlmat = _aligned_alloc(64,ost->r*ost->n*256*N/8);

  reduce_commit(ost,pi);
  ret = reduce_project(ost,jlmat,pi,pi->r,ist->betasq);
  if(ret) goto err;  // projection too long

  for(i=0;i<LIFTS;i++) {
    collaps_jlproj(cnst,ost,pi,jlmat);
    reduce_lift_aggregate_zqcnst(ost,pi,i,cnst);
  }
  free_constraint(cnst);
  free(jlmat);
  jlmat = NULL;

  aggregate(ost,pi,ist);
  ret = reduce_amortize(ost,pi);
  if(ret) {  // commitments not secure (1/2)
    ret += 10;
    goto err;
  }

  polx_refresh(ost->cnst->b);
  polxvec_refresh(ost->cnst->phi,ost->n);
  return 0;

err:
  free_statement(ost);
  free_constraint(cnst);
  free(jlmat);
  return ret;
}

int verify(const statement *st, const witness *wt) {
  const comparams *cpp = st->cpp;
  const size_t r = st->r;
  const size_t n = st->n;
  const size_t m = st->m;

  const size_t l = cpp->fu*cpp->kappa;
  const size_t t = 0;
  const size_t g = t + r*l;
  const size_t h = g + cpp->fg*(r*r+r)/2;

  size_t i,j,k;
  int ret = 0;
  uint64_t normsq = 0;
  polx tmp0[cpp->kappa];
  polx tmp1[cpp->kappa1];

  void *buf = _aligned_alloc(64,(n+m)*sizeof(polx));
  polx *z = (polx*)buf;
  polx *v = &z[n];

  for(i=0;i<wt->r;i++)
    normsq += polyvec_sprodz(wt->s[i],wt->s[i],wt->n[i]);
  if(normsq > st->betasq) {
    fprintf(stderr,"ERROR in verify(): Total witness norm bigger than bound\n");
    ret = 1;
    goto end;
  }

  if(!st->tail) {
    /* Bv1 = u1 */
    polxvec_copy(tmp0,st->u1,cpp->kappa1);
    j = 0;
    for(i=0;i<r;i++) {
      polxvec_frompolyvec(&v[t+i*l],&wt->s[cpp->f][t+i*l],l);
      j += polxvec_mul_extension(tmp1,&comkey[j],&v[t+i*l],l,cpp->kappa1,1);
      polxvec_sub(tmp0,tmp0,tmp1,cpp->kappa1);
    }
    polxvec_frompolyvec(&v[g],&wt->s[cpp->f][g],h-g);
    polxvec_mul_extension(tmp1,&comkey[j],&v[g],h-g,cpp->kappa1,1);
    polxvec_sub(tmp0,tmp0,tmp1,cpp->kappa1);
    if(!polxvec_iszero(tmp0,cpp->kappa1)) {
      fprintf(stderr,"ERROR in verify(): First outer commitment opening wrong\n");
      ret = 2;
      goto end;
    }

    /* Bv2 = u2 */
    polxvec_frompolyvec(&v[h],&wt->s[cpp->f][h],m-h);
    polxvec_mul_extension(tmp0,comkey,&v[h],m-h,cpp->kappa1,1);
    polxvec_sub(tmp0,tmp0,st->u2,cpp->kappa1);
    if(!polxvec_iszero(tmp0,cpp->kappa1)) {
      fprintf(stderr,"ERROR in verify(): Second outer commitment opening wrong\n");
      ret = 3;
      goto end;
    }

    /* reconstruct inner coms and garbage */
    for(i=0;i<r;i++)
      for(j=1;j<cpp->fu;j++)
        polxvec_scale_add(&v[t+i*l],&v[t+i*l+j*cpp->kappa],cpp->kappa,(int64_t)1 << j*cpp->bu);
    for(i=1;i<cpp->fg;i++)
      polxvec_scale_add(&v[g],&v[g+i*(r*r+r)/2],(r*r+r)/2,(int64_t)1 << i*cpp->bg);
    for(i=1;i<cpp->fu;i++)
      polxvec_scale_add(&v[h],&v[h+i*(r*r+r)/2],(r*r+r)/2,(int64_t)1 << i*cpp->bu);
  }
  else {
    polxvec_copy(&v[t],st->u1,cpp->u1len);
    polxvec_copy(&v[h],st->u2,cpp->u2len);
  }

  /* reconstruct z */
  polxvec_reconstruct(z,wt->s[0],n,cpp->f,cpp->b);

  /* Az = \sum_i c_i t_i */
  polxvec_polx_mul(&v[t],&st->c[0],&v[t],cpp->kappa);
  for(i=1;i<r;i++)
    polxvec_polx_mul_add(&v[t],&st->c[i],&v[t+i*l],cpp->kappa);
  polxvec_mul_extension(tmp0,comkey,z,n,cpp->kappa,1);
  polxvec_sub(tmp0,tmp0,&v[t],cpp->kappa);
  if(!polxvec_iszero(tmp0,cpp->kappa)) {
    fprintf(stderr,"ERROR in verify(): Amortized (inner commitment) opening wrong\n");
    ret = 4;
    goto end;
  }

  /* \sum_ij a_ij g_ij + \sum_i h_ii = b */
  polx_neg(tmp0,st->cnst->b);
  j = 0;
  for(i=0;i<r;i++) {
    polx_add(tmp0,tmp0,&v[h+j]);
    j += (st->tail) ? 2 : r-i;
  }
  for(i=0;i<st->cnst->a->len;i++) {
    j = triangularidx(st->cnst->a->rows[i],st->cnst->a->cols[i],r);
    polx_mul_add(tmp0,&st->cnst->a->coeffs[i],&v[g+j]);
  }
  if(!polxvec_iszero(tmp0,1)) {
    fprintf(stderr,"ERROR in verify(): Aggregated dot-product constraint doesn't hold\n");
    ret = 5;
    goto end;
  }

  /* <z,z> = \sum_ij c_i c_j g_ij */
  if(st->cnst->a->len) {
    k = 0;
    for(i=0;i<r;i++) {
      polx_mul(tmp0,&st->c[i],&v[g+k]);
      polxvec_sprod(&tmp0[1],&st->c[i+1],&v[g+k+1],r-1-i);
      polx_scale_add(tmp0,&tmp0[1],2);
      if(i) polx_mul_add(&v[g],&st->c[i],tmp0);
      else polx_mul(&v[g],&st->c[i],tmp0);
      k += r-i;
    }
    polxvec_sprod(tmp0,z,z,n);
    polx_sub(tmp0,tmp0,&v[g]);
    if(!polx_iszero(tmp0)) {
      fprintf(stderr,"ERROR in verify(): Quadratic garbage polynomials wrong\n");
      ret = 6;
      goto end;
    }
  }

  /* <phi,z> = \sum_ij c_i c_j h_ij */
  if(!st->tail) {
    k = 0;
    for(i=0;i<r;i++) {
      polxvec_sprod(tmp0,&st->c[i],&v[h+k],r-i);
      if(i) polx_mul_add(&v[h],&st->c[i],tmp0);
      else polx_mul(&v[h],&st->c[i],tmp0);
      k += r-i;
    }
  }
  else {
    polx_mul(&v[h],&st->c[0],&v[h]);
    polx_mul(&v[h],&st->c[0],&v[h]);
    for(i=1;i<r;i++) {
      polx_mul_add(&v[h+2*i-1],&st->c[i],&v[h+2*i]);
      polx_mul_add(&v[h],&st->c[i],&v[h+2*i-1]);
    }
  }
  polxvec_sprod(tmp0,st->cnst->phi,z,n);
  polx_sub(tmp0,tmp0,&v[h]);
  if(!polxvec_iszero(tmp0,1)) {
    fprintf(stderr,"ERROR in verify(): Linear garbage polynomials wrong\n");
    ret = 7;
    goto end;
  }

end:
  free(buf);
  return ret;
}
