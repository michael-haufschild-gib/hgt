# Cofinal odd moments and sign symmetry

Status: active conjecture; no odd-moment Lean proof claimed. The quadratic
quotient profile is now formalized and audited. Scope is divisor-incidence arithmetic, independent
of MC/PM receivers and unrelated to RH.

## Conjecture

For every fixed integer B>=0 and odd positive integer r, with
`s_N(k)=sieveSeq N moebiusReal k`,

    (1/N) sum_{1<=k<=(B+1)N} s_N(k)^r -> 0.

Stronger candidate: the bounded integer-valued source on each fixed linear
window has a limiting distribution symmetric under changing sign. The
quadratic profile would be its second moment; it does not determine this
distribution by itself.

## Mechanism exposed by the quadratic route

Expand the finite complementary-quotient sum before taking the limit.
For any fixed tuple of quotient indices, common divisibility writes
`k=l*n`, with l their lcm. Each Möbius factor is `mu(a_i*n)` for a fixed
integer `a_i=l/q_i`. The band endpoints are fixed rational multiples of N.

Outside coprimality with the product of the a_i, some factor vanishes.
Inside coprimality, the product factors as

    (product_i mu(a_i)) * mu(n)^r.

For odd r, this is a constant times mu(n); for even positive r it is a
constant times mu(n)^2. Thus the odd-moment question reduces to a
finite-modulus coprime Möbius mean, rather than an additive shifted
correlation estimate.

## Obligations before implementation

- [x] Complete the existing quadratic profile and its original-source audit.
- Find or prove the unconditional finite-modulus coprime Möbius mean zero
  using the corpus PNT and prime-deletion contraction.
- Handle repeated prime factors in the modulus explicitly. In tuples of
  length greater than two, the multipliers need not be pairwise coprime.
- Audit tuple lcm reindexing, all strict lower endpoints, and odd-power
  identities without numerical experiments.
- Prove finite support bounds before inferring distributional symmetry
  from moments. Fixed B is essential; no uniform growing-B rate is claimed.

## Corpus evidence so far

Deep query `coprime Mobius mean zero finite modulus odd products dilation`
returned partial results, inspected in both candidate and source-argument
lists. It found finite multiplicative pair identities and prime-deletion
identities, not the proposed odd-moment limit. The file
`RHTower/CoprimeMobiusSumsZeroFree.lean` is not an applicable mean-zero
producer: its declaration inventory concerns conditional zero-free
consequences and was not pursued. A focused query `coprime moebius tendsto`
is the next retrieval step. No external novelty claim.

## Closed paper foundation: every fixed coprime Möbius mean vanishes

Define `m_Q(x)=x^{-1} sum_{1<=n<=floor(x), coprime(Q,n)} mu(n)`.
The global bound is `|m_Q(x)|<=1`, including x<=0 by the natural floor.
For a prime p not dividing Q, the exact indicator partition gives

    m_Q(x)=m_{pQ}(x)-(1/p)m_{pQ}(x/p).

The existing `tendsto_of_div_contraction` therefore propagates a zero
limit from Q to pQ. The base Q=1 is the unconditional corpus PNT
`tendsto_norm_sum_moebius_div`; Q=0 is supported only at n=1 and also has
zero normalized mean. Strong induction handles every Q: write Q=pR using
its least prime factor. If p divides R, coprimality with pR equals
coprimality with R, so the functions coincide. Otherwise use prime deletion.
This handles repeated prime factors without assuming a squarefree modulus.

The focused complete query `coprime moebius tendsto` found logarithmic
coprime kernels, not this unweighted mean theorem. Both candidate and
source-argument sections were inspected. A lexical `coprimeMoebiusDiv`
query found the weighted arithmetic function and its finite convolution
identity; that longer route is unnecessary for this foundation.

The foundation's paper proof is dependency-closed. Its Lean proof will be
checked next; the odd-moment theorem still needs product factorization,
finite-tuple reindexing, and the complete source-power expansion.

## Live implementation checkpoint

Owned Lean session 6385 is checking the original source
`CoprimeMobiusCancellationAndOddDilationMeans.lean`, emitting olean/ilean;
log `/tmp/bvi-coprime-mobius-canonical.log`. Source SHA-256
`2fc00ca638f7adf96d12914658b0add1c37e89faba00d0e29271145e5b7c9619`.
Scratch session 33012 passed with no diagnostics: unrestricted-modulus
mean zero and every fixed odd dilation-product mean. Original scratch
`/tmp/bvi_coprime_mobius_mean_proof.lean` is retained until final audit;
prepared public-declaration audit is `/tmp/bvi_coprime_mobius_axioms.lean`
(19 declarations). The leaf is not yet wired or axiom audited. Re-poll
before another owned Lean process.

Base PNT source verified: `RHTower/Sieve/MoebiusSharpLittleO.lean`,
`tendsto_norm_sum_moebius_div`, for real cutoffs and natural floors. The
complex-to-real norm conversion is the existing pattern from
`MoebiusMaximalWindow.lean`. The private trichotomy proof in
`MoebiusSignBalance.lean` derives the three Möbius values directly from
`abs_moebius_le_one`; this will supply symbolic odd-power reduction.

Search inputs retained for this active phase: `/tmp/bvi-odd-dilation-moments-research.json`,
`/tmp/bvi-coprime-mobius-mean-research.json`, `/tmp/bvi-coprime-moebius-div-research.json`,
and `/tmp/bvi-mobius-odd-product-research.json`. No computations or numerical
experiments have been used.

## Closed paper transfer to odd source moments

For a tuple q=(q_i) of length m=2r+1 with 1<=q_i<=B, put
`L=lcm_i q_i` and `H=max_i q_i`. Then L,H>0. The exact product of the
quotient-band terms is supported on `L|k` and `H*N<k`. Substitution k=L*n
turns every factor into `mu((L/q_i)*n)`. Consequently its prefix over
1<=k<=M, for H*N<=M, is exactly

    P_{(L/q_i)}(floor(M/L)) - P_{(L/q_i)}(floor(H*N/L)),

where P is the finite prefix of the product of Möbius dilations. The two
terms divided by N tend to zero at M=(B+1)N by the just-checked odd-product
mean and fixed rational rescaling. The multipliers may share primes;
the all-moduli mean-zero theorem is precisely what removes this issue.

For N>=1, the source is `1_{k=1}-sum_q T(N,q,k)` and each T vanishes at
k=1. Its m-th power is therefore `1_{k=1}-(sum_q T)^m`. The finite power
expansion (`Finset.sum_pow'`, verified in installed mathlib source) sums
over all length-m quotient tuples. Exchange the two finite sums, apply
each tuple limit, and let the single unit contribution 1/N tend to zero.
This closes the paper proof of all fixed odd source moments.

The full source-moment Lean transfer remains unimplemented. Relevant APIs
located in installed source: `Finset.lcm_ne_zero_iff`, `Finset.dvd_lcm`,
`Finset.lcm_dvd`, `Finset.exists_mem_eq_sup`, `Finset.le_sup`,
`Finset.sup_le_iff`, `Finset.sum_pow'`, and `Fintype.mem_piFinset`. They must
be checked in the forthcoming scratch before canonical use.

Odd moments alone do not prove existence of every sign-class density.
With the finite support bound they can imply vanishing differences of
opposite sign-class counts. Existence of a full limiting distribution
requires further even-moment or direct counting control.
