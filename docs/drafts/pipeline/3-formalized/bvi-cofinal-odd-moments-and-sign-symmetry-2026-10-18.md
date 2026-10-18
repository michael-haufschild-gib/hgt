# Cofinal odd moments and sign symmetry

Status: all fixed odd source moments formalized, audited, wired, and indexed.
All 34 public declarations use only standard Lean axioms. Scope is divisor-incidence arithmetic, independent
of MC/PM receivers and unrelated to RH.

## Proved theorem and deferred extension

For every fixed integer B>=0 and odd positive integer r, with
`s_N(k)=sieveSeq N moebiusReal k`,

    (1/N) sum_{1<=k<=(B+1)N} s_N(k)^r -> 0.

Deferred stronger candidate: the bounded integer-valued source on each fixed linear
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

## Completed proof obligations

- [x] Complete the existing quadratic profile and its original-source audit.
- [x] Prove the unconditional finite-modulus coprime Möbius mean zero
  using the corpus PNT and prime-deletion contraction.
- [x] Handle repeated prime factors in the modulus explicitly. In tuples of
  length greater than two, the multipliers need not be pairwise coprime.
- [x] Audit tuple lcm reindexing, all strict lower endpoints, and odd-power
  identities without numerical experiments.
- Sign-class balance and existence of a full limiting distribution remain
  separate extensions, not obligations for the proved odd-moment theorem.
  Fixed B is essential; no uniform growing-B rate is claimed. Further research
  is deferred at the user's request to finish started Lean work and pause.

## Corpus evidence so far

Deep query `coprime Mobius mean zero finite modulus odd products dilation`
returned partial results, inspected in both candidate and source-argument
lists. It found finite multiplicative pair identities and prime-deletion
identities, not the proposed odd-moment limit. The file
`RHTower/CoprimeMobiusSumsZeroFree.lean` is not an applicable mean-zero
producer: its declaration inventory concerns conditional zero-free
consequences and was not pursued. The subsequent focused query
`coprime moebius tendsto` is discussed below. No external novelty claim.

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

The foundation's paper proof and Lean proof are complete. Product
factorization, finite-tuple reindexing, and the complete source-power
expansion are also proved and audited in the second leaf.

## Final verification

Canonical session 27293 finished checking the original source
`CofinalMobiusOddMomentsAndQuotientProducts.lean`, emitting olean/ilean;
log `/tmp/bvi-source-odd-moments-canonical.log`; source SHA-256
`dc3457fd6d32dc41e7516d271ee8fd08fb8e5813253a956b3dd0194ae116a9b9`.
Both canonical artifacts were emitted at 17:36:18; the diagnostic log is empty.
Scratch 68201 passed the complete tuple reindexing and every fixed odd
source moment. Its only warning was deprecated `push_neg`, replaced by
direct propositional reasoning before canonical audit. That scratch also
audited all 19 foundation declarations: standard Lean axioms only.
Source-leaf axiom audit 81081 passed all 15 public declarations. Both new
leaves are wired into the BVI umbrella. Index 97441 passed; lint 41902
reported only the existing root `TransHorizonIncidenceMechanics.lean`
placement error. No owned lint finding. Global lint is not claimed clean.
Canonical logs, all 34 public axiom blocks, source hashes, index/lint logs,
and corpus coverage are archived in `logs/bvi-odd-moments-2026-10-18-*`.
The manifest is authoritative. Completed scratch inputs are removed after
archive; historical `/tmp` references in this card are not live inputs.
Original-source session 6385 passed with empty diagnostics for
`CoprimeMobiusCancellationAndOddDilationMeans.lean`, emitting olean/ilean;
log `/tmp/bvi-coprime-mobius-canonical.log`. Source SHA-256
`2fc00ca638f7adf96d12914658b0add1c37e89faba00d0e29271145e5b7c9619`.
Scratch session 33012 passed with no diagnostics: unrestricted-modulus
mean zero and every fixed odd dilation-product mean. Original scratch
and the prepared public-declaration audit were retained through final audit
and then removed. Its 19-declaration axiom audit passed in scratch 68201.
No C9 Lean process remains running.

Base PNT source verified: `RHTower/Sieve/MoebiusSharpLittleO.lean`,
`tendsto_norm_sum_moebius_div`, for real cutoffs and natural floors. The
complex-to-real norm conversion is the existing pattern from
`MoebiusMaximalWindow.lean`. The private trichotomy proof in
`MoebiusSignBalance.lean` derives the three Möbius values directly from
`abs_moebius_le_one`; this supplied symbolic odd-power reduction.

Search coverage and inspected candidate/source-argument records are archived
in `logs/bvi-odd-moments-2026-10-18-research.json`. No computations or numerical
experiments were used.

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

The full source-moment Lean transfer passed scratch check 68201 and its
canonical and public axiom audits. Relevant APIs
located in installed source: `Finset.lcm_ne_zero_iff`, `Finset.dvd_lcm`,
`Finset.lcm_dvd`, `Finset.exists_mem_eq_sup`, `Finset.le_sup`,
`Finset.sup_le_iff`, `Finset.sum_pow'`, and `Fintype.mem_piFinset`. They
passed probes in the scratch before canonical use.

The additional deep source-moment query completed partially and is included
in the research archive. Candidate and source-argument
lists were inspected; no matching odd source-moment limit appeared.

Odd moments alone do not prove existence of every sign-class density.
With the finite support bound they can imply vanishing differences of
opposite sign-class counts. Existence of a full limiting distribution
requires further even-moment or direct counting control.
