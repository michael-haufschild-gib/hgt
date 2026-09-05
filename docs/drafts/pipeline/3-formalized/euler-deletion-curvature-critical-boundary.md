# Literal factorization curvature at the critical exponent

## Question and relevance

The current candidate chain asks for a zero-source law annihilating the Hermitian
factorization curvature at exponent `2 Re(rho)`. Audit whether that literal charge
vanishes on the critical line before interpreting it as an off-line obstruction.

Corpus checked: `EulerDeletionFactorizationCurvature` proves its sign only for
absolute exponent `alpha>1`; `EulerDeletionBalancedPeriodFreedom` gives its exact
four-channel linear coefficient form; `EulerDeletionQuasiShuffleZeroLanding` supplies
the holomorphic chronological deletion sum on `Re(s)>0` and its pole-cleared zeta
identity. Search found no critical ordered value. No numerical experiment is needed.

## Conjecture / paper derivation

Write `a_d(n)=1-d[d|n]` and let `S_d(s)` denote the ordinary ordered sum of
`a_d(n)n^(-s)`. The pole-cleared identity is
`(s-1)S_d(s)=(1-d^(1-s)) G(s)`, where `G(1)=1`.
Differentiate at `s=1`: `S_d(1)=log d`.

The proved curvature coefficient is
`k(n)=(q-1)[a_pq(n)-a_q(n)+r(a_qr(n)-a_pqr(n))]`.
Consequently its literal ordered harmonic sum exists and equals

`sum_(n>=1) k(n)/n = -(q-1)(r-1) log p`.

This is strictly negative for nontrivial pairwise-coprime labels, including at every
critical-line zeta zero after the Hermitian exponent substitution. There is no
absolute-summability assertion at exponent one and no use of Lean's unordered `tsum`
as a replacement for this ordered limit.

## Exact source identification and actual-zero counterexample

The physical observable is the four-term curvature of the literal pairing
`Re(a_q(n)n^(-rho) conjugate(a_p(n)a_q(n)n^(-rho)))`, with one common integer cutoff.
Its term is exactly `a_p(n)a_q(n)^2 n^(-2 Re(rho))`, for every `n>0` and complex
`rho`. Thus the critical computation does not substitute an artificial receiver.
For `Re(rho)>1/2`, its ordered limit equals the existing
`deletionFactorizationGradeCurvature (2*rho.re) p q r`.

At every non-pole zeta zero with positive real part, the same coefficient `k(n)`
with the original exponent has ordered source sum zero: its four deletion sums
vanish individually. Unconditional corpus Hardy theory supplies an actual critical-line
zero. At that very zero, with labels `(2,3,5)`, the two limits are therefore

`sum k(n)n^(-rho) = 0`, but `sum k(n)n^(-2 Re(rho)) = -8 log 2 < 0`.

Source zero-landing does not pass through Hermitian regrading. This is a counterexample
at a genuine zeta zero, not a perturbed-weight or functional-equation model.

## Scope and positive survivor

Unrestricted zero-fibre annihilation of this literal charge is false: it does not
vanish on the critical line. The exact positive survivor is its source-derived ordered
boundary value, together with coefficient-faithful identification with both the physical
Mellin pairings and the existing charge in its absolute-convergence chamber.

This does **not** refute a law genuinely restricted to `Re(rho)>1/2`; that producer
remains open. Subtracting the boundary value would define a different receiver, not prove
zero-selection. No Xi multiplicity/index transport or RH proof is claimed. Do not evaluate
an unordered `tsum` outside its proved summability domain as a substitute for this boundary.

The deletion logarithm and pole argument use classical analytic ingredients; see
[DLMF §25.2](https://dlmf.nist.gov/25.2). No literature-level novelty claim is made.

## Lean and verification

`formal/GaloisForLFunctions/RHTower/EulerDeletionCurvatureCriticalBoundary.lean`,
namespace `RHTower.DeletionCriticalCurvature`:

- `deletion_sum_one`, `tendsto_curvaturePrefix`: logarithmic source value and exact boundary.
- `grade_pair_term`, `physicalPairPrefix_eq`: literal coefficient/complex-pair identification.
- `tendsto_hermitianPrefix_of_half_lt`: compatibility with existing admitted curvature.
- `tendsto_sourcePrefix_zero`: original source exponent vanishes at actual zeros.
- `exists_actual_zero_with_different_source_limits`: source zero and negative physical
  limit at the same genuine critical-line zero.
- `not_global_zero_curvature_annihilation`: unconditional refutation for labels `(2,3,5)`.

Scratch and targeted leaf olean passed without warnings. Ten imported capstones audited:
only `propext`, `Classical.choice`, `Quot.sound`. Wired into `RHTower`; no umbrella build.
Global lint reports one unrelated unwired module, `EulerDeletionBalancedPeriodCurvatureNoGo`;
no error in this change. No computational experiment used.
