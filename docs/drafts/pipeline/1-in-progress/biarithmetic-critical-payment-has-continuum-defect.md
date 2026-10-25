# Critical payment has a continuum-dimensional closure defect

- **ID:** biarithmetic-critical-payment-has-continuum-defect
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (Lean formalization incomplete)
- **Proof status:** Only statements with completed Lean checks and axiom audits are proved. Paper arguments below are proof plans; every significant claim remains a formalization obligation.
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** At the critical golden damping, the quotient of the Wiener closure of the paid ideal by the paid ideal has complex Hamel dimension exactly continuum. The defect already occurs among kernels supported on powers of five. The intrinsic norm-lattice receiver has the same defect despite its rank-one tangent module.

## Exact one-prime model

The dependency-closed proofs on the digital-energy and intrinsic-module cards identify
critical payment with

`D={g in ell1(N,C): (sum_(r<=m) g_r)_m belongs to ell2}`.

Here `g_r=5^(-r/2)f(5^r)` is the normalized Wiener coefficient. Its closure is
`Z={g in ell1: sum_r g_r=0}`. Necessity follows because an `ell2` sequence of
partial sums tends to zero, while the `ell1` sum exists. For sufficiency after closure,
keep the coefficients below `M`, replace `g_M` by `g_M-S_M`, and delete the tail,
where `S_M=sum_(r<=M)g_r`. The corrected finite sequence has partial sums `S_m`
for `m<M` and zero for `m>=M`; it belongs to `D`. Its `ell1` distance from `g`
is at most `|S_M|+sum_(r>M)|g_r|`, which tends to zero for `g in Z`.

## Explicit independent unpaid classes

For each real `alpha` with `0<alpha<=1/2`, define

`g_alpha(0)=-1`,
`g_alpha(r)=r^(-alpha)-(r+1)^(-alpha)` for `r>=1`.

The positive tail telescopes: its sum is one, so the `ell1` norm is two and
the total sum is zero. Its exact partial sum is `S_alpha(m)=-(m+1)^(-alpha)`.
Because `2alpha<=1`, the squares have divergent sum. Thus `g_alpha` belongs
to `Z` but not to `D`.

Take a nontrivial finite complex combination with distinct parameters and choose
the smallest parameter `alpha0` whose coefficient `c0` is nonzero. Its partial sum,
divided by `(m+1)^(-alpha0)`, tends to `-c0`: every remaining term has the factor
`(m+1)^(-(alpha-alpha0))`, which tends to zero. Hence its absolute value is eventually
at least `(|c0|/2)(m+1)^(-alpha0)`. Its squared partial sums still diverge. Every
such combination therefore lies outside `D`. The classes of the `g_alpha` form
a linearly independent family in `Z/D` indexed by a real interval.

The same coefficient construction makes sense for every `alpha>0`, not
only the unpaid interval. Telescoping still gives absolute sum two, total
sum zero, and partial sum `-(m+1)^(-alpha)`. The exact square energy is
the shifted power series with exponent `-2alpha`, hence it is finite
exactly for `alpha>1/2`. This supplies a complete parameter calibration
on both sides of the critical sequence boundary. Dedicated corpus searches
did not return a general power-difference family; Mathlib's classical
`Real.summable_nat_rpow` supplies the power-series criterion. The extension
is a paper deduction, with no separate originality claim and Lean pending.

The power-difference family and exact half-exponent threshold are drafted in
`/tmp/BiarithmeticPowerTailCoefficients.lean`, unchecked. The finite-combination
argument can use the corpus's dominant-exponent method from
`HTGeometry/ExponentialSumAsymptotics.lean`: normalize by the smallest active
exponent, pass a finite sum through the limit, and retain its nonzero complex
coefficient. That existing theorem is for real exponential sums; the required
complex discrete power-tail specialization and divergent lower bound remain
to be formalized. Its source proof was inspected before reuse of the method.

That specialization is now drafted in `/tmp/BiarithmeticPowerTailIndependence.lean`.
It divides a finite combination by its smallest active power tail, passes the
finite complex sum through the limit, and obtains its nonzero coefficient.
Eventually the norm is at least half that coefficient norm times the dominant
tail. Squaring and removing a finite prefix transfers summability to the
divergent power series, a contradiction. Filtering zero coefficients and
taking the minimum active exponent gives the full finite independence statement.
The lower-bound argument only needs exponents at most one half; positivity
of the exponents is needed separately to place their coefficient differences
in `ell1`. This extension follows from exactly the same ratio proof.
The independence draft is unchecked. Quotient bundling and the cardinality
upper bounds passed scratch verification and await the direct repository check.

The quotient-interface corpus audit found the existing finite-family proof
pattern in `HTGeometry/ContinuumAnalyticEulerTailFaithfulnessUniversalityLaw.lean`
(`linearIndependent_iff'`, `Submodule.mkQ`, and its zero-membership law).
`HTGeometry/InfiniteHilbertImagesHaveContinuumRank.lean` supplies the interval
cardinality/rank comparison pattern. Its Hilbert-image theorem is not being
applied to the non-Hausdorff payment quotient. The needed ambient upper bound
already exists as `WienerAlgebraAt.cardinal_le_continuum` in
`ArithmeticDefectRigidity/TheClosedCofactorAnnihilatorHasNoCountableIndex.lean`;
it follows from the actual coefficient injection into `C^N`. Its source was
inspected and its dependency olean exists. These are reusable interfaces,
not yet a formal quotient-dimension proof for this source.

The actual quotient construction has passed its scratch check in
`CriticalGoldenPaymentQuotients`: restrict the paid ideal to complex scalars,
take its actual Wiener closure, and quotient that closure by the pulled-back
paid subspace. The canonical map to the full unreduced quotient is well defined.
Both ranks are at most continuum by quotient surjectivity, subtype injection,
and the existing Wiener cardinality theorem. All three transitive axiom
audits are clean. The wired production leaf awaits its direct source check.

`PowerTailWienerFamily` drafts actual norm-two closure members for every positive
exponent, with payment exactly above one half. The concluding
`CriticalGoldenContinuumDefect` draft uses the open interval `(0,1/2)`.
A finite relation in the actual quotient becomes a paid Wiener sum. Continuous
coefficient evaluation reads its exact normalized partial sums, and the
power-tail independence theorem forces every coefficient to vanish. The same
family lifts to the closure defect; its canonical image is the independent
family in the full quotient, so those lifted classes are independent as well.
The interval has cardinality continuum, supplying both matching lower bounds.
The two family/lower-bound drafts and their closure/power dependencies are unchecked.
This completes a proposed Lean proof chain for the ordinary-floor source only;
the intrinsic-source comparison still requires its separate module construction.

This proves dimension at least continuum. The ambient `ell1` space injects into
`C^N`, which has cardinality continuum, so any quotient and any Hamel basis in it
have cardinality at most continuum. Consequently `dim_C(Z/D)=continuum`.

## Transfer to the actual sources

The normalized one-prime embedding is linear and isometric into the full critical
Wiener algebra. Its intersection with the actual paid ideal is exactly `D` by the
source payment criterion, and its zero-sum subspace lies in the closure of that ideal
by the corrected finite approximants. Thus the same independent family injects into
`closure(P)/P`. The full algebra also injects into `C^N`, giving the matching upper
bound. This proves the claimed continuum dimension for the ordinary-floor golden
source. The independently proved intrinsic mean-correction and shift bounds give
the same transfer to its own norm-lattice payment ideal.

The one-prime annihilator quotient has dimension one, whereas its payment closure
defect has dimension continuum. These are distinct from the Hilbert dimension of
the tangent carrier. No Baire theorem for a nonclosed quotient is used.

## Scope and verification

The independent-power construction and cardinality upper bound are elementary
functional analysis. No claim of a new general Banach-space theorem is made.
This provides an explicit source calibration of the index ambiguity; it neither
counts arithmetic zeros nor proves a Riemann--Roch formula.

- [x] Dependency-closed proof plan, including complex linear independence.
- [ ] Lean exact source payment criterion and corrected finite approximation.
- [ ] Lean independent quotient family and matching cardinality bound.
- [ ] Direct source checks, transitive axiom audits, and umbrella imports.

The first explicit boundary witness and its corrected finite approximation are
formalized in `BiarithmeticGeometry/CriticalUnpaidSequence.lean`. It includes the exact
coefficient norm, zero evaluation, divergent square partial sums, and exact
`ell1` approximation distance. The direct source check and seven axiom audits
passed; its [stage-3 card](../3-formalized/biarithmetic-explicit-critical-unpaid-sequence.md)
records the exact scope. The continuum-independent
family, complex Wiener embedding, and quotient dimension remain separate.

The actual real Wiener embedding is now promoted to
`BiarithmeticGeometry/CriticalWienerLift.lean`, reusing AOT's `toWiener`,
`norm_term_realFn`, and the local-factor critical weight identity. It includes
exact coefficient norm and distance preservation. The separate draft
`/tmp/BiarithmeticCriticalGoldenPaymentNonclosed.lean` transfers the explicit
witness and finite repairs to the actual critical golden paid ideal. The real
embedding passed its direct source check and four audits, with a
[stage-3 card](../3-formalized/biarithmetic-critical-wiener-lift.md).
The nonclosedness draft is unchecked. Neither proves the continuum-dimensional quotient yet.

The complex normalized lift is separately drafted in
`/tmp/BiarithmeticComplexCriticalWienerLift.lean`. It assembles the existing
real embeddings, proves the exact coefficient formula and complex norm,
and transfers the checked complex golden criterion to ordinary coefficient
partial sums. Its proofs are unchecked. The corpus's general AOT weight
isometry was inspected; no duplicate Wiener carrier is introduced.

`CriticalGoldenClosure` separately drafts the full actual-closure transfer
for every absolutely summable complex coefficient sequence with zero total
evaluation. It uses the corrected finite-core sequence, the complex lift's
exact distances, and the actual golden payment criterion. Its assertion is
inclusion in the full actual ideal's closure; it does not identify that full
closure's intersection with the one-prime subalgebra. The draft is unchecked.
