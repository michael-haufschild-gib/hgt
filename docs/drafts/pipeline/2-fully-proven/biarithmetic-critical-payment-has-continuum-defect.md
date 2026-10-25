# Critical payment has a continuum-dimensional closure defect

- **ID:** biarithmetic-critical-payment-has-continuum-defect
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; explicit index calibration)
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

- [x] Dependency-closed paper proof, including complex linear independence.
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
embedding passed its scratch check and four audits; its direct check is pending.
The nonclosedness draft is unchecked. Neither proves the continuum-dimensional quotient yet.

The complex normalized lift is separately drafted in
`/tmp/BiarithmeticComplexCriticalWienerLift.lean`. It assembles the existing
real embeddings, proves the exact coefficient formula and complex norm,
and transfers the checked complex golden criterion to ordinary coefficient
partial sums. Its proofs are unchecked. The corpus's general AOT weight
isometry was inspected; no duplicate Wiener carrier is introduced.
