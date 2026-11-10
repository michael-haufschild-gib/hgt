# Classical inputs from review-1011

- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAM
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, §2.1, Classical inputs to formalize.
- **Acceptance:** Unconditional proofs on the actual mathematical objects, direct Lean checks,
  transitive axiom audits, and umbrella imports. No numerical experiments or web search.

| Task | Required conclusion | Remaining mathematical input |
|---|---|---|
| A18 | Twisted second moments beyond mollifier length `T^(21/50)` | **Formalized:** every `0≤θ<1/2`, actual two-main-term formula and interval upper bound. See `../3-formalized/twisted-second-moments-below-square-root.md`. |
| A21 | Logarithmic two-point Chowla | Actual Liouville/Möbius correlation cancellation, including entropy decrement and short-interval Fourier uniformity. |
| A26 | Modular Weyl asymptotic `N(Λ) ∼ Λ/12` | Exact leading coefficient; existing two-sided order bounds do not suffice. |
| A33 | Fourier coefficients of the cubic residue | Arithmetic evaluation of the continued nonzero scattering residues; their existence alone does not suffice. |
| A41 | Count law for every smooth projective geometrically connected curve over a finite field | Actual curve point counts and the sharp genus-dependent bound; first case plane quartics. |
| A59 | Primes in short intervals in every reduced residue class | Power-saving interval lengths; fixed-modulus power-log PNT alone does not suffice. |
| A84 | Greedy carry-free optimality and Carlitz–Goss Newton polygon | General residue degree and arbitrary composition length, then actual zeta coefficients and slopes. |
| A101 | Deuring–Heilbronn margin on remaining twisted-comb squares | Quantitative transfer of proved uniform real-zero repulsion to the actual twisted form. |

## First analytic target

`ZetaGateFarPairError.norm_pairError_le_gen` separates smooth and dual contour
remainders from direct and dual off-diagonal terms. Its existing specialization
fixes contour depth `7`, taper `u^95`, scale `u^100`, and length `u^43`.
The constraints must be proved with adjustable parameters before claiming
the full range below `1/2`; a renamed existing specialization is not completion.

## Proved components

`MultiscaleMollifiedZetaField/AdjustableOffDiagonalBounds.lean` passes direct
Lean checking. `windowCarrierJetConst_le_rpow` retains the `T^(-aK)` derivative
saving when `a+b≤1`. `exists_directOffDiag_power_saving` proves arbitrary power
saving for the actual direct off-diagonal when `a>1/2+θ`, uniformly in both
coefficient indices `h,k≤T^θ` and displacement `0<d≤1/8`.

`AdjustableDualOffDiagonalBounds.lean` also passes direct checking.
`exists_dualOffDiag_power_saving` proves arbitrary power saving for the complete
dual off-diagonal when `0<b<1`, `a<1`, `a+b≤1`, and `a>1/2+θ+b/2`.
Both components use only `propext`, `Classical.choice`, and `Quot.sound`.

`AdjustableContourRemainders.lean` proves arbitrary power saving for both
actual contour remainders. `TwistedPairsBelowSquareRoot.lean` combines all
five error terms and proves `exists_pairError_power_saving` for every
`0≤θ<1/2`. Both pass direct Lean checks and use only the same standard
axioms. `TwistedSecondMomentsBelowSquareRoot.lean` passes its final direct
check: `exists_twistedMoment_power_saving` and
`exists_interval_twistedMoment_le` use only these axioms. All five modules
are imported by their umbrella.

## A18: parameter argument

For `0≤θ<1/2`, put `δ=1/2−θ`, `b=δ/2`, `a=1−b`.
Use scale `T`, taper `T^a`, frequency split `T^b`, and dual-product split
`T^(1+b)`. The direct exponent is `1−Kδ/2`; the dual oscillation exponent
is `4+b−Kδ/4`; the dual shifted tail exponent is `2+b−bJ`.
All three can be made less than any prescribed negative exponent by choosing
`K,J`. The Gaussian split tail is smaller than every power. Contour depth
`A=2j+1` saves `(1−2θ)A` powers on the smooth diagonal and at least
`(1−2θ)A−1` on the dual diagonal. This also absorbs the at most `T^(2θ)`
coefficient pairs. This proves the actual two-main-term twisted moment
formula with every remainder discharged.

## A101: quantitative square margin

For a real exceptional zero `β`, let
`m(γ)=log(1/(C(1−β)log(q(|γ|+3))))/(C log(q(|γ|+3)))`.
The current uniform repulsion theorem gives `Re ρ−1/2≤1/2−m(Im ρ)`
for every other zero in the right half-strip. Reflection gives
`|Re ρ−1/2|≤D(Im ρ)`, where `D(γ)=max(0,1/2−m(γ))`.
Each actual square contributes at least `−mult(ρ) S(D(Im ρ),a)‖f‖₂²`,
where `S(δ,a)=∫[-a,a] sinh²(δu)du`, including `S(0,a)=0`.
This follows from the conjugate-transform difference bound and
monotonicity of `S` in absolute depth. It retains the
quantitative gain before the stronger strip-clearing threshold is reached.
The existing comb theorem treats that threshold; its source also uses an
older signature of `exists_deuring_heilbronn_repulsion`. The new transfer
must use the current theorem directly and audit its dependencies.

## A84: reduced combinatorial obstruction

`MinimalStructure.exists_singleton_normalized_counterexample` reduces any
failure to an optimum with singleton last part `{x}`. Every proper part has
zeroth inverse content `1`. The competing greedy last part contains a
larger exponent, has zeroth cyclic weight `p^(x.exp mod s)`, and uses only
residue representatives below `x.exp mod s`. The remaining step is a
weight-increasing carry exchange across the proper parts; the singleton
normal form alone is not a contradiction. The subsequent Newton-polygon
identification must use the actual Carlitz–Goss coefficients.
