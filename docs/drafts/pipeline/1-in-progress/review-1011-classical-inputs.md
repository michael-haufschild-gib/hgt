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
| A84 | Greedy carry-free optimality and Carlitz–Goss Newton polygon | **Greedy optimality formalized** for every residue degree and composition length. Actual zeta coefficients, strict slopes and entire-series passage remain. |
| A101 | Deuring–Heilbronn margin on remaining twisted-comb squares | **Formalized:** full logarithmic margin and hyperbolic square-energy bound on the actual twisted comb. See `../3-formalized/exceptional-square-repulsion-margin.md`. |

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
`TheExceptionalSquareRepelsTheOtherSquares.lean` proves the stronger exact
margin `m(Im ρ)≤1/2−|Re ρ−1/2|`, the square-energy bound, and their joint
endpoint with the actual comb limit. Its direct check and both transitive
axiom audits pass with only the three standard axioms. The umbrella imports it.

## A84: reduced combinatorial obstruction

`MinimalStructure.exists_singleton_normalized_counterexample` reduces any
failure to an optimum with singleton last part `{x}`. Every proper part has
zeroth inverse content `1`. The competing greedy last part contains a
larger exponent, has zeroth cyclic weight `p^(x.exp mod s)`, and uses only
residue representatives below `x.exp mod s`. The actual carry exchange
strictly increases weight, contradicting optimality. `GreedyOptimality`
therefore proves equivalence of greediness and optimality and uniqueness of
maximizing numerical part values. The subsequent Newton-polygon
identification must use the actual Carlitz–Goss coefficients.

The detailed card `carlitz-goss-rh-from-greedy-compositions.md` contains the
geometric prefix-cost argument, including `p=2`, and its checked components:
actual integral prefix coordinates, singleton boundary identities, interval
carry recursion, content-matrix realization, residue exponent gaps, and strict
geometric gain. General optimality passed the direct Lean check and both
endpoint transitive axiom audits using only the three standard axioms.
