# Classical inputs from review-1011

- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAM
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, §2.1, Classical inputs to formalize.
- **Acceptance:** Unconditional proofs on the actual mathematical objects, direct Lean checks,
  transitive axiom audits, and umbrella imports. No numerical experiments or web search.

| Task | Required conclusion | Remaining mathematical input |
|---|---|---|
| A18 | Twisted second moments beyond mollifier length `T^(21/50)` | Retain free contour depth, taper and integration orders in the product approximate functional equation; seek every exponent below `1/2`. |
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

The full moment theorem still requires the dual off-diagonal, both contour
remainders, and summation over the mollifier coefficients. None is assumed in
these proved components. The two endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.
