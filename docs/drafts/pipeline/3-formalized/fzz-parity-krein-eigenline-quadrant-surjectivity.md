# FZZ parity Krein eigenline quadrant surjectivity

- **ID:** HC23
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** FZZ-P
- **Date:** 2026-08-28
- **Statement:** Positive scale variation of the balanced positive-imaginary literal FZZ source eigenline is exactly the strict upper-left unit quadrant.

## Goal

Resolve the positive survivor left by F13. F13 proves that the two literal conjugate source lines
miss every right-half dyadic phase, but does not determine whether their left-half image has a
further hidden defect. HC23 computes the image exactly, without zero data or divisor fitting.

## Result

For the corpus-defined balanced eigenline coordinate `y(beta)`:

1. `(-Re y(beta))^2 = P(beta) * P(4 * beta) / P(2 * beta)^2`;
2. after `a = exp(beta)`, this ratio is
   `(a^2 + 1)^2 / ((a + 1) * (a^4 + 1))`;
3. every `c` with `0 < c < 1` occurs as `-Re y(beta)` at some `beta > 0`;
4. every unit complex `z` with `Re z < 0 < Im z` is exactly `y(beta)` at some positive scale;
5. conversely, every such source eigenline lies in that quadrant.

Thus the literal two-line phase image is exactly the strict left semicircle. F13's obstruction is
sharp: it is a missing-half-circle obstruction, not an internal interval or fractal defect.

## Proof certificate

The exact Fermi identity reduces the squared radial coordinate to the rational function

`g(a) = (a^2 + 1)^2 / ((a + 1) * (a^4 + 1))`.

It is continuous on every interval `[1,A]`, satisfies `g(1)=1`, and obeys `g(a) <= 4/a` for
`a >= 1`. For prescribed `0<c<1`, choose `A=4/c^2`; the intermediate value theorem gives
`g(a)=c^2`. Positivity and injectivity of squaring on nonnegative reals recover
`-Re y(log a)=c`. Unit norm and positive imaginary part then identify every upper-left target from
its real coordinate.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityKreinEigenlineQuadrantSurjectivity.lean`.

Main theorems:

- `fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_neg_re_sq`
- `fzzCigarParityKreinFermiRatio_log_eq_algebraic`
- `fzzCigarParityKreinEigenlineAlgebraicRadialSq_le_four_div`
- `exists_pos_fzzCigarParityKreinEigenline_neg_re_eq`
- `exists_pos_fzzCigarParityKreinEigenline_eq_of_unit_upperLeft`
- `exists_pos_fzzCigarParityKreinEigenline_eq_iff_unit_upperLeft`

Verification: direct `lake env lean` passed; target-only `lake build
GaloisForLFunctions.RHTower.FZZCigarParityKreinEigenlineQuadrantSurjectivity` passed (9760 jobs);
all audited endpoints report only `[propext, Classical.choice, Quot.sound]`.

## Literature and corpus novelty audit

Mandatory corpus searches covered FZZ phase range, parity/Krein eigenlines, Fermi ratios, and
nonlinear interaction channels. No prior corpus theorem computed this scale image or proved its
surjectivity.

Primary-source searches checked the exact cigar reflection/density framework in Ikhlef,
Jacobsen, and Saleur, *An integrable spin chain for the SL(2,R)/U(1) black hole sigma model*
(arXiv:1109.1119); the semiclassical cigar analysis of Jafferis and Schneider
(arXiv:2004.05223); and general Krein/pseudo-Hermitian spectral formulations in Mostafazadeh
(arXiv:quant-ph/0606173), Blasi--Scolarici--Solombrino (arXiv:quant-ph/0310106), and
Feinberg--Riser (arXiv:2109.09221). Within those searched sources, no coefficient-faithful theorem
identifies this Fermi-ratio eigenline image with an exact unit-circle quadrant. Novelty claim is
bounded to corpus plus these searches as of 2026-08-28.

## Gates

- [x] 0 -> 1: corpus-derived, source-pure, exact analytic attack
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: unconditional Lean theorem, target build, axiom audit
- [ ] 3 -> 4: standalone publication draft

## Remaining burden

Linear incidence remains cofinally incomplete by F13. HC23 supplies exact input for HC24: test
whether the first nonlinear interaction degree fills the missing right half-circle.

## Log

- 2026-08-28 — conjectured from F12/F13 corpus boundary
- 2026-08-28 — paper proof closed via exact algebraic Fermi ratio and IVT
- 2026-08-28 — formalized, wired, target-built, and axiom-audited
