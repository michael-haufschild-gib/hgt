# CGL principal high-ordinate residue decay

- **ID:** cgl-principal-high-ordinate-residue-decay
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** Chen--Gupta--Li, arXiv:2507.08296v2, Section 12.1, equation (12.1)
- **Statement:** The principal zero-detector residue is bounded uniformly in conductor and strip abscissa by `(X+1) C |t|^N exp (-pi |t| / 2)`, hence is below every fixed threshold at sufficiently large ordinate.

## Goal
Close the high-ordinate half of CGL's sole principal Mellin-residue obligation with no RH, zero-density, or caller-supplied analytic premise.  Keep the genuinely separate low-ordinate principal zero census explicit.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `cglPrincipalRegularizedMellinFactor_at_principalPole_norm_le_polyExp`, targeted Lean check green, new declarations axiom-clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Use the exact residue identity already formalized in `ChenGuptaLiPrincipalContour.lean`.  Bound the finite Möbius detector at `1` by `X+1` and the principal Euler residue by `1`.  The delicate uniformity as `Re rho` approaches `1` is obtained from
`Gamma(1-rho) = Gamma(2-rho)/(1-rho)`: on `|Im rho| >= 1`, the denominator has norm at least `|Im rho|`, while `2-Re rho` lies in the fixed compact strip `[1,2]`.  Apply the corpus Gamma vertical-strip estimate there and polynomial--exponential decay for the threshold consequence.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** active

## Log
- 2026-08-23 — created in 1-in-progress after exact comparison with CGL Section 12.1; principal contour and residue identity already Lean-proved, high-ordinate quantitative decay selected as open theorem.
