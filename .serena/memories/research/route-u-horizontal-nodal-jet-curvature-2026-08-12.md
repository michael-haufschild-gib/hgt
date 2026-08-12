# Route U horizontal nodal jet curvature (2026-08-12)

Formal module:
`formal/GaloisForLFunctions/RHTower/XiShiftedHorizontalNodalJetCurvature.lean`

Stage-3 card:
`docs/drafts/pipeline/3-formalized/route-u-horizontal-nodal-jet-curvature-law.md`

Main unconditional Lean theorems:
- `iteratedFDeriv_xiShiftedHorizontalPolynomialEnergy_zero`: for every real w, polynomial P, and j, the j-th diagonal jet at u=0 of the shifted-Xi Padé normal energy based at y=exp(w) is
  (-1)^j (2 deg(P)+1)^(rising j) L_y(P^2 X^j).
- `iteratedFDeriv_xiShiftedHorizontalPolynomialEnergy_succ_zero`: exact connection-free odd-cocycle jet hierarchy.
- `xiShiftedHorizontalPolynomialCurvature_eq_turan`: denominator-free curvature
  a E(0) E''(0) - (a+1) E'(0)^2
  equals a^2(a+1) times the actual weighted Route U Turan landing, a=2 deg(P)+1.
- `xiShiftedHorizontalPolynomialCurvature_one_eq_completedArithmeticLanding`: at base y=exp(1), same curvature equals the literal rational-Gamma-minus-von-Mangoldt completed arithmetic landing at w=sqrt(exp(1)).

Universal interpretation: moving nodal roots are denominator-cleared Mobius pullbacks of fixed spectral annihilators. Freezing coefficients creates admission connection debt; horizontal Mobius gauge absorbs it into odd exponent 2d+1. Remaining open core is sign of this literal scalar curvature for every nodal P=X^m prod(X-r), still RH-equivalent.

No computation was used. Direct `lake env lean` passed. Final targeted `lake build GaloisForLFunctions.RHTower.XiShiftedHorizontalNodalJetCurvature` passed (12123 jobs). Axiom audit for all six capstones: only propext, Classical.choice, Quot.sound. Module is umbrella-wired. Formal lint command hung amid concurrent repo activity and was terminated; owned-file placeholder scan and diff check passed.

Related memories: `mem:research/mass-shifted-nodal-adaptive-arithmetic-source-landing-2026-08-12`, `mem:research/mass_shifted_half_density_mobius_source_connection_2026_08_11`.
