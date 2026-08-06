# Route E Gibbs parity–energy defect law (2026-08-06)

Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-e-gibbs-parity-energy-defect-jet.md`.
Lean: `formal/GaloisForLFunctions/RHTower/GibbsParityEnergyCovariance.lean`, wired into `GaloisForLFunctions.RHTower`.

## New exact source identity
For finite aperture S, normalized parity current psi=J/Z, and division-free parity–energy covariance numerator C:
- `hasDerivAt_normalized_gibbs_current`: psi'(x) = -C_S(x)/Z_S(x)^2.
- `gibbsScaleDefect_eq_integral_neg_covariance`:
  Delta_{S,p}(x) = Z_S(x) Z_S(px) * integral_{x}^{px}[-C_S(t)/Z_S(t)^2] dt.
This upgrades cycle-21's opaque defect into an exact accumulated covariance statistic; it does not bound it.

## New defect jet / no-go
For nonempty S:
Delta'_{S,p}(0) = (p-1) 2^{|S|} (-1)^{|S|+1} product_{q in S}(q-1).
For natural prime apertures it is positive at odd |S| and negative at even |S| (Lean corollaries proved). Therefore uniform sign-definite covariance, monotone prime insertion, and termwise-positive defect-production strategies are false. Fixed-volume Taylor estimates are nonuniform because the coefficient grows rapidly.

## Current exact Route E frontier
Route E remains OPEN. Best Gibbs route:
finite moving aperture + exact insertion recurrence + covariance integral -> prove one missing **cofinal signed covariance accumulation theorem** giving |J|/Z <= x^(1/2-o(1)) -> existing tail bridge and strict-half consumer -> RH.
MR/Littlewood controls fluctuations after subtracting the coherent mean, so cannot prove this source. The R_X^gr Hall route and charged operator seam remain separate alternatives, both open.

## Verification
- direct `lake env lean`: pass, no warnings.
- targeted `lake build GaloisForLFunctions.RHTower.GibbsParityEnergyCovariance`: pass 8658/8658; no full build.
- axiom audit capstone/jet/sign corollaries: only propext, Classical.choice, Quot.sound.
- no stale Lean/lake processes.
