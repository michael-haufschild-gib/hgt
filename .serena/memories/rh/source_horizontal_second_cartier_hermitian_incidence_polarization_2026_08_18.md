# Xi-selected nonlinear Hermitian incidence polarization (2026-08-18)

Formal module: `formal/GaloisForLFunctions/RHTower/SourceHorizontalSecondCartierHermitianIncidencePolarization.lean`.

Construction:
- Pointed Krein jet `w=(u,a,b)`; invariant `I(w)=u * star(a+b)`.
- Nonlinear shell `P_c(v,w)` is parent linear relation `R_c` plus `I(w)=2*star c`.
- Under transfer, `u -> lam*u`, `a+b -> (star lam)⁻¹(a+b)`, hence `I` is invariant for every `lam != 0`.
- Shell admits forward `(2,c,0)`, inverse `(2,0,c)`, ghost `H_c=(1,c,c)`, and negative ghost `-H_c`.
- For `c(v1+v2) != 0`, unique anchor is `2*star c / star(c(v1+v2))`.
- For `c != 0`, shell contains opposite points but not zero, so is nonadditive and cannot be any complex submodule.
- `[H_c,H_c]=2c+2star(c)`; actual Xi scale is positive real, so selected square has positive real part.
- Actual capstone preserves prime transfer and exact Xi support multiplicity.

Key theorem: `sourceHorizontalActualXiSecondCartierKreinHermitianPolarization_capstone`.
Verification:
- direct production `lake env lean` passed;
- exact leaf build passed: `lake build GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierHermitianIncidencePolarization`;
- axiom audit only `propext`, `Classical.choice`, `Quot.sound`;
- module wired into `RHTower.lean`.
Research card promoted to `docs/drafts/pipeline/3-formalized/source-horizontal-second-cartier-hermitian-incidence-polarization.md`.
Frontier updated: former nonlinear-polarization core is closed. New core is source-natural two-sided orbit compactness/coercivity/order for this shell, or coefficient-faithful identification with literal endpoint contraction, excluding reciprocal hyperbolic escape. Bare shell remains invariant for every nonzero character and does not imply RH.
Novelty boundary: abstract opposite-weight product invariant is rediscovered; exact Cartier/Xi specialization is novelty-unverified.