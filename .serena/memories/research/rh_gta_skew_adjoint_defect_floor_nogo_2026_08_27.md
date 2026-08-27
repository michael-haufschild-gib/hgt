# GTA-PQ4-SAD skew-adjoint producer no-go (2026-08-27)

Frontier map is read-only; it was not modified.

## Result
For actual corrected theta stages M_k, the coefficient-only skew-adjoint energies
A_k = ||M_k - M_k^H||_HS^2
converge exactly to
A_inf = ||(-thetaKernelMatrix) - hsAdjoint(-thetaKernelMatrix)||_HS^2 > 0.
Thus ThetaSourceSignedStageSkewAdjointEnergyCofinallySmall is false, even though the corpus theorem shows it would imply RH.

Strict positivity is source-side: on pinnedCoordinate c(t)=t,
< c, thetaKernelOperator c > = -i ∫ q(t) t^2(1-t)/2 dt,
and the real integral is strictly positive. Hence thetaKernelOperator is not ordinarily self-adjoint.

Finite support proves exact stage equality with the kernel anti-Hermitian energy. Adjoint is an HS isometry, giving
||(K_k-K_k*)-(L-L*)||_HS <= 2||K_k-L||_HS -> 0,
then exact squared-energy convergence and eventual A_k > A_inf/2.

## Lean
- formal/GaloisForLFunctions/HTGeometry/FiniteMatrixSchurQuarticSkewAdjointDefect.lean
- formal/GaloisForLFunctions/RHTower/HedenmalmThetaSkewAdjointDefectCriterion.lean
- formal/GaloisForLFunctions/RHTower/HedenmalmThetaSkewAdjointDefectFloorNoGo.lean
- wired into formal/GaloisForLFunctions/RHTower.lean
- direct lake env lean and targeted lake build pass
- #print axioms: only propext, Classical.choice, Quot.sound

## Card
Moved to docs/drafts/pipeline/5-failed/theta-schur-quartic-skew-adjoint-source-criterion.md.
Type: FALSIFIED (producer); THEOREM (Lean) positive survivor.

## Novelty
No exact literature match found as of 2026-08-27. Hedenmalm arXiv:2606.17494 concerns a different theta differential pair-self-adjointness construction; general HS finite approximation is classical. Novelty remains UNVERIFIED pending expert review.

## Audit caveat
formal_tools.py lint sees this module reachable and no forbidden declarations, but global lint exits 1 because concurrently added unrelated unwired modules (MatomakiTeravainen, theta eighth-jet, and several HTGeometry files).