ULF-RFDM-2 theta-Hasse KMS card completed and promoted from Stage 2 to Stage 3.

Lean module:
- formal/GaloisForLFunctions/HTGeometry/ThetaHasseKMSContinuousAssembly.lean
- wired into formal/GaloisForLFunctions/HTGeometry/UniversalLawField.lean
- wired into formal/GaloisForLFunctions/HTGeometry.lean

Stage-3 card/certificate:
- docs/drafts/pipeline/3-formalized/universal-law-field/reversible-formation-dilation-mechanics/theta-hasse-kms-execution-balance-fisher-fusion-law.md
- docs/drafts/pipeline/3-formalized/universal-law-field/reversible-formation-dilation-mechanics/theta-hasse-kms-execution-balance-fisher-fusion-law-formalized.md
The original Stage-2 card was removed with apply_patch.

Formal surface includes generic bounded tilted moments/means/covariance, differentiation under tilted integral, covariance positivity, continuous TV/entropy execution averages and exact source bounds, reflected gap monotonicity/center uniqueness, intrinsic-image homeomorphism/properness, covariance/variance/Cauchy–Schwarz/Popoviciu, exact Fisher constants THK.37/38, exact half-line sinh reflected formula THK.29, common-recovery marginal/reflection/KL composition, normalized characteristic/Xi identity THK.33, source-averaged purity/Shannon conservation, and sigma=1/2 capstones.

Validation:
- direct `lake env lean GaloisForLFunctions/HTGeometry/ThetaHasseKMSContinuousAssembly.lean` passed after final capstones;
- targeted `lake build GaloisForLFunctions.HTGeometry.ThetaHasseKMSContinuousAssembly` passed before four tiny final capstones; it unexpectedly traversed a large cached Fourier dependency cone, so do not rerun;
- all created declarations, including final capstones checked source-identically, have only `[propext, Classical.choice, Quot.sound]`;
- lint reported only unrelated concurrent unreachable modules; this module was umbrella-reachable and had no forbidden declarations.
All THK scratch files were deleted. Do not re-audit or rebuild this module.