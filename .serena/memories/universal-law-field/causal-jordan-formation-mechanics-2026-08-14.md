# Causal Jordan Formation Mechanics (2026-08-14)

Audited requested functional-equation packet action. Exact common-kernel construction was already Stage3-certified in `ConstitutiveFunctionalEquationPacketLift.lean`: split formation `mu tensor_k kappa`, lifted action recovers observer, applies measurable involution, regenerates latent history through same kernel; naturality, involution, KL isometry, Jeffreys isometry; capstone `involutiveFormationLift_informationNeutral`.

New exact mechanism formalized in `formal/GaloisForLFunctions/HTGeometry/ConstitutiveCausalJordanFormation.lean`, wired into `HTGeometry.UniversalLawField`:
- positive two-leg formation `(P,N)`;
- visible `P-N`, reserve `min(P,N)`, common delay `max(P,N)=|visible|+reserve`;
- strict fusion; exact reserve birth `c(x,y)=(|x|+|y|-|x+y|)/2`; cocycle identity;
- functional equation swaps legs and preserves reserve/common delay;
- common recovery factoring through visible coordinate is reserve-blind;
- reciprocal common-delay profile invariant under `q -> q^-1`;
- `BoundedReciprocalCommonDelay q iff q=1` for `q>0`;
- closed visible formation can retain arbitrary reserve.

Paper files:
- Stage2 `docs/drafts/pipeline/2-fully-proven/universal-law-field/causal-jordan-formation-mechanics/titchmarsh-jordan-formation-reserve-functional-equation-and-information-blindness-law.md`
- Stage1 programme `docs/drafts/pipeline/1-in-progress/universal-law-field/causal-jordan-formation-mechanics/field-programme.md`
- Stage3 certificate `docs/drafts/pipeline/3-formalized/universal-law-field/causal-jordan-formation-mechanics/causal-jordan-formation-algebra-and-reciprocal-common-delay-properness-formalized.md`

Honest collision: `SourceFormationHarmonicMechanics` already supplies literal Möbius positive/coherent refinement and bilateral energy selection. New delta is reserve composition + causal/recovery coupling + common-delay properness receiver, not new source refinement. Remaining selection gate: coefficient-faithful comparison from existing source refinement into causal/common-recovery doctrine plus proof physical formation admits one uniform common-delay budget. This premise is not supplied by FE/information neutrality.

Verification: direct Lean pass; leaf build 8658 jobs; UniversalLawField build 11864 jobs; axiom audit only propext/Classical.choice/Quot.sound. Global lint was run but red on unrelated concurrent unwired RHTower/HTGeometry modules; regenerated indexes afterward. No project axioms/placeholders in new module.