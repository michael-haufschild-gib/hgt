# EDQ joint fifth-word phase — verified checkpoint 2026-09-07

RH remains unproved/unfalsified; persistent goal stays ACTIVE. Current turn made verified progress. No external blocker, no route retired.

Full chain: Euler deletion -> exact complex zero balance -> signed arithmetic separation -> off-line exclusion -> RH. Pivot from prime-energy transport to chronological signature. Read JointPolygonMoment and continuing card, JointExponentialRemainder, ZeroLanding, NilpotentWitness, Sharpness; OneFifth through main block convergence. Actual zero landing is still only level one. Degree-four polynomial moment corresponds word length five, not degree-four signature.

## New complete leaf
formal/GaloisForLFunctions/RHTower/EulerDeletionJointFifthPhase.lean, 311 lines, namespace RHTower.DeletionJointSharpness. Imports JointProductSharpness, EulerDeletionPowerSumRemainder, ZetaPartialSumStrip, PrimeLogIncommensuratePhaseClock, EulerMascheroni. 12 public theorems, 1 public definition, 1 private linear readout. Wired into RHTower umbrella.

d_w(k)=weight w(6k) - sum_(j<6)weight w(6k+j)/6:
- strideCorrection_summable: sum norms finite for Re w>0, retains full averaging correction.
- stride_sum_decomposition: sum_(k<N)weight w6k = ordinary first6N sum /6 + sum d.
- fifthCoefficient_eq_weight: actual fifth coefficient = weight(5s)(6k)/60.
- tendsto_stride_sum_sub_power: for Re w>0,w!=1,
  sum stride - (6N)^(1-w)/(6(1-w)) -> zeta(w)/6 + tsum d_w.
- sourceProduct_power_asymptotic: exists actual corrected product limit V,
  actual first6N product + (6N)^(1-5s)/(360(1-5s))*topWord
  -> V - ((zeta(5s)/6+tsum d_(5s))/60)*topWord.
  Holds Re s>0,5s!=1; no zero premise.
- sourceProduct_scaled_limit: 0<Re s<1/5 ->
  (6N)^(5s-1) smul actual first6N product -> -1/(360(1-5s))*topWord, nonzero.
- sourceProduct_not_convergent_of_re_lt: full complex divergence below boundary.
- tendsto_stride_sum_sub_log: w=1, subtract log(6N)/6 -> EulerGamma/6+tsum d_1.
- sourceProduct_log_asymptotic: actual s=1/5 product + log(6N)/360*topWord -> V-((EulerGamma/6+tsum d_1)/60)*topWord.
- six_nat_cpow_not_convergent: Re z=0,z!=0 -> (6N)^z cannot converge. Norm of putative limit1; comparing all dilations pN forces p^z=1. PrimeLogIncommensuratePhaseClock.two_three_injective forces Im z=0.
- sourceProduct_not_convergent_on_complex_boundary: Re s=1/5,5s!=1; linear top-entry readout extracts counterterm from difference of convergent sequences -> contradiction.
- positive_halfPlane_convergence_iff: unconditional subtype theorem for EVERY Re s>0, actual full source products converge iff Re s>1/5. Includes real and all oscillatory boundary cases. Existence above line already gives unit in arbitrary Banach target. This fixed target shows sharpness.

No independent zero-specific signed comparison obtained. Sharp convergence boundary remains nonselective on whole right half of critical strip. Finite positive polygon moment cannot silently become complex weighted orientation.

## Audits — DO NOT REPEAT OR REBUILD
Final scratch session18933 exit0 no diagnostics.
Final leaf build23101 exit0; ONLY new leaf built3.9s, other8700 jobs cached/replayed. No umbrella/full builds.
Axiom21009 exit0; all13 new public declarations std propext/Classical.choice/Quot.sound only; private readout in their closure. /tmp scratch sources deleted.
Lint8737 exit1 solely12 concurrent unwired modules:
RHTower.ThetaCuspSecondAtomAllMoments, ThetaCuspTwoAtomExponentialAdmission, ThetaCuspTwoAtomOddProfiles, ThetaCuspTwoAtomOddReserves;
HTGeometry.LogarithmicLaplaceMiddleAbsoluteBounds, MiddleHankelPerturbation, TwoAtomMiddleEntryBounds, TwoAtomMiddleHighEntries, TwoAtomMiddleLowEntries, TwoAtomOddAlgebra, TwoAtomOddHighReserve, TwoAtomOddLowerReserve.
Do not modify concurrent files or claim global lint passed. Existing size warnings.
Index72415 exit0 ONCE,10 changed0removed. Scoped diff whitespace check passed.
All check/build/axiom/lint/index handles terminal. Logs retained /tmp/edq_fifth.api.log,.check.log,.build.log,.axioms.log,.lint.log,.index.log. Scratch /tmp/edq_fifth.lean and /tmp/edq_fifth_axioms.lean deleted.

## Docs
3-formalized/edq-joint-fifth-phase-asymptotic.md contains dependency-closed proof, complete complex boundary proof, certificate/audit. In-progress temporary card moved there.
Frontier line46 and EDQrow updated CURRENT state.
STATUS appended MUST-RETAIN-OSCILLATORY-BOUNDARY, route-independent bounded-oscillation vs convergence and finite correction.
Continuing polygon card and prior joint-product-sharpness certificate link successor.

## Possible next work (not a proved claim)
Need actual zero-specific relation, not another convergence wrapper. Investigate relation of top word XXYYY to full weighted polynomial circulation at simultaneously closed deletion endpoints. Finite unweighted circulation integral x*y^3 dx=1/10 and frozen topword=-1/60 agree with a -1/6 factor. Establish exact weighted finite endpoint formula from actual matrix source and all endpoints before using zero closure; no sign is implied by this algebra. Corpus all finite words/carry and level-one zero landing may help. User requires corpus starting point, no numerical evidence, one owned foreground Lean at a time, scratch only then one leaf build, no repeated old axioms. No subagents authorized.