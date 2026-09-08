# HB complete continued cusp-source admission — verified; RH unproved

Full chain: literal theta cusp → Xi occurrence → retained spin-two source → original causal response and physical left-QNM pairing → independent Hawking-clock extinction → RH. Goal remains active and unproved. Frontier map READ ONLY; did not edit it or universal STATUS. Other agents/tasks changed both concurrently; preserve their work. No subagents authorized, no experiments run.

## Closed result

Paper/current result: docs/drafts/pipeline/3-formalized/hb-complete-continued-cusp-source-admission.md.
Active proof card: docs/drafts/pipeline/1-in-progress/hb-qnm-parameter-continuation.md, replaced with current state and concrete next attack.

The actual continued cusp residual is L² on radialMeasure.prod D4BMModularCore.measure for nonreal w, -2 < w.re ≤ 0. This is the complete residual AFTER subtracting the explicit full-square/principal field, not admission of the unrenormalized original angular source. All three cutoff commutators retained. Exact equality to original residual/field in original source convergence chamber. Actual full wave equation with actual radial derivatives and metric angular Laplacian holds on one punctured frequency neighborhood. At both fundamental QNMs of every Xi copy, the same neighborhood has actual full residual L² admission. No supplied source-admission, endpoint-growth, continuation, nonresonance, or RH premise in all-Xi capstone.

Canonical leaves (all prefixed GaloisForLFunctions):
HTGeometry.HorizonEnergyGronwall, ComplexDichotomyEnergy, ForcedSecondOrderHorizonBound.
RHTower.ThetaCuspHawkingBMJointSourceTortoiseContinuation, PrincipalContinuation, FullForcingContinuation, ContinuedFieldWave, PrincipalHorizonBound, ContinuedAdmission, ContinuedSourceGerm (expand full prefix for every RHTower leaf).

Key namespace RHTower.D4BMJointSource:
continuedOnset s w = 1/(w-2s)+onsetCorrection (2s) w.
continuedTortoiseGreen w chi s a J K t = continuedResponse s chi a J K (horizonCoordinate t) w.
continuedPrincipalDifference q branch w a i t = continuedTortoiseGreen(...)-radialLift(s,w,a,continuedOnset s w,t)*principalAmplitude q i. First/Second actual jets retained.
continuedCutoffRadialCoefficient = (horizonCoordinate t:ℂ)*continuedPrincipalDifference.
continuedCuspResidualForcing = reducedCoefficient(s,w,a,continuedOnset s w)*squareResidual + sum all 3 cutoffCoeff*cutoffCommutator.
continuedExplicitField = radialLift*fullSquarePotential + sum all 3 principalDifference*cutoffPower.

Public capstones:
- continuedPrincipalDifference_equation: true ODE, nonreal w, -2<Rew, off connection zero.
- originalForcing_continuedField_germ: full original forcing = actual fieldWave continuedExplicitField + continuedCuspResidualForcing on common punctured neighborhood, ∀t<0,∀z:UpperHalfPlane.
- continuedPrincipalDifference_norm_le_exp q branch w a hw hwre hwr i: ∃C≥0,∀t<0, norm difference ≤ C exp(w.re*t), hwr:Rew≤0. Handles totalized connection-zero values directly as negative lift.
- continuedCutoffRadialCoefficient_norm_le_exp: gains two decay powers.
- continuedCutoffRadialCoefficient_memLp / continuedCuspResidualForcing_memLp: natural nonreal negative strip.
- continuedCuspResidualForcing_allXi_fundamental_memLp: both actual n0 physical frequencies every Xi q.
- continuedOriginalSource_admitted_germ: admission AND full original actual wave decomposition throughout one punctured neighborhood, requires only nonreal w,-2<Rew<0.
- continuedOriginalSource_allXi_fundamental_admitted_germ: unconditional all-Xi specialization, main capstone, ContinuedSourceGerm.lean:34.

## New hard estimate

Generic HTGeometry.forcedSecondOrder_horizon_bound uses actual U'=V and V'=w²U+pU-f on t<0, w≠0,Rew≤0, ∥p∥≤A exp2t, ∥f∥≤B exp((Rew+2)t), A,B≥0. Gives ∃C≥0,∀t<0,∥U∥≤C exp(Rew*t) with no endpoint condition.
Channels P=exp(-Rew*t)(U'+wU), M=exp(-Rew*t)(U'-wU); coupling G=exp(-Rew*t)(pU-f). Actual E'= -4 Rew ∥M∥²+2Re(G(conj P+conj M)). Derived lower bound -C exp2t(E+1), upper K(E+1). Integrating factors compare with t=-1 in both directions to control entire Iio0. Apply DIRECTLY to actual principal DIFFERENCE; separate moment estimates lose cancellation.
Actual potential p=-(horizonCoordinate:ℂ)*m(m-1), norm≤4∥m(m-1)∥exp2t via exact hcoordfactor. Actual source f=reducedCoefficient*principalAmplitude. Existing reducedCoefficient_frequency_horizon and sourceHorizonProfile_continuousOn supply decay; existing reducedCoefficient_memLp_horizon already admitted native term, reused. At a connection zero normalized moments vanish by totalized division; direct compact lift bound gives point admission, not pole removability. Final germ avoids all three connection zeros using their previously proved isolated-zero theorem.

## Next concrete obligation, still OPEN

Pointwise meromorphy + L² membership at each frequency is NOT L²-valued meromorphy. Clear exact shared denominators with explicit numerator formulas, not radius-dependent guessed pole orders. For channel i use c_i=connection(w,principalFrequency q i), S(w)=1+(w-2s)*onsetCorrection(2s,w). Away from zeros, -(w-2s)c_i U_i is undivided Green numerator plus cleared lift. Define this numerator directly: N*firstEndpointMellin*S + H*outerIntegral*S + c_i*S*(lift with T=1)*J. Multiplication of the totalized quotient at a pole can give 0 instead of analytic limit, so use explicit undivided expression at center. Its spatial ODE and source are inherited/extended, all local frequency ingredients already in corpus.
Bound numerator U and first jet at t=-1 uniformly on compact frequency disk. Source profile jointly continuous on disk×Icc0 1 has common bound; disk strictly inside -2<Rew<0 and away from0 gives common positive decay margin. New energy formula then supplies uniform L² majorant. Establish complex local L² holomorphy (not yet done). Existing HTGeometry.L2DominatedContinuity, L2DominatedDerivative (REAL parameter only), CauchyDominatedIntegralHolomorphy are useful. Wider OR searches followed by AND Lp holomorphic/analytic, outgoing resolvent, weighted Fredholm, causal continuation found no existing ready BM joint outgoing continuation producer.
Then genuinely continue ORIGINAL causal joint response in appropriate outgoing weighted domain and identify physical advanced/adjoint left residue. Opposite-half-plane energy inverse does NOT identify causal sheet. Pole survival, physical source projection, spin-two/AIME identification and independent Hawking-clock extinction still open. Higher overtones require additional endpoint Taylor subtraction orders.

## Audit / efficiency

10 canonical individual foreground lake build <module> audits in isolated package reusing 4053 own-tree dependency oleans; exactly10 new oleans,979 source lines,40 new public theorems. All40 #print axioms checks only propext,Classical.choice,Quot.sound.20 installed olean/ilean artifacts byte-match audit; source bytes match too. Umbrellas appended once; never built. One harmless ring tactic info at ForcedSecondOrderHorizonBound:109; build passed, do not repeat checks merely for it. No other prior theorem axioms rechecked.
Index refreshed once. Global lint --check-generated exit1 ONLY for concurrent unrelated unwired RHTower.SelbergCompactTestApproximation plus existing large-file warnings; no new-leaf errors/generated drift. Do not fix unrelated files or rerun all checks.
Owned scratch /tmp/hb-joint-continuation.ZNjWYY is to be removed after this memory is written; no owned Lean/Lake processes remain. Canonical modules/artifacts installed and wired. No commit/push. Preserve concurrent repository edits. Parent prior memory: `mem:hawking_bm_original_continued_radial_master_2026_09_08`.
