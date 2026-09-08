# HB principal causal evolution and cutoff-source transform

RH goal remains active and unproved. Frontier map is READ ONLY. No subagents, experiments, numerical certificates, commits/pushes, full builds or umbrella builds were used. No new route-independent STATUS law was added.

Proof card: docs/drafts/pipeline/3-formalized/hb-principal-causal-evolution-and-cutoff-source.md. Current active card: docs/drafts/pipeline/1-in-progress/hb-joint-causal-laplace-identification.md. Chain: literal theta cusp → Xi occurrence → retained spin-two source → original causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

## Closed batch

15 canonical leaves, 80 public theorems, 1019 source lines. Each leaf passed its individual `lake build <module>` audit in an isolated existing-cache-only package. Exactly the requested leaf compiled each time, without warnings; no old dependency or umbrella rebuilt. All 15 canonical sources and 30 installed .olean/.ilean artifacts byte-matched audit copies. Each leaf wired exactly once. A scratch `lake env lean` printed ONLY the 80 new public theorem axiom sets; every set exactly [propext, Classical.choice, Quot.sound]. Do not repeat these audits next turn.

Reusable GaloisForLFunctions.HTGeometry modules: VolterraCausalConstraints (4), L2SpatialReflectionMultipliers (5), L2NegativeHalfLineExtension (6), L2NegativeHalfLineRestriction (3), UnitWaveSine (7), UnitWaveDuhamel (4), UnitWavePotentialKernel (4), UnitWaveDuhamelDerivative (3).

Route module prefix GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSource, declaration namespace RHTower.D4BMJointSource: PrincipalWavePotential (8), PrincipalTimeForcing (8), PrincipalTimeResponse (8), PrincipalTimeLaplace (2), PrincipalTimeRegularity (6), PrincipalCutoffTime (6), CausalCuspSource (6).

## Exact mathematics and APIs

alpha=2*pi. The corpus kgFreq has sqrt(1+xi²), so unrescaled KG has spatial speed 1/(2*pi). `unitWaveSine tau = alpha^-1 • kgSinFreqOp(alpha*tau)` restores the original unit speed, with free mass alpha². Its norm is <=alpha^-1; derivative is kgCosOp(alpha*tau); it commutes with exact L² reflection. `unitWaveDuhamel F tau` is integral_0^tau unitWaveSine(tau-sigma)(F sigma). Continuous F gives continuity, actual cosine-convolution derivative and continuous derivative, plus exact spatial kgFreqInvOp range (`unitWaveDuhamel_freqInv`).

`negativeOddExtension` is a CLM from L²(volume.restrict(Iio 0)) to whole-line L². Norm <=2||f||, exact negative eigenvector of reflection, AE retention of the negative-ray source. `negativeRestriction` is contractive and its composition with odd extension is the identity. Generic Volterra support and commuting-constraint theorems apply to the actually constructed factorial solution.

`principalWavePotential q i t = alpha² + k_i(k_i-1)*horizonCoordinate t`, with original h=1-tanh²(t), globally in [0,1] and even. This is a bounded complex multiplier, not assumed self-adjoint. `principalTimeForcing q branch a i tau` is literal principalAmplitude q i times odd extension of the actual native timeRadialSourceVector. Proved continuous, causal, integrable on positive time, exact negative-ray AE function, odd, and its native Bochner transform for Re(w)>-2.

`principalTimeResponse` is the actual frequency-independent Volterra construction with this source and complex potential. `principalTimeResponse_duhamel`, `_unique`, `_continuous`, `_zero_of_nonpos`, `_reflection`, `_bound` proved without supplied analytic source/domain hypotheses. Bound B_i exp(M_i|tau|), M_i=alpha^-1||W_i||, B_i=alpha^-1 integral_0^infinity||F_i||. It permits growth, NOT extinction.

`principalEffectiveForcing=F_i+W_i U_i`. `principalTimeResponse_convolution`, `_hasDerivAt`, `_deriv_continuous`, `_initial_data` prove one physical convolution, C¹ time evolution and zero value/velocity. `_freqInv` gives U_i=kgFreqInvOp[alpha^-1 integral sin(alpha*(tau-sigma)*Lambda) G_i(sigma)]. This is one spatial inverse-frequency gain; no pointwise trace is inferred from L² oddness.

`principalTimeResponse_laplace_integrable` holds Re(w)>M_i. `principalTimeLaplace` is its actual Bochner integral and is odd there. `principalCutoffRadialOp` retains the literal horizon multiplier then negative-ray restriction. `principalCutoffSpatialOp` tensors this with actual cutoffCommutatorVector(k_i). `principalCutoffTimeVector` is continuous, causal and admits the exact CLM/Bochner transform interchange.

`causalPrincipalThreshold q=1+sum_i M_i` is positive and greater than every M_i. `causalCuspSourceVector= timeCuspMainVector + sum_i principalCutoffTimeVector_i` is one continuous causal source in ORIGINAL joint spatial L². In Re(w)>threshold, norm integrability and `causalCuspSourceVector_laplace` give exactly cuspMainLaplaceVector + sum_i principalCutoffSpatialOp_i(principalTimeLaplace_i).

## Remaining hard obligation and specific next construction

NOT proved: negative-ray principalTimeLaplace equals existing `principalDifference` at T=onsetTransform(2*s,w). Original second-order radial PDE and endpoint trace must first be identified. Therefore the assembled transform is NOT yet identified with cuspResidualVector. Original complete-source joint convolution, left-QNM continuation and retained spin-two/AIME pairing, and independent Hawking-clock extinction remain open. These 80 theorems impose no Xi-zero location constraint.

Next direct target: prove native forcing's time derivative continuous in original L² using actual onset derivatives and horizon coefficients. Then G=F+WU is C¹. Bounded integration by parts with A^-2 cos(A*tau), A=alpha*Lambda, gives paper target U(tau)=A^-2[G(tau)-cos(A*tau)G(0)-integral_0^tau cos(A*(tau-sigma))G'(sigma)]. That gains TWO spatial inverse-frequency factors and exposes original second-order equation. This upgrade is a paper derivation ONLY, not a Lean theorem yet. Source chamber Re(w)>-2 cannot be used to continue response inverse.

## Verification/hygiene

Generated indexes refreshed; final generated freshness check passed. Repository lint --check-generated has 141 existing large-file warnings and one unrelated unreachable module error: HTGeometry.BistochasticMixingMajorization. Concurrent SelbergMaassCuspDecay and umbrella edits were preserved. No new leaf flagged. Owned scratch /tmp/hb-principal-causal.HeMbYW and isolated audit directory were removed. All 30 installed artifacts remain; no owned Lean/Lake process remained. Frontier untouched.

## Lean details that save time

For integral-congr goals with beta redexes, use explicit `change` before rw. For IntegrableOn.add over SpatialSpace, `.congr` with an explicit pointwise equality avoids the norm-instance diamond that `simpa` fails to resolve. Use current `continuous_finsetSum`/`integrable_finsetSum`/`integral_finsetSum` (snake_case sum names deprecated). `map_smul_of_tower` does not exist here: restrict a complex CLM to real scalars before rewriting its real-scalar action. Put CompleteSpace section variables only before the two generic Volterra theorems needing them; doc comment followed by `omit` is invalid syntax. Canonical audit new lean_libs must have explicit roots and default globs: `globs=[]` would build an empty library. Cache-only dependency stubs intentionally use globs=[] and expose absolute existing lean cache directories.