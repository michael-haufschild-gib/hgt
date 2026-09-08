# HB full native cusp source projection — verified progress

RH remains unproved; goal active. Full chain: literal theta cusp → Xi occurrence → retained spin-two source → original causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

## User discipline
Frontier map READ ONLY; do not edit/revert others' modifications. One foreground owned Lean process. Scratch development with lake env lean; exact new-leaf final lake build using isolated cache-only package, no dependency/umbrella/full builds. Wire modules once. Audit only new theorem names, once. No subagents authorized, no commits/push. Experiments only if surprising and useful, short RunPod; none needed/run here.

## Verified exact result
Namespace RHTower.D4BMCuspProjection. Six new leaves under GaloisForLFunctions.RHTower.ThetaCuspHawkingBM:
CuspMeanCharacter(5), CuspPairedFourier(7), CuspSourceMean(7), CuspCutoffMean(5), CuspNativeSourcePair(2), CuspIndicialSelection(6) public theorems. All32 checked.
mean f = integral x in Ioc(-1/2)(1/2) f(x).
a_N(u,y)=D4BMAngularSeries.coefficient u 0 N * (Real.rpow y (1/2):Complex) * modifiedBesselKOrder(2*pi*(N+1)*y) u.
For y>0: sum ||a_N|| and sum ||a_N^2|| converge. Original tail = 2 sum a_N*(chi_(N+1)+chi_(-(N+1))). Mean tail0, mean tail²=mean squareRemainder=8 sum a_N², mean scalar²=P²+8 sum a_N². Full complex squares, NO conjugation/positivity. Absolute pair-index product majorant proves actual infinite sum/integral interchange.
For every actual Xi occurrence and branch, C(y)=original cutoffResponse(q,branch)(![0,y]), globally smooth. Full cutoff Laplacian=y² C''. Exact mean forcing=(L/2)*(P²+8 sum a_N²)-(y²C''-LC). Above y>3 mean forcing=4L sum a_N².
For every actual CuspHeightTest h in original operator domain:
inner h.operatorVector forcingVector = integral y>2 conj(h.field y)*mean(forcing(x,y))/y² dy, also explicit whole-source version. L2 integrability, original native-measure transport, cutoff support, exact density and Fubini are discharged.
PowerDensity p y=||y^p||²/y² is integrable y>2 iff Re p<1/2. Actual cusp powers y^(w+2),y^(-w-1) solve Delta f=(w+1)(w+2)f. Finite density iff Rew<−3/2 and Rew>−3/2 respectively. Original doubled physical rates w=2(rho−2) or2(−rho−1) satisfy−4<Rew<−2 for every Xi occurrence, independently of RH; first root finite, second not. This is density classification, NOT global-domain membership of noncompact powers or proof of retarded branch.

## Remaining hard obstacle
Derive original causal convergence chamber; continue its full forced response; compute source-dependent homogeneous cusp coefficient retaining compact modular scattering. Native mean alone does NOT identify global scattering coefficient. Physical gauge, SS/VV, actual left-QNM pairing and independent extinction remain open. Nonvanishing of complex sum NOT proved.
Corpus candidate: ThetaCuspHawkingBMEisensteinGenericMixedCasimirSourceLanding actualUnfoldedScalarSource_eq_positiveLambdaProduct evaluates factorized Whittaker/Bessel/Dirichlet expression for ReP>1,2ReP<ReQ. It does not itself identify actual native projection at Xi parameters or justify required continuation. Do not skip either bridge. BesselOrderLaplaceAsymptotic only order1, not arbitrary complex order; local arbitrary-order majorants and full-tail exponential decay exist.

## Audit and artifacts
All six scratch development checks and six exact canonical final lake builds passed, only requested new leaf compiled using cached imports in isolated package. Twelve olean/ilean copied to main cache and byte-verified. Single scratch #print axioms audit of precisely32 new public names: propext,Classical.choice,Quot.sound only. Six imports wired once, umbrella NOT built. index refreshed; scoped whitespace/import checks passed. lint --check-generated FAILED only unrelated concurrent RHTower.DivisorSourceEntire unreachable from umbrella, plus old large-file warnings. That file preexisted and was left untouched. No new Lean failure. Scratch /tmp/hb-cusp-projection.f7oPeq removed at end; no owned Lean/Lake process. No computations/experiments.
Docs: 3-formalized/hb-native-cusp-source-projection.md; live hb-cusp-spectrum-and-causal-continuation.md updated with actual source proof and remaining coefficient; hb-global-angular-resolvent.md stale spectrum sentence corrected; STATUS F20i-s complex quadratic vs Hermitian measure/pairing rule. Frontier untouched.

## Lean traps
integral_exp_mul_complex unqualified works with Mathlib.Analysis.SpecialFunctions.Integrals.Basic. integral_tsum_of_summable_integral_norm direction needs .symm. integrable_const takes value. mean_tsum and integral_add require explicit lambda Integrable type to avoid hidden Pi operations. Expand/reassociate products explicitly. integral_div exists, integral_div_const does not. Native chart integrability needs typed IntegrableOn before .mono_set. MeasurePreserving.integrableOn_comp_preimage with measurable embedding gives iff; beta-reduce using dsimp only before congr for setIntegral_congr_fun. Complex.ofNat_re/im do not exist; norm_num (without only) normalizes Re2. Power density rpow proof: rpow_sub, replace2*Re p by Re p*2, rpow_mul, norm_num. Git diff --no-index --check /dev/null newFile may return1 with empty output; that denotes difference, not whitespace failure.
