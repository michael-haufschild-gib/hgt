# Factorial Müntz uniform analytic repair (2026-10-18)

Goal remains unconditional RH in Lean; RH is NOT proved. This actual goal turn made progress: 26 new public theorems + 2 definitions in two verified leaves. No no-go route was newly retired.

## Actual source result
Namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar.
N=n+1, epsilon=sourceFactorialCollar N, F_n=factorialMuntzCompletion n, r_n=sourceFactorialRamp N, c_n=factorialMuntzBoundaryCoefficient n=1/(2 sqrt N).
G_n=factorialMuntzBoundaryCorrected n c_n.
T_n=factorialMuntzCorrectedTail n=1_(x<=0)G_n=G_n-r_n.

The actual source parameter bounds give epsilon>=sourceFactorialWidth N>=1/(15N). This removes the apparent collar dependence left in the prior turn:
K_n=factorialMuntzBoundaryError n<=12/sqrt N.
Also |factorialMuntzSum n t+1/2|<=12t for t>0.
The exact corrected tail satisfies
|T_n(x)|<=1_(x<=0)12 exp(3x/2)/sqrt N.

For EVERY complex s with Re s>-1, the actual tail readout is integrable and
integral |exp((s-1/2)x) T_n(x)| dx <=12/(sqrt N (Re s+1)).
Its integral norm obeys the same bound.
For a<=0, the readout over x<=a has norm <=12 exp((Re s+1)a)/(sqrt N (Re s+1)).
The actual corrected source readout is integrable on Re s>-1, including the negative polar parameter s=0. Its difference from the compact ramp readout is exactly the tail readout.
Tail readouts, and corrected-minus-ramp readouts, tend uniformly to zero on every ENTIRE closed half-plane Re s>=-1+delta, delta>0.

Define B_n(t)=factorialMuntzRegularizedSum n t=A_n(t)+(1/2)1_(0<t<=1).
It is measurable, globally bounded by21/2, vanishes above max(factorialMuntzSupport n,1), and |B_n(t)|<=12t on (0,1].
Its Mellin transform is differentiable on Re s>-1.
The corrected source readout equals Mellin(B_n)(s)/sqrt N exactly; hence the source integral itself is analytic on that half-plane.
The original readout plus c_n/s tends to the corrected s=0 readout as s->0 through Re s>0.
The exact residue statement is s*(original readout)->-c_n through that right-half-plane filter.

At a right-half-plane zeta zero rho, ramp readout norm <=c_n/|rho|+12/(sqrt N (Re rho+1)).
The already-proved corpus theorem RHTower.four_le_abs_im_of_zeta_zero gives |rho|>=4. Thus:
|ramp readout_n(rho)|<=13/sqrt N for EVERY right-half-plane zeta zero.
The literal compact-ramp readouts tend uniformly to zero on the whole nontrivial zero set, without a height cutoff or RH.
Uniform vanishing over infinitely many zeros DOES NOT justify exchanging the unweighted Weil zero sum.

## Files
formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzUniformTail.lean
- factorialMuntzBoundaryError_uniform
- factorialMuntzSum_boundary_error_uniform
- factorialMuntzCorrectedTail
- factorialMuntzBoundaryCorrected_sub_ramp
- factorialMuntzCorrectedTail_measurable, _abs_le
- factorialMuntzCorrectedTail_readout_integrable, _cutoff_norm_le, _integral_norm_le, _norm_le
- factorialMuntzBoundaryCorrected_readout_integrable_extended, _readout_sub_ramp
- factorialRamp_zeta_readout_boundary_bound

formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzAnalyticRepair.lean
- factorialMuntzRegularizedSum, _measurable, _abs_le, _small_bound, _support, _mellin_differentiableAt
- factorialMuntzBoundaryCorrected_readout_eq_regularized_mellin, _readout_differentiableAt, _readout_analyticOnNhd
- factorialMuntzCompletion_readout_regularized_tendsto, _readout_residue
- factorialMuntzCorrectedTail_readout_tendstoUniformlyOn
- factorialMuntzBoundaryCorrected_readout_sub_ramp_tendstoUniformlyOn
- factorialRamp_zeta_readout_uniform_bound, _tendstoUniformlyOn

Both imported exactly once in BiScaleUncertainty.lean. No existing Lean source proof was changed.

## Verification
Both final leaves passed direct lake --old env lean -j1 with -o. First leaf one harmless unnecessarySeqFocus warning; second log empty.
28/28 public declarations audited in /tmp/bsu-muntz-uniform-axioms.lean: only propext, Classical.choice, Quot.sound.
Narrow mathlib API probe passed. Three missing unchanged dependencies restored by direct leaf checks: ClampedExponentialRamp, SignedPrimePolarHarmonicCorrection, SignedPrimePolarFactorialLift; all exit0.
No private object snapshot/cache was created this turn. Checks used existing dependency objects; initial closure had133 pre-existing objects older than source timestamps. Not a fresh whole-tree build.
Index exit0 updated formal/LEAN_API.md, LEAN_GAPS.md, LEAN_OVERVIEW.md.
Lint --check-generated exit1: five unrelated unreachable modules:
BiScaleUncertainty.AffineFourierCorrelation
BezoutValuationIncidence.DilatedCellScalingAndSecondOctaveFermiJumpBridge
BezoutValuationIncidence.EndpointHaarCellDecompositionAndWitnessPronicTransfer
BezoutValuationIncidence.PowerDampedPronicMultiplicativityAndRoutePMBridge
BezoutValuationIncidence.ReturnWindowTwoMomentKernelsAndSharpZeroBlocks
No lint error names the two new leaves. Old two-error list from prior turn is stale.
Evidence /tmp/bsu-muntz-uniform-verification.json: source hashes, object freshness, imports, all28 axiom lists and latest process/gate exits.
Logs /tmp/bsu-FactorialMuntzUniformTail.log, /tmp/bsu-FactorialMuntzAnalyticRepair.log, /tmp/bsu-muntz-uniform-axioms.log, /tmp/bsu-uniform-index.log, /tmp/bsu-uniform-lint.log.
All owned compiler/search/gate processes terminal. No heartbeat increase, full/umbrella build, numerical experiment, web search, commit/push or dev server.

## Cards and next frontier
Formalized child docs/drafts/pipeline/3-formalized/factorial-muntz-uniform-analytic-repair-2026-10-18.md.
Parent docs/drafts/pipeline/1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md updated; stays active.
Child old 1-in-progress path removed.
README and frontier map not edited by this work.

Full-Weil domain/identity for the corrected source and quantitative transfer to the compact ramp remain OPEN. The correction jumps at0. Coupled margin B_n>=2 polarLoss_n+factorialWeilGramError n, all-source RW positivity and RH remain OPEN.

Source-inspected follow-up:
RHTower.WeilSpectral.archPoleEnergy_eq_re_W_add_abelPrimePairing (WeilPrimeBlindZeroSideIdentity.lean:139) proves the explicit formula when an actual ExpDecayTest is produced.
A concrete next construction is convolution of G_n with a compact smooth kernel. Use new exponential bound for integrability/decay, move derivatives onto the kernel, prove exact readout product by Fubini. This construction is NOT formalized yet.
Search /tmp/bsu-muntz-smoothing-followup-search.json found AllExpDecay.convolution in WeilPositivityCharacterSpanHalfSpace.lean. Source definition requires decay faster than EVERY exponential; our fixed 3/2 tail decay does NOT discharge it. Build a finite-rate smoothing theorem instead of silently using that lemma.
DecayBound.expDecayTest in WeilConeXiDivisibleBlindFamily.lean merely packages C2 + value/derivative exponential bounds; it does not produce them.

All four searches this turn completed without execution errors but semantic coverage not measured: /tmp/bsu-muntz-continuation-search.json, /tmp/bsu-muntz-pole-moment-search.json, /tmp/bsu-muntz-zero-height-search.json, /tmp/bsu-muntz-smoothing-followup-search.json. No exhaustive-search claim.

## Lean lessons
indicator_of_mem hx with hx:x<=0 inferred the wrong set; force (show x in Iic (0:Real) from hx) at EVERY occurrence. Same for notMem.
For membership ht:t in Ioi0, give htpos:0<t:=ht before abs_of_pos.
ring does not split inverses of products involving sums; use simp only [div_eq_mul_inv,mul_inv_rev] first.
An eventually equality written with forall-eventually may elaborate to underlying Exists; use Filter.EventuallyEq.symm he explicitly, not he.symm.
Finite-part endpoint -(1/2) versus -1/2 needs simp only [zero_sub,neg_div].
Uniform convergence limits may need Function.comp_def and BOTH mul_zero/zero_mul.
dsimp at hs fails if already reduced; use change -1+delta<=s.re at hs.
Generic scratch have:=@Name may need explicit universe levels .{0,0}.
