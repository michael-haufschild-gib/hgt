# Route PM: actual adjacent correlation, active drift, interior budget

Completed 2026-10-18. Four kernel-checked Lean leaves in formal/GaloisForLFunctions/RHTower:
- PMAdjacentDivisorCorrelation.lean
- PMAdjacentDivisorEuler.lean
- PMAdjacentDivisorSmallDamping.lean
- PMActivePairLogarithmicDrift.lean
All four are imported by RHTower.lean. Full paper proof/card: docs/drafts/pipeline/3-formalized/pm-active-pair-shifted-correlation.md. Retired estimate: docs/drafts/pipeline/5-failed/pm-uniform-active-pair-bound.md.

## Exact arithmetic result
Let u_s(n)=pmPowerDampedDivisorCoeff s n=prod_{p|n}(1-p^(-s)), alpha_s=(pmPowerDampedDivisorDensity s).re. For every s,t>0, the actual Cesaro mean of u_s(n+1)u_t(n) tends to H(s,t)=prod_p(1-p^(-1-s)-p^(-1-t)). This is not just a periodic/truncated model. Exported names: tendsto_pm_adjacent_divisor_mean, pmAdjacentDivisorDensity_hasProd.

Proof mechanism: first expand u_s(n+1) on a fixed progression d|n; coprime CRT gives density 1/(ad), and count/N <=2/a. Then expand u_t(n), using 0<=u_s<=1 and count(d|n)<=N/d for a second dominated convergence. Both majorants are absolutely summable for every positive damping; no L2 premise is needed. Coprime double series is reindexed through squarefree damped-Mobius convolution to its Euler product.

A=pmAdjacentArtinConstant=prod_p(1-1/(p(p-1))) satisfies 0<A<=5/12. H(e,e)/e ->0 and H(e,1+e)/e ->A as e decreases to 0. Names: tendsto_pmAdjacentDivisorDensity_self_div_parameter, tendsto_pmAdjacentDivisorDensity_shifted_div_parameter, pmAdjacentArtinConstant_pos_le.

## Route consequence
Let A_e=pmShiftedExponentSecondDensity e, C_e=pmPowerDampedSecondDensity e, and
kappa_e=pmActivePairLogDrift e=(A_e-C_e-H(e,1+e)+H(e,e))/2.
For P_e(T)=pmActivePredictableMartingaleSum e T+pmPredecessorPeakMartingaleSum e T,
P_e(T)/log T ->kappa_e for EVERY e>0. Moreover kappa_e/e ->1/4-A/2 >=1/24. Thus eventually near e=0+, kappa_e>e/48 and P_e(T)->+infinity. Both a bounded complete active-pair estimate and the bounded uncentered shifted-difference remainder in the existing 1/8+half-remainder bound are refuted. Names: tendsto_pmActivePair_div_log, tendsto_pmActivePairLogDrift_div_parameter, eventually_tendsto_pmActivePair_atTop, eventually_not_bounded_pmActivePair, eventually_not_bounded_pmUncenteredShiftedDifference.

Positive survivor: with v_e=pmPowerDampedDivisorVariance e, r_e=pmInteriorLogCounterterm e=v_e/2+kappa_e, exact finite identity
E=(V-v log T)+2(P-kappa log T)+2(I+r log T)
for E the complete discrete energy, V its diagonal, I the actual doubly-inactive Bezout interior. Unconditionally (I+r log T-E/2)/log T ->0. Also r_e/e ->(1-A)/2, in [7/24,1/2). Names: pmPowerDampedDivisorDiscreteEnergy_eq_log_renormalized, tendsto_pmInteriorLogCounterterm_energy_residual, tendsto_pmInteriorLogCounterterm_div_parameter, pmInteriorLogCounterterm_slope_bounds.
This fixes the required arithmetic interior cancellation coefficient. It does NOT prove bounded full energy or RH; control of the renormalized interior beyond this logarithmic identity remains open.

## Audits and scope
Each actual leaf passed lake --old env lean with its own emitted olean, sequentially in foreground, without warnings. All 22 exported theorems were audited by #print axioms in /tmp: only propext, Classical.choice, Quot.sound. No new axioms or unproved analytic premises. Scoped whitespace check passed. scripts/formal_tools.py index completed, updating three generated formal indexes and source search database.
Final global lint exited 1 on FOUR unrelated layout/registration issues: three arithmetic-positivity-theory leaves (FactorialCollarIrrationalityAndSpacing, RankOnePoleReadoutAndZeroNullspace, SourceRelativeSchurMarginAndPerturbationCalculus) not reachable from ArithmeticPositivityTheory; TransHorizonIncidenceMechanics.lean at package root. No finding concerns these four PM leaves. Earlier three BVI registration failures were resolved by concurrent work before final lint. These are session observations, not a claim about future global lint state.
Task forbade web/literature novelty checks, numerical experiments, old research-note reading, and frontier-map edits. No global literature novelty claim. Frontier map was left untouched; its PM narrative may not yet include this result.

Lean 4.32.2 note: literal Nat.Primes pair finsets caused instance-transparency rewrite mismatches; typed local p2/p3 bindings and Finset.prod_pair solved the finite 2,3-prime bound.