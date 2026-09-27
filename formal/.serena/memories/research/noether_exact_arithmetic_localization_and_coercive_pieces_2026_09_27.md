# Exact full arithmetic localization and concrete coercive pieces

## Goal and status
Active goal remains RH proof via arithmetic conservation/Noether and conjecture loops. RH is neither proved nor falsified. This turn made verified progress; no goal blocker. Do not mark complete. User requires no added axioms/sorry, no numerical experiments, no heartbeat changes, one own foreground leaf build at a time, `lake --old env lean` final audits, fresh oleans for imported leaves, umbrella wiring but no umbrella/full builds. Preserve other chats' edits.

Repo `/Users/michael/Documents/code/hgt/formal`. Prior context: `mem:research/noether_small_measure_coercivity_explicit_support_gap_2026_09_27`, `mem:research/noether_full_weil_modulus_obstruction_2026_09_27`.

## Six new finished leaves (all namespace RHTower)
All individually audited with `lake --old env lean GaloisForLFunctions/RHTower/<Leaf>.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Leaf>.olean`, final exit 0 and no warnings. All wired into RHTower.lean lines 19718–19723 at audit time; MainTheorems already imports RHTower.

### CCMThetaSmoothLocalization
For arbitrary actual `u : CCMComplexSmoothInteriorSource a` and real Schwartz `theta`:
- `ccmCosLocalizedSource u theta`, `ccmSinLocalizedSource u theta`: pointwise cos(theta)*u and sin(theta)*u. Smooth compact strict-interior at same aperture, no extra premises.
- `ccmThetaGroundProfile_cosLocalized`, `_sinLocalized`: same multipliers after dividing by positive theta ground state k.
- `thetaLocalizationWeight theta x y = (cos(theta y)-cos(theta x))²+(sin(theta y)-sin(theta x))² = 2*(1-cos(theta y-theta x))`.
- Weight nonnegative and <=4.
- `thetaLocalization_increment_identity`: for complex z,w,
  |cy*z-cx*w|²+|sy*z-sx*w|²-|z-w|² = W(x,y)*Re(z*conj w).
- `thetaGroundNormSq_localization`, `ccmPhysicalMass_localization`: exact mass conservation under split.

### CCMThetaArithmeticLocalization
Literal physical-source correction (ground k cancels exactly):
- `ccmThetaLocalizationCross u theta x y = W(x,y)*Re(u(y)*conj(u(x)))`.
- `ccmThetaGroundProfile_cross` proves k(x)k(y)*Re(profile(y)*conj(profile(x))) = physical correlation.
- `ccmThetaWeightedIncrement_localization` weighted complex increment identity.
- Prime error density on counting*volume: Lambda(n)/sqrt(n)*Cross(x,x+log n).
- Continuous error density on positive-shift*volume: mu(h)*Cross(x,x+h), mu=thetaGammaPolarScalingKernel=2cosh(h/2)-exp(-h/2)/(1-exp(-2h)).
- Both `integrable_ccmThetaPrimeLocalizationDensity` and `integrable_ccmThetaContinuousLocalizationDensity` proved unconditionally from actual convergent energies, via density difference identities.
- Errors `ccmThetaPrimeLocalizationError`, `ccmThetaContinuousLocalizationError` are literal integrals.
- `ccmRestrictedWeilSourceQuadratic_localization` (line168 at audit):
  Q(u)=Q(cos(theta)u)+Q(sin(theta)u)-ErrPrime(u,theta)+ErrContinuous(u,theta).
  Holds for EVERY complex smooth source and real Schwartz angle, with no supplied IMS/convergence/positivity hypotheses.

### CCMThetaLocalizationCrossBounds
- `thetaLocalizationWeight_le_angle_sq`: W <= (theta(y)-theta(x))².
- `thetaLocalizationWeight_le_seminorm`: W <= D²*(y-x)² where D=SchwartzMap.seminorm R 0 1 theta.
- `abs_ccmThetaLocalizationCross_le`: |Cross| <= D²*(y-x)²*|u y|*|u x|.
- `ccmThetaLocalizationCross_eq_zero_of_aperture_le`: exact zero when 2a<=|h|, because both physical support values cannot be nonzero.
- `integrable_ccmSmooth_norm_sq`, `integrable_ccmSmooth_shift_norm_mul`.
- `integral_ccmSmooth_shift_norm_mul_le`: spatial absolute correlation <= actual physical L2 mass (2ab<=a²+b² + translation invariance).
- `integrable_ccmThetaLocalizationCross_shift`.
- `integral_abs_ccmThetaLocalizationCross_shift_le`: integral_x |Cross(x,x+h)| <= D²*h²*mass(u).

### CCMThetaContinuousLocalizationMoment
- `ccmThetaContinuousMomentDensity a h`: if h<2a then |mu(h)|*h² else0; integrated only over h>0.
- `ccmThetaContinuousLocalizationMoment a = integral_{h>0} density`.
- Integrability proved, not assumed: source-independent bound density <= exp(4a)*(2h²+h/2)*exp(-h/2), from existing thetaGammaPolar_damped_square_bound and h<2a.
- Moment nonnegative.
- `abs_ccmThetaContinuousLocalizationError_le`: |ErrContinuous| <= D²*Mcontinuous(a)*physicalMass(u).

### CCMThetaPrimeLocalizationMoment
- Prime moment density: Lambda(n)/sqrt(n)*log(n)² if n in Finset.Icc 2 floor(exp(2a)), otherwise0.
- `ccmThetaPrimeLocalizationMoment a`: literal finite sum of those weights, nonnegative.
- Integrability for counting measure, integral equals finite sum.
- `ccmThetaPrimeLocalizationDensity_eq_zero_outside`: exact prime cutoff, n=0,1 via vonMangoldt, others via aperture separation.
- `abs_ccmThetaPrimeLocalizationError_le`: |ErrPrime| <= D²*Mprime(a)*physicalMass(u).
- `ccmRestrictedWeilSourceQuadratic_localization_lower_bound` (line117):
  Q(cos(theta)u)+Q(sin(theta)u)-D²*(Mprime(a)+Mcontinuous(a))*mass(u) <= Q(u).
  Fully unconditional endpoint on actual arithmetic source, no modeled second moment or assumed IMS identity.

### CCMThetaLocalizedCoercivity
Concrete cutoff infrastructure linking previous explicit small-support coercivity to localization:
- `ccmTinyLocalizationBump a L c`: ContDiffBump centered c, inner radius delta(a,L)/8, outer delta(a,L)/4, where delta=ccmExplicitSupportThreshold.
- `ccmTinyLocalizationAngle a L c`: (pi/2)*bump as real Schwartz.
- `ccmTinyCosLocalizedSource_eq_zero`: complementary source zero on inner closed ball.
- `ccmTinySinLocalizedSource_eq_source`: local source equals original there.
- `ccmTinySinLocalizedSource_support_subset`: local source supported in outer open ball.
- supportMeasure <=delta (indeed <=delta/2).
- `ccmTinySinLocalizedSource_coercivity`: local piece v has L*mass(v)+(1/2)*formNorm(v)² <=Q(v), EVERY a,L,c,u, no support premise.
- `ccmRestrictedWeilSourceQuadratic_tinyLocalization_lower_bound` (line86 after fixes):
  Q(complement)+L*mass(local)+(1/2)*formNorm(local)² - D²*(Mp+Mc)*mass(u) <=Q(u).

## Interpretation and limits
This closes the actual-form localization infrastructure gap. Old IMSLocalizationWeilForm only proves scalar partition algebra and a lower bound assuming hIMS/hErr. Old IMSBootstrapObstruction uses a modeled second moment; it does not prove a universal obstruction to all exact signed arithmetic localization.
Our literal errors keep prime, Gamma and both pole contributions, arbitrary complex phases, and their correct signs. The absolute second-moment bound is rigorous but does NOT show local positivity gains dominate interaction cost. No all-aperture positivity or RH follows. Next meaningful target: exploit exact signed cancellation, or construct/prove sign obstructions for actual localization errors, then iterate source-specific partitions. Do not infer that continuity/mass conservation forces action positivity; it does not.
Prior modulus obstruction already gives an actual pair with Q(|u|)>Q(u) under all local potentials. It might help build smooth-separated examples showing both signs of exact localization error. A compact smooth separator could be constructed from original explicit disjoint bumps or mathlib smooth Urysohn; not yet done. Avoid duplicating existing abstract finite Schur criteria.

## Validation / cleanup
- Six final leaf audits all green, fresh oleans, no warnings.
- Nine endpoint `#print axioms` audits all only `propext, Classical.choice, Quot.sound`.
- Scratch `work/noether_localization_axioms.lean` deleted and absence checked.
- No computations, #eval/native_decide, sorry, new axioms or heartbeat changes.
- Whitespace clean. Six umbrella imports each present once.
- Guarded `formal_tools.py index` successful (0 changed/removed due concurrent indexing); generated docs refreshed.
- `lint --check-generated` reports only four unrelated concurrent unwired modules: MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroDensityPowerSaving. No own module or generated staleness errors. Do not wire their unfinished work.
- No own live Lean/index/lint process remains after this audit. No commit/push.

## Lean repairs worth retaining
- `theta.smooth` is a function; use `(theta.smooth top).cos/.sin`.
- Integral rewrite with lambda sums needs `Integrable.fun_add`, not `.add`, when rw otherwise fails to match Pi applications.
- HasCompactSupport of norm-square: bind explicit type first:
  `have hc : HasCompactSupport (fun x : R => norm(u x)^2) := u.hasCompactSupport.comp_left (g := fun z : C => norm z^2) (by simp)`.
  Trying apply-then-infer on a Pi power produced a whnf heartbeat timeout; explicit function avoids it without heartbeat changes.
- `integral_add_right_eq_self` sometimes needs explicit function `(fun x : R => norm(u x)^2)` and shift.
- Measurable ite: `Measurable.ite measurableSet_Iio (by fun_prop) measurable_const`; fun_prop alone did not handle ite.
- Count outer integral syntax MUST parenthesize inner integral: `integral n, (integral x : R, f(n,x)) dMeasure.count`.
- `measure_mono` needs explicit `volume` inequality type when both measures otherwise unresolved.
