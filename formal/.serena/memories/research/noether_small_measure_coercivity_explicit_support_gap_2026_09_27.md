# Small total support gives an explicit full arithmetic energy gap (2026-09-27)

Continuation of `mem:research/noether_full_weil_modulus_obstruction_2026_09_27`, `mem:research/noether_three_positive_energies_small_gap_kernel_orientation_2026_09_27`, `mem:research/noether_cut_conservation_exact_weil_ground_criterion_2026_09_27`.

RH remains unproved/unfalsified; goal active and completion only on formal RH proof. Prior turn was progress. This turn made verified positive arithmetic estimates, not just criteria/no-go results.

Repo `/Users/michael/Documents/code/hgt/formal`; other chats concurrently edit/index/build/commit. Do not touch their unwired leaves or processes. No subagents. No full/umbrella builds. Each final audit foreground `lake --old env lean Leaf.lean -o .lake/build/lib/lean/.../Leaf.olean`, one own build at a time. No new axioms/sorry/numerical experiments/heartbeat hacks.

## New mathematical mechanism

Originally targeting pairwise cross estimates for separated bumps. Found a stronger way to control every cross term together: actual Gamma form embedding J_a from form domain to physical L2 is compact, and full Q satisfies
`norm(u)_form^2 - M(a)*norm(J_a u)^2 <= Q_a(u)`
with existing explicit arithmetic envelope
`M(a)=abs(2*gammaHardyPhaseRate(0)-1)+4*a*exp(a)+42*exp(a)`.

A compact family in L2 has uniformly little mass on any measurable set of sufficiently small measure. Finite metric nets + finite-family uniform integrability prove this directly. Thus P_s J_a has arbitrarily small operator norm as volume(s)->0, uniformly over arbitrary geometry/disconnected sets. This gives full Weil coercivity on small TOTAL support, at EVERY fixed aperture, and uniform nonconcentration of all nonpositive states.

Then replaced the qualitative threshold for smooth sources with an explicit Fourier bound: L1^2 <= support_measure * physical_L2^2; hence Fourier(u)(xi)^2 <= support_measure * physical_L2^2 and low frequency mass in [-R,R] <= 2R*support_measure*physical_L2^2. The divergent exact Gamma weight supplies the remainder.

## Five new leaf modules, all final audited green, fresh oleans

1. `GaloisForLFunctions/RHTower/CCMCompactPhysicalConcentration.lean` (namespace RHTower)
   - `exists_smallSet_cutoff_norm_le_of_isCompact`: compact K: Set SoninL2, epsilon>0 => delta>0 all measurable s with volume(s)<=ofReal delta, all f in K, norm(indicatorCutoff_s f)<=epsilon.
   - Finite ball cover at epsilon/2, subtype finite T, `unifIntegrable_finite` for T, cutoff norm contraction.
   - `exists_ccmSmallSet_restriction_norm_le a epsilon`: norm(P_s.comp J_a)<=epsilon.
   - `exists_ccmSmallSet_mass_le a eta`: for eta>0 find delta>0 with norm(P_s J_a u)^2<=eta*norm(u)_form^2 for every form-domain u.

2. `CCMSmallSupportCoercivity.lean`
   - Imports prior leaf + existing CCMRestrictedWeilSourceAlignedFiniteBlock.
   - `exists_ccmSmallSupport_coercivity a L`: for any real L, delta>0 such that supported form vectors (P_sJ_au=J_au) with volume(s)<=ofReal delta satisfy
     `L*norm(J_a u)^2 + (1/2)*norm(u)_form^2 <= Q_a(u)`.
   - Choose eta=1/[2*(M(a)+abs L+1)], absorb (M+L) physical mass into half form norm.
   - `exists_ccmNonpositive_smallSet_mass_fraction a epsilon`: every Q_a(u)<=0 direction has local mass norm(P_sJ_au)^2 <= epsilon*norm(J_au)^2 on every sufficiently small measurable s. No support or smoothness assumption, works full form domain and controls mass ratios (no normalization needed).
   - `exists_ccmNonpositive_support_measure_floor a`: nonzero nonpositive form-domain state supported in s has volume(s)>ofReal delta for a uniform positive delta.

3. `CCMThetaSmallMeasureEnergy.lean`
   - Smooth-source/ground-energy transport, all actual complex CCM sources.
   - `CCMComplexSmoothInteriorSource.measurableSet_support`.
   - `indicatorCutoff_ccmSmooth_source_support`: restricting J_a u to literal Function.support u returns same L2 vector.
   - `norm_sq_indicatorCutoff_ccmSmooth`: local cutoff norm squared = integral_s norm(u(x))^2.
   - `exists_ccmSmooth_smallSupport_coercivity a L`.
   - `exists_smallMeasure_thetaThreeEnergy_gap a L`: delta>0; if total source support measure<=ofReal delta, then
     `Epole(u/k)+L*groundNormSq(u/k)+(1/2)*norm(u.toCCMFormVector)^2 <= Eprime(u/k)+EGamma(u/k)`.
   - `exists_ccmSmooth_nonpositive_localMass_fraction`: physical local integral version of uniform nonconcentration, RHS epsilon*groundNormSq.

4. `CCMSmoothSupportUncertainty.lean`
   - `ccmSmoothSupportMeasure u := (volume (Function.support u)).toReal` (finite since compact inside aperture).
   - `ccmSmooth_support_volume_lt_top`, nonneg measure.
   - `ccmSmooth_integral_norm_sq_eq_physical` identifies literal integral with J_a L2 norm squared.
   - `ccmSmooth_integral_norm_sq_le_supportMeasure`: (integral norm u)^2 <= measure(support u)*norm(J_a u)^2.
   - Uses Holder p=q=2 on restricted support measure, followed by real square-root squaring; all measures finite/integrability explicit.
   - `norm_fourier_ccmSmooth_sq_le_supportMeasure`: pointwise squared Fourier bound with exact Mathlib 2pi normalization.
   - `fourier_ccmSmooth_physical_coeFn`: unitary Fourier transform of physical embedding AE equals Fourier integral of source Schwartz.
   - `ccmSmooth_fourierWindow_mass_le_supportMeasure`: integral_{[-R,R]} norm(Fourier J_a u)^2 <= 2R*support_measure*norm(J_a u)^2 for R>=0.

5. `CCMThetaExplicitSupportGap.lean`
   - `ccmSmooth_formNorm_lower_supportMeasure`: for A>=0,R>0,A<ccmArchimedeanFormWeight R,
     `A*(1-2R*m(u))*norm(J_a u)^2 <= norm(u)_form^2`.
   - Proof: exact Fourier window+tail mass identity; low-frequency bound above; existing weighted tail budget.
   - `ccmSmooth_source_lower_supportMeasure`: full actual Q >= `[A*(1-2R*m(u))-M(a)]*norm(J_a u)^2`.
   - Definitions:
     `ccmExplicitSupportFrequencyRadius a L = ccmArchimedeanBudgetFrequencyRadius (4*(M(a)+abs L+1)) <1,positive>`.
     `ccmExplicitSupportThreshold a L = 1/(4*radius)`.
   - `ccmExplicitSupportFrequencyRadius_eq_exp` proves radius = exp(C*[4*(M(a)+abs L+1)+2]), with existing C=`ccmArchimedeanLogComparisonConstant`.
   - Both radius and threshold strictly positive.
   - `ccmSmooth_explicitSupport_coercivity`: m(u)<=threshold => L*norm(J_a u)^2+(1/2)*formnorm^2<=Q.
   - `thetaThreeEnergy_explicitSupport_gap`: same exact Eprime+EGamma-Epole statement as qualitative result, now explicit threshold.
   - `ccmSmooth_nonpositive_explicit_supportFloor`: nonzero form-vector smooth source with Q<=0 has support measure strictly greater than threshold(a,0).

## Meaning and limitation

This includes all signs/complex phases and any number of disconnected support components; no atom-avoidance or disjointness hypothesis. It excludes shrinking-spike counterexamples inside any fixed ambient aperture, even with mixed interactions. It is an actual region of the RH-equivalent energy inequality, rather than a reformulation of RH.

Does NOT prove RH: threshold depends on aperture, with very coarse exp(M(a)) dependence. M(a) itself grows like a*exp(a). Broadly spread sources remain uncontrolled. Do not extrapolate from positive localized pieces to positivity of their sum: all missing mixed terms matter, and prior modulus obstruction rules out that shortcut. Qualitative uniform nonconcentration is stronger in a different direction than smooth support bound: applies to arbitrary full form-domain nonpositive states and small local mass fractions, even when support not small.

Next promising real work: sharpen combined arithmetic bounds by using prime/Gamma/pole cancellations before the crude M(a) envelope; or derive exact localization (IMS) defect for smooth partitions to connect these local positivity estimates with broad source interactions. No unconditional global mixed Gram bound or negative determinant exists yet. Corpus already has extensive finite Schur/finite source-head criteria: search before adding more equivalent criteria. Translation invariance of full Q is in CCMRestrictedWeilFullTranslationCovariance.

## Validation state at memory write

All five leaves final audited green with foreground lake --old env lean, fresh oleans, no warnings. Five umbrella imports added next to CCMThetaModulusObstruction; MainTheorems already imports RHTower. No full builds. git diff --check passed; rg found no sorry/admit/native_decide/new axioms/heartbeat changes/#eval. Eight endpoint #print axioms checks passed, all only propext/Classical.choice/Quot.sound. Audit scratch `work/noether_small_measure_axioms.lean` removed; absence verified. All own processes terminal. Index refresh passed (1 changed; concurrent chats had indexed earlier files). Global lint --check-generated reports only four unrelated concurrent unwired leaves: MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroDensityPowerSaving. No generated staleness or own unreachable modules. Five umbrella imports verified, fresh oleans present, diff whitespace clean. No commit/push.

## Lean API repairs

- `UnifIntegrable` epsilon is implicit: call hui (half_pos hepsilon), not hui (epsilon/2) proof.
- Unit sphere opNorm bound: explicit simp le_refl after rewriting norm(u)=1.
- Global `_root_.measurableSet_support u.continuous.measurable`; not a Measurable field.
- MemLp.restrict requires the set argument S.
- For function-valued u.toSchwartz coercion, simp apply theorem does not rewrite whole function: first `he : (u.toSchwartz:Real->Complex)=(fun x=>u x) := funext (...)`, then rewrite he.
- Holder integral_mul_norm_le_Lp_mul_Lq uses SAME codomain for f and g. Set g=constant (1:Complex) when f is complex; real g can leave casts stuck.
- integral_const uses Measure.real; rewrite `measureReal_def` before Measure.restrict_apply_univ.
- Physical ToAperture and Embedding coeFn are definitionally related but rw does not unfold: `change (Embedding ... : Real->Complex) x=u x at hx` first.
- No local heartbeat overrides were needed.
