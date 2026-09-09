## Goal / constraints / current stopping state
Active unbudgeted SQB goal remains unconditional Lean proof/falsification of RH. RH and full-Xi occurrence UNPROVED. Previous source-energy turn and this all-Mellin/native-pairing turn made VERIFIED PROGRESS; no blocker streak. Do not mark goal complete or blocked just because mathematics hard. Frontier map READ ONLY. No numerical computations, Runpod, native_decide or numerical certificates. Broad corpus research OR searches. One owned foreground Lean/Lake process at a time; COLLECT terminal exit before next. Source/scratch `lake env lean FILE`; final only named leaf `lake --old build MODULE`, with --old --no-build preflight. No full or umbrella builds. No subagents, commits/push. Preserve peers. Every turn starts full chain, hardest obstacle, attack. User demands positive conjecture/proof-or-pivot and no more no-go/conditional-receiver theatre.
NO LIVE OWNED PROCESSES. Every handle collected terminal. Latest /tmp/sqb33_axioms.lean check session65405 exit0. All new scratch is complete and canonical, not pending. Do not restart completed checks.

## New closed results
1. formal/GaloisForLFunctions/RHTower/SelbergThetaNativeMoments.lean
namespace RHTower.SelbergThetaNativeMoments;7public;235lines.
2. formal/GaloisForLFunctions/RHTower/SelbergThetaNativePairing.lean
namespace RHTower.SelbergThetaNativePairing;12public;450lines.
Wired once into RHTower.lean after NativeEnergy. No other Lean source edited. Report docs/drafts/pipeline/3-formalized/sqb-theta-native-pairing.md. Card docs/drafts/pipeline/1-in-progress/sqb-positive-occurrence-conjecturing-loop.md upgraded from paper-only to closed Lean status. Prior report sqb-theta-native-source-energy.md continuation updated with pairing report link. Frontier map and universal STATUS untouched; new facts route-specific.

q:actual XiZeroCopy, z=xiSpectralPoint q=b+ic, b≠0. Phi=thetaCuspFullSource, u=SelbergThetaSourcePhase.mode q, R=u/Phi. Original native seeds x=logy/2, p(y)=exp(x)Phi(x), w(y)=exp(x)u(x); P,W complete primitive-row periodizations. h=z-i, m_a=tiltedMass a=2∫exp(ax)Phi(x)>0; m=sourceMass=m_-1. V=centeredSource q=W+P/h.

All-real tilt moments now proved:
- weightedMode_integrable(q,a): Integrable exp(ax)u for EVERY REAL a (not only old |a|<1).
- weightedMode_integral(q,a): ∫exp(ax)u=−(∫exp(ax)Phi)/(z+ia), endpoints/derivative admission discharged.
- tiltedMass(a), tiltedMass_pos(a), tiltedMass_neg(a):m_-a=m_a.
- positiveProfile_mellin(r): ∫_{y>0} y^-2 • ((p(y):complex)*(y^r:real))=m_(2r-1).
- modeProfile_mellin(q,r): same w moment=−m_(2r-1)/(z+i(2r-1)).
These are all7 public names.

Complete native pairing now proved:
E2=positiveCuspRows2, k=cuspReflectionNorm2.
∫fd V E2 = [2i*m3/(z-i)]*[2/(z+3i)−k/(z−3i)] ≠0.
Actual pairing integrable; V not ae0 in angularMeasure. centeredEnergy(q)=∫|V|²/P>0. With prior identity, nativeEnergy(q)=∫|W|²/P now satisfies STRICT lower m/|z-i|²<nativeEnergy<2m/|z-i|².
Actual centeredVector q :Space=(centeredSource_memLp q).toLp(centeredSource q), actual representative aeV; centeredVector_ne_zero; exact zero integral. centeredUnit q=((‖centeredVector q‖^-1:real):complex) • centeredVector q, native norm exactly1.
All12 public Pairing names: centeredSource_pairing, centeredSource_pairing_ne_zero, centeredSource_not_ae_zero, centeredEnergy_pos, nativeEnergy_lower_strict, centeredSource_pairing_integrable, centeredVector, centeredVector_coe, centeredVector_ne_zero, centeredUnit, centeredUnit_norm, centeredVector_integral.

## Proof mechanisms / no hidden assumptions
NativeSource's all height powers bound every exp(ax)Phi. For exp(ax)u endpoints, use tilt bounds at a+1 and a−1 plus globally boundedR. Integrability comes from all-rate theta tails; derivative follows original forced firstorder. Integrate derivative with two zero endpoints, solve denominator z+ia whose real part b≠0. General y=exp(2x) Jacobian evaluates all-real Mellin moments. Evenness gives equality m3=m_-3.
E2 mean: lowCuspPower_completed_mean at height2 + positiveLowCuspRows_coe + positiveLowCuspRows_mean identify Lambda3=Lambda4*k. Substitute into full completed mean to obtain ∫_0^1 E2(x+iy)=y²+k/y every y>0. k_pos also privately proved from nonzero completion factors; the final noncancellation actually needs only that k is real.
For a measurable literal seed with all real power bounds, private profile_power_integrable proves ∫_{y>0}|v(y)|y^r finite for every real r using a bounded low-height majorant and y^-2 high-height majorant. Norm mean of v(y)E2 is |v(y)|(y²+k/y), so hyperbolic strip admission follows from moments0 and−3 via modularStrip_integrable_of_norm_mean. Complete primitive-row unfolding includes absolute norm-integral summability and all rows. Product_mellin splits both Weyl terms with integrability proved, then actual centered profile moment is mode moment+positive moment/h. Plug r2,-1 and evenness.
Noncancellation: bracket zero implies (2−k)z−3i(2+k)=0; real part/b≠0 forces k2, imaginary gives−12=0. Thus native V not ae0. Density |V|²/P integrable by |V|≤K P with K=2/|b|+‖h^-1‖, from original native strict disk; exact zero-integral iff density ae0 yields positive centeredEnergy. Native toLp and unit norms use actual representatives, not abstract existence assumptions.
E2 itself is NOT nativeL2, but full V*E2 pairing is integrable. Exported centeredSource_pairing_integrable uses the valid integral_undef contrapositive of its already proved nonzero exact integral; the absolute strip/row-norm proof is inside product_unfold. No approximate operator equation, spectral occurrence or RH used anywhere.

## Audit exact evidence
Complete scratch /tmp/sqb33_moments.lean and /tmp/sqb33_pairing.lean PASS. Canonical checks PASS without diagnostics: /tmp/sqb33_moments_source_check.log, /tmp/sqb33_pairing_source_check.log. Scratch corresponding *_check.log empty.
NativeMoments final leaf build PASS9.5s, preflight only own leaf: /tmp/sqb33_moments_preflight.log, /tmp/sqb33_moments_leaf_build.log.
NativePairing final named leaf build PASS9.6s. Its preflight identified required direct dependency ThetaCuspHawkingBMStripMeanAdmission, which was rebuilt21s. These are the ONLY TWO Built lines. /tmp/sqb33_pairing_preflight.log, /tmp/sqb33_pairing_leaf_build.log. Other dependencies replayed from existing artifacts, not fresh whole-source dependency audit. No full builds.
Combined /tmp/sqb33_axioms.lean imports Pairing and prints all19 public declarations of both modules. /tmp/sqb33_axioms.log checked: all19 outputs, only propext/Classical.choice/Quot.sound. No diagnostics.
Repository formal lint PASS /tmp/sqb33_lint.log; index PASS /tmp/sqb33_index.log; scoped whitespace PASS. Umbrella wired once each. All handles terminal collected. No live Lean/Lake.

## Hardest remaining mathematics / next turn
Chain actual theta source→normalized native approximate vectors at fullXi target→occurrence→existing realpreimage classification→critical line→RH. Fixed source nonvanishing and native normalization NOW CLOSED; do not spend another turn on their basic corollaries or re-proving their audits.
Unchanged paper target e=5/4+z²/4; literal halfdensity residual:
(A−e)W=(1/4)periodize[sqrt(y)(zPhi+iPhi')],
(A−e)V=−1/[4(z−i)]periodize[sqrt(y)(D−1)(D−iz)Phi].
Full graph/derivative interchange and a FAMILY whose COMPLETE residual/native normalization tends0 remain UNPROVED. Recovery scalar is not residual norm. Need attack actual forcing cancellation while preserving native denominator; fixed V being nonzero alone proves no spectral incidence.
Existing entireCovariance already injectively maps any native vector to entireOperator.domain, so merely constructing CV/‖CV‖ and re-exporting the generic residual formula would be a conditional-wrapper detour. Likewise ordinary graph-convergent cutoffs of fixed source need not approximate any target; do not revive their retired residual-to-zero claim. The next useful step must actually control full residual for a new source/correction family (or find genuine source arithmetic handoff), not another receipt of assumptions.
Possible analytic strengthening if directly needed: E2 is notL2, but P*E2² should be integrable because all-power p bound gives P decays by all powers on fd (nonparabolic height≤1/y and quadratic row bound). Then pairing gives quantitative weighted recovery via Cauchy; do not formalize unless part of a concrete residual-correction argument. Actual native nonzero/unit already proved, so not needed just to normalize.

## Broad searches / leads in this turn
/tmp/sqb33_correction_search.json: correction resolvent synthesis OR allcorpus. Found HedenmalmThetaRealResolventTrace (real resolvent local norm<1 hypotheses; no missing native cancellation), HedenmalmThetaResolventMetricPlancherel (source-space Plancherel, not native handoff).
/tmp/sqb33_feedback_search.json: Schur Feshbach feedback OR allcorpus; mostly general algebra, no actual theta forcing cancellation supplied.
/tmp/sqb33_modular_search.json: theta modular lift OR.
/tmp/sqb33_moment_search.json: tiltedSource weightedMode OR.
Read memory selberg/sqb-entire-forcing-kernel-and-source-family-obstruction-2026-09-09: original corrected scattering source + its specific graph cutoffs have nonzero residual; do not repeat fixed-family failure. Read old positive-loop memory; actual card/new source results supersede old pending normalization text.
Read formal/AGENTS.md, README1–110, LEAN_OVERVIEW1–65, current frontier SQB rows (read only), universalSTATUS entries. No architecture/testing docs found. No subagents.

## Lean API lessons (new)
- Measure.integral_comp_mul_left (g)(a), NOT root integral_comp_mul_left. Defined under MeasureTheory.Measure in Haar/NormedSpace. For reflection `simpa using Measure.integral_comp_mul_left g (-1:ℝ)`.
- Generic halfDensity_moment rewrite needs explicit function argument for realcast Phi: `rw [halfDensity_moment (fun x => (thetaCuspFullSource x:ℂ)) r]`; unification cannot infer cast lambda.
- General norm-power integrability: `fun_prop` successfully proves measurable real rpow for any exponent. `Real.rpow_sub hy`, `Real.rpow_add hy`, `Real.rpow_neg hy.le`; distinguish membership hy:Ioi0 with `have hy0:0<y:=hy` before hy.ne' (field_simp elaborator won't unfold membership itself).
- Numerical cpow negative exponent not reduced by bare norm_num: use `[Complex.cpow_neg_one]` at he.
- Specialized positiveLowCuspRows_coe cast numeral2 doesn't rw directly to lowCuspPower (2:ℂ): first local hc(z):cast positiveLow2=periodize(low(2:ℂ)) via `simpa using positiveLowCuspRows_coe 2 ... z`, then simp_rw←hc.
- Avoid dsimp[φ] on group-action function: it expands SL2Z action into toGL/map, so im_T_zpow_smul / PSL2Z invariance rewrites stop matching. Use explicit `change h (T^n • z).im*... = ...`, keeping SL2Z action opaque. Same for gammaSetMatrix.
- Measurable composition uses UpperHalfPlane.continuous_im.measurable, not ambiguous continuous_im.
- Definitional function equations under Integrable.congr_fun need `simp only [Pi.add_apply]` or explicit change before rewriting an inner integral. Density measurable division also needs explicit `change ‖‖V z‖²/Pz‖≤...` before rw abs.
- Typed local `have hp:0<positiveProfile y:=...` before `rw[abs_of_pos hp]`; inline proof may infer expanded exponential expression causing rw mismatch.
- Complex shift h=z−i: `simpa [sub_eq_add_neg] using shift_ne_zero q (-1)`; similarly add mul_comm for±3. Before field_simp rational pairing normalize Complex.ofReal_neg/ofReal_ofNat, mul_neg,←sub_eq_add_neg, mul_comm I 3. Otherwise z+I*↑(-3) remains opaque inverse.
- Complex.ofNat_re/im DON'T EXIST; use `norm_num [Complex.mul_re,Complex.mul_im] at hr` and linarith instead.
- `add_le_add h le_rfl` avoids surprising add_le_add_right orientation (possibly opened theorem shadowing).
- Remove redundant ring after field_simp when field_simp already closes; no unnecessary seq focus warnings retained.

Prior result source/energy details: `mem:selberg/sqb-native-source-energy-2026-09-09` (paper-only claims there now superseded by this memory). Earlier source phase/variance/energy-disk modules stay valid and audited.