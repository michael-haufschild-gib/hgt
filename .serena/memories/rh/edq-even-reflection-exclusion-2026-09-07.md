# EDQ even reflection exclusion — 2026-09-07

Full active goal remains unconditional RH proof/falsification via EDQ. Chain: Euler deletion -> exact complex zero balance -> signed arithmetic separation -> exclude all off-line zeros -> RH. RH remains unproved/unfalsified; goal ACTIVE, never count this partial component as complete. Previous HRC turn was progress, current turn also authoritative Lean progress.

New completed leaf formal/GaloisForLFunctions/RHTower/ArithmeticEvenReflectionExclusion.lean, 357 lines, 16 theorems +4 defs, namespace RHTower.DeletionMixedRefinement. Imports ArithmeticHardyResponseCoercivity and ZetaLineFirstMoment, all cached.

New actual even source control:
P=bernoulliPeriodic+1/12, c=.5+i*t, r=1-star s, delta=s.re-.5.
reflectionEvenKernel(delta,x)=2P*x^-5/2*(cosh(delta log x)-1).
reflectionEvenDensity=kernel*exp(i*t log x).
unitFullFourierSource_even_eq_integral: F(s)+F(r)-2F(c)=integral evenDensity, throughout open strip.
norm_unitFullFourierSource_even_le line98: norm(Fs+Fr-2Fc)<=delta^2/6 ALL heights. Proof uses exact even power pairing, abs(P)<=1/12, cosh defect <=delta^2 log^2*x^.5/2, exact integral x^-2 log^2=2. Whole literal source retained, no lost sector or mean.

reflectionEvenBoundary A(s)=unitPhaseBoundary(s)+1/(12(s+1))=-1/(2s(1-s))+1/(12(s+1)).
reflectionEvenCorrection E(s)=-(c*s*r)^-1 - ((1-c)*(1-s)*(1-r))^-1 + ((c+1)*(s+1)*(r+1))^-1/6.
reflectionEvenBoundary_pair: A(s)+A(r)-2A(c)=delta^2 E(s). Inverse pair helper for u+v=2c: u^-1+v^-1-2c^-1=2(u-c)^2/(cuv).
normalized_value_even_constraint_at_zero: every actual strip zero satisfies norm(2*normalizedMinimumZeta(c)+delta^2 E(s))<=delta^2/6. Uses actual FE partner zero and F=star(A-Z); no additional zero hypothesis asserted independently.
norm_reflectionEvenCorrection_le: norm(E(s))<=13/(6 abs(t)^3) for ALL complex s with t!=0. Each three-factor endpoint product has norms >=abs(t). Exact height decay retained.
norm_normalized_value_at_zero_le: for abs(t)>=1 and strip zero, norm(Z(c))<=7 delta^2/6.
hardyResponseDenominator_norm_le: norm(c(c+1))<=6t^2 for abs(t)>=1.
hardy_amplitude_at_zero_le line289: every strip zero with abs(t)>=1 forces abs(hardyZ t)<=7*t^2*delta^2.

Actual exclusion:
zeta_ne_zero_of_hardy_floor: in strip, abs(t)>=1, abs(H t)>=1/4, abs(delta)<=1/(8 abs(t)) imply actual zeta(s)!=0. Bound gives 7/64<1/4.
exists_high_hardy_amplitude_floor T: exists t>T, t>=1, abs(H t)>=1/4, UNCONDITIONAL. Uses existing ZetaLineFirstMoment.exists_le_integral_hardyZ_sq (dyadic integral>=U/4) and continuity. Negation would bound H^2<=1/16 throughout selected [U,2U], contradict moment floor.
exists_high_even_reflection_exclusion line345: above EVERY T there is actual height t>=1 such that every strip s with im=t and abs(delta)<=1/(8t) is NONZERO. This produces actual explicit horizontal zero-free segments, not just necessary-condition coordinate transforms. It does NOT cover every height or displacement. Critical zeros fail amplitude floor; no RH or simplicity proved. Keep exact even constraint together with odd Hardy value/slope disks; don't infer full coverage from cofinal segments.

Docs: card moved to docs/drafts/pipeline/3-formalized/edq-even-reflection-exclusion.md. Frontier current paragraph + EDQ row updated; scoped old RDA paragraph now explicitly refers to its two derivative-response disks (new even condition is separate). STATUS new route-independent Must prove coverage when assembling local zero exclusion. Umbrella import appended, NO umbrella build.

Verification: final scratch84666 exit0 no diagnostics; final leaf build14232 exit0 ONLY new leaf4.5sec, cached10784jobs. New-only axioms30324 exit0 all20 declarations only standard propext/Classical.choice/Quot.sound. Repository lint95956 EXIT0: previous concurrent wiring errors resolved by others; do not keep reporting old failures. Index48658 exit0 2changed0removed. All owned process handles terminal; no owned even-reflection Lean/lake remains. /tmp/edq_even_reflection.lean and /tmp/edq_even_reflection_axioms.lean removed; logs /tmp/edq_even_reflection.{check,build,axioms,lint,index}.log retained. Do NOT rebuild/re-audit this or older leaves.

Corpus audit before work: first Laguerre inequality in XiLaguerrePolya is conditional on RH and cannot serve as producer. SpeiserCriticalLineSignLaw proves Re(zeta'/zeta)<0 on critical line above20 at nonzeros and derivative zero there=>zeta zero, but Speiser equivalence is receiver. SpeiserCriticalPacketGauge shows polynomial gauges can prescribe finite critical packets while preserving real-axis positivity and order-one envelope; zero-free exponential gauge with fixed divisor/growth rigid affine. Source theta D1/Turan positivity is about source, not unconditionally first Laguerre for Xi. No RH-dependent input used.

Useful actual APIs:
integrable_unitFullFourierDensity hs from ArithmeticReflectionErrorHeight: -1<s.re.
fullFourier_cpow_eq_logMode s hx: x^(-star s-2)=real x^(-(s.re+2))*exp(i*t logx).
reflection_hyperbolic_substrip_bounds hx hdelta, use epsilon=0 for even majorant, second component.
incoming_reflected_zeta_zero hs.1 hs.2 hz.
HardyZ.intervalIntegrable_hardyZ_sq (T U) is interval T..(T+U), NOT T..U! Use (continuous_hardyZ.pow 2).intervalIntegrable U (2*U) for dyadic proof.
intervalIntegral.integral_mono_on hab hf hg (fun x hx=>...), integral_const.
mul_self_le_mul_self returns a*a<=b*b; pow2 not defeq here: rw [<-pow_two,<-pow_two] then sq_abs/mul_pow.
A let-bound definition whose body starts unary minus can parse minus into preceding let RHS; put semicolon after last let.
linear_combination after push_cast can introduce unnormalized real casts via hypotheses/coefficients; use (norm := (push_cast; ring)).
Avoid unknown RHS metavariable in have h := norm_add_le.trans (by linarith); annotate entire target inequality first.
add_le_add_right is shadowed in open namespaces; norm triangle inequalities plus explicitly typed target and linarith avoids argument order surprises.
