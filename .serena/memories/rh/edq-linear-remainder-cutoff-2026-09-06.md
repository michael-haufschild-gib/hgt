# EDQ actual weighted remainder: linear cutoff — 2026-09-06

Goal remains ACTIVE, RH neither proved nor falsified. This turn was PROGRESS: closed a stronger uniform source theorem reducing the uncontrolled arithmetic head from N²<t³ to N<t. Do not re-prove or re-audit completed tail/cotangent/unit-phase modules.

User latest efficiency rules: one foreground Lean process per agent, no full/umbrella builds, scratch lake env lean, only final target lake build --old <module>, only NEW declarations' axioms. No numerical computations or certificate used here.

New completed leaves:
1. formal/GaloisForLFunctions/RHTower/ArithmeticLogarithmicFourierTail.lean (280 lines, 22 decls; imports existing weighted vdC +/- tests, BernoulliFourierBridge, EulerDeletionPowerSumRemainder).
2. formal/GaloisForLFunctions/RHTower/ArithmeticRemainderLinearCutoff.lean (155 lines, 5 theorems).
Both namespace RHTower.DeletionMixedRefinement. Both wired into RHTower.lean.
Total 27 new declarations (24 theorems, 3 definitions), ONLY these axiom-audited; every one depends solely on propext, Classical.choice, Quot.sound.
All scratch checks passed, both final leaf builds passed, formal lint PASSED. Final cutoff build refreshed direct prerequisite ArithmeticRemainderPhaseCutoff (18 s) then new cutoff leaf (28 s); no umbrella/full build. One premature axiom-import attempt failed immediately because new leaf olean was still being generated; did not audit any result. After leaf completion, actual axiom audit ran and passed. All owned processes terminal; six scratch Lean sources removed. Logs retained /tmp/edq_linear_fourier_build.log, /tmp/edq_linear_cutoff_build.log, /tmp/edq_linear_new_axioms.log, /tmp/edq_linear_lint.log.

Main theorem line143 ArithmeticRemainderLinearCutoff:
normalizedWeightedRemainder_im_neg_of_height_le_cutoff
  hs:0<s.re, hs':s.re<=1, ht:1<=s.im, hN:1<=N, htN:s.im<=N
  -> (normalizedWeightedRemainder s N).im<0.
No zero premise. N integer. Full actual power weights retained. R's sharper proposed t<2pi N still OPEN, C/B2 still OPEN, decisive unit-head orientation OPEN.

Exact proof chain:
- b(x)=BernoulliPeriodic(x)=((fract x)^2-fract x)/2.
- Existing BernoulliFourierBridge has Fourier expansion. New weight a_k=1/(4pi² k²), real nonnegative, a_0=0, HasSum a_k=1/12 by series at x=0.
- New logarithmicFourierMode beta t omega x = x^-beta * exp(i(omega*x+t*log x)).
- For anchor a>0, |t|<=a, |omega|>=6, beta>1, actual half-line mode norm <=4*a^-beta/5. First prove finite interval using BOTH existing weighted first-derivative tests (positive omega, split sign t); phase derivative>=5, second derivative=-t/x² with fixed sign, weight derivative negative. Negative omega via exact conjugation. Integrability passes interval bound to Ioi.
- New fourier_mul_cpow_eq_mode: fourier k x*x^(-s-2)=mode(s.re+2,-s.im,2pi k,x).
- New bernoulliFourierTerm retains positive a_k. Norm integral majorant factors a_k times common integrable power amplitude. hasSum_integral_bernoulliFourierTerm proves full infinite sum-integral interchange using summable integrals of norms.
- norm_centeredBernoulliTail_le_linear: Re(s)>-1, a>0, |Im(s)|<=a -> norm integral((b+1/12)*x^(-s-2))<=a^(-Re(s)-2)/15.
  Sum mode bound 4/5 against EXACT coefficient mass1/12. No zeta-value numerical bound or quadrature.
- centeredBernoulliTail_eq_sub_mean: at integer N, centered integral = zetaBernoulliTail N s + N^(-s-1)/(12(s+1)).
- normalizedWeightedRemainder_scaled_eq_tail: g_s(N)*N^(2Re(s)+1)=tail(N,star s)*N^(star s+1).
- norm_normalizedWeightedRemainder_scaled_sub_mean_le_linear: Re(s)>0,s!=1, N>=1, |Im(s)|<=N ->
  norm(g_s(N)*N^(2Re(s)+1)-[-1/(12(star s+1))])<=1/(15N).
- normalizedWeightedRemainder_im_neg_of_linear_bound: in addition t>0 and 4*normSq(s+1)<5*t*N -> Im g<0.
- High heights t>5 with sigma<=1 and N>=t satisfy this margin. For1<=t<=5, reuse already proved quartic disk: product norm numerator <=(t²+25/2)(t²+4)=t4+33/2*t²+50 <=143/2*t³<96*t³ <=32*(sigma+3)*t*N². Final combines regimes.

Docs:
- Completed certificate moved from 1-in-progress/edq-linear-remainder-cutoff.md to docs/drafts/pipeline/3-formalized/edq-linear-remainder-cutoff.md. Contains exact paper proof, corpus ancestry, theorem map, validation, RH gap.
- rh-current-frontier-map.md all EDQ cutoff summaries now N>=t, exceptional head N<t; preserves sharper R conjecture. No new route label.
- universal-law-field/STATUS.md route-independent exceptional-initial-term constraint updated to proved linear bound.
- arithmetic-successor-phase-threshold.md notes LNC and unchanged sharper R.
- edq-logarithmic-cotangent-orientation.md remains ACTIVE comparison card; now references LNC and says next proof must control N<t and unit value. Cotangent separate weighted drifts have no assigned sign; source integral controlled by Fourier only on N>=t.

Next work must target actual finite head/zero-bearing unit constraint, or a new signed/source comparison reaching it. More eventual convergence, unweighted prefix identities, routine linear-cutoff reproving, or merely restating RH receivers would not progress. Stronger R t<2piN can still be investigated, but even R leaves unit at large zeros. Do not silently claim LNC proves R, C/B2, or RH.
Prior holomorphic unit-phase global/finite charts are terminal; local phase germ iff simple critical zero. Actual mod2/3 source product is nonselective. General remainder family inverse/reconstruction supplies no sign.

Lean implementation notes:
- convert! for HasDerivAt/HasSum, ordinary convert created instance-equality noise.
- star_mul reverses factors; for complex conjugation use Complex.star_def then map_mul, <-Complex.exp_conj.
- integral_conj exists, integral_star does NOT.
- AE function equality: filter_upwards [ae_restrict_mem measurableSet_Ioi] works; rw ae_restrict_iff' does not unfold EventuallyEq.
- simp only [neg_div] at BOTH hb and him before linarith, else equal norm expressions are syntactically different.
- push_cast handles (N:Real):Complex vs Nat:Complex after cpow normalization.
- Real.pi_gt_three verified actual mathlib.
- HasSum.norm_le_of_bounded avoids extra summability proofs for final mode norm sum.
- No new arbitrary APIs or assumptions added; set_option autoImplicit false used.
