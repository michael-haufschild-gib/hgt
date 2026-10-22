import GaloisForLFunctions.RHTower.Deninger.DeningerDampedWeightedSourceBoundary

/-!
# Literal Mellin jets and native Xi order of the same damped source

Two nearby exponentially weighted L1 norms control every finite polynomial
moment of the actual source and its finite-prefix error. Local dominated
differentiation identifies these literal integrals with all complex
Mellin derivatives on the proved strip `1-a < re(s) < a`. Only after this
source identification are the derivatives matched with the Euler quotient.

At damping one every actual Xi point lies in that strip. Multiplication of
`XiC` by the same nonzero Mellin source, in the original centered coordinate,
preserves its analytic order, all lower vanishing jets, and the native leading
jet with its exact nonzero multiplier. No simplicity or bounded-multiplicity
premise is used.

This closes literal jet admission. The complete Xi Hilbert packet, original
Green/BV domain, fixed physical-reader comparison, and damping continuation
remain separate obligations. The original circle boundary from C44 survives;
no boundary cancellation or Riemann-hypothesis conclusion is asserted here.
-/

open Complex Filter Topology SchwartzMap MeasureTheory
noncomputable section
namespace RHTower

/-- A finite polynomial moment costs only an arbitrarily small exponential margin. -/
theorem deninger_abs_pow_le_exp_margin (k : ℕ) {d : ℝ} (hd : 0<d) (t : ℝ) :
    |t|^k ≤ ((k.factorial : ℝ)/d^k)*Real.exp (d*|t|) := by
  have hfac : (0 : ℝ)<k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hp := Real.pow_div_factorial_le_exp (d*|t|) (mul_nonneg hd.le (abs_nonneg t)) k
  rw [div_le_iff₀ hfac,mul_pow] at hp
  rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hd k)]
  nlinarith only [hp]

/-- Both sides of the original line are controlled by two nearby admitted weights. -/
theorem deninger_abs_pow_exp_le_two_weights (k : ℕ) (c : ℝ) {d : ℝ}
    (hd : 0<d) (t : ℝ) :
    |t|^k*Real.exp (c*t) ≤ ((k.factorial : ℝ)/d^k)*
      (Real.exp ((c-d)*t)+Real.exp ((c+d)*t)) := by
  have hC : 0 ≤ (k.factorial : ℝ)/d^k := by positivity
  calc
    _ ≤ (((k.factorial : ℝ)/d^k)*Real.exp (d*|t|))*Real.exp (c*t) :=
      mul_le_mul_of_nonneg_right (deninger_abs_pow_le_exp_margin k hd t) (Real.exp_pos _).le
    _ = ((k.factorial : ℝ)/d^k)*Real.exp (c*t+d*|t|) := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      by_cases ht : 0≤t
      · rw [abs_of_nonneg ht,show c*t+d*t=(c+d)*t by ring]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
      · rw [abs_of_neg (lt_of_not_ge ht),show c*t+d*(-t)=(c-d)*t by ring]
        exact le_add_of_nonneg_right (Real.exp_pos _).le

private theorem mellin_strip_margin {a c : ℝ} (hc0 : 1-a<c) (hc1 : c<a) :
    ∃ d : ℝ, 0<d ∧ 1-a<c-d ∧ c+d<a := by
  let d := min (c-(1-a)) (a-c)/2
  have hm : 0 < min (c-(1-a)) (a-c) := lt_min (by linarith) (by linarith)
  have h1 := min_le_left (c-(1-a)) (a-c)
  have h2 := min_le_right (c-(1-a)) (a-c)
  refine ⟨d,by dsimp [d]; positivity,?_,?_⟩ <;> dsimp [d] <;> linarith

theorem deningerDampedLogSource_weightedNorm_integrable (a : {a : ℝ // 1/2<a})
    (c : {c : ℝ // 1-a.val<c ∧ c<a.val}) :
    Integrable (fun t => Real.exp (c.val*t)*‖deningerDampedLogSource a t‖) := by
  convert (deningerDampedLogSource_weighted_integrable a c).norm using 1
  ext t
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

theorem deningerDampedLogSource_jet_aestronglyMeasurable
    (a : {a : ℝ // 1/2<a}) (k : ℕ) (s : ℂ) :
    AEStronglyMeasurable (deningerMeyerStrongLogMellinJet k s (deningerDampedLogSource a))
      (volume : Measure ℝ) := by
  have heq : deningerMeyerStrongLogMellinJet k s (deningerDampedLogSource a) =
      (fun t : ℝ => (t : ℂ)^k*Complex.exp (s*(t : ℂ))*deningerDampedLogSource a t) := rfl
  rw [heq]
  exact (by fun_prop : Continuous (fun t : ℝ => (t : ℂ)^k*Complex.exp (s*(t : ℂ)))).aestronglyMeasurable.mul
    (deningerDampedLogSource_aestronglyMeasurable a)

/-- Every finite literal Mellin jet of the actual limit is integrable in the admitted strip. -/
theorem deningerDampedLogSource_jet_integrable (a : {a : ℝ // 1/2<a})
    (k : ℕ) (s : ℂ) (hs0 : 1-a.val<s.re) (hs1 : s.re<a.val) :
    Integrable (deningerMeyerStrongLogMellinJet k s (deningerDampedLogSource a)) := by
  obtain ⟨d,hd,hlo,hhi⟩ := mellin_strip_margin hs0 hs1
  let cl : {c : ℝ // 1-a.val<c ∧ c<a.val} := ⟨s.re-d,hlo,by linarith⟩
  let ch : {c : ℝ // 1-a.val<c ∧ c<a.val} := ⟨s.re+d,by linarith,hhi⟩
  have hb := ((deningerDampedLogSource_weightedNorm_integrable a cl).add
    (deningerDampedLogSource_weightedNorm_integrable a ch)).const_mul ((k.factorial : ℝ)/d^k)
  apply hb.mono' (deningerDampedLogSource_jet_aestronglyMeasurable a k s)
  filter_upwards with t
  rw [norm_deningerMeyerStrongLogMellinJet]
  have h := mul_le_mul_of_nonneg_right (deninger_abs_pow_exp_le_two_weights k s.re hd t)
    (norm_nonneg (deningerDampedLogSource a t))
  simpa only [cl,ch,Function.comp_apply,Pi.add_apply,mul_add,add_mul,mul_assoc] using h

/-- Exact integral expression for the weighted L1 error of the same source. -/
theorem deningerDampedLogSource_weighted_error (a : {a : ℝ // 1/2<a})
    (c : {c : ℝ // 1-a.val<c ∧ c<a.val}) (n : ℕ) :
    (∫ t, Real.exp (c.val*t)*‖(deningerDampedPrimeListSource a.val
      (GaloisForLFunctions.primesLE n).toList : ℝ → ℂ) t-deningerDampedLogSource a t‖) =
        ‖deningerDampedWeightedL1Prefix a.val c.val n-deningerDampedWeightedL1Limit a c‖ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (deningerDampedWeightedL1Prefix a.val c.val n)
      (deningerDampedWeightedL1Limit a c),
    (deningerStrongLogWeightedSchwartzLM c.val
      (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList)).coeFn_toLp
        (p:=1) (μ:=volume),deningerDampedLogSource_weighted_ae a c] with t hsub hprefix hlimit
  rw [hsub,Pi.sub_apply,← hlimit]
  change Real.exp (c.val*t)*‖_‖ = ‖((deningerStrongLogWeightedSchwartzLM c.val
    (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList)).toLp 1 volume) t - _‖
  rw [hprefix,deningerStrongLogWeightedSchwartzLM_apply,← mul_sub]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

theorem deningerDampedLogSource_weighted_error_integrable
    (a : {a : ℝ // 1/2<a}) (c : {c : ℝ // 1-a.val<c ∧ c<a.val}) (n : ℕ) :
    Integrable (fun t => Real.exp (c.val*t)*‖(deningerDampedPrimeListSource a.val
      (GaloisForLFunctions.primesLE n).toList : ℝ → ℂ) t-deningerDampedLogSource a t‖) := by
  have hf : Integrable (fun t => (Real.exp (c.val*t) : ℂ)*
      (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList : ℝ → ℂ) t) := by
    exact (deningerStrongLogWeightedSchwartzLM c.val
      (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList)).integrable
  apply ((hf.sub (deningerDampedLogSource_weighted_integrable a c)).norm).congr
  filter_upwards with t
  simp only [Pi.sub_apply,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- The actual full jet error is bounded by two already-convergent weighted source errors. -/
theorem deningerDampedLogSource_jet_error_bound (a : {a : ℝ // 1/2<a})
    (k : ℕ) (s : ℂ) {d : ℝ} (hd : 0<d)
    (hlo : 1-a.val<s.re-d) (hhi : s.re+d<a.val) (n : ℕ) :
    let cl : {c : ℝ // 1-a.val<c ∧ c<a.val} := ⟨s.re-d,hlo,by linarith⟩
    let ch : {c : ℝ // 1-a.val<c ∧ c<a.val} := ⟨s.re+d,by linarith,hhi⟩
    ‖(∫ t, deningerMeyerStrongLogMellinJet k s
      (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList) t)-
        ∫ t, deningerMeyerStrongLogMellinJet k s (deningerDampedLogSource a) t‖ ≤
      ((k.factorial : ℝ)/d^k)*
        (‖deningerDampedWeightedL1Prefix a.val cl.val n-deningerDampedWeightedL1Limit a cl‖+
          ‖deningerDampedWeightedL1Prefix a.val ch.val n-deningerDampedWeightedL1Limit a ch‖) := by
  dsimp only
  let cl : {c : ℝ // 1-a.val<c ∧ c<a.val} := ⟨s.re-d,hlo,by linarith⟩
  let ch : {c : ℝ // 1-a.val<c ∧ c<a.val} := ⟨s.re+d,by linarith,hhi⟩
  let f := deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList
  have hf := integrable_deningerMeyerStrongLogMellinJet f.property k s
  have hg := deningerDampedLogSource_jet_integrable a k s (by linarith) (by linarith)
  have hl := deningerDampedLogSource_weighted_error_integrable a cl n
  have hh := deningerDampedLogSource_weighted_error_integrable a ch n
  have hb := (hl.add hh).const_mul ((k.factorial : ℝ)/d^k)
  rw [← integral_sub hf hg]
  calc
    _ ≤ ∫ t, ‖deningerMeyerStrongLogMellinJet k s f t-
        deningerMeyerStrongLogMellinJet k s (deningerDampedLogSource a) t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, ((k.factorial : ℝ)/d^k)*
        (Real.exp (cl.val*t)*‖(f : ℝ → ℂ) t-deningerDampedLogSource a t‖+
          Real.exp (ch.val*t)*‖(f : ℝ → ℂ) t-deningerDampedLogSource a t‖) := by
      apply integral_mono_ae (hf.sub hg).norm hb
      filter_upwards with t
      have heq : deningerMeyerStrongLogMellinJet k s f t-
          deningerMeyerStrongLogMellinJet k s (deningerDampedLogSource a) t =
          deningerMeyerStrongLogMellinJet k s (fun t => (f : ℝ → ℂ) t-deningerDampedLogSource a t) t := by
        simp only [deningerMeyerStrongLogMellinJet,mul_sub]
      rw [Pi.sub_apply,Pi.add_apply,heq,norm_deningerMeyerStrongLogMellinJet]
      have h := mul_le_mul_of_nonneg_right (deninger_abs_pow_exp_le_two_weights k s.re hd t)
        (norm_nonneg ((f : ℝ → ℂ) t-deningerDampedLogSource a t))
      simpa only [cl,ch,mul_add,add_mul,mul_assoc] using h
    _ = _ := by
      rw [integral_const_mul,integral_add hl hh,
        deningerDampedLogSource_weighted_error a cl n,deningerDampedLogSource_weighted_error a ch n]

/-- All literal Mellin jets pass to the same actual source, at every finite order. -/
theorem deningerDampedLogSource_jet_tendsto (a : {a : ℝ // 1/2<a})
    (k : ℕ) (s : ℂ) (hs0 : 1-a.val<s.re) (hs1 : s.re<a.val) :
    Tendsto (fun n => ∫ t, deningerMeyerStrongLogMellinJet k s
      (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList) t) atTop
      (𝓝 (∫ t, deningerMeyerStrongLogMellinJet k s (deningerDampedLogSource a) t)) := by
  obtain ⟨d,hd,hlo,hhi⟩ := mellin_strip_margin hs0 hs1
  let cl : {c : ℝ // 1-a.val<c ∧ c<a.val} := ⟨s.re-d,hlo,by linarith⟩
  let ch : {c : ℝ // 1-a.val<c ∧ c<a.val} := ⟨s.re+d,by linarith,hhi⟩
  have hleft : Tendsto (fun n => ‖deningerDampedWeightedL1Prefix a.val cl.val n-
      deningerDampedWeightedL1Limit a cl‖) atTop (𝓝 0) := by
    simpa using ((deningerDampedWeightedL1Prefix_tendsto a cl).sub_const
      (deningerDampedWeightedL1Limit a cl)).norm
  have hright : Tendsto (fun n => ‖deningerDampedWeightedL1Prefix a.val ch.val n-
      deningerDampedWeightedL1Limit a ch‖) atTop (𝓝 0) := by
    simpa using ((deningerDampedWeightedL1Prefix_tendsto a ch).sub_const
      (deningerDampedWeightedL1Limit a ch)).norm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n =>
    deningerDampedLogSource_jet_error_bound a k s hd hlo hhi n)
  simpa using (hleft.add hright).const_mul ((k.factorial : ℝ)/d^k)

/-- The actual damping-one source admits every jet at every original Xi coordinate. -/
theorem deningerDampingOne_source_all_xi_jets (rho : XiDivisorSupport) (k : ℕ) :
    Integrable (deningerMeyerStrongLogMellinJet k (rho : ℂ)
      (deningerDampedLogSource ⟨1,by norm_num⟩)) ∧
    Tendsto (fun n => ∫ t, deningerMeyerStrongLogMellinJet k (rho : ℂ)
      (deningerDampedPrimeListSource 1 (GaloisForLFunctions.primesLE n).toList) t) atTop
      (𝓝 (∫ t, deningerMeyerStrongLogMellinJet k (rho : ℂ)
        (deningerDampedLogSource ⟨1,by norm_num⟩) t)) := by
  have hs := xi_divisor_support_re_mem_open_unit rho
  exact ⟨deningerDampedLogSource_jet_integrable ⟨1,by norm_num⟩ k rho (by simpa using hs.1) hs.2,
    deningerDampedLogSource_jet_tendsto ⟨1,by norm_num⟩ k rho (by simpa using hs.1) hs.2⟩

private theorem exp_weight_le_two {b c d : ℝ} (hb : c-d≤b) (hc : b≤c+d) (t : ℝ) :
    Real.exp (b*t) ≤ Real.exp ((c-d)*t)+Real.exp ((c+d)*t) := by
  by_cases ht : 0≤t
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc ht)).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hb (le_of_not_ge ht))).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)

/-- Differentiation under the original integral uses only an admitted local strip. -/
theorem hasDerivAt_deningerDampedLogSource_jet_integral (a : {a : ℝ // 1/2<a})
    (k : ℕ) (s : ℂ) (hs0 : 1-a.val<s.re) (hs1 : s.re<a.val) :
    HasDerivAt (fun z => ∫ t, deningerMeyerStrongLogMellinJet k z (deningerDampedLogSource a) t)
      (∫ t, deningerMeyerStrongLogMellinJet (k+1) s (deningerDampedLogSource a) t) s := by
  obtain ⟨d,hd,hlo,hhi⟩ := mellin_strip_margin hs0 hs1
  let lo : ℂ := (s.re-d : ℝ)
  let hi : ℂ := (s.re+d : ℝ)
  let B : ℝ → ℝ := fun t =>
    ‖deningerMeyerStrongLogMellinJet (k+1) lo (deningerDampedLogSource a) t‖+
    ‖deningerMeyerStrongLogMellinJet (k+1) hi (deningerDampedLogSource a) t‖
  have hB : Integrable B :=
    (deningerDampedLogSource_jet_integrable a (k+1) lo hlo (by dsimp [lo]; linarith)).norm.add
      (deningerDampedLogSource_jet_integrable a (k+1) hi (by dsimp [hi]; linarith) hhi).norm
  have hdom : ∀ᵐ t : ℝ, ∀ z ∈ Metric.ball s d,
      ‖deningerMeyerStrongLogMellinJet (k+1) z (deningerDampedLogSource a) t‖ ≤ B t := by
    filter_upwards with t
    intro z hz
    have he := Complex.abs_re_le_norm (z-s)
    rw [Complex.sub_re] at he
    have hn : ‖z-s‖<d := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
    have hl : s.re-d≤z.re := by linarith [(le_abs_self (z.re-s.re)).trans he,neg_abs_le (z.re-s.re)]
    have hh : z.re ≤ s.re+d := by linarith [(le_abs_self (z.re-s.re)).trans he]
    have hb := exp_weight_le_two hl hh t
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (pow_nonneg (abs_nonneg t) (k+1)))
      (norm_nonneg (deningerDampedLogSource a t))
    simpa only [B,norm_deningerMeyerStrongLogMellinJet,lo,hi,Complex.ofReal_re,mul_add,add_mul] using hm
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => deningerMeyerStrongLogMellinJet k z (deningerDampedLogSource a) t)
    (F' := fun z t => deningerMeyerStrongLogMellinJet (k+1) z (deningerDampedLogSource a) t)
    (x₀ := s) (s := Metric.ball s d) (bound := B)
    (Metric.ball_mem_nhds s hd)
    (Filter.Eventually.of_forall (deningerDampedLogSource_jet_aestronglyMeasurable a k))
    (deningerDampedLogSource_jet_integrable a k s hs0 hs1)
    (deningerDampedLogSource_jet_aestronglyMeasurable a (k+1) s)
    hdom hB (by
      filter_upwards with t
      intro z hz
      exact hasDerivAt_deningerMeyerStrongLogMellinJet k z (deningerDampedLogSource a) t)).2

/-- Local all-order derivative identification of the same strip-admitted source. -/
theorem iteratedDeriv_deningerDampedLogSource_mellin (a : {a : ℝ // 1/2<a})
    (k : ℕ) (s : ℂ) (hs0 : 1-a.val<s.re) (hs1 : s.re<a.val) :
    iteratedDeriv k (deningerMeyerStrongLogMellin (deningerDampedLogSource a)) s =
      ∫ t, deningerMeyerStrongLogMellinJet k s (deningerDampedLogSource a) t := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hop : IsOpen {z : ℂ | 1-a.val<z.re ∧ z.re<a.val} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have heq : iteratedDeriv k (deningerMeyerStrongLogMellin (deningerDampedLogSource a)) =ᶠ[𝓝 s]
        (fun z => ∫ t, deningerMeyerStrongLogMellinJet k z (deningerDampedLogSource a) t) := by
      filter_upwards [hop.mem_nhds ⟨hs0,hs1⟩] with z hz
      exact ih z hz.1 hz.2
    rw [heq.deriv_eq]
    exact (hasDerivAt_deningerDampedLogSource_jet_integral a k s hs0 hs1).deriv

/-- Every original finite Mellin derivative converges to that of the actual source. -/
theorem deningerDampedLogSource_mellin_derivatives_tendsto (a : {a : ℝ // 1/2<a})
    (k : ℕ) (s : ℂ) (hs0 : 1-a.val<s.re) (hs1 : s.re<a.val) :
    Tendsto (fun n => iteratedDeriv k (deningerMeyerStrongLogMellin
      (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList)) s) atTop
      (𝓝 (iteratedDeriv k (deningerMeyerStrongLogMellin (deningerDampedLogSource a)) s)) := by
  rw [iteratedDeriv_deningerDampedLogSource_mellin a k s hs0 hs1]
  exact (deningerDampedLogSource_jet_tendsto a k s hs0 hs1).congr'
    (Filter.Eventually.of_forall fun n =>
      (iteratedDeriv_deningerMeyerStrongLogMellin_eq_integral_jet
        (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList).property k s).symm)

/-- The literal Mellin transform is analytic on its proved admission strip. -/
theorem analyticOnNhd_deningerDampedLogSource_mellin (a : {a : ℝ // 1/2<a}) :
    AnalyticOnNhd ℂ (deningerMeyerStrongLogMellin (deningerDampedLogSource a))
      {s : ℂ | 1-a.val < s.re ∧ s.re < a.val} := by
  have hopen : IsOpen {s : ℂ | 1-a.val < s.re ∧ s.re < a.val} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro s hs
  exact (hasDerivAt_deningerDampedLogSource_jet_integral a 0 s hs.1 hs.2).differentiableAt.differentiableWithinAt

/-- The Euler quotient derivatives are the actual source integrals at every finite order. -/
theorem deningerDampedLogSource_jet_eq_euler_derivative (a : {a : ℝ // 1/2<a})
    (k : ℕ) (s : ℂ) (hs0 : 1-a.val < s.re) (hs1 : s.re < a.val) :
    (∫ t, deningerMeyerStrongLogMellinJet k s (deningerDampedLogSource a) t) =
      iteratedDeriv k (fun z =>
        deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource z /
          (riemannZeta ((a.val : ℂ)+z)*riemannZeta ((a.val : ℂ)+1-z))) s := by
  rw [← iteratedDeriv_deningerDampedLogSource_mellin a k s hs0 hs1]
  apply Filter.EventuallyEq.iteratedDeriv_eq k
  have hopen : IsOpen {z : ℂ | 1-a.val < z.re ∧ z.re < a.val} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  filter_upwards [hopen.mem_nhds ⟨hs0,hs1⟩] with z hz
  exact deningerDampedLogSource_mellin_eq a z hz.1 hz.2

private theorem damped_source_xi_coordinate (rho : XiDivisorSupport) :
    (1/2 : ℂ)+xiSpectralPointSupport rho*I = (rho : ℂ) := by
  dsimp [xiSpectralPointSupport]
  rw [mul_assoc,neg_mul,I_mul_I,neg_neg,mul_one]
  ring

/-- Source-side analyticity at each actual centered Xi point, with no simplicity premise. -/
theorem deningerDampingOne_source_analyticAt_xiPlane (rho : XiDivisorSupport) :
    AnalyticAt ℂ (fun z : ℂ => deningerMeyerStrongLogMellin
      (deningerDampedLogSource ⟨1,by norm_num⟩) (1/2+z*I)) (xiSpectralPointSupport rho) := by
  have hsource : AnalyticAt ℂ (deningerMeyerStrongLogMellin
      (deningerDampedLogSource ⟨1,by norm_num⟩)) (rho : ℂ) := by
    apply analyticOnNhd_deningerDampedLogSource_mellin
    simpa using xi_divisor_support_re_mem_open_unit rho
  rw [← damped_source_xi_coordinate rho] at hsource
  exact hsource.comp (f := fun z : ℂ => 1/2+z*I) (x := xiSpectralPointSupport rho)
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 1/2+z*I) (xiSpectralPointSupport rho))

/-- Literal Xi response of the damping-one source in the original centered coordinate. -/
def deningerDampingOneXiResponse (z : ℂ) : ℂ :=
  XiC z * deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨1,by norm_num⟩) (1/2+z*I)

/-- Multiplication by the actual source preserves the native Xi analytic order. -/
theorem deningerDampingOneXiResponse_native_order (rho : XiDivisorSupport) :
    analyticOrderAt deningerDampingOneXiResponse (xiSpectralPointSupport rho) =
      analyticOrderAt XiC (xiSpectralPointSupport rho) := by
  have hnonzero : deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨1,by norm_num⟩)
      (1/2+xiSpectralPointSupport rho*I) ≠ 0 := by
    rw [damped_source_xi_coordinate]
    exact deningerDampingOne_source_xi_ne_zero rho
  change analyticOrderAt (XiC * (fun z : ℂ => deningerMeyerStrongLogMellin
      (deningerDampedLogSource ⟨1,by norm_num⟩) (1/2+z*I))) _ = _
  have horder : analyticOrderAt (fun z : ℂ => deningerMeyerStrongLogMellin
      (deningerDampedLogSource ⟨1,by norm_num⟩) (1/2+z*I)) (xiSpectralPointSupport rho) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hnonzero)
  rw [analyticOrderAt_mul (XiC_analytic _ (Set.mem_univ _))
    (deningerDampingOne_source_analyticAt_xiPlane rho),horder,add_zero]

/-- All lower native Xi jets remain zero after actual source multiplication. -/
theorem deningerDampingOneXiResponse_lower_jets (rho : XiDivisorSupport)
    {k : ℕ} (hk : k < xiSupportMultiplicity rho) :
    iteratedDeriv k deningerDampingOneXiResponse (xiSpectralPointSupport rho) = 0 := by
  change iteratedDeriv k (XiC * (fun z : ℂ => deningerMeyerStrongLogMellin
      (deningerDampedLogSource ⟨1,by norm_num⟩) (1/2+z*I))) _ = 0
  rw [iteratedDeriv_mul (XiC_analytic _ (Set.mem_univ _)).contDiffAt
    (deningerDampingOne_source_analyticAt_xiPlane rho).contDiffAt]
  apply Finset.sum_eq_zero
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho (hjk.trans_lt hk)]
  simp

/-- The exact native leading jet retains the old Xi coefficient times the same nonzero source. -/
theorem deningerDampingOneXiResponse_leading_jet (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) deningerDampingOneXiResponse
        (xiSpectralPointSupport rho) =
      iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho) *
        deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨1,by norm_num⟩) (rho : ℂ) := by
  change iteratedDeriv (xiSupportMultiplicity rho) (XiC * (fun z : ℂ =>
      deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨1,by norm_num⟩) (1/2+z*I))) _ = _
  rw [iteratedDeriv_mul (XiC_analytic _ (Set.mem_univ _)).contDiffAt
    (deningerDampingOne_source_analyticAt_xiPlane rho).contDiffAt]
  rw [Finset.sum_eq_single (xiSupportMultiplicity rho)]
  · simp only [Nat.choose_self,Nat.cast_one,Nat.sub_self,iteratedDeriv_zero,
      one_mul,damped_source_xi_coordinate]
  · intro j hj hjm
    have hj' : j < xiSupportMultiplicity rho := by
      rw [Finset.mem_range] at hj
      omega
    rw [iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hj']
    simp
  · simp

/-- The actual source response has a nonzero leading jet at every original Xi multiplicity. -/
theorem deningerDampingOneXiResponse_leading_jet_ne_zero (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) deningerDampingOneXiResponse
      (xiSpectralPointSupport rho) ≠ 0 := by
  rw [deningerDampingOneXiResponse_leading_jet]
  exact mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
    (deningerDampingOne_source_xi_ne_zero rho)

end RHTower
