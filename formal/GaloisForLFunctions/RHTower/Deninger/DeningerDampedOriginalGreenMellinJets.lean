import GaloisForLFunctions.RHTower.Deninger.DeningerDampedOriginalGreenMellin

/-!
# Literal jets of the original prime Green source

Nearby admitted exponential weights control every finite Mellin jet of the
same function. This gives absolute integral admission and differentiation on
the open strip `max(0, 1-a) < Re(s) < a` for the actual future Green sum.
Every finite-prime Green jet converges to the corresponding full-source jet;
all derivatives of the original prime denominator are retained.

At damping one, every native Xi point and every finite order are admitted.
These results do not assert a bound uniform in jet order, a zero-damping
source limit, or agreement with the fixed cyclic/physical boundary reader.
-/

open Complex Filter Topology MeasureTheory
noncomputable section
namespace RHTower

private theorem open_strip_margin {l u c : ℝ} (hl : l < c) (hu : c < u) :
    ∃ d : ℝ, 0 < d ∧ l < c-d ∧ c+d < u := by
  let d := min (c-l) (u-c)/2
  have hm : 0 < min (c-l) (u-c) := lt_min (by linarith) (by linarith)
  have h1 := min_le_left (c-l) (u-c)
  have h2 := min_le_right (c-l) (u-c)
  refine ⟨d, by dsimp [d]; positivity, ?_, ?_⟩ <;> dsimp [d] <;> linarith

private theorem strip_jet_measurable (f : ℝ → ℂ) (k : ℕ) (s : ℂ)
    (hf : Integrable (deningerMeyerStrongLogMellinJet 0 s f)) :
    AEStronglyMeasurable (deningerMeyerStrongLogMellinJet k s f) volume := by
  have hp : AEStronglyMeasurable (fun t : ℝ => (t : ℂ)^k) volume :=
    (by fun_prop : Continuous (fun t : ℝ => (t : ℂ)^k)).aestronglyMeasurable
  have heq : deningerMeyerStrongLogMellinJet k s f =
      (fun t : ℝ => (t : ℂ)^k) * deningerMeyerStrongLogMellinJet 0 s f := by
    funext t
    simp only [Pi.mul_apply, deningerMeyerStrongLogMellinJet, pow_zero, one_mul, mul_assoc]
  rw [heq]
  exact hp.mul hf.aestronglyMeasurable

/-- Nearby admitted zeroth moments control every literal jet of the same function. -/
theorem deningerStripMellin_jet_integrable (f : ℝ → ℂ) {l u : ℝ}
    (hf : ∀ s : ℂ, l < s.re → s.re < u →
      Integrable (deningerMeyerStrongLogMellinJet 0 s f))
    (k : ℕ) (s : ℂ) (hl : l < s.re) (hu : s.re < u) :
    Integrable (deningerMeyerStrongLogMellinJet k s f) := by
  obtain ⟨d, hd, hlo, hhi⟩ := open_strip_margin hl hu
  let lo : ℂ := (s.re-d : ℝ)
  let hi : ℂ := (s.re+d : ℝ)
  have hlow := hf lo hlo (by dsimp [lo]; linarith)
  have hhigh := hf hi (by dsimp [hi]; linarith) hhi
  have hb := (hlow.norm.add hhigh.norm).const_mul ((k.factorial : ℝ)/d^k)
  apply hb.mono' (strip_jet_measurable f k s (hf s hl hu))
  filter_upwards with t
  have h := mul_le_mul_of_nonneg_right (deninger_abs_pow_exp_le_two_weights k s.re hd t)
    (norm_nonneg (f t))
  simpa only [norm_deningerMeyerStrongLogMellinJet, pow_zero, one_mul, lo, hi,
    Complex.ofReal_re, Pi.add_apply, mul_add, add_mul, mul_assoc] using h

private theorem exp_weight_strip {b c d : ℝ} (hb : c-d ≤ b) (hc : b ≤ c+d) (t : ℝ) :
    Real.exp (b*t) ≤ Real.exp ((c-d)*t)+Real.exp ((c+d)*t) := by
  by_cases ht : 0 ≤ t
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc ht)).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hb (le_of_not_ge ht))).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)

/-- Differentiation of literal Mellin jets uses only the actual open-strip domain. -/
theorem hasDerivAt_deningerStripMellin_jet_integral (f : ℝ → ℂ) {l u : ℝ}
    (hf : ∀ s : ℂ, l < s.re → s.re < u →
      Integrable (deningerMeyerStrongLogMellinJet 0 s f))
    (k : ℕ) (s : ℂ) (hl : l < s.re) (hu : s.re < u) :
    HasDerivAt (fun z => ∫ t, deningerMeyerStrongLogMellinJet k z f t)
      (∫ t, deningerMeyerStrongLogMellinJet (k+1) s f t) s := by
  obtain ⟨d, hd, hlo, hhi⟩ := open_strip_margin hl hu
  let lo : ℂ := (s.re-d : ℝ)
  let hi : ℂ := (s.re+d : ℝ)
  let B : ℝ → ℝ := fun t =>
    ‖deningerMeyerStrongLogMellinJet (k+1) lo f t‖ +
      ‖deningerMeyerStrongLogMellinJet (k+1) hi f t‖
  have hB : Integrable B :=
    (deningerStripMellin_jet_integrable f hf (k+1) lo hlo (by dsimp [lo]; linarith)).norm.add
      (deningerStripMellin_jet_integrable f hf (k+1) hi (by dsimp [hi]; linarith) hhi).norm
  have hdom : ∀ᵐ t : ℝ, ∀ z ∈ Metric.ball s d,
      ‖deningerMeyerStrongLogMellinJet (k+1) z f t‖ ≤ B t := by
    filter_upwards with t
    intro z hz
    have he := Complex.abs_re_le_norm (z-s)
    rw [Complex.sub_re] at he
    have hn : ‖z-s‖ < d := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
    have hlz : s.re-d ≤ z.re := by
      linarith [(le_abs_self (z.re-s.re)).trans he, neg_abs_le (z.re-s.re)]
    have huz : z.re ≤ s.re+d := by linarith [(le_abs_self (z.re-s.re)).trans he]
    have hb := exp_weight_strip hlz huz t
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (pow_nonneg (abs_nonneg t) (k+1))) (norm_nonneg (f t))
    simpa only [B, norm_deningerMeyerStrongLogMellinJet, lo, hi, Complex.ofReal_re,
      mul_add, add_mul] using hm
  have hmeas : ∀ z : ℂ,
      AEStronglyMeasurable (deningerMeyerStrongLogMellinJet k z f) volume := by
    intro z
    have heq : deningerMeyerStrongLogMellinJet k z f =
        fun t : ℝ => ((t : ℂ)^k * Complex.exp ((z-s)*(t : ℂ))) *
          deningerMeyerStrongLogMellinJet 0 s f t := by
      funext t
      simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul, mul_assoc]
      rw [← mul_assoc (Complex.exp ((z-s)*(t : ℂ))) (Complex.exp (s*(t : ℂ))) (f t),
        ← Complex.exp_add, show (z-s)*(t : ℂ)+s*(t : ℂ) = z*(t : ℂ) by ring]
    rw [heq]
    exact (by fun_prop : Continuous (fun t : ℝ =>
      (t : ℂ)^k * Complex.exp ((z-s)*(t : ℂ)))).aestronglyMeasurable.mul
        (hf s hl hu).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => deningerMeyerStrongLogMellinJet k z f t)
    (F' := fun z t => deningerMeyerStrongLogMellinJet (k+1) z f t)
    (x₀ := s) (s := Metric.ball s d) (bound := B)
    (Metric.ball_mem_nhds s hd) (Eventually.of_forall hmeas)
    (deningerStripMellin_jet_integrable f hf k s hl hu)
    (strip_jet_measurable f (k+1) s (hf s hl hu)) hdom hB (by
      filter_upwards with t
      intro z hz
      exact hasDerivAt_deningerMeyerStrongLogMellinJet k z f t)).2

/-- All analytic derivatives are the literal admitted integral readers. -/
theorem iteratedDeriv_deningerStripMellin_eq_integral_jet (f : ℝ → ℂ) {l u : ℝ}
    (hf : ∀ s : ℂ, l < s.re → s.re < u →
      Integrable (deningerMeyerStrongLogMellinJet 0 s f))
    (k : ℕ) (s : ℂ) (hl : l < s.re) (hu : s.re < u) :
    iteratedDeriv k (deningerMeyerStrongLogMellin f) s =
      ∫ t, deningerMeyerStrongLogMellinJet k s f t := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hop : IsOpen {z : ℂ | l < z.re ∧ z.re < u} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have heq : iteratedDeriv k (deningerMeyerStrongLogMellin f) =ᶠ[𝓝 s]
        (fun z => ∫ t, deningerMeyerStrongLogMellinJet k z f t) := by
      filter_upwards [hop.mem_nhds ⟨hl,hu⟩] with z hz
      exact ih z hz.1 hz.2
    rw [heq.deriv_eq]
    exact (hasDerivAt_deningerStripMellin_jet_integral f hf k s hl hu).deriv

private theorem original_green_strip_admission (a : {a : ℝ // 1/2<a}) (p : Nat.Primes)
    (s : ℂ) (hl : max 0 (1-a.val) < s.re) (hu : s.re < a.val) :
    Integrable (deningerMeyerStrongLogMellinJet 0 s (deningerDampedOriginalPrimeGreen a p)) :=
  deningerDampedOriginalPrimeGreen_weighted_integrable a p s
    ((le_max_left _ _).trans_lt hl) ((le_max_right _ _).trans_lt hl) hu

/-- Every literal jet of the unchanged original Green sum is absolutely admitted. -/
theorem deningerDampedOriginalPrimeGreen_jet_integrable
    (a : {a : ℝ // 1/2<a}) (p : Nat.Primes) (k : ℕ) (s : ℂ)
    (hs : 0 < s.re) (hl : 1-a.val < s.re) (hu : s.re < a.val) :
    Integrable (deningerMeyerStrongLogMellinJet k s (deningerDampedOriginalPrimeGreen a p)) :=
  deningerStripMellin_jet_integrable _ (original_green_strip_admission a p) k s
    (max_lt hs hl) hu

/-- Agreement of analytic and literal integral readers for the complete original Green source. -/
theorem iteratedDeriv_deningerDampedOriginalPrimeGreen_mellin
    (a : {a : ℝ // 1/2<a}) (p : Nat.Primes) (k : ℕ) (s : ℂ)
    (hs : 0 < s.re) (hl : 1-a.val < s.re) (hu : s.re < a.val) :
    iteratedDeriv k (deningerMeyerStrongLogMellin (deningerDampedOriginalPrimeGreen a p)) s =
      ∫ t, deningerMeyerStrongLogMellinJet k s (deningerDampedOriginalPrimeGreen a p) t :=
  iteratedDeriv_deningerStripMellin_eq_integral_jet _ (original_green_strip_admission a p)
    k s (max_lt hs hl) hu

/-- The literal jet reader is the derivative of the full original Euler expression. -/
theorem deningerDampedOriginalPrimeGreen_jet_eq_euler_derivative
    (a : {a : ℝ // 1/2<a}) (p : Nat.Primes) (k : ℕ) (s : ℂ)
    (hs : 0 < s.re) (hl : 1-a.val < s.re) (hu : s.re < a.val) :
    (∫ t, deningerMeyerStrongLogMellinJet k s (deningerDampedOriginalPrimeGreen a p) t) =
      iteratedDeriv k (fun z =>
        (deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource z /
          (riemannZeta ((a.val : ℂ)+z)*riemannZeta ((a.val : ℂ)+1-z))) /
            (1-(p : ℂ)^(-z))) s := by
  rw [← iteratedDeriv_deningerDampedOriginalPrimeGreen_mellin a p k s hs hl hu]
  apply Filter.EventuallyEq.iteratedDeriv_eq k
  have hop : IsOpen {z : ℂ | 0 < z.re ∧ 1-a.val < z.re ∧ z.re < a.val} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const))
  filter_upwards [hop.mem_nhds ⟨hs,hl,hu⟩] with z hz
  rw [deningerDampedOriginalPrimeGreen_mellin a p z hz.1 hz.2.1 hz.2.2,
    deningerDampedLogSource_mellin_eq a z hz.2.1 hz.2.2]

/-- All original Xi copies admit the literal Green reader at every native finite order. -/
theorem deningerDampingOneOriginalPrimeGreen_all_xi_jets
    (p : Nat.Primes) (rho : XiDivisorSupport) (k : ℕ) :
    Integrable (deningerMeyerStrongLogMellinJet k (rho : ℂ)
      (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p)) ∧
    iteratedDeriv k (deningerMeyerStrongLogMellin
      (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p)) (rho : ℂ) =
        ∫ t, deningerMeyerStrongLogMellinJet k (rho : ℂ)
          (deningerDampedOriginalPrimeGreen ⟨1,by norm_num⟩ p) t := by
  have h := xi_divisor_support_re_mem_open_unit rho
  exact ⟨deningerDampedOriginalPrimeGreen_jet_integrable _ p k rho h.1 (by simpa using h.1) h.2,
    iteratedDeriv_deningerDampedOriginalPrimeGreen_mellin _ p k rho h.1 (by simpa using h.1) h.2⟩

private theorem mellinJet_zero_eq (s : ℂ) (f : ℝ → ℂ) :
    deningerMeyerStrongLogMellinJet 0 s f =
      (fun t : ℝ => Complex.exp (s*(t : ℂ))*f t) := by
  funext t
  simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul]

private theorem original_prime_log_pos (p : Nat.Primes) : 0 < Real.log (p : ℕ) :=
  Real.log_pos (by exact_mod_cast p.property.one_lt)

private theorem strong_prime_green_admission (g : DeningerMeyerStrongLogTarget)
    (p : Nat.Primes) (s : ℂ) (hs : 0 < s.re) :
    Integrable (deningerMeyerStrongLogMellinJet 0 s
      (deningerL1OriginalGreenSum g (Real.log (p : ℕ)))) := by
  have hf : Integrable (fun t : ℝ => Complex.exp (s*(t : ℂ))*(g : ℝ → ℂ) t) := by
    simpa only [mellinJet_zero_eq] using
      integrable_deningerMeyerStrongLogMellinJet g.property 0 s
  simpa only [mellinJet_zero_eq] using
    deningerL1OriginalGreenSum_weighted_integrable (original_prime_log_pos p) hs hf

/-- Each original finite source's Green primitive admits every right-half-plane jet. -/
theorem deningerStrongSourceOriginalPrimeGreen_jet_integrable
    (g : DeningerMeyerStrongLogTarget) (p : Nat.Primes) (k : ℕ) (s : ℂ)
    (hs : 0 < s.re) :
    Integrable (deningerMeyerStrongLogMellinJet k s
      (deningerL1OriginalGreenSum g (Real.log (p : ℕ)))) :=
  deningerStripMellin_jet_integrable _ (u := s.re+1)
    (fun z hz _ => strong_prime_green_admission g p z hz) k s hs (by linarith)

/-- The finite-source Green derivative is its literal integral jet. -/
theorem iteratedDeriv_deningerStrongSourceOriginalPrimeGreen_mellin
    (g : DeningerMeyerStrongLogTarget) (p : Nat.Primes) (k : ℕ) (s : ℂ)
    (hs : 0 < s.re) :
    iteratedDeriv k (deningerMeyerStrongLogMellin
      (deningerL1OriginalGreenSum g (Real.log (p : ℕ)))) s =
        ∫ t, deningerMeyerStrongLogMellinJet k s
          (deningerL1OriginalGreenSum g (Real.log (p : ℕ))) t :=
  iteratedDeriv_deningerStripMellin_eq_integral_jet _ (u := s.re+1)
    (fun z hz _ => strong_prime_green_admission g p z hz) k s hs (by linarith)

private theorem strong_prime_green_derivative (g : DeningerMeyerStrongLogTarget)
    (p : Nat.Primes) (k : ℕ) (s : ℂ) (hs : 0 < s.re) :
    iteratedDeriv k (deningerMeyerStrongLogMellin
      (deningerL1OriginalGreenSum g (Real.log (p : ℕ)))) s =
        iteratedDeriv k (fun z => deningerMeyerStrongLogMellin g z /
          (1-Complex.exp (-z*(Real.log (p : ℕ) : ℂ)))) s := by
  apply Filter.EventuallyEq.iteratedDeriv_eq k
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  have hf : Integrable (fun t : ℝ => Complex.exp (z*(t : ℂ))*(g : ℝ → ℂ) t) := by
    simpa only [mellinJet_zero_eq] using
      integrable_deningerMeyerStrongLogMellinJet g.property 0 z
  simpa only [deningerMeyerStrongLogMellin, deningerMeyerStrongLogMellinJet,
    pow_zero, one_mul] using
      deningerL1OriginalGreenSum_mellin (original_prime_log_pos p) hz hf

/-- Every finite literal Green jet passes from the original prime prefixes to the full source. -/
theorem deningerDampedOriginalPrimeGreen_jet_tendsto
    (a : {a : ℝ // 1/2<a}) (p : Nat.Primes) (k : ℕ) (s : ℂ)
    (hs : 0 < s.re) (hl : 1-a.val < s.re) (hu : s.re < a.val) :
    Tendsto (fun n => ∫ t, deningerMeyerStrongLogMellinJet k s
      (deningerL1OriginalGreenSum
        (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList)
        (Real.log (p : ℕ))) t) atTop
      (𝓝 (∫ t, deningerMeyerStrongLogMellinJet k s
        (deningerDampedOriginalPrimeGreen a p) t)) := by
  let D : ℂ → ℂ := fun z => (1-Complex.exp (-z*(Real.log (p : ℕ) : ℂ)))⁻¹
  have hD : AnalyticAt ℂ D s :=
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ =>
      1-Complex.exp (-z*(Real.log (p : ℕ) : ℂ))) s).inv
        (deningerOriginalGreen_denominator_ne_zero (original_prime_log_pos p) hs)
  have hfull := (analyticOnNhd_deningerDampedLogSource_mellin a s ⟨hl,hu⟩).contDiffAt (n := k)
  have hfinite (n : ℕ) := (analyticOnNhd_deningerMeyerStrongLogMellin
    (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList).property
      s (Set.mem_univ _)).contDiffAt (n := k)
  have hlim := tendsto_finsetSum (Finset.range (k+1)) (fun i _ =>
    ((deningerDampedLogSource_mellin_derivatives_tendsto a i s hl hu).const_mul
      (k.choose i : ℂ)).mul_const (iteratedDeriv (k-i) D s))
  have hfull_eq : (∫ t, deningerMeyerStrongLogMellinJet k s
      (deningerDampedOriginalPrimeGreen a p) t) =
        ∑ i ∈ Finset.range (k+1), (k.choose i : ℂ) *
          iteratedDeriv i (deningerMeyerStrongLogMellin (deningerDampedLogSource a)) s *
          iteratedDeriv (k-i) D s := by
    rw [← iteratedDeriv_deningerDampedOriginalPrimeGreen_mellin a p k s hs hl hu,
      deningerDampedOriginalPrimeGreen_mellin_derivative a p k s hs hl hu]
    change iteratedDeriv k (deningerMeyerStrongLogMellin (deningerDampedLogSource a) * D) s = _
    exact iteratedDeriv_mul hfull hD.contDiffAt
  rw [hfull_eq]
  apply hlim.congr'
  filter_upwards with n
  rw [← iteratedDeriv_deningerStrongSourceOriginalPrimeGreen_mellin _ p k s hs,
    strong_prime_green_derivative _ p k s hs]
  change _ = iteratedDeriv k (deningerMeyerStrongLogMellin
    (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList) * D) s
  exact (iteratedDeriv_mul (hfinite n) hD.contDiffAt).symm

end RHTower
