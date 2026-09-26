import GaloisForLFunctions.RHTower.ThetaPowerSaddleIntegral

/-!
# Strip rigidity above the cusp-order wall

For `a > 1/2` the transform `Λ_a(w) = ∫ e^{-iwx} T_a(x) dx` of `F_a = θ₃h^{a/4}` has only finitely
many zeros in the closed critical strip `|Im w| ≤ 1/2`.

At `w = u + iv` the contour shift to `Im z = -β` gives `Λ_a(w) = e^{-wβ} ∫ e^{-ius} e^{vs} T_a(s - iβ) ds`:
the imaginary part of the frequency only inserts the positive weight `e^{vs}`.  Positivity of a real
part survives a positive weight, so the saddle estimate goes through with the weight: the core keeps
positive real part, the Gaussian and the Farey far field absorb `e^{|s|/2}`, and every large `u` is
a saddle frequency.  Evenness and holomorphy on `|Im w| < 1` confine the remaining zeros to a
compact rectangle.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower

noncomputable section

section Weighted

variable {a t : ℝ}

/-- Far-field thresholds with a general denominator `D`. -/
def chFarQ1D (a D : ℝ) : ℝ :=
  720 * 36 ^ a / ((2 : ℝ) ^ (-(2 * a)) / (D * (a + 1)) * (2 * (3 * chMa a / 16) / 3) ^ 6)

def chFarQ2D (a D M : ℝ) : ℝ :=
  720 * M / (π * a / 4 * ((2 : ℝ) ^ (-(2 * a)) / (D * (a + 1))) * (3 * chMa a / 16) ^ 6)

theorem two_chBfarA_le_div (ha : 1 / 2 < a) {D : ℝ} (hD : 0 < D) (ht0 : 0 < t)
    (ht1 : t ≤ 1 / 100) {M : ℝ} (hM0 : 0 ≤ M) (h1 : t * chFarQ1D a D ≤ 1)
    (h2 : t * chFarQ2D a D M ≤ 1) :
    2 * chBfarA a t M ≤ chG0a a t * t ^ 3 / (D * (a + 1)) := by
  have ht1' : t ≤ 1 := by linarith
  have ht4 : t ^ 4 ≤ 3 / 4 := by
    have := pow_le_of_le_one ht0.le ht1' (by norm_num : (4:ℕ) ≠ 0); nlinarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have := pow_le_of_le_one ht0.le ht1' (by norm_num : (2:ℕ) ≠ 0); nlinarith
  have hκ := chKap_ge ht4
  have hm := chMa_pos ha
  have hμ : 0 < 3 * chMa a / 16 := by positivity
  have hRt := chR0m_mul_sq_ge hm.le ht0 ht4
  have hp := one_le_chP0 ht0 ht2
  have hK : 0 < a + 1 := by linarith
  set c : ℝ := (2 : ℝ) ^ (-(2 * a)) / (D * (a + 1)) with hc
  have hc0 : 0 < c := by positivity
  have hGt : c * Real.exp (chR0m (chMa a) t) * t ^ 3 ≤ chG0a a t * t ^ 3 / (D * (a + 1)) := by
    unfold chG0a
    rw [hc]
    have e : (2 : ℝ) ^ (-(2 * a)) / (D * (a + 1)) * Real.exp (chR0m (chMa a) t) * t ^ 3 =
        (2 : ℝ) ^ (-(2 * a)) * 1 * Real.exp (chR0m (chMa a) t) * t ^ 3 / (D * (a + 1)) := by
      ring
    rw [e]
    gcongr
  have hA : (0 : ℝ) ≤ 36 ^ a := by positivity
  have hb1 := far_one_real (A := 36 ^ a) (c := c) (μ := 3 * chMa a / 16) ht0 ht1' hκ hμ hRt hA hc0
    (by unfold chFarQ1D at h1; rw [hc]; exact h1)
  have hr : 0 < π * a / 4 := by have := Real.pi_pos; nlinarith
  have hb2 := far_two_real (M := M) (r := π * a / 4) (c := c) (μ := 3 * chMa a / 16) ht0 ht1' hκ hμ
    hRt hM0 hr hc0 (by unfold chFarQ2D at h2; rw [hc]; exact h2)
  unfold chBfarA
  rw [mul_comm, max_mul_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  refine le_trans (max_le ?_ hb2) hGt
  linarith

/-- The Gaussian decay of the window integrand beyond a core of radius `Λt³`. -/
theorem norm_chLineA_le_mid (ha : 1 / 2 < a) (h : chSmallA a t) {Λ s : ℝ}
    (hΛs : Λ * t ^ 3 ≤ |s|) (h2 : |s| ≤ 2 * t ^ 2) :
    ‖chLineA a t s‖ ≤ 9 / 8 * chG0a a t * Real.exp (-(chMa a * Λ / (28 * t ^ 3) * |s|)) := by
  have ha0 : 0 ≤ a := by linarith
  have ht0 := h.1
  have hm := chMa_pos ha
  have hw := norm_chLineA_le_window ha0 h h2
  have hmid := chR0m_sub_psim_re_ge_mid_real hm ht0 (by nlinarith [h.t2 ha0]) h2
  have hk : chMa a * Λ / (28 * t ^ 3) * |s| ≤ chMa a * s ^ 2 / (28 * t ^ 6) := by
    have e : chMa a * Λ / (28 * t ^ 3) * |s| = chMa a * (Λ * t ^ 3 * |s|) / (28 * t ^ 6) := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hm.le
    rw [← sq_abs s, sq]
    exact mul_le_mul_of_nonneg_right hΛs (abs_nonneg s)
  have hexp : Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) ≤
      Real.exp (-(chMa a * Λ / (28 * t ^ 3) * |s|)) :=
    Real.exp_le_exp.mpr (by linarith)
  refine le_trans hw ?_
  have hG := chG0a_pos a t
  have := mul_le_mul_of_nonneg_left hexp (by positivity : (0:ℝ) ≤ 9 / 8 * chG0a a t)
  linarith

/-- The weighted core radius `Λ = 4032K/m + 1`. -/
def chLamB (a : ℝ) : ℝ := 4032 * (a + 1) / chMa a + 1

theorem chLamA_le_chLamB (ha : 1 / 2 < a) : chLamA a ≤ chLamB a := by
  unfold chLamA chLamB
  have hm := chMa_pos ha
  have hK : 0 ≤ a + 1 := by linarith
  have : 1008 * (a + 1) / chMa a ≤ 4032 * (a + 1) / chMa a :=
    div_le_div_of_nonneg_right (by nlinarith) hm.le
  linarith

/-- The weighted integrand `e^{vs}` times the saddle integrand. -/
def chLineAW (a t v s : ℝ) : ℂ := (Real.exp (v * s) : ℂ) * chLineA a t s

theorem norm_chLineAW_le {v : ℝ} (hv : |v| ≤ 1 / 2) (s : ℝ) :
    ‖chLineAW a t v s‖ ≤ Real.exp (|s| / 2) * ‖chLineA a t s‖ := by
  unfold chLineAW
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have h1 : v * s ≤ |v * s| := le_abs_self _
  rw [abs_mul] at h1
  have := mul_le_mul_of_nonneg_right hv (abs_nonneg s)
  linarith

theorem re_chLineAW (a t v s : ℝ) :
    (chLineAW a t v s).re = Real.exp (v * s) * (chLineA a t s).re := by
  unfold chLineAW; rw [Complex.re_ofReal_mul]

theorem integrable_chLineAW (ha : 0 < a) (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) {v : ℝ}
    (hv : |v| ≤ 1 / 2) : Integrable (chLineAW a t v) := by
  have hβ := chBeta_lt ht (by linarith)
  have hβ0 := chBeta_nonneg ht2
  obtain ⟨C, _, hbd⟩ := thetaPowerTail_decay ha (chBeta t) hβ0 hβ
  have hcont : Continuous (chLineAW a t v) := by
    unfold chLineAW
    exact (Complex.continuous_ofReal.comp (by fun_prop)).mul (continuous_chLineA ht ht2)
  refine Integrable.mono' ((integrable_exp_neg_mul_abs' (by norm_num : (0:ℝ) < 1 / 2)).const_mul C)
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  have hz : |((s : ℂ) - (chBeta t : ℂ) * Complex.I).im| ≤ chBeta t := by
    simp [abs_of_nonneg hβ0]
  have h1 := hbd _ hz
  have hre : ((s : ℂ) - (chBeta t : ℂ) * Complex.I).re = s := by simp
  rw [hre, ← norm_chLineA] at h1
  refine (norm_chLineAW_le hv s).trans ?_
  calc Real.exp (|s| / 2) * ‖chLineA a t s‖ ≤ Real.exp (|s| / 2) * (C * Real.exp (-|s|)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = C * Real.exp (-(1 / 2 * |s|)) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- **Lower bound for the weighted saddle-line integral.** -/
theorem re_chLineAWInt_ge (ha : 1 / 2 < a) (h : chSmallA a t)
    (hcore : t * (176 * (a + 1) * chLamB a ^ 3) ≤ 1) {M : ℝ}
    (hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaPowerForm a τ‖ ≤ M * Real.exp (-(π * a / 4) * τ.im))
    {v : ℝ} (hv : |v| ≤ 1 / 2) :
    chG0a a t * t ^ 3 / (32 * (a + 1)) - 4 * chBfarA a t M ≤
      (∫ s : ℝ, chLineAW a t v s).re := by
  have ha0 : 0 ≤ a := by linarith
  have ht0 := h.1
  have ht1 : t ≤ 1 := by linarith [h.le ha0]
  have ht2' : t ^ 2 ≤ 1 / 2 := by linarith [h.t2 ha0]
  have hm := chMa_pos ha
  have hK : 0 < a + 1 := by linarith
  have hΛA := one_le_chLamA ha
  have hΛB : 1 ≤ chLamB a := le_trans hΛA (chLamA_le_chLamB ha)
  have hcoreA : t * (176 * (a + 1) * chLamA a ^ 3) ≤ 1 := by
    refine le_trans ?_ hcore
    apply mul_le_mul_of_nonneg_left _ ht0.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by linarith) (chLamA_le_chLamB ha) 3
  have hG := chG0a_pos a t
  have hint := integrable_chLineAW (a := a) (by linarith) ht0 ht2' hv
  have hre_int : Integrable (fun s => (chLineAW a t v s).re) := hint.re
  set ι : ℝ := t ^ 3 / (4 * (a + 1)) with hι
  have hι0 : 0 ≤ ι := by positivity
  have hι1 : ι ≤ 1 := by
    rw [hι, div_le_one (by positivity)]
    have : t ^ 3 ≤ 1 := pow_le_one₀ ht0.le ht1
    linarith
  set k : ℝ := chMa a * chLamB a / (28 * t ^ 3) with hk
  have hmΛ : chMa a * chLamB a = 4032 * (a + 1) + chMa a := by
    unfold chLamB; field_simp
  have hk1 : 1 ≤ k := by
    rw [hk, le_div_iff₀ (by positivity), hmΛ]
    have : t ^ 3 ≤ 1 := pow_le_one₀ ht0.le ht1
    nlinarith
  set B : ℝ := chBfarA a t M with hBdef
  have hBf : 0 ≤ B := chBfarA_nonneg ht0 (by nlinarith [pow_pos ht0 2]) M
  have hk2 : 0 < k / 2 := by linarith
  set lam : ℝ → ℝ := fun s =>
    9 / 8 * chG0a a t * Real.exp (-(k / 2 * |s|)) + B * Real.exp (-(1 / 2 * |s|)) with hlam
  have hlam_int : Integrable lam :=
    ((integrable_exp_neg_mul_abs' hk2).const_mul _).add
      ((integrable_exp_neg_mul_abs' (by norm_num : (0:ℝ) < 1 / 2)).const_mul _)
  have hlam_val : ∫ s, lam s = 126 * chG0a a t * t ^ 3 / (chMa a * chLamB a) + 4 * B := by
    rw [hlam, integral_add ((integrable_exp_neg_mul_abs' hk2).const_mul _)
      ((integrable_exp_neg_mul_abs' (by norm_num : (0:ℝ) < 1 / 2)).const_mul _),
      integral_const_mul, integral_const_mul, integral_exp_neg_mul_abs_eq hk2,
      integral_exp_neg_mul_abs_eq (by norm_num : (0:ℝ) < 1 / 2), hk]
    field_simp; ring
  have hlamsmall : 126 * chG0a a t * t ^ 3 / (chMa a * chLamB a) ≤
      chG0a a t * t ^ 3 / (32 * (a + 1)) := by
    rw [hmΛ, div_le_div_iff₀ (by positivity) (by positivity)]
    have hGt : 0 ≤ chG0a a t * t ^ 3 := by positivity
    nlinarith
  have hinner : ∀ s ∈ Icc (-ι) ι, chG0a a t / 8 ≤ (chLineAW a t v s).re := by
    intro s hs
    have hs' : |s| ≤ ι := abs_le.mpr ⟨hs.1, hs.2⟩
    have h1 := chLineA_re_ge_inner ha h hcoreA hs'
    have he : 1 / 2 ≤ Real.exp (v * s) := by
      have h3 : -(1 / 2) ≤ v * s := by
        have := neg_abs_le (v * s)
        rw [abs_mul] at this
        have := mul_le_mul hv hs' (abs_nonneg s) (by norm_num)
        linarith
      have := Real.add_one_le_exp (v * s); linarith
    rw [re_chLineAW]
    have h4 : 0 ≤ chG0a a t / 4 := by positivity
    have := mul_le_mul he h1 h4 (Real.exp_pos _).le
    linarith
  have hout : ∀ s, -lam s ≤ (chLineAW a t v s).re := by
    intro s
    have hl1 : 0 ≤ 9 / 8 * chG0a a t * Real.exp (-(k / 2 * |s|)) := by positivity
    have hl2 : 0 ≤ B * Real.exp (-(1 / 2 * |s|)) := by positivity
    have hneg : -‖chLineAW a t v s‖ ≤ (chLineAW a t v s).re := by
      have := Complex.abs_re_le_norm (chLineAW a t v s)
      have := neg_abs_le (chLineAW a t v s).re
      linarith
    have hW := norm_chLineAW_le (a := a) (t := t) hv s
    simp only [hlam]
    rcases le_or_gt |s| (chLamB a * t ^ 3) with h1 | h1
    · have h3 := half_le_re_chLineA_core ha h (by linarith) (chMa_le ha0) hΛB hcore h1
      have : 0 ≤ chG0a a t * Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) / 2 := by
        positivity
      rw [re_chLineAW]
      have := mul_nonneg (Real.exp_pos (v * s)).le (le_trans this h3)
      linarith
    rcases le_or_gt |s| (2 * t ^ 2) with h2 | h2
    · have h3 := norm_chLineA_le_mid ha h h1.le h2
      have h4 : Real.exp (|s| / 2) * (9 / 8 * chG0a a t * Real.exp (-(k * |s|))) ≤
          9 / 8 * chG0a a t * Real.exp (-(k / 2 * |s|)) := by
        rw [mul_left_comm, ← Real.exp_add]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [abs_nonneg s]
      have h5 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (|s| / 2)).le
      linarith
    · have hf := norm_chargeTailA_far ha ht0 (by nlinarith [h.t2 ha0, pow_pos ht0 2]) hM h2.le
      rw [← norm_chLineA] at hf
      have h4 : Real.exp (|s| / 2) * (B * Real.exp (-|s|)) = B * Real.exp (-(1 / 2 * |s|)) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      have h5 := mul_le_mul_of_nonneg_left hf (Real.exp_pos (|s| / 2)).le
      linarith
  have hsplit := integral_add_compl (μ := volume) measurableSet_Icc hre_int (s := Icc (-ι) ι)
  have hre_eq : (∫ s, chLineAW a t v s).re = ∫ s, (chLineAW a t v s).re :=
    (integral_re hint).symm
  rw [hre_eq, ← hsplit]
  have hA : chG0a a t / 8 * (2 * ι) ≤ ∫ s in Icc (-ι) ι, (chLineAW a t v s).re := by
    have hc : ∫ s in Icc (-ι) ι, (chG0a a t / 8 : ℝ) = chG0a a t / 8 * (2 * ι) := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]
      ring
    rw [← hc]
    exact setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Icc]))
      hre_int.integrableOn measurableSet_Icc hinner
  have hB : -(∫ s, lam s) ≤ ∫ s in (Icc (-ι) ι)ᶜ, (chLineAW a t v s).re := by
    have h1 : ∫ s in (Icc (-ι) ι)ᶜ, -lam s ≤ ∫ s in (Icc (-ι) ι)ᶜ, (chLineAW a t v s).re :=
      setIntegral_mono_on hlam_int.neg.integrableOn hre_int.integrableOn
        measurableSet_Icc.compl (fun s _ => hout s)
    have h2 : ∫ s in (Icc (-ι) ι)ᶜ, lam s ≤ ∫ s, lam s :=
      setIntegral_le_integral hlam_int (Filter.Eventually.of_forall fun s => by
        simp only [hlam]; positivity)
    rw [integral_neg] at h1
    linarith
  rw [hlam_val] at hB
  have e : chG0a a t / 8 * (2 * ι) = 2 * (chG0a a t * t ^ 3 / (32 * (a + 1))) := by
    rw [hι]; field_simp; ring
  linarith

/-- **Positivity of the weighted saddle-line integral, uniformly in `|v| ≤ 1/2`.** -/
theorem exists_re_chLineAWInt_pos (ha : 1 / 2 < a) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t : ℝ, 0 < t → t ≤ t₁ → ∀ v : ℝ, |v| ≤ 1 / 2 →
      0 < (∫ s : ℝ, chLineAW a t v s).re := by
  have ha0 : 0 ≤ a := by linarith
  set M : ℝ := thetaPowerCuspConstant a with hMdef
  have hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaPowerForm a τ‖ ≤ M * Real.exp (-(π * a / 4) * τ.im) :=
    thetaPowerForm_cuspDecay ha0
  have hM0 : 0 ≤ M := by unfold thetaPowerCuspConstant at hMdef; rw [hMdef]; positivity
  have hK : 0 < a + 1 := by linarith
  have hm := chMa_pos ha
  set A : ℝ := 20000 * (1 + a) with hA
  set B : ℝ := 176 * (a + 1) * chLamB a ^ 3 with hB
  set C₁ : ℝ := chFarQ1D a 128 with hC1
  set C₂ : ℝ := chFarQ2D a 128 M with hC2
  have hApos : 0 < A := by rw [hA]; linarith
  have hBpos : 0 < B := by
    have : 1 ≤ chLamB a := le_trans (one_le_chLamA ha) (chLamA_le_chLamB ha)
    rw [hB]; positivity
  have hC1pos : 0 ≤ C₁ := by rw [hC1]; unfold chFarQ1D; positivity
  have hC2pos : 0 ≤ C₂ := by
    rw [hC2]; unfold chFarQ2D
    have : 0 < π * a / 4 := by have := Real.pi_pos; nlinarith
    positivity
  refine ⟨min (1 / 100) (min (1 / A) (min (1 / B) (min (1 / (C₁ + 1)) (1 / (C₂ + 1))))),
    by positivity, fun t ht htt v hv => ?_⟩
  have h0 : t ≤ 1 / 100 := le_trans htt (min_le_left _ _)
  have h1 : t * A ≤ 1 := by
    have := le_trans htt (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [le_div_iff₀ hApos] at this; linarith
  have h2 : t * B ≤ 1 := by
    have := le_trans htt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    rw [le_div_iff₀ hBpos] at this; linarith
  have h3 : t * C₁ ≤ 1 := by
    have := le_trans htt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
    rw [le_div_iff₀ (by linarith)] at this; nlinarith
  have h4 : t * C₂ ≤ 1 := by
    have := le_trans htt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
    rw [le_div_iff₀ (by linarith)] at this; nlinarith
  have hsmall : chSmallA a t := by
    refine ⟨ht, ?_⟩
    have ht1 : t ≤ 1 := by linarith
    have : t ^ 2 ≤ t := by nlinarith
    have := mul_le_mul_of_nonneg_right this hApos.le
    rw [hA] at h1 this; linarith
  have hlo := re_chLineAWInt_ge ha hsmall (by rw [hB] at h2; linarith) hM hv
  have hfar := two_chBfarA_le_div ha (by norm_num : (0:ℝ) < 128) ht h0 hM0 h3 h4
  have hG := chG0a_pos a t
  have : 0 < chG0a a t * t ^ 3 / (128 * (a + 1)) := by positivity
  have e : chG0a a t * t ^ 3 / (32 * (a + 1)) = 4 * (chG0a a t * t ^ 3 / (128 * (a + 1))) := by
    field_simp; ring
  linarith

end Weighted

/-! ## The complex transform on the critical strip -/

section Strip

variable {a : ℝ}

/-- **Contour shift at a complex frequency.** -/
theorem thetaPowerXiC_eq_shift (ha : 0 < a) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 4) {w : ℂ}
    (hw : |w.im| < 1) :
    thetaPowerXiC a w = Complex.exp (-(w * β)) *
      ∫ s : ℝ, Complex.exp (-Complex.I * w * s) *
        chargeTailC (thetaPowerForm a) ((s : ℂ) - (β : ℂ) * Complex.I) := by
  obtain ⟨C, hC, hbd⟩ := thetaPowerTail_decay ha β hβ0 hβ
  set F := thetaPowerForm a
  have hF := differentiableOn_thetaPowerForm a
  set G : ℂ → ℂ := fun z => Complex.exp (-Complex.I * w * z) * chargeTailC F z with hG
  set G' : ℂ → ℂ := fun z => G (-z) with hG'
  have hdiff : ∀ z : ℂ, |z.im| ≤ β → DifferentiableAt ℂ G' z := by
    intro z hz
    have hz' : |(-z).im| < π / 4 := by rw [Complex.neg_im, abs_neg]; linarith
    have h1 : DifferentiableAt ℂ G (-z) :=
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (-Complex.I * w * z)) (-z)).mul
        (differentiableAt_chargeTailC hF hz')
    exact h1.comp z differentiableAt_id.neg
  have hr : 0 < 1 - |w.im| := by linarith
  have hbound : ∀ z : ℂ, |z.im| ≤ β →
      ‖G' z‖ ≤ (Real.exp (|w.re| * β) * C) * Real.exp (-((1 - |w.im|) * |z.re|)) := by
    intro z hz
    have hz' : |(-z).im| ≤ β := by rw [Complex.neg_im, abs_neg]; exact hz
    have h1 := hbd (-z) hz'
    rw [Complex.neg_re, abs_neg] at h1
    have hexp : ‖Complex.exp (-Complex.I * w * -z)‖ ≤
        Real.exp (|w.re| * β + |w.im| * |z.re|) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have : (-Complex.I * w * -z).re = -(w.re * z.im + w.im * z.re) := by
        simp [Complex.mul_re, Complex.mul_im]; ring
      rw [this]
      have h3 : |w.re * z.im| ≤ |w.re| * β := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      have h4 : |w.im * z.re| = |w.im| * |z.re| := abs_mul _ _
      have h5 := neg_abs_le (w.re * z.im)
      have h6 := neg_abs_le (w.im * z.re)
      linarith
    simp only [hG', hG, norm_mul]
    calc ‖Complex.exp (-Complex.I * w * -z)‖ * ‖chargeTailC F (-z)‖
        ≤ Real.exp (|w.re| * β + |w.im| * |z.re|) * (C * Real.exp (-|z.re|)) :=
          mul_le_mul hexp h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = (Real.exp (|w.re| * β) * C) * Real.exp (-((1 - |w.im|) * |z.re|)) := by
          rw [show |w.re| * β + |w.im| * |z.re| = |w.re| * β + (|w.im| * |z.re|) by ring,
            Real.exp_add]
          have : Real.exp (|w.im| * |z.re|) * Real.exp (-|z.re|) =
              Real.exp (-((1 - |w.im|) * |z.re|)) := by rw [← Real.exp_add]; congr 1; ring
          calc Real.exp (|w.re| * β) * Real.exp (|w.im| * |z.re|) * (C * Real.exp (-|z.re|))
              = Real.exp (|w.re| * β) * C * (Real.exp (|w.im| * |z.re|) * Real.exp (-|z.re|)) := by
                ring
            _ = _ := by rw [this]
  have hshift := integral_horizontal_shift_of_decay hβ0 hr hdiff hbound
  simp only [hG', hG] at hshift
  have hL : (∫ x : ℝ, Complex.exp (-Complex.I * w * -((x : ℂ) + (β : ℂ) * Complex.I)) *
      chargeTailC F (-((x : ℂ) + (β : ℂ) * Complex.I))) =
      ∫ s : ℝ, Complex.exp (-Complex.I * w * ((s : ℂ) - (β : ℂ) * Complex.I)) *
        chargeTailC F ((s : ℂ) - (β : ℂ) * Complex.I) := by
    rw [← integral_neg_eq_self]
    congr 1; funext s; push_cast; ring_nf
  have hR : (∫ x : ℝ, Complex.exp (-Complex.I * w * -(x : ℂ)) * chargeTailC F (-(x : ℂ))) =
      ∫ x : ℝ, Complex.exp (-Complex.I * w * x) * modTail F 0 x := by
    rw [← integral_neg_eq_self]
    congr 1; funext x; push_cast; rw [neg_neg, chargeTailC_ofReal]
  unfold thetaPowerXiC
  rw [← hR, ← hshift, hL, ← integral_const_mul]
  congr 1; funext s
  have : Complex.exp (-Complex.I * w * ((s : ℂ) - (β : ℂ) * Complex.I)) =
      Complex.exp (-(w * β)) * Complex.exp (-Complex.I * w * s) := by
    rw [← Complex.exp_add]; congr 1; ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

theorem thetaPowerXiC_neg (a : ℝ) (w : ℂ) : thetaPowerXiC a (-w) = thetaPowerXiC a w := by
  unfold thetaPowerXiC
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  have he : modTail (thetaPowerForm a) 0 (-x) = modTail (thetaPowerForm a) 0 x := by
    have h := modTail_neg (F := thetaPowerForm a) 0 (thetaPowerForm_axis a) x
    simpa using h
  rw [he]
  push_cast
  ring_nf

theorem thetaPowerXiC_saddle (ha : 1 / 2 < a) {t : ℝ} (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) {v : ℝ}
    (hv : |v| ≤ 1 / 2) :
    thetaPowerXiC a ((chUm (chMa a) t : ℂ) + (v : ℂ) * Complex.I) =
      Complex.exp (-(((chUm (chMa a) t : ℂ) + (v : ℂ) * Complex.I) * chBeta t)) *
        ∫ s : ℝ, chLineAW a t v s := by
  have hw : |((chUm (chMa a) t : ℂ) + (v : ℂ) * Complex.I).im| < 1 := by simp; linarith
  rw [thetaPowerXiC_eq_shift (by linarith) (chBeta_nonneg ht2) (chBeta_lt ht (by linarith)) hw]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  dsimp only
  unfold chLineAW chLineA
  have e : Complex.exp (-Complex.I * ((chUm (chMa a) t : ℂ) + (v : ℂ) * Complex.I) * (s : ℂ)) =
      (Real.exp (v * s) : ℂ) * Complex.exp (-Complex.I * (chUm (chMa a) t : ℂ) * (s : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [e]; ring

/-- **No zeros of `Λ_a` in the critical strip beyond a height.** -/
theorem thetaPowerXiC_strip_ne_zero (ha : 1 / 2 < a) :
    ∃ U : ℝ, 0 < U ∧ ∀ w : ℂ, |w.im| ≤ 1 / 2 → U ≤ w.re → thetaPowerXiC a w ≠ 0 := by
  obtain ⟨t₁, ht₁, hpos⟩ := exists_re_chLineAWInt_pos ha
  set t₂ : ℝ := min t₁ (1 / 2) with ht₂
  have ht₂pos : 0 < t₂ := by positivity
  have hm := chMa_pos ha
  refine ⟨chUm (chMa a) t₂, by unfold chUm; positivity, fun w hw hu => ?_⟩
  set u : ℝ := w.re
  have hu0 : 0 < u := lt_of_lt_of_le (by unfold chUm; positivity) hu
  set t : ℝ := (chMa a * π / (8 * u)) ^ (1 / 4 : ℝ) with htdef
  have hbase : 0 < chMa a * π / (8 * u) := by positivity
  have ht0 : 0 < t := Real.rpow_pos_of_pos hbase _
  have ht4 : t ^ 4 = chMa a * π / (8 * u) := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hbase.le]; norm_num
  have hu_eq : chUm (chMa a) t = u := by
    unfold chUm; rw [ht4]; field_simp
  have htt : t ≤ t₂ := by
    have h4 : t ^ 4 ≤ t₂ ^ 4 := by
      rw [ht4]
      have : chUm (chMa a) t₂ = chMa a * π / (8 * t₂ ^ 4) := rfl
      rw [this] at hu
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hu
      nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) ht₂pos.le h4
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have : t ≤ 1 / 2 := le_trans htt (min_le_right _ _)
    nlinarith
  have hre := hpos t ht0 (le_trans htt (min_le_left _ _)) w.im hw
  have hw_eq : w = (chUm (chMa a) t : ℂ) + (w.im : ℂ) * Complex.I := by
    rw [hu_eq]; exact (Complex.re_add_im w).symm
  rw [hw_eq, thetaPowerXiC_saddle ha ht0 ht2 hw]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  intro h0; rw [h0] at hre; simp at hre

/-- **Strip rigidity.**  For `a > 1/2` the transform of `F_a = θ₃h^{a/4}` has only finitely many
zeros in the closed critical strip `|Im w| ≤ 1/2`. -/
theorem thetaPowerXiC_strip_zeros_finite (ha : 1 / 2 < a) :
    {w : ℂ | |w.im| ≤ 1 / 2 ∧ thetaPowerXiC a w = 0}.Finite := by
  have ha' : 0 < a := by linarith
  obtain ⟨U, hU, hne⟩ := thetaPowerXiC_strip_ne_zero ha
  have hf := differentiableOn_thetaPowerXiC ha'
  have hUmem : (U : ℂ) ∈ unitStripSet := by show |((U : ℂ)).im| < 1; simp
  have hiso : ∀ z ∈ unitStripSet, ¬ (∀ᶠ w in 𝓝 z, thetaPowerXiC a w = 0) := by
    intro z hz hev
    have han := hf.analyticOnNhd isOpen_unitStripSet
    have hconv : Convex ℝ unitStripSet := by
      intro x hx y hy s' t' hs ht hst
      show |(s' • x + t' • y).im| < 1
      have hx' : |x.im| < 1 := hx
      have hy' : |y.im| < 1 := hy
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      calc |s' * x.im + t' * y.im| ≤ s' * |x.im| + t' * |y.im| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
        _ < 1 := by
            rcases eq_or_lt_of_le hs with h0 | h0
            · subst h0; simp at hst; subst hst; simpa using hy'
            · nlinarith [mul_lt_mul_of_pos_left hx' h0, mul_le_mul_of_nonneg_left hy'.le ht]
    have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconv.isPreconnected hz hev
    exact hne U (by simp) (by simp) (hzero hUmem)
  set R : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Set.Icc (-U) U ×ˢ Set.Icc (-(1 / 2)) (1 / 2)) with hR
  have hRc : IsCompact R :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hRsub : R ⊆ unitStripSet := by
    rintro _ ⟨p, hp, rfl⟩
    show |((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im| < 1
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    rw [abs_lt]; constructor <;> linarith [hp.2.1, hp.2.2]
  have hfin := GaloisForLFunctions.HTGeometry.finite_zeros_of_isCompact isOpen_unitStripSet hf hiso
    hRc hRsub
  apply hfin.subset
  rintro w ⟨hw, h0⟩
  refine ⟨⟨(w.re, w.im), ⟨⟨?_, ?_⟩, ?_, ?_⟩, by simp [Complex.re_add_im]⟩, h0⟩
  · by_contra hc; push Not at hc
    have := hne (-w) (by simpa using hw) (by simp; linarith)
    rw [thetaPowerXiC_neg] at this
    exact this h0
  · by_contra hc; push Not at hc
    exact hne w hw hc.le h0
  · exact (abs_le.mp hw).1
  · exact (abs_le.mp hw).2

end Strip

end

end RHTower
