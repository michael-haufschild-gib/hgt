import GaloisForLFunctions.RHTower.WeilSinglePrimeDeletionUniform

/-!
# The even two-bump test and the insertion of a prime power

The even two-bump `g(x) = φ(x − u₀/2) + φ(x + u₀/2)` is the mirror of the odd two-bump: its Fourier
transform is `2 cos(z u₀/2) φ̂(z)`, bounded by `2 cosh(u₀ Im z / 2)|φ̂(z)|` exactly as for the odd one,
while its autocorrelation at the separation `±u₀` is `+∫ φ²` instead of `−∫ φ²`.  Consequently the
explicit-formula functional evaluated at `g ⋆ g̃` is tiny (the same zero-side bound as for the odd
test), and adding a prime-power term of positive weight at the scale `e^{u₀}` to the prime side
makes it negative: the prime side cannot be enlarged at a single scale any more than it can be
diminished.
-/

open Complex MeasureTheory Set
open scoped Convolution

namespace RHTower.WeilDeletion

/-- The even two-bump `φ(· − u₀/2) + φ(· + u₀/2)`. -/
noncomputable def evenBump (φ : ℝ → ℝ) (u₀ : ℝ) (y : ℝ) : ℝ := φ (y - u₀ / 2) + φ (y + u₀ / 2)

/-! ## Regularity and support -/

theorem evenBump_contDiff {φ : ℝ → ℝ} {n : ℕ} (hφ : ContDiff ℝ n φ) (u₀ : ℝ) :
    ContDiff ℝ n (evenBump φ u₀) := by
  unfold evenBump
  exact (hφ.comp (contDiff_id.sub contDiff_const)).add (hφ.comp (contDiff_id.add contDiff_const))

theorem evenBump_contDiff_top {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (u₀ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (evenBump φ u₀) := by
  unfold evenBump
  exact (hφ.comp (contDiff_id.sub contDiff_const)).add (hφ.comp (contDiff_id.add contDiff_const))

theorem support_evenBump_subset {φ : ℝ → ℝ} {s : ℝ} (hsupp : Function.support φ ⊆ Icc (-s) s)
    {u₀ : ℝ} (hu : 0 ≤ u₀) :
    Function.support (evenBump φ u₀) ⊆ Icc (-(u₀ / 2 + s)) (u₀ / 2 + s) := by
  intro y hy
  rw [Function.mem_support] at hy
  unfold evenBump at hy
  by_cases h1 : φ (y - u₀ / 2) = 0
  · have h2 : φ (y + u₀ / 2) ≠ 0 := by
      intro h2; apply hy; rw [h1, h2, add_zero]
    have := hsupp (Function.mem_support.mpr h2)
    rw [Set.mem_Icc] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · have := hsupp (Function.mem_support.mpr h1)
    rw [Set.mem_Icc] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

theorem evenBump_hasCompactSupport {φ : ℝ → ℝ} {s : ℝ} (hsupp : Function.support φ ⊆ Icc (-s) s)
    {u₀ : ℝ} (hu : 0 ≤ u₀) : HasCompactSupport (evenBump φ u₀) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_evenBump_subset hsupp hu)

theorem evenBump_integrable {φ : ℝ → ℝ} {s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 0 ≤ u₀) :
    Integrable (evenBump φ u₀) :=
  (evenBump_contDiff hφ u₀).continuous.integrable_of_hasCompactSupport
    (evenBump_hasCompactSupport hsupp hu)

/-! ## Fourier transform -/

theorem paperFT_evenBump {φ : ℝ → ℝ} {s : ℝ} (hφ : Integrable φ)
    (hsupp : Function.support φ ⊆ Icc (-s) s) (u₀ : ℝ) (z : ℂ) :
    Zeta23.paperFT (fun x => (evenBump φ u₀ x : ℂ)) z =
      Zeta23.paperFT (fun x => (φ x : ℂ)) z *
        (Complex.exp (I * z * (u₀ / 2)) + Complex.exp (-(I * z * (u₀ / 2)))) := by
  have h1 : Zeta23.paperFT (fun y => (φ (y - u₀ / 2) : ℂ)) z =
      Complex.exp (I * z * (u₀ / 2)) * Zeta23.paperFT (fun x => (φ x : ℂ)) z := by
    have := paperFT_translate φ (u₀ / 2) z
    push_cast at this
    exact this
  have h2 : Zeta23.paperFT (fun y => (φ (y + u₀ / 2) : ℂ)) z =
      Complex.exp (-(I * z * (u₀ / 2))) * Zeta23.paperFT (fun x => (φ x : ℂ)) z := by
    have := paperFT_translate φ (-(u₀ / 2)) z
    simp only [sub_neg_eq_add] at this
    rw [this]
    congr 2
    push_cast
    ring
  have hadd : Zeta23.paperFT (fun x => (evenBump φ u₀ x : ℂ)) z =
      Zeta23.paperFT (fun y => (φ (y - u₀ / 2) : ℂ)) z +
        Zeta23.paperFT (fun y => (φ (y + u₀ / 2) : ℂ)) z := by
    unfold Zeta23.paperFT evenBump
    rw [← integral_add]
    · congr 1
      funext x
      push_cast
      ring
    · exact integrable_ofReal_mul_exp (hφ.comp_sub_right (u₀ / 2))
        (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
          (support_translate_subset hsupp (u₀ / 2))) z
    · have hsupp' : Function.support (fun y => φ (y + u₀ / 2)) ⊆
          Icc (-s + -(u₀ / 2)) (s + -(u₀ / 2)) := by
        have := support_translate_subset hsupp (-(u₀ / 2))
        simpa [sub_neg_eq_add] using this
      exact integrable_ofReal_mul_exp (hφ.comp_add_right (u₀ / 2))
        (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp') z
  rw [hadd, h1, h2]
  ring

theorem norm_paperFT_evenBump_le {φ : ℝ → ℝ} {s : ℝ} (hφ : Integrable φ)
    (hsupp : Function.support φ ⊆ Icc (-s) s) (u₀ : ℝ) (z : ℂ) :
    ‖Zeta23.paperFT (fun x => (evenBump φ u₀ x : ℂ)) z‖ ≤
      ‖Zeta23.paperFT (fun x => (φ x : ℂ)) z‖ * (2 * Real.cosh (u₀ / 2 * z.im)) := by
  rw [paperFT_evenBump hφ hsupp u₀ z, norm_mul]
  gcongr
  calc ‖Complex.exp (I * z * (u₀ / 2)) + Complex.exp (-(I * z * (u₀ / 2)))‖
      ≤ ‖Complex.exp (I * z * (u₀ / 2))‖ + ‖Complex.exp (-(I * z * (u₀ / 2)))‖ := norm_add_le _ _
    _ = Real.exp (-(u₀ / 2 * z.im)) + Real.exp (u₀ / 2 * z.im) := by
        rw [Complex.norm_exp, Complex.norm_exp]
        congr 2
        · simp [Complex.mul_re, Complex.mul_im]; ring
        · simp [Complex.mul_re, Complex.mul_im]; ring
    _ = 2 * Real.cosh (u₀ / 2 * z.im) := by rw [Real.cosh_eq]; ring

/-! ## The autocorrelation at the separation -/

theorem evenBump_mul_shift {φ : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 2 * s < u₀) (t : ℝ) :
    evenBump φ u₀ t * evenBump φ u₀ (t - u₀) = (φ (t - u₀ / 2)) ^ (2 : ℕ) := by
  unfold evenBump
  have e1 : t - u₀ + u₀ / 2 = t - u₀ / 2 := by ring
  rw [e1]
  have h1 : φ (t - u₀ / 2) * φ (t - u₀ - u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t - u₀ / 2 - (t - u₀ - u₀ / 2) = u₀ by ring]; rw [abs_of_pos (by linarith)]; linarith)
  have h2 : φ (t + u₀ / 2) * φ (t - u₀ - u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t + u₀ / 2 - (t - u₀ - u₀ / 2) = 2 * u₀ by ring]; rw [abs_of_pos (by linarith)]; linarith)
  have h3 : φ (t + u₀ / 2) * φ (t - u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t + u₀ / 2 - (t - u₀ / 2) = u₀ by ring]; rw [abs_of_pos (by linarith)]; linarith)
  linear_combination h1 + h2 + h3

theorem evenBump_mul_shift' {φ : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 2 * s < u₀) (t : ℝ) :
    evenBump φ u₀ t * evenBump φ u₀ (t + u₀) = (φ (t + u₀ / 2)) ^ (2 : ℕ) := by
  unfold evenBump
  have e1 : t + u₀ - u₀ / 2 = t + u₀ / 2 := by ring
  rw [e1]
  have h1 : φ (t - u₀ / 2) * φ (t + u₀ + u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t - u₀ / 2 - (t + u₀ + u₀ / 2) = -(2 * u₀) by ring]; rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have h2 : φ (t + u₀ / 2) * φ (t + u₀ + u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t + u₀ / 2 - (t + u₀ + u₀ / 2) = -u₀ by ring]; rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have h3 : φ (t - u₀ / 2) * φ (t + u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t - u₀ / 2 - (t + u₀ / 2) = -u₀ by ring]; rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  linear_combination h1 + h2 + h3

/-- `k(u₀) = +∫ φ²` for the even two-bump. -/
theorem autocorr_evenBump_apply {φ : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 2 * s < u₀) :
    autocorr (evenBump φ u₀) u₀ = ∫ x, φ x ^ (2 : ℕ) := by
  unfold autocorr
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, reflectFn, neg_sub]
  have h : (fun t : ℝ => evenBump φ u₀ t * evenBump φ u₀ (t - u₀)) =
      fun t : ℝ => (fun x : ℝ => φ x ^ (2 : ℕ)) (t - u₀ / 2) := by
    funext t
    exact evenBump_mul_shift hs hsupp hu t
  rw [h, integral_sub_right_eq_self (fun x : ℝ => φ x ^ (2 : ℕ)) (u₀ / 2)]

/-- `k(−u₀) = +∫ φ²` for the even two-bump. -/
theorem autocorr_evenBump_apply_neg {φ : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 2 * s < u₀) :
    autocorr (evenBump φ u₀) (-u₀) = ∫ x, φ x ^ (2 : ℕ) := by
  unfold autocorr
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, reflectFn, neg_sub]
  have h : (fun t : ℝ => evenBump φ u₀ t * evenBump φ u₀ (t - -u₀)) =
      fun t : ℝ => (fun x : ℝ => φ x ^ (2 : ℕ)) (t + u₀ / 2) := by
    funext t
    rw [sub_neg_eq_add]
    exact evenBump_mul_shift' hs hsupp hu t
  rw [h, integral_add_right_eq_self (fun x : ℝ => φ x ^ (2 : ℕ)) (u₀ / 2)]

/-! ## The zero-side bound for the even two-bump autocorrelation -/

theorem norm_paperFT_autocorr_evenBump_le (n : ℕ) {u₀ p : ℝ} (hu0 : 0 ≤ u₀)
    (hexp_half : Real.exp (u₀ / 2) = Real.sqrt p) {γ : ℂ} (hγ0 : γ ≠ 0)
    (hγim : |γ.im| ≤ 1 / 2) (hγsq : (41 / 2 : ℝ) < ‖γ‖ ^ (2 : ℕ)) :
    ‖Zeta23.paperFT (fun x => (autocorr (evenBump (phiN n) u₀) x : ℂ)) γ‖ ≤
      (4 * Real.sqrt p * (3 / 2) * ((1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n)) *
        (1 / ‖γ‖ ^ (2 : ℕ)) := by
  have hsupp := support_phiN_subset n
  have hγpos : 0 < ‖γ‖ := norm_pos_iff.mpr hγ0
  set f := evenBump (phiN n) u₀ with hf
  have hkFT : Zeta23.paperFT (fun x => (autocorr f x : ℂ)) γ =
      Zeta23.paperFT (fun x => (f x : ℂ)) γ * Zeta23.paperFT (fun x => (f x : ℂ)) (-γ) :=
    paperFT_autocorr (evenBump_integrable (phiN_contDiff n) hsupp hu0)
      (support_evenBump_subset hsupp hu0) γ
  rw [hkFT, norm_mul]
  have hΦ : ∀ z : ℂ, z ≠ 0 → |z.im| ≤ 1 / 2 →
      ‖Zeta23.paperFT (fun x => (f x : ℂ)) z‖ ≤
        (Real.exp (1 / 5) * ((1081 / 780) / ‖z‖) ^ (n + 1)) * (2 * Real.cosh (u₀ / 2 * z.im)) := by
    intro z hz hzim
    refine (norm_paperFT_evenBump_le (integrable_phiN n) hsupp u₀ z).trans ?_
    gcongr
    exact norm_paperFT_phiN_le n hz hzim
  have hγ' : -γ ≠ 0 := neg_ne_zero.mpr hγ0
  have hγim' : |(-γ).im| ≤ 1 / 2 := by rw [Complex.neg_im, abs_neg]; exact hγim
  have hcosh : ∀ t : ℝ, |t| ≤ 1 / 2 → 2 * Real.cosh (u₀ / 2 * t) ≤ 2 * Real.exp (u₀ / 4) := by
    intro t ht
    have := cosh_le_exp_abs (u₀ / 2 * t)
    have h2 : Real.exp |u₀ / 2 * t| ≤ Real.exp (u₀ / 4) := by
      apply Real.exp_le_exp.mpr
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u₀ / 2)]
      nlinarith [ht, abs_nonneg t]
    linarith
  have hA := hΦ γ hγ0 hγim
  have hB := hΦ (-γ) hγ' hγim'
  rw [norm_neg] at hB
  have hc1 := hcosh γ.im hγim
  have hc2 := hcosh (-γ).im hγim'
  set E := Real.exp (1 / 5) * ((1081 / 780) / ‖γ‖) ^ (n + 1) with hE
  have hEnn : 0 ≤ E := by positivity
  have hstep1 : ‖Zeta23.paperFT (fun x => (f x : ℂ)) γ‖ *
      ‖Zeta23.paperFT (fun x => (f x : ℂ)) (-γ)‖ ≤
      (E * (2 * Real.exp (u₀ / 4))) * (E * (2 * Real.exp (u₀ / 4))) := by
    calc ‖Zeta23.paperFT (fun x => (f x : ℂ)) γ‖ * ‖Zeta23.paperFT (fun x => (f x : ℂ)) (-γ)‖
        ≤ (E * (2 * Real.cosh (u₀ / 2 * γ.im))) * (E * (2 * Real.cosh (u₀ / 2 * (-γ).im))) :=
          mul_le_mul hA hB (norm_nonneg _) (by positivity)
      _ ≤ (E * (2 * Real.exp (u₀ / 4))) * (E * (2 * Real.exp (u₀ / 4))) := by
          gcongr
  have hexp2 : Real.exp (1 / 5) * Real.exp (1 / 5) = Real.exp (2 / 5) := by
    rw [← Real.exp_add]; norm_num
  have hexp4 : Real.exp (u₀ / 4) * Real.exp (u₀ / 4) = Real.sqrt p := by
    rw [← Real.exp_add, ← hexp_half]; congr 1; ring
  have hpow : ((1081 / 780 : ℝ) / ‖γ‖) ^ (n + 1) * ((1081 / 780 : ℝ) / ‖γ‖) ^ (n + 1) =
      (1081 / 780 : ℝ) ^ (2 * (n + 1)) * (1 / ‖γ‖ ^ (2 * (n + 1))) := by
    rw [← pow_add, div_pow, mul_one_div]
    congr 2 <;> ring
  have hnorm : 1 / ‖γ‖ ^ (2 * (n + 1)) ≤ (2 / 41) ^ n * (1 / ‖γ‖ ^ (2 : ℕ)) := by
    have h : ‖γ‖ ^ (2 * (n + 1)) = ‖γ‖ ^ (2 : ℕ) * (‖γ‖ ^ (2 : ℕ)) ^ n := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    rw [h, one_div, mul_inv, ← one_div, ← one_div, mul_comm]
    gcongr
    rw [div_le_iff₀ (by positivity)]
    rw [show (2 / 41 : ℝ) ^ n * (‖γ‖ ^ (2 : ℕ)) ^ n = ((2 / 41) * ‖γ‖ ^ (2 : ℕ)) ^ n by rw [mul_pow]]
    have : (1 : ℝ) ≤ (2 / 41) * ‖γ‖ ^ (2 : ℕ) := by nlinarith
    exact one_le_pow₀ this
  have hstep2 : (E * (2 * Real.exp (u₀ / 4))) * (E * (2 * Real.exp (u₀ / 4))) =
      4 * Real.sqrt p * Real.exp (2 / 5) *
        ((1081 / 780) ^ (2 * (n + 1)) * (1 / ‖γ‖ ^ (2 * (n + 1)))) := by
    rw [hE, ← hexp2, ← hexp4, ← hpow]
    ring
  have hstep3 : 4 * Real.sqrt p * Real.exp (2 / 5) *
      ((1081 / 780) ^ (2 * (n + 1)) * (1 / ‖γ‖ ^ (2 * (n + 1)))) ≤
      4 * Real.sqrt p * (3 / 2) * ((1081 / 780) ^ (2 * (n + 1)) * ((2 / 41) ^ n * (1 / ‖γ‖ ^ (2 : ℕ)))) := by
    gcongr
    exact exp_two_fifths_le
  calc ‖Zeta23.paperFT (fun x => (f x : ℂ)) γ‖ * ‖Zeta23.paperFT (fun x => (f x : ℂ)) (-γ)‖
      ≤ _ := hstep1
    _ = _ := hstep2
    _ ≤ _ := hstep3
    _ = (4 * Real.sqrt p * (3 / 2) * ((1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n)) *
        (1 / ‖γ‖ ^ (2 : ℕ)) := by ring

end RHTower.WeilDeletion
