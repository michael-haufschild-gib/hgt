import GaloisForLFunctions.RHTower.HalfWeightUnfolding

/-!
# Regularity and moderate growth of the continued weight-½ Eisenstein series

* `fourier_hab_scale`, `Gk_scale`, `PhiK_scale`: the kernel transforms scale exactly,
  `Φ_k^{(y)}(w)(ξ) = y^{1-w} Φ_k^{(1)}(w)(yξ)`.
* `continuousOn_Gk`, `continuousOn_PhiK_one`: `ξ ↦ Φ_k^{(1)}(w)(ξ)` is continuous on `ξ ≠ 0`
  (Fourier transforms of integrable functions are continuous; the recursion divides by `2πiξ`).
* `exists_bound_PhiK_y`: `‖Φ_K^{(y)}(w)(ξ)‖ ≤ C y^{1-Re w-K} |ξ|^{-K}` uniformly on a closed ball.
* `exists_aTerm_bound`: the terms of `E*` satisfy
  `‖a_n(z,w)‖ ≤ ([n = 0] C₀ + C|n|^{-2}) (y^A + y^{-A})` uniformly on a closed ball in `Re w > 1/4`.
* **`Estar_growth`**: `‖E*(z,w)‖ ≤ C (y^A + y^{-A})` — moderate growth, uniformly in `w` near any point
  of `Re w > 1/4` and in `z ∈ ℍ`.
* **`continuous_Estar`**: `z ↦ E*(z,w)` is continuous (locally uniform convergence).
-/

open Real Complex Filter Topology MeasureTheory Metric
open scoped FourierTransform

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.RHTower.SelbergPoincareKernel

noncomputable section

/-! ### Scaling of the continued kernel transforms -/

theorem fourier_hab_scale {y : ℝ} (hy : 0 < y) (a b : ℂ) (ξ : ℝ) :
    𝓕 (hab y a b) ξ = (y : ℂ) ^ (1 - a - b) * 𝓕 (hab 1 a b) (y * ξ) := by
  simp only [Real.fourier_real_eq]
  have h := Measure.integral_comp_mul_left (fun x : ℝ => ((𝐞 (-(x * ξ)) : Circle) : ℂ) * hab y a b x) y
  have e : ∀ t : ℝ, ((𝐞 (-(y * t * ξ)) : Circle) : ℂ) * hab y a b (y * t) =
      (y : ℂ) ^ (-a - b) * (((𝐞 (-(t * (y * ξ))) : Circle) : ℂ) * hab 1 a b t) := by
    intro t
    rw [hab_scale hy, show y * t * ξ = t * (y * ξ) by ring]
    ring
  simp_rw [e, integral_const_mul] at h
  rw [abs_inv, abs_of_pos hy, Complex.real_smul] at h
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have e2 : (y : ℂ) ^ (1 - a - b) = (y : ℂ) * (y : ℂ) ^ (-a - b) := by
    rw [show (1 : ℂ) - a - b = 1 + (-a - b) by ring, Complex.cpow_add _ _ hy0, Complex.cpow_one]
  simp only [Circle.smul_def, smul_eq_mul]
  rw [e2, mul_assoc, h, Complex.ofReal_inv]
  field_simp
  congr 1; funext t; rw [mul_comm ξ t]

/-- `G_k^{(y)}(a,b)(ξ) = y^{1-a-b} G_k^{(1)}(a,b)(yξ)`. -/
theorem Gk_scale {y : ℝ} (hy : 0 < y) (k : ℕ) :
    ∀ (a b : ℂ) (ξ : ℝ), Gk y k a b ξ = (y : ℂ) ^ (1 - a - b) * Gk 1 k a b (y * ξ) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  induction k with
  | zero => intro a b ξ; exact fourier_hab_scale hy a b ξ
  | succ k ih =>
    intro a b ξ
    rw [Gk_succ, Gk_succ, ih, ih]
    have e1 : (y : ℂ) ^ (1 - (a + 1) - b) = (y : ℂ) ^ (1 - a - b) * (y : ℂ)⁻¹ := by
      rw [show (1 : ℂ) - (a + 1) - b = (1 - a - b) + (-1) by ring, Complex.cpow_add _ _ hy0,
        Complex.cpow_neg_one]
    have e2 : (y : ℂ) ^ (1 - a - (b + 1)) = (y : ℂ) ^ (1 - a - b) * (y : ℂ)⁻¹ := by
      rw [show (1 : ℂ) - a - (b + 1) = (1 - a - b) + (-1) by ring, Complex.cpow_add _ _ hy0,
        Complex.cpow_neg_one]
    rw [e1, e2]
    push_cast
    by_cases hξ : ξ = 0
    · subst hξ; simp
    have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp

/-- `Φ_k^{(y)}(w)(ξ) = y^{1-w} Φ_k^{(1)}(w)(yξ)`. -/
theorem PhiK_scale {y : ℝ} (hy : 0 < y) (k : ℕ) (w : ℂ) (ξ : ℝ) :
    PhiK y k w ξ = (y : ℂ) ^ (1 - w) * PhiK 1 k w (y * ξ) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  unfold PhiK
  rw [Gk_scale hy, Complex.ofReal_one, Complex.one_cpow, one_mul, ← mul_assoc,
    ← Complex.cpow_add _ _ hy0]
  congr 2; ring

/-! ### Continuity in the spectral-free variable -/

theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

/-- `ξ ↦ G_k^{(1)}(a,b)(ξ)` is continuous on `ξ ≠ 0` when `Re(a+b) + k > 1`. -/
theorem continuousOn_Gk (k : ℕ) :
    ∀ (a b : ℂ), 1 < (a + b).re + k → ContinuousOn (Gk 1 k a b) {ξ | ξ ≠ 0} := by
  induction k with
  | zero =>
    intro a b h
    simp only [Nat.cast_zero, add_zero] at h
    exact (continuous_fourier_of_integrable (integrable_hab one_pos h)).continuousOn
  | succ k ih =>
    intro a b h
    push_cast at h
    have h1 := ih (a + 1) b (by simp; simp at h; linarith)
    have h2 := ih a (b + 1) (by simp; simp at h; linarith)
    have hden : ContinuousOn (fun ξ : ℝ => (2 * Real.pi * I * ξ : ℂ)) {ξ | ξ ≠ 0} := by fun_prop
    refine ((h1.const_smul a).add (h2.const_smul b)).neg.div hden ?_ |>.congr fun ξ _ => ?_
    · intro ξ hξ
      have : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp_all
    · simp only [Gk_succ, Pi.div_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem continuousOn_PhiK_one (k : ℕ) {w : ℂ} (hw : 1 < 2 * w.re + k) :
    ContinuousOn (PhiK 1 k w) {ξ | ξ ≠ 0} := by
  unfold PhiK
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
  exact continuousOn_Gk k _ _ (by simp; linarith)


/-! ### Bounds with explicit dependence on `y` -/

/-- `‖Φ_K^{(y)}(w)(ξ)‖ ≤ C y^{1-Re w-K} |ξ|^{-K}` uniformly on a closed ball in `Re w > 0`. -/
theorem exists_bound_PhiK_y {K : ℕ} (hK : 1 ≤ K) {w₀ : ℂ} {r : ℝ} (hr : 0 < r) (hτ : 0 < w₀.re - r) :
    ∃ C, 0 ≤ C ∧ ∀ w ∈ closedBall w₀ r, ∀ y : ℝ, 0 < y → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖PhiK y K w ξ‖ ≤ C * y ^ (1 - w.re - K) * |ξ| ^ (-(K : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_PhiK one_pos hK hr hτ
  refine ⟨C, hC0, fun w hw y hy ξ hξ => ?_⟩
  have hyξ : y * ξ ≠ 0 := mul_ne_zero hy.ne' hξ
  rw [PhiK_scale hy, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have h := hC w hw (y * ξ) hyξ
  rw [abs_mul, abs_of_pos hy, Real.mul_rpow hy.le (abs_nonneg _)] at h
  have he : (1 - w).re + -(K : ℝ) = 1 - w.re - K := by
    simp only [Complex.sub_re, Complex.one_re]; ring
  have e : y ^ (1 - w.re - K) = y ^ (1 - w).re * y ^ (-(K : ℝ)) := by
    rw [← Real.rpow_add hy, he]
  rw [e]
  calc y ^ (1 - w).re * ‖PhiK 1 K w (y * ξ)‖ ≤ y ^ (1 - w).re * (C * (y ^ (-(K : ℝ)) * |ξ| ^ (-(K : ℝ)))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem rpow_le_add_neg {y t A : ℝ} (hy : 0 < y) (ht : |t| ≤ A) : y ^ t ≤ y ^ A + y ^ (-A) := by
  have h1 := neg_abs_le t
  have h2 := le_abs_self t
  rcases le_or_gt 1 y with hy1 | hy1
  · have := Real.rpow_le_rpow_of_exponent_le hy1 (show t ≤ A by linarith)
    have : 0 ≤ y ^ (-A) := by positivity
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hy hy1.le (show -A ≤ t by linarith)
    have : 0 ≤ y ^ A := by positivity
    linarith

section Regularity

variable (M : ℕ) [NeZero M]

/-- **Uniform bound for the terms of `E*`** on a closed ball in `Re w > 1/4`:
`‖aTerm_n(z,w)‖ ≤ ([n = 0] C₀ + C |n|^{-2}) (y^A + y^{-A})`. -/
theorem exists_aTerm_bound {w₀ : ℂ} (h1 : 1 / 4 < w₀.re) :
    ∃ r > 0, ∃ C0 C A : ℝ, 0 ≤ C0 ∧ 0 ≤ C ∧ w₀.re + r ≤ A ∧ ∀ w ∈ closedBall w₀ r, ∀ z : UpperHalfPlane, ∀ n : ℤ,
      ‖aTerm M z w n‖ ≤ ((if n = 0 then C0 else 0) + C * |(n : ℝ)| ^ (-2 : ℝ)) *
        (z.im ^ A + z.im ^ (-A)) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set r := (w₀.re - 1 / 4) / 2 with hr
  have hr0 : 0 < r := by simp only [hr]; linarith
  have hl : 1 / 4 < w₀.re - r := by simp only [hr]; linarith
  set e := expE (w₀.re - r)
  set K : ℕ := ⌈e⌉₊ + 2 with hK
  have hK1 : 1 ≤ K := by omega
  have heK : e - K ≤ -2 := by
    have := Nat.le_ceil e
    have : ((⌈e⌉₊ + 2 : ℕ) : ℝ) = (⌈e⌉₊ : ℝ) + 2 := by push_cast; ring
    rw [hK, this]; linarith
  obtain ⟨CP, hCP0, hCP⟩ := exists_bound_PhiK_y hK1 hr0 (by linarith)
  obtain ⟨CD, hCD0, hCD⟩ := exists_bound_Dstar hM hl
  have hcont0 : ContinuousOn (phiStar M) (closedBall w₀ r) := fun w hw =>
    (differentiableAt_phiStar M (by linarith [(re_ge_of_mem_closedBall hw).1])).continuousAt.continuousWithinAt
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall w₀ r).exists_bound_of_continuousOn hcont0
  set A : ℝ := w₀.re + r + K + 1
  refine ⟨r, hr0, max C0 0, CP * CD, A, le_max_right _ _, by positivity,
    by simp only [A]; have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith, fun w hw z n => ?_⟩
  obtain ⟨hre1, hre2⟩ := re_ge_of_mem_closedBall hw
  set y := z.im
  have hy : 0 < y := z.im_pos
  have hyA : ∀ t : ℝ, |t| ≤ A → y ^ t ≤ y ^ A + y ^ (-A) := fun t ht => rpow_le_add_neg hy ht
  have hYpos : 0 ≤ y ^ A + y ^ (-A) := by positivity
  by_cases hn : n = 0
  · subst hn
    simp only [aTerm, if_true, Int.cast_zero, abs_zero]
    rw [Real.zero_rpow (by norm_num), mul_zero, add_zero, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hp := (hC0 w hw).trans (le_max_left C0 0)
    have hyt : y ^ (1 - w).re ≤ y ^ A + y ^ (-A) := hyA _ (by
      simp only [Complex.sub_re, Complex.one_re]
      rw [abs_le]; constructor <;> linarith)
    calc y ^ (1 - w).re * ‖phiStar M w‖ ≤ (y ^ A + y ^ (-A)) * max C0 0 :=
          mul_le_mul hyt hp (norm_nonneg _) hYpos
      _ = _ := by ring
  · simp only [aTerm, if_neg hn, zero_add]
    have hξ : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hn
    have hPhi : PhiK z.im 1 w n = PhiK z.im K w n :=
      PhiK_eq_PhiK hy hξ hK1 (by push_cast; linarith)
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    rw [hPhi, norm_mul, norm_mul, continuous_cexp_mode, mul_one, DstarZ, dif_neg hn]
    have hP := hCP w hw y hy n hξ
    have hD := hCD w hw n hn
    have hyt : y ^ (1 - w.re - K) ≤ y ^ A + y ^ (-A) := hyA _ (by
      rw [abs_le]; constructor <;> linarith)
    calc ‖PhiK y K w n‖ * ‖Dstar hn hM w‖
        ≤ (CP * y ^ (1 - w.re - K) * |(n : ℝ)| ^ (-(K : ℝ))) * (CD * |(n : ℝ)| ^ e) :=
          mul_le_mul hP hD (norm_nonneg _) (by positivity)
      _ = CP * CD * y ^ (1 - w.re - K) * |(n : ℝ)| ^ (e - K) := by
          rw [Real.rpow_sub (show (0 : ℝ) < |(n : ℝ)| by linarith) e K,
            Real.rpow_neg (show (0 : ℝ) ≤ |(n : ℝ)| by linarith)]; ring
      _ ≤ CP * CD * (y ^ A + y ^ (-A)) * |(n : ℝ)| ^ (-2 : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hyt (by positivity))
            (Real.rpow_le_rpow_of_exponent_le hn1 heK) (by positivity) (by positivity)
      _ = _ := by ring

theorem summable_bound (C0 C : ℝ) : Summable fun n : ℤ => (if n = 0 then C0 else 0) + C * |(n : ℝ)| ^ (-2 : ℝ) :=
  (hasSum_ite_eq (0 : ℤ) C0).summable.add ((Real.summable_abs_int_rpow (b := 2) (by norm_num)).mul_left C)

/-- **Moderate growth of `E*`**, uniformly on a closed ball in `Re w > 1/4`:
`‖E*(z,w)‖ ≤ C (y^A + y^{-A})`. -/
theorem Estar_growth {w₀ : ℂ} (h1 : 1 / 4 < w₀.re) :
    ∃ r > 0, ∃ C A : ℝ, 0 ≤ C ∧ ∀ w ∈ closedBall w₀ r, ∀ z : UpperHalfPlane,
      ‖Estar M z w‖ ≤ C * (z.im ^ A + z.im ^ (-A)) := by
  obtain ⟨r, hr0, C0, C, A, hC00, hC0, hAr, hb⟩ := exists_aTerm_bound M h1
  obtain ⟨CR, hCR⟩ := (isCompact_closedBall w₀ r).exists_bound_of_continuousOn
    (differentiable_regF.continuous.continuousOn (s := closedBall w₀ r))
  set u : ℤ → ℝ := fun n => (if n = 0 then C0 else 0) + C * |(n : ℝ)| ^ (-2 : ℝ)
  have hu := summable_bound C0 C
  set S : ℝ := ∑' n : ℤ, u n
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [u]; split_ifs <;> positivity
  have hS0 : 0 ≤ S := tsum_nonneg hu0
  refine ⟨r, hr0, 2 * (max CR 0 + S), A, by positivity, fun w hw z => ?_⟩
  obtain ⟨hre1, hre2⟩ := re_ge_of_mem_closedBall hw
  set y := z.im
  have hy : 0 < y := z.im_pos
  set Y := y ^ A + y ^ (-A)
  have hY : 0 ≤ Y := by positivity
  have hterm : ∀ n, ‖aTerm M z w n‖ ≤ u n * Y := fun n => hb w hw z n
  have hsn : Summable fun n : ℤ => ‖aTerm M z w n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hu.mul_right Y)
  have htsum : ‖∑' n : ℤ, aTerm M z w n‖ ≤ S * Y :=
    (norm_tsum_le_tsum_norm hsn).trans ((hsn.tsum_le_tsum hterm (hu.mul_right Y)).trans
      (le_of_eq (tsum_mul_right)))
  have hlead : ‖regF w * ((y : ℝ) : ℂ) ^ w‖ ≤ max CR 0 * Y := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hyt : y ^ w.re ≤ Y := rpow_le_add_neg hy (by
      rw [abs_le]; constructor <;> linarith)
    exact mul_le_mul ((hCR w hw).trans (le_max_left _ _)) hyt (by positivity) (le_max_right _ _)
  unfold Estar
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have := (norm_add_le _ _).trans (add_le_add hlead htsum)
  calc 2 * ‖regF w * ((z.im : ℝ) : ℂ) ^ w + ∑' n : ℤ, aTerm M z w n‖
      ≤ 2 * (max CR 0 * Y + S * Y) := by gcongr
    _ = _ := by ring

theorem continuous_im_cpow (s : ℂ) : Continuous fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ) ^ s := by
  refine Continuous.cpow (by fun_prop) continuous_const fun z => ?_
  exact Complex.ofReal_mem_slitPlane.2 z.im_pos

theorem continuous_aTerm {w : ℂ} (h1 : 1 / 4 < w.re) (n : ℤ) :
    Continuous fun z : UpperHalfPlane => aTerm M z w n := by
  by_cases hn : n = 0
  · subst hn
    simp only [aTerm, if_true]
    exact (continuous_im_cpow _).mul continuous_const
  · simp only [aTerm, if_neg hn]
    have hξ : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hn
    have e : (fun z : UpperHalfPlane => PhiK z.im 1 w n) =
        fun z => ((z.im : ℝ) : ℂ) ^ (1 - w) * PhiK 1 1 w (z.im * n) := by
      funext z; exact PhiK_scale z.im_pos 1 w n
    have hP : Continuous fun z : UpperHalfPlane => PhiK z.im 1 w n := by
      rw [e]
      refine (continuous_im_cpow _).mul ?_
      refine (continuousOn_PhiK_one 1 (by push_cast; linarith)).comp_continuous (by fun_prop) ?_
      intro z; exact mul_ne_zero z.im_pos.ne' hξ
    have hE : Continuous fun z : UpperHalfPlane => cexp (2 * π * I * n * z.re) := by fun_prop
    exact (hP.mul hE).mul continuous_const

/-- **Continuity of `E*` in `z`** for `Re w > 1/4`. -/
theorem continuous_Estar {w : ℂ} (h1 : 1 / 4 < w.re) :
    Continuous fun z : UpperHalfPlane => Estar M z w := by
  obtain ⟨r, hr0, C0, C, A, hC00, hC0, hAr, hb⟩ := exists_aTerm_bound M h1
  have hw : w ∈ closedBall w r := mem_closedBall_self hr0.le
  have hA : 0 ≤ A := by have := hr0.le; linarith
  have htsum : Continuous fun z : UpperHalfPlane => ∑' n : ℤ, aTerm M z w n := by
    refine continuous_iff_continuousAt.2 fun z₀ => ?_
    set y₀ := z₀.im
    have hy₀ : 0 < y₀ := z₀.im_pos
    set U : Set UpperHalfPlane := {z | y₀ / 2 < z.im ∧ z.im < 2 * y₀}
    have hUo : IsOpen U :=
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const)
    have hz₀ : z₀ ∈ U := ⟨by linarith, by linarith⟩
    set Ymax : ℝ := (2 * y₀) ^ A + (y₀ / 2) ^ (-A)
    have hbd : ∀ n : ℤ, ∀ z ∈ U, ‖aTerm M z w n‖ ≤
        ((if n = 0 then C0 else 0) + C * |(n : ℝ)| ^ (-2 : ℝ)) * Ymax := by
      intro n z hz
      refine (hb w hw z n).trans (mul_le_mul_of_nonneg_left ?_ (by split_ifs <;> positivity))
      have hy : 0 < z.im := z.im_pos
      have e1 : z.im ^ A ≤ (2 * y₀) ^ A := Real.rpow_le_rpow hy.le hz.2.le hA
      have e2 : z.im ^ (-A) ≤ (y₀ / 2) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hz.1.le (by linarith)
      linarith
    have hc := continuousOn_tsum (fun n => (continuous_aTerm M h1 n).continuousOn)
      ((summable_bound C0 C).mul_right Ymax) hbd
    exact hc.continuousAt (hUo.mem_nhds hz₀)
  have hlead : Continuous fun z : UpperHalfPlane => regF w * ((z.im : ℝ) : ℂ) ^ w :=
    continuous_const.mul (continuous_im_cpow _)
  unfold Estar
  exact continuous_const.mul (hlead.add htsum)

end Regularity
