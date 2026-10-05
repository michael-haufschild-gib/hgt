import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Poisson summation along arithmetic progressions

For a `C^k` function `G` (`k ≥ 2`) whose derivatives up to order `k` are bounded by
`M (1 + x²)^{−1}`, Poisson summation and integration by parts give, for every step `γ > 0` and
offset `β`,

`|Σ_{n∈ℤ} G(β + γn) − γ^{−1} ∫ G| ≤ M γ^{k−1} Z`,  `Z = Σ_{n∈ℤ} |n|^{−2}`.

This is the quantitative lattice-sum input for the smooth-gauge progression bounds.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped FourierTransform

namespace RHTower

noncomputable section

/-- `‖𝓕 f ξ‖ ≤ ∫ ‖f‖`. -/
theorem norm_fourier_le_integral_norm_real (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  ext x
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Integration-by-parts decay: `(2π|ξ|)^k ‖𝓕 f ξ‖ ≤ ∫ ‖f^{(k)}‖`. -/
theorem pow_mul_norm_fourier_le_of_iteratedDeriv {f : ℝ → ℂ} {k : ℕ} (hf : ContDiff ℝ k f)
    (hint : ∀ j ≤ k, Integrable (iteratedDeriv j f)) (ξ : ℝ) :
    (2 * Real.pi * |ξ|) ^ k * ‖𝓕 f ξ‖ ≤ ∫ x, ‖iteratedDeriv k f x‖ := by
  have h := congrFun (Real.fourier_iteratedDeriv (N := (k : ℕ∞)) (n := k) (by exact_mod_cast hf)
    (fun n hn => hint n (by exact_mod_cast hn)) le_rfl) ξ
  have hb := norm_fourier_le_integral_norm_real (iteratedDeriv k f) ξ
  rw [h, norm_smul, norm_pow] at hb
  have hn : ‖(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ))‖ = 2 * Real.pi * |ξ| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rwa [hn] at hb

theorem iteratedDeriv_ofReal_comp_of_le {u : ℝ → ℝ} {k : ℕ} (hu : ContDiff ℝ k u) {j : ℕ} (hj : j ≤ k) :
    iteratedDeriv j (fun y => (u y : ℂ)) = fun y => ((iteratedDeriv j u y : ℝ) : ℂ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih (by omega), iteratedDeriv_succ]
    funext y
    have hd : Differentiable ℝ (iteratedDeriv j u) :=
      hu.differentiable_iteratedDeriv j (by exact_mod_cast (show j < k by omega))
    exact ((hd y).hasDerivAt.ofReal_comp).deriv

theorem iteratedDeriv_comp_affine {G : ℝ → ℝ} {k : ℕ} (hG : ContDiff ℝ k G) (β γ : ℝ) {j : ℕ}
    (hj : j ≤ k) :
    iteratedDeriv j (fun y => G (β + γ * y)) = fun y => γ ^ j * iteratedDeriv j G (β + γ * y) := by
  have hc : ContDiff ℝ j (fun z => G (β + z)) :=
    (hG.of_le (by exact_mod_cast hj)).comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_comp_const_mul hc γ, iteratedDeriv_comp_const_add]

theorem integrable_inv_one_add_sq_affine (β : ℝ) {γ : ℝ} (hγ : γ ≠ 0) :
    Integrable fun y : ℝ => (1 + (β + γ * y) ^ 2)⁻¹ :=
  (integrable_inv_one_add_sq.comp_add_left β).comp_mul_left' hγ

theorem integral_inv_one_add_sq_affine (β : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∫ y : ℝ, (1 + (β + γ * y) ^ 2)⁻¹ = γ⁻¹ * Real.pi := by
  rw [Measure.integral_comp_mul_left (fun z => (1 + (β + z) ^ 2)⁻¹) γ,
    integral_add_left_eq_self (fun z : ℝ => (1 + z ^ 2)⁻¹) β, integral_univ_inv_one_add_sq,
    abs_of_pos (inv_pos.2 hγ), smul_eq_mul]

/-- `(1 + (β + γy)²)^{−1} ≤ 4/(γ²y²)` once `γ|y| ≥ 2|β|`. -/
theorem inv_one_add_sq_affine_le {β γ y : ℝ} (hγ : 0 < γ) (hy : 2 * |β| ≤ γ * |y|) (hy0 : y ≠ 0) :
    (1 + (β + γ * y) ^ 2)⁻¹ ≤ 4 / γ ^ 2 * |y| ^ (-2 : ℝ) := by
  have hyabs : 0 < |y| := abs_pos.2 hy0
  have h1 : γ * |y| / 2 ≤ |β + γ * y| := by
    have := abs_sub_abs_le_abs_sub (γ * y) (-β)
    rw [sub_neg_eq_add, add_comm, abs_neg, abs_mul, abs_of_pos hγ] at this
    linarith
  have h2 : (γ * |y| / 2) ^ 2 ≤ (β + γ * y) ^ 2 := by
    rw [← sq_abs (β + γ * y)]
    exact pow_le_pow_left₀ (by positivity) h1 2
  rw [Real.rpow_neg (abs_nonneg _), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpos : 0 < (γ * |y| / 2) ^ 2 := by positivity
  calc (1 + (β + γ * y) ^ 2)⁻¹ ≤ ((γ * |y| / 2) ^ 2)⁻¹ := by
        apply inv_anti₀ hpos; linarith
    _ = 4 / γ ^ 2 * (|y| ^ 2)⁻¹ := by field_simp; ring

/-- **Poisson summation along a progression.** -/
theorem summable_and_abs_tsum_progression_sub_integral_le {G : ℝ → ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hG : ContDiff ℝ k G) {M : ℝ} (hM : ∀ j ≤ k, ∀ x, |iteratedDeriv j G x| ≤ M * (1 + x ^ 2)⁻¹)
    {γ : ℝ} (hγ : 0 < γ) (β : ℝ) :
    Summable (fun n : ℤ => G (β + γ * n)) ∧
      |∑' n : ℤ, G (β + γ * n) - γ⁻¹ * ∫ x, G x| ≤
        M * γ ^ (k - 1) * ∑' n : ℤ, |(n : ℝ)| ^ (-2 : ℝ) := by
  have hM0 : 0 ≤ M := by
    have := (abs_nonneg _).trans (hM 0 (Nat.zero_le k) 0)
    simpa using this
  set h : ℝ → ℂ := fun y => (G (β + γ * y) : ℂ) with hh
  have hGa : ContDiff ℝ k (fun y => G (β + γ * y)) :=
    hG.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hcd : ContDiff ℝ k h := Complex.ofRealCLM.contDiff.comp hGa
  have hder : ∀ j ≤ k, iteratedDeriv j h =
      fun y => ((γ ^ j * iteratedDeriv j G (β + γ * y) : ℝ) : ℂ) := by
    intro j hj
    rw [hh, iteratedDeriv_ofReal_comp_of_le hGa hj, iteratedDeriv_comp_affine hG β γ hj]
  have hbound : ∀ j ≤ k, ∀ y, ‖iteratedDeriv j h y‖ ≤ γ ^ j * M * (1 + (β + γ * y) ^ 2)⁻¹ := by
    intro j hj y
    rw [hder j hj, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hγ j), mul_assoc]
    exact mul_le_mul_of_nonneg_left (hM j hj _) (pow_pos hγ j).le
  have hint : ∀ j ≤ k, Integrable (iteratedDeriv j h) := by
    intro j hj
    refine ((integrable_inv_one_add_sq_affine β hγ.ne').const_mul (γ ^ j * M)).mono'
      (hcd.continuous_iteratedDeriv j (by exact_mod_cast hj)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    exact hbound j hj y
  -- the zero mode
  have h0 : 𝓕 h 0 = ((γ⁻¹ * ∫ x, G x : ℝ) : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul, hh]
    rw [integral_complex_ofReal]
    congr 1
    rw [Measure.integral_comp_mul_left (fun z => G (β + z)) γ, integral_add_left_eq_self G β,
      abs_of_pos (inv_pos.2 hγ), smul_eq_mul]
  -- nonzero modes
  set A : ℝ := γ ^ (k - 1) * M * Real.pi with hA
  have hmode : ∀ n : ℤ, n ≠ 0 → ‖𝓕 h n‖ ≤ A / (4 * Real.pi ^ 2) * |(n : ℝ)| ^ (-2 : ℝ) := by
    intro n hn
    have hnR : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    have hk' := pow_mul_norm_fourier_le_of_iteratedDeriv hcd hint (n : ℝ)
    have hI : ∫ x, ‖iteratedDeriv k h x‖ ≤ A := by
      calc ∫ x, ‖iteratedDeriv k h x‖ ≤ ∫ y, γ ^ k * M * (1 + (β + γ * y) ^ 2)⁻¹ :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              ((integrable_inv_one_add_sq_affine β hγ.ne').const_mul _)
              (Eventually.of_forall fun y => hbound k le_rfl y)
        _ = γ ^ k * M * (γ⁻¹ * Real.pi) := by
            rw [integral_const_mul, integral_inv_one_add_sq_affine β hγ]
        _ = A := by
            rw [hA]
            obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
            rw [Nat.add_sub_cancel, pow_succ]
            field_simp
    have hpow : (2 * Real.pi * |(n : ℝ)|) ^ 2 ≤ (2 * Real.pi * |(n : ℝ)|) ^ k := by
      apply pow_le_pow_right₀ _ hk
      nlinarith [Real.two_le_pi]
    have h2 : (2 * Real.pi * |(n : ℝ)|) ^ 2 * ‖𝓕 h n‖ ≤ A :=
      (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans (hk'.trans hI)
    rw [Real.rpow_neg (abs_nonneg _), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hpos : 0 < (2 * Real.pi * |(n : ℝ)|) ^ 2 := by positivity
    calc ‖𝓕 h n‖ ≤ A / (2 * Real.pi * |(n : ℝ)|) ^ 2 := by
          rw [le_div_iff₀ hpos]; linarith
      _ = A / (4 * Real.pi ^ 2) * (|(n : ℝ)| ^ 2)⁻¹ := by
          rw [mul_pow, mul_pow]; field_simp; ring
  have hZ : Summable fun n : ℤ => |(n : ℝ)| ^ (-2 : ℝ) := Real.summable_abs_int_rpow one_lt_two
  have hA0 : 0 ≤ A / (4 * Real.pi ^ 2) := by rw [hA]; positivity
  have hF : Summable fun n : ℤ => 𝓕 h n := by
    refine Summable.of_norm_bounded ((summable_of_ne_finset_zero (s := {0})
      (f := fun n : ℤ => if n = 0 then ‖𝓕 h 0‖ else 0) fun n hn => by
        rw [if_neg (by simpa using hn)]).add (hZ.mul_left (A / (4 * Real.pi ^ 2)))) fun n => ?_
    by_cases hn : n = 0
    · subst hn
      simp only [if_true, Int.cast_zero, abs_zero]
      have : (0 : ℝ) ^ (-2 : ℝ) = 0 := Real.zero_rpow (by norm_num)
      rw [this, mul_zero, add_zero]
    · rw [if_neg hn, zero_add]; exact hmode n hn
  -- decay of `h`
  have hdecay : h =O[Filter.cocompact ℝ] fun y : ℝ => |y| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound (M * (4 / γ ^ 2)) ?_
    rw [cocompact_eq_atBot_atTop, Filter.eventually_sup]
    have key : ∀ y : ℝ, 2 * (|β| + 1) / γ ≤ |y| →
        ‖h y‖ ≤ M * (4 / γ ^ 2) * ‖|y| ^ (-2 : ℝ)‖ := by
      intro y hy
      have hy0 : y ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hy
        have : 0 < 2 * (|β| + 1) / γ := by positivity
        linarith
      have hy' : 2 * |β| ≤ γ * |y| := by
        rw [div_le_iff₀ hγ] at hy; nlinarith [abs_nonneg β]
      have h0b := hbound 0 (Nat.zero_le k) y
      simp only [iteratedDeriv_zero, pow_zero, one_mul] at h0b
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      calc ‖h y‖ ≤ M * (1 + (β + γ * y) ^ 2)⁻¹ := h0b
        _ ≤ M * (4 / γ ^ 2 * |y| ^ (-2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (inv_one_add_sq_affine_le hγ hy' hy0) hM0
        _ = M * (4 / γ ^ 2) * |y| ^ (-2 : ℝ) := by ring
    constructor
    · filter_upwards [eventually_le_atBot (-(2 * (|β| + 1) / γ))] with y hy
      have hR : 0 < 2 * (|β| + 1) / γ := by positivity
      have hy0 : y < 0 := by linarith
      exact key y (by rw [abs_of_neg hy0]; linarith)
    · filter_upwards [eventually_ge_atTop (2 * (|β| + 1) / γ)] with y hy
      have hR : 0 < 2 * (|β| + 1) / γ := by positivity
      have hy0 : 0 < y := by linarith
      exact key y (by rw [abs_of_pos hy0]; exact hy)
  have hcont : Continuous h := hcd.continuous
  have hpoisson := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hcont one_lt_two hdecay hF 0
  have hfour : ∀ n : ℤ, (fourier n) ((0 : ℝ) : UnitAddCircle) = 1 := by
    intro n; rw [fourier_coe_apply]; simp
  simp only [zero_add, hfour, mul_one] at hpoisson
  -- summability of the progression
  have hsC : Summable fun n : ℤ => h n :=
    summable_of_isBigO hZ (hdecay.comp_tendsto Int.tendsto_coe_cofinite)
  have hs : Summable fun n : ℤ => G (β + γ * n) := Complex.summable_ofReal.1 hsC
  refine ⟨hs, ?_⟩
  have hreal : ((∑' n : ℤ, G (β + γ * n) : ℝ) : ℂ) = ∑' n : ℤ, 𝓕 h n := by
    rw [Complex.ofReal_tsum]; exact hpoisson
  have hsplit := hF.tsum_eq_add_tsum_ite 0
  rw [Int.cast_zero, h0] at hsplit
  have hdiff : ((∑' n : ℤ, G (β + γ * n) - γ⁻¹ * ∫ x, G x : ℝ) : ℂ) =
      ∑' n : ℤ, if n = 0 then 0 else 𝓕 h n := by
    rw [Complex.ofReal_sub, hreal, hsplit]; ring
  have hnorm : ‖((∑' n : ℤ, G (β + γ * n) - γ⁻¹ * ∫ x, G x : ℝ) : ℂ)‖ ≤
      ∑' n : ℤ, A / (4 * Real.pi ^ 2) * |(n : ℝ)| ^ (-2 : ℝ) := by
    rw [hdiff]
    have hb : ∀ n : ℤ, ‖(if n = 0 then 0 else 𝓕 h n)‖ ≤ A / (4 * Real.pi ^ 2) * |(n : ℝ)| ^ (-2 : ℝ) := by
      intro n
      by_cases hn : n = 0
      · rw [if_pos hn, norm_zero]; positivity
      · rw [if_neg hn]; exact hmode n hn
    exact tsum_of_norm_bounded (hZ.mul_left _).hasSum hb
  rw [Complex.norm_real, Real.norm_eq_abs, tsum_mul_left] at hnorm
  refine hnorm.trans ?_
  have hZ0 : 0 ≤ ∑' n : ℤ, |(n : ℝ)| ^ (-2 : ℝ) := tsum_nonneg fun n => Real.rpow_nonneg (abs_nonneg _) _
  have hfac : A / (4 * Real.pi ^ 2) ≤ M * γ ^ (k - 1) := by
    rw [hA, div_le_iff₀ (by positivity)]
    have : Real.pi ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
    have h0 : 0 ≤ γ ^ (k - 1) * M := by positivity
    nlinarith
  exact mul_le_mul_of_nonneg_right hfac hZ0

end

end RHTower
