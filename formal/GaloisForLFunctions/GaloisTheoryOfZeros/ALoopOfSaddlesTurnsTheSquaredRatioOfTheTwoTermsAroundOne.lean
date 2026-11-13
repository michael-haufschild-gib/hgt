import GaloisForLFunctions.GaloisTheoryOfZeros.TheHeatFamilyAtASaddleTimeIsAConstantPlusACosine
import GaloisForLFunctions.RHTower.XiHorizontalLogDerivativeModel
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# A loop of saddles turns the squared ratio of the two terms around one

The model `B₀(a) + 2S₀(a) cos ζ` of the heat family at the saddle time `τ(a)` has a double zero
where `2S₀ = ±B₀`. The square of the ratio has no square roots: since `2P − τ = τ(2a − 1)`,

`(2S₀)² = Q(a) B₀²`, `Q(a) = −64π⁴ e^{9a + 2f(a)} / (Φ(0)²(2a − 1))` (`two_mul_saddleTerm_sq`).

* `exists_basePoint`: the saddles `a₁ = 1 + η cot 2δ + iη`, `η = π/4 − δ`, have `Re f(a₁) = 0` and
  `3/10 ≤ δ Re a₁ ≤ 7/10`; there `|Q(a₁)| = c e^{9σ}/|2a₁ − 1|`.
* `saddleRatioSq_add`: exactly, with `D₁ = f'(a₁) = P₁(2a₁ − 1)`,
  `Q(a₁ + h) = Q(a₁) e^{2D₁h} · e^{2P₁R(h) + 9h} (2a₁ − 1)/(2a₁ − 1 + 2h)`,
  `R(h) = (e^{2h} − 1 − 2h)(a₁ − 1) + (e^{2h} − 1)h`.
* `loopSaddle a₁ s = a₁ + (−Log Q(a₁) − 2 Log cos ξ₀(s))/(2D₁)`, `ξ₀(s) = e^{iπs}/4`: a closed
  loop of saddles, of size `O(σe^{−2σ})`.
* `exists_loopSaddle` (**the loop**): for a base point far out, the loop stays in the saddle
  region and `|Q(a(s)) cos² ξ₀(s) − 1| ≤ 1/4096`: the value `Q` turns once around `1`, and the
  zeros `ζ` of the model follow `±ξ₀(s)` modulo `π`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The squared ratio of the saddle term to the bulk term -/

/-- The square of the ratio `2S₀/B₀`: `Q(a) = −64π⁴ e^{9a + 2f(a)} / (Φ(0)²(2a − 1))`. -/
def saddleRatioSq (a : ℂ) : ℂ :=
  -(64 * (π : ℂ) ^ 4) * cexp (9 * a + 2 * saddleValue a) / (kernelC 0 ^ 2 * (2 * a - 1))

theorem saddleP_ne_zero (a : ℂ) : saddleP a ≠ 0 :=
  mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (Complex.exp_ne_zero _)

/-- `2P − τ = τ(2a − 1)`. -/
theorem saddleRate_eq {a : ℂ} (ha : a ≠ 0) :
    2 * saddleP a - saddleTime a = saddleTime a * (2 * a - 1) := by
  have h := saddleTime_mul ha
  linear_combination -2 * h

theorem sq_cpow_half (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  have h := Complex.cpow_nat_inv_pow w (n := 2) (by norm_num)
  rwa [show (((2 : ℕ) : ℂ))⁻¹ = (1 / 2 : ℂ) by norm_num] at h

/-- **The squared ratio.** `(2S₀)² = Q B₀²`. -/
theorem two_mul_saddleTerm_sq {a : ℂ} (ha : a ≠ 0) (ha2 : 2 * a - 1 ≠ 0) :
    (2 * saddleTerm a) ^ 2 = saddleRatioSq a * bulkTerm a ^ 2 := by
  have hΦ := kernelC_zero_ne_zero
  have hτ : saddleTime a ≠ 0 := div_ne_zero (saddleP_ne_zero a) ha
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : cexp (9 * a / 2 + saddleValue a) ^ 2 = cexp (9 * a + 2 * saddleValue a) := by
    rw [sq, ← Complex.exp_add]
    congr 1
    ring
  rw [saddleTerm, bulkTerm, saddleRatioSq, saddleRate_eq ha]
  simp only [mul_pow, sq_cpow_half, he, Complex.I_sq]
  field_simp
  ring

/-! ## The cosine near the origin -/

theorem norm_cos_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖Complex.cos w - 1‖ ≤ ‖w‖ ^ 2 := by
  have h := Complex.cos_bound hw
  have h0 := norm_nonneg w
  have e : Complex.cos w - 1 = (Complex.cos w - (1 - w ^ 2 / 2)) + -(w ^ 2 / 2) := by ring
  have h2 : ‖-(w ^ 2 / 2)‖ = ‖w‖ ^ 2 / 2 := by
    rw [norm_neg, norm_div, norm_pow, Complex.norm_ofNat]
  have h4 : ‖w‖ ^ 4 ≤ ‖w‖ ^ 2 := by
    calc ‖w‖ ^ 4 = ‖w‖ ^ 2 * ‖w‖ ^ 2 := by ring
      _ ≤ ‖w‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0 hw) (sq_nonneg _)
      _ = ‖w‖ ^ 2 := mul_one _
  rw [e]
  calc ‖(Complex.cos w - (1 - w ^ 2 / 2)) + -(w ^ 2 / 2)‖
      ≤ ‖Complex.cos w - (1 - w ^ 2 / 2)‖ + ‖-(w ^ 2 / 2)‖ := norm_add_le _ _
    _ ≤ ‖w‖ ^ 4 * (5 / 96) + ‖w‖ ^ 2 / 2 := by rw [h2]; linarith
    _ ≤ ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]

/-- The half circle `ξ₀(s) = e^{iπs}/4` from `1/4` to `−1/4`. -/
def turnPoint (s : ℝ) : ℂ := (1 / 4 : ℂ) * cexp ((π * s : ℝ) * I)

theorem norm_turnPoint (s : ℝ) : ‖turnPoint s‖ = 1 / 4 := by
  have h : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num)]
  rw [turnPoint, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, h]

theorem turnPoint_zero : turnPoint 0 = 1 / 4 := by
  rw [turnPoint, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]

theorem turnPoint_one : turnPoint 1 = -(1 / 4) := by
  rw [turnPoint, mul_one, Complex.exp_pi_mul_I]
  ring

theorem continuous_turnPoint : Continuous turnPoint := by
  unfold turnPoint
  fun_prop

theorem norm_cos_turnPoint_sub_one_le (s : ℝ) : ‖Complex.cos (turnPoint s) - 1‖ ≤ 1 / 16 := by
  calc ‖Complex.cos (turnPoint s) - 1‖ ≤ ‖turnPoint s‖ ^ 2 :=
        norm_cos_sub_one_le (by rw [norm_turnPoint]; norm_num)
    _ = 1 / 16 := by rw [norm_turnPoint]; norm_num

theorem cos_turnPoint_mem_slitPlane (s : ℝ) : Complex.cos (turnPoint s) ∈ slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have h2 := (Complex.abs_re_le_norm (Complex.cos (turnPoint s) - 1)).trans
    (norm_cos_turnPoint_sub_one_le s)
  rw [Complex.sub_re, Complex.one_re] at h2
  linarith [(abs_le.mp h2).1]

theorem cos_turnPoint_ne_zero (s : ℝ) : Complex.cos (turnPoint s) ≠ 0 :=
  Complex.slitPlane_ne_zero (cos_turnPoint_mem_slitPlane s)

theorem norm_cos_turnPoint_bounds (s : ℝ) :
    15 / 16 ≤ ‖Complex.cos (turnPoint s)‖ ∧ ‖Complex.cos (turnPoint s)‖ ≤ 17 / 16 := by
  have h := norm_cos_turnPoint_sub_one_le s
  have h1 := norm_sub_norm_le (Complex.cos (turnPoint s)) 1
  have h2 := norm_sub_norm_le (1 : ℂ) (Complex.cos (turnPoint s))
  rw [norm_sub_rev] at h2
  rw [norm_one] at h1 h2
  constructor <;> linarith

theorem norm_log_cos_turnPoint_le (s : ℝ) :
    ‖Complex.log (Complex.cos (turnPoint s))‖ ≤ 1 / 2 := by
  have h := norm_cos_turnPoint_sub_one_le s
  have h1 := Complex.norm_log_one_add_half_le_self (z := Complex.cos (turnPoint s) - 1)
    (by linarith)
  rw [add_sub_cancel] at h1
  linarith

/-! ## Base points -/

theorem saddleValue_re (a : ℂ) : (saddleValue a).re =
    π * Real.exp (2 * a.re) *
      (Real.cos (2 * a.im) * (a.re - 1) - Real.sin (2 * a.im) * a.im) := by
  rw [saddleValue, Complex.mul_re, saddleP_re, saddleP_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero]
  ring

/-- **Base points.** For every `σ₂` there is a saddle `a₁` with `Re a₁ ≥ σ₂`, `Re f(a₁) = 0` and
`3/10 ≤ (π/4 − Im a₁) Re a₁ ≤ 7/10`: `a₁ = 1 + η cot 2δ + iη`, `η = π/4 − δ`, `δ` small. -/
theorem exists_basePoint (σ₂ : ℝ) : ∃ a₁ : ℂ, σ₂ ≤ a₁.re ∧ (saddleValue a₁).re = 0 ∧
    3 / 10 ≤ (π / 4 - a₁.im) * a₁.re ∧ (π / 4 - a₁.im) * a₁.re ≤ 7 / 10 := by
  have hπ3 := Real.pi_gt_d2
  have hπ4 := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hπne : π ≠ 0 := Real.pi_ne_zero
  have hm : 0 < max σ₂ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨δ, hδ0, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 100 ∧ δ * max σ₂ 1 ≤ 3 / 10 := by
    refine ⟨min (1 / 100) (3 / (10 * max σ₂ 1)), lt_min (by norm_num) (by positivity),
      min_le_left _ _, ?_⟩
    have h := min_le_right (1 / 100 : ℝ) (3 / (10 * max σ₂ 1))
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hδsq : δ * δ ≤ δ * (1 / 100) := mul_le_mul_of_nonneg_left hδ1 hδ0.le
  have hsn0 : 0 < Real.sin (2 * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsn_le : Real.sin (2 * δ) ≤ 2 * δ := Real.sin_le (by linarith)
  have hsn_ge : 4 / π * δ ≤ Real.sin (2 * δ) := by
    have h := Real.mul_le_sin (x := 2 * δ) (by linarith) (by linarith)
    calc 4 / π * δ = 2 / π * (2 * δ) := by ring
      _ ≤ Real.sin (2 * δ) := h
  have hcs_le : Real.cos (2 * δ) ≤ 1 := Real.cos_le_one _
  have hcs_ge : 1 - 2 * δ ^ 2 ≤ Real.cos (2 * δ) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := 2 * δ)
    calc 1 - 2 * δ ^ 2 = 1 - (2 * δ) ^ 2 / 2 := by ring
      _ ≤ Real.cos (2 * δ) := h
  have hcs0 : 0 < Real.cos (2 * δ) := by nlinarith
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = π / 4 - δ := ⟨_, rfl⟩
  have hη0 : 0 < η := by linarith
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = η * Real.cos (2 * δ) / Real.sin (2 * δ) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hkey : X * Real.sin (2 * δ) = η * Real.cos (2 * δ) := by
    rw [hX, div_mul_cancel₀ _ hsn0.ne']
  -- `δ X` lies between `38/100` and `63/100`
  have hlow : 38 / 100 ≤ δ * X := by
    have h1 : X * Real.sin (2 * δ) ≤ X * (2 * δ) := mul_le_mul_of_nonneg_left hsn_le hX0
    have h2 : η * (1 - 2 * δ ^ 2) ≤ η * Real.cos (2 * δ) :=
      mul_le_mul_of_nonneg_left hcs_ge hη0.le
    have h3 : (775 / 1000 : ℝ) ≤ η := by linarith
    have h4 : (9998 / 10000 : ℝ) ≤ 1 - 2 * δ ^ 2 := by nlinarith
    have h5 : (775 / 1000 : ℝ) * (9998 / 10000) ≤ η * (1 - 2 * δ ^ 2) :=
      mul_le_mul h3 h4 (by norm_num) hη0.le
    nlinarith
  have hupp : δ * X ≤ 63 / 100 := by
    have h1 : X * (4 / π * δ) ≤ X * Real.sin (2 * δ) := mul_le_mul_of_nonneg_left hsn_ge hX0
    have h2 : η * Real.cos (2 * δ) ≤ η * 1 := mul_le_mul_of_nonneg_left hcs_le hη0.le
    have h3 : 4 / π * (δ * X) ≤ π / 4 := by
      calc 4 / π * (δ * X) = X * (4 / π * δ) := by ring
        _ ≤ η * 1 := by linarith
        _ ≤ π / 4 := by linarith
    have h4 : δ * X ≤ π / 4 * (π / 4) := by
      have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ π / 4)
      have e : π / 4 * (4 / π * (δ * X)) = δ * X := by field_simp
      rw [e] at h5
      exact h5
    nlinarith [mul_le_mul hπ4.le hπ4.le hπ0.le (by norm_num : (0 : ℝ) ≤ 3.15)]
  have hδη : π / 4 - η = δ := by rw [hη]; ring
  refine ⟨⟨1 + X, η⟩, ?_, ?_, ?_, ?_⟩
  · show σ₂ ≤ 1 + X
    have h1 : δ * max σ₂ 1 ≤ δ * (1 + X) := by nlinarith
    exact (le_max_left _ _).trans (le_of_mul_le_mul_left h1 hδ0)
  · rw [saddleValue_re]
    have h2η : 2 * η = π / 2 - 2 * δ := by rw [hη]; ring
    show π * Real.exp (2 * (1 + X)) *
      (Real.cos (2 * η) * (1 + X - 1) - Real.sin (2 * η) * η) = 0
    rw [h2η, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    have h0 : Real.sin (2 * δ) * (1 + X - 1) - Real.cos (2 * δ) * η = 0 := by
      linear_combination hkey
    rw [h0, mul_zero]
  · show 3 / 10 ≤ (π / 4 - η) * (1 + X)
    rw [hδη]
    nlinarith
  · show (π / 4 - η) * (1 + X) ≤ 7 / 10
    rw [hδη]
    nlinarith

/-! ## The squared ratio near a base point -/

/-- **The squared ratio along a shift.** With `D₁ = P₁(2a₁ − 1)` the derivative of `f` at `a₁`,
`Q(a₁ + h) = Q(a₁) e^{2D₁h} · e^{2P₁R(h) + 9h}(2a₁ − 1)/(2a₁ − 1 + 2h)`,
`R(h) = (e^{2h} − 1 − 2h)(a₁ − 1) + (e^{2h} − 1)h`. -/
theorem saddleRatioSq_add {a₁ h : ℂ} (h1 : 2 * a₁ - 1 ≠ 0) (h2 : 2 * a₁ - 1 + 2 * h ≠ 0) :
    saddleRatioSq (a₁ + h) =
      saddleRatioSq a₁ * cexp (2 * (saddleP a₁ * (2 * a₁ - 1)) * h) *
        (cexp (2 * saddleP a₁ *
            ((cexp (2 * h) - 1 - 2 * h) * (a₁ - 1) + (cexp (2 * h) - 1) * h) + 9 * h) *
          ((2 * a₁ - 1) / (2 * a₁ - 1 + 2 * h))) := by
  have hΦ := kernelC_zero_ne_zero
  have hP : saddleP (a₁ + h) = saddleP a₁ * cexp (2 * h) := by
    rw [saddleP, saddleP, mul_add, Complex.exp_add]
    ring
  have he : 9 * (a₁ + h) + 2 * saddleValue (a₁ + h) =
      (9 * a₁ + 2 * saddleValue a₁) + 2 * (saddleP a₁ * (2 * a₁ - 1)) * h +
        (2 * saddleP a₁ *
          ((cexp (2 * h) - 1 - 2 * h) * (a₁ - 1) + (cexp (2 * h) - 1) * h) + 9 * h) := by
    rw [saddleValue, saddleValue, hP]
    ring
  have h2' : 2 * (a₁ + h) - 1 ≠ 0 := by
    have e : 2 * (a₁ + h) - 1 = 2 * a₁ - 1 + 2 * h := by ring
    rw [e]
    exact h2
  have hden : 2 * (a₁ + h) - 1 = 2 * a₁ - 1 + 2 * h := by ring
  rw [saddleRatioSq, saddleRatioSq, he, Complex.exp_add, Complex.exp_add, hden]
  field_simp

/-- The factor beyond the linear term of the phase is close to `1`. -/
theorem norm_remainder_sub_one_le {a₁ h : ℂ} {K : ℝ} (hσ : 2 ≤ a₁.re) (him0 : 0 ≤ a₁.im)
    (him : a₁.im ≤ 1) (hK : K ≤ 1 / 17) (hh : ‖h‖ ≤ K)
    (hh2 : π * Real.exp (2 * a₁.re) * (a₁.re + 1) * ‖h‖ ^ 2 ≤ K) :
    ‖cexp (2 * saddleP a₁ *
          ((cexp (2 * h) - 1 - 2 * h) * (a₁ - 1) + (cexp (2 * h) - 1) * h) + 9 * h) *
        ((2 * a₁ - 1) / (2 * a₁ - 1 + 2 * h)) - 1‖ ≤ 70 * K := by
  have hπ := Real.pi_pos
  have hn0 := norm_nonneg h
  have hK0 : 0 ≤ K := hn0.trans hh
  have h2n : ‖2 * h‖ = 2 * ‖h‖ := by rw [norm_mul, Complex.norm_ofNat]
  have h2le : ‖2 * h‖ ≤ 1 := by rw [h2n]; linarith
  have hT2 : ‖cexp (2 * h) - 1 - 2 * h‖ ≤ 4 * ‖h‖ ^ 2 := by
    have h3 := Complex.norm_exp_sub_one_sub_id_le h2le
    rw [h2n] at h3
    exact h3.trans (le_of_eq (by ring))
  have hT1 : ‖cexp (2 * h) - 1‖ ≤ 4 * ‖h‖ := by
    have h3 := Complex.norm_exp_sub_one_le h2le
    rw [h2n] at h3
    linarith
  have ha1 : ‖a₁ - 1‖ ≤ a₁.re := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : (a₁ - 1).re = a₁.re - 1 := by simp
    have e2 : (a₁ - 1).im = a₁.im := by simp
    rw [e1, e2, abs_of_nonneg (by linarith), abs_of_nonneg him0]
    linarith
  -- the Taylor remainder of the phase
  have hR : ‖(cexp (2 * h) - 1 - 2 * h) * (a₁ - 1) + (cexp (2 * h) - 1) * h‖ ≤
      4 * ‖h‖ ^ 2 * (a₁.re + 1) := by
    calc ‖(cexp (2 * h) - 1 - 2 * h) * (a₁ - 1) + (cexp (2 * h) - 1) * h‖
        ≤ ‖cexp (2 * h) - 1 - 2 * h‖ * ‖a₁ - 1‖ + ‖cexp (2 * h) - 1‖ * ‖h‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, norm_mul]
      _ ≤ 4 * ‖h‖ ^ 2 * a₁.re + 4 * ‖h‖ * ‖h‖ :=
          add_le_add (mul_le_mul hT2 ha1 (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_right hT1 hn0)
      _ = 4 * ‖h‖ ^ 2 * (a₁.re + 1) := by ring
  set w : ℂ := 2 * saddleP a₁ *
    ((cexp (2 * h) - 1 - 2 * h) * (a₁ - 1) + (cexp (2 * h) - 1) * h) + 9 * h with hw
  have hwn : ‖w‖ ≤ 17 * K := by
    have h1 : ‖2 * saddleP a₁ *
        ((cexp (2 * h) - 1 - 2 * h) * (a₁ - 1) + (cexp (2 * h) - 1) * h)‖ ≤ 8 * K := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_saddleP]
      calc 2 * (π * Real.exp (2 * a₁.re)) *
            ‖(cexp (2 * h) - 1 - 2 * h) * (a₁ - 1) + (cexp (2 * h) - 1) * h‖
          ≤ 2 * (π * Real.exp (2 * a₁.re)) * (4 * ‖h‖ ^ 2 * (a₁.re + 1)) :=
            mul_le_mul_of_nonneg_left hR (by positivity)
        _ = 8 * (π * Real.exp (2 * a₁.re) * (a₁.re + 1) * ‖h‖ ^ 2) := by ring
        _ ≤ 8 * K := by linarith
    have h2 : ‖9 * h‖ ≤ 9 * K := by
      rw [norm_mul, Complex.norm_ofNat]
      linarith
    calc ‖w‖ ≤ ‖2 * saddleP a₁ *
          ((cexp (2 * h) - 1 - 2 * h) * (a₁ - 1) + (cexp (2 * h) - 1) * h)‖ + ‖9 * h‖ :=
          norm_add_le _ _
      _ ≤ 17 * K := by linarith
  have hexp : ‖cexp w - 1‖ ≤ 34 * K := by
    have h3 := Complex.norm_exp_sub_one_le (x := w) (by linarith)
    linarith
  -- the rational factor
  have hden : 1 ≤ ‖2 * a₁ - 1 + 2 * h‖ := by
    have hre' : (2 * a₁ - 1 + 2 * h).re = 2 * a₁.re - 1 + 2 * h.re := by simp
    have h3 := Complex.re_le_norm (2 * a₁ - 1 + 2 * h)
    rw [hre'] at h3
    have h4 := (abs_le.mp ((Complex.abs_re_le_norm h).trans hh)).1
    linarith
  have hden0 : 2 * a₁ - 1 + 2 * h ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hden
    linarith
  set ρ : ℂ := (2 * a₁ - 1) / (2 * a₁ - 1 + 2 * h) with hρ
  have hρ1 : ‖ρ - 1‖ ≤ 2 * K := by
    have e : ρ - 1 = -(2 * h) / (2 * a₁ - 1 + 2 * h) := by
      rw [hρ, div_sub_one hden0]
      congr 1
      ring
    rw [e, norm_div, norm_neg, h2n, div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hden)]
  have hρn : ‖ρ‖ ≤ 2 := by
    have h3 := norm_sub_norm_le ρ 1
    rw [norm_one] at h3
    linarith
  calc ‖cexp w * ρ - 1‖ = ‖(cexp w - 1) * ρ + (ρ - 1)‖ := by congr 1; ring
    _ ≤ ‖cexp w - 1‖ * ‖ρ‖ + ‖ρ - 1‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul]
    _ ≤ 34 * K * 2 + 2 * K :=
        add_le_add (mul_le_mul hexp hρn (norm_nonneg _) (by positivity)) hρ1
    _ = 70 * K := by ring

/-! ## The loop of saddles -/

/-- The loop of saddles around the saddle where `Q = 1`:
`a(s) = a₁ + (−Log Q(a₁) − 2 Log cos ξ₀(s))/(2P₁(2a₁ − 1))`. -/
def loopSaddle (a₁ : ℂ) (s : ℝ) : ℂ :=
  a₁ + (-Complex.log (saddleRatioSq a₁) - 2 * Complex.log (Complex.cos (turnPoint s))) /
    (2 * (saddleP a₁ * (2 * a₁ - 1)))

theorem continuous_loopSaddle (a₁ : ℂ) : Continuous (loopSaddle a₁) := by
  have h : Continuous fun s : ℝ => Complex.log (Complex.cos (turnPoint s)) :=
    (Complex.continuous_cos.comp continuous_turnPoint).clog cos_turnPoint_mem_slitPlane
  unfold loopSaddle
  exact continuous_const.add ((continuous_const.sub (continuous_const.mul h)).div_const _)

/-- The loop is closed: `ξ₀(1) = −ξ₀(0)` and the cosine is even. -/
theorem loopSaddle_one (a₁ : ℂ) : loopSaddle a₁ 1 = loopSaddle a₁ 0 := by
  rw [loopSaddle, loopSaddle, turnPoint_one, turnPoint_zero, Complex.cos_neg]

/-- The constant of the size of the loop: `|log(64π⁴/Φ(0)²)| + 12`. -/
def loopConst : ℝ := |Real.log (64 * π ^ 4 / ‖kernelC 0‖ ^ 2)| + 12

/-- **The loop at a base point.** If `Re a₁ = σ ≥ 51`, `Re f(a₁) = 0`,
`3/10 ≤ (π/4 − Im a₁)σ ≤ 7/10` and `(1 + M)²σ⁴e^{−σ} ≤ 1/300000`, then every point of the loop is
in the saddle region, within `1` of `a₁`, and `|Q(a(s)) cos² ξ₀(s) − 1| ≤ 1/4096`. -/
theorem loopSaddle_spec {a₁ : ℂ} (hσ : 51 ≤ a₁.re) (hf : (saddleValue a₁).re = 0)
    (hlo : 3 / 10 ≤ (π / 4 - a₁.im) * a₁.re) (hhi : (π / 4 - a₁.im) * a₁.re ≤ 7 / 10)
    (hK : (1 + loopConst) ^ 2 * a₁.re ^ 4 * Real.exp (-a₁.re) ≤ 1 / 300000) (s : ℝ) :
    SaddleRegion (loopSaddle a₁ s) ∧ a₁.re - 1 ≤ (loopSaddle a₁ s).re ∧
      ‖saddleRatioSq (loopSaddle a₁ s) * Complex.cos (turnPoint s) ^ 2 - 1‖ ≤ 1 / 4096 := by
  have hπ3 := Real.pi_gt_d2
  have hπ4 := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hσ0 : 0 < a₁.re := by linarith
  have hM12 : 12 ≤ loopConst := by
    rw [loopConst]
    linarith [abs_nonneg (Real.log (64 * π ^ 4 / ‖kernelC 0‖ ^ 2))]
  have hM0 : 0 ≤ loopConst := by linarith
  -- the imaginary part of the base point
  have hd0 : 0 < π / 4 - a₁.im := by
    by_contra hc
    push Not at hc
    have h1 := mul_nonpos_of_nonpos_of_nonneg hc hσ0.le
    linarith
  have hd1 : π / 4 - a₁.im ≤ 1 / 50 := by
    by_contra hc
    push Not at hc
    have h1 := mul_lt_mul_of_pos_right hc hσ0
    linarith
  have him0 : 0 ≤ a₁.im := by linarith
  have him1 : a₁.im ≤ 1 := by linarith
  -- the norm of `2a₁ − 1`
  have hre2 : (2 * a₁ - 1).re = 2 * a₁.re - 1 := by simp
  have him2 : (2 * a₁ - 1).im = 2 * a₁.im := by simp
  have hn_lo : 2 * a₁.re - 1 ≤ ‖2 * a₁ - 1‖ := by
    have h1 := Complex.re_le_norm (2 * a₁ - 1)
    rw [hre2] at h1
    exact h1
  have hn_hi : ‖2 * a₁ - 1‖ ≤ 2 * a₁.re + 1 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hre2, him2, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  have hn0 : 0 < ‖2 * a₁ - 1‖ := lt_of_lt_of_le (by linarith) hn_lo
  have h2a : 2 * a₁ - 1 ≠ 0 := norm_pos_iff.mp hn0
  -- the size of `Q(a₁)`
  have hΦ : 0 < ‖kernelC 0‖ := norm_pos_iff.mpr kernelC_zero_ne_zero
  have hc₀pos : 0 < 64 * π ^ 4 / ‖kernelC 0‖ ^ 2 := by positivity
  have hQnorm : ‖saddleRatioSq a₁‖ =
      64 * π ^ 4 / ‖kernelC 0‖ ^ 2 * Real.exp (9 * a₁.re) / ‖2 * a₁ - 1‖ := by
    have h1 : ‖-(64 * (π : ℂ) ^ 4)‖ = 64 * π ^ 4 := by
      rw [norm_neg, show (64 : ℂ) * (π : ℂ) ^ 4 = ((64 * π ^ 4 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h2 : (9 * a₁ + 2 * saddleValue a₁).re = 9 * a₁.re := by
      have e1 : (9 * a₁).re = 9 * a₁.re := by simp
      have e2 : (2 * saddleValue a₁).re = 2 * (saddleValue a₁).re := by simp
      rw [Complex.add_re, e1, e2, hf]
      ring
    rw [saddleRatioSq, norm_div, norm_mul, norm_mul, norm_pow, h1, Complex.norm_exp, h2]
    ring
  have hQne : saddleRatioSq a₁ ≠ 0 := by
    rw [← norm_pos_iff, hQnorm]
    exact div_pos (mul_pos hc₀pos (Real.exp_pos _)) hn0
  have hlogn : 0 ≤ Real.log ‖2 * a₁ - 1‖ := Real.log_nonneg (by linarith)
  have hlogn2 : Real.log ‖2 * a₁ - 1‖ ≤ 2 * a₁.re := by
    have h1 := Real.log_le_sub_one_of_pos hn0
    linarith
  have hlogQ : Real.log ‖saddleRatioSq a₁‖ =
      Real.log (64 * π ^ 4 / ‖kernelC 0‖ ^ 2) + 9 * a₁.re - Real.log ‖2 * a₁ - 1‖ := by
    rw [hQnorm, Real.log_div (mul_pos hc₀pos (Real.exp_pos _)).ne' hn0.ne',
      Real.log_mul hc₀pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlogQn : ‖Complex.log (saddleRatioSq a₁)‖ ≤ loopConst - 12 + 11 * a₁.re + π := by
    refine (norm_log_le_abs_log_norm_add_abs_arg _).trans ?_
    have h1 := Complex.abs_arg_le_pi (saddleRatioSq a₁)
    have h2 : |Real.log ‖saddleRatioSq a₁‖| ≤
        |Real.log (64 * π ^ 4 / ‖kernelC 0‖ ^ 2)| + 11 * a₁.re := by
      rw [hlogQ, abs_le]
      have h3 := neg_abs_le (Real.log (64 * π ^ 4 / ‖kernelC 0‖ ^ 2))
      have h4 := le_abs_self (Real.log (64 * π ^ 4 / ‖kernelC 0‖ ^ 2))
      constructor <;> linarith
    have h5 : loopConst - 12 = |Real.log (64 * π ^ 4 / ‖kernelC 0‖ ^ 2)| := by
      rw [loopConst]
      ring
    linarith
  -- the shift
  obtain ⟨h, hh⟩ : ∃ h : ℂ, h =
      (-Complex.log (saddleRatioSq a₁) - 2 * Complex.log (Complex.cos (turnPoint s))) /
        (2 * (saddleP a₁ * (2 * a₁ - 1))) := ⟨_, rfl⟩
  have hloop : loopSaddle a₁ s = a₁ + h := by rw [loopSaddle, hh]
  have hP0 := saddleP_ne_zero a₁
  have hE : 0 < Real.exp (2 * a₁.re) := Real.exp_pos _
  have hD : ‖2 * (saddleP a₁ * (2 * a₁ - 1))‖ =
      2 * (π * Real.exp (2 * a₁.re) * ‖2 * a₁ - 1‖) := by
    rw [norm_mul, norm_mul, norm_saddleP, Complex.norm_ofNat]
  have hDpos : 0 < 2 * (π * Real.exp (2 * a₁.re) * ‖2 * a₁ - 1‖) :=
    mul_pos two_pos (mul_pos (mul_pos hπ0 hE) hn0)
  have hnum : ‖-Complex.log (saddleRatioSq a₁) -
      2 * Complex.log (Complex.cos (turnPoint s))‖ ≤ loopConst * a₁.re := by
    have h1 := norm_log_cos_turnPoint_le s
    calc ‖-Complex.log (saddleRatioSq a₁) - 2 * Complex.log (Complex.cos (turnPoint s))‖
        ≤ ‖-Complex.log (saddleRatioSq a₁)‖ +
            ‖2 * Complex.log (Complex.cos (turnPoint s))‖ := norm_sub_le _ _
      _ ≤ (loopConst - 12 + 11 * a₁.re + π) + 2 * (1 / 2) := by
          rw [norm_neg, norm_mul, Complex.norm_ofNat]
          linarith
      _ ≤ loopConst * a₁.re := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hM12) (by linarith : (0 : ℝ) ≤ a₁.re - 1)]
  have hhn : ‖h‖ ≤ loopConst * Real.exp (-(2 * a₁.re)) := by
    rw [hh, norm_div, hD, div_le_iff₀ hDpos]
    have e : loopConst * Real.exp (-(2 * a₁.re)) *
        (2 * (π * Real.exp (2 * a₁.re) * ‖2 * a₁ - 1‖)) =
        2 * π * loopConst * ‖2 * a₁ - 1‖ *
          (Real.exp (-(2 * a₁.re)) * Real.exp (2 * a₁.re)) := by ring
    rw [e, SaddleRegion.exp_neg_two_mul_exp, mul_one]
    refine hnum.trans ?_
    have h1 : loopConst * a₁.re ≤ loopConst * ‖2 * a₁ - 1‖ :=
      mul_le_mul_of_nonneg_left (by linarith) hM0
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * π - 1) (mul_nonneg hM0 hn0.le)]
  -- the smallness parameter
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (1 + loopConst) ^ 2 * a₁.re ^ 4 * Real.exp (-a₁.re) :=
    ⟨_, rfl⟩
  rw [← hKdef] at hK
  have hx0 : 0 < Real.exp (-a₁.re) := Real.exp_pos _
  have hx1 : Real.exp (-a₁.re) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx2 : Real.exp (-(2 * a₁.re)) = Real.exp (-a₁.re) * Real.exp (-a₁.re) := by
    rw [← Real.exp_add]
    ring_nf
  have hMM : loopConst ≤ (1 + loopConst) ^ 2 := by nlinarith
  have hMM2 : loopConst ^ 2 ≤ (1 + loopConst) ^ 2 := by nlinarith
  have hσ14 : a₁.re ≤ a₁.re ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have h8σ : 8 * a₁.re ≤ a₁.re ^ 4 := by
    have h3 : (8 : ℝ) ≤ a₁.re ^ 3 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 51) hσ 3)
    have e : a₁.re ^ 4 = a₁.re * a₁.re ^ 3 := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h3 hσ0.le]
  have hk1 : loopConst * Real.exp (-(2 * a₁.re)) * a₁.re ≤ K := by
    have hA : loopConst * a₁.re ≤ (1 + loopConst) ^ 2 * a₁.re ^ 4 :=
      mul_le_mul hMM hσ14 hσ0.le (by positivity)
    calc loopConst * Real.exp (-(2 * a₁.re)) * a₁.re
        = loopConst * a₁.re * Real.exp (-a₁.re) * Real.exp (-a₁.re) := by rw [hx2]; ring
      _ ≤ loopConst * a₁.re * Real.exp (-a₁.re) * 1 :=
          mul_le_mul_of_nonneg_left hx1 (by positivity)
      _ ≤ (1 + loopConst) ^ 2 * a₁.re ^ 4 * Real.exp (-a₁.re) * 1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hx0.le) zero_le_one
      _ = K := by rw [hKdef, mul_one]
  have hhσ : ‖h‖ * a₁.re ≤ K :=
    (mul_le_mul_of_nonneg_right hhn hσ0.le).trans hk1
  have hhK : ‖h‖ ≤ K := by
    have h1 : ‖h‖ * 1 ≤ ‖h‖ * a₁.re := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg h)
    linarith
  have hk2 : π * Real.exp (2 * a₁.re) * (a₁.re + 1) * ‖h‖ ^ 2 ≤ K := by
    have h1 : ‖h‖ ^ 2 ≤ (loopConst * Real.exp (-(2 * a₁.re))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg h) hhn 2
    have e : π * Real.exp (2 * a₁.re) * (a₁.re + 1) *
        (loopConst * Real.exp (-(2 * a₁.re))) ^ 2 =
        π * (a₁.re + 1) * loopConst ^ 2 * Real.exp (-(2 * a₁.re)) *
          (Real.exp (-(2 * a₁.re)) * Real.exp (2 * a₁.re)) := by ring
    have h2 : π * (a₁.re + 1) ≤ a₁.re ^ 4 := by nlinarith
    have h3 : π * (a₁.re + 1) * loopConst ^ 2 ≤ a₁.re ^ 4 * (1 + loopConst) ^ 2 :=
      mul_le_mul h2 hMM2 (sq_nonneg _) (by positivity)
    calc π * Real.exp (2 * a₁.re) * (a₁.re + 1) * ‖h‖ ^ 2
        ≤ π * Real.exp (2 * a₁.re) * (a₁.re + 1) *
            (loopConst * Real.exp (-(2 * a₁.re))) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = π * (a₁.re + 1) * loopConst ^ 2 * (Real.exp (-a₁.re) * Real.exp (-a₁.re)) := by
          rw [e, SaddleRegion.exp_neg_two_mul_exp, mul_one, hx2]
      _ ≤ a₁.re ^ 4 * (1 + loopConst) ^ 2 * (Real.exp (-a₁.re) * 1) :=
          mul_le_mul h3 (mul_le_mul_of_nonneg_left hx1 hx0.le) (by positivity) (by positivity)
      _ = K := by rw [hKdef]; ring
  -- the loop stays in the saddle region
  have hK0 : 0 ≤ K := (norm_nonneg h).trans hhK
  have ht51 : ‖h‖ * 51 ≤ 1 / 300000 := by
    have h1 : ‖h‖ * 51 ≤ ‖h‖ * a₁.re := mul_le_mul_of_nonneg_left hσ (norm_nonneg h)
    linarith
  have hre := abs_le.mp (Complex.abs_re_le_norm h)
  have him := abs_le.mp (Complex.abs_im_le_norm h)
  have hreg : SaddleRegion (a₁ + h) := by
    have hn := norm_nonneg h
    have hare : (a₁ + h).re = a₁.re + h.re := Complex.add_re _ _
    have haim : (a₁ + h).im = a₁.im + h.im := Complex.add_im _ _
    have hpos : 0 < a₁.re + h.re := by linarith [hre.1]
    -- the products of the shift with the base point
    have A1 : (π / 4 - a₁.im) * ‖h‖ ≤ 1 / 50 * ‖h‖ := mul_le_mul_of_nonneg_right hd1 hn
    have A2 : -((π / 4 - a₁.im) * ‖h‖) ≤ (π / 4 - a₁.im) * h.re := by
      have := mul_le_mul_of_nonneg_left hre.1 hd0.le
      linarith
    have A3 : (π / 4 - a₁.im) * h.re ≤ (π / 4 - a₁.im) * ‖h‖ :=
      mul_le_mul_of_nonneg_left hre.2 hd0.le
    have A4 : h.im * a₁.re ≤ ‖h‖ * a₁.re := mul_le_mul_of_nonneg_right him.2 hσ0.le
    have A5 : -(‖h‖ * a₁.re) ≤ h.im * a₁.re := by
      have := mul_le_mul_of_nonneg_right him.1 hσ0.le
      linarith
    have A6 : |h.im * h.re| ≤ ‖h‖ * ‖h‖ := by
      rw [abs_mul]
      exact mul_le_mul (Complex.abs_im_le_norm h) (Complex.abs_re_le_norm h) (abs_nonneg _) hn
    have A7 : ‖h‖ * ‖h‖ ≤ ‖h‖ * 1 := mul_le_mul_of_nonneg_left (by linarith) hn
    have A6' := abs_le.mp A6
    have hprod : (π / 4 - (a₁.im + h.im)) * (a₁.re + h.re) =
        (π / 4 - a₁.im) * a₁.re + (π / 4 - a₁.im) * h.re - h.im * a₁.re - h.im * h.re := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hare]
      linarith [hre.1]
    · rw [hare, haim, div_le_iff₀ (by linarith)]
      have h1 : 1 / 4 ≤ (π / 4 - (a₁.im + h.im)) * (a₁.re + h.re) := by
        rw [hprod]
        linarith [A6'.2]
      linarith
    · rw [hare, haim, le_div_iff₀ hpos, hprod]
      linarith [A6'.1]
  -- the squared ratio on the loop
  have h2h : 2 * a₁ - 1 + 2 * h ≠ 0 := by
    intro h0
    have hre' : (2 * a₁ - 1 + 2 * h).re = 2 * a₁.re - 1 + 2 * h.re := by simp
    rw [h0, Complex.zero_re] at hre'
    linarith [hre.1]
  have hcos0 := cos_turnPoint_ne_zero s
  have hD0 : 2 * (saddleP a₁ * (2 * a₁ - 1)) ≠ 0 :=
    mul_ne_zero two_ne_zero (mul_ne_zero hP0 h2a)
  have hexp : cexp (2 * (saddleP a₁ * (2 * a₁ - 1)) * h) =
      (saddleRatioSq a₁)⁻¹ * (Complex.cos (turnPoint s) ^ 2)⁻¹ := by
    have e : 2 * (saddleP a₁ * (2 * a₁ - 1)) * h =
        -Complex.log (saddleRatioSq a₁) - 2 * Complex.log (Complex.cos (turnPoint s)) := by
      rw [hh, mul_div_cancel₀ _ hD0]
    rw [e, Complex.exp_sub, Complex.exp_neg, Complex.exp_log hQne, two_mul, Complex.exp_add,
      Complex.exp_log hcos0, div_eq_mul_inv, sq]
  have hX := norm_remainder_sub_one_le (a₁ := a₁) (h := h) (K := K) (by linarith) him0 him1
    (by linarith) hhK hk2
  have hQ : saddleRatioSq (a₁ + h) * Complex.cos (turnPoint s) ^ 2 =
      cexp (2 * saddleP a₁ *
          ((cexp (2 * h) - 1 - 2 * h) * (a₁ - 1) + (cexp (2 * h) - 1) * h) + 9 * h) *
        ((2 * a₁ - 1) / (2 * a₁ - 1 + 2 * h)) := by
    rw [saddleRatioSq_add h2a h2h, hexp]
    have hc2 : Complex.cos (turnPoint s) ^ 2 ≠ 0 := pow_ne_zero 2 hcos0
    field_simp
  rw [hloop]
  refine ⟨hreg, ?_, ?_⟩
  · rw [Complex.add_re]
    linarith [hre.1]
  · rw [hQ]
    linarith

/-- The smallness of the loop holds far out. -/
theorem exists_loop_threshold : ∃ σ₂ : ℝ, 51 ≤ σ₂ ∧ ∀ σ : ℝ, σ₂ ≤ σ →
    (1 + loopConst) ^ 2 * σ ^ 4 * Real.exp (-σ) ≤ 1 / 300000 := by
  have ht : Tendsto (fun x : ℝ => (1 + loopConst) ^ 2 * (x ^ 4 * Real.exp (-x))) atTop
      (𝓝 ((1 + loopConst) ^ 2 * 0)) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).const_mul _
  rw [mul_zero] at ht
  obtain ⟨σ₂, hσ₂⟩ := eventually_atTop.mp
    (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 300000)))
  refine ⟨max σ₂ 51, le_max_right _ _, fun σ hσ => ?_⟩
  have h1 := (hσ₂ σ ((le_max_left _ _).trans hσ)).le
  calc (1 + loopConst) ^ 2 * σ ^ 4 * Real.exp (-σ)
      = (1 + loopConst) ^ 2 * (σ ^ 4 * Real.exp (-σ)) := by ring
    _ ≤ 1 / 300000 := h1

/-- **The loop of saddles.** For every `σ₀` there is a base point `a₁` whose loop `a(s)` stays in
the saddle region with `Re a(s) ≥ σ₀` and `|Q(a(s)) cos² ξ₀(s) − 1| ≤ 1/4096`. -/
theorem exists_loopSaddle (σ₀ : ℝ) : ∃ a₁ : ℂ, ∀ s : ℝ, SaddleRegion (loopSaddle a₁ s) ∧
    σ₀ ≤ (loopSaddle a₁ s).re ∧
      ‖saddleRatioSq (loopSaddle a₁ s) * Complex.cos (turnPoint s) ^ 2 - 1‖ ≤ 1 / 4096 := by
  obtain ⟨σ₂, h51, hthr⟩ := exists_loop_threshold
  obtain ⟨a₁, ha, hf, hlo, hhi⟩ := exists_basePoint (max σ₂ (σ₀ + 1))
  have h1 : σ₂ ≤ a₁.re := (le_max_left _ _).trans ha
  have h2 : σ₀ + 1 ≤ a₁.re := (le_max_right _ _).trans ha
  refine ⟨a₁, fun s => ?_⟩
  obtain ⟨hR, hre, hQ⟩ := loopSaddle_spec (h51.trans h1) hf hlo hhi (hthr _ h1) s
  exact ⟨hR, by linarith, hQ⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
