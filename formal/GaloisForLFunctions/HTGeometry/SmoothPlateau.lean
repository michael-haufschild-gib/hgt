import GaloisForLFunctions.HTGeometry.SmoothWeight
import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smooth plateaus

`smoothPlateau a b ℓ x = σ((x − a)/ℓ)·σ((b − x)/ℓ)`, with `σ = Real.smoothTransition`, is smooth,
takes values in `[0, 1]`, vanishes off `(a, b)` and equals `1` on `[a + ℓ, b − ℓ]`.  Its first
two derivatives are written out explicitly (`smoothPlateauDeriv`, `smoothPlateauDeriv2`) and obey:

* `|φ'| ≤ K₁/ℓ` and `|φ''| ≤ K₂/ℓ²` with absolute constants;
* `∫_u^v |φ'| ≤ 2` on every interval: `σ` is nondecreasing, so `|φ'|` is at most the sum of the
  derivatives of the two monotone factors, whose integrals telescope to at most `1` each.

A dilated plateau is again a plateau: `smoothPlateau a b ℓ (x/X) = smoothPlateau (aX) (bX) (ℓX) x`.
-/

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem hasDerivAt_smoothTransition (x : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt

theorem contDiff_deriv_smoothTransition (n : ℕ) : ContDiff ℝ n (deriv Real.smoothTransition) :=
  (contDiff_infty_iff_deriv.1 Real.smoothTransition.contDiff).2.of_le (by exact_mod_cast le_top)

theorem hasDerivAt_deriv_smoothTransition (x : ℝ) :
    HasDerivAt (deriv Real.smoothTransition) (deriv (deriv Real.smoothTransition) x) x :=
  ((contDiff_deriv_smoothTransition 1).differentiable (by norm_num) x).hasDerivAt

theorem continuous_deriv_deriv_smoothTransition :
    Continuous (deriv (deriv Real.smoothTransition)) :=
  (contDiff_deriv_smoothTransition 1).continuous_deriv (by norm_num)

theorem deriv_smoothTransition_nonneg (x : ℝ) : 0 ≤ deriv Real.smoothTransition x :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem exists_bound_deriv_deriv_smoothTransition :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ Λ := by
  obtain ⟨C, hC, h⟩ := exists_bound_iteratedDeriv_smoothTransition 2
  refine ⟨C, hC, fun x => ?_⟩
  have e : iteratedDeriv 2 Real.smoothTransition = deriv (deriv Real.smoothTransition) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  simpa [e] using h x

/-- The smooth plateau on `(a, b)` with transition length `ℓ`. -/
def smoothPlateau (a b ℓ x : ℝ) : ℝ :=
  Real.smoothTransition ((x - a) / ℓ) * Real.smoothTransition ((b - x) / ℓ)

/-- The derivative of the smooth plateau. -/
def smoothPlateauDeriv (a b ℓ x : ℝ) : ℝ :=
  deriv Real.smoothTransition ((x - a) / ℓ) / ℓ * Real.smoothTransition ((b - x) / ℓ) -
    Real.smoothTransition ((x - a) / ℓ) * (deriv Real.smoothTransition ((b - x) / ℓ) / ℓ)

/-- The second derivative of the smooth plateau. -/
def smoothPlateauDeriv2 (a b ℓ x : ℝ) : ℝ :=
  deriv (deriv Real.smoothTransition) ((x - a) / ℓ) / ℓ ^ 2 * Real.smoothTransition ((b - x) / ℓ) -
    2 * (deriv Real.smoothTransition ((x - a) / ℓ) / ℓ) *
      (deriv Real.smoothTransition ((b - x) / ℓ) / ℓ) +
    Real.smoothTransition ((x - a) / ℓ) * (deriv (deriv Real.smoothTransition) ((b - x) / ℓ) / ℓ ^ 2)

variable {a b ℓ : ℝ}

theorem smoothPlateau_nonneg (x : ℝ) : 0 ≤ smoothPlateau a b ℓ x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem smoothPlateau_le_one (x : ℝ) : smoothPlateau a b ℓ x ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem smoothPlateau_eq_zero_of_le (hℓ : 0 < ℓ) {x : ℝ} (hx : x ≤ a) :
    smoothPlateau a b ℓ x = 0 := by
  rw [smoothPlateau, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hℓ.le), zero_mul]

theorem smoothPlateau_eq_zero_of_ge (hℓ : 0 < ℓ) {x : ℝ} (hx : b ≤ x) :
    smoothPlateau a b ℓ x = 0 := by
  rw [smoothPlateau, Real.smoothTransition.zero_of_nonpos (x := (b - x) / ℓ)
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hℓ.le), mul_zero]

theorem smoothPlateau_eq_one (hℓ : 0 < ℓ) {x : ℝ} (h1 : a + ℓ ≤ x) (h2 : x ≤ b - ℓ) :
    smoothPlateau a b ℓ x = 1 := by
  rw [smoothPlateau, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hℓ).2 (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hℓ).2 (by linarith)), mul_one]

theorem smoothPlateau_mem_Icc (x : ℝ) : smoothPlateau a b ℓ x ∈ Icc (0 : ℝ) 1 :=
  ⟨smoothPlateau_nonneg x, smoothPlateau_le_one x⟩

theorem continuous_smoothPlateau : Continuous (smoothPlateau a b ℓ) := by
  unfold smoothPlateau
  exact (Real.smoothTransition.continuous.comp (by fun_prop)).mul
    (Real.smoothTransition.continuous.comp (by fun_prop))

theorem continuous_smoothPlateauDeriv : Continuous (smoothPlateauDeriv a b ℓ) := by
  unfold smoothPlateauDeriv
  have h1 := continuous_deriv_smoothTransition
  have h0 := Real.smoothTransition.continuous
  exact (((h1.comp (by fun_prop)).div_const ℓ).mul (h0.comp (by fun_prop))).sub
    ((h0.comp (by fun_prop)).mul ((h1.comp (by fun_prop)).div_const ℓ))

theorem continuous_smoothPlateauDeriv2 : Continuous (smoothPlateauDeriv2 a b ℓ) := by
  unfold smoothPlateauDeriv2
  have h2 := continuous_deriv_deriv_smoothTransition
  have h1 := continuous_deriv_smoothTransition
  have h0 := Real.smoothTransition.continuous
  exact ((((h2.comp (by fun_prop)).div_const _).mul (h0.comp (by fun_prop))).sub
    ((continuous_const.mul ((h1.comp (by fun_prop)).div_const ℓ)).mul
      ((h1.comp (by fun_prop)).div_const ℓ))).add
    ((h0.comp (by fun_prop)).mul ((h2.comp (by fun_prop)).div_const _))

private theorem hasDerivAt_left (ℓ a x : ℝ) :
    HasDerivAt (fun y => (y - a) / ℓ) (1 / ℓ) x :=
  ((hasDerivAt_id' x).sub_const a).div_const ℓ

private theorem hasDerivAt_right (ℓ b x : ℝ) :
    HasDerivAt (fun y => (b - y) / ℓ) (-(1 / ℓ)) x :=
  (((hasDerivAt_id' x).const_sub b).div_const ℓ).congr_deriv (by ring)

theorem hasDerivAt_smoothPlateau (x : ℝ) :
    HasDerivAt (smoothPlateau a b ℓ) (smoothPlateauDeriv a b ℓ x) x := by
  have h1 := (hasDerivAt_smoothTransition ((x - a) / ℓ)).comp x (hasDerivAt_left ℓ a x)
  have h2 := (hasDerivAt_smoothTransition ((b - x) / ℓ)).comp x (hasDerivAt_right ℓ b x)
  have h := h1.mul h2
  have hf : smoothPlateau a b ℓ = (Real.smoothTransition ∘ fun y => (y - a) / ℓ) *
      (Real.smoothTransition ∘ fun y => (b - y) / ℓ) := by funext y; rfl
  rw [hf]
  refine h.congr_deriv ?_
  simp only [smoothPlateauDeriv, Function.comp_apply]
  ring

theorem hasDerivAt_smoothPlateauDeriv (x : ℝ) :
    HasDerivAt (smoothPlateauDeriv a b ℓ) (smoothPlateauDeriv2 a b ℓ x) x := by
  have hd1 := (hasDerivAt_deriv_smoothTransition ((x - a) / ℓ)).comp x (hasDerivAt_left ℓ a x)
  have hd2 := (hasDerivAt_deriv_smoothTransition ((b - x) / ℓ)).comp x (hasDerivAt_right ℓ b x)
  have h1 := (hasDerivAt_smoothTransition ((x - a) / ℓ)).comp x (hasDerivAt_left ℓ a x)
  have h2 := (hasDerivAt_smoothTransition ((b - x) / ℓ)).comp x (hasDerivAt_right ℓ b x)
  have h := ((hd1.div_const ℓ).mul h2).sub (h1.mul (hd2.div_const ℓ))
  have hf : smoothPlateauDeriv a b ℓ = (fun y => (deriv Real.smoothTransition ∘
      fun y => (y - a) / ℓ) y / ℓ) * (Real.smoothTransition ∘ fun y => (b - y) / ℓ) -
      (Real.smoothTransition ∘ fun y => (y - a) / ℓ) *
        (fun y => (deriv Real.smoothTransition ∘ fun y => (b - y) / ℓ) y / ℓ) := by
    funext y; rfl
  rw [hf]
  refine h.congr_deriv ?_
  simp only [smoothPlateauDeriv2, Function.comp_apply]
  ring

/-- `|φ'|` is at most the sum of the two (nonnegative) transition slopes. -/
theorem abs_smoothPlateauDeriv_le (hℓ : 0 < ℓ) (x : ℝ) :
    |smoothPlateauDeriv a b ℓ x| ≤
      deriv Real.smoothTransition ((x - a) / ℓ) / ℓ +
        deriv Real.smoothTransition ((b - x) / ℓ) / ℓ := by
  have p1 := deriv_smoothTransition_nonneg ((x - a) / ℓ)
  have p2 := deriv_smoothTransition_nonneg ((b - x) / ℓ)
  have q1 : 0 ≤ deriv Real.smoothTransition ((x - a) / ℓ) / ℓ := div_nonneg p1 hℓ.le
  have q2 : 0 ≤ deriv Real.smoothTransition ((b - x) / ℓ) / ℓ := div_nonneg p2 hℓ.le
  have s1 := Real.smoothTransition.nonneg ((x - a) / ℓ)
  have s1' := Real.smoothTransition.le_one ((x - a) / ℓ)
  have s2 := Real.smoothTransition.nonneg ((b - x) / ℓ)
  have s2' := Real.smoothTransition.le_one ((b - x) / ℓ)
  rw [smoothPlateauDeriv, abs_le]
  constructor <;> nlinarith

/-- **Total variation of a plateau.**  `∫_u^v |φ'| ≤ 2` on every interval. -/
theorem integral_abs_smoothPlateauDeriv_le (hℓ : 0 < ℓ) {u v : ℝ} (huv : u ≤ v) :
    ∫ x in u..v, |smoothPlateauDeriv a b ℓ x| ≤ 2 := by
  have hc1 : Continuous fun x => deriv Real.smoothTransition ((x - a) / ℓ) / ℓ :=
    (continuous_deriv_smoothTransition.comp (by fun_prop)).div_const ℓ
  have hc2 : Continuous fun x => deriv Real.smoothTransition ((b - x) / ℓ) / ℓ :=
    (continuous_deriv_smoothTransition.comp (by fun_prop)).div_const ℓ
  have hmono : ∫ x in u..v, |smoothPlateauDeriv a b ℓ x| ≤
      ∫ x in u..v, (deriv Real.smoothTransition ((x - a) / ℓ) / ℓ +
        deriv Real.smoothTransition ((b - x) / ℓ) / ℓ) :=
    integral_mono_on huv (continuous_smoothPlateauDeriv.abs.intervalIntegrable _ _)
      ((hc1.add hc2).intervalIntegrable _ _) fun x _ => abs_smoothPlateauDeriv_le hℓ x
  have hF1 : ∀ x ∈ uIcc u v, HasDerivAt (fun y => Real.smoothTransition ((y - a) / ℓ))
      (deriv Real.smoothTransition ((x - a) / ℓ) / ℓ) x := by
    intro x _
    refine ((hasDerivAt_smoothTransition ((x - a) / ℓ)).comp x
      (hasDerivAt_left ℓ a x)).congr_deriv ?_
    ring
  have hF2 : ∀ x ∈ uIcc u v, HasDerivAt (fun y => -Real.smoothTransition ((b - y) / ℓ))
      (deriv Real.smoothTransition ((b - x) / ℓ) / ℓ) x := by
    intro x _
    refine ((hasDerivAt_smoothTransition ((b - x) / ℓ)).comp x
      (hasDerivAt_right ℓ b x)).neg.congr_deriv ?_
    ring
  rw [integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    integral_eq_sub_of_hasDerivAt hF1 (hc1.intervalIntegrable _ _),
    integral_eq_sub_of_hasDerivAt hF2 (hc2.intervalIntegrable _ _)] at hmono
  have := Real.smoothTransition.le_one ((v - a) / ℓ)
  have := Real.smoothTransition.nonneg ((u - a) / ℓ)
  have := Real.smoothTransition.le_one ((b - u) / ℓ)
  have := Real.smoothTransition.nonneg ((b - v) / ℓ)
  linarith

/-- **Uniform slope bound.**  `|φ'| ≤ K₁/ℓ` with `K₁` absolute. -/
theorem exists_abs_smoothPlateauDeriv_le :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ a b ℓ x : ℝ, 0 < ℓ → |smoothPlateauDeriv a b ℓ x| ≤ K₁ / ℓ := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_bound_deriv_smoothTransition
  refine ⟨2 * Λ, by positivity, fun a b ℓ x hℓ => ?_⟩
  refine le_trans (abs_smoothPlateauDeriv_le hℓ x) ?_
  have e1 := le_trans (le_abs_self _) (hΛ ((x - a) / ℓ))
  have e2 := le_trans (le_abs_self _) (hΛ ((b - x) / ℓ))
  rw [← add_div, mul_comm]
  exact div_le_div_of_nonneg_right (by linarith) hℓ.le

/-- **Uniform curvature bound.**  `|φ''| ≤ K₂/ℓ²` with `K₂` absolute. -/
theorem exists_abs_smoothPlateauDeriv2_le :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ a b ℓ x : ℝ, 0 < ℓ → |smoothPlateauDeriv2 a b ℓ x| ≤ K₂ / ℓ ^ 2 := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_bound_deriv_smoothTransition
  obtain ⟨Λ₂, hΛ₂0, hΛ₂⟩ := exists_bound_deriv_deriv_smoothTransition
  refine ⟨2 * Λ₂ + 2 * Λ ^ 2, by positivity, fun a b ℓ x hℓ => ?_⟩
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have key : smoothPlateauDeriv2 a b ℓ x * ℓ ^ 2 =
      deriv (deriv Real.smoothTransition) ((x - a) / ℓ) * Real.smoothTransition ((b - x) / ℓ) -
        2 * deriv Real.smoothTransition ((x - a) / ℓ) * deriv Real.smoothTransition ((b - x) / ℓ) +
        Real.smoothTransition ((x - a) / ℓ) * deriv (deriv Real.smoothTransition) ((b - x) / ℓ) := by
    simp only [smoothPlateauDeriv2]
    field_simp
  generalize (x - a) / ℓ = p at key
  generalize (b - x) / ℓ = q at key
  have e1 := hΛ p
  have e2 := hΛ q
  have f1 := hΛ₂ p
  have f2 := hΛ₂ q
  have s1 := Real.smoothTransition.nonneg p
  have s1' := Real.smoothTransition.le_one p
  have s2 := Real.smoothTransition.nonneg q
  have s2' := Real.smoothTransition.le_one q
  have hb : |smoothPlateauDeriv2 a b ℓ x * ℓ ^ 2| ≤ 2 * Λ₂ + 2 * Λ ^ 2 := by
    rw [key]
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add (abs_sub _ _) le_rfl) ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg s1, abs_of_nonneg s2,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have : |deriv Real.smoothTransition p| * |deriv Real.smoothTransition q| ≤ Λ * Λ :=
      mul_le_mul e1 e2 (abs_nonneg _) hΛ0
    nlinarith [abs_nonneg (deriv (deriv Real.smoothTransition) p),
      abs_nonneg (deriv (deriv Real.smoothTransition) q)]
  rw [abs_mul, abs_of_pos hℓ2] at hb
  rw [le_div_iff₀ hℓ2]
  exact hb

/-- The slope vanishes strictly left of the plateau. -/
theorem smoothPlateauDeriv_eq_zero_of_lt (hℓ : 0 < ℓ) {x : ℝ} (hx : x < a) :
    smoothPlateauDeriv a b ℓ x = 0 := by
  have hp : (x - a) / ℓ < 0 := div_neg_of_neg_of_pos (by linarith) hℓ
  rw [smoothPlateauDeriv, deriv_smoothTransition_eq_zero_of_notMem (fun h => by linarith [h.1]),
    Real.smoothTransition.zero_of_nonpos hp.le]
  ring

/-- The slope vanishes strictly right of the plateau. -/
theorem smoothPlateauDeriv_eq_zero_of_gt (hℓ : 0 < ℓ) {x : ℝ} (hx : b < x) :
    smoothPlateauDeriv a b ℓ x = 0 := by
  have hp : (b - x) / ℓ < 0 := div_neg_of_neg_of_pos (by linarith) hℓ
  rw [smoothPlateauDeriv, deriv_smoothTransition_eq_zero_of_notMem (x := (b - x) / ℓ)
    (fun h => by linarith [h.1]), Real.smoothTransition.zero_of_nonpos hp.le]
  ring

/-- A dilated plateau is a plateau. -/
theorem smoothPlateau_div (X : ℝ) (hX : 0 < X) (x : ℝ) :
    smoothPlateau a b ℓ (x / X) = smoothPlateau (a * X) (b * X) (ℓ * X) x := by
  unfold smoothPlateau
  congr 2 <;> field_simp

end

end GaloisForLFunctions.HTGeometry
