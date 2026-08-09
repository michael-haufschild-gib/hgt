import Mathlib

/-!
# A product box of Gaussian coordinates has an explicit probability floor

On `[-2,2]` the standard Gaussian density is bounded below by an explicit constant, so an interval
inside that range has probability at least the constant times its length.  Independent coordinates
multiply, so a product box centred within `[-1,1]` and of half-width at most one has probability at
least the corresponding power.

The bound is explicit and needs no asymptotics: it is the density floor times the side length,
raised to the number of coordinates.
-/

open ProbabilityTheory MeasureTheory

noncomputable section

namespace HTGeometry

/-- The floor of the standard Gaussian density on `[-2,2]`. -/
def gaussianFloorConstant : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-2)

theorem gaussianFloorConstant_pos : 0 < gaussianFloorConstant := by
  unfold gaussianFloorConstant
  have : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- **The standard Gaussian density is bounded below on `[-2,2]`.** -/
theorem gaussianFloorConstant_le_gaussianPDFReal {x : ℝ} (hx : |x| ≤ 2) :
    gaussianFloorConstant ≤ gaussianPDFReal 0 1 x := by
  rw [gaussianPDFReal, gaussianFloorConstant]
  simp only [NNReal.coe_one, mul_one]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.exp_le_exp.mpr ?_
  have hx2 : x ^ 2 ≤ 4 := by
    have := abs_le.mp hx
    nlinarith [this.1, this.2]
  rw [sub_zero]
  nlinarith

/-- **An interval inside `[-2,2]` carries at least the floor times its length.** -/
theorem gaussianReal_Icc_ge {a b : ℝ} (ha : -2 ≤ a) (hb : b ≤ 2) :
    ENNReal.ofReal (gaussianFloorConstant * (b - a)) ≤ gaussianReal 0 1 (Set.Icc a b) := by
  rw [gaussianReal_apply _ one_ne_zero]
  have hle : ∀ x ∈ Set.Icc a b,
      ENNReal.ofReal gaussianFloorConstant ≤ gaussianPDF 0 1 x := by
    intro x hx
    rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal (gaussianFloorConstant_le_gaussianPDFReal ?_)
    rw [abs_le]
    exact ⟨le_trans ha hx.1, le_trans hx.2 hb⟩
  calc ENNReal.ofReal (gaussianFloorConstant * (b - a))
      = ENNReal.ofReal gaussianFloorConstant * ENNReal.ofReal (b - a) :=
        ENNReal.ofReal_mul gaussianFloorConstant_pos.le
    _ = ENNReal.ofReal gaussianFloorConstant * volume (Set.Icc a b) := by
        rw [Real.volume_Icc]
    _ = ∫⁻ _ in Set.Icc a b, ENNReal.ofReal gaussianFloorConstant :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in Set.Icc a b, gaussianPDF 0 1 x :=
        setLIntegral_mono' measurableSet_Icc hle

/-- **A product box of independent Gaussian coordinates has an explicit floor.** -/
theorem measure_pi_box_ge {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, |c i| ≤ 1)
    (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) :
    ENNReal.ofReal ((gaussianFloorConstant * (2 * w)) ^ m)
      ≤ (Measure.pi fun _ : Fin m => gaussianReal 0 1)
          (Set.univ.pi fun i => Set.Icc (c i - w) (c i + w)) := by
  rw [Measure.pi_pi]
  have hterm : ∀ i : Fin m,
      ENNReal.ofReal (gaussianFloorConstant * (2 * w))
        ≤ gaussianReal 0 1 (Set.Icc (c i - w) (c i + w)) := by
    intro i
    have hci := abs_le.mp (hc i)
    have h := gaussianReal_Icc_ge (a := c i - w) (b := c i + w)
      (by linarith [hci.1]) (by linarith [hci.2])
    calc ENNReal.ofReal (gaussianFloorConstant * (2 * w))
        = ENNReal.ofReal (gaussianFloorConstant * ((c i + w) - (c i - w))) := by ring_nf
      _ ≤ _ := h
  calc ENNReal.ofReal ((gaussianFloorConstant * (2 * w)) ^ m)
      = ∏ _i : Fin m, ENNReal.ofReal (gaussianFloorConstant * (2 * w)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← ENNReal.ofReal_pow (mul_nonneg gaussianFloorConstant_pos.le (by positivity))]
    _ ≤ ∏ i : Fin m, gaussianReal 0 1 (Set.Icc (c i - w) (c i + w)) :=
        Finset.prod_le_prod' fun i _ => hterm i

/-- **The Gaussian product-box floor at half-width `ε²/(16m)`.**  Every centre inside `[-1,1]`
carries probability at least `(c₀ ε² / (8m))^m`. -/
theorem gaussianBox_prob_ge {m : ℕ} (hm : 0 < m) (c : Fin m → ℝ) (hc : ∀ i, |c i| ≤ 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ENNReal.ofReal ((gaussianFloorConstant * ε ^ 2 / (8 * m)) ^ m)
      ≤ (Measure.pi fun _ : Fin m => gaussianReal 0 1)
          (Set.univ.pi fun i =>
            Set.Icc (c i - ε ^ 2 / (16 * m)) (c i + ε ^ 2 / (16 * m))) := by
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hw : 0 < ε ^ 2 / (16 * m) := by positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hw1 : ε ^ 2 / (16 * m) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [hm1, hε0, hε1]
  have h := measure_pi_box_ge c hc (ε ^ 2 / (16 * m)) hw hw1
  refine le_trans (le_of_eq ?_) h
  congr 1
  congr 1
  field_simp
  ring

end HTGeometry

end
