import GaloisForLFunctions.BiScaleUncertainty.TwoGridTraceData

/-!
# Arithmetic stability and the closed joint trace range

The reduced projection angle controls the signed cross energy. Removing shared
nodes gives a uniformly bounded inverse and closes the algebraic sum of ranges.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

theorem twoGrid_cross_bound (d e : ℕ) (v : TwoGridData d e) :
    |⟪coprimeExtension d v.1.1, coprimeExtension e v.1.2⟫| ≤
      Real.sqrt (coprimeAngleSquare d e) * twoGridMass d e v := by
  let x := coprimeExtension d v.1.1
  let y := coprimeExtension e v.1.2
  have hp : coprimeProjector d x = x := coprimeProjection_extension d _
  have hq : coprimeProjector e y = y := coprimeProjection_extension e _
  have hr : coprimeProjector (coprimeLcm d e) y = 0 := twoGridData_common_zero d e v
  have ht : reducedCoprimeProduct d e y = coprimeProjector d y := by
    simp only [reducedCoprimeProduct, sub_apply, mul_apply_eq_comp, hq, hr, sub_zero]
  have hi : ⟪x, y⟫ = ⟪x, reducedCoprimeProduct d e y⟫ := by
    rw [ht, ← coprimeProjector_adjoint d,
      ContinuousLinearMap.adjoint_inner_right, coprimeProjector_adjoint, hp]
  have hn : ‖x‖ * ‖y‖ ≤ twoGridMass d e v := by
    have hx := norm_sq_coprimeExtension d v.1.1
    have hy := norm_sq_coprimeExtension e v.1.2
    change ‖x‖ ^ 2 = _ at hx
    change ‖y‖ ^ 2 = _ at hy
    unfold twoGridMass
    nlinarith only [hx, hy, sq_nonneg (‖x‖ - ‖y‖)]
  change |⟪x, y⟫| ≤ _
  rw [hi]
  calc
    |⟪x, reducedCoprimeProduct d e y⟫| ≤ ‖x‖ * ‖reducedCoprimeProduct d e y‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖reducedCoprimeProduct d e‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left ((reducedCoprimeProduct d e).le_opNorm y) (norm_nonneg x)
    _ = Real.sqrt (coprimeAngleSquare d e) * (‖x‖ * ‖y‖) := by
      rw [norm_reducedCoprimeProduct]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)

/-- Both arithmetic stability constants hold for every actual joint datum. -/
theorem twoGridExtension_stability (d e : ℕ) (v : TwoGridData d e) :
    (2 - 2 * Real.sqrt (coprimeAngleSquare d e)) * twoGridMass d e v ≤
        ‖twoGridExtension d e v‖ ^ 2 ∧
      ‖twoGridExtension d e v‖ ^ 2 ≤
        (2 + 2 * Real.sqrt (coprimeAngleSquare d e)) * twoGridMass d e v := by
  have h := abs_le.mp (twoGrid_cross_bound d e v)
  rw [twoGridExtension_apply, norm_add_sq_real, norm_sq_coprimeExtension,
    norm_sq_coprimeExtension]
  unfold twoGridMass at *
  constructor <;> nlinarith only [h.1, h.2]

theorem coprimeAngleSqrt_le_three_quarters (d e : ℕ) :
    Real.sqrt (coprimeAngleSquare d e) ≤ 3 / 4 := by
  have hc : coprimeAngleSquare d e ≤ 1 / 2 := by
    unfold coprimeAngleSquare
    split_ifs <;> norm_num
  have hs := Real.sq_sqrt (coprimeAngleSquare_nonneg d e)
  have hn := Real.sqrt_nonneg (coprimeAngleSquare d e)
  nlinarith only [hc, hs, hn]

theorem twoGridExtension_lower_uniform (d e : ℕ) (v : TwoGridData d e) :
    (1 / 2 : ℝ) * twoGridMass d e v ≤ ‖twoGridExtension d e v‖ ^ 2 := by
  have h := (twoGridExtension_stability d e v).1
  have hc := coprimeAngleSqrt_le_three_quarters d e
  have hm := twoGridMass_nonneg d e v
  nlinarith only [h, hc, hm, mul_nonneg (by linarith only [hc] :
    0 ≤ 3 / 4 - Real.sqrt (coprimeAngleSquare d e)) hm]

theorem twoGridData_norm_sq_le_mass (d e : ℕ) (v : TwoGridData d e) :
    ‖v‖ ^ 2 ≤ twoGridMass d e v := by
  change (max ‖v.1.1‖ ‖v.1.2‖)^2 ≤ ‖v.1.1‖^2 + ‖v.1.2‖^2
  rcases le_total ‖v.1.1‖ ‖v.1.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith only [sq_nonneg ‖v.1.1‖]
  · rw [max_eq_left h]
    nlinarith only [sq_nonneg ‖v.1.2‖]

theorem twoGridExtension_antilipschitz (d e : ℕ) :
    AntilipschitzWith 2 (twoGridExtension d e) := by
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro v
  have h := twoGridExtension_lower_uniform d e v
  have hn := twoGridData_norm_sq_le_mass d e v
  norm_num only [NNReal.coe_ofNat]
  nlinarith only [h, hn, norm_nonneg v, norm_nonneg (twoGridExtension d e v)]

theorem twoGridExtension_injective (d e : ℕ) : Function.Injective (twoGridExtension d e) :=
  (twoGridExtension_antilipschitz d e).injective

theorem isClosed_range_twoGridExtension (d e : ℕ) :
    IsClosed (Set.range (twoGridExtension d e)) :=
  (twoGridExtension_antilipschitz d e).isClosed_range (twoGridExtension d e).uniformContinuous

theorem coprimeExtension_coefficients_lcm (d e : ℕ) (q : Velocity) :
    coprimeExtension d (coprimeCoefficients d
        (coprimeProjector (coprimeLcm d e) q)) =
      coprimeProjector (coprimeLcm d e) q := by
  rw [← coprimeProjection_eq_extension]
  exact congrArg (fun A : Velocity →L[ℝ] Velocity => A q) (coprimeProjector_mul_lcm d e)

theorem coprimeExtension_eraseCommon (d e : ℕ) (b : TraceData) :
    coprimeExtension e (twoGridEraseCommon d e b) =
      coprimeExtension e b - coprimeProjector (coprimeLcm d e) (coprimeExtension e b) := by
  unfold twoGridEraseCommon
  change coprimeExtensionL e (b - _) = _
  rw [map_sub, coprimeExtensionL_apply, coprimeExtensionL_apply, coprimeLcm_comm d e,
    coprimeExtension_coefficients_lcm]

/-- Every algebraic sum admits the canonical nonredundant joint data. -/
theorem range_twoGridExtension (d e : ℕ) :
    Set.range (twoGridExtension d e) =
      {q | ∃ a b : TraceData, coprimeExtension d a + coprimeExtension e b = q} := by
  ext q
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v.1.1, v.1.2, rfl⟩
  · rintro ⟨a, b, rfl⟩
    refine ⟨twoGridData d e (a + coprimeCoefficients d
      (coprimeProjector (coprimeLcm d e) (coprimeExtension e b))) b, ?_⟩
    rw [twoGridExtension_apply]
    change coprimeExtension d (a + _) + coprimeExtension e (twoGridEraseCommon d e b) = _
    rw [coprimeExtension_add, coprimeExtension_coefficients_lcm, coprimeExtension_eraseCommon]
    abel

/-- The sum of the two infinite tent ranges is closed, without a closure operation. -/
theorem isClosed_sum_coprimeExtension_ranges (d e : ℕ) :
    IsClosed {q | ∃ a b : TraceData, coprimeExtension d a + coprimeExtension e b = q} := by
  rw [← range_twoGridExtension]
  exact isClosed_range_twoGridExtension d e

/-- The sharp displacement from the single-grid energy constant two. -/
theorem two_mul_sqrt_coprimeAngleSquare (d e : ℕ) :
    2 * Real.sqrt (coprimeAngleSquare d e) =
      if 2 ≤ Nat.gcd (d + 2) (e + 2) then 0
      else if d = 0 ∨ e = 0 then Real.sqrt 2 else 1 := by
  unfold coprimeAngleSquare
  split_ifs
  · simp
  · have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [h, h2, Real.sqrt_nonneg (1 / 2), Real.sqrt_nonneg 2]
  · have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith only [h, Real.sqrt_nonneg (1 / 4)]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
