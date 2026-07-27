import GaloisForLFunctions.HTGeometry.GammaCyclicSpectralMeasure

/-!
# The logarithmic tail integral of the Gamma cyclic density

The quadratic decay `ρ(x) ≤ ‖φ''‖₁/(4π²x²)` makes every logarithmic weight integrable against the
density away from the origin:

```text
∫_{|x| ≥ 3} (log(2|x|) + C)² ρ(x) dx < ∞ ,
```

because `log t ≤ 4 t^(1/4)` turns the weight into `(128 + 2C²)|x|^(1/2)` and the product with the
decay is the convergent tail `|x|^(-3/2)`.
-/

open MeasureTheory Set

namespace HTGeometry

noncomputable section

/-! ### The two-sided power tail -/

theorem setOf_three_le_abs : {x : ℝ | 3 ≤ |x|} = Set.Iic (-3) ∪ Set.Ici 3 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, le_abs]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl h

theorem integrableOn_abs_rpow_tail :
    IntegrableOn (fun x : ℝ => |x| ^ (-(3 / 2) : ℝ)) {x : ℝ | 3 ≤ |x|} := by
  have hpos : IntegrableOn (fun x : ℝ => |x| ^ (-(3 / 2) : ℝ)) (Set.Ici 3) := by
    have h := integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (by norm_num)
      (by norm_num : (0 : ℝ) < 3)
    refine (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi h).congr_fun ?_ measurableSet_Ici
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := by linarith [Set.mem_Ici.mp hx]
    show x ^ (-(3 / 2) : ℝ) = |x| ^ (-(3 / 2) : ℝ)
    rw [abs_of_nonneg hx0]
  have hneg : IntegrableOn (fun x : ℝ => |x| ^ (-(3 / 2) : ℝ)) (Set.Iic (-3)) := by
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' (Set.Ici 3) = Set.Iic (-3) := by
      ext x
      simp [le_neg]
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      measurableEmbedding_neg (f := fun x : ℝ => |x| ^ (-(3 / 2) : ℝ)) (s := Set.Ici 3)
    rw [hpre] at hmp
    refine (hmp.mpr hpos).congr_fun ?_ measurableSet_Iic
    intro x _
    simp [Function.comp]
  rw [setOf_three_le_abs]
  exact hneg.union hpos

/-! ### The logarithmic weight -/

theorem log_two_mul_abs_le {x : ℝ} (hx : 3 ≤ |x|) :
    Real.log (2 * |x|) ≤ 8 * |x| ^ (1 / 4 : ℝ) := by
  have hxpos : (0 : ℝ) < |x| := by linarith
  have h2 : (2 : ℝ) * |x| ≤ |x| * |x| := by nlinarith
  have hlog : Real.log (2 * |x|) ≤ Real.log (|x| * |x|) :=
    Real.log_le_log (by linarith) h2
  have hsplit : Real.log (|x| * |x|) = 2 * Real.log |x| := by
    rw [Real.log_mul (ne_of_gt hxpos) (ne_of_gt hxpos)]
    ring
  have hpow : Real.log |x| ≤ 4 * |x| ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div (abs_nonneg x) (by norm_num : (0 : ℝ) < 1 / 4)
    calc Real.log |x| ≤ |x| ^ (1 / 4 : ℝ) / (1 / 4) := h
      _ = 4 * |x| ^ (1 / 4 : ℝ) := by ring
  linarith [hlog, hsplit ▸ hlog]

theorem log_weight_le {C : ℝ} {x : ℝ} (hx : 3 ≤ |x|) :
    (Real.log (2 * |x|) + C) ^ 2 ≤ (128 + 2 * C ^ 2) * |x| ^ (1 / 2 : ℝ) := by
  have hxpos : (0 : ℝ) < |x| := by linarith
  have hlog := log_two_mul_abs_le hx
  have hlognn : (0 : ℝ) ≤ Real.log (2 * |x|) :=
    Real.log_nonneg (by linarith)
  have hquarter : (0 : ℝ) ≤ |x| ^ (1 / 4 : ℝ) := Real.rpow_nonneg (abs_nonneg x) _
  have hsq : (|x| ^ (1 / 4 : ℝ)) ^ 2 = |x| ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (|x| ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul (abs_nonneg x)]
    norm_num
  have hone : (1 : ℝ) ≤ |x| ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  calc (Real.log (2 * |x|) + C) ^ 2
      ≤ 2 * Real.log (2 * |x|) ^ 2 + 2 * C ^ 2 := by nlinarith [sq_nonneg (Real.log (2 * |x|) - C)]
    _ ≤ 2 * (8 * |x| ^ (1 / 4 : ℝ)) ^ 2 + 2 * C ^ 2 := by nlinarith
    _ = 128 * |x| ^ (1 / 2 : ℝ) + 2 * C ^ 2 := by
        rw [mul_pow, ← hsq]
        ring
    _ ≤ (128 + 2 * C ^ 2) * |x| ^ (1 / 2 : ℝ) := by nlinarith [sq_nonneg C]

/-! ### The tail integral -/

/-- **The logarithmic tail integral of the density converges.** -/
theorem integrableOn_log_sq_mul_gammaCyclicDensity (C : ℝ) :
    IntegrableOn (fun x : ℝ => (Real.log (2 * |x|) + C) ^ 2 * gammaCyclicDensity x)
      {x : ℝ | 3 ≤ |x|} := by
  have hB : (0 : ℝ) ≤ ∫ t : ℝ, ‖coshHalfDeriv2 t‖ :=
    integral_nonneg fun t => norm_nonneg _
  have hπ : (0 : ℝ) < 4 * Real.pi ^ 2 := by
    have := Real.pi_pos
    positivity
  refine Integrable.mono' (g := fun x : ℝ =>
    ((128 + 2 * C ^ 2) * ((∫ t : ℝ, ‖coshHalfDeriv2 t‖) / (4 * Real.pi ^ 2))) *
      |x| ^ (-(3 / 2) : ℝ)) (integrableOn_abs_rpow_tail.const_mul _) ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    refine Measurable.mul ?_ continuous_gammaCyclicDensity.measurable
    have habs : Measurable fun x : ℝ => 2 * |x| :=
      (continuous_const.mul continuous_abs).measurable
    exact ((Real.measurable_log.comp habs).add measurable_const).pow measurable_const
  · filter_upwards [ae_restrict_mem (measurableSet_le measurable_const continuous_abs.measurable)] with x hx
    have hx3 : 3 ≤ |x| := hx
    have hxpos : (0 : ℝ) < |x| := by linarith
    have hρ : gammaCyclicDensity x ≤ (∫ t : ℝ, ‖coshHalfDeriv2 t‖) / (4 * Real.pi ^ 2) *
        |x| ^ (-(2 : ℝ)) := by
      have hkey := gammaCyclicDensity_mul_sq_le x
      have hxsq : x ^ 2 = |x| ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
      have hxsqpos : (0 : ℝ) < |x| ^ (2 : ℝ) := Real.rpow_pos_of_pos hxpos _
      have hinv : |x| ^ (-(2 : ℝ)) = (|x| ^ (2 : ℝ))⁻¹ := by
        rw [Real.rpow_neg (abs_nonneg x)]
      rw [hxsq] at hkey
      rw [hinv, ← div_eq_mul_inv, le_div_iff₀ hxsqpos, le_div_iff₀ hπ]
      nlinarith [hkey]
    have hweight := log_weight_le (C := C) hx3
    have hwnn : (0 : ℝ) ≤ (Real.log (2 * |x|) + C) ^ 2 := sq_nonneg _
    have hρnn : (0 : ℝ) ≤ gammaCyclicDensity x := gammaCyclicDensity_nonneg x
    have hmulrpow : |x| ^ (1 / 2 : ℝ) * |x| ^ (-(2 : ℝ)) = |x| ^ (-(3 / 2) : ℝ) := by
      rw [← Real.rpow_add hxpos]
      norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (Real.log (2 * |x|) + C) ^ 2 * gammaCyclicDensity x
        ≤ ((128 + 2 * C ^ 2) * |x| ^ (1 / 2 : ℝ)) *
          ((∫ t : ℝ, ‖coshHalfDeriv2 t‖) / (4 * Real.pi ^ 2) * |x| ^ (-(2 : ℝ))) := by
          refine mul_le_mul hweight hρ hρnn ?_
          have : (0 : ℝ) ≤ |x| ^ (1 / 2 : ℝ) := Real.rpow_nonneg (abs_nonneg x) _
          nlinarith [sq_nonneg C]
      _ = ((128 + 2 * C ^ 2) * ((∫ t : ℝ, ‖coshHalfDeriv2 t‖) / (4 * Real.pi ^ 2))) *
          (|x| ^ (1 / 2 : ℝ) * |x| ^ (-(2 : ℝ))) := by ring
      _ = ((128 + 2 * C ^ 2) * ((∫ t : ℝ, ‖coshHalfDeriv2 t‖) / (4 * Real.pi ^ 2))) *
          |x| ^ (-(3 / 2) : ℝ) := by rw [hmulrpow]

end

end HTGeometry
