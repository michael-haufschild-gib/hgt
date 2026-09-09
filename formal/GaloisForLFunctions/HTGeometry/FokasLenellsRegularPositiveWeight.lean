import GaloisForLFunctions.HTGeometry.FokasLenellsRegularOriginIntegrability
import GaloisForLFunctions.HTGeometry.FokasLenellsInverseFrequency

/-!
# Global positive-axis second-inverse-weight classification

The existing global first-inverse-frequency bound controls the tail after
one more division by z. The local origin classification therefore gives
an exact L^2 criterion on the entire positive squared spectral axis for
the actual globally small scattering data.
-/

open Complex Matrix MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The second inverse weight is one more division of the corpus's actual first-inverse data. -/
theorem regularSecondInverseReflection_globalSmall_eq (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) :
    regularSecondInverseReflection (globalSmallScatteringPotential q) reverse z =
      regularInverseFrequencyReflection q reverse z/(z : ℂ) := by
  cases reverse <;> simp only [regularSecondInverseReflection,regularInverseFrequencyReflection,
    Bool.false_eq_true,↓reduceIte,div_div,pow_two]

private theorem regular_second_inverse_tail (q : SchwartzMap ℝ ℂ) (reverse : Bool)
    (δ : ℝ) (hδ : 0 < δ) :
    MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) 2
      (volume.restrict (Ici δ)) := by
  have hfirst := (regularInverseFrequencyReflection_memLp q reverse).restrict (Ici δ)
  apply (hfirst.norm.const_mul (δ⁻¹)).mono'
    (regularSecondInverseReflection_measurable _ reverse).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
  have hzpos : 0 < z := lt_of_lt_of_le hδ hz
  rw [regularSecondInverseReflection_globalSmall_eq,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hzpos]
  exact (div_le_div_of_nonneg_left (norm_nonneg _) hδ hz).trans_eq (by ring)

private theorem regular_second_inverse_global_of_local (q : SchwartzMap ℝ ℂ) (reverse : Bool)
    (h : ∃ δ : ℝ, 0 < δ ∧ MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) 2
      (volume.restrict (Ioo 0 δ))) :
    MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) 2
      (volume.restrict (Ioi 0)) := by
  obtain ⟨δ,hδ,hlocal⟩ := h
  have htail := regular_second_inverse_tail q reverse δ hδ
  have hL := (memLp_indicator_iff_restrict measurableSet_Ioo).2 hlocal
  have hR := (memLp_indicator_iff_restrict measurableSet_Ici).2 htail
  have hsum := (hL.add hR).restrict (Ioi (0 : ℝ))
  apply MemLp.ae_eq ?_ hsum
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  change (Ioo 0 δ).indicator (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) z+
    (Ici δ).indicator (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) z = _
  by_cases hzd : z < δ
  · have hLz : z ∈ Ioo 0 δ := ⟨hz,hzd⟩
    have hRz : z ∉ Ici δ := not_le.mpr hzd
    simp [hLz,hRz]
  · have hLz : z ∉ Ioo 0 δ := fun h => hzd h.2
    have hRz : z ∈ Ici δ := le_of_not_gt hzd
    simp [hLz,hRz]

/-- The lower (-r2) coefficient always satisfies the second inverse weight on the entire positive axis. -/
theorem regularSecondInverseReflection_lower_globalSmall_positive_memLp (q : SchwartzMap ℝ ℂ) :
    MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) false) 2
      (volume.restrict (Ioi 0)) := by
  obtain ⟨δ,hδ,hW⟩ := regularSecondInverseReflection_lower_locally_memLp_all (globalSmallScatteringPotential q)
  exact regular_second_inverse_global_of_local q false ⟨δ,hδ,hW 2⟩

/-- The upper (r1) coefficient satisfies the full positive-axis weighted condition exactly at compatibility. -/
theorem regularSecondInverseReflection_upper_globalSmall_positive_memLp_iff (q : SchwartzMap ℝ ℂ) :
    MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) true) 2
      (volume.restrict (Ioi 0)) ↔ compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  constructor
  · intro h
    apply (regularSecondInverseReflection_upper_locally_memLp_two_iff _).1
    refine ⟨1,zero_lt_one,?_⟩
    exact MemLp.mono_measure (Measure.restrict_mono (fun _ hx => hx.1) le_rfl) h
  · intro hm
    exact regular_second_inverse_global_of_local q true
      ((regularSecondInverseReflection_upper_locally_memLp_two_iff _).2 hm)

/-- The explicit positive smallness scale gives the exact nonlinear balance for the global weighted criterion. -/
theorem regularSecondInverseReflection_upper_globalSmall_positive_iff_balance (q : SchwartzMap ℝ ℂ) :
    MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) true) 2
      (volume.restrict (Ioi 0)) ↔
      (∫ x : ℝ, q x) = I*(globalScatteringScale q : ℂ)^2*parityCoupling q := by
  rw [regularSecondInverseReflection_upper_globalSmall_positive_memLp_iff,
    ← rawReflection_isBigO_fifth_iff]
  exact rawReflection_globalSmall_isBigO_fifth_iff q

/-- Small Gaussian data fail the upper-channel weighted condition on the entire positive axis. -/
theorem regularSecondInverseReflection_upper_globalSmallGaussian_not_positive_memLp (a : ℝ) :
    ¬ MemLp (regularSecondInverseReflection (globalSmallScatteringPotential (compatibilityGaussian a)) true) 2
      (volume.restrict (Ioi 0)) := by
  rw [regularSecondInverseReflection_upper_globalSmall_positive_memLp_iff]
  exact compatibilityMoment_globalSmallGaussian_ne_zero a

/-- Therefore the upper-channel weighted claim on the full real line also fails for explicit small Gaussian data. -/
theorem regularSecondInverseReflection_upper_globalSmallGaussian_not_memLp (a : ℝ) :
    ¬ MemLp (regularSecondInverseReflection (globalSmallScatteringPotential (compatibilityGaussian a)) true) 2 volume := by
  intro h
  exact regularSecondInverseReflection_upper_globalSmallGaussian_not_positive_memLp a (h.restrict (Ioi 0))

/-- The prescribed-fifth-trace compatible family satisfies the actual upper global positive-axis weighted condition. -/
theorem regularSecondInverseReflection_upper_globalSmall_quinticGaussianProfile_positive_memLp (a : ℝ) (c : ℂ) :
    MemLp (regularSecondInverseReflection (globalSmallScatteringPotential (quinticGaussianProfile a c)) true) 2
      (volume.restrict (Ioi 0)) :=
  (regularSecondInverseReflection_upper_globalSmall_positive_memLp_iff _).2
    (compatibilityMoment_globalSmall_quinticGaussianProfile a c)

end
end GaloisForLFunctions.HTGeometry.FokasLenells
