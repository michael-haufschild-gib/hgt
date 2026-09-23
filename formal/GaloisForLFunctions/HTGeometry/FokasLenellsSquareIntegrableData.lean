import GaloisForLFunctions.HTGeometry.FokasLenellsScatteringDecay
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Square-integrable regularized Fokas–Lenells jump data

The established reciprocal scattering envelope is square integrable by
Japanese-bracket integrability. Both actual regularized reflection
coefficients therefore belong to L² for every explicitly normalized Schwartz
potential. Their prescribed singular time phases preserve this property.
Uniform boundedness controls the product entry, so every entry of the exact
regularized jump perturbation `R = jump - I` supplies valid L² forcing.
This closes the forcing-space prerequisite of the constructed Cauchy inverse;
weighted Sobolev regularity and nonlinear reconstruction are separate steps.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The reciprocal envelope is square integrable, by the corpus's Japanese-bracket integrability theorem. -/
theorem reciprocalEnvelope_memLp (C : ℝ) :
    MemLp (fun z : ℝ => C/(1+|z|)) 2 volume := by
  have hc : Continuous (fun z : ℝ => C/(1+|z|)) :=
    continuous_const.div (continuous_const.add continuous_abs) (fun z => by positivity)
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  have hi : Integrable (fun z : ℝ => (1+‖z‖)^(-(2:ℝ))) volume :=
    integrable_one_add_norm (by simp)
  have he : (fun z : ℝ => (C/(1+|z|))^(2 : ℕ)) = fun z : ℝ => C^(2 : ℕ)*(1+‖z‖)^(-(2:ℝ)) := by
    funext z
    simp [Real.norm_eq_abs, Real.rpow_neg (by positivity : 0 ≤ 1+|z|), mul_pow, inv_pow, div_eq_mul_inv]
  rw [he]
  exact hi.const_mul (C^(2 : ℕ))

/-- Both actual regularized reflection coefficients are square integrable for every explicitly normalized Schwartz potential. -/
theorem globalSmall_regularReflection_memLp (q : SchwartzMap ℝ ℂ) :
    MemLp (regularReflectionCoefficient (globalSmallScatteringPotential q)) 2 volume ∧
    MemLp (regularReverseReflectionCoefficient (globalSmallScatteringPotential q)) 2 volume := by
  have hc := continuous_globalSmall_regularReflection q
  constructor
  · exact (reciprocalEnvelope_memLp (1/3+regularReflectionDecay q false)).mono' hc.1.aestronglyMeasurable
      (Eventually.of_forall (fun z => (globalSmall_regularReflection_reciprocal_bound q z).1))
  · exact (reciprocalEnvelope_memLp (1/3+regularReflectionDecay q true)).mono' hc.2.aestronglyMeasurable
      (Eventually.of_forall (fun z => (globalSmall_regularReflection_reciprocal_bound q z).2))

/-- The prescribed singular time phases preserve actual reflection-data square integrability. -/
theorem globalSmall_regularJump_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    MemLp (regularJumpReflection (globalSmallScatteringPotential q) t x) 2 volume ∧
    MemLp (regularJumpReverseReflection (globalSmallScatteringPotential q) t x) 2 volume := by
  have hm := measurable_globalSmall_regularJump q t x
  have hr := globalSmall_regularReflection_memLp q
  exact ⟨hr.1.congr_norm hm.1.aestronglyMeasurable (Eventually.of_forall (fun z => (regularJumpReflection_norms _ t x z).1.symm)),
    hr.2.congr_norm hm.2.aestronglyMeasurable (Eventually.of_forall (fun z => (regularJumpReflection_norms _ t x z).2.symm))⟩

/-- The nonlinear product entry of the regularized jump is also in L² because the other factor is bounded. -/
theorem globalSmall_regularJump_product_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    MemLp (fun z => regularJumpReflection (globalSmallScatteringPotential q) t x z*
      regularJumpReverseReflection (globalSmallScatteringPotential q) t x z) 2 volume := by
  have hLp := ((globalSmall_regularJump_memLp q t x).1.norm).const_mul (1/3:ℝ)
  have hm := measurable_globalSmall_regularJump q t x
  apply hLp.mono' (hm.1.mul hm.2).aestronglyMeasurable
  filter_upwards with z
  simp only [Pi.mul_apply, norm_mul]
  have hb := (globalSmall_regularJump_bounds q t x z).2
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb
    (norm_nonneg (regularJumpReflection (globalSmallScatteringPotential q) t x z))

/-- Every entry of the exact regularized perturbation `R = jump - I` supplies valid L² forcing data. -/
theorem globalSmall_regularJump_sub_one_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    MemLp (fun z => (regularJump (globalSmallScatteringPotential q) t x z-
      (1 : Matrix (Fin 2) (Fin 2) ℂ)) i j) 2 volume := by
  fin_cases i <;> fin_cases j
  · simp [regularJump, jump]
  · simpa [regularJump, jump] using (globalSmall_regularJump_memLp q t x).2
  · have hm := (globalSmall_regularJump_memLp q t x).1.neg
    change MemLp (fun z => -regularJumpReflection (globalSmallScatteringPotential q) t x z) 2 volume at hm
    simpa [regularJump, jump] using hm
  · have hm := (globalSmall_regularJump_product_memLp q t x).neg
    change MemLp (fun z => -(regularJumpReflection (globalSmallScatteringPotential q) t x z*
      regularJumpReverseReflection (globalSmallScatteringPotential q) t x z)) 2 volume at hm
    simpa [regularJump, jump] using hm

/-- The whole jump has measurable entries for every prescribed time and position. -/
theorem measurable_globalSmall_regularJumpMatrix_entry (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    Measurable (fun z => regularJump (globalSmallScatteringPotential q) t x z i j) := by
  have hm := measurable_globalSmall_regularJump q t x
  fin_cases i <;> fin_cases j
  · exact measurable_const
  · exact hm.2
  · exact hm.1.neg
  · exact measurable_const.sub (hm.1.mul hm.2)

end
end GaloisForLFunctions.HTGeometry.FokasLenells
