import GaloisForLFunctions.HilbertMetric.Bergman.DiskAreaSurjectivity
import GaloisForLFunctions.HilbertMetric.Bergman.DiskReproducingKernel

/-!
# Sharp Bergman interpolation at every disk point

A normalized reproducing vector is the unique minimum-area interpolant
for one prescribed value. Orthogonal decomposition gives the exact
excess area of every competitor. Surjectivity of the coefficient model
transfers the bound and its equality case to all holomorphic L² functions.
-/

open Complex MeasureTheory Metric
open scoped ComplexConjugate
namespace GaloisForLFunctions.HilbertMetric.Bergman
noncomputable section

private theorem boundaryFactor_pos (z : Point) : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := by
  nlinarith only [z.property, norm_nonneg (z : ℂ)]

/-- The normalized reproducing vector with the prescribed value. -/
def pointInterpolant (z : Point) (v : ℂ) : Disk :=
  ((((1 - ‖(z : ℂ)‖ ^ 2) ^ 2 : ℝ) : ℂ) * v) • kernel z

theorem pointInterpolant_value (z : Point) (v : ℂ) : diskFun (pointInterpolant z v) z = v := by
  have hr : (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 * ‖kernel z‖ ^ 2 = 1 := by
    rw [kernel_norm_sq]
    field_simp [(boundaryFactor_pos z).ne']
  have hc : ((((1 - ‖(z : ℂ)‖ ^ 2) ^ 2 : ℝ) : ℂ)) * (‖kernel z‖ : ℂ) ^ 2 = 1 := by
    exact_mod_cast hr
  rw [← inner_kernel, pointInterpolant, inner_smul_right, inner_self_eq_norm_sq_to_K]
  change ((((1 - ‖(z : ℂ)‖ ^ 2) ^ 2 : ℝ) : ℂ) * v) * (‖kernel z‖ : ℂ) ^ 2 = v
  rw [mul_right_comm, hc, one_mul]

/-- Exact norm of the minimum-norm interpolating vector. -/
theorem pointInterpolant_norm (z : Point) (v : ℂ) :
    ‖pointInterpolant z v‖ = (1 - ‖(z : ℂ)‖ ^ 2) * ‖v‖ := by
  rw [pointInterpolant, norm_smul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _), kernel_norm]
  field_simp [(boundaryFactor_pos z).ne']

private theorem pointInterpolant_orthogonal (z : Point) (a : Disk) :
    inner ℂ (pointInterpolant z (diskFun a z)) (a - pointInterpolant z (diskFun a z)) = 0 := by
  have he : inner ℂ (kernel z) (a - pointInterpolant z (diskFun a z)) = 0 := by
    rw [inner_sub_right, inner_kernel, inner_kernel, pointInterpolant_value, sub_self]
  change inner ℂ (((((1 - ‖(z : ℂ)‖ ^ 2) ^ 2 : ℝ) : ℂ) * diskFun a z) • kernel z)
    (a - pointInterpolant z (diskFun a z)) = 0
  rw [inner_smul_left, he, mul_zero]

/-- Every competitor splits into its unique interpolant and an orthogonal zero-value remainder. -/
theorem point_interpolation_pythagorean (z : Point) (a : Disk) :
    ‖a‖ ^ 2 = (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 * ‖diskFun a z‖ ^ 2 +
      ‖a - pointInterpolant z (diskFun a z)‖ ^ 2 := by
  have he : pointInterpolant z (diskFun a z) +
      (a - pointInterpolant z (diskFun a z)) = a := by abel
  have h := norm_add_sq (𝕜 := ℂ) (pointInterpolant z (diskFun a z))
    (a - pointInterpolant z (diskFun a z))
  simpa only [he, pointInterpolant_orthogonal, map_zero, mul_zero, add_zero,
    pointInterpolant_norm, mul_pow] using h

theorem point_interpolation_norm_bound (z : Point) (a : Disk) :
    (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 * ‖diskFun a z‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  rw [point_interpolation_pythagorean z a]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Equality in the sharp evaluation bound determines the entire coefficient vector. -/
theorem point_interpolation_norm_eq_iff (z : Point) (a : Disk) :
    ‖a‖ ^ 2 = (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 * ‖diskFun a z‖ ^ 2 ↔
      a = pointInterpolant z (diskFun a z) := by
  rw [point_interpolation_pythagorean z a]
  constructor
  · intro h
    have hz : ‖a - pointInterpolant z (diskFun a z)‖ = 0 := by
      nlinarith only [h, norm_nonneg (a - pointInterpolant z (diskFun a z))]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro h
    rw [sub_eq_zero.mpr h, norm_zero, zero_pow two_ne_zero, add_zero]

/-- Sharp area interpolation holds on the entire holomorphic L² disk class. -/
theorem holomorphic_point_area_bound {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hi : IntegrableOn (fun w => ‖f w‖ ^ 2) (ball (0 : ℂ) 1)) (z : Point) :
    Real.pi * (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 * ‖f z‖ ^ 2 ≤
      ∫ w in ball (0 : ℂ) 1, ‖f w‖ ^ 2 := by
  obtain ⟨a, ha, _, hn⟩ := exists_disk_coordinates hf hi
  rw [← hn, ← ha z z.property]
  have h := mul_le_mul_of_nonneg_left (point_interpolation_norm_bound z a) Real.pi_pos.le
  simpa only [mul_assoc] using h

/-- The sharp area bound has exactly one extremal holomorphic function on the disk. -/
theorem holomorphic_point_area_eq_iff {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hi : IntegrableOn (fun w => ‖f w‖ ^ 2) (ball (0 : ℂ) 1)) (z : Point) :
    (∫ w in ball (0 : ℂ) 1, ‖f w‖ ^ 2) =
        Real.pi * (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 * ‖f z‖ ^ 2 ↔
      ∀ w : ℂ, ‖w‖ < 1 → f w = diskFun (pointInterpolant z (f z)) w := by
  obtain ⟨a, ha, _, hn⟩ := exists_disk_coordinates hf hi
  have hvalue := ha z z.property
  have he : (∫ w in ball (0 : ℂ) 1, ‖f w‖ ^ 2) =
      Real.pi * (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 * ‖f z‖ ^ 2 ↔
      a = pointInterpolant z (f z) := by
    rw [← hn, mul_assoc, ← hvalue]
    constructor
    · intro h
      exact (point_interpolation_norm_eq_iff z a).mp (mul_left_cancel₀ Real.pi_ne_zero h)
    · intro h
      exact congrArg (fun r : ℝ => Real.pi * r) ((point_interpolation_norm_eq_iff z a).mpr h)
  rw [he]
  constructor
  · intro h w hw
    exact (ha w hw).symm.trans (congrArg (fun b : Disk => diskFun b w) h)
  · intro h
    apply (diskFun_eqOn_iff _ _).mp
    intro w hw
    exact (ha w hw).trans (h w hw)

#print axioms point_interpolation_pythagorean
#print axioms point_interpolation_norm_eq_iff
#print axioms holomorphic_point_area_bound
#print axioms holomorphic_point_area_eq_iff
end
end GaloisForLFunctions.HilbertMetric.Bergman
