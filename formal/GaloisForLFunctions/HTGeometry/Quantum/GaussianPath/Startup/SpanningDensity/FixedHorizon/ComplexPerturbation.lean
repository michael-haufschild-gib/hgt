import GaloisForLFunctions.HTGeometry.LieTrotterProduct
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw

/-! # Complex coupling perturbations with uniform control of the background -/
open Filter NormedSpace Topology
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
variable {A : Type*} [CStarAlgebra A] [NormOneClass A]

/-- A skew-adjoint summand makes no contribution to this exponential
norm bound. In each Lie–Trotter step its exponential is unitary. -/
theorem norm_exp_skew_add_le (X Y : A) (hX : X ∈ skewAdjoint A) :
    ‖exp (X+Y)‖ ≤ Real.exp ‖Y‖ := by
  apply le_of_tendsto (tendsto_pow_exp_smul_inv X Y).norm
  filter_upwards [eventually_gt_atTop 0] with n hn
  let t := (n:ℝ)⁻¹
  have ht : 0 ≤ t := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hu := NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hX)
  calc
    ‖(exp (t • X)*exp (t • Y))^n‖ ≤ ‖exp (t • X)*exp (t • Y)‖^n := norm_pow_le _ _
    _ = ‖exp (t • Y)‖^n := by rw [CStarRing.norm_mem_unitary_mul _ hu]
    _ ≤ (Real.exp ‖t • Y‖)^n := pow_le_pow_left₀ (norm_nonneg _) (norm_exp_le_exp_norm _) _
    _ = Real.exp ‖Y‖ := by
      rw [←Real.exp_nat_mul,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
      congr 1
      dsimp only [t]
      rw [←mul_assoc,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'),one_mul]

/-- For a complex coefficient multiplying one Hermitian interaction,
only its imaginary part can grow the propagator's norm. The estimate
is independent of the dimension and of the real background Hamiltonian. -/
theorem norm_complex_field_evolution (H P : A) (hH : IsSelfAdjoint H) (hP : IsSelfAdjoint P)
    (z : ℂ) (t : ℝ) :
    ‖exp (t • ((-Complex.I) • (H+z • P)))‖ ≤ Real.exp (|t|*|z.im|*‖P‖) := by
  let R := H+(z.re:ℂ) • P
  have hR : IsSelfAdjoint R := by
    change star (H+(z.re:ℂ) • P)=H+(z.re:ℂ) • P
    rw [star_add,star_smul,hH.star_eq,hP.star_eq,Complex.star_def,Complex.conj_ofReal]
  have hskew : t • ((-Complex.I) • R) ∈ skewAdjoint A := by
    apply skewAdjoint.smul_mem
    rw [skewAdjoint.mem_iff,star_smul,hR.star_eq]
    simp
  have hcoef : (-Complex.I)*z = (-Complex.I)*(z.re:ℂ)+(z.im:ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  have heq : t • ((-Complex.I) • (H+z • P)) =
      t • ((-Complex.I) • R)+t • ((z.im:ℂ) • P) := by
    dsimp only [R]
    simp only [smul_add,smul_smul,hcoef,add_smul,add_assoc]
  rw [heq]
  apply (norm_exp_skew_add_le _ _ hskew).trans_eq
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,mul_assoc]

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
