import GaloisForLFunctions.HTGeometry.PauliEdgeBlockNorms
import GaloisForLFunctions.HTGeometry.ContinuousCircuitMetricEntropyLaw
import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-! # Restricted operator error from diagonal unitary measurements -/

open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Orthogonal projection onto the designated coordinate subspace. -/
def coordinateProjection (R : Finset I) : Mat I := diagonal fun j => if j∈R then 1 else 0

theorem projection_norm_le [Nonempty I] (R : Finset I) : ‖coordinateProjection R‖ ≤ 1 := by
  rw [coordinateProjection,Matrix.l2_opNorm_diagonal,pi_norm_le_iff_of_nonempty]
  intro j
  by_cases hj : j∈R <;> simp [hj]

omit [DecidableEq I] in
private theorem gramColumn (M : Mat I) (j : I) : ∑ i, ‖M i j‖^2=((Mᴴ*M) j j).re := by
  rw [Matrix.mul_apply,Complex.re_sum]
  apply sum_congr rfl
  intro i _
  rw [conjTranspose_apply,Complex.star_def,Complex.conj_mul',←Complex.ofReal_pow,Complex.ofReal_re]

/-- A diagonal test on each selected vector controls every superposition of
those vectors. The squared error costs twice the sum of the scalar errors. -/
theorem restricted_norm_sq (R : Finset I) [Nonempty I] (A : Mat I) (hA : A∈unitary _)
    (z : I → ℂ) (hz : ∀ j, ‖z j‖=1) :
    ‖(A-diagonal z)*coordinateProjection R‖^2 ≤ 2*∑ j ∈ R, ‖A j j-z j‖ := by
  let D := diagonal z
  let M := A-D
  let W := M*coordinateProjection R
  have hD := StaticLocalLaboratoryComplexityGrowthLaw.mem_unitaryGroup_diagonal_general z hz
  have hx : Aᴴ*A=1 := (Unitary.mem_iff.mp hA).1
  have hy : Dᴴ*D=1 := (Unitary.mem_iff.mp hD).1
  have he : Mᴴ*M=1+1-(Dᴴ*A+(Dᴴ*A)ᴴ) := by
    simp only [M,conjTranspose_sub,conjTranspose_mul,conjTranspose_conjTranspose,sub_mul,mul_sub,hx,hy]
    abel
  have hdiag (j : I) : ((Mᴴ*M) j j).re ≤ 2*‖A j j-z j‖ := by
    have hprod : star (z j)*z j=1 := by rw [Complex.star_def,Complex.conj_mul',hz]; norm_num
    have hh := Complex.re_le_norm (star (z j)*(z j-A j j))
    rw [norm_mul,norm_star,hz,one_mul,norm_sub_rev,mul_sub,hprod,Complex.sub_re,Complex.one_re] at hh
    rw [he]
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.one_apply_eq,Complex.sub_re,Complex.add_re,
      Complex.one_re,conjTranspose_apply,Complex.star_def,Complex.conj_re,
      D,Matrix.diagonal_conjTranspose,diagonal_mul,Pi.star_apply]
    simpa only [Complex.star_def] using (show 1+1-((star (z j)*A j j).re+(star (z j)*A j j).re) ≤
      2*‖A j j-z j‖ by linarith only [hh])
  have hs : hsNormSq W = ∑ j ∈ R, ((Mᴴ*M) j j).re := by
    unfold hsNormSq
    calc
      _ = ∑ j, if j∈R then ((Mᴴ*M) j j).re else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j∈R
        · simpa only [hj,if_true,W,coordinateProjection,mul_diagonal,mul_one] using gramColumn M j
        · simp only [W,coordinateProjection,mul_diagonal,if_neg hj,mul_zero,norm_zero,zero_pow (by decide : 2≠0),sum_const_zero]
      _ = _ := by rw [sum_ite_mem,univ_inter]
  have hn := sq_le_sq₀ (norm_nonneg W) (hsNorm_nonneg W) |>.mpr (l2_opNorm_le_hsNorm W)
  rw [hsNorm_sq,sum_comm] at hn
  change ‖W‖^2 ≤ hsNormSq W at hn
  rw [hs] at hn
  apply hn.trans
  rw [mul_sum]
  exact sum_le_sum fun j _ => hdiag j

#print axioms restricted_norm_sq
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
