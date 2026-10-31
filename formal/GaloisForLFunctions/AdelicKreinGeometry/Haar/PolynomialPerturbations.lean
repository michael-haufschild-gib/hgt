import GaloisForLFunctions.HeckeKreinToeplitz.Index.SubgroupColumns
import GaloisForLFunctions.BiarithmeticGeometry.Affine.PolynomialCoefficients
import GaloisForLFunctions.AdelicKreinGeometry.Haar.FiniteRankPerturbations
import GaloisForLFunctions.ArithmeticPositiveDuality.ArchimedeanEigenvectorsAreInvisibleToTranslations
import GaloisForLFunctions.HTGeometry.ConstitutiveNilpotentSocleLaw

/-!
# Negative index bounds the degree of zero-axis affine kernels

A nonzero Hermitian affine kernel vanishing on translations and dilations is polynomial on
each translation fibre. Its degree is strictly below its negative index: the translation
columns span a space of dimension at most that index, and their unipotent action has the
same bound on its nilpotence exponent.
-/

open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

private theorem zero_on_translation_kernel {k : AffineGroupQ → ℂ}
    (ht : ∀ b : ℚ, k (translation b) = 0) : ∀ g ∈ slopeUnit.ker, k g = 0 := by
  intro g hg
  change slopeUnit g = 1 at hg
  have he := congrArg (fun u : ℚˣ => (u : ℚ)) hg
  change affSlope g = 1 at he
  have hg' : g = translation (affShift g) :=
    affine_ext (by rw [affSlope_translation, he]) (affShift_translation _).symm
  rw [hg']
  exact ht _

/-- Negative index bounds the polynomial degree along every affine translation fibre. -/
theorem exists_polynomial_translation_fibre_lt_index {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hk0 : k ≠ 0) {r : ℕ} (hi : negIndex k ≤ r)
    (ht : ∀ b : ℚ, k (translation b) = 0) (hd : ∀ u : ℚˣ, k (dilation u) = 0)
    (u : ℚˣ) : ∃ P : Polynomial ℂ, P.natDegree < r ∧
      ∀ b : ℚ, k (translation b * dilation u) = P.eval (b : ℂ) := by
  let H := slopeUnit.ker
  obtain ⟨hfin, hdim⟩ := finite_kernelSubgroupColumnSpan hk hi H (zero_on_translation_kernel ht)
  letI := hfin
  letI := (finite_columnSpan_of_zero_axes hk hi ht hd).1
  have hm : 0 < Module.finrank ℂ (kernelSubgroupColumnSpan k H) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨kernelSubgroupVector k H, kernelSubgroupVector_ne_zero H hk0⟩
  let t (b : ℚ) : H := ⟨translation (b / (u : ℚ)), by
    change slopeUnit (translation (b / (u : ℚ))) = 1
    exact Units.ext (affSlope_translation _)⟩
  have ht0 : t 0 = 1 := by
    apply Subtype.ext
    change translation (0 / (u : ℚ)) = 1
    rw [zero_div, translation_zero]
  have htadd (a b : ℚ) : t (a + b) = t a * t b := by
    apply Subtype.ext
    change translation ((a + b) / (u : ℚ)) =
      translation (a / (u : ℚ)) * translation (b / (u : ℚ))
    rw [add_div, translation_add]
  let f (b : ℚ) := kernelSubgroupRepresentation k H (t b)
  have h0 : f 0 = 1 := by dsimp [f]; rw [ht0, map_one]
  have ha (a b : ℚ) : f (a + b) = f a * f b := by
    dsimp [f]
    rw [htadd, map_mul]
  have hnil (b : ℚ) :
      (f b - 1) ^ Module.finrank ℂ (kernelSubgroupColumnSpan k H) = 0 := by
    apply pow_finrank_eq_zero_of_isNilpotent
    apply isNilpotent_subgroup_sub_one k H (t b)
    exact ⟨Module.finrank ℂ (kernelColumnSpan k),
      finite_rational_affine_end_translation_unipotent (kernelColumnRepresentation k)
        (b / (u : ℚ))⟩
  let L : Module.End ℂ (kernelSubgroupColumnSpan k H) →ₗ[ℂ] ℂ :=
    { toFun := fun A => kernelSubgroupObservation k H (dilation u) (A (kernelSubgroupVector k H))
      map_add' A B := by rw [LinearMap.add_apply, map_add]
      map_smul' c A := by simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply] }
  let P := unipotentPowerPolynomial (Module.finrank ℂ (kernelSubgroupColumnSpan k H)) (f 1) L
  refine ⟨P, (unipotentPowerPolynomial_natDegree_lt _ hm _ _).trans_le hdim, fun b => ?_⟩
  have hp := unipotent_rational_coefficient _ f h0 ha hnil L b
  have hmul : (u : ℚ) * (b / (u : ℚ)) = b := by
    rw [div_eq_mul_inv]
    calc
      (u : ℚ) * (b * (u : ℚ)⁻¹) = ((u : ℚ) * (u : ℚ)⁻¹) * b := by ring
      _ = b := by rw [mul_inv_cancel₀ u.ne_zero, one_mul]
  have hg := translation_mul_dilation u (b / (u : ℚ))
  rw [hmul] at hg
  calc
    k (translation b * dilation u) = k (dilation u * translation (b / (u : ℚ))) :=
      congrArg k hg
    _ = L (f b) := (kernelSubgroupObservation_representation k H (dilation u) (t b)).symm
    _ = P.eval (b : ℂ) := hp.symm

#print axioms exists_polynomial_translation_fibre_lt_index
end GaloisForLFunctions.AdelicKreinGeometry
