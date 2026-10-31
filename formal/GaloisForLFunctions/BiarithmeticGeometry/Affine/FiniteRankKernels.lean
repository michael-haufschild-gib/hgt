import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnRepresentation
import GaloisForLFunctions.BiarithmeticGeometry.Affine.PolynomialCoefficients

/-!
# Polynomial translation fibres of finite-rank affine kernels

The column space of a finite-rank affine kernel is a finite-dimensional cyclic module.
Unipotence of its rational translations makes every fixed-slope reading polynomial, with
degree below the column-space dimension. No Hermitian or continuity hypothesis is needed.
-/

open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry


/-- A nonzero finite-rank affine kernel is polynomial on every translation fibre. -/
theorem exists_polynomial_translation_fibre {k : AffineGroupQ → ℂ}
    [Module.Finite ℂ (kernelColumnSpan k)] (hk : k ≠ 0) (u : ℚˣ) :
    ∃ P : Polynomial ℂ, P.natDegree < Module.finrank ℂ (kernelColumnSpan k) ∧
      ∀ b : ℚ, k (translation b * dilation u) = P.eval (b : ℂ) := by
  have hv : kernelColumnVector k ≠ 0 := by
    intro h
    apply hk
    funext g
    have he := congrArg (fun f : kernelColumnSpan k => (f : AffineGroupQ → ℂ) g⁻¹) h
    change k ((g⁻¹)⁻¹ * 1) = 0 at he
    simpa only [inv_inv, mul_one, Pi.zero_apply] using he
  have hdim : 0 < Module.finrank ℂ (kernelColumnSpan k) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨kernelColumnVector k, hv⟩
  let ρ := kernelColumnRepresentation k
  let v := ρ (dilation u) (kernelColumnVector k)
  let L : Module.End ℂ (kernelColumnSpan k) →ₗ[ℂ] ℂ :=
    { toFun := fun A => kernelColumnObservation k (A v)
      map_add' A B := by rw [LinearMap.add_apply, map_add]
      map_smul' c A := by simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply] }
  obtain ⟨P, hP, he⟩ := exists_polynomial_affine_translation_coefficient ρ L hdim
  refine ⟨P, hP, fun b => ?_⟩
  rw [he]
  change k (translation b * dilation u) =
    kernelColumnObservation k (ρ (translation b) (ρ (dilation u) (kernelColumnVector k)))
  have hr : ρ (translation b * dilation u) (kernelColumnVector k) =
      ρ (translation b) (ρ (dilation u) (kernelColumnVector k)) := by rw [map_mul]; rfl
  rw [← hr]
  exact (kernelColumnObservation_representation k (translation b * dilation u)).symm

#print axioms exists_polynomial_translation_fibre
end GaloisForLFunctions.BiarithmeticGeometry
