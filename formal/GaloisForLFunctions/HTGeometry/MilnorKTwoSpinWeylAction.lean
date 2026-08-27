import GaloisForLFunctions.HTGeometry.MilnorKTwoSignSpinEmbedding
import GaloisForLFunctions.HTGeometry.SteinbergTWTWeylKernel

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorSpinWeyl

open CliffordAlgebra

/-- Conjugation by a Spin element on the ambient Clifford algebra. -/
def spinConjugation (s : spinGroup spinQ) : Clifford ≃ₐ[ℝ] Clifford :=
  MulSemiringAction.toAlgEquiv ℝ _ (ConjAct.toConjAct (spinGroup.toUnits s))

/-- Conjugation restricted to the subspace of represented vectors. -/
def spinConjugationOnVectors (s : spinGroup spinQ) :
    LinearMap.range (CliffordAlgebra.ι spinQ) →ₗ[ℝ]
      LinearMap.range (CliffordAlgebra.ι spinQ) :=
  ((spinConjugation s).toLinearMap.domRestrict
    (LinearMap.range (CliffordAlgebra.ι spinQ))).codRestrict
      (LinearMap.range (CliffordAlgebra.ι spinQ)) (by
        rintro ⟨x, p, rfl⟩
        exact spinGroup.conjAct_smul_ι_mem_range_ι s.property p)

theorem spinConjugationOnVectors_apply_ι (s : spinGroup spinQ)
    (p : Fin 4 → ℝ) :
    (spinConjugationOnVectors s
      ⟨CliffordAlgebra.ι spinQ p, LinearMap.mem_range_self _ p⟩ : Clifford) =
      spinConjugation s (CliffordAlgebra.ι spinQ p) := rfl

theorem spinCliffordIota_injective :
    Function.Injective (CliffordAlgebra.ι spinQ) := by
  intro p q hpq
  apply (ExteriorAlgebra.ι_inj ℝ p q).mp
  simpa [CliffordAlgebra.equivExterior] using
    congrArg (CliffordAlgebra.equivExterior spinQ) hpq

def spinConjugationOnVectorsEquiv (s : spinGroup spinQ) :
    LinearMap.range (CliffordAlgebra.ι spinQ) ≃ₗ[ℝ]
      LinearMap.range (CliffordAlgebra.ι spinQ) :=
  { spinConjugationOnVectors s with
    invFun := spinConjugationOnVectors s⁻¹
    left_inv := by
      intro x
      apply Subtype.ext
      exact show spinConjugation s⁻¹ (spinConjugation s (x : Clifford)) = x by
        simp [spinConjugation]
    right_inv := by
      intro x
      apply Subtype.ext
      exact show spinConjugation s (spinConjugation s⁻¹ (x : Clifford)) = x by
        simp [spinConjugation] }

def spinCliffordIotaRangeEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ]
    LinearMap.range (CliffordAlgebra.ι spinQ) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι spinQ) spinCliffordIota_injective

/-- Concrete vector representation of one Spin element. -/
def spinVectorLinearEquiv (s : spinGroup spinQ) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  (spinCliffordIotaRangeEquiv.trans (spinConjugationOnVectorsEquiv s)).trans
    spinCliffordIotaRangeEquiv.symm

theorem spinCliffordIota_spinVectorLinearEquiv
    (s : spinGroup spinQ) (p : Fin 4 → ℝ) :
    CliffordAlgebra.ι spinQ (spinVectorLinearEquiv s p) =
      spinConjugation s (CliffordAlgebra.ι spinQ p) := by
  change (spinCliffordIotaRangeEquiv (spinVectorLinearEquiv s p) : Clifford) =
    spinConjugation s (CliffordAlgebra.ι spinQ p)
  simp [spinVectorLinearEquiv, spinCliffordIotaRangeEquiv,
    spinConjugationOnVectorsEquiv, spinConjugationOnVectors]

def spinVectorRepresentation :
    spinGroup spinQ →* ((Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) where
  toFun := spinVectorLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro p
    apply spinCliffordIota_injective
    rw [spinCliffordIota_spinVectorLinearEquiv]
    simp [spinConjugation]
  map_mul' s t := by
    apply LinearEquiv.ext
    intro p
    apply spinCliffordIota_injective
    rw [spinCliffordIota_spinVectorLinearEquiv]
    change spinConjugation (s * t) (CliffordAlgebra.ι spinQ p) =
      CliffordAlgebra.ι spinQ ((spinVectorLinearEquiv s * spinVectorLinearEquiv t) p)
    rw [LinearEquiv.mul_apply]
    rw [spinCliffordIota_spinVectorLinearEquiv,
      spinCliffordIota_spinVectorLinearEquiv]
    simp [spinConjugation]
    exact mul_smul _ _ _

theorem smul_outer (c : ℝ) (x y z : Clifford) :
    (c • x) * y * (c • z) = (c * c) • (x * y * z) := by
  rw [smul_mul_assoc, smul_mul_smul]

theorem rotor_conj_of_anti (B E : Clifford)
    (hB2 : B * B = -1) (hBE : B * E = -(E * B)) :
    (B - 1) * E * (-B - 1) = 2 • (E * B) := by
  have hBEB : B * E * B = E := by
    calc
      B * E * B = -(E * B) * B := by rw [hBE]
      _ = -E * (B * B) := by noncomm_ring
      _ = E := by rw [hB2]; simp
  calc
    (B - 1) * E * (-B - 1) =
        -(B * E * B) - B * E + E * B + E := by noncomm_ring
    _ = 2 • (E * B) := by rw [hBEB, hBE]; module

theorem rotor_conj_of_comm (B E : Clifford)
    (hB2 : B * B = -1) (hBE : B * E = E * B) :
    (B - 1) * E * (-B - 1) = 2 • E := by
  have hBEB : B * E * B = -E := by
    calc
      B * E * B = E * (B * B) := by rw [hBE]; noncomm_ring
      _ = -E := by rw [hB2]; simp
  calc
    (B - 1) * E * (-B - 1) =
        -(B * E * B) - B * E + E * B + E := by noncomm_ring
    _ = 2 • E := by rw [hBEB, hBE]; module

theorem bivector_mul_basis_left_anti (i j : Fin 4) (hij : i ≠ j) :
    bivector i j * basisClifford i = -(basisClifford i * bivector i j) := by
  calc
    bivector i j * basisClifford i =
        basisClifford i * (basisClifford j * basisClifford i) := by
      simp [bivector, mul_assoc]
    _ = basisClifford i * (-(basisClifford i * basisClifford j)) := by
      rw [basisClifford_anti j i (Ne.symm hij)]
    _ = -(basisClifford i * bivector i j) := by
      simp only [bivector]
      rw [show basisClifford i * (-(basisClifford i * basisClifford j)) =
          -(basisClifford i * basisClifford i) * basisClifford j by noncomm_ring,
        basisClifford_sq]
      rw [← mul_assoc, basisClifford_sq]
      simp

theorem bivector_mul_basis_right_anti (i j : Fin 4) (hij : i ≠ j) :
    bivector i j * basisClifford j = -(basisClifford j * bivector i j) := by
  calc
    bivector i j * basisClifford j =
        basisClifford i * (basisClifford j * basisClifford j) := by
      simp [bivector, mul_assoc]
    _ = -basisClifford i := by rw [basisClifford_sq]; simp
    _ = -(basisClifford j * bivector i j) := by
      rw [show basisClifford j * bivector i j = basisClifford i by
        calc
          basisClifford j * bivector i j =
              (basisClifford j * basisClifford i) * basisClifford j := by
            simp [bivector, mul_assoc]
          _ = -(basisClifford i * basisClifford j) * basisClifford j := by
            rw [basisClifford_anti j i (Ne.symm hij)]
          _ = basisClifford i := by
            rw [show -(basisClifford i * basisClifford j) * basisClifford j =
                -basisClifford i * (basisClifford j * basisClifford j) by noncomm_ring,
              basisClifford_sq]
            simp]

theorem basis_left_mul_bivector (i j : Fin 4) :
    basisClifford i * bivector i j = -basisClifford j := by
  simp [bivector, ← mul_assoc]

theorem basis_right_mul_bivector (i j : Fin 4) (hij : i ≠ j) :
    basisClifford j * bivector i j = basisClifford i := by
  calc
    basisClifford j * bivector i j =
        (basisClifford j * basisClifford i) * basisClifford j := by
      simp [bivector, mul_assoc]
    _ = -(basisClifford i * basisClifford j) * basisClifford j := by
      rw [basisClifford_anti j i (Ne.symm hij)]
    _ = basisClifford i := by
      rw [show -(basisClifford i * basisClifford j) * basisClifford j =
          -basisClifford i * (basisClifford j * basisClifford j) by noncomm_ring,
        basisClifford_sq]
      simp

theorem bivector_mul_basis_comm (i j k : Fin 4)
    (hik : i ≠ k) (hjk : j ≠ k) :
    bivector i j * basisClifford k = basisClifford k * bivector i j := by
  calc
    bivector i j * basisClifford k =
        basisClifford i * (basisClifford j * basisClifford k) := by
      simp [bivector, mul_assoc]
    _ = basisClifford i * (-(basisClifford k * basisClifford j)) := by
      rw [basisClifford_anti j k hjk]
    _ = -(basisClifford i * basisClifford k) * basisClifford j := by
      noncomm_ring
    _ = basisClifford k * basisClifford i * basisClifford j := by
      rw [basisClifford_anti i k hik]
      noncomm_ring
    _ = basisClifford k * bivector i j := by simp [bivector, mul_assoc]

theorem weylLift_conj_basis_left (i j : Fin 4) (hij : i ≠ j) :
    ((weylLift i j hij : spinGroup spinQ) : Clifford) * basisClifford i *
        (((weylLift i j hij)⁻¹ : spinGroup spinQ) : Clifford) =
      -basisClifford j := by
  rw [← weylLift_reverse i j hij]
  change weylLiftVal i j * basisClifford i * weylLiftVal j i = _
  rw [weylLiftVal_formula, weylLiftVal_formula, bivector_reverse i j hij,
    smul_outer, invSqrtTwo_mul_self]
  rw [rotor_conj_of_anti (bivector i j) (basisClifford i)
    (bivector_sq i j hij) (bivector_mul_basis_left_anti i j hij)]
  rw [basis_left_mul_bivector i j]
  module

theorem weylLift_conj_basis_right (i j : Fin 4) (hij : i ≠ j) :
    ((weylLift i j hij : spinGroup spinQ) : Clifford) * basisClifford j *
        (((weylLift i j hij)⁻¹ : spinGroup spinQ) : Clifford) =
      basisClifford i := by
  rw [← weylLift_reverse i j hij]
  change weylLiftVal i j * basisClifford j * weylLiftVal j i = _
  rw [weylLiftVal_formula, weylLiftVal_formula, bivector_reverse i j hij,
    smul_outer, invSqrtTwo_mul_self]
  rw [rotor_conj_of_anti (bivector i j) (basisClifford j)
    (bivector_sq i j hij) (bivector_mul_basis_right_anti i j hij)]
  rw [basis_right_mul_bivector i j hij]
  module

theorem weylLift_conj_basis_other (i j k : Fin 4) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) :
    ((weylLift i j hij : spinGroup spinQ) : Clifford) * basisClifford k *
        (((weylLift i j hij)⁻¹ : spinGroup spinQ) : Clifford) =
      basisClifford k := by
  rw [← weylLift_reverse i j hij]
  change weylLiftVal i j * basisClifford k * weylLiftVal j i = _
  rw [weylLiftVal_formula, weylLiftVal_formula, bivector_reverse i j hij,
    smul_outer, invSqrtTwo_mul_self]
  rw [rotor_conj_of_comm (bivector i j) (basisClifford k)
    (bivector_sq i j hij) (bivector_mul_basis_comm i j k (Ne.symm hki) (Ne.symm hkj))]
  module

def weylVectorAction (i j k : Fin 4) : Fin 4 → ℝ :=
  if k = i then -basisVector j else if k = j then basisVector i else basisVector k

theorem spinVectorLinearEquiv_weylLift_basis (i j : Fin 4) (hij : i ≠ j)
    (k : Fin 4) :
    spinVectorLinearEquiv (weylLift i j hij) (basisVector k) =
      weylVectorAction i j k := by
  apply spinCliffordIota_injective
  rw [spinCliffordIota_spinVectorLinearEquiv]
  simp only [spinConjugation, MulSemiringAction.toAlgEquiv_apply]
  rw [@ConjAct.units_smul_def, @ConjAct.ofConjAct_toConjAct]
  change ((weylLift i j hij : spinGroup spinQ) : Clifford) *
      basisClifford k *
      (((weylLift i j hij)⁻¹ : spinGroup spinQ) : Clifford) = _
  by_cases hki : k = i
  · subst k
    rw [weylLift_conj_basis_left]
    simp [weylVectorAction, basisClifford]
  · by_cases hkj : k = j
    · subst k
      rw [weylLift_conj_basis_right]
      simp [weylVectorAction, hki, basisClifford]
    · rw [weylLift_conj_basis_other i j k hij hki hkj]
      simp [weylVectorAction, hki, hkj, basisClifford]

end MilnorSpinWeyl
end GaloisForLFunctions.HTGeometry

end
