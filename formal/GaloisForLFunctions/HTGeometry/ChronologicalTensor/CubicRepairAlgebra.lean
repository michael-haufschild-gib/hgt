import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspQuotient
import Mathlib.RingTheory.Ideal.Basic

/-!
# The complete lattice of intermediate observation repairs

The coefficient of the missing middle gap identifies intermediate algebras
between the actual cusp and its normalization with ideals of the first-mode
polynomial ring. Both directions and their order correspondence are proved.
Faithful evaluation keeps different repairs distinct as physical observations.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicRepairAlgebra (I : Ideal (Polynomial ℝ)) : Subalgebra ℝ (Polynomial (Polynomial ℝ)) where
  carrier := {P | P.coeff 1 ∈ I}
  algebraMap_mem' r := by
    change (Polynomial.C (Polynomial.C r)).coeff 1 ∈ I
    simp
  zero_mem' := by simp
  one_mem' := by simp [Polynomial.coeff_one]
  add_mem' {P Q} hP hQ := by
    change (P+Q).coeff 1 ∈ I
    rw [Polynomial.coeff_add]
    exact I.add_mem hP hQ
  mul_mem' {P Q} hP hQ := by
    change (P*Q).coeff 1 ∈ I
    rw [Polynomial.mul_coeff_one]
    exact I.add_mem (I.mul_mem_left (P.coeff 0) hQ) (I.mul_mem_right (Q.coeff 0) hP)

theorem cubicRepairAlgebra_mem (I : Ideal (Polynomial ℝ)) (P : Polynomial (Polynomial ℝ)) :
    P ∈ cubicRepairAlgebra I ↔ P.coeff 1 ∈ I := Iff.rfl

theorem cubicRepairAlgebra_contains (I : Ideal (Polynomial ℝ)) : cubicCuspAlgebra ≤ cubicRepairAlgebra I := by
  intro P hP
  change P.coeff 1 ∈ I
  rw [(cubicCuspAlgebra_mem P).mp hP]
  exact I.zero_mem

def cubicRepairIdeal (S : Ici cubicCuspAlgebra) : Ideal (Polynomial ℝ) where
  carrier := {p | Polynomial.C p*Polynomial.X ∈ S.val}
  zero_mem' := by simp
  add_mem' {p q} hp hq := by
    change Polynomial.C (p+q)*Polynomial.X ∈ S.val
    rw [map_add,add_mul]
    exact S.val.add_mem hp hq
  smul_mem' r p hp := by
    change Polynomial.C (r*p)*Polynomial.X ∈ S.val
    rw [map_mul,mul_assoc]
    exact S.val.mul_mem (S.property (cubicCuspAlgebra_constant r)) hp

theorem cubicRepairIdeal_mem (S : Ici cubicCuspAlgebra) (p : Polynomial ℝ) :
    p ∈ cubicRepairIdeal S ↔ Polynomial.C p*Polynomial.X ∈ S.val := Iff.rfl

theorem cubicRepairIdeal_leftInverse (I : Ideal (Polynomial ℝ)) :
    cubicRepairIdeal ⟨cubicRepairAlgebra I,cubicRepairAlgebra_contains I⟩=I := by
  ext p
  rw [cubicRepairIdeal_mem]
  change (Polynomial.C p*Polynomial.X).coeff 1 ∈ I ↔ p ∈ I
  rw [Polynomial.C_mul_X_eq_monomial,Polynomial.coeff_monomial_same]

theorem cubicRepairAlgebra_rightInverse (S : Ici cubicCuspAlgebra) :
    cubicRepairAlgebra (cubicRepairIdeal S)=S.val := by
  ext P
  rw [cubicRepairAlgebra_mem,cubicRepairIdeal_mem]
  constructor
  · intro h
    have hr := S.property (cubicCuspRemainder_mem P)
    have hsum := S.val.add_mem hr h
    rwa [← cubicCuspRemainder_decomposition] at hsum
  · intro h
    have hr := S.property (cubicCuspRemainder_mem P)
    have hd := S.val.sub_mem h hr
    have he : P-cubicCuspRemainder P=Polynomial.C (P.coeff 1)*Polynomial.X := by
      rw [cubicCuspRemainder,Polynomial.C_mul_X_eq_monomial]
      ring
    rwa [he] at hd

theorem cubicRepairAlgebra_le_iff (I J : Ideal (Polynomial ℝ)) :
    cubicRepairAlgebra I ≤ cubicRepairAlgebra J ↔ I ≤ J := by
  constructor
  · intro h p hp
    have hm : Polynomial.monomial 1 p ∈ cubicRepairAlgebra I := by
      rw [cubicRepairAlgebra_mem,Polynomial.coeff_monomial_same]
      exact hp
    have hj := h hm
    simpa only [cubicRepairAlgebra_mem,Polynomial.coeff_monomial_same] using hj
  · intro h P hP
    exact h hP

def cubicRepairOrderIso : Ideal (Polynomial ℝ) ≃o Ici cubicCuspAlgebra where
  toFun I := ⟨cubicRepairAlgebra I,cubicRepairAlgebra_contains I⟩
  invFun := cubicRepairIdeal
  left_inv := cubicRepairIdeal_leftInverse
  right_inv S := Subtype.ext (cubicRepairAlgebra_rightInverse S)
  map_rel_iff' := cubicRepairAlgebra_le_iff _ _

theorem cubicRepairAlgebra_bot : cubicRepairAlgebra ⊥=cubicCuspAlgebra := by
  ext P
  simp only [cubicRepairAlgebra_mem,Submodule.mem_bot,cubicCuspAlgebra_mem]

theorem cubicRepairAlgebra_top : cubicRepairAlgebra ⊤=⊤ := by
  ext P
  simp [cubicRepairAlgebra_mem]

def cubicRepairObservationAlgebra (I : Ideal (Polynomial ℝ)) : Subalgebra ℝ (cubicProbeSection → ℝ) :=
  (cubicRepairAlgebra I).map cubicPolynomialObservation

theorem cubicRepairObservationAlgebra_injective : Function.Injective cubicRepairObservationAlgebra := by
  intro I J h
  have he := Subalgebra.map_injective cubicPolynomialObservation_injective h
  exact le_antisymm ((cubicRepairAlgebra_le_iff I J).mp he.le)
    ((cubicRepairAlgebra_le_iff J I).mp he.ge)

theorem cubicRepairObservationAlgebra_bot : cubicRepairObservationAlgebra ⊥=cubicDecayObservationAlgebra := by
  rw [cubicRepairObservationAlgebra,cubicRepairAlgebra_bot]
  exact cubicDecayObservationAlgebra_presentation

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
