import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairQuotient

/-!
# The discrete chain of power repairs

Adding the physical observation u^k c gives exactly the algebra whose missing-gap
coefficient is divisible by u^k. The algebras form a strictly distinguished
decreasing family, begin at the full normalization, and intersect in the
original cusp. Their membership criterion is the vanishing of the first k
coefficients in the first-mode variable.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicRepairPowerIdeal (k : ℕ) : Ideal (Polynomial ℝ) := Ideal.span {Polynomial.X^k}

def cubicFiniteRepairAlgebra (k : ℕ) : Subalgebra ℝ (Polynomial (Polynomial ℝ)) :=
  cubicRepairAlgebra (cubicRepairPowerIdeal k)

def cubicRepairPowerWitness (k : ℕ) : Polynomial (Polynomial ℝ) := Polynomial.C (Polynomial.X^k)*Polynomial.X

theorem cubicRepairPowerIdeal_mem (k : ℕ) (p : Polynomial ℝ) :
    p ∈ cubicRepairPowerIdeal k ↔ ∀ n < k, p.coeff n=0 := by
  rw [cubicRepairPowerIdeal,Ideal.mem_span_singleton,Polynomial.X_pow_dvd_iff]

theorem cubicFiniteRepairAlgebra_mem (k : ℕ) (P : Polynomial (Polynomial ℝ)) :
    P ∈ cubicFiniteRepairAlgebra k ↔ ∀ n < k, (P.coeff 1).coeff n=0 := by
  rw [cubicFiniteRepairAlgebra,cubicRepairAlgebra_mem,cubicRepairPowerIdeal_mem]

theorem cubicFiniteRepairAlgebra_contains (k : ℕ) : cubicCuspAlgebra ≤ cubicFiniteRepairAlgebra k :=
  cubicRepairAlgebra_contains _

theorem cubicRepairPowerWitness_mem (k j : ℕ) :
    cubicRepairPowerWitness j ∈ cubicFiniteRepairAlgebra k ↔ k ≤ j := by
  rw [cubicFiniteRepairAlgebra_mem,cubicRepairPowerWitness,Polynomial.C_mul_X_eq_monomial,
    Polynomial.coeff_monomial_same]
  constructor
  · intro h
    by_contra hn
    have hj : j < k := by omega
    have hc := h j hj
    simp at hc
  · intro h n hn
    have hnj : n ≠ j := by omega
    simp [Polynomial.coeff_X_pow,hnj]

theorem cubicFiniteRepairAlgebra_zero : cubicFiniteRepairAlgebra 0=⊤ := by
  rw [cubicFiniteRepairAlgebra,cubicRepairPowerIdeal,pow_zero,Ideal.span_singleton_one,cubicRepairAlgebra_top]

theorem cubicFiniteRepairAlgebra_antitone : Antitone cubicFiniteRepairAlgebra := by
  intro k j hkj P hP
  rw [cubicFiniteRepairAlgebra_mem] at hP ⊢
  intro n hn
  exact hP n (lt_of_lt_of_le hn hkj)

theorem cubicFiniteRepairAlgebra_injective : Function.Injective cubicFiniteRepairAlgebra := by
  intro k j h
  have hk : cubicRepairPowerWitness k ∈ cubicFiniteRepairAlgebra j := by
    rw [← h,cubicRepairPowerWitness_mem]
  have hj : cubicRepairPowerWitness j ∈ cubicFiniteRepairAlgebra k := by
    rw [h,cubicRepairPowerWitness_mem]
  exact le_antisymm ((cubicRepairPowerWitness_mem k j).mp hj)
    ((cubicRepairPowerWitness_mem j k).mp hk)

theorem cubicFiniteRepairAlgebra_intersection :
    (⨅ k : ℕ, cubicFiniteRepairAlgebra k)=cubicCuspAlgebra := by
  apply le_antisymm
  · intro P hP
    rw [cubicCuspAlgebra_mem]
    ext n
    have hk := (iInf_le cubicFiniteRepairAlgebra (n+1)) hP
    exact (cubicFiniteRepairAlgebra_mem (n+1) P).mp hk n (Nat.lt_succ_self n)
  · exact le_iInf cubicFiniteRepairAlgebra_contains

theorem cubicFiniteRepairAlgebra_adjoin (k : ℕ) :
    cubicFiniteRepairAlgebra k=cubicCuspAlgebra ⊔ Algebra.adjoin ℝ {cubicRepairPowerWitness k} := by
  apply le_antisymm
  · intro P hP
    change P.coeff 1 ∈ Ideal.span {Polynomial.X^k} at hP
    obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hP
    let S := cubicCuspAlgebra ⊔ Algebra.adjoin ℝ {cubicRepairPowerWitness k}
    have hCS : cubicCuspAlgebra ≤ S := le_sup_left
    have hWS : Algebra.adjoin ℝ {cubicRepairPowerWitness k} ≤ S := le_sup_right
    have hR : cubicCuspRemainder P ∈ S := hCS (cubicCuspRemainder_mem P)
    have hC : Polynomial.C r ∈ S := hCS (cubicCuspAlgebra_constant r)
    have hW : cubicRepairPowerWitness k ∈ S := hWS (Algebra.subset_adjoin (by rfl))
    have hm := S.mul_mem hC hW
    have he : Polynomial.C r*cubicRepairPowerWitness k=Polynomial.C (P.coeff 1)*Polynomial.X := by
      rw [hr,cubicRepairPowerWitness,map_mul]
      ring
    rw [he] at hm
    have hs := S.add_mem hR hm
    rwa [← cubicCuspRemainder_decomposition] at hs
  · apply sup_le (cubicFiniteRepairAlgebra_contains k)
    apply Algebra.adjoin_le
    intro P hP
    rcases hP with rfl
    exact (cubicRepairPowerWitness_mem k k).mpr le_rfl

theorem cubicRepairPowerWitness_observation (k : ℕ) :
    cubicPolynomialObservation (cubicRepairPowerWitness k)=
      (fun g => (cubicDecayMode 0 g.val)^k*g.val 2) :=
  cubicCuspDefectBasis_observation k

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
