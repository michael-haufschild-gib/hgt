import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairRigidity

/-!
# Classification of all invariant intermediate observation algebras

Preservation by the physical half-retraction is equivalent to preservation by
all polynomial flow parameters. Every such intermediate algebra is either the
original cusp or one unique finite power repair. The correspondence with ideal
stability and the exact classification are proved for the entire family.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial

theorem cubicFiniteRepairAlgebra_flow (q : ℝ) (k : ℕ) :
    MapsTo (cubicPolynomialFlow q) (cubicFiniteRepairAlgebra k) (cubicFiniteRepairAlgebra k) := by
  intro P hP
  change (cubicPolynomialFlow q P).coeff 1 ∈ cubicRepairPowerIdeal k
  rw [cubicPolynomialFlow_coefficient]
  exact (cubicRepairPowerIdeal k).mul_mem_right _ (cubicRepairPowerIdeal_flow q k hP)

theorem cubicRepairAlgebra_halfStable_iff (I : Ideal (Polynomial ℝ)) :
    MapsTo (cubicPolynomialFlow (1/2)) (cubicRepairAlgebra I) (cubicRepairAlgebra I) ↔
      I ∈ cubicHalfStableIdeals := by
  constructor
  · intro h p hp
    have hP : Polynomial.C p*Polynomial.X ∈ cubicRepairAlgebra I := by
      rw [cubicRepairAlgebra_mem,Polynomial.C_mul_X_eq_monomial,Polynomial.coeff_monomial_same]
      exact hp
    have hf := h hP
    change (cubicPolynomialFlow (1/2) (Polynomial.C p*Polynomial.X)).coeff 1 ∈ I at hf
    rw [cubicPolynomialFlow_coefficient,Polynomial.C_mul_X_eq_monomial,
      Polynomial.coeff_monomial_same,pow_one] at hf
    have hm := I.mul_mem_right (Polynomial.C 2) hf
    have he : (cubicInnerPolynomialFlow (1/2) p*Polynomial.C (1/2))*Polynomial.C 2=
        cubicInnerPolynomialFlow (1/2) p := by
      rw [mul_assoc,← map_mul]
      have hhalf : (1/2:ℝ)*2=1 := by ring
      rw [hhalf,map_one,mul_one]
    rwa [he] at hm
  · intro h P hP
    change (cubicPolynomialFlow (1/2) P).coeff 1 ∈ I
    rw [cubicPolynomialFlow_coefficient]
    exact I.mul_mem_right _ (h hP)

def cubicHalfStableRepairAlgebras : Set (Ici cubicCuspAlgebra) :=
  {S | MapsTo (cubicPolynomialFlow (1/2)) S.val S.val}

theorem cubicHalfStableRepairAlgebras_classification (S : Ici cubicCuspAlgebra) :
    S ∈ cubicHalfStableRepairAlgebras ↔
      S.val=cubicCuspAlgebra ∨ ∃ k : ℕ, S.val=cubicFiniteRepairAlgebra k := by
  constructor
  · intro h
    change MapsTo (cubicPolynomialFlow (1/2)) S.val S.val at h
    rw [← cubicRepairAlgebra_rightInverse S] at h
    have hI := (cubicRepairAlgebra_halfStable_iff (cubicRepairIdeal S)).mp h
    have he := cubicRepairAlgebra_rightInverse S
    rcases (cubicHalfStableIdeals_classification _).mp hI with hzero | ⟨k,hk⟩
    · rw [hzero,cubicRepairAlgebra_bot] at he
      exact Or.inl he.symm
    · rw [hk] at he
      exact Or.inr ⟨k,he.symm⟩
  · rintro (h | ⟨k,h⟩)
    · change MapsTo (cubicPolynomialFlow (1/2)) S.val S.val
      rw [h]
      exact cubicPolynomialFlow_preservesCusp (1/2)
    · change MapsTo (cubicPolynomialFlow (1/2)) S.val S.val
      rw [h]
      exact cubicFiniteRepairAlgebra_flow (1/2) k

theorem cubicHalfStableRepairAlgebras_fullFlow :
    cubicHalfStableRepairAlgebras=
      {S : Ici cubicCuspAlgebra | ∀ q : ℝ, MapsTo (cubicPolynomialFlow q) S.val S.val} := by
  ext S
  constructor
  · intro h
    rcases (cubicHalfStableRepairAlgebras_classification S).mp h with hA | ⟨k,hk⟩
    · intro q
      rw [hA]
      exact cubicPolynomialFlow_preservesCusp q
    · intro q
      rw [hk]
      exact cubicFiniteRepairAlgebra_flow q k
  · intro h
    exact h (1/2)

theorem cubicFiniteRepairAlgebra_ne_cusp (k : ℕ) : cubicFiniteRepairAlgebra k ≠ cubicCuspAlgebra := by
  intro h
  have hm := (cubicRepairPowerWitness_mem k k).mpr le_rfl
  rw [h,cubicCuspAlgebra_mem,cubicRepairPowerWitness,Polynomial.C_mul_X_eq_monomial,
    Polynomial.coeff_monomial_same] at hm
  exact pow_ne_zero k Polynomial.X_ne_zero hm

theorem cubicHalfStableRepairAlgebras_uniqueFinite (S : Ici cubicCuspAlgebra) :
    S ∈ cubicHalfStableRepairAlgebras ↔
      S.val=cubicCuspAlgebra ∨ ∃! k : ℕ, S.val=cubicFiniteRepairAlgebra k := by
  rw [cubicHalfStableRepairAlgebras_classification]
  constructor
  · rintro (h | ⟨k,hk⟩)
    · exact Or.inl h
    · exact Or.inr ⟨k,hk,fun j hj => cubicFiniteRepairAlgebra_injective (hj.symm.trans hk)⟩
  · rintro (h | ⟨k,hk,_⟩)
    · exact Or.inl h
    · exact Or.inr ⟨k,hk⟩

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
