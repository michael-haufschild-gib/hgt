import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedReduced
import GaloisForLFunctions.HTGeometry.FiniteTypeSpecialization

/-!
# Tensor products of domains over an algebraically closed field

If the first domain is finitely generated over an algebraically closed field, its rational points
can simultaneously preserve one nonzero coefficient from each of two tensors.  Specializing that
factor then detects their product in the second domain.
-/

open TensorProduct Module

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Over an algebraically closed field, the tensor product of a finite-type domain with any domain
is a domain. -/
theorem isDomain_tensorProduct_of_finiteType
    {k A B : Type*} [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain A] [IsDomain B]
    [Algebra.FiniteType k A] :
    IsDomain (A ⊗[k] B) := by
  classical
  let bs := Basis.ofVectorSpace k B
  have hnozero : ∀ z w : A ⊗[k] B, z * w = 0 → z = 0 ∨ w = 0 := by
    intro z w hzw
    by_cases hz : z = 0
    · exact Or.inl hz
    by_cases hw : w = 0
    · exact Or.inr hw
    exfalso
    obtain ⟨tz, az, hzrepr⟩ := exists_basis_tmul_repr bs z
    obtain ⟨tw, aw, hwrepr⟩ := exists_basis_tmul_repr bs w
    have hazine : ∃ i ∈ tz, az i ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      rw [hzrepr]
      apply Finset.sum_eq_zero
      intro i hi
      rw [h i hi, TensorProduct.zero_tmul]
    have hawine : ∃ i ∈ tw, aw i ≠ 0 := by
      by_contra h
      push Not at h
      apply hw
      rw [hwrepr]
      apply Finset.sum_eq_zero
      intro i hi
      rw [h i hi, TensorProduct.zero_tmul]
    obtain ⟨iz, hiz, haz⟩ := hazine
    obtain ⟨iw, hiw, haw⟩ := hawine
    obtain ⟨χ, hχ⟩ :=
      GaloisForLFunctions.exists_algHom_ne_zero_of_finiteType_domain
        k A (az iz * aw iw) (mul_ne_zero haz haw)
    have hχz : χ (az iz) ≠ 0 := by
      intro h
      apply hχ
      rw [map_mul, h, zero_mul]
    have hχw : χ (aw iw) ≠ 0 := by
      intro h
      apply hχ
      rw [map_mul, h, mul_zero]
    let Φ : A ⊗[k] B →ₐ[k] B :=
      Algebra.TensorProduct.lift ((Algebra.ofId k B).comp χ) (AlgHom.id k B)
        (fun _ _ => Commute.all _ _)
    have hΦz : Φ z = ∑ i ∈ tz, χ (az i) • bs i := by
      rw [hzrepr, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Φ, Algebra.smul_def]
    have hΦw : Φ w = ∑ i ∈ tw, χ (aw i) • bs i := by
      rw [hwrepr, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Φ, Algebra.smul_def]
    have hΦzne : Φ z ≠ 0 := by
      intro hzero
      rw [hΦz] at hzero
      exact hχz (linearIndependent_iff'.mp bs.linearIndependent tz
        (fun i => χ (az i)) hzero iz hiz)
    have hΦwne : Φ w ≠ 0 := by
      intro hzero
      rw [hΦw] at hzero
      exact hχw (linearIndependent_iff'.mp bs.linearIndependent tw
        (fun i => χ (aw i)) hzero iw hiw)
    exact mul_ne_zero hΦzne hΦwne
      (by simpa [map_mul] using congrArg Φ hzw)
  letI : NoZeroDivisors (A ⊗[k] B) := ⟨fun {z w} h => hnozero z w h⟩
  exact NoZeroDivisors.to_isDomain (A ⊗[k] B)

end

end GaloisForLFunctions.HTGeometry
