import GaloisForLFunctions.HTGeometry.PointsSeparate
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor products of reduced algebras over an algebraically closed field

Over an algebraically closed field the points of a reduced finitely generated algebra separate its
elements.  Expanding a nilpotent element of a tensor product against a basis of the second factor,
each pair of points kills it; separating points in the second factor and then in the first forces
every coefficient to vanish.  Both factors reduce to finitely generated subalgebras because a
tensor product over a field is a filtered colimit of tensor products of finitely generated pieces.
-/


namespace GaloisForLFunctions.HTGeometry

open TensorProduct Module

noncomputable section

/-- Every element of `M ⊗[k] N` is a finite sum of tensors against basis vectors of `N`. -/
theorem exists_basis_tmul_repr {k M N ι : Type*} [Field k] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (bs : Basis ι k N) (z : M ⊗[k] N) :
    ∃ (t : Finset ι) (a : ι → M), z = ∑ i ∈ t, a i ⊗ₜ[k] bs i := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun _ => 0, by simp⟩
  | tmul m n =>
      refine ⟨(bs.repr n).support, fun i => (bs.repr n i) • m, ?_⟩
      conv_lhs => rw [← bs.linearCombination_repr n]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
      obtain ⟨t₁, a₁, h₁⟩ := hx
      obtain ⟨t₂, a₂, h₂⟩ := hy
      refine ⟨t₁ ∪ t₂, fun i => (if i ∈ t₁ then a₁ i else 0) + (if i ∈ t₂ then a₂ i else 0), ?_⟩
      have e₁ : ∑ i ∈ t₁ ∪ t₂, (if i ∈ t₁ then a₁ i else 0) ⊗ₜ[k] bs i
          = ∑ i ∈ t₁, a₁ i ⊗ₜ[k] bs i := by
        rw [← Finset.sum_subset Finset.subset_union_left]
        · exact Finset.sum_congr rfl fun i hi => by rw [if_pos hi]
        · intro i _ hi
          rw [if_neg hi, TensorProduct.zero_tmul]
      have e₂ : ∑ i ∈ t₁ ∪ t₂, (if i ∈ t₂ then a₂ i else 0) ⊗ₜ[k] bs i
          = ∑ i ∈ t₂, a₂ i ⊗ₜ[k] bs i := by
        rw [← Finset.sum_subset Finset.subset_union_right]
        · exact Finset.sum_congr rfl fun i hi => by rw [if_pos hi]
        · intro i _ hi
          rw [if_neg hi, TensorProduct.zero_tmul]
      rw [h₁, h₂, ← e₁, ← e₂, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [TensorProduct.add_tmul]

/-- **Over an algebraically closed field, reduced finitely generated algebras have reduced tensor
product.** -/
theorem isReduced_tensorProduct_of_finiteType
    {k A B : Type*} [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsReduced A] [IsReduced B]
    [Algebra.FiniteType k A] [Algebra.FiniteType k B] :
    IsReduced (A ⊗[k] B) := by
  classical
  constructor
  intro z hz
  obtain ⟨t, a, rfl⟩ := exists_basis_tmul_repr (Basis.ofVectorSpace k B) z
  set bs := Basis.ofVectorSpace k B with hbs
  have key : ∀ χ : A →ₐ[k] k, ∀ i ∈ t, χ (a i) = 0 := by
    intro χ
    set Φ : A ⊗[k] B →ₐ[k] B :=
      Algebra.TensorProduct.lift ((Algebra.ofId k B).comp χ) (AlgHom.id k B)
        (fun _ _ => Commute.all _ _) with hΦ
    have hzero : Φ (∑ i ∈ t, a i ⊗ₜ[k] bs i) = 0 := (hz.map Φ).eq_zero
    rw [map_sum] at hzero
    have hexp : ∑ i ∈ t, Φ (a i ⊗ₜ[k] bs i) = ∑ i ∈ t, χ (a i) • bs i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hΦ, Algebra.TensorProduct.lift_tmul]
      simp [Algebra.smul_def]
    rw [hexp] at hzero
    exact fun i hi =>
      linearIndependent_iff'.mp bs.linearIndependent t (fun i => χ (a i)) hzero i hi
  have hazero : ∀ i ∈ t, a i = 0 := fun i hi =>
    eq_zero_of_forall_algHom_eq_zero (fun χ => key χ i hi)
  rw [Finset.sum_congr rfl (fun i hi => by rw [hazero i hi, TensorProduct.zero_tmul])]
  simp

/-- **Over an algebraically closed field the tensor product of reduced algebras is reduced.**
Both factors are reduced to finitely generated subalgebras, where points separate. -/
theorem isReduced_tensorProduct_of_isAlgClosed
    {k A B : Type*} [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsReduced A] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  classical
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun B' hB' => ?_)
  haveI : IsReduced ↥B' := isReduced_of_injective B'.subtype Subtype.val_injective
  haveI : Algebra.FiniteType k ↥B' := ⟨(Subalgebra.fg_top B').mpr hB'⟩
  have hswap : IsReduced (↥B' ⊗[k] A) := by
    refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun A' hA' => ?_)
    haveI : IsReduced ↥A' := isReduced_of_injective A'.subtype Subtype.val_injective
    haveI : Algebra.FiniteType k ↥A' := ⟨(Subalgebra.fg_top A').mpr hA'⟩
    exact isReduced_tensorProduct_of_finiteType
  exact isReduced_of_injective (Algebra.TensorProduct.comm k A ↥B')
    (Algebra.TensorProduct.comm k A ↥B').injective

end

end GaloisForLFunctions.HTGeometry
