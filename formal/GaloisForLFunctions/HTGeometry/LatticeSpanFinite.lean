import GaloisForLFunctions.HTGeometry.IntegralLatticeBasis

/-!
# Finite witnesses for character-lattice spans

Membership in the field-linear span of an integral character subgroup is witnessed by finitely
many actual character relations.  This is the finite bridge needed before extracting an integral
basis and applying a finite-dimensional transcendence theorem.
-/

namespace GaloisForLFunctions.HTGeometry
namespace LatticeSpanFinite

open TorusCharacterCoLie
open IntegralLatticeBasis

variable (k : Type*) [Field k]

/-- Exact finite-sum characterization of a field-linear character-lattice span. -/
theorem mem_latticeSpan_iff_exists_fin {n : ℕ}
    (L : AddSubgroup (Fin n →₀ ℤ)) (x : Fin n → k) :
    x ∈ latticeSpan k L ↔
      ∃ (r : ℕ) (m : Fin r → (Fin n →₀ ℤ)) (a : Fin r → k),
        (∀ j, m j ∈ L) ∧ x = ∑ j, a j • integralCast k (m j) := by
  constructor
  · intro hx
    obtain ⟨c, hcSupport, hcSum⟩ := Submodule.mem_span_set.mp hx
    let e : Fin c.support.card ≃ c.support := (Finset.equivFin c.support).symm
    have heImage (j : Fin c.support.card) :
        (e j).1 ∈ integralCast k '' (L : Set (Fin n →₀ ℤ)) :=
      hcSupport (e j).2
    let m : Fin c.support.card → (Fin n →₀ ℤ) := fun j => (heImage j).choose
    have hm (j : Fin c.support.card) : m j ∈ L := (heImage j).choose_spec.1
    have heq (j : Fin c.support.card) : integralCast k (m j) = (e j).1 :=
      (heImage j).choose_spec.2
    refine ⟨c.support.card, m, fun j => c (e j).1, hm, ?_⟩
    rw [← hcSum]
    change c.sum (fun v a => a • v) = _
    rw [Finsupp.sum]
    calc
      ∑ v ∈ c.support, c v • v = ∑ v : c.support, c v.1 • v.1 := by
        rw [← Finset.sum_attach]
        rfl
      _ = ∑ j : Fin c.support.card, c (e j).1 • (e j).1 :=
        (Equiv.sum_comp e _).symm
      _ = ∑ j : Fin c.support.card, c (e j).1 • integralCast k (m j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [heq]
  · rintro ⟨r, m, a, hm, rfl⟩
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨m j, hm j, rfl⟩)

/-- Every lattice-span vector has a finite expansion in actual lattice elements whose rational
coordinate vectors are linearly independent. -/
theorem exists_independent_latticeSpan_representation {n : ℕ}
    (L : AddSubgroup (Fin n →₀ ℤ)) (x : Fin n → k)
    (hx : x ∈ latticeSpan k L) :
    ∃ (r : ℕ) (m : Fin r → (Fin n →₀ ℤ)) (a : Fin r → k),
      LinearIndependent ℚ (fun j => integralCast ℚ (m j)) ∧
      (∀ j, m j ∈ L) ∧ x = ∑ j, a j • integralCast k (m j) := by
  classical
  obtain ⟨s, m₀, a₀, hm₀, hxsum⟩ :=
    (mem_latticeSpan_iff_exists_fin k L x).mp hx
  let S : Finset (Fin n →₀ ℤ) := Finset.univ.image m₀
  obtain ⟨r, m, hmIndependent, hmClosure, hmSpan⟩ :=
    exists_integralLatticeBasis_of_finset S
  have hSle : AddSubgroup.closure (S : Set (Fin n →₀ ℤ)) ≤ L :=
    (AddSubgroup.closure_le L).2 (by
      intro q hq
      simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ] at hq
      obtain ⟨j, rfl⟩ := hq
      exact hm₀ j)
  have hmL (j : Fin r) : m j ∈ L := hSle (hmClosure j)
  have hm₀S (j : Fin s) : m₀ j ∈ S := by simp [S]
  let z : Fin s → Fin r → ℤ := fun j => (hmSpan (m₀ j) (hm₀S j)).choose
  have hz (j : Fin s) : m₀ j = ∑ i, z j i • m i :=
    (hmSpan (m₀ j) (hm₀S j)).choose_spec
  have hcast (j : Fin s) :
      integralCast k (m₀ j) = ∑ i, (z j i : k) • integralCast k (m i) := by
    rw [hz, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  refine ⟨r, m, fun i => ∑ j, a₀ j * (z j i : k), hmIndependent, hmL, ?_⟩
  rw [hxsum]
  simp_rw [hcast]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]

end LatticeSpanFinite
end GaloisForLFunctions.HTGeometry
