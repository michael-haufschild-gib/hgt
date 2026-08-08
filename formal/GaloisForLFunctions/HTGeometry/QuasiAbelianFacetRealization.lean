import GaloisForLFunctions.HTGeometry.QuasiAbelianFacetCertificateOfTheta
import GaloisForLFunctions.HTGeometry.TranslationOperatorIncidence

/-!
# From a realization to a facet palette

The single statement assembling the chain.  Its inputs are the two facts the Stanley--Reisner side
produces about a facet realization -- translation by a vertex displacement fixes it exactly for the
vertices outside the facet, and distinct integral facet exponents translate it to distinct functions
-- together with the period-geometric data of the facet.  Its output is a facet certificate whose
lattice class is injective, hence a full palette input.

Extending a facet exponent by zero identifies the facet-indexed lattice sum with the ambient one, so
freeness of the complete integral orbit is exactly the triviality of the facet lattice's
intersection with the period group.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {W : Type*} [AddCommGroup W] {Y : Type*}

/-- Extending a facet exponent by zero does not change its displacement. -/
theorem sum_facetExponentExtend {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α)
    (a : α → W) (k : A → ℤ) :
    (∑ v : α, (facetExponentExtend A k v) • a v) = ∑ v : A, (k v) • a v.1 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset α) (· ∈ A)
    (fun v => (facetExponentExtend A k v) • a v)
  have hout : ∑ v ∈ Finset.univ.filter (fun v => v ∉ A),
      (facetExponentExtend A k v) • a v = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    have hvA : v ∉ A := (Finset.mem_filter.mp hv).2
    rw [facetExponentExtend, dif_neg hvA, zero_zsmul]
  have hin : ∑ v ∈ Finset.univ.filter (fun v => v ∈ A),
      (facetExponentExtend A k v) • a v = ∑ v : A, (k v) • a v.1 := by
    rw [show Finset.univ.filter (fun v => v ∈ A) = A by
      ext v; simp]
    rw [← Finset.sum_attach A (fun v => (facetExponentExtend A k v) • a v)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [facetExponentExtend, dif_pos v.2]
  rw [← hsplit, hout, hin, add_zero]

/-- **The facet lattice meets the periods only at the origin.**  Transported form of freeness of
the complete integral facet orbit. -/
theorem facetLattice_eq_zero_of_orbit_injective {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) {a : α → W} {G : W → Y}
    (hinj : Function.Injective fun n : α → ℤ => translateOp (∑ v, (n v) • a v) G)
    (k : A → ℤ) (hk : (∑ v : A, (k v) • a v.1) ∈ translationPeriods G) : k = 0 := by
  have hext : (∑ v : α, (facetExponentExtend A k v) • a v) ∈ translationPeriods G := by
    rw [sum_facetExponentExtend]
    exact hk
  have hzero := eq_zero_of_mem_translationPeriods_of_injective hinj _ hext
  have := facetExponentExtend_injective (α := α) A
  apply this
  rw [hzero]
  funext v
  rw [facetExponentExtend]
  split_ifs <;> rfl

section Capstone

/-- **From a facet realization to a facet palette.**  The two facts the Stanley--Reisner side
produces about a facet realization -- translation by a vertex displacement fixes it exactly for the
vertices outside the facet, and distinct integral facet exponents translate it to distinct functions
-- together with the period-geometric data of the facet, yield a facet certificate with an injective
integral lattice class.  Every clause of the certificate is a theorem; nothing is assumed. -/
theorem exists_quasiAbelianFacetCertificate_of_realization {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℝ W]
    {G : W → ℂ} (hGc : Continuous G) (a : α → W)
    (hincidence : ∀ v : α, translateOp (a v) G = G ↔ v ∉ A)
    (hinj : Function.Injective fun n : α → ℤ => translateOp (∑ v, (n v) • a v) G)
    [DiscreteTopology ((translationPeriods G : AddSubgroup W))]
    (hspan : Submodule.span ℝ ((translationPeriods G : AddSubgroup W) : Set W) ≠ ⊤)
    {E : W → W → ℝ} (hE : IsAlternatingCompatible E)
    (hEint : ∀ x ∈ translationPeriods G, ∀ y ∈ translationPeriods G, ∃ n : ℤ, E x y = (n : ℝ))
    (hpsd : ∀ x : W, 0 ≤ altSym E x x)
    (hnd : ∀ x : W, x ≠ 0 → ∃ y, altSym E x y ≠ 0) :
    ∃ C : QuasiAbelianFacetCertificate α A, Function.Injective C.latticeClass := by
  refine ⟨certificateOfAlternating A (translationPeriods G)
    (isClosed_translationPeriods hGc) hspan hE hEint hpsd hnd a
    (fun v => mem_translationPeriods_iff_of_translateOp hincidence v), ?_⟩
  intro n m h
  exact latticeClass_injective_of_free A (translationPeriods G)
    (isClosed_translationPeriods hGc) hspan hE hEint hpsd hnd a
    (fun v => mem_translationPeriods_iff_of_translateOp hincidence v)
    (facetLattice_eq_zero_of_orbit_injective A hinj) n m h

end Capstone

end GaloisForLFunctions.HTGeometry
