import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryHeterogeneousReciprocity
import GaloisForLFunctions.HTGeometry.ABHN.HeterogeneousTorsionSupportHasse

/-!
# Support rigidity for place-dependent cyclic carry profiles

Literal cyclic `H²` carry classes may vary by base field, splitting field, and torsion order at
each place. Their faithful embeddings in the common `ℚ/ℤ` target still force every nonzero
reciprocal packet to occupy at least two places.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

variable {ι : Type u} [DecidableEq ι]
  (K L : ι → Type)
  [(i : ι) → Field (K i)] [(i : ι) → Field (L i)]
  [(i : ι) → Algebra (K i) (L i)]
  [(i : ι) → FiniteDimensional (K i) (L i)]
  [(i : ι) → IsGalois (K i) (L i)]
  [(i : ι) → IsCyclic Gal(L i / K i)]
  (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
  (qEquiv : ∀ i,
    Additive (K i)ˣ ⧸ cyclicGaloisH2BaseNormImage (K i) (L i) ≃+ ZMod (n i))

local instance (i : ι) : DecidableEq (cyclicGaloisH2 (K i) (L i)) :=
  Classical.decEq _

/-- A nonzero reciprocal heterogeneous carry profile occupies at least two places. -/
theorem cyclicGaloisCarryH2Heterogeneous_two_le_support_card_of_sum_eq_zero
    (f : Π₀ i, cyclicGaloisH2 (K i) (L i))
    (hf : cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv f = 0)
    (hne : f ≠ 0) :
    2 ≤ f.support.card := by
  apply heterogeneousTorsionProfile_two_le_support_card_of_sum_eq_zero
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv) f
  · exact hf
  · exact hne

/-- Product-one reciprocity gives two nonzero places even when local cyclic data vary. -/
theorem cyclicGaloisCarryH2Heterogeneous_exists_two_nonzero_places_of_product_eq_one
    (f : Π₀ i, cyclicGaloisH2 (K i) (L i))
    (hf : f.prod (fun i z => ratModIntStdAddChar
      (cyclicGaloisCarryH2HeterogeneousLocalInvariantAddHom K L n hn qEquiv i z)) = 1)
    (hne : f ≠ 0) :
    ∃ i j, i ≠ j ∧ f i ≠ 0 ∧ f j ≠ 0 := by
  apply heterogeneousTorsionProfile_exists_two_nonzero_places_of_sum_eq_zero
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv) f
  · exact (cyclicGaloisCarryH2Heterogeneous_product_eq_one_iff_sum_eq_zero
      K L n hn qEquiv f).mp hf
  · exact hne

/-- A placewise nonnorm carry coordinate in a reciprocal packet forces another nonzero place. -/
theorem cyclicGaloisCarryH2Heterogeneous_nonnorm_coordinate_has_nonzero_partner
    (f : Π₀ i, cyclicGaloisH2 (K i) (L i)) (i : ι) (a : Additive (K i)ˣ)
    (hi : f i = cyclicGaloisCarryH2Class (K i) (L i) a)
    (ha : a ∉ cyclicGaloisH2BaseNormImage (K i) (L i))
    (hf : cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv f = 0) :
    ∃ j, j ≠ i ∧ f j ≠ 0 := by
  have hfi : f i ≠ 0 := by
    rw [hi]
    intro hzero
    exact ha ((cyclicGaloisCarryH2Class_eq_zero_iff_mem_normImage (K i) (L i) a).mp hzero)
  apply heterogeneousTorsionProfile_exists_other_nonzero_place_of_sum_eq_zero
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv) f
  · exact hf
  · exact hfi

end

end GaloisForLFunctions.HTGeometry.ABHN
