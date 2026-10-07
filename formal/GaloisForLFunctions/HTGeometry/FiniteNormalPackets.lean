import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Group

/-!
# Finite images of commonly conjugatable normal packets

A common conjugator for each finite packet suffices to contain the image of
a normal subgroup in every finite image. No single global conjugator, discrete
subgroup inclusion, or surjectivity of the finite homomorphism is asserted.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Finite packet conjugation forces containment in every finite group image. -/
theorem map_le_of_finite_normal_packets {Γ G : Type*} [Group Γ] [Group G] [Finite G]
    (N H : Subgroup Γ) [hN : N.Normal]
    (hpacket : ∀ T : Finset Γ, (∀ x ∈ T, x ∈ N) →
      ∃ g : Γ, ∀ x ∈ T, g * x * g⁻¹ ∈ H)
    (q : Γ →* G) : N.map q ≤ H.map q := by
  classical
  letI : Fintype (N.map q) := Fintype.ofFinite _
  have hrep (y : N.map q) : ∃ x ∈ N, q x = (y : G) := Subgroup.mem_map.mp y.2
  choose t htN htq using hrep
  let T : Finset Γ := Finset.univ.image t
  have hTN : ∀ x ∈ T, x ∈ N := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact htN y
  obtain ⟨g, hg⟩ := hpacket T hTN
  intro y hy
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
  let v : N.map q := ⟨q (g⁻¹ * n * g),
    Subgroup.mem_map.mpr ⟨g⁻¹ * n * g, hN.conj_mem' n hn g, rfl⟩⟩
  refine Subgroup.mem_map.mpr ⟨g * t v * g⁻¹, ?_, ?_⟩
  · exact hg (t v) (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
  · rw [map_mul, map_mul, htq]
    change q g * q (g⁻¹ * n * g) * q (g⁻¹) = q n
    simp only [map_mul, map_inv]
    group

end GaloisForLFunctions.HTGeometry
