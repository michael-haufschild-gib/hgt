import GaloisForLFunctions.HodgeTheoryWithoutVarieties.FiniteConeComplexesHaveSphereBouquets
import Mathlib.Data.Nat.Prime.Basic

/-!
# The arithmetic height filtration of the prime complex

Faces are prime supports with product at most the height. In a fixed ambient
simplex the filtration inclusions preserve barycentric coordinates. Adjoining
prime two costs at most a factor two in height, so the inclusion into the doubled
height has an explicit nullhomotopy. This contracts an inclusion, not either
space, and therefore does not erase the homology at a fixed height.
-/

noncomputable section
open Finset ContinuousMap
open DifferentialGeometry.Simplex
open GaloisForLFunctions.HodgeTheoryWithoutVarieties
namespace GaloisForLFunctions.EffectiveScalingGeometry

/-- Prime faces at height `N`, in a fixed finite ambient simplex. -/
def primeHeightFaces (B N : ℕ) : Finset (Finset (Fin (B+3))) :=
  univ.filter fun S => (∀ p ∈ S, p.val.Prime) ∧ ∏ p ∈ S, p.val ≤ N

theorem mem_primeHeightFaces {B N : ℕ} {S : Finset (Fin (B+3))} :
    S ∈ primeHeightFaces B N ↔ (∀ p ∈ S, p.val.Prime) ∧ ∏ p ∈ S, p.val ≤ N := by
  simp only [primeHeightFaces, mem_filter, mem_univ, true_and]

def twoVertex (B : ℕ) : Fin (B+3) := ⟨2, by omega⟩

theorem primeHeightFaces_mono (B : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    primeHeightFaces B N ⊆ primeHeightFaces B M := by
  intro S hS
  obtain ⟨hp, hprod⟩ := mem_primeHeightFaces.mp hS
  exact mem_primeHeightFaces.mpr ⟨hp, hprod.trans hNM⟩

theorem insert_two_mem_double_height {B N : ℕ} {S : Finset (Fin (B+3))}
    (hS : S ∈ primeHeightFaces B N) :
    insert (twoVertex B) S ∈ primeHeightFaces B (2*N) := by
  obtain ⟨hp, hprod⟩ := mem_primeHeightFaces.mp hS
  apply mem_primeHeightFaces.mpr
  constructor
  · intro p hpS
    rcases mem_insert.mp hpS with rfl | hpS
    · exact Nat.prime_two
    · exact hp p hpS
  · by_cases h2 : twoVertex B ∈ S
    · rw [insert_eq_of_mem h2]
      omega
    · rw [prod_insert h2]
      exact Nat.mul_le_mul_left 2 hprod

/-- Realization of the arithmetic height filtration, with fixed vertex labels. -/
abbrev PrimeHeightSpace (B N : ℕ) := faceFamilySpace (primeHeightFaces B N)

/-- The actual filtration inclusion, preserving all barycentric coordinates. -/
def heightInclusion (B : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    C(PrimeHeightSpace B N, PrimeHeightSpace B M) where
  toFun x := ⟨x.val, faceFamilySpace_mono (primeHeightFaces_mono B hNM) x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem heightInclusion_refl (B N : ℕ) :
    heightInclusion B (le_refl N) = ContinuousMap.id _ := rfl

theorem heightInclusion_comp (B : ℕ) {N M L : ℕ} (hNM : N ≤ M) (hML : M ≤ L) :
    (heightInclusion B hML).comp (heightInclusion B hNM) =
      heightInclusion B (hNM.trans hML) := rfl

def heightApex (B N : ℕ) : PrimeHeightSpace B (2*(N+1)) :=
  ⟨stdSimplex.vertex (S := ℝ) (twoVertex B), mem_faceFamilySpace.mpr
    ⟨{twoVertex B}, mem_primeHeightFaces.mpr ⟨by
      intro p hp
      rw [mem_singleton] at hp
      subst p
      exact Nat.prime_two, by simp only [prod_singleton, twoVertex]; omega⟩,
      vertex_mem_supportFace (mem_singleton_self _)⟩⟩

theorem vertexContraction_mem_double_height (B N : ℕ) (t : unitInterval)
    (x : PrimeHeightSpace B (N+1)) :
    vertexContraction (twoVertex B) (t, x.val) ∈ PrimeHeightSpace B (2*(N+1)) := by
  obtain ⟨S, hS, hxS⟩ := mem_faceFamilySpace.mp x.property
  exact mem_faceFamilySpace.mpr ⟨insert (twoVertex B) S,
    insert_two_mem_double_height hS, vertexContraction_mem_insert_supportFace t hxS⟩

/-- Doubling the height makes the inclusion nullhomotopic through the cone at prime two. -/
def primeHeightDoublingHomotopy (B N : ℕ) :
    (heightInclusion B (show N+1 ≤ 2*(N+1) by omega)).Homotopy
      (ContinuousMap.const _ (heightApex B N)) where
  toFun z := ⟨vertexContraction (twoVertex B) (z.1, z.2.val),
    vertexContraction_mem_double_height B N z.1 z.2⟩
  continuous_toFun := ((vertexContraction (twoVertex B)).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext (vertexContraction_zero (twoVertex B) x.val)
  map_one_left x := Subtype.ext (vertexContraction_one (twoVertex B) x.val)

/-- The contraction is compatible with increasing the source height. -/
theorem primeHeightDoublingHomotopy_natural (B : ℕ) {N M : ℕ} (hNM : N ≤ M)
    (t : unitInterval) (x : PrimeHeightSpace B (N+1)) :
    heightInclusion B (Nat.mul_le_mul_left 2 (Nat.succ_le_succ hNM))
        (primeHeightDoublingHomotopy B N (t, x)) =
      primeHeightDoublingHomotopy B M
        (t, heightInclusion B (Nat.succ_le_succ hNM) x) := rfl

#print axioms primeHeightDoublingHomotopy
#print axioms primeHeightDoublingHomotopy_natural
end GaloisForLFunctions.EffectiveScalingGeometry
