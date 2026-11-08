import GaloisForLFunctions.HeightHomotopyArithmeticCounts.PrimeCoreEuler
import GaloisForLFunctions.EffectiveScalingGeometry.PrimePersistenceIntervals

/-!
# The positive-dimensional spheres of the connected core

The core's complementary facets are exactly the original complementary facets
with at least two vertices. All their proper subfaces lie in the core star of
two, giving an actual bouquet equivalence. This retains all positive-dimensional
arithmetic spheres while removing precisely the isolated-prime contribution.
-/

noncomputable section
open Finset ContinuousMap
open DifferentialGeometry.Simplex
open GaloisForLFunctions.EffectiveScalingGeometry
open GaloisForLFunctions.HodgeTheoryWithoutVarieties
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

/-- At full ambient height every arithmetic core face is represented exactly. -/
theorem primeCoreNerve_iff_exists_coreFace (N : ℕ) (S : Finset ℕ) :
    S∈primeCoreNerve N ↔ ∃ T∈primeCoreFaces N N, T.map Fin.valEmbedding=S := by
  constructor
  · intro hS
    have hn := (mem_filter.mp hS).1
    have hp : S∈_root_.RHTower.primeSets N :=
      HTGeometry.mem_primeSets_iff.mpr (mem_squarefreeNerve.mp hn)
    obtain ⟨T,_hT,he⟩ := (primeSets_iff_exists_heightFace N S).mp hp
    refine ⟨T,(primeCoreFaces_map_iff T).mpr ?_,he⟩
    rwa [he]
  · rintro ⟨T,hT,rfl⟩
    exact (primeCoreFaces_map_iff T).mp hT

/-- Restricting the vertex labels preserves downward closure. -/
theorem primeCoreFaces_down_closed (B N : ℕ) :
    ∀ S∈primeCoreFaces B N, ∀ T⊆S, T∈primeCoreFaces B N := by
  intro S hS T hTS
  obtain ⟨hS,hsmall⟩ := mem_filter.mp hS
  exact mem_filter.mpr ⟨primeHeightFaces_down_closed B N S hS T hTS,
    fun p hp => hsmall p (hTS hp)⟩

/-- Prime two remains in the connected core. -/
theorem primeCore_two_mem (B N : ℕ) : {twoVertex B}∈primeCoreFaces B (N+4) := by
  apply mem_filter.mpr
  refine ⟨?_,?_⟩
  · simpa only [Nat.add_assoc] using primeHeight_two_mem B (N+2)
  · intro p hp
    rw [mem_singleton] at hp
    subst p
    change 2*2≤N+4
    omega

/-- The core star is the original star restricted to core labels. -/
theorem primeCore_star_iff {B N : ℕ} (hN : 4≤N) (S : Finset (Fin (B+3))) :
    S∈faceStar (primeCoreFaces B N) (twoVertex B) ↔
      S∈faceStar (primeHeightFaces B N) (twoVertex B) ∧ ∀p∈S,2*p.val≤N := by
  simp only [mem_faceStar, primeCoreFaces, mem_filter]
  constructor
  · rintro ⟨⟨hS,hs⟩,⟨hi,_⟩⟩
    exact ⟨⟨hS,hi⟩,hs⟩
  · rintro ⟨⟨hS,hi⟩,hs⟩
    refine ⟨⟨hS,hs⟩,hi,?_⟩
    intro p hp
    rcases mem_insert.mp hp with rfl|hp
    · exact hN
    · exact hs p hp

private theorem core_complement_iff_small {B N : ℕ} (hN : 4≤N)
    (S : Finset (Fin (B+3))) :
    S∈complementaryFaces (primeCoreFaces B N) (twoVertex B) ↔
      S∈complementaryFaces (primeHeightFaces B N) (twoVertex B) ∧ ∀p∈S,2*p.val≤N := by
  rw [mem_complementaryFaces,primeCore_star_iff hN,mem_complementaryFaces]
  simp only [primeCoreFaces, mem_filter]
  tauto

/-- Exactly the zero-sphere facets disappear when the isolated vertices are removed. -/
theorem primeCore_complement_iff {B N : ℕ} (hN : 4≤N)
    (S : Finset (Fin (B+3))) :
    S∈complementaryFaces (primeCoreFaces B N) (twoVertex B) ↔
      S∈complementaryFaces (primeHeightFaces B N) (twoVertex B) ∧ 2≤S.card := by
  rw [core_complement_iff_small hN]
  constructor
  · rintro ⟨hS,hsmall⟩
    refine ⟨hS,?_⟩
    by_contra hc
    have hle : S.card≤1 := by omega
    obtain rfl|⟨p,hp⟩ := S.eq_empty_or_nonempty
    · have hl := (prime_complement_lifetime B N ∅).mp hS
      simp only [prod_empty] at hl
      omega
    · have he : S={p} := by
        apply subset_antisymm
        · intro q hq
          exact mem_singleton.mpr (card_le_one.mp hle q hq p hp)
        · exact singleton_subset_iff.mpr hp
      subst S
      have hl := (prime_complement_lifetime B N {p}).mp hS
      have hs := hsmall p (mem_singleton_self p)
      simp only [prod_singleton] at hl
      omega
  · rintro ⟨hS,hcard⟩
    refine ⟨hS,?_⟩
    intro p hp
    by_contra hlarge
    have he := upperPrime_face_singleton (Nat.lt_of_not_ge hlarge)
      (mem_complementaryFaces.mp hS).1 hp
    rw [he,card_singleton] at hcard
    omega

/-- Every proper subface of a core facet is in the core star of two. -/
theorem primeCore_proper_subface {B N : ℕ} (hN : 4≤N) :
    ∀ S∈complementaryFaces (primeCoreFaces B N) (twoVertex B),
      ∀ T⊂S, T∈faceStar (primeCoreFaces B N) (twoVertex B) := by
  intro S hS T hTS
  obtain ⟨hS,hsmall⟩ := (core_complement_iff_small hN S).mp hS
  exact (primeCore_star_iff hN T).mpr
    ⟨primeHeight_proper_subface B N S hS T hTS, fun p hp => hsmall p (hTS.le hp)⟩

/-- The bouquet of the connected core has no zero-dimensional sphere summands. -/
abbrev PrimeCoreBouquet (B N : ℕ) := ConeBouquet (primeCore_two_mem B N)

/-- An actual homotopy equivalence retaining every positive-dimensional arithmetic sphere. -/
def primeCoreBouquetEquiv (B N : ℕ) :
    HomotopyEquiv (faceFamilySpace (primeCoreFaces B (N+4))) (PrimeCoreBouquet B N) :=
  finiteConeComplexHomotopyEquiv (primeCoreFaces_down_closed B (N+4))
    (primeCore_two_mem B N) (primeCore_proper_subface (by omega))

/-- The remaining sphere labels are odd squarefree composite products, with their exact dimensions. -/
theorem primeCore_complement_arithmetic (B N : ℕ)
    (S : complementaryFaces (primeCoreFaces B (N+4)) (twoVertex B)) :
    2≤S.val.card ∧ Odd (∏p∈S.val,p.val) ∧ Squarefree (∏p∈S.val,p.val) ∧
      (∏p∈S.val,p.val).primeFactors.card=S.val.card := by
  obtain ⟨hS,hcard⟩ := (primeCore_complement_iff (by omega) S.val).mp S.property
  exact ⟨hcard,prime_complement_arithmetic B (N+4) ⟨S.val,hS⟩⟩

#print axioms primeCoreNerve_iff_exists_coreFace
#print axioms primeCore_complement_iff
#print axioms primeCoreBouquetEquiv
#print axioms primeCore_complement_arithmetic
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
