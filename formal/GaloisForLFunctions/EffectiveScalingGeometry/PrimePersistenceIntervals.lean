import GaloisForLFunctions.EffectiveScalingGeometry.ConeFiltrationPersistence
import GaloisForLFunctions.HTGeometry.SquarefreePrimeComplex

/-!
# The interval law for prime-height persistence

An odd prime support of product `m` is a complementary facet exactly at heights
`m ≤ N < 2m`. The explicit bouquet coordinates identify the filtration map on
its sphere with the identity up to homotopy while it survives, and with the
constant map after height `2m`. Thus the height filtration remembers a fixed
multiplicative lifespan, while parity remains in the sphere dimensions.
-/

noncomputable section
open Finset ContinuousMap
open DifferentialGeometry.Simplex
open GaloisForLFunctions.HodgeTheoryWithoutVarieties
namespace GaloisForLFunctions.EffectiveScalingGeometry

/-- The fixed-ambient model has precisely the original arithmetic prime faces. -/
theorem primeHeightFaces_iff_primeSets {B N : ℕ} {S : Finset (Fin (B+3))} :
    S ∈ primeHeightFaces B N ↔ S.map Fin.valEmbedding ∈ _root_.RHTower.primeSets N := by
  rw [mem_primeHeightFaces, HTGeometry.mem_primeSets_iff]
  simp only [Finset.forall_mem_map, Fin.valEmbedding_apply, Finset.prod_map]

/-- With ambient labels through `N+2`, every face of the full prime nerve occurs. -/
theorem primeSets_iff_exists_heightFace (N : ℕ) (S : Finset ℕ) :
    S ∈ _root_.RHTower.primeSets N ↔
      ∃ T ∈ primeHeightFaces N N, T.map Fin.valEmbedding = S := by
  constructor
  · intro hS
    have hs := HTGeometry.mem_primeSets_iff.mp hS
    have hbound : ∀ p ∈ S, p < N+3 := by
      intro p hp
      have hle := Nat.le_of_dvd (Finset.prod_pos fun q hq => (hs.1 q hq).pos)
        (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp)
      omega
    let e : S ↪ Fin (N+3) := ⟨fun p => ⟨p.val, hbound p.val p.property⟩,
      fun p q h => Subtype.ext (congrArg Fin.val h)⟩
    let T := S.attach.map e
    have hmap : T.map Fin.valEmbedding = S := by
      rw [Finset.map_map]
      exact Finset.attach_map_val
    refine ⟨T, primeHeightFaces_iff_primeSets.mpr ?_, hmap⟩
    rwa [hmap]
  · rintro ⟨T, hT, rfl⟩
    exact primeHeightFaces_iff_primeSets.mp hT

theorem primeHeightFaces_down_closed (B N : ℕ) :
    ∀ S ∈ primeHeightFaces B N, ∀ T ⊆ S, T ∈ primeHeightFaces B N := by
  intro S hS T hTS
  obtain ⟨hp, hprod⟩ := mem_primeHeightFaces.mp hS
  exact mem_primeHeightFaces.mpr ⟨fun p hpT => hp p (hTS hpT),
    (Finset.prod_le_prod_of_subset_of_one_le' hTS
      (fun p hpS _ => (hp p hpS).one_lt.le)).trans hprod⟩

theorem primeHeight_two_mem (B N : ℕ) :
    {twoVertex B} ∈ primeHeightFaces B (N+2) := by
  apply mem_primeHeightFaces.mpr
  constructor
  · intro p hp
    rw [mem_singleton] at hp
    subst p
    exact Nat.prime_two
  · simp only [prod_singleton, twoVertex]
    omega

theorem not_mem_primeHeightStar_iff {B N : ℕ} {S : Finset (Fin (B+3))}
    (hS : S ∈ primeHeightFaces B N) :
    S ∉ faceStar (primeHeightFaces B N) (twoVertex B) ↔
      twoVertex B ∉ S ∧ N < 2*∏ p ∈ S, p.val := by
  rw [mem_faceStar]
  simp only [hS, true_and]
  by_cases h2 : twoVertex B ∈ S
  · simp only [insert_eq_of_mem h2, hS, not_true_eq_false, h2, false_and]
  · rw [mem_primeHeightFaces]
    have hp : ∀ p ∈ insert (twoVertex B) S, p.val.Prime := by
      intro p hp
      rcases mem_insert.mp hp with rfl | hp
      · exact Nat.prime_two
      · exact (mem_primeHeightFaces.mp hS).1 p hp
    rw [and_iff_right hp, prod_insert h2, not_le]
    simp only [h2, not_false_eq_true, true_and]

/-- Exact arithmetic birth and death heights of each complementary facet. -/
theorem prime_complement_lifetime (B N : ℕ) (S : Finset (Fin (B+3))) :
    S ∈ complementaryFaces (primeHeightFaces B N) (twoVertex B) ↔
      (∀ p ∈ S, p.val.Prime) ∧ twoVertex B ∉ S ∧
        (∏ p ∈ S, p.val) ≤ N ∧ N < 2*∏ p ∈ S, p.val := by
  rw [mem_complementaryFaces]
  constructor
  · rintro ⟨hS, hs⟩
    obtain ⟨h2, ht⟩ := (not_mem_primeHeightStar_iff hS).mp hs
    exact ⟨(mem_primeHeightFaces.mp hS).1, h2, (mem_primeHeightFaces.mp hS).2, ht⟩
  · rintro ⟨hp, h2, hN, ht⟩
    have hS := mem_primeHeightFaces.mpr ⟨hp, hN⟩
    exact ⟨hS, (not_mem_primeHeightStar_iff hS).mpr ⟨h2, ht⟩⟩

/-- Surviving facet labels are actual odd squarefree integers, with the expected dimension. -/
theorem prime_complement_arithmetic (B N : ℕ)
    (S : complementaryFaces (primeHeightFaces B N) (twoVertex B)) :
    Odd (∏ p ∈ S.val, p.val) ∧ Squarefree (∏ p ∈ S.val, p.val) ∧
      (∏ p ∈ S.val, p.val).primeFactors.card = S.val.card := by
  have hs := (prime_complement_lifetime B N S.val).mp S.property
  have hp : ∀ p ∈ S.val.map Fin.valEmbedding, p.Prime := by
    simpa only [Finset.forall_mem_map, Fin.valEmbedding_apply] using hs.1
  have h2 : 2 ∉ S.val.map Fin.valEmbedding := by
    intro h
    obtain ⟨p, hpS, hp2⟩ := Finset.mem_map.mp h
    exact hs.2.1 ((show p = twoVertex B from Fin.ext hp2) ▸ hpS)
  have ho := (HTGeometry.primeSupport_odd_prod_iff hp).mpr h2
  have hsq := _root_.RHTower.GibbsGas.squarefree_prod_primes hp
  have hcard := congrArg Finset.card (Nat.primeFactors_prod hp)
  simp only [Finset.prod_map, Fin.valEmbedding_apply, Finset.card_map] at ho hsq hcard
  exact ⟨ho, hsq, hcard⟩

theorem primeHeight_proper_subface (B N : ℕ) :
    ∀ S ∈ complementaryFaces (primeHeightFaces B N) (twoVertex B),
      ∀ T ⊂ S, T ∈ faceStar (primeHeightFaces B N) (twoVertex B) := by
  intro S hS T hTS
  obtain ⟨hp, h2, hprod, _⟩ := (prime_complement_lifetime B N S).mp hS
  obtain ⟨p, hpS, hpT⟩ := Finset.exists_of_ssubset hTS
  have hT : T ∈ primeHeightFaces B N :=
    primeHeightFaces_down_closed B N S (mem_complementaryFaces.mp hS).1 T hTS.le
  apply mem_faceStar.mpr
  refine ⟨hT, mem_primeHeightFaces.mpr ⟨?_, ?_⟩⟩
  · intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact Nat.prime_two
    · exact hp q (hTS.le hq)
  · have h2T : twoVertex B ∉ T := fun h => h2 (hTS.le h)
    rw [prod_insert h2T]
    have hi := primeHeightFaces_down_closed B N S (mem_complementaryFaces.mp hS).1
      (insert p T) (Finset.insert_subset hpS hTS.le)
    have hibound := (mem_primeHeightFaces.mp hi).2
    rw [prod_insert hpT] at hibound
    exact (Nat.mul_le_mul_right (∏ q ∈ T, q.val) (hp p hpS).two_le).trans hibound

/-- Boundary-sphere coordinates at height `N+2`. -/
abbrev PrimeHeightBouquet (B N : ℕ) := ConeBouquet (primeHeight_two_mem B N)

/-- The bouquet equivalence has all its geometric premises proved arithmetically. -/
def primeHeightBouquetEquiv (B N : ℕ) :
    HomotopyEquiv (PrimeHeightSpace B (N+2)) (PrimeHeightBouquet B N) :=
  finiteConeComplexHomotopyEquiv (primeHeightFaces_down_closed B (N+2))
    (primeHeight_two_mem B N) (primeHeight_proper_subface B (N+2))

/-- The actual inclusion from height `N+2` to `N+d+2`, in bouquet coordinates. -/
def primePersistenceMap (B N d : ℕ) : C(PrimeHeightBouquet B N, PrimeHeightBouquet B (N+d)) :=
  conePersistenceMap (primeHeightFaces_mono B (show N+2 ≤ N+d+2 by omega))
    (primeHeight_two_mem B N) (primeHeight_two_mem B (N+d))
    (primeHeight_proper_subface B (N+2)) (primeHeightFaces_down_closed B (N+d+2))
    (primeHeight_proper_subface B (N+d+2))

/-- A sphere dies precisely when the height reaches twice its odd support product. -/
theorem primePersistence_survival_iff (B N d : ℕ)
    (S : complementaryFaces (primeHeightFaces B (N+2)) (twoVertex B)) :
    S.val ∈ complementaryFaces (primeHeightFaces B (N+d+2)) (twoVertex B) ↔
      N+d+2 < 2*∏ p ∈ S.val, p.val := by
  obtain ⟨hp, h2, hprod, ht⟩ := (prime_complement_lifetime B (N+2) S.val).mp S.property
  rw [prime_complement_lifetime]
  exact ⟨fun h => h.2.2.2, fun h => ⟨hp, h2, by omega, h⟩⟩

/-- The surviving arithmetic sphere is preserved by an explicit homotopy. -/
def primePersistenceSurvivingHomotopy (B N d : ℕ)
    (S : complementaryFaces (primeHeightFaces B (N+2)) (twoVertex B))
    (hS : N+d+2 < 2*∏ p ∈ S.val, p.val) :
    (bouquetInclusion (complementarySpherePoint (primeHeight_two_mem B (N+d)))
      ⟨S.val, (primePersistence_survival_iff B N d S).mpr hS⟩).Homotopy
      ((primePersistenceMap B N d).comp
        (bouquetInclusion (complementarySpherePoint (primeHeight_two_mem B N)) S)) :=
  survivingSummandHomotopy
    (primeHeightFaces_mono B (show N+2 ≤ N+d+2 by omega))
    (primeHeight_two_mem B N) (primeHeight_two_mem B (N+d))
    (primeHeight_proper_subface B (N+2)) (primeHeightFaces_down_closed B (N+d+2))
    (primeHeight_proper_subface B (N+d+2)) S
    ((primePersistence_survival_iff B N d S).mpr hS)

/-- Complete summand formula for every arithmetic height inclusion. -/
theorem primePersistence_on_summand (B N d : ℕ)
    (S : complementaryFaces (primeHeightFaces B (N+2)) (twoVertex B))
    (p : FacetBoundary (twoVertex B) S.val) :
    primePersistenceMap B N d
        (bouquetInclusion (complementarySpherePoint (primeHeight_two_mem B N)) S p) =
      if h : N+d+2 < 2*∏ q ∈ S.val, q.val then
        bouquetInclusion (complementarySpherePoint (primeHeight_two_mem B (N+d)))
          ⟨S.val, (primePersistence_survival_iff B N d S).mpr h⟩
          (complementarySphereHomotopy (primeHeight_two_mem B (N+d))
            ⟨S.val, (primePersistence_survival_iff B N d S).mpr h⟩ (1, p))
      else bouquetPoint (complementarySpherePoint (primeHeight_two_mem B (N+d))) := by
  by_cases h : N+d+2 < 2*∏ q ∈ S.val, q.val
  · rw [dif_pos h]
    exact conePersistenceMap_surviving _ _ _ _ _ _ S
      ((primePersistence_survival_iff B N d S).mpr h) p
  · rw [dif_neg h]
    exact conePersistenceMap_dead _ _ _ _ _ _ S
      (fun hs => h ((primePersistence_survival_iff B N d S).mp hs)) p

#print axioms primeHeightBouquetEquiv
#print axioms primeSets_iff_exists_heightFace
#print axioms prime_complement_arithmetic
#print axioms primePersistence_survival_iff
#print axioms primePersistenceSurvivingHomotopy
#print axioms primePersistence_on_summand
end GaloisForLFunctions.EffectiveScalingGeometry
