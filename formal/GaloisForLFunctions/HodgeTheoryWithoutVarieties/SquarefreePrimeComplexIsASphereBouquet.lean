import GaloisForLFunctions.HodgeTheoryWithoutVarieties.FiniteConeComplexesHaveSphereBouquets
import GaloisForLFunctions.HTGeometry.SquarefreePrimeComplex
import DifferentialGeometry.Topology.Simplex.NormedBall

/-!
# The squarefree prime complex is a wedge of spheres

The star of two is contractible. Its complementary facets are the prime
supports of odd squarefree integers in the upper half-window. Their
surrounding simplex boundaries give the actual homotopy equivalence.
-/

noncomputable section
open ContinuousMap Finset
open DifferentialGeometry.Simplex
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- Prime labels of a face in the finite ambient vertex set. -/
def primeFaceImage {N : ℕ} (S : Finset (Fin (N + 1))) : Finset ℕ :=
  S.map Fin.valEmbedding

/-- The prime-support complex on the finite vertex set `{0,…,N}`.
Vertices zero, one, and composite labels occur in no face. -/
def boundedPrimeFaces (N : ℕ) : Finset (Finset (Fin (N + 1))) :=
  Finset.univ.filter (fun S => primeFaceImage S ∈ _root_.RHTower.primeSets N)

theorem mem_boundedPrimeFaces {N : ℕ} {S : Finset (Fin (N + 1))} :
    S ∈ boundedPrimeFaces N ↔ primeFaceImage S ∈ _root_.RHTower.primeSets N := by
  simp only [boundedPrimeFaces, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The nonempty faces are exactly those of the abstract prime complex. -/
theorem boundedPrimeFaces_nonempty_iff {N : ℕ} {S : Finset (Fin (N + 1))} :
    primeFaceImage S ∈ (squarefreePrimeComplex N).faces ↔
      S ∈ boundedPrimeFaces N ∧ S.Nonempty := by
  simp [squarefreePrimeComplex, mem_boundedPrimeFaces, primeFaceImage]

theorem boundedPrimeFaces_down_closed (N : ℕ) :
    ∀ S ∈ boundedPrimeFaces N, ∀ T ⊆ S, T ∈ boundedPrimeFaces N := by
  intro S hS T hTS
  exact mem_boundedPrimeFaces.mpr (primeSets_down_closed (mem_boundedPrimeFaces.mp hS)
    (Finset.map_subset_map.mpr hTS))

/-- Standard barycentric realization of the squarefree prime complex. -/
def primeComplexRealization (N : ℕ) := faceFamilySpace (boundedPrimeFaces N)

instance (N : ℕ) : TopologicalSpace (primeComplexRealization N) :=
  inferInstanceAs (TopologicalSpace (faceFamilySpace (boundedPrimeFaces N)))

def primeTwoVertex {N : ℕ} (hN : 2 ≤ N) : Fin (N + 1) := ⟨2, by omega⟩

theorem primeTwoVertex_mem {N : ℕ} (hN : 2 ≤ N) :
    {primeTwoVertex hN} ∈ boundedPrimeFaces N := by
  apply mem_boundedPrimeFaces.mpr
  rw [mem_primeSets_iff]
  simpa [primeFaceImage, primeTwoVertex] using And.intro Nat.prime_two hN

theorem primeFaceImage_insert {N : ℕ} (hN : 2 ≤ N) (S : Finset (Fin (N + 1))) :
    primeFaceImage (insert (primeTwoVertex hN) S) = insert 2 (primeFaceImage S) := by
  simp only [primeFaceImage, Finset.map_insert, primeTwoVertex, Fin.valEmbedding_apply]

theorem boundedPrimeFaces_star_iff {N : ℕ} (hN : 2 ≤ N) {S : Finset (Fin (N + 1))} :
    S ∈ faceStar (boundedPrimeFaces N) (primeTwoVertex hN) ↔
      primeFaceImage S ∈ primeTwoStar N := by
  rw [mem_faceStar, mem_boundedPrimeFaces, mem_boundedPrimeFaces,
    primeFaceImage_insert, mem_primeTwoStar_iff]
  exact and_iff_right_of_imp (fun h => primeSets_down_closed h (Finset.subset_insert 2 _))

theorem boundedPrimeFaces_proper_subface {N : ℕ} (hN : 2 ≤ N) :
    ∀ S ∈ complementaryFaces (boundedPrimeFaces N) (primeTwoVertex hN),
      ∀ T ⊂ S, T ∈ faceStar (boundedPrimeFaces N) (primeTwoVertex hN) := by
  intro S hS T hTS
  obtain ⟨hS, hstar⟩ := mem_complementaryFaces.mp hS
  rw [boundedPrimeFaces_star_iff] at hstar ⊢
  exact proper_subface_mem_primeTwoStar (mem_boundedPrimeFaces.mp hS) hstar
    (Finset.map_ssubset_map.mpr hTS)

/-- Finite relabeling identifies the complementary facets with their prime supports. -/
def boundedPrimeComplementEquiv {N : ℕ} (hN : 2 ≤ N) :
    complementaryFaces (boundedPrimeFaces N) (primeTwoVertex hN) ≃
      {S : Finset ℕ // S ∈ _root_.RHTower.primeSets N ∧ S ∉ primeTwoStar N} := by
  let f : complementaryFaces (boundedPrimeFaces N) (primeTwoVertex hN) →
      {S : Finset ℕ // S ∈ _root_.RHTower.primeSets N ∧ S ∉ primeTwoStar N} := fun S =>
    ⟨primeFaceImage S.val, mem_boundedPrimeFaces.mp (mem_complementaryFaces.mp S.property).1,
      fun h => (mem_complementaryFaces.mp S.property).2 ((boundedPrimeFaces_star_iff hN).mpr h)⟩
  apply Equiv.ofBijective f
  constructor
  · intro S T h
    exact Subtype.ext (Finset.map_injective Fin.valEmbedding (congrArg Subtype.val h))
  · intro T
    have hbound : ∀ p ∈ T.val, p < N + 1 := by
      have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp T.property.1).1
      exact fun p hp => Finset.mem_range.mp (hsub hp)
    let e : T.val ↪ Fin (N + 1) :=
      ⟨fun p => ⟨p.val, hbound p.val p.property⟩,
        fun p q he => Subtype.ext (congrArg Fin.val he)⟩
    let S := T.val.attach.map e
    have hSimage : primeFaceImage S = T.val := by
      ext p
      constructor
      · intro hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hp
        obtain ⟨q, _, hqi⟩ := Finset.mem_map.mp hi
        have hval : q.val = i.val := congrArg Fin.val hqi
        change i.val ∈ T.val
        rw [← hval]
        exact q.property
      · intro hp
        exact Finset.mem_map.mpr ⟨e ⟨p, hp⟩,
          Finset.mem_map.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩, rfl⟩
    have hS : S ∈ complementaryFaces (boundedPrimeFaces N) (primeTwoVertex hN) := by
      rw [mem_complementaryFaces, mem_boundedPrimeFaces, boundedPrimeFaces_star_iff, hSimage]
      exact T.property
    exact ⟨⟨S, hS⟩, Subtype.ext hSimage⟩

/-- Odd squarefree integers in the upper half-window. -/
abbrev PrimeSphereIndex (N : ℕ) :=
  {m : ℕ // 1 ≤ m ∧ m ≤ N ∧ Odd m ∧ Squarefree m ∧ N < 2 * m}

theorem primeSphereIndex_window (N m : ℕ) :
    (1 ≤ m ∧ m ≤ N ∧ Odd m ∧ Squarefree m ∧ N < 2 * m) ↔
      N / 2 < m ∧ m ≤ N ∧ Odd m ∧ Squarefree m := by
  constructor
  · rintro ⟨_, hm, ho, hs, h2⟩
    exact ⟨by omega, hm, ho, hs⟩
  · rintro ⟨h2, hm, ho, hs⟩
    exact ⟨by omega, hm, ho, hs, by omega⟩

instance (N : ℕ) : Finite (PrimeSphereIndex N) :=
  Finite.of_injective
    (fun m : PrimeSphereIndex N => (⟨m.val, Nat.lt_succ_of_le m.property.2.1⟩ : Fin (N + 1)))
    (fun _ _ h => Subtype.ext (congrArg Fin.val h))

def primeSphereIndexEquiv {N : ℕ} (hN : 2 ≤ N) :
    complementaryFaces (boundedPrimeFaces N) (primeTwoVertex hN) ≃ PrimeSphereIndex N :=
  (boundedPrimeComplementEquiv hN).trans (primeTwoComplementEquiv N)

theorem primeSphereIndex_primeFactors {N : ℕ} (hN : 2 ≤ N)
    (S : complementaryFaces (boundedPrimeFaces N) (primeTwoVertex hN)) :
    (primeSphereIndexEquiv hN S).val.primeFactors = primeFaceImage S.val := by
  exact Nat.primeFactors_prod
    (mem_primeSets_iff.mp (mem_boundedPrimeFaces.mp (mem_complementaryFaces.mp S.property).1)).1

theorem primeSphereIndex_card {N : ℕ} (hN : 2 ≤ N)
    (S : complementaryFaces (boundedPrimeFaces N) (primeTwoVertex hN)) :
    (primeSphereIndexEquiv hN S).val.primeFactors.card = S.val.card := by
  rw [primeSphereIndex_primeFactors]
  exact Finset.card_map _

/-- The unit sphere in `ℝ^ω(m)`, hence of dimension `ω(m)−1`. -/
abbrev PrimeSphere {N : ℕ} (m : PrimeSphereIndex N) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin m.val.primeFactors.card)) 1

def primeBoundarySphereHomeomorph {N : ℕ} (hN : 2 ≤ N)
    (S : complementaryFaces (boundedPrimeFaces N) (primeTwoVertex hN)) :
    FacetBoundary (primeTwoVertex hN) S.val ≃ₜ PrimeSphere (primeSphereIndexEquiv hN S) :=
  (boundaryReindex (Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, Fintype.card_fin, primeSphereIndex_card]
    simp [apex_not_mem_complementary S.property]))).trans
    (stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin (primeSphereIndexEquiv hN S).val.primeFactors.card) ℝ).symm)

/-- The basepoint of each sphere is the image of vertex two. -/
def primeSphereBase {N : ℕ} (hN : 2 ≤ N) : ∀ m : PrimeSphereIndex N, PrimeSphere m :=
  Equiv.piCongrLeft (fun m : PrimeSphereIndex N => PrimeSphere m) (primeSphereIndexEquiv hN)
    (fun S => primeBoundarySphereHomeomorph hN S (complementarySpherePoint (primeTwoVertex_mem hN) S))

theorem primeSphereBase_index {N : ℕ} (hN : 2 ≤ N)
    (S : complementaryFaces (boundedPrimeFaces N) (primeTwoVertex hN)) :
    primeBoundarySphereHomeomorph hN S (complementarySpherePoint (primeTwoVertex_mem hN) S) =
      primeSphereBase hN (primeSphereIndexEquiv hN S) := by
  exact (Equiv.piCongrLeft_apply_apply
    (fun m : PrimeSphereIndex N => PrimeSphere m) (primeSphereIndexEquiv hN)
    (fun T => primeBoundarySphereHomeomorph hN T
      (complementarySpherePoint (primeTwoVertex_mem hN) T)) S).symm

/-- The finite wedge indexed by odd squarefree `N/2<m≤N`. -/
abbrev PrimeSphereBouquet {N : ℕ} (hN : 2 ≤ N) :=
  BasedBouquet (fun m : PrimeSphereIndex N => PrimeSphere m) (primeSphereBase hN)

/-- Björner's decomposition, as an actual homotopy equivalence of spaces. -/
def primeComplexSphereBouquetHomotopyEquiv {N : ℕ} (hN : 2 ≤ N) :
    HomotopyEquiv (primeComplexRealization N) (PrimeSphereBouquet hN) :=
  (finiteConeComplexHomotopyEquiv (boundedPrimeFaces_down_closed N)
    (primeTwoVertex_mem hN) (boundedPrimeFaces_proper_subface hN)).trans
    (bouquetFamilyHomeomorph (primeSphereIndexEquiv hN)
      (complementarySpherePoint (primeTwoVertex_mem hN)) (primeSphereBase hN)
      (primeBoundarySphereHomeomorph hN) (primeSphereBase_index hN)).toHomotopyEquiv

/-- Below the first prime the realization is empty. -/
theorem primeComplexRealization_empty {N : ℕ} (hN : N < 2) :
    IsEmpty (primeComplexRealization N) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨S, hS, hxS⟩ := mem_faceFamilySpace.mp x.property
  have hSe : S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hp := (mem_primeSets_iff.mp (mem_boundedPrimeFaces.mp hS)).1 i.val
      (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
    have hil := i.isLt
    have := hp.two_le
    omega
  have hx0 : ∀ i, x.val.val i = 0 := by
    intro i
    exact hxS i (by simp only [hSe, Finset.notMem_empty, not_false_eq_true])
  have hs := x.val.property.2
  simp only [hx0, Finset.sum_const_zero] at hs
  exact zero_ne_one hs

#print axioms primeComplexSphereBouquetHomotopyEquiv
#print axioms primeComplexRealization_empty
#print axioms primeSphereIndex_card
end GaloisForLFunctions.HodgeTheoryWithoutVarieties
