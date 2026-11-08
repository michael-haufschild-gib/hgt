import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeVertexSignedLocalization

/-!
# Arithmetic homotopy types of prime-vertex exits

The least upper neighbour is a conical star apex. Replacing a deleted
vertex by that least neighbour decreases the product, so all proper
subfaces of every complementary face lie in the star. The resulting
bouquet is an actual homotopy model of the local exit.
-/
noncomputable section
open Finset ContinuousMap
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open EffectiveScalingGeometry HodgeTheoryWithoutVarieties

/-- Actual vertices of the upper link. -/
def primeUpperVertices (B N : ℕ) (p : Fin (B+3)) : Finset (Fin (B+3)) :=
  univ.filter (fun q => {q}∈primeUpperLinkFaces B N p)

/-- The least available upper vertex; existence is decided by the finite link. -/
def primeUpperApex {B N : ℕ} (p : Fin (B+3))
    (h : (primeUpperVertices B N p).Nonempty) : Fin (B+3) :=
  (primeUpperVertices B N p).min' h

theorem primeUpperApex_mem {B N : ℕ} (p : Fin (B+3))
    (h : (primeUpperVertices B N p).Nonempty) :
    {primeUpperApex p h}∈primeUpperLinkFaces B N p :=
  (mem_filter.mp (min'_mem (primeUpperVertices B N p) h)).2

theorem primeUpperApex_le {B N : ℕ} (p : Fin (B+3))
    (h : (primeUpperVertices B N p).Nonempty) {S : Finset (Fin (B+3))}
    (hS : S∈primeUpperLinkFaces B N p) {q : Fin (B+3)} (hq : q∈S) :
    primeUpperApex p h≤q :=
  min'_le _ q (mem_filter.mpr ⟨mem_univ _,
    primeUpperLink_down_closed B N p S hS {q} (singleton_subset_iff.mpr hq)⟩)

/-- Replacing a removed vertex by the least upper prime preserves the product bound. -/
theorem primeUpperLink_proper_subface {B N : ℕ} (p : Fin (B+3))
    (h : (primeUpperVertices B N p).Nonempty) :
    ∀S∈complementaryFaces (primeUpperLinkFaces B N p) (primeUpperApex p h),
      ∀T⊂S,T∈faceStar (primeUpperLinkFaces B N p) (primeUpperApex p h) := by
  intro S hS T hTS
  let a := primeUpperApex p h
  have hSK := (mem_complementaryFaces.mp hS).1
  have haS : a∉S := apex_not_mem_complementary hS
  have hST := (mem_filter.mp hSK).2
  have haK := (mem_filter.mp (primeUpperApex_mem p h)).2
  have hpa : p<a := haK.1 a (mem_singleton_self a)
  have haPrime : a.val.Prime := (mem_primeHeightFaces.mp haK.2).1 a
    (mem_insert_of_mem (mem_singleton_self a))
  have hpPrime : p.val.Prime := (mem_primeHeightFaces.mp hST.2).1 p (mem_insert_self p S)
  have hT := primeUpperLink_down_closed B N p S hSK T hTS.le
  obtain ⟨q,hqS,hqT⟩ := exists_of_ssubset hTS
  have haq : a≤q := primeUpperApex_le p h hSK hqS
  have hpq : p<q := hST.1 q hqS
  have hpT : p∉T := fun hp => (lt_irrefl p) (hST.1 p (hTS.le hp))
  have haT : a∉T := fun ha => haS (hTS.le ha)
  have hqbound := (mem_primeHeightFaces.mp ((mem_filter.mp
    (primeUpperLink_down_closed B N p S hSK (insert q T)
      (insert_subset hqS hTS.le))).2.2)).2
  have hpqT : p∉insert q T := by
    simp only [mem_insert,not_or]
    exact ⟨ne_of_lt hpq,hpT⟩
  rw [prod_insert hpqT,prod_insert hqT] at hqbound
  apply mem_faceStar.mpr
  refine ⟨hT,mem_filter.mpr ⟨mem_univ _,?_,?_⟩⟩
  · intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact hpa
    · exact hST.1 r (hTS.le hr)
  · apply mem_primeHeightFaces.mpr
    constructor
    · intro r hr
      rcases mem_insert.mp hr with rfl | hr
      · exact hpPrime
      · rcases mem_insert.mp hr with rfl | hr
        · exact haPrime
        · exact (mem_primeHeightFaces.mp hST.2).1 r (mem_insert_of_mem (hTS.le hr))
    · have hpaT : p∉insert a T := by
        simp only [mem_insert,not_or]
        exact ⟨ne_of_lt hpa,hpT⟩
      rw [prod_insert hpaT,prod_insert haT]
      exact (Nat.mul_le_mul_left p.val (Nat.mul_le_mul_right (∏r∈T,r.val) haq)).trans hqbound

/-- The exit has an actual bouquet model whenever it has a vertex. -/
def primeExitBouquetEquiv {B N : ℕ} (p : Fin (B+3))
    (h : (primeUpperVertices B N p).Nonempty) :
    primeVertexExit B N p ≃ₕ ConeBouquet (primeUpperApex_mem p h) :=
  (primeExitLinkHomotopyEquiv B N p).trans
    (finiteConeComplexHomotopyEquiv (primeUpperLink_down_closed B N p)
      (primeUpperApex_mem p h) (primeUpperLink_proper_subface p h))

/-- Without upper vertices the actual exit is empty. -/
theorem primeExit_isEmpty_of_no_upperVertex {B N : ℕ} (p : Fin (B+3))
    (h : ¬(primeUpperVertices B N p).Nonempty) : IsEmpty (primeVertexExit B N p) := by
  have hempty : IsEmpty (faceFamilySpace (primeUpperLinkFaces B N p)) := ⟨fun x => by
    have hx : x∈⋃q,faceStarIntersection (primeUpperLinkFaces B N p) {q} := by
      rw [faceVertexStars_cover]
      trivial
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hx
    have hqK := faceStarIntersection_face (primeUpperLink_down_closed B N p) ⟨x,hq⟩
    exact h ⟨q,mem_filter.mpr ⟨mem_univ _,hqK⟩⟩⟩
  exact ⟨fun x => hempty.false ((primeExitLinkHomotopyEquiv B N p).toFun x)⟩

/-- Every arithmetic local exit is empty or has a proved finite sphere-bouquet model. -/
theorem primeExit_bouquet_or_empty (B N : ℕ) (p : Fin (B+3)) :
    (∃a,∃ha : {a}∈primeUpperLinkFaces B N p,
      Nonempty (primeVertexExit B N p ≃ₕ ConeBouquet ha)) ∨ IsEmpty (primeVertexExit B N p) := by
  by_cases h : (primeUpperVertices B N p).Nonempty
  · exact Or.inl ⟨primeUpperApex p h,primeUpperApex_mem p h,⟨primeExitBouquetEquiv p h⟩⟩
  · exact Or.inr (primeExit_isEmpty_of_no_upperVertex p h)

/-- Upper faces are specified by primes, strict order, and one integer product bound. -/
theorem mem_primeUpperLinkFaces_arithmetic (B N : ℕ) (p : Fin (B+3))
    (S : Finset (Fin (B+3))) :
    S∈primeUpperLinkFaces B N p ↔ p.val.Prime ∧
      (∀q∈S,p<q ∧ q.val.Prime) ∧ p.val*(∏q∈S,q.val)≤N := by
  constructor
  · intro hS
    have h := (mem_filter.mp hS).2
    have hf := mem_primeHeightFaces.mp h.2
    have hpS : p∉S := fun hp => (lt_irrefl p) (h.1 p hp)
    refine ⟨hf.1 p (mem_insert_self p S),fun q hq =>
      ⟨h.1 q hq,hf.1 q (mem_insert_of_mem hq)⟩,?_⟩
    simpa only [prod_insert hpS] using hf.2
  · rintro ⟨hp,hs,hbound⟩
    refine mem_filter.mpr ⟨mem_univ _,fun q hq => (hs q hq).1,?_⟩
    apply mem_primeHeightFaces.mpr
    constructor
    · intro q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact hp
      · exact (hs q hq).2
    · have hpS : p∉S := fun h => (lt_irrefl p) (hs p h).1
      rw [prod_insert hpS]
      exact hbound

/-- Sphere labels are exactly rough prime supports in the multiplicative window selected by the least neighbour. -/
theorem primeExit_bouquet_window {B N : ℕ} (p : Fin (B+3))
    (h : (primeUpperVertices B N p).Nonempty) (S : Finset (Fin (B+3))) :
    S∈complementaryFaces (primeUpperLinkFaces B N p) (primeUpperApex p h) ↔
      (∀q∈S,primeUpperApex p h<q ∧ q.val.Prime) ∧
      p.val*(∏q∈S,q.val)≤N ∧ N<p.val*((primeUpperApex p h).val*(∏q∈S,q.val)) := by
  let a := primeUpperApex p h
  have ha := (mem_primeUpperLinkFaces_arithmetic B N p {a}).mp (primeUpperApex_mem p h)
  have hpa : p<a := (ha.2.1 a (mem_singleton_self a)).1
  have haPrime : a.val.Prime := (ha.2.1 a (mem_singleton_self a)).2
  constructor
  · intro hS
    have hSK := (mem_complementaryFaces.mp hS).1
    have hd := (mem_primeUpperLinkFaces_arithmetic B N p S).mp hSK
    have haS : a∉S := apex_not_mem_complementary hS
    refine ⟨?_,hd.2.2,?_⟩
    · intro q hq
      have hqa : q≠a := fun he => haS (he ▸ hq)
      exact ⟨lt_of_le_of_ne (primeUpperApex_le p h hSK hq) hqa.symm,(hd.2.1 q hq).2⟩
    · by_contra hn
      have hb : p.val*(a.val*(∏q∈S,q.val))≤N := Nat.le_of_not_gt hn
      apply (mem_complementaryFaces.mp hS).2
      refine mem_faceStar.mpr ⟨hSK,(mem_primeUpperLinkFaces_arithmetic B N p (insert a S)).mpr
        ⟨ha.1,?_,?_⟩⟩
      · intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · exact ⟨hpa,haPrime⟩
        · exact hd.2.1 q hq
      · rw [prod_insert haS]
        exact hb
  · rintro ⟨hs,hbound,hlarge⟩
    have hSK := (mem_primeUpperLinkFaces_arithmetic B N p S).mpr
      ⟨ha.1,fun q hq => ⟨hpa.trans (hs q hq).1,(hs q hq).2⟩,hbound⟩
    refine mem_complementaryFaces.mpr ⟨hSK,?_⟩
    intro hstar
    have hb := ((mem_primeUpperLinkFaces_arithmetic B N p (insert a S)).mp
      (mem_faceStar.mp hstar).2).2.2
    have haS : a∉S := fun haS => (lt_irrefl a) (hs a haS).1
    rw [prod_insert haS] at hb
    exact (not_lt_of_ge hb) hlarge

#print axioms primeExit_bouquet_window

#print axioms primeUpperLink_proper_subface
#print axioms primeExitBouquetEquiv
#print axioms primeExit_bouquet_or_empty
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
