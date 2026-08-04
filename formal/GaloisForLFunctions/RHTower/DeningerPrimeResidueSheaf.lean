import GaloisForLFunctions.RHTower.DeningerArithLogSheaves

/-!
# The direct sum of skyscrapers along a finite set of primes

The sheaf `⨁_{p ∈ P} i_{p,*} A` on the arithmetic curve has as sections over an open set the
functions on the primes of `P` lying in that set.  It is a sheaf: a compatible family on a cover
prescribes one value at each prime of the union, because each such prime lies in some member of the
cover and the values agree on overlaps.

* `deningerResidueMulPresheaf`, `deningerResidueAddPresheaf` : the presheaves.
* `deningerResidueMulSheaf`, `deningerResidueAddSheaf` : the sheaves.
-/

namespace RHTower

open TopologicalSpace CategoryTheory Opposite TopCat

/-- Restriction of a residue section to a smaller open set. -/
def deningerResidueRes {A : Type} {P : Finset Nat.Primes} {U V : Opens deningerArithBase}
    (h : U ≤ V) (f : deningerLogIdx P V → A) : deningerLogIdx P U → A :=
  fun i => f ⟨i.1, i.2.1, h i.2.2⟩

/-- **Residue sections glue uniquely**: a prime of the union lies in some member of the cover, and
the prescribed values agree there. -/
theorem deningerResidue_existsUnique_gluing {A : Type} {P : Finset Nat.Primes} {ι : Type}
    (U : ι → Opens deningerArithBase) (f : ∀ i, deningerLogIdx P (U i) → A)
    (hcompat : ∀ i j (p : Nat.Primes) (hP : p ∈ P) (hi : deningerClosedPt p ∈ U i)
      (hj : deningerClosedPt p ∈ U j), f i ⟨p, hP, hi⟩ = f j ⟨p, hP, hj⟩) :
    ∃! s : deningerLogIdx P (iSup U) → A,
      ∀ i (p : Nat.Primes) (hP : p ∈ P) (hi : deningerClosedPt p ∈ U i),
        s ⟨p, hP, Opens.mem_iSup.2 ⟨i, hi⟩⟩ = f i ⟨p, hP, hi⟩ := by
  classical
  refine ⟨fun q => f (Opens.mem_iSup.1 q.2.2).choose
    ⟨q.1, q.2.1, (Opens.mem_iSup.1 q.2.2).choose_spec⟩, ?_, ?_⟩
  · intro i p hP hi
    have h2 : deningerClosedPt p ∈ iSup U := Opens.mem_iSup.2 ⟨i, hi⟩
    exact hcompat (Opens.mem_iSup.1 h2).choose i p hP (Opens.mem_iSup.1 h2).choose_spec hi
  · intro t ht
    funext q
    exact ht (Opens.mem_iSup.1 q.2.2).choose q.1 q.2.1
      (Opens.mem_iSup.1 q.2.2).choose_spec

section Mul

variable (P : Finset Nat.Primes) (A : Type) [CommMonoid A]

/-- Restriction of residue sections, as a monoid homomorphism. -/
def deningerResidueMulRes {U V : Opens deningerArithBase} (h : U ≤ V) :
    (deningerLogIdx P V → A) →* (deningerLogIdx P U → A) where
  toFun f := deningerResidueRes h f
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The direct sum of the skyscrapers `i_{p,*} A` for `p ∈ P`**, as a presheaf of commutative
monoids. -/
def deningerResidueMulPresheaf : TopCat.Presheaf CommMonCat.{0} deningerArithBase where
  obj U := CommMonCat.of (deningerLogIdx P U.unop → A)
  map h := CommMonCat.ofHom (deningerResidueMulRes P A (leOfHom h.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

theorem deningerResidueMulPresheaf_hom {U V : (Opens deningerArithBase)ᵒᵖ} (h : U ⟶ V) :
    ConcreteCategory.hom ((deningerResidueMulPresheaf P A).map h) =
      deningerResidueMulRes P A (leOfHom h.unop) := rfl

theorem deningerResidueMulPresheaf_isSheaf : (deningerResidueMulPresheaf P A).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  have hcompat' : ∀ i j (p : Nat.Primes) (hP : p ∈ P) (hi : deningerClosedPt p ∈ U i)
      (hj : deningerClosedPt p ∈ U j),
      (sf i : deningerLogIdx P (U i) → A) ⟨p, hP, hi⟩ =
        (sf j : deningerLogIdx P (U j) → A) ⟨p, hP, hj⟩ := by
    intro i j p hP hi hj
    have h := hcompat i j
    rw [deningerResidueMulPresheaf_hom, deningerResidueMulPresheaf_hom] at h
    exact congrFun h ⟨p, hP, ⟨hi, hj⟩⟩
  obtain ⟨s, hs, huniq⟩ :=
    deningerResidue_existsUnique_gluing (A := A) (P := P) U
      (fun i => (sf i : deningerLogIdx P (U i) → A)) hcompat'
  have hgoal : ∀ t : deningerLogIdx P (iSup U) → A,
      (∀ i, ConcreteCategory.hom
          ((deningerResidueMulPresheaf P A).map (Opens.leSupr U i).op) t = sf i) ↔
        ∀ i (p : Nat.Primes) (hP : p ∈ P) (hi : deningerClosedPt p ∈ U i),
          t ⟨p, hP, Opens.mem_iSup.2 ⟨i, hi⟩⟩ =
            (sf i : deningerLogIdx P (U i) → A) ⟨p, hP, hi⟩ := by
    intro t
    constructor
    · intro h i p hP hi
      have h1 := h i
      rw [deningerResidueMulPresheaf_hom] at h1
      exact congrFun h1 ⟨p, hP, hi⟩
    · intro h i
      rw [deningerResidueMulPresheaf_hom]
      funext q
      exact h i q.1 q.2.1 q.2.2
  refine ⟨s, (hgoal s).2 hs, ?_⟩
  intro t ht
  have ht' : ∀ i, ConcreteCategory.hom
      ((deningerResidueMulPresheaf P A).map (Opens.leSupr U i).op) t = sf i := ht
  exact huniq t ((hgoal t).1 ht')

/-- **The direct sum of the skyscrapers `i_{p,*} A` for `p ∈ P`**, as a sheaf. -/
def deningerResidueMulSheaf : TopCat.Sheaf CommMonCat.{0} deningerArithBase :=
  ⟨deningerResidueMulPresheaf P A, deningerResidueMulPresheaf_isSheaf P A⟩

end Mul

section Add

variable (P : Finset Nat.Primes) (A : Type) [AddCommGroup A]

/-- Restriction of residue sections, as a group homomorphism. -/
def deningerResidueAddRes {U V : Opens deningerArithBase} (h : U ≤ V) :
    (deningerLogIdx P V → A) →+ (deningerLogIdx P U → A) where
  toFun f := deningerResidueRes h f
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The direct sum of the skyscrapers `i_{p,*} A` for `p ∈ P`**, as a presheaf of abelian
groups. -/
def deningerResidueAddPresheaf : TopCat.Presheaf AddCommGrpCat.{0} deningerArithBase where
  obj U := AddCommGrpCat.of (deningerLogIdx P U.unop → A)
  map h := AddCommGrpCat.ofHom (deningerResidueAddRes P A (leOfHom h.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

theorem deningerResidueAddPresheaf_hom {U V : (Opens deningerArithBase)ᵒᵖ} (h : U ⟶ V) :
    ConcreteCategory.hom ((deningerResidueAddPresheaf P A).map h) =
      deningerResidueAddRes P A (leOfHom h.unop) := rfl

theorem deningerResidueAddPresheaf_isSheaf : (deningerResidueAddPresheaf P A).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  have hcompat' : ∀ i j (p : Nat.Primes) (hP : p ∈ P) (hi : deningerClosedPt p ∈ U i)
      (hj : deningerClosedPt p ∈ U j),
      (sf i : deningerLogIdx P (U i) → A) ⟨p, hP, hi⟩ =
        (sf j : deningerLogIdx P (U j) → A) ⟨p, hP, hj⟩ := by
    intro i j p hP hi hj
    have h := hcompat i j
    rw [deningerResidueAddPresheaf_hom, deningerResidueAddPresheaf_hom] at h
    exact congrFun h ⟨p, hP, ⟨hi, hj⟩⟩
  obtain ⟨s, hs, huniq⟩ :=
    deningerResidue_existsUnique_gluing (A := A) (P := P) U
      (fun i => (sf i : deningerLogIdx P (U i) → A)) hcompat'
  have hgoal : ∀ t : deningerLogIdx P (iSup U) → A,
      (∀ i, ConcreteCategory.hom
          ((deningerResidueAddPresheaf P A).map (Opens.leSupr U i).op) t = sf i) ↔
        ∀ i (p : Nat.Primes) (hP : p ∈ P) (hi : deningerClosedPt p ∈ U i),
          t ⟨p, hP, Opens.mem_iSup.2 ⟨i, hi⟩⟩ =
            (sf i : deningerLogIdx P (U i) → A) ⟨p, hP, hi⟩ := by
    intro t
    constructor
    · intro h i p hP hi
      have h1 := h i
      rw [deningerResidueAddPresheaf_hom] at h1
      exact congrFun h1 ⟨p, hP, hi⟩
    · intro h i
      rw [deningerResidueAddPresheaf_hom]
      funext q
      exact h i q.1 q.2.1 q.2.2
  refine ⟨s, (hgoal s).2 hs, ?_⟩
  intro t ht
  have ht' : ∀ i, ConcreteCategory.hom
      ((deningerResidueAddPresheaf P A).map (Opens.leSupr U i).op) t = sf i := ht
  exact huniq t ((hgoal t).1 ht')

/-- **The direct sum of the skyscrapers `i_{p,*} A` for `p ∈ P`**, as a sheaf of abelian groups. -/
def deningerResidueAddSheaf : TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase :=
  ⟨deningerResidueAddPresheaf P A, deningerResidueAddPresheaf_isSheaf P A⟩

end Add

end RHTower
