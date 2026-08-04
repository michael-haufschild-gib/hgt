import GaloisForLFunctions.RHTower.DeningerFlasqueAcyclic
import GaloisForLFunctions.RHTower.DeningerRestrictedPrimeGluing
import GaloisForLFunctions.RHTower.DeningerArithCurvePoints

/-!
# The restricted prime sum is an acyclic sheaf

The restricted prime sum, whose sections over an arithmetic open are the prime-indexed families
supported there and satisfying the two weighted summability conditions, is a sheaf of abelian
groups: gluing is the unique-gluing statement already proved.  It is flasque, because extension by
zero is a section of coordinate deletion, and therefore it has no higher cohomology.  So its derived
global sections are concentrated in degree zero, where they are the restricted sum itself.

* `deningerPrimeSheaf` : the restricted prime sum as a sheaf of abelian groups.
* `deningerPrimeSheaf_isFlasque` : it is flasque.
* `deningerPrimeSheaf_ext_eq_zero` : it has no higher cohomology.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

section PrimeSheaf

variable {E : Nat.Primes → Type} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
variable (n1 n2 : ∀ p, Seminorm ℝ (E p)) (α β : Nat.Primes → NNReal)

/-- Coordinate deletion as a homomorphism of sections. -/
noncomputable def deningerPrimeRestrictHom (U V : Opens (PrimeSpectrum ℤ)) :
    deningerPrimeSections n1 n2 α β U →+ deningerPrimeSections n1 n2 α β V where
  toFun s := ⟨deningerPrimeRestrict V ((s : ∀ p, E p)), deningerPrimeRestrict_mem s.2⟩
  map_zero' := by
    refine Subtype.ext (funext fun p => ?_)
    show deningerPrimeRestrict V ((0 : deningerPrimeSections n1 n2 α β U) : ∀ q, E q) p = 0
    by_cases hp : p ∈ deningerPrimeIndex V
    · rw [deningerPrimeRestrict_of_mem hp]
      rfl
    · rw [deningerPrimeRestrict_of_notMem hp]
  map_add' s t := by
    refine Subtype.ext (funext fun p => ?_)
    show deningerPrimeRestrict V ((s + t : deningerPrimeSections n1 n2 α β U) : ∀ q, E q) p
      = deningerPrimeRestrict V ((s : ∀ q, E q)) p + deningerPrimeRestrict V ((t : ∀ q, E q)) p
    by_cases hp : p ∈ deningerPrimeIndex V
    · rw [deningerPrimeRestrict_of_mem hp, deningerPrimeRestrict_of_mem hp,
        deningerPrimeRestrict_of_mem hp]
      rfl
    · rw [deningerPrimeRestrict_of_notMem hp, deningerPrimeRestrict_of_notMem hp,
        deningerPrimeRestrict_of_notMem hp, add_zero]

/-- **The restricted prime sum as a presheaf of abelian groups.** -/
noncomputable def deningerPrimePresheaf :
    TopCat.Presheaf AddCommGrpCat.{0} deningerArithBase where
  obj U := AddCommGrpCat.of (deningerPrimeSections n1 n2 α β U.unop)
  map {U V} _ := AddCommGrpCat.ofHom (deningerPrimeRestrictHom n1 n2 α β U.unop V.unop)
  map_id U := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => Subtype.ext (funext fun p => ?_))
    show deningerPrimeRestrict U.unop ((s : ∀ q, E q)) p = (s : ∀ q, E q) p
    by_cases hp : p ∈ deningerPrimeIndex U.unop
    · exact deningerPrimeRestrict_of_mem hp
    · rw [deningerPrimeRestrict_of_notMem hp]
      exact (s.2.1 p hp).symm
  map_comp {U V W} i j := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => Subtype.ext (funext fun p => ?_))
    show deningerPrimeRestrict W.unop ((s : ∀ q, E q)) p
      = deningerPrimeRestrict W.unop (deningerPrimeRestrict V.unop ((s : ∀ q, E q))) p
    by_cases hp : p ∈ deningerPrimeIndex W.unop
    · rw [deningerPrimeRestrict_of_mem hp, deningerPrimeRestrict_of_mem hp,
        deningerPrimeRestrict_of_mem (deningerPrimeIndex_mono (leOfHom j.unop) hp)]
    · rw [deningerPrimeRestrict_of_notMem hp, deningerPrimeRestrict_of_notMem hp]

theorem deningerPrimePresheaf_hom {U V : (Opens deningerArithBase)ᵒᵖ} (i : U ⟶ V) :
    ConcreteCategory.hom ((deningerPrimePresheaf n1 n2 α β).map i) =
      deningerPrimeRestrictHom n1 n2 α β U.unop V.unop := rfl

/-- The underlying family of a section. -/
def deningerPrimeVal {U : Opens (PrimeSpectrum ℤ)}
    (s : deningerPrimeSections n1 n2 α β U) : ∀ p, E p := s

/-- The primes of an intersection are the primes common to both. -/
theorem deningerPrimeIndex_inf {U V : Opens (PrimeSpectrum ℤ)} {p : Nat.Primes} :
    p ∈ deningerPrimeIndex (U ⊓ V) ↔
      p ∈ deningerPrimeIndex U ∧ p ∈ deningerPrimeIndex V := Iff.rfl

/-- **The restricted prime sum is a sheaf.** -/
theorem deningerPrimePresheaf_isSheaf : (deningerPrimePresheaf n1 n2 α β).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  have hcompat' : ∀ i j, ∀ p, p ∈ deningerPrimeIndex (U i) → p ∈ deningerPrimeIndex (U j) →
      deningerPrimeVal n1 n2 α β (sf i) p = deningerPrimeVal n1 n2 α β (sf j) p := by
    intro i j p hpi hpj
    have h := hcompat i j
    rw [deningerPrimePresheaf_hom, deningerPrimePresheaf_hom] at h
    have h' := congrArg (fun z : deningerPrimeSections n1 n2 α β (U i ⊓ U j) =>
      deningerPrimeVal n1 n2 α β z p) h
    have hmem : p ∈ deningerPrimeIndex (U i ⊓ U j) := ⟨hpi, hpj⟩
    have hL : deningerPrimeVal n1 n2 α β
        (deningerPrimeRestrictHom n1 n2 α β (U i) (U i ⊓ U j) (sf i)) p =
        deningerPrimeVal n1 n2 α β (sf i) p :=
      deningerPrimeRestrict_of_mem hmem
    have hR : deningerPrimeVal n1 n2 α β
        (deningerPrimeRestrictHom n1 n2 α β (U j) (U i ⊓ U j) (sf j)) p =
        deningerPrimeVal n1 n2 α β (sf j) p :=
      deningerPrimeRestrict_of_mem hmem
    rw [← hL, ← hR]
    exact h'
  obtain ⟨g, ⟨hgmem, hgres⟩, huniq⟩ :=
    deningerPrimeSections_unique_gluing (n1 := n1) (n2 := n2) (α := α) (β := β) U
      (fun i => deningerPrimeVal n1 n2 α β (sf i)) (fun i => (sf i).2) hcompat'
  refine ⟨(⟨g, hgmem⟩ : deningerPrimeSections n1 n2 α β (iSup U)), ?_, ?_⟩
  · intro i
    rw [deningerPrimePresheaf_hom]
    exact Subtype.ext (hgres i)
  · intro t ht
    refine Subtype.ext ?_
    refine huniq (deningerPrimeVal n1 n2 α β t) ⟨t.2, fun i => ?_⟩
    have h := ht i
    rw [deningerPrimePresheaf_hom] at h
    exact congrArg (fun z : deningerPrimeSections n1 n2 α β (U i) =>
      deningerPrimeVal n1 n2 α β z) h

/-- **The restricted prime sum as a sheaf of abelian groups.** -/
noncomputable def deningerPrimeSheaf : TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase :=
  ⟨deningerPrimePresheaf n1 n2 α β, deningerPrimePresheaf_isSheaf n1 n2 α β⟩

/-- **The restricted prime sum is flasque**: extension by zero is a section of coordinate
deletion. -/
theorem deningerPrimeSheaf_isFlasque :
    TopCat.Sheaf.IsFlasque (deningerPrimeSheaf n1 n2 α β) := by
  constructor
  intro U V i
  refine (AddCommGrpCat.epi_iff_surjective _).2 (fun g => ?_)
  obtain ⟨f, hf, hfg⟩ := deningerPrimeSections_restrict_surjective (leOfHom i.unop) g.2
  refine ⟨(⟨f, hf⟩ : deningerPrimeSections n1 n2 α β U.unop), ?_⟩
  show ConcreteCategory.hom ((deningerPrimePresheaf n1 n2 α β).map i)
    (⟨f, hf⟩ : deningerPrimeSections n1 n2 α β U.unop) = g
  rw [deningerPrimePresheaf_hom]
  exact Subtype.ext hfg

variable [CategoryTheory.HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase)]

/-- **The restricted prime sum has no higher cohomology**, so its derived global sections are
concentrated in degree zero. -/
theorem deningerPrimeSheaf_ext_eq_zero (U : Opens deningerArithBase) (n : ℕ)
    (x : deningerSheafCohomology.{0} U (deningerPrimeSheaf n1 n2 α β) (n + 1)) : x = 0 :=
  deningerFlasque_ext_eq_zero n (deningerPrimeSheaf n1 n2 α β)
    (deningerPrimeSheaf_isFlasque n1 n2 α β) U x

/-- **Derived sections of the restricted prime sum are the restricted prime sum.** -/
noncomputable def deningerPrimeSheaf_cohomologyZeroEquiv (U : Opens deningerArithBase) :
    deningerSheafCohomology.{0} U (deningerPrimeSheaf n1 n2 α β) 0 ≃
      deningerPrimeSections n1 n2 α β U :=
  deningerSheafCohomologyZeroEquiv U (deningerPrimeSheaf n1 n2 α β)

end PrimeSheaf

end RHTower
