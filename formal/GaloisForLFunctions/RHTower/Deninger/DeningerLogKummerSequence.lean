import GaloisForLFunctions.RHTower.Deninger.DeningerLogGroupSequence
import GaloisForLFunctions.RHTower.Deninger.DeningerSheafShortExact

/-!
# The Kummer sequence of the divisorial log structure

The sheaf of units, the groupified divisorial log structure of `P`, and the direct sum of the
skyscrapers `i_{p,*} ℤ` over `p ∈ P` form a short exact sequence of sheaves of abelian groups on the
arithmetic curve.  It is short exact over every open set — the first map is an inclusion of
sections, a section with vanishing valuations along `P` has all valuations zero, and every exponent
vector is the divisor of a product of prime powers — and objectwise short exactness of presheaves
gives short exactness of sheaves.

* `deningerLogKummerComplex` : the sequence.
* `deningerLogKummerComplex_shortExact` : it is short exact.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

/-- The inclusion of the sheaf of units into the groupified divisorial log structure. -/
def deningerUnitToGp (P : Finset Nat.Primes) :
    deningerUnitAddCond.presheaf ⟶ (deningerLogGpAddCond P).presheaf :=
  deningerUnitAddCond.incl (deningerLogGpAddCond P) (fun _ _ h p hxp _ => h p hxp)

/-- The valuations along `P`, as a morphism of presheaves. -/
def deningerGpResidueMap (P : Finset Nat.Primes) :
    (deningerLogGpAddCond P).presheaf ⟶ deningerResidueAddPresheaf P ℤ where
  app U := AddCommGrpCat.ofHom (deningerGpResidueHom P U.unop)
  naturality U V h := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
    funext i
    show padicValRat _ ((Additive.toMul _ : ℚˣ) : ℚ) = padicValRat _ ((Additive.toMul _ : ℚˣ) : ℚ)
    refine congrArg (fun z : Additive ℚˣ => padicValRat (((i : Nat.Primes) : ℕ))
      ((Additive.toMul z : ℚˣ) : ℚ)) ?_
    exact s.2.1 _ _

theorem deningerGpResidueMap_app_hom (P : Finset Nat.Primes)
    (U : (Opens deningerArithBase)ᵒᵖ) :
    ConcreteCategory.hom ((deningerGpResidueMap P).app U) = deningerGpResidueHom P U.unop := rfl

/-- **The Kummer sequence of the divisorial log structure**, as a complex of sheaves of abelian
groups. -/
def deningerLogKummerComplex (P : Finset Nat.Primes) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase) where
  X₁ := deningerUnitAddSheaf
  X₂ := deningerLogGpSheaf P
  X₃ := deningerResidueAddSheaf P ℤ
  f := ⟨deningerUnitToGp P⟩
  g := ⟨deningerGpResidueMap P⟩
  zero := by
    refine CategoryTheory.Sheaf.hom_ext ?_
    refine NatTrans.ext (funext fun U => ?_)
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
    funext i
    exact s.2.2 ⟨deningerClosedPt ((i : Nat.Primes)), i.2.2⟩ (i : Nat.Primes) rfl

/-- The inclusion of unit sections is injective. -/
theorem deningerUnitToGp_injective (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    Function.Injective (deningerUnitAddCond.inclSub (deningerLogGpAddCond P)
      (fun _ _ h p hxp _ => h p hxp) U) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun z : (deningerLogGpAddCond P).sub U =>
    (z : ↥U → Additive ℚˣ)) hab)

/-- Exactness in the middle, on sections. -/
theorem deningerLogKummer_exact_sections (P : Finset Nat.Primes) (U : Opens deningerArithBase)
    (s : (deningerLogGpAddCond P).sub U) (hs : deningerGpResidueHom P U s = 0) :
    ∃ t : deningerUnitAddCond.sub U,
      deningerUnitAddCond.inclSub (deningerLogGpAddCond P)
        (fun _ _ h p hxp _ => h p hxp) U t = s := by
  obtain hmem := (deningerGpResidue_eq_zero_iff s).1 hs
  exact ⟨⟨(s : ↥U → Additive ℚˣ), hmem⟩, Subtype.ext rfl⟩

/-- **The Kummer sequence is short exact.** -/
theorem deningerLogKummerComplex_shortExact (P : Finset Nat.Primes) :
    (deningerLogKummerComplex P).ShortExact := by
  refine deningerSheafShortExact_of_forget _ ?_
  refine deningerPresheafShortExact_of_app _ (fun U => ?_) (fun U => ?_) (fun U => ?_)
  · exact (AddCommGrpCat.mono_iff_injective _).2 (deningerUnitToGp_injective P U.unop)
  · exact (AddCommGrpCat.epi_iff_surjective _).2 (deningerGpResidue_surjective P U.unop)
  · rw [ShortComplex.ab_exact_iff]
    exact fun s hs => deningerLogKummer_exact_sections P U.unop s hs

end RHTower
