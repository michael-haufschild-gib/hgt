import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCechComplex
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! An exact coefficient test descends to an injective map on cohomology. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits HTGeometry

namespace GlobalTheory.SchemeCohomology

universe u

variable {ι : Type u} [DecidableEq ι] [LinearOrder ι]
  {D E : FinsetCechDatum.{u} ι}

/-- An isomorphism on the nonempty intersections is degreewise bijective on
the unaugmented complexes. -/
theorem cochainMap_bijective_of_nonempty (f : D.Hom E)
    (hf : ∀ a : Finset ι, a.Nonempty → Function.Bijective (f.app a)) (n : ℕ) :
    Function.Bijective (f.cochainMap.f n) := by
  constructor
  · intro x y h
    apply Subtype.ext
    funext a
    by_cases ha : a.card = n + 1
    · exact (hf a (Finset.card_pos.mp (by omega))).1 (congrFun (congrArg Subtype.val h) a)
    · exact (x.2 a ha).trans (y.2 a ha).symm
  · intro y
    have h (a : Finset ι) (ha : a.card = n + 1) : ∃ z, f.app a z = y.1 a :=
      (hf a (Finset.card_pos.mp (by omega))).2 _
    choose z hz using h
    let x : D.Cochain := fun a => if ha : a.card = n + 1 then z a ha else 0
    refine ⟨⟨x, fun a ha => dif_neg ha⟩, Subtype.ext (funext fun a => ?_)⟩
    change f.app a (x a) = y.1 a
    by_cases ha : a.card = n + 1
    · simpa only [x, dif_pos ha] using hz a ha
    · simp only [x, dif_neg ha, map_zero, y.2 a ha]

variable (S : ShortComplex AddCommGrpCat.{u}) {A : AddCommGrpCat.{u}} (g : S.X₂ ⟶ A)

private theorem exact_coefficient_zero (h : Function.Exact S.f g) :
    S.toCycles ≫ S.iCycles ≫ g = 0 := by
  rw [← Category.assoc, S.toCycles_i]
  apply AddCommGrpCat.ext
  intro x
  exact (h (S.f x)).mpr ⟨x, rfl⟩

/-- A coefficient map with kernel equal to the boundaries descends to homology. -/
def descHomologyOfExact (h : Function.Exact S.f g) : S.homology ⟶ A :=
  S.descHomology (S.iCycles ≫ g) (exact_coefficient_zero S g h)

@[reassoc]
theorem homologyπ_descHomologyOfExact (h : Function.Exact S.f g) :
    S.homologyπ ≫ descHomologyOfExact S g h = S.iCycles ≫ g :=
  S.π_descHomology _ _

theorem descHomologyOfExact_injective (h : Function.Exact S.f g) :
    Function.Injective (descHomologyOfExact S g h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective S.homologyπ).mp inferInstance x
  have hz := (ConcreteCategory.congr_hom (homologyπ_descHomologyOfExact S g h) z).symm.trans hx
  obtain ⟨b, hb⟩ := (h (S.iCycles z)).mp hz
  have he : S.toCycles b = z := by
    apply (AddCommGrpCat.mono_iff_injective S.iCycles).mp inferInstance
    exact (ConcreteCategory.congr_hom S.toCycles_i b).trans hb
  rw [← he]
  exact ConcreteCategory.congr_hom S.toCycles_comp_homologyπ b

theorem descHomologyOfExact_natural (h : Function.Exact S.f g) (m : S ⟶ S)
    (r : A ⟶ A) (hc : m.τ₂ ≫ g = g ≫ r) :
    ShortComplex.homologyMap m ≫ descHomologyOfExact S g h =
      descHomologyOfExact S g h ≫ r := by
  apply (cancel_epi S.homologyπ).mp
  rw [← Category.assoc, ShortComplex.homologyπ_naturality, Category.assoc,
    homologyπ_descHomologyOfExact, ← Category.assoc, ShortComplex.cyclesMap_i,
    Category.assoc, hc, ← Category.assoc, ← homologyπ_descHomologyOfExact, Category.assoc]

end GlobalTheory.SchemeCohomology
