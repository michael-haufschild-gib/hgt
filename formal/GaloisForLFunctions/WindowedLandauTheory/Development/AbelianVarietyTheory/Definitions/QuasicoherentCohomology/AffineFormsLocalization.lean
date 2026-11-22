import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFormTrace
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.BaseChange

/-! Relative forms on section rings localize along affine basic opens. -/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {s : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens}

private abbrev basicOpenRestriction (g : SectionRing s U) :=
  sectionRes s (homOfLE (X.basicOpen_le (U := U) g))

/-- Forms on a basic open have a power of its defining section as a common denominator. -/
theorem formsOn_basicOpen (hU : IsAffineOpen U) (g : SectionRing s U) (n : ℕ) :
    (∀ y : FormsOn s (X.basicOpen g) n, ∃ (m : ℕ) (x : FormsOn s U n),
      (basicOpenRestriction g g) ^ m • y = ExteriorDifferentials.map (basicOpenRestriction g) n x) ∧
    ∀ x : FormsOn s U n, ExteriorDifferentials.map (basicOpenRestriction g) n x = 0 →
      ∃ m : ℕ, g ^ m • x = 0 := by
  let A := SectionRing s U
  let B := SectionRing s (X.basicOpen g)
  let r : A →ₐ[k] B := basicOpenRestriction g
  letI : Algebra A B := r.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun c => (r.commutes c).symm
  letI : IsLocalization.Away g B := hU.isLocalization_basicOpen g
  letI : Algebra.FormallyEtale A B := .of_isLocalization (Submonoid.powers g)
  let L := algebraFormPullback k A B n
  have hL : ∀ x, L x = ExteriorDifferentials.map r n x :=
    algebraFormPullback_eq_map k A B r rfl n
  letI : IsLocalizedModule (Submonoid.powers g) L :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) B L).2
      (algebraFormPullback_isBaseChange k A B n)
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  · obtain ⟨⟨x, _, m, rfl⟩, h⟩ := IsLocalizedModule.surj (Submonoid.powers g) L y
    refine ⟨m, x, ?_⟩
    rw [← hL, ← h, ← map_pow]
    exact IsScalarTower.algebraMap_smul B (g ^ m) y
  · have hx' : L x = 0 := (hL x).trans hx
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g) L).1 hx'
    exact ⟨m, hm⟩

end GlobalTheory.SchemeCohomology
