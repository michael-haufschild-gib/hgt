import GaloisForLFunctions.RHTower.CHMDCriticalBandReduction
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The arithmetic graph modulo its signed radical

The literal quotient carries its complete Hilbert graph norm and is isometric
to the orthogonal complement of the exact critical band. The signed form
descends continuously and is nondegenerate. Quotient coercivity is exactly
coercivity in the reduced graph norm on original representatives.
-/

open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph

instance signedRadical_isClosed : IsClosed (signedRadical : Set SourceGraph) :=
  isClosed_signedRadical

/-- The complete arithmetic graph with its entire signed radical removed. -/
abbrev SignedQuotient := SourceGraph ⧸ signedRadical

def signedQuotientMk : SourceGraph →L[ℝ] SignedQuotient := signedRadical.mkQL

/-- The quotient Hilbert norm is the graph norm of the orthogonal representative. -/
def signedQuotientEquiv : SignedQuotient ≃ₗᵢ[ℝ] signedRadicalᗮ :=
  signedRadical.quotientEquivOrthogonal

instance signedQuotient_complete : CompleteSpace SignedQuotient :=
  signedQuotientEquiv.toIsometryEquiv.completeSpace

def signedQuotientRepresentative : SignedQuotient →L[ℝ] SourceGraph :=
  signedRadicalᗮ.subtypeL.comp
    signedQuotientEquiv.toContinuousLinearEquiv.toContinuousLinearMap

theorem signedQuotientRepresentative_mem (x : SignedQuotient) :
    signedQuotientRepresentative x ∈ signedRadicalᗮ :=
  (signedQuotientEquiv x).property

theorem signedQuotientMk_reducedSource (p : SourceGraph) :
    signedQuotientMk (reducedSource p) = signedQuotientMk p := by
  change (Submodule.Quotient.mk (p - criticalProjection p) : SignedQuotient) = _
  rw [Submodule.Quotient.mk_sub,
    (Submodule.Quotient.mk_eq_zero signedRadical).mpr (criticalProjection_mem p), sub_zero]
  rfl

@[simp] theorem signedQuotientRepresentative_mk (p : SourceGraph) :
    signedQuotientRepresentative (signedQuotientMk p) = reducedSource p := by
  change (signedQuotientEquiv (signedQuotientMk p)).val = _
  rw [← signedQuotientMk_reducedSource p]
  exact congrArg Subtype.val
    (signedRadical.quotientEquivOrthogonal_mk (reducedSource p) (reducedSource_mem p))

theorem signedQuotientRepresentative_mk_of_mem {p : SourceGraph}
    (hp : p ∈ signedRadicalᗮ) :
    signedQuotientRepresentative (signedQuotientMk p) = p :=
  congrArg Subtype.val (signedRadical.quotientEquivOrthogonal_mk p hp)

@[simp] theorem signedQuotientMk_representative (x : SignedQuotient) :
    signedQuotientMk (signedQuotientRepresentative x) = x := by
  change Submodule.Quotient.mk (signedRadical.quotientEquivOrthogonal x).val = x
  exact Submodule.mk_quotientEquivOfIsCompl_apply signedRadical.isCompl_orthogonal x

theorem signedQuotientMk_surjective : Function.Surjective signedQuotientMk :=
  fun x => ⟨signedQuotientRepresentative x, signedQuotientMk_representative x⟩

@[simp] theorem signedQuotientMk_eq_zero (p : SourceGraph) :
    signedQuotientMk p = 0 ↔ p ∈ signedRadical :=
  Submodule.Quotient.mk_eq_zero signedRadical

theorem signedQuotientMk_eq_iff (p q : SourceGraph) :
    signedQuotientMk p = signedQuotientMk q ↔ p - q ∈ signedRadical := by
  rw [← sub_eq_zero, ← map_sub, signedQuotientMk_eq_zero]

theorem norm_signedQuotientRepresentative (x : SignedQuotient) :
    ‖signedQuotientRepresentative x‖ = ‖x‖ :=
  signedQuotientEquiv.norm_map x

theorem norm_signedQuotientMk (p : SourceGraph) :
    ‖signedQuotientMk p‖ = ‖reducedSource p‖ := by
  rw [← signedQuotientRepresentative_mk, norm_signedQuotientRepresentative]

/-- The actual signed form on the quotient; its Hilbert norm need not be this form. -/
def quotientPair (x y : SignedQuotient) : ℝ :=
  sourcePair (signedQuotientRepresentative x) (signedQuotientRepresentative y)

def quotientEnergy (x : SignedQuotient) : ℝ := quotientPair x x

@[simp] theorem quotientPair_mk (p q : SourceGraph) :
    quotientPair (signedQuotientMk p) (signedQuotientMk q) = sourcePair p q := by
  rw [quotientPair, signedQuotientRepresentative_mk, signedQuotientRepresentative_mk,
    sourcePair_reduced]

@[simp] theorem quotientEnergy_mk (p : SourceGraph) :
    quotientEnergy (signedQuotientMk p) = sourceEnergy p := by
  rw [quotientEnergy, quotientPair_mk, sourcePair_self]

theorem continuous_quotientPair :
    Continuous (fun p : SignedQuotient × SignedQuotient => quotientPair p.1 p.2) :=
  continuous_sourcePair.comp
    ((signedQuotientRepresentative.continuous.comp continuous_fst).prodMk
      (signedQuotientRepresentative.continuous.comp continuous_snd))

theorem continuous_quotientEnergy : Continuous quotientEnergy :=
  continuous_quotientPair.comp (continuous_id.prodMk continuous_id)

theorem quotientPair_symm (x y : SignedQuotient) : quotientPair x y = quotientPair y x :=
  sourcePair_symm _ _

theorem quotientPair_add_left (x y z : SignedQuotient) :
    quotientPair (x + y) z = quotientPair x z + quotientPair y z := by
  simp only [quotientPair, map_add, sourcePair_add_left]

theorem quotientPair_smul_left (c : ℝ) (x y : SignedQuotient) :
    quotientPair (c • x) y = c * quotientPair x y := by
  simp only [quotientPair, map_smul, sourcePair_smul_left]

theorem quotientPair_add_right (x y z : SignedQuotient) :
    quotientPair x (y + z) = quotientPair x y + quotientPair x z := by
  rw [quotientPair_symm, quotientPair_add_left, quotientPair_symm y x, quotientPair_symm z x]

theorem quotientPair_smul_right (c : ℝ) (x y : SignedQuotient) :
    quotientPair x (c • y) = c * quotientPair x y := by
  rw [quotientPair_symm, quotientPair_smul_left, quotientPair_symm y x]

/-- No nonzero quotient class is invisible to every signed pairing. -/
theorem quotientPair_nondegenerate (x : SignedQuotient) :
    (∀ y, quotientPair x y = 0) ↔ x = 0 := by
  constructor
  · intro h
    have hx : signedQuotientRepresentative x = 0 := by
      apply reduced_nondegenerate (signedQuotientRepresentative_mem x)
      intro q hq
      have he := h (signedQuotientMk q)
      change sourcePair (signedQuotientRepresentative x)
        (signedQuotientRepresentative (signedQuotientMk q)) = 0 at he
      rwa [signedQuotientRepresentative_mk_of_mem hq] at he
    rw [← signedQuotientMk_representative x, hx, map_zero]
  · rintro rfl y
    simp [quotientPair, sourcePair]

/-- Coercivity uses the reduced graph norm on every original representative. -/
theorem quotient_coercivity_iff (c : ℝ) :
    (∀ x : SignedQuotient, c * ‖x‖ ^ 2 ≤ quotientEnergy x) ↔
      ∀ p : SourceGraph, c * ‖reducedSource p‖ ^ 2 ≤ sourceEnergy p := by
  constructor
  · intro h p
    simpa only [norm_signedQuotientMk, quotientEnergy_mk] using h (signedQuotientMk p)
  · intro h x
    obtain ⟨p, rfl⟩ := signedQuotientMk_surjective x
    simpa only [norm_signedQuotientMk, quotientEnergy_mk] using h p

end RHTower.CHMDDoobGraph
