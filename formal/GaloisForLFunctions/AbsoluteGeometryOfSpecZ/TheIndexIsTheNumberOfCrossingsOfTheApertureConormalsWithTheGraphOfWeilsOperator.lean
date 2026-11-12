import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexAtAnApertureIsTheSumOfTheNullitiesBelowIt
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNullSpaceOfACompressionIsTheCrossingOfAGraphWithAConormal
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilCrossApertureFormTransport

/-!
# The index is the number of crossings of the aperture conormals with the graph of Weil's operator

Fix an aperture `b` and an energy `E`. The form domain `H_b` at `b` contains the form domain `H_a`
of every smaller aperture `a`, isometrically (`apertureIsometry`), and Weil's operator at `b`
compresses on `H_a` to Weil's operator at `a` (`inner_operator_apertureExt`).

In the symplectic space `H_b × H_b`:

* the graph of Weil's operator at `(b, E)` is one fixed Lagrangian subspace (`weilGraph`,
  `mem_weilGraph_iff_forall_sympForm`); it is the only place where the primes and the poles
  enter;
* the conormals `H_a × H_aᗮ` of the apertures `a ≤ b` are a path of Lagrangian subspaces
  (`apertureConormal`, `mem_apertureConormal_iff_forall_sympForm`), increasing in `a`
  (`range_apertureIsometry_le`), which ends at the horizontal Lagrangian `H_b × 0`
  (`mem_apertureConormal_self`); the path does not depend on the primes.

The crossing of the path with the graph at the aperture `a` is the space of null modes of Weil's
form at `a` (`finrank_weilGraph_inf_apertureConormal`). So the resonant apertures are the
crossings, with their nullities, and the index at `b` is the number of crossings of the path with
the graph (`negativeRank_eq_sum_apertureCrossing`): the Morse index of Weil's form is the Maslov
index of the path of aperture conormals against the graph of Weil's operator.
-/

open Module Finset
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil
open ArithmeticContinuationAndCriticalEnergy HTGeometry

variable {a b : SuzukiPositiveAperture}

/-- Zero extension to a larger aperture, as an isometry of the form domains. -/
def apertureIsometry (hab : a.1 ≤ b.1) : Space a →ₗᵢ[ℂ] Space b :=
  ⟨apertureExtLinear hab, norm_apertureExt hab⟩

theorem apertureIsometry_apply (hab : a.1 ≤ b.1) (u : Space a) :
    apertureIsometry hab u = apertureExt hab u :=
  rfl

/-- **Weil's operator at a larger aperture compresses to Weil's operator at a smaller one.** -/
theorem inner_operator_apertureExt (hab : a.1 ≤ b.1) (E : ℝ) (u v : Space a) :
    ⟪operator b E (apertureExt hab u), apertureExt hab v⟫_ℂ = ⟪operator a E u, v⟫_ℂ := by
  rw [operator_mixed, operator_mixed,
    ccmRestrictedWeilForm_eq_of_val_eq hab (apertureExt_val hab u) (apertureExt_val hab v),
    inner_embedding_apertureExt]

/-- The graph of Weil's operator at the aperture `b`, shifted by the energy `E`. -/
def weilGraph (b : SuzukiPositiveAperture) (E : ℝ) : Submodule ℂ (Space b × Space b) :=
  operatorGraph (operator b E)

/-- The conormal of the form domain of a smaller aperture. -/
def apertureConormal (hab : a.1 ≤ b.1) : Submodule ℂ (Space b × Space b) :=
  conormal (LinearMap.range (apertureIsometry hab).toLinearMap)

/-- **The graph of Weil's operator is Lagrangian.** -/
theorem mem_weilGraph_iff_forall_sympForm (b : SuzukiPositiveAperture) (E : ℝ)
    (p : Space b × Space b) :
    p ∈ weilGraph b E ↔ ∀ q ∈ weilGraph b E, sympForm p q = 0 :=
  mem_operatorGraph_iff_forall_sympForm (operator_selfAdjoint b E) p

/-- **The conormal of an aperture is Lagrangian.** -/
theorem mem_apertureConormal_iff_forall_sympForm (hab : a.1 ≤ b.1) (p : Space b × Space b) :
    p ∈ apertureConormal hab ↔ ∀ q ∈ apertureConormal hab, sympForm p q = 0 := by
  haveI := hasOrthogonalProjection_range_isometry (apertureIsometry hab)
  exact mem_conormal_iff_forall_sympForm _ p

/-- The form domains of the apertures increase. -/
theorem range_apertureIsometry_le {c : SuzukiPositiveAperture} (hac : a.1 ≤ c.1)
    (hcb : c.1 ≤ b.1) :
    LinearMap.range (apertureIsometry (hac.trans hcb)).toLinearMap ≤
      LinearMap.range (apertureIsometry hcb).toLinearMap := by
  rintro _ ⟨u, rfl⟩
  exact ⟨apertureExt hac u, Subtype.ext
    ((apertureExt_val hcb _).trans ((apertureExt_val hac u).trans
      (apertureExt_val (hac.trans hcb) u).symm))⟩

/-- **The path ends at the horizontal Lagrangian.** -/
theorem mem_apertureConormal_self (b : SuzukiPositiveAperture) (p : Space b × Space b) :
    p ∈ apertureConormal (le_refl b.1) ↔ p.2 = 0 := by
  have htop : LinearMap.range (apertureIsometry (le_refl b.1)).toLinearMap = ⊤ := by
    rw [eq_top_iff]
    intro u _
    exact ⟨u, Subtype.ext (apertureExt_val (le_refl b.1) u)⟩
  rw [apertureConormal, mem_conormal, htop, Submodule.top_orthogonal_eq_bot,
    Submodule.mem_bot]
  exact ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩

/-- **The crossing of the conormal of the aperture `a` with the graph is the space of null modes
of Weil's form at `a`.** -/
theorem finrank_weilGraph_inf_apertureConormal (hab : a.1 ≤ b.1) (E : ℝ) :
    finrank ℂ ↥(weilGraph b E ⊓ apertureConormal hab) = weilNullity a E :=
  finrank_operatorGraph_inf_conormal (apertureIsometry hab) (operator b E) (operator a E)
    (inner_operator_apertureExt hab E)

/-- The dimension of the crossing of the conormal of the aperture `a` with the graph of Weil's
operator at `b`. -/
def apertureCrossing (b : SuzukiPositiveAperture) (E : ℝ) (a : SuzukiPositiveAperture) : ℕ :=
  if h : a.1 ≤ b.1 then finrank ℂ ↥(weilGraph b E ⊓ apertureConormal h) else 0

theorem apertureCrossing_eq_weilNullity (hab : a.1 ≤ b.1) (E : ℝ) :
    apertureCrossing b E a = weilNullity a E := by
  rw [apertureCrossing, dif_pos hab, finrank_weilGraph_inf_apertureConormal]

/-- The resonant apertures are the crossings of the path with the graph. -/
theorem mem_resonantBelow_iff_apertureCrossing {E : ℝ} :
    a ∈ resonantBelow b E ↔ a.1 < b.1 ∧ 0 < apertureCrossing b E a := by
  rw [mem_resonantBelow]
  exact and_congr_right fun h => by rw [apertureCrossing_eq_weilNullity h.le]

/-- **The index is the number of crossings.** The negative index of Weil's form at the aperture
`b` and the energy `E` is the sum of the dimensions of the crossings of the conormals of the
smaller apertures with the graph of Weil's operator at `b`. -/
theorem negativeRank_eq_sum_apertureCrossing (b : SuzukiPositiveAperture) (E : ℝ) :
    negativeRank b E = ∑ a ∈ resonantBelow b E, apertureCrossing b E a := by
  rw [negativeRank_eq_sum_nullity]
  exact Finset.sum_congr rfl fun a ha =>
    (apertureCrossing_eq_weilNullity (mem_resonantBelow.mp ha).1.le E).symm

/-- **The Riemann hypothesis holds iff no aperture conormal crosses the graph of Weil's operator
at the energy zero.** -/
theorem riemannHypothesis_iff_forall_apertureCrossing_zero :
    RiemannHypothesis ↔
      ∀ a b : SuzukiPositiveAperture, a.1 ≤ b.1 → apertureCrossing b 0 a = 0 := by
  rw [riemannHypothesis_iff_forall_weilNullity_zero]
  constructor
  · intro h a b hab
    rw [apertureCrossing_eq_weilNullity hab, h a]
  · intro h a
    rw [← apertureCrossing_eq_weilNullity (le_refl a.1) 0, h a a (le_refl a.1)]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
