import GaloisForLFunctions.ScaleSignedIncidenceCriticality.RefutationIsFiniteConfirmationIsNot
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheApertureCertificateIsBlindInEveryUnit
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading

/-!
# Sparse apertures suffice, and the incidence face does not reduce

What must a closing mechanism actually verify? This module answers it on each face, and the answers
differ by the order structure of the reading.

**The scale faces reduce to a cofinal set.** Aperture positivity is monotone, so positivity along
*any* unbounded set of apertures already gives the unconditional certificate and hence RH
(`riemannHypothesis_of_unbounded_apertures`) — with nothing proved in between, and with or without a
fixed deficit level (`riemannHypothesis_of_unbounded_apertures_gain`). The prime face reduces the
same way: positivity along an unbounded set of radii gives membership in the full Weil cone
(`weilPositiveFull_of_unbounded_radii`) and hence RH
(`riemannHypothesis_of_unbounded_radii`).

**The incidence face does not reduce at all.** Omitting a single prime power destroys zero-pole
positivity, so no proper subset of the nodes suffices — not a cofinal one, not one of density one
(`not_zeroPoleBlindPositiveOn_of_notMem`). Every prime power is individually necessary.

`theReductionDichotomy` states the two. A monotone reading, whose value at a large parameter
contains its value at every smaller one, need only be checked cofinally; a reading indexed by an
unstructured set, where each index is an independent constraint, must be checked everywhere. That is
why the field's one-bit refutation and its infinite confirmation requirement both sit on the
incidence face, and why a mechanism may attack the aperture axis along a sparse sequence.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold
open Zeta23 _root_.RHTower
open Zeta23 _root_.RHTower GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false


/-- The configuration of the nontrivial zeros of `ζ`. -/
noncomputable def zetaConfig : TemperedZeroConfig :=
  ⟨zetaZeroConfig, temperedConfig_zetaZeroConfig⟩

-- from AnUnboundedSetOfAperturesSuffices.lean
/-! ### 1. Unbounded suffices -/

/-- **An unbounded set of apertures gives the unbounded certificate.** -/
theorem fullPositivity_of_unbounded_apertures {Z : TemperedZeroConfig}
    (h : ∀ M : ℝ, ∃ a : ℝ, M < a ∧ aperturePositivity a Z) : fullPositivity Z := by
  intro f hf hfc
  obtain ⟨a₀, ha₀, hsub⟩ := exists_aperture_of_hasCompactSupport hfc
  obtain ⟨a, hlt, hpos⟩ := h a₀
  exact aperturePositivity_mono hlt.le hpos f hf hsub

/-- Hence the width is zero. -/
theorem width_eq_zero_of_unbounded_apertures {Z : TemperedZeroConfig}
    (h : ∀ M : ℝ, ∃ a : ℝ, M < a ∧ aperturePositivity a Z) : width Z = 0 :=
  (configWidth_eq_zero_iff_weil_nonneg Z.2).mpr
    fun f hf hfc => fullPositivity_of_unbounded_apertures h f hf hfc

/-! ### 2. On `ζ` it is RH -/

/-- **RH from an unbounded sequence of apertures.** -/
theorem riemannHypothesis_of_unbounded_apertures
    (h : ∀ M : ℝ, ∃ a : ℝ, M < a ∧ aperturePositivity a zetaConfig) : RiemannHypothesis :=
  riemannHypothesis_iff_configWidth_zetaZeroConfig_eq_zero.mpr
    (width_eq_zero_of_unbounded_apertures h)

/-- **And with a fixed deficit level**, since a uniform gain adds nothing. -/
theorem riemannHypothesis_of_unbounded_apertures_gain {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ M : ℝ, ∃ a : ℝ, M < a ∧ apertureGain a η zetaConfig) : RiemannHypothesis := by
  refine riemannHypothesis_of_unbounded_apertures fun M => ?_
  obtain ⟨a, hlt, hgain⟩ := h M
  refine ⟨a, hlt, fun f hf hfs => ?_⟩
  have hint : (0 : ℝ) ≤ ∫ t, ‖f t‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  have hbase := hgain f hf hfs
  nlinarith

/-! ### 3. The reduced requirement -/

/-- **The requirement on a closing mechanism.** Positivity of `ζ`'s configuration along any
unbounded set of apertures — with or without a fixed deficit level, and with nothing asked about
the apertures in between — already gives RH. -/
theorem theReducedRequirement {η : ℝ} (hη : 0 ≤ η) :
    ((∀ M : ℝ, ∃ a : ℝ, M < a ∧ aperturePositivity a zetaConfig) → RiemannHypothesis) ∧
      ((∀ M : ℝ, ∃ a : ℝ, M < a ∧ apertureGain a η zetaConfig) → RiemannHypothesis) :=
  ⟨riemannHypothesis_of_unbounded_apertures, riemannHypothesis_of_unbounded_apertures_gain hη⟩

-- from MonotoneFacesReduceToCofinalSets.lean
/-! ### 1. The prime face reduces to a cofinal set of radii -/

/-- **An unbounded set of radii gives the full cone.** -/
theorem weilPositiveFull_of_unbounded_radii {lam : ℕ → ℝ}
    (h : ∀ M : ℝ, ∃ R : ℝ, M < R ∧ weightAperturePositivity R lam) : WeilPositiveFull lam := by
  intro f hf hfc
  obtain ⟨a, ha, hsub⟩ := exists_aperture_of_hasCompactSupport hfc
  obtain ⟨R, hlt, hpos⟩ := h a
  exact weightAperturePositivity_mono hlt.le hpos f hf hsub

/-- **RH from an unbounded sequence of radii.** -/
theorem riemannHypothesis_of_unbounded_radii
    (h : ∀ M : ℝ, ∃ R : ℝ, M < R ∧
      weightAperturePositivity R (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))) :
    RiemannHypothesis :=
  (WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp
    (weilPositiveFull_of_unbounded_radii h)).1

/-! ### 2. The incidence face does not reduce -/

/-- **Every prime power is individually necessary.** A node set omitting one prime power is never
zero-pole positive, so no proper subset of the nodes suffices, however large. -/
theorem not_zeroPoleBlindPositiveOn_of_notMem {𝒩 : Set ℕ} {m : ℕ} (hm : IsPrimePow m)
    (hmem : m ∉ 𝒩) : ¬ ZeroPoleBlindPositiveOn 𝒩 := by
  have hdiff : deleteNode m 𝒩 = 𝒩 := Set.sdiff_singleton_eq_self hmem
  intro hpos
  exact not_zeroPoleBlindPositiveOn_deleteNode hm 𝒩 (by rw [hdiff]; exact hpos)

/-! ### 3. The dichotomy -/

/-- **The reduction dichotomy.** The two monotone faces need only be verified along an unbounded
set of their parameter; the incidence face needs every single node. -/
theorem theReductionDichotomy :
    ((∀ M : ℝ, ∃ R : ℝ, M < R ∧
        weightAperturePositivity R (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))) →
      RiemannHypothesis) ∧
      ∀ (𝒩 : Set ℕ) (m : ℕ), IsPrimePow m → m ∉ 𝒩 → ¬ ZeroPoleBlindPositiveOn 𝒩 :=
  ⟨riemannHypothesis_of_unbounded_radii,
    fun _ _ hm hmem => not_zeroPoleBlindPositiveOn_of_notMem hm hmem⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
