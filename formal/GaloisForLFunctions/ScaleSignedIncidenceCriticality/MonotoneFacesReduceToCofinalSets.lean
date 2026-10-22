import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThePrimeSideScaleUnitAndItsUniversalFloor
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThePrimePowersAreTheLeastPositiveNodeSet

/-!
# Monotone faces reduce to cofinal sets; the incidence face does not

`AnUnboundedSetOfAperturesSuffices` shows the zero-side certificate need only be verified along an
unbounded sequence of apertures. The reason is monotonicity, and monotonicity is a property of the
*scale* faces, not of the field as a whole. This module draws the line.

* **The prime face reduces too.** Radius positivity is monotone
  (`weightAperturePositivity_mono`), so positivity along an unbounded set of radii already gives
  membership in the full Weil cone (`weilPositiveFull_of_unbounded_radii`) and hence RH
  (`riemannHypothesis_of_unbounded_radii`). A sequence `R_n → ∞` suffices on the prime side as
  well.
* **The incidence face does not reduce at all.** Omitting a single prime power destroys zero-pole
  positivity (`not_zeroPoleBlindPositiveOn_of_notMem`), so no proper subset of the nodes suffices —
  not a cofinal one, not one of density one, not one missing a single element. Every prime power is
  individually necessary.

`theReductionDichotomy` states the two. The field therefore splits by the order structure of its
readings rather than by its faces: a *monotone* reading, whose value at a large parameter contains
its value at every smaller one, need only be checked cofinally; a reading indexed by an
unstructured set, where each index is an independent constraint, must be checked everywhere.

For a closing mechanism this is the practical division of labour. The two scale faces may be
attacked along sequences, with nothing proved in between; the incidence condition cannot be
sampled, and must be established for every prime power at once — which is exactly why the field's
one-bit refutation (`TheNodeFaceRefutesFromOneBit`) and its infinite confirmation requirement sit on
that face and not on the others.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

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
