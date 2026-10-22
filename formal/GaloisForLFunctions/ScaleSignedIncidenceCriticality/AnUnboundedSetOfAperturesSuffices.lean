import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheGradedApertureJumpIsUniformityItself

/-!
# An unbounded set of apertures suffices

The corpus's criteria demand "every scale, not almost every". On the aperture face that demand is
automatically met, and the reason is the monotone structure of the certificate: positivity at a
large aperture contains positivity at every smaller one
(`aperturePositivity_mono`). So the exceptional set a method is allowed to skip may be enormous, as
long as it is not cofinal.

* `fullPositivity_of_unbounded_apertures` — if the certificate holds at an **unbounded** set of
  apertures, it holds at every aperture, and the width is zero
  (`width_eq_zero_of_unbounded_apertures`).
* `riemannHypothesis_of_unbounded_apertures` — hence RH follows from Weil positivity of `ζ`'s
  configuration along any unbounded set of apertures: a sequence `a_n → ∞` suffices, no continuum is
  needed.
* `riemannHypothesis_of_unbounded_apertures_gain` — and the same with a fixed deficit level: by
  `TheGradedApertureJumpIsUniformityItself` a uniform gain adds nothing, so positivity along an
  unbounded sequence *at one level* is already enough.

This is a reduction of the remaining proof burden rather than a floor. The programme's one faithful
reading — the unbounded certificate — need only be verified along a sequence, and the sequence may
be as sparse as one likes. Together with `SubexponentialSubsidiesAreHarmless` the requirement on a
closing mechanism is now: a deficit not growing exponentially, at an unbounded sequence of
apertures. Nothing about the apertures in between, and no margin.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

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

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
