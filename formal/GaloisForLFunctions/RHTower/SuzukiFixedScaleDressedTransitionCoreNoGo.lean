import GaloisForLFunctions.RHTower.SuzukiNaturalApertureWardScalingNoGo
import GaloisForLFunctions.RHTower.SuzukiApertureDressedSchurTaxUniformBound
import GaloisForLFunctions.RHTower.SuzukiCauchyReporterSecantTransitionCoreEscape

/-!
# Fixed-scale dressed Suzuki channels cannot renormalize the transition core

The current Suzuki Ward frontier contains two exact scaling classes.  After every favorable
transition-separated reporter interaction is removed, the remaining positive arithmetic
transition core still grows at least linearly along apertures `8n`.  By contrast, at fixed source
scale the complete aperture-dressed wall-light mass, marked halfgap completion, and scalar
holonomy Schur tax have one ceiling independent of observer aperture and height.

This module proves the resulting route kill.  First, any correction bounded above leaves the
transition-core rectangular Ward defect tending to negative infinity.  The theorem then inserts
the three literal corpus budgets, grants them the most favorable possible subtraction sign, and
allows an arbitrary positive moving aperture.  The defect still tends to negative infinity and
is not eventually lower-semibounded.

Therefore fixed source scale with fixed scalar marked and Schur coordinates cannot realize
`SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`.  A viable producer must use signed atomic--continuous
relative renormalization, cutoff-growing/non-scalar transport, or growing channel rank.  No RH
premise, Xi-zero hypothesis, numerical computation, asymptotic interchange, or added axiom is
used.
-/

open Filter
open scoped BigOperators
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Complete fixed-coordinate dressed budget appearing in the current Suzuki wall assembly:
wall-light mass, marked halfgap completion, and scalar holonomy Schur tax. -/
def suzukiFixedScaleDressedWardBudget
    (h a t m d r s positiveBlock coupling : ℝ) : ℝ :=
  (∑' pe : Nat.Primes × ℕ,
      Complex.normSq
        (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2)) +
    (∑' pe : Nat.Primes × ℕ,
      suzukiCriticalApertureDressedMarkedRootedCompletion
        h a t m d r s pe) +
    (∑' pe : Nat.Primes × ℕ,
      suzukiCriticalApertureDressedScalarSchurTax
        h a t positiveBlock coupling pe)

/-- Fixed source/marked/Schur coordinates give one ceiling independent of observer aperture. -/
theorem suzukiFixedScaleDressedWardBudget_le
    {h a positiveBlock : ℝ} (hh : 0 < h) (ha : 0 < a)
    (hpositive : 0 < positiveBlock) (t m d r s coupling : ℝ) :
    suzukiFixedScaleDressedWardBudget
        h a t m d r s positiveBlock coupling ≤
      (2 * ((h * Real.sqrt h)⁻¹) ^ (2 : ℕ) *
        (∑' p : Nat.Primes,
          Real.log (p : ℝ) * ((p : ℝ) ^ (2 : ℕ))⁻¹)) +
      (2 * ((h * Real.sqrt h)⁻¹) ^ (2 : ℕ) *
        (∑' p : Nat.Primes,
          Real.log (p : ℝ) * ((p : ℝ) ^ (2 : ℕ))⁻¹)) *
        (r - m * s) ^ (2 : ℕ) +
      (2 * ((h * Real.sqrt h)⁻¹) ^ (2 : ℕ) *
        (∑' p : Nat.Primes,
          Real.log (p : ℝ) * ((p : ℝ) ^ (2 : ℕ))⁻¹)) *
        (coupling ^ (2 : ℕ) / positiveBlock) := by
  unfold suzukiFixedScaleDressedWardBudget
  exact add_le_add
    (add_le_add
      (tsum_normSq_suzukiCriticalApertureBoundaryAtom_allPrime_le hh ha t)
      (tsum_suzukiCriticalApertureDressedMarkedRootedCompletion_le
        hh ha t m d r s))
    (tsum_suzukiCriticalApertureDressedScalarSchurTax_le
      hh ha t hpositive coupling)

/-- A correction bounded above cannot renormalize the positive transition core.  This theorem
already grants the correction its favorable sign. -/
theorem tendsto_suzukiRectangularWardDefect_transitionCore_sub_bounded_atBot
    (L : ℝ) {correction : ℕ → ℝ} {B : ℝ}
    (hcorrection : ∀ N, correction N ≤ B) :
    Tendsto (fun n : ℕ =>
      suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N - correction N)
        (8 * n)) atTop atBot := by
  have hraw :=
    tendsto_suzukiRectangularWardDefect_naturalCauchyEnergy_eight_mul_atBot L
  rw [tendsto_atBot] at hraw ⊢
  intro b
  filter_upwards [hraw (b - B)] with n hn
  rw [suzukiRectangularWardDefect] at hn ⊢
  have hcore := suzukiNaturalApertureCauchyEnergy_le_transitionCore (8 * n)
  have hcorr := hcorrection (8 * n)
  linarith

/-- **Fixed-scale dressed transition-core no-go.**  Even with the entire dressed light,
marked-halfgap, and scalar-holonomy budget inserted with the favorable subtraction sign, the
rectangular Ward defect tends to negative infinity along `8n`. -/
theorem tendsto_suzukiRectangularWardDefect_transitionCore_sub_fixedScaleDressed_atBot
    {h positiveBlock : ℝ} (hh : 0 < h) (hpositive : 0 < positiveBlock)
    (L t m d r s coupling : ℝ) (aperture : ℕ → ℝ)
    (haperture : ∀ N, 0 < aperture N) :
    Tendsto (fun n : ℕ =>
      suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiFixedScaleDressedWardBudget h (aperture N) t m d r s
            positiveBlock coupling)
        (8 * n)) atTop atBot := by
  apply tendsto_suzukiRectangularWardDefect_transitionCore_sub_bounded_atBot L
  intro N
  exact suzukiFixedScaleDressedWardBudget_le
    hh (haperture N) hpositive t m d r s coupling

/-- The fixed-scale dressed producer cannot satisfy the semibounded Ward premise that implies RH. -/
theorem not_exists_eventually_bddBelow_suzukiRectangularWardDefect_transitionCore_sub_fixedScaleDressed
    {h positiveBlock : ℝ} (hh : 0 < h) (hpositive : 0 < positiveBlock)
    (L t m d r s coupling : ℝ) (aperture : ℕ → ℝ)
    (haperture : ∀ N, 0 < aperture N) :
    ¬ ∃ lower : ℝ, ∀ᶠ n : ℕ in atTop,
      lower ≤ suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiFixedScaleDressedWardBudget h (aperture N) t m d r s
            positiveBlock coupling)
        (8 * n) := by
  rintro ⟨lower, hlower⟩
  have hfall :=
    tendsto_suzukiRectangularWardDefect_transitionCore_sub_fixedScaleDressed_atBot
      hh hpositive L t m d r s coupling aperture haperture
  have hbelow : ∀ᶠ n : ℕ in atTop,
      suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiFixedScaleDressedWardBudget h (aperture N) t m d r s
            positiveBlock coupling)
        (8 * n) ≤ lower - 1 :=
    (tendsto_atBot.1 hfall) (lower - 1)
  rcases (hlower.and hbelow).exists with ⟨n, hlow, hhigh⟩
  linarith

/-- **Closed producer-class kill.**  No choice of fixed positive source scale, fixed scalar marked
and Schur coordinates, and positive moving observer apertures can make the favorably corrected
transition-core Ward defect eventually lower-semibounded. -/
theorem no_fixedScaleDressed_transitionCore_WardProducer :
    ¬ ∃ (h positiveBlock L t m d r s coupling : ℝ) (aperture : ℕ → ℝ),
      0 < h ∧ 0 < positiveBlock ∧ (∀ N, 0 < aperture N) ∧
      ∃ lower : ℝ, ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            suzukiFixedScaleDressedWardBudget h (aperture N) t m d r s
              positiveBlock coupling)
          (8 * n) := by
  rintro ⟨h, positiveBlock, L, t, m, d, r, s, coupling, aperture,
    hh, hpositive, haperture, hbounded⟩
  exact
    not_exists_eventually_bddBelow_suzukiRectangularWardDefect_transitionCore_sub_fixedScaleDressed
      hh hpositive L t m d r s coupling aperture haperture hbounded

end

end RHTower
