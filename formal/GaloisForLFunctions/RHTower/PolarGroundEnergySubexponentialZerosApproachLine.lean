import GaloisForLFunctions.RHTower.ConstrainedWeilPolarGroundDecay
import GaloisForLFunctions.RHTower.PolarGroundEnergyNonnegIffRiemannHypothesis
import GaloisForLFunctions.RHTower.AsymptoticAbscissaLawProducers

/-!
# The restricted Weil ground energy: subexponential lower bounds and the zeros approaching the line

Let `μ₀(a)` be the pole-vanishing ground energy of the restricted Weil form at aperture `a`.  RH is
`μ₀ ≥ 0` at every aperture (`riemannHypothesis_iff_forall_polarGroundEnergy_nonneg`).  An attained
top excess `Θ = max |Re ρ − ½| > 0` forces `μ₀(B) ≤ −c' e^{2ΘB}/B³`
(`polarGroundEnergy_le_neg_exp_of_attainedTop`), so a lower bound `μ₀(B) ≥ −C e^{εB}` caps every
attained excess by `ε/2` (`two_mul_attainedExcess_le_of_polarGroundEnergy_ge`).

* **AAL producer** (`asymptoticAbscissaLaw_of_polarGroundEnergySubexponential`).  A subexponential
  lower bound on `μ₀` (`μ₀(B) ≥ −C_ε e^{εB}` for every `ε > 0`) excludes every attained top excess,
  hence gives the asymptotic abscissa law.
* **Split** (`riemannHypothesis_iff_zerosApproachLine_and_polarGroundEnergySubexponential`).
  RH ⟺ (the zeros approach the line) ∧ (`μ₀` is subexponentially bounded below).
* **Gauge** (`abs_re_sub_half_le_of_zerosApproachLine_of_polarGroundEnergy_ge`).  Under ZAL, one
  bound `μ₀(B) ≥ −C e^{εB}` puts every zero within `ε/2` of the line.

So the restricted Weil route needs only a subexponential floor once the zeros approach the line: the
exponential rate of decay of `μ₀` reads the attained top excess, and its only escape is a
non-attained supremum.
-/

open Complex Set

namespace RHTower

noncomputable section

open BacklundConverse LindelofSparse

/-- **Subexponential lower bound on the pole-vanishing ground energy.** -/
def PolarGroundEnergySubexponential : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ B : SuzukiPositiveAperture,
    -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B

/-- **A subexponential floor excludes every attained top excess.** -/
theorem not_attainedTopExcess_of_polarGroundEnergySubexponential
    (h : PolarGroundEnergySubexponential) : ¬ AttainedTopExcess := by
  rintro ⟨Θ, hΘ, q₀, hq₀, hall⟩
  obtain ⟨C, hC⟩ := h Θ hΘ
  have := two_mul_attainedExcess_le_of_polarGroundEnergy_ge hC hΘ q₀ hq₀ hall
  linarith

/-- **A subexponential floor gives the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_polarGroundEnergySubexponential
    (h : PolarGroundEnergySubexponential) : AsymptoticAbscissaLaw :=
  asymptoticAbscissaLaw_of_not_attainedTopExcess
    (not_attainedTopExcess_of_polarGroundEnergySubexponential h)

/-- **RH splits into the zeros approaching the line and a subexponential floor for `μ₀`.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_polarGroundEnergySubexponential :
    RiemannHypothesis ↔ ZerosApproachLine ∧ PolarGroundEnergySubexponential := by
  constructor
  · intro hRH
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, fun ε _ => ⟨0, fun B => ?_⟩⟩
    have := riemannHypothesis_iff_forall_polarGroundEnergy_nonneg.mp hRH B
    simpa using this
  · rintro ⟨hZ, h⟩
    by_contra hRH
    exact not_attainedTopExcess_of_polarGroundEnergySubexponential h
      (attainedTopExcess_of_zerosApproachLine hZ hRH)

/-- **Under ZAL one exponential floor bounds the distance of every zero to the line.** -/
theorem abs_re_sub_half_le_of_zerosApproachLine_of_polarGroundEnergy_ge
    (hZ : ZerosApproachLine) {C ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ B : SuzukiPositiveAperture,
      -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ ε / 2 := by
  by_cases hRH : RiemannHypothesis
  · rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q, sub_self, abs_zero]
    linarith
  · obtain ⟨Θ, hΘ, q₀, hq₀, hall⟩ := attainedTopExcess_of_zerosApproachLine hZ hRH
    have h2 := two_mul_attainedExcess_le_of_polarGroundEnergy_ge h hΘ q₀ hq₀ hall
    have hq := hall q
    rw [spectral_im_eq, abs_sub_comm] at hq
    linarith

end

end RHTower
