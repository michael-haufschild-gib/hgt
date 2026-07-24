import GaloisForLFunctions.RHTower.ThetaCuspShellIncompleteGammaCoordinate
import GaloisForLFunctions.RHTower.ThetaCuspWignerProductFiberNormalForm

/-!
# Theta-cusp Wigner–Gamma–Xi transverse-energy universality

The actual center-mixed theta current has four exact coordinates: a radial Wigner integral, the
cofinal completed-source product-fibre current, reflected incomplete-Gamma shell currents, and the
transverse derivative of the completed Xi norm square. The fibre energies themselves sum exactly
to that norm square. This closes the value/derivative square without interchanging an infinite
sum and a derivative.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Twice the real radial Wigner current in the normalization of the actual theta source. -/
def thetaCuspRadialWignerCurrent (a b : ℝ) : ℝ :=
  2 * (∫ r : ℝ in Set.Ioi 0,
    (r * Real.sinh (a * r) : ℝ) *
      thetaWignerDistribution thetaCuspComplexSource (r / 2) b).re

/-- Reflected incomplete-Gamma coordinate for one ordered positive shell-pair current. -/
def thetaCuspShellPairGammaCurrent (z : ℂ) (q : ℕ × ℕ) : ℝ :=
  2 * (thetaCuspShellEvenGammaSpectralDerivative z q.1 *
    (starRingEnd ℂ)
      (2 * thetaCuspShellGammaBoundary q.2 +
        Real.pi * (I * z - 1 / 2) *
          thetaCuspShellGammaCoreRemainder z q.2 +
        Real.pi * (I * (-z) - 1 / 2) *
          thetaCuspShellGammaCoreRemainder (-z) q.2)).im

/-- **Theta-cusp Wigner–Gamma–Xi transverse-energy universality law.** On the physical
half-aperture, the radial Wigner current is simultaneously the derivative of `‖XiC‖²` and the
cofinal sum of completed-source product-fibre currents. Every finite fibre current is the
derivative of its Hermitian energy; those energies are summable and total `‖XiC‖²`; and every
ordered shell-pair current has the exact reflected incomplete-Gamma coordinate. -/
theorem thetaCusp_completeWignerGammaXiTransverseEnergyUniversality
    {a b : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) :
    let z : ℂ := (b : ℂ) - (a : ℂ) * I
    HasDerivAt
        (fun α : ℝ =>
          Complex.normSq (XiC ((b : ℂ) - (α : ℂ) * I)))
        (thetaCuspRadialWignerCurrent a b) a ∧
      thetaCuspRadialWignerCurrent a b =
        ∑' k : ℕ, thetaCuspSourceProductFiberHedenmalmCurrent k z ∧
      (∀ k : ℕ,
        HasDerivAt
          (fun α : ℝ =>
            thetaCuspSourceProductFiberHermitianEnergy k
              ((b : ℂ) - (α : ℂ) * I))
          (thetaCuspSourceProductFiberHedenmalmCurrent k z) a) ∧
      Summable (fun k : ℕ =>
        thetaCuspSourceProductFiberHermitianEnergy k z) ∧
      (∑' k : ℕ, thetaCuspSourceProductFiberHermitianEnergy k z) =
        Complex.normSq (XiC z) ∧
      ∀ q : ℕ × ℕ, 0 < q.1 → 0 < q.2 →
        thetaCuspShellPairHedenmalmCurrent z q =
          thetaCuspShellPairGammaCurrent z q := by
  dsimp only
  have ha : |a| < 1 := by
    rw [abs_of_nonneg ha0]
    linarith
  have hz :
      |(((b : ℂ) - (a : ℂ) * I).im)| < 1 := by
    simpa only [sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
      zero_mul, mul_one, zero_sub, add_zero, abs_neg] using ha
  have hW :=
    thetaCuspCenterMixedFourierCurrent_eq_two_mul_re_radialWigner
      ha0 haHalf b
  have hderiv :=
    hasDerivAt_normSq_XiC_transverse_eq_centerMixedFourierCurrent
      ha (b := b)
  change thetaCuspCenterMixedFourierCurrent a ha b =
      thetaCuspRadialWignerCurrent a b at hW
  rw [hW] at hderiv
  refine ⟨hderiv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hW]
    exact thetaCuspCenterMixedFourierCurrent_eq_tsum_sourceProductFiber ha b
  · intro k
    exact hasDerivAt_thetaCuspSourceProductFiberHermitianEnergy ha k
  · exact summable_thetaCuspSourceProductFiberHermitianEnergy hz
  · exact tsum_thetaCuspSourceProductFiberHermitianEnergy_eq_normSq_XiC hz
  · intro q hq1 hq2
    exact thetaCuspShellPairHedenmalmCurrent_eq_gamma hz hq1 hq2

end

end RHTower
