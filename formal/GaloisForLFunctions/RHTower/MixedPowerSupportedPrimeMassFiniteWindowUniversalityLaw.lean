import GaloisForLFunctions.RHTower.FiniteWindowSeamSincUniversalityLaw
import GaloisForLFunctions.RHTower.SquareSupportPrimeMass

/-!
# Power-supported prime mass in mixed finite-window seams

Multiplicative convolution turns a product of finite Dirichlet carriers into one coefficient
packet.  If that convolution is forced to carry reciprocal prime mass on power labels, the exact
mixed Steinhaus diagonal carries the mass and every symmetric deterministic mixed window retains
it up to the explicit convolution sinc-collision energy.
-/

open Complex MeasureTheory intervalIntegral Finset
open scoped Classical

namespace RHTower

open SteinhausModel

noncomputable section

/-- **Mixed power-supported prime-mass finite-window law.**  Forced reciprocal prime mass in a
multiplicative convolution transfers exactly to the random mixed product and survives every
deterministic symmetric window after subtracting only the explicit mixed sinc energy. -/
theorem mixedPowerSupportedPrimeMass_randomExact_deterministicWindowLowerBound
    (a b : ℕ → ℝ) (s t : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) (ht : ∀ n ∈ t, 1 ≤ n)
    {P : Finset ℕ} {δ : ℝ} {m : ℕ}
    (hm : m ≠ 0) (hδ0 : 0 ≤ δ)
    (hmem : ∀ p ∈ P, p ^ m ∈ prodSupport s t)
    (hval : ∀ p ∈ P,
      δ * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        |dpolyConv a b s t (p ^ m)|)
    (T : ℝ) (hT : 0 < T) :
    (∫ ω,
        ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
          (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ 2 ∂steinhausMeasure =
      ∑ k ∈ prodSupport s t, dpolyConv a b s t k ^ 2) ∧
      δ ^ 2 * ∑ p ∈ P, (p : ℝ)⁻¹ ≤
        ∫ ω,
          ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
            (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ 2 ∂steinhausMeasure ∧
      δ ^ 2 * ∑ p ∈ P, (p : ℝ)⁻¹ -
          dpolySincOffDiagonalEnergy
            (dpolyConv a b s t) (prodSupport s t) T ≤
        (∫ τ in (-T)..T, ‖dpoly a s τ * dpoly b t τ‖ ^ 2) / (2 * T) := by
  have hforced := primeMass_le_pow_sum_of_forced hm hδ0 hmem hval
  have hrandom := mixedSteinhausSecondMoment_eq_convolutionDiagonal a b s t hs ht
  have herror := mixedSecondMoment_symmetric_sinc_error_le a b s t hs ht T hT
  refine ⟨hrandom, ?_, ?_⟩
  · rw [hrandom]
    exact hforced
  · have hlower := neg_le_of_abs_le herror
    linarith

end

end RHTower
