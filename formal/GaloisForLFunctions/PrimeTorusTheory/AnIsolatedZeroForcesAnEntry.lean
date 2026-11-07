import «GaloisForLFunctions».«arithmetic-positivity-theory».SingleHeightPhaseSelectiveApertureAndPowerSaving

/-!
# An isolated zero forces an entry

Non-alignment speaks about large heights and a zero speaks about one height. The bridge is the explicit formula: at the height of a zero of depth `δ`, on the window of length `y = e^{2a}`, the smoothed prime polynomial carries the zero with weight `sinh(δ(a − 2w))²`. So a zero with no off-line companion in a window of radius `R` forces the polynomial above any power `c e^{θ a}` of its norm, once `sinh(δ a)⁴ ≫ log γ · poly(a) · (1 + e^a/(1 + R))`.

**Theorem** (`isolated_zero_forces_entry`). This is the contrapositive of the local visibility `zeta_single_height_power_saving_forces_offLine_companion`, read as a statement on the orbit: a one-sided bound for the column at height `γ` excludes an isolated zero of depth `δ` at that height, at length `(log γ)^{O(1/δ)}`. Every saving against size past the horizon is thereby a zero-free statement up to crystal shielding, with the companion clause as the shielding.
-/

open MeasureTheory

namespace GaloisForLFunctions.PrimeTorusTheory

open GaloisForLFunctions.ArithmeticPositivityTheory
open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular
open GaloisForLFunctions GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-- **An isolated zero forces an entry.** See the module docstring. -/
theorem isolated_zero_forces_entry :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier →
      ∀ {δ a R w c θ : ℝ}, 0 < δ → ρ₀.re = 1 / 2 + δ → 0 ≤ R → 0 < w → w ≤ a / 4 →
        (∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ →
          |ρ.im - ρ₀.im| ≤ R → ρ.re = 1 / 2) →
        12 + c * Real.exp (θ * a) ≤ Real.log (1 + |ρ₀.im| / 8) →
        (4 * testNorm (sinhTest a δ)) ^ 2 / (8 * (1 + |ρ₀.im| / 2)) ≤
          ∫ t, ‖((sinhTest a δ t : ℝ) : ℂ)‖ ^ 2 →
        2 * Real.exp a * (4 * testNorm (sinhTest a δ)) ^ 2 / (1 + |ρ₀.im|) ^ 4 ≤
          ∫ t, ‖((sinhTest a δ t : ℝ) : ℂ)‖ ^ 2 →
        384 * A₀ * Real.log (|ρ₀.im| + 3) *
            (2 * a * Real.cosh (δ * a) *
              (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
            (1 + Real.exp a / (1 + R)) <
          2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2 →
        c * Real.exp (θ * a) * ∫ t, ‖((sinhTest a δ t : ℝ) : ℂ)‖ ^ 2 <
          (primePolynomial (fun u => ((sinhTest a δ u : ℝ) : ℂ)) ⌊Real.exp (2 * a)⌋₊
            (-ρ₀.im / (2 * Real.pi))).re := by
  obtain ⟨A₀, hA₀, h⟩ := zeta_single_height_power_saving_forces_offLine_companion
  refine ⟨A₀, hA₀, fun {ρ₀} hρ₀ {δ a R w c θ} hδ hre hR hw hwa hiso hlog htail hpole hbig => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨ρ, hρ, h1, h2, h3, h4⟩ := h hρ₀ hδ hre hR hw hwa hcon hlog htail hpole hbig
  exact h4 (hiso ρ hρ h1 h2 h3)

end

end GaloisForLFunctions.PrimeTorusTheory
