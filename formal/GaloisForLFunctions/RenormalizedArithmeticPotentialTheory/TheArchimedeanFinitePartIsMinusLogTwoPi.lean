import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartOfTheMarkovFormAtTheSpacing
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheMarkovFormFailsInsideTheSeparatedRegime

/-!
# The archimedean finite part is `−log 2π`

The finite part of the Markov form at the spacing scale
(`TheFinitePartOfTheMarkovFormAtTheSpacing`) is `2θ′(0) + κ_L(φ) + γ`, with the Robin constant
`κ_L(φ) = 2c_∞ + β(φ)/‖φ‖²` of the atom (`TheRobinConstantOfAnAtom`). This file evaluates the
profile-free part, with the archimedean Robin constant `2c_∞ = 2 log 2 + π/2`
(SSHA `archRobinConstant_eq`):

* **The finite part** (`archimedeanFinitePart_eq`): with Gauss's `ψ(1/4) = −γ − π/2 − 3 log 2`,
  `2θ′(0) + 2c_∞ + γ = −log 2π`.
* **The Markov form at the spacing** (`eventually_markovEnergy_atomicTest_ge_logTwoPi`,
  `eventually_markovEnergy_truncPole_le_logTwoPi`): its ground energy at width `w ≤ δ_N/2` is
  `log(1/(2π wN)) + β(φ)/‖φ‖² + O(wN) + o(1)`.

The Gamma factor, the Lévy self-energy of the atom and the pole of the prime place cancel to the
conductor `−log 2π` of the real place; the only free datum is the shape `β(φ)/‖φ‖²` of the profile,
and the leading-order critical width is `wN = e^{β(φ)/‖φ‖²}/(2π)`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset RHTower
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticIntersectionTheory

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 1. The archimedean finite part -/

/-- **The archimedean finite part is `−log 2π`**: `2θ′(0) + 2c_∞ + γ = −log 2π`. -/
theorem archimedeanFinitePart_eq :
    2 * gammaHardyPhaseRate 0 + SpacingScaleHarmonicAnalysis.archRobinConstant + γ =
      -Real.log (2 * π) := by
  rw [SpacingScaleHarmonicAnalysis.archRobinConstant_eq, gammaHardyPhaseRate_zero_closed,
    Real.log_mul (by norm_num) Real.pi_ne_zero]
  ring

/-- `2θ′(0) + κ_L(φ) + γ = −log 2π + β(φ)/‖φ‖²`. -/
theorem finitePart_profileRobin_eq (φ : ℝ → ℝ) :
    2 * gammaHardyPhaseRate 0 + SpacingScaleHarmonicAnalysis.profileRobin φ + γ =
      -Real.log (2 * π) + SpacingScaleHarmonicAnalysis.bumpRobin φ 1 / ∫ u, φ u ^ 2 := by
  rw [SpacingScaleHarmonicAnalysis.profileRobin, ← archimedeanFinitePart_eq]
  ring

/-! ### 2. The Markov form at the spacing in closed form -/

/-- **The Markov form at the spacing, lower bound in closed form**: eventually in `N`, for
`w ≤ δ_N/2` and `wN ≤ 1/(64e²)`,
`M(f) ≥ (log(1/(2π wN)) + β(φ)/‖φ‖² − ε − (e^{1/2}/2) w − A·wN) ‖f‖²`. -/
theorem eventually_markovEnergy_atomicTest_ge_logTwoPi {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      w * N ≤ markovOverlapBound → ∀ x : ℕ → ℝ,
        (Real.log (1 / (2 * π * (w * N))) +
            SpacingScaleHarmonicAnalysis.bumpRobin φ 1 / (∫ u, φ u ^ 2) - ε -
            Real.exp (1 / 2) / 2 * w - markovCrossConstant * (w * N)) *
            ∫ u, atomicTest N x (SpacingScaleHarmonicAnalysis.atomDilate φ w) u ^ 2 ≤
          markovEnergy
            (fun u => (atomicTest N x (SpacingScaleHarmonicAnalysis.atomDilate φ w) u : ℂ)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_markovEnergy_atomicTest_ge hφ hφsupp hφ0 hK hε hε1
  refine ⟨max N₀ 1, fun N hN w hw0 hw hwN x => ?_⟩
  have h := hN₀ N (le_trans (le_max_left _ _) hN) w hw0 hw hwN x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := le_max_right N₀ 1; omega)
  have hlog : Real.log (1 / (2 * π * (w * N))) = Real.log (1 / (w * N)) - Real.log (2 * π) := by
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity), one_div,
      Real.log_inv]
    ring
  have hfp := finitePart_profileRobin_eq φ
  rw [hlog]
  convert h using 2
  linarith

/-- **The Markov form at the spacing, upper bound in closed form**: for a nonnegative profile,
eventually the pole vector has
`M(f) ≤ (log(1/(2π wN)) + β(φ)/‖φ‖² + ε + (e^{1/2}/2) w) ‖f‖²` at every width `w ≤ δ_N/2`. -/
theorem eventually_markovEnergy_truncPole_le_logTwoPi {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) (hφnn : ∀ u, 0 ≤ φ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      markovEnergy
          (fun u => (atomicTest N (truncPole N) (SpacingScaleHarmonicAnalysis.atomDilate φ w) u : ℂ)) ≤
        (Real.log (1 / (2 * π * (w * N))) +
            SpacingScaleHarmonicAnalysis.bumpRobin φ 1 / (∫ u, φ u ^ 2) + ε +
            Real.exp (1 / 2) / 2 * w) *
          ∫ u, atomicTest N (truncPole N) (SpacingScaleHarmonicAnalysis.atomDilate φ w) u ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := eventually_markovEnergy_truncPole_le hφ hφsupp hφ0 hK hφnn hε
  refine ⟨max N₀ 1, fun N hN w hw0 hw => ?_⟩
  have h := hN₀ N (le_trans (le_max_left _ _) hN) w hw0 hw
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := le_max_right N₀ 1; omega)
  have hlog : Real.log (1 / (2 * π * (w * N))) = Real.log (1 / (w * N)) - Real.log (2 * π) := by
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity), one_div,
      Real.log_inv]
    ring
  have hfp := finitePart_profileRobin_eq φ
  rw [hlog]
  convert h using 2
  linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
