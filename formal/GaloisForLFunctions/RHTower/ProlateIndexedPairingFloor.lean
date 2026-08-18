import GaloisForLFunctions.RHTower.ProlateHermitePairingFloor
import GaloisForLFunctions.RHTower.ProlateCanonicalOscillatorLower

/-!
# The canonical family has a window-pairing floor at its own rung

The canonical origin-normalised profiles satisfy the window package
(`eventually_indexedOscillatorProfile_windowBound`) and their separation constants converge to the
even rung `4n+1` (`tendsto_indexedOscillatorSeparation_atTop`).  The general floor therefore applies
verbatim: at every large aperture the window pairing against `φ_{2n}` stays above half its nonzero
limit.
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **The canonical window-pairing floor.** -/
theorem eventually_abs_indexedOscillator_window_pairing_ge (n : ℕ) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ a : ProlatePositiveAperture in atTop,
      |∫ x in (-K)..K, oscProfile (2 * ((2 * n : ℕ) : ℝ) + 1) x * hermiteFun (2 * n) x| / 2
        ≤ |∫ x in (-K)..K, indexedOscillatorProfile n a x * hermiteFun (2 * n) x| := by
  have hM : (0 : ℝ) ≤ 4 * (n : ℝ) + 1 := by positivity
  have hmu : Tendsto (indexedOscillatorSeparation n) atTop (𝓝 (2 * ((2 * n : ℕ) : ℝ) + 1)) := by
    have h := tendsto_indexedOscillatorSeparation_atTop n
    have hcast : 2 * ((2 * n : ℕ) : ℝ) + 1 = 4 * (n : ℝ) + 1 := by push_cast; ring
    rwa [hcast]
  have hev := eventually_indexedOscillatorProfile_windowBound (L := atTop)
    (M := 4 * (n : ℝ) + 1) (m := 4 * (n : ℝ) + 1) hM n
    (tendsto_indexedOscillatorSeparation_atTop n) le_rfl
    tendsto_indexedOscillatorBandwidth_atTop hK
  exact eventually_abs_window_pairing_ge (n := 2 * n)
    (B := indexedOscillatorWindowBound (4 * (n : ℝ) + 1) K)
    ⟨n, by ring⟩ hK
    (indexedOscillatorProfile_hasDerivAt n) (indexedOscillatorProfileDeriv_hasDerivAt n)
    (indexedOscillatorProfile_even n) hev hmu tendsto_indexedOscillatorBandwidth_atTop

end GaloisForLFunctions.RHTower

end
