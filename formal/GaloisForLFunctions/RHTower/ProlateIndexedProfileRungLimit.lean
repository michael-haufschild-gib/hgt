import GaloisForLFunctions.RHTower.ProlateCanonicalOscillatorLower
import GaloisForLFunctions.RHTower.ProlateHermiteRungWindowLimit

/-!
# The canonical indexed prolate profile converges to its Hermite rung

The window comparison at the `n`-th rung needs its hypotheses at every index of the family; a
family parametrized by the aperture satisfies them only eventually, because the window fits inside
the classically allowed region only once the bandwidth is large.  Weakening the hypotheses to
`∀ᶠ` costs nothing: the Grönwall envelope still dominates the distance eventually, and a squeeze
along a filter only needs eventual bounds.

With that, the canonical indexed even prolate family is a family of the required kind.  Its
separation constants converge to the even oscillator rungs, `μ_n → 4n+1 = 2·(2n)+1`, and its
profiles are normalized to value `1` and derivative `0` at the origin; rescaling by `φ_{2n}(0)`
matches the initial phase vector of the `2n`-th Hermite function exactly, because an even Hermite
function has vanishing derivative there.  So the profile of the `n`-th canonical mode converges,
on every window, to the `2n`-th Hermite function.
-/

open Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **Window convergence at the `n`-th rung, from eventual hypotheses.**  The Grönwall envelope
dominates the window distance wherever the hypotheses hold, so a squeeze along the filter needs
them only eventually. -/
theorem tendsto_prolateProfile_hermiteRung_eventually
    {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K B : ℝ} {n : ℕ}
    {u u' u'' : ι → ℝ → ℝ} (hK : 0 < K)
    (hgood : ∀ᶠ i in L, 2 * K ^ (2 : ℕ) ≤ c i ∧
      (∀ x, HasDerivAt (u i) (u' i x) x) ∧ (∀ x, HasDerivAt (u' i) (u'' i x) x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' i x
        = rescaledProlateP (c i) (mu i) x * u i x + rescaledProlateQ (c i) x * u' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B) ∧
      u i 0 = hermiteFun n 0 ∧ u' i 0 = deriv (hermiteFun n) 0)
    (hmu : Tendsto mu L (𝓝 (2 * (n : ℝ) + 1))) (hc : Tendsto c L atTop) :
    ∀ x ∈ Icc (0 : ℝ) K, Tendsto (fun i => u i x) L (𝓝 (hermiteFun n x)) := by
  intro x hx
  have henv := tendsto_prolateWindow_envelope (mu := mu) (c := c) (K := K) (B := B) (n := n) hmu hc
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun i => dist_nonneg) ?_ henv
  filter_upwards [hgood] with i hi
  rw [Real.dist_eq]
  exact le_trans (le_max_left _ _)
    (prolateProfile_window_hermiteRung_dist_le hK hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1
      hi.2.2.2.2.1 hi.2.2.2.2.2.1 hi.2.2.2.2.2.2 x hx)

/-- **The canonical indexed profile converges to its Hermite rung on every window.**  Scaling the
canonical profile by `φ_{2n}(0)` matches the Hermite initial phase vector, and the indexed
oscillator law supplies the separation constant. -/
theorem tendsto_indexedOscillatorProfile_hermiteRung (n : ℕ) {K : ℝ} (hK : 0 < K) :
    ∀ x ∈ Icc (0 : ℝ) K,
      Tendsto (fun a : ProlatePositiveAperture =>
          hermiteFun (2 * n) 0 * indexedOscillatorProfile n a x)
        atTop (𝓝 (hermiteFun (2 * n) x)) := by
  set κ : ℝ := hermiteFun (2 * n) 0 with hκ
  have hmu' : Tendsto (indexedOscillatorSeparation n) atTop (𝓝 (2 * ((2 * n : ℕ) : ℝ) + 1)) := by
    have hval : 2 * ((2 * n : ℕ) : ℝ) + 1 = 4 * (n : ℝ) + 1 := by push_cast; ring
    rw [hval]
    exact tendsto_indexedOscillatorSeparation_atTop n
  have hgood := eventually_indexedOscillatorProfile_windowBound
    (M := 4 * (n : ℝ) + 2) (m := 4 * (n : ℝ) + 1) (by positivity) n
    (tendsto_indexedOscillatorSeparation_atTop n) (by linarith)
    tendsto_indexedOscillatorBandwidth_atTop hK
  have heven : Even (2 * n) := ⟨n, by ring⟩
  refine tendsto_prolateProfile_hermiteRung_eventually (n := 2 * n)
    (u := fun a x => κ * indexedOscillatorProfile n a x)
    (u' := fun a x => κ * indexedOscillatorProfileDeriv n a x)
    (u'' := fun a x => κ * indexedOscillatorProfileDeriv2 n a x)
    (B := |κ| * indexedOscillatorWindowBound (4 * (n : ℝ) + 2) K)
    hK ?_ hmu' tendsto_indexedOscillatorBandwidth_atTop
  filter_upwards [hgood] with a ha
  refine ⟨ha.2.1, fun x => (indexedOscillatorProfile_hasDerivAt n a x).const_mul κ,
    fun x => (indexedOscillatorProfileDeriv_hasDerivAt n a x).const_mul κ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [ha.2.2.1 x hx]
    ring
  · intro x hx
    have hb := ha.2.2.2.1 x hx
    have hP : |indexedOscillatorProfile n a x|
        ≤ indexedOscillatorWindowBound (4 * (n : ℝ) + 2) K := le_trans (le_max_left _ _) hb
    have hP' : |indexedOscillatorProfileDeriv n a x|
        ≤ indexedOscillatorWindowBound (4 * (n : ℝ) + 2) K := le_trans (le_max_right _ _) hb
    refine max_le ?_ ?_
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hP (abs_nonneg κ)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hP' (abs_nonneg κ)
  · rw [ha.2.2.2.2.1, hκ]
    ring
  · rw [ha.2.2.2.2.2, deriv_hermiteFun_zero_of_even heven]
    ring

end GaloisForLFunctions.RHTower

end
