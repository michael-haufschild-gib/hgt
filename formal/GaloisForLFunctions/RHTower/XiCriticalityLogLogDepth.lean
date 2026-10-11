import GaloisForLFunctions.RHTower.XiCriticalityEveryScale
import GaloisForLFunctions.RHTower.ZetaZeroAntiCrystalLogLog

/-!
# Lossless realizations of Ξ have resonances within depth `C / log log T`

**Theorem** (`exists_eventually_shallow_resonance_loglog`). Let `E` be a locally uniform limit of
polynomials with roots in `Im < 0`, nonzero on `ℝ`, with `Re E = Ξ` on `ℝ`. There are `C > 0` and
`K` such that for all large `T`, `E` has a zero `z` with `T^{1/2} − 1 ≤ Re z ≤ T³ + K` and
`Im z ≥ −C / log log T`.

**Proof.** A resonance-free box of depth `d = 2C'/log log T` makes the window `[T^{1/2}, T³]`
`(d/2)`-rigid (`rigidWindow_of_resonance_free`), and the anti-crystal law at depth
`C'/log log T` (`exists_eventually_not_rigidWindow_loglog`) forbids that.
-/

open Complex Filter Topology Set

namespace RHTower

/-- **Resonances within depth `C / log log T` at every scale.** -/
theorem exists_eventually_shallow_resonance_loglog {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    (hrep : ∀ t : ℝ, Xi t = (E t).re) (hne : ∀ t : ℝ, E t ≠ 0) :
    ∃ C K : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∃ z : ℂ, E z = 0 ∧
      T ^ (1 / 2 : ℝ) - 1 ≤ z.re ∧ z.re ≤ T ^ 3 + K ∧ -(C / Real.log (Real.log T)) ≤ z.im := by
  obtain ⟨w, hw, T₁, -, hgap2, hzwin⟩ := exists_ordinate_window_facts
  obtain ⟨K, hK0, hnot⟩ := exists_eventually_not_rigidWindow_loglog
  refine ⟨2 * K, 2 * w + 1, by positivity, ?_⟩
  have eX := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop T₁
  have eV : ∀ᶠ T : ℝ in atTop, 2 * K ≤ Real.log (Real.log T) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _
  filter_upwards [hnot, eX, eventually_ge_atTop (1 : ℝ), eV] with T hnotT hXT hT1 hv
  have hv0 : 0 < Real.log (Real.log T) := by linarith
  have hd0 : 0 < 2 * K / Real.log (Real.log T) := by positivity
  have hd1 : 2 * K / Real.log (Real.log T) ≤ 1 := by rw [div_le_one hv0]; exact hv
  by_contra hcon
  push Not at hcon
  apply hnotT
  have hR := rigidWindow_of_resonance_free hE hrep hne hgap2 hzwin hw hd0 hXT hT1 hcon
  have e : min (2 * K / Real.log (Real.log T)) 1 / 2 = K / Real.log (Real.log T) := by
    rw [min_eq_left hd1]; ring
  rwa [e] at hR

end RHTower
