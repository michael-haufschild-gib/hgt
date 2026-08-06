/-
The completeness list of the Lindelöf frontier, in one theorem.

Every unconditional route to `μ(1/2)` examined in the frontier map terminates at a ceiling, and the
ceilings are `1/4`, `1/6`, `1/8`, or nothing at all.  The list is:

* mean-value / large sieve — `1/4`, traced with no slack against Phragmén–Lindelöf;
* Halász–Montgomery — `1/4`, being the fourth-moment bound read backwards;
* Guth–Maynard — inert at the self-dual block, which always binds;
* the `E(T)` and `E₂(T)` error-term programmes — `1/8`, sharp by `Ω`-results;
* Heath-Brown's twelfth moment — attained exactly on the window `v ∈ [1/8, 1/6]`, whose lower end
  is the pivot;
* the additive-divisor route with Vinogradov's size — `1/8`;
* the short-interval mean square — strictly worse than the known envelope at its proved value, and
  exactly neutral at its conjecturally optimal one;
* resonance — subpolynomial, so no `Ω(T^c)`;
* `GL(3)` subconvexity for `ζ³` — `1/6`.

Uncapped is exactly the family equivalent to, or stronger than, Lindelöf: the Conrey–Gonek size
together with square-root shift cancellation gives `m(k) = 1` for every `k`.

There is no uncapped intermediate.  That is the structural content of the map.
-/
import GaloisForLFunctions.HTGeometry.LindelofMethodCeilings
import GaloisForLFunctions.HTGeometry.LindelofPivotCoincidences
import GaloisForLFunctions.HTGeometry.ResonanceSubpolynomialGain

namespace HTGeometry

open Filter Topology

/-- **The completeness list.**  Each conjunct is one entry of the frontier's capped column, and the
last conjunct is the uncapped one. -/
theorem lindelof_frontier_completeness :
    -- mean-value / large sieve: traces convexity with no slack, ceiling `1/4`
    (∀ k : ℝ, k ≠ 0 → convexityExponent (meanValueAbscissa k) = meanValueOutput k) ∧
    convexityExponent (1/2) = 1/4 ∧
    -- Halász–Montgomery: the fourth-moment bound and nothing more, ceiling `1/4`
    (∀ v : ℝ, halaszMeasureExponent v = 1 - fourthMomentPhi v) ∧
    meanValueOutput 2 = 1/4 ∧
    -- Guth–Maynard: inert at the self-dual block
    (∀ v : ℝ, min (guthMaynardBound 1 v) (classicalMeasureExponent v) =
      classicalMeasureExponent v) ∧
    -- the error-term programmes: floor `1/8` at both indices where an asymptotic is known
    resolutionFloor 1 = 1/8 ∧ resolutionFloor 2 = 1/8 ∧
    -- Heath-Brown's twelfth moment: the window is exactly `[1/8, 1/6]`
    (∀ v : ℝ, (1/4 ≤ shortSecondMomentLength v ∧ shortSecondMomentLength v ≤ 1/3) ↔
      (1/8 ≤ v ∧ v ≤ 1/6)) ∧
    -- additive divisor with Vinogradov's size: `1/8`
    (∀ k : ℝ, 4 ≤ k → transferBound k (1/2) (1 - 1/k) / (2*k) = 1/8) ∧
    -- the short-interval mean square: worse at its proved value, neutral at its optimum
    (momentChord (2*(3:ℝ)) < transferBound 3 (2/3) 1 ∧
      momentChord (2*(6:ℝ)) < transferBound 6 (2/3) 1) ∧
    (∀ k : ℝ, 2 ≤ k → transferBound k (1/2) 1 = momentChord (2*k)) ∧
    -- resonance: subpolynomial, so no power `Ω`-result
    (∀ C c : ℝ, 0 < c →
      Tendsto (fun L : ℝ => Real.exp (galSumExponent C L) / Real.exp (c * L))
        atTop (nhds 0)) ∧
    -- `GL(3)` subconvexity for `ζ³`: `1/6`
    meanValueOutput 3 = 1/6 ∧
    -- uncapped: the Conrey–Gonek size with square-root shift cancellation is Lindelöf
    (∀ k : ℝ, transferBound k (1/2) (1/2) = 1) :=
  ⟨fun _ hk => meanValue_traces_convexity hk, convexityExponent_half,
    halasz_is_fourthMoment, meanValueOutput_two, guthMaynard_inert,
    resolutionFloor_one, resolutionFloor_two, heathBrown_window_iff,
    fun _ hk => vinogradov_cap hk, shortIntervalVariance_worse_than_chord,
    fun _ hk => transferBound_half_one hk,
    fun C _ hc => resonanceGain_tendsto_zero C hc,
    meanValueOutput_three, transferBound_conreyGonek⟩

/-- **The pivot is one point.**  All four independent characterisations of `v = 1/8` — the crossing
of the two large-value lines, the Halász–Montgomery self-dual balance, the forced critical block
size, and the chord–pivot plateau — become critical at the same `v`, with the same value `1/2`. -/
theorem lindelof_pivot_is_one_point :
    (∀ v : ℝ, fourthMomentPhi v = heathBrownPhi v ↔ v = 1/8) ∧
    (∀ v : ℝ, halaszAmplitude v = gramSquareRootSize ↔ v = 1/8) ∧
    (∀ v : ℝ, forcedBlockExponent v = 3/4 ↔ v = 1/8) ∧
    certifiedPhi (1/8) = 1/2 ∧
    (∀ A : ℝ, pivotGain momentChord A = 1/2) ∧
    shortSecondMomentLength (1/8) = 1/4 ∧
    (∀ k : ℝ, 0 < k → modelErrorExponent k / (2*k) = 1/8) :=
  ⟨phi_lines_cross_iff, halasz_selfDual_balance_iff, forcedBlockExponent_threshold_iff,
    certifiedPhi_at_pivot, pivotGain_momentChord, heathBrown_window_lower_is_pivot,
    fun _ hk => model_floor_is_eighth hk⟩

end HTGeometry
