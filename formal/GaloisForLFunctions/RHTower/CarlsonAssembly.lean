/-
Carlson's `o(T)` density: assembling the mollified detection second moment into `RH₂`.

The detection second moment (`DetectionSecondMoment.detectionW_secondMoment_bound`) has the shape

  ∫_T^{2T} ‖E‖²  ≤  T · D(T)  +  O(T),

where `D(T)` is the divisor diagonal tail `∑' 𝟙_{k>min} d(k)² k^{-2σ}` (the mollifier makes this
vanish as the cutoff grows) and `O(T)` is the elementary off-diagonal bound
`4·(N·y)·H(N·y)·∑ eₖ²` (`U`-independent).  Along a parameter schedule `N=N(T)`, `y=y(T)` with the
cutoff `→ ∞` and `N(T)·y(T)·H → o(T)`, both `D(T) → 0` and `O(T)/T → 0`.

`sublinear_of_tail_and_offdiag` is the purely real-analytic bridge: those two limits force
`T·D(T)+O(T)` to be sublinear (`≤ ε·V²·T` eventually), which is exactly the hypothesis
`CarlsonDensity.sublinearDensity_of_largeValues` needs.  Feeding it the zeros-to-mean-square count
(each ζ-zero right of the line is a large value of `E`, `afe_detection`, counted by the
large-values inequality) and the defect recurrence yields `RH₂` (`carlson_rhLadder_of_schedule`).

The two inputs left explicit are the genuinely classical steps: the **zeros-to-mean-square count**
(Gallagher's well-spaced-points lemma applied to the built large-values inequality) and the
**schedule** (`D(T) → 0`, `O(T)/T → 0`) — the mollifier-length optimization.  Everything between them
is machine-checked here.
-/
import GaloisForLFunctions.RHTower.DetectionSecondMoment
import GaloisForLFunctions.RHTower.CarlsonDensity

namespace RHTower

/-- **Sublinearity bridge.**  If a diagonal `D` tends to `0` (`D T ≤ ε` eventually) and an
off-diagonal `O` is `o(T)` (`O T ≤ ε·T` eventually), then the mean-square shape `T·D(T)+O(T)` is
sublinear against any `ε·V²·T`.  Pure real analysis: split the target `ε·V²` between the two tails.
This is the exact `Φ`-sublinearity input of `sublinearDensity_of_largeValues`. -/
theorem sublinear_of_tail_and_offdiag {D O : ℝ → ℝ} {V : ℝ} (hV : 0 < V)
    (hD : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, D T ≤ ε)
    (hO : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, O T ≤ ε * T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, T * D T + O T ≤ ε * V ^ 2 * T := by
  intro ε hε
  have hV2 : 0 < V ^ 2 := by positivity
  set δ : ℝ := ε * V ^ 2 / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨T₁, hT₁⟩ := hD δ hδpos
  obtain ⟨T₂, hT₂⟩ := hO δ hδpos
  refine ⟨max T₁ (max T₂ 0), fun T hT => ?_⟩
  have hTge : T ≥ 0 := le_trans (le_max_right _ _ |>.trans (le_max_right _ _)) hT
  have hT1 : T ≥ T₁ := le_trans (le_max_left _ _) hT
  have hT2 : T ≥ T₂ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hDb : D T ≤ δ := hT₁ T hT1
  have hOb : O T ≤ δ * T := hT₂ T hT2
  have hTD : T * D T ≤ T * δ := mul_le_mul_of_nonneg_left hDb hTge
  calc T * D T + O T ≤ T * δ + δ * T := by linarith [hTD, hOb]
    _ = ε * V ^ 2 * T := by rw [hδ]; ring

/-- **`RH₂` from the mollified detection schedule.**  Given the defect recurrence (`hrec`), a
zeros-to-mean-square count `N(T)·V² ≤ T·D(T)+O(T)` (each right-half ζ-zero a large value of the
detection polynomial, counted by the large-values inequality — the mean square is the
`detectionW_secondMoment_bound` shape), and a schedule making the diagonal `D(T) → 0` and the
off-diagonal `O(T) = o(T)`, the count is sublinear while the recurrence forces a linear floor: the two
are incompatible, so every right-half ξ-zero has even multiplicity (`RHLadder 1`). -/
theorem carlson_rhLadder_of_schedule {N_count : ℝ → ℝ} {c V : ℝ} {D O : ℝ → ℝ}
    (hc : 0 < c) (hV : 0 < V)
    (hrec : (∃ ρ, XiDefect ρ) → LinearLowerBound N_count c)
    (hbound : ∀ T, N_count T * V ^ 2 ≤ T * D T + O T)
    (hD : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, D T ≤ ε)
    (hO : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, O T ≤ ε * T) :
    RHLadder 1 :=
  rhLadder_one_of_recurrence_of_largeValues hc hV hrec hbound
    (sublinear_of_tail_and_offdiag hV hD hO)

end RHTower
