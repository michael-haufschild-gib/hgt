/-
Where the two conjectured correlation sizes part company.

Two sizes are conjectured for the error `Δ_k(x,h)` in the `k`-fold additive divisor problem:
Conrey–Gonek's `x^{1/2+ε}` and Ivić's `Ω(x^{1-1/k})`.  They agree at `k = 2`.  Feeding each into the
transfer with no shift cancellation (`a = 1`) shows exactly where their consequences diverge:

* Ivić's size delivers the Lindelöf value `m(k) = 1` precisely for `k ≤ 3`;
* it beats the known moment envelope precisely for `k < 4`, and at `k = 4` it meets the envelope with
  **equality** — `transferBound 4 1 (3/4) = momentChord 8 = 3/2`;
* Conrey–Gonek's size delivers `m(k) = 1` for `k ≤ 4` and beats the envelope at every `k`.

So the two conjectures have *identical* consequences at `k = 3`: the sixth moment cannot distinguish
them.  The first index at which they differ is `k = 4`, and the first at which Ivić's size fails
outright is `k = 5`.
-/
import GaloisForLFunctions.HTGeometry.AveragedDivisorInput

namespace HTGeometry

/-- Ivić's conjectured size exponent for the `k`-fold correlation error. -/
noncomputable def ivicSize (k : ℝ) : ℝ := 1 - 1/k

@[simp] theorem ivicSize_two : ivicSize 2 = 1/2 := by unfold ivicSize; norm_num

@[simp] theorem ivicSize_three : ivicSize 3 = 2/3 := by unfold ivicSize; norm_num

@[simp] theorem ivicSize_four : ivicSize 4 = 3/4 := by unfold ivicSize; norm_num

/-- **At `k = 2` the two conjectures coincide.**  This is why the solved case cannot discriminate. -/
theorem sizes_agree_at_two : ivicSize 2 = 1/2 := ivicSize_two

/-- **Ivić's size yields the Lindelöf value exactly up to `k = 3`.** -/
theorem ivic_gives_one_iff {k : ℝ} (hk : 0 < k) :
    transferBound k 1 (ivicSize k) = 1 ↔ k ≤ 3 := by
  rw [pointwise_input_eq_one_iff]
  unfold ivicSize
  rw [mul_sub, mul_one_div, div_self (ne_of_gt hk)]
  constructor <;> intro h <;> linarith

/-- **Exact criticality at `k = 4`.**  Ivić's size meets the known moment envelope with equality. -/
theorem ivic_critical_at_four : transferBound 4 1 (ivicSize 4) = momentChord (2 * 4) := by
  rw [ivicSize_four]
  unfold transferBound momentChord
  rw [show (4 : ℝ) * ((1 : ℝ) + 3/4 - 1) / 2 - 1 = 1/2 by norm_num]
  rw [max_eq_right (by norm_num : (0:ℝ) ≤ 1/2)]
  norm_num

/-- **Ivić's size beats the envelope exactly below `k = 4`.**  Via the averaged-input threshold
`δ > 1/2 - 1/k` with `δ = 1/k`. -/
theorem ivic_beats_envelope_iff {k : ℝ} (hk : 2 < k) (hk0 : 0 < k) :
    transferBound k 1 (ivicSize k) < momentChord (2 * k) ↔ k < 4 := by
  have hrw : ivicSize k = 1 - 1/k := rfl
  rw [hrw, averaged_input_threshold hk]
  constructor
  · intro h
    have h2 : 1/2 - 1/k < 1/k := h
    have : (1:ℝ)/2 < 2 * (1/k) := by linarith
    rw [mul_one_div, div_lt_div_iff₀ (by norm_num) hk0] at this
    linarith
  · intro h
    show 1/2 - 1/k < 1/k
    have : (1:ℝ)/2 < 2 * (1/k) := by
      rw [mul_one_div, div_lt_div_iff₀ (by norm_num) hk0]; linarith
    linarith

/-- **The dichotomy is invisible at `k = 3`.**  Both conjectured sizes deliver `m(3) = 1`, so no
theorem about the sixth moment can distinguish them. -/
theorem sixth_moment_cannot_discriminate :
    transferBound 3 1 (ivicSize 3) = 1 ∧ transferBound 3 1 (1/2) = 1 := by
  constructor
  · rw [pointwise_input_eq_one_iff, ivicSize_three]; norm_num
  · rw [pointwise_input_eq_one_iff]; norm_num

/-- Conrey–Gonek's size delivers the Lindelöf value up to `k = 4`, one index further. -/
theorem conreyGonek_gives_one_iff {k : ℝ} :
    transferBound k 1 (1/2) = 1 ↔ k ≤ 4 := pointwise_route_saturates

end HTGeometry
