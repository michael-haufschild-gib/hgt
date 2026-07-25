/-
The price of averaging instead of cancelling in the shift.

Results on shifted convolutions of higher divisor functions come in two shapes.  The first bounds the
plain average `(1/H) Σ_{h ≤ H} Δ_k(x,h) ≪ x^{1-δ}`, i.e. `Σ_{h≤H} Δ_k(x,h) ≪ H x^{1-δ}` — an input
with shift exponent `a = 1`.  The second exhibits square-root cancellation in the shift,
`Σ_{h≤H} Δ_k(x,h) ≪ H^{1/2} x^{b}` — an input with `a = 1/2`.

Through the shift-average transfer the two are worth very different amounts.  With `a = 1/2` **any**
power saving in `x` beats the known moment envelope, at every index.  With `a = 1` the saving must
exceed `1/2 - 1/k` before it beats the envelope at index `k`, so a route confined to plain averages
needs `δ → 1/2` to reach every index — and `δ = 1/2` is exactly the shift-free Conrey–Gonek size,
which the transfer caps at the pivot rather than at the Lindelöf value.
-/
import GaloisForLFunctions.HTGeometry.ShiftAverageTransfer
import GaloisForLFunctions.HTGeometry.MomentChordPivot

namespace HTGeometry

/-- **The averaged input beats the envelope exactly above `1/2 - 1/k`.**  An input with no
cancellation in the shift (`a = 1`) and a power saving `δ` in `x` improves on the known moment
envelope at index `k` if and only if `k(1 - 2δ) < 2`. -/
theorem averaged_input_lt_chord_iff {k δ : ℝ} (hk : 2 < k) :
    transferBound k 1 (1 - δ) < momentChord (2 * k) ↔ k * (1 - 2 * δ) < 2 := by
  rw [transferBound_lt_chord_iff hk]
  constructor <;> intro h <;> nlinarith [h]

/-- The same threshold in solved form: the required saving is `δ > 1/2 - 1/k`. -/
theorem averaged_input_threshold {k δ : ℝ} (hk : 2 < k) :
    transferBound k 1 (1 - δ) < momentChord (2 * k) ↔ 1/2 - 1/k < δ := by
  rw [averaged_input_lt_chord_iff hk]
  have hk0 : (0 : ℝ) < k := by linarith
  constructor
  · intro h
    have hlt : 1/2 - δ < 1/k := by
      rw [lt_div_iff₀ hk0]; nlinarith [h]
    linarith
  · intro h
    have h' : (1/2 - 1/k) * k < δ * k := mul_lt_mul_of_pos_right h hk0
    have hid : (1/2 - 1/k) * k = k/2 - 1 := by field_simp
    rw [hid] at h'
    nlinarith [h']

/-- At the first unknown index `k = 3` the averaged input must save more than `1/6`. -/
theorem averaged_input_threshold_three {δ : ℝ} :
    transferBound 3 1 (1 - δ) < momentChord (2 * 3) ↔ 1/6 < δ := by
  have h := averaged_input_threshold (k := 3) (δ := δ) (by norm_num)
  rw [h]; norm_num

/-- **The contrast.**  With square-root cancellation in the shift, any positive saving suffices at
every index; with a plain average, the demand grows to `1/2` as `k → ∞`.  So `a = 1/2` is not a
technical convenience: it is what separates an input worth the Lindelöf hypothesis from one worth
only the pivot. -/
theorem shift_cancellation_is_essential {k δ : ℝ} (hk : 2 < k) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2 - 1/k) :
    transferBound k (1/2) (1 - δ) < momentChord (2 * k) ∧
    ¬ (transferBound k 1 (1 - δ) < momentChord (2 * k)) := by
  constructor
  · rw [transferBound_lt_chord_iff hk]
    nlinarith [hδ, hk]
  · rw [averaged_input_threshold hk]
    exact not_lt.mpr hδ1

/-- **The pointwise branch, exactly.**  A uniform pointwise bound `Δ_k(x,h) ≪ x^{b+ε}` is the input
`(a,b) = (1,b)`, and it delivers the Lindelöf value `m(k) = 1` precisely when `k·b ≤ 2`. -/
theorem pointwise_input_eq_one_iff {k b : ℝ} :
    transferBound k 1 b = 1 ↔ k * b ≤ 2 := by
  unfold transferBound
  constructor
  · intro h
    have h0 : max 0 (k * (1 + b - 1) / 2 - 1) = 0 := by linarith
    have := (max_eq_left_iff.mp h0)
    nlinarith [this]
  · intro h
    have h0 : k * (1 + b - 1) / 2 - 1 ≤ 0 := by nlinarith [h]
    rw [max_eq_left h0]; ring

/-- At `k = 3` the ternary additive divisor problem delivers the sixth moment conjecture exactly at
the same exponent `2/3` that solves the binary problem. -/
theorem ternary_two_thirds : transferBound 3 1 (2/3) = 1 := by
  rw [pointwise_input_eq_one_iff]; norm_num

/-- …and delivers *any* improvement on the known envelope precisely below `5/6`. -/
theorem ternary_improves_iff {b : ℝ} :
    transferBound 3 1 b < momentChord (2 * 3) ↔ b < 5/6 := by
  have h := averaged_input_threshold (k := 3) (δ := 1 - b) (by norm_num)
  simp only [sub_sub_cancel] at h
  rw [h]; constructor <;> intro hb <;> linarith

/-- **Why the pointwise route caps at the pivot.**  Even the best conceivable size, the Conrey–Gonek
`Δ_k(x,h) ≪ x^{1/2+ε}`, gives `m(k) = 1` only for `k ≤ 4`; beyond that a pointwise bound cannot
reach the Lindelöf value, because `x^{2/k}` drops below the square-root barrier `x^{1/2}`.  This is
the exact arithmetic behind the `(1, 1/2) ↦ 1/8` row of the separation table. -/
theorem pointwise_route_saturates {k : ℝ} :
    transferBound k 1 (1/2) = 1 ↔ k ≤ 4 := by
  rw [pointwise_input_eq_one_iff]
  constructor <;> intro h <;> linarith

end HTGeometry
