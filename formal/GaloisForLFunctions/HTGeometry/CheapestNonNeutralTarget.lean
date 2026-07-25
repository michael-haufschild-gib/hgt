/-
The cheapest additive-divisor input that beats the record.

The neutrality law says a perfect `2j`-th moment improves on an established exponent `θ` exactly when
`j > 1/(2θ)`.  At `θ = 13/84` the threshold is `42/13 = 3.23…`, so `j = 4` — the **eighth** moment —
is the least index that helps, and it delivers `μ ≤ 1/8 < 13/84`.

What does `m(4) = 1` cost?  Through the transfer, `transferBound k 1 b = 1 ⟺ k·b ≤ 2`, so at `k = 4`
the requirement is `b ≤ 1/2`: the Conrey–Gonek size, **with no shift cancellation at all**.  With
shift cancellation `a = 1/2` the requirement relaxes to `b ≤ 1/2 + 1/k`, the same curve that the
Lindelöf hypothesis imposes.

So the eighth moment is where three things coincide: it is the first non-neutral index, the last
index at which the pointwise branch can reach the Lindelöf value, and the first index at which the two
conjectured correlation sizes give different answers.
-/
import GaloisForLFunctions.HTGeometry.IvicSizeCriticality
import GaloisForLFunctions.HTGeometry.MomentNeutralityLaw

namespace HTGeometry

/-- **The eighth moment needs exactly the Conrey–Gonek size, with no shift cancellation.** -/
theorem eighth_moment_needs_conreyGonek {b : ℝ} :
    transferBound 4 1 b = 1 ↔ b ≤ 1/2 := by
  rw [pointwise_input_eq_one_iff]
  constructor <;> intro h <;> linarith

/-- With shift cancellation the requirement relaxes to the Lindelöf curve `1/2 + 1/k`. -/
theorem shifted_requirement {k b : ℝ} (hk : 0 < k) :
    transferBound k (1/2) b = 1 ↔ b ≤ 1/2 + 1/k := by
  unfold transferBound
  constructor
  · intro h
    have h0 : max 0 (k * (1/2 + b - 1) / 2 - 1/2) = 0 := by linarith
    have hle := max_eq_left_iff.mp h0
    rw [← sub_le_iff_le_add', le_div_iff₀ hk]
    nlinarith [hle]
  · intro h
    have h' : k * (1/2 + b - 1) / 2 - 1/2 ≤ 0 := by
      have hb : b - 1/2 ≤ 1/k := by linarith
      have : k * (b - 1/2) ≤ k * (1/k) := mul_le_mul_of_nonneg_left hb hk.le
      rw [mul_one_div, div_self (ne_of_gt hk)] at this
      nlinarith [this]
    rw [max_eq_left h']; ring

/-- At `k = 6` the shifted requirement is `b ≤ 2/3`; at `k = 3` it is `b ≤ 5/6`.  Higher moments
demand strictly more. -/
theorem shifted_requirement_six_vs_three :
    (1/2 + 1/(6:ℝ) = 2/3) ∧ (1/2 + 1/(3:ℝ) = 5/6) ∧ (2/3 : ℝ) < 5/6 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The eighth moment beats Bourgain's exponent.** -/
theorem eighth_moment_beats_bourgain : (1:ℝ)/8 < bourgainExponent := by
  unfold bourgainExponent; norm_num

/-- **`j = 4` is the least integer index that is not subconvexity-neutral.**  The neutrality threshold
at `θ = 13/84` is `42/13`, and `3 < 42/13 < 4`. -/
theorem four_is_least_nonneutral :
    (3 : ℝ) < 1/(2*bourgainExponent) ∧ 1/(2*bourgainExponent) < 4 := by
  unfold bourgainExponent
  constructor <;> norm_num

/-- **Ivić's size does not reach the eighth moment.**  At `k = 4` it gives `b = 3/4 > 1/2`, so the
pointwise branch returns the known envelope value rather than the Lindelöf value: the eighth moment is
the first index at which the two conjectured sizes give different conclusions. -/
theorem eighth_moment_separates_the_conjectures :
    ¬ (transferBound 4 1 (ivicSize 4) = 1) ∧ (transferBound 4 1 (1/2) = 1) := by
  constructor
  · rw [pointwise_input_eq_one_iff, ivicSize_four]
    norm_num
  · rw [pointwise_input_eq_one_iff]; norm_num

/-- **The cheapest route to beating the record, assembled.**  Prove the Conrey–Gonek bound at the
single index `k = 4` — no shift cancellation required — and `μ ≤ 1/8 < 13/84` follows. -/
theorem cheapest_nonneutral_target :
    (∀ b : ℝ, b ≤ 1/2 → transferBound 4 1 b = 1) ∧
    (1:ℝ)/8 < bourgainExponent ∧
    ((3 : ℝ) < 1/(2*bourgainExponent) ∧ 1/(2*bourgainExponent) < 4) :=
  ⟨fun _ hb => eighth_moment_needs_conreyGonek.mpr hb,
   eighth_moment_beats_bourgain, four_is_least_nonneutral⟩

end HTGeometry
