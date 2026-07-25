/-
The shift-average transfer and its critical input.

A bound `∑_{h ≤ H} Δ_k(x,h) ≪ H^a x^{b+ε}` on the additive-divisor error summed over shifts
transfers into a bound on the moment growth exponent.  Optimising the transfer over the block
length gives

  `M(2k) ≤ transferBound k a b = 1 + max 0 (k(a+b-1)/2 - a)`.

The single input `(a,b) = (1/2, 1)` — which is what Cauchy–Schwarz produces from the sharp
short-interval mean square `∑_{n ≤ x} |Δ_k(n+h) - Δ_k(n)|² ≪ x h^{1+ε}` — reproduces the chord
`1 + (k-2)/4` **for every `k`**, hence exactly the known envelope: `M(4) = 1`, `M(6) ≤ 5/4`,
`M(8) ≤ 3/2`, `M(12) ≤ 2`.

The criterion for an input to beat the chord is `k(2a+2b-3) < 4a-2`, which fails with equality at
`(1/2,1)` simultaneously for every `k`, and holds for every `k > 2` as soon as `b < 1` (a pointwise
saving) or `a < 1/2` (better than square-root cancellation in the shift average).

The module is source-independent: it is arithmetic of the transfer exponents.
-/
import Mathlib.Analysis.Convex.Function
import GaloisForLFunctions.HTGeometry.MomentChordPivot

namespace HTGeometry

/-- The moment growth exponent delivered by a shift-average input `∑_{h≤H} Δ_k(x,h) ≪ H^a x^b`,
after optimising the transfer over the block length. -/
noncomputable def transferBound (k a b : ℝ) : ℝ := 1 + max 0 (k * (a + b - 1) / 2 - a)

/-- **The critical input.**  `(a,b) = (1/2, 1)` sends every `k ≥ 2` to the chord value
`1 + (k-2)/4 = momentChord (2k)`. -/
theorem transferBound_half_one {k : ℝ} (hk : 2 ≤ k) :
    transferBound k (1/2) 1 = momentChord (2 * k) := by
  unfold transferBound momentChord
  have h : k * (1/2 + 1 - 1) / 2 - 1/2 = (k - 2) / 4 := by ring
  rw [h, max_eq_right (by linarith : (0:ℝ) ≤ (k - 2) / 4)]
  ring

/-- Specialisations: the critical input reproduces the whole known envelope. -/
theorem transferBound_envelope :
    transferBound 2 (1/2) 1 = 1 ∧ transferBound 3 (1/2) 1 = 5/4 ∧
    transferBound 4 (1/2) 1 = 3/2 ∧ transferBound 6 (1/2) 1 = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · unfold transferBound
      norm_num

/-- **Breaking criterion.**  For `k > 2` the transfer beats the chord exactly when `k(2a+2b-3) < 4a-2`. -/
theorem transferBound_lt_chord_iff {k a b : ℝ} (hk : 2 < k) :
    transferBound k a b < momentChord (2 * k) ↔ k * (2*a + 2*b - 3) < 4*a - 2 := by
  unfold transferBound momentChord
  have hnn : (0:ℝ) ≤ k * (a + b - 1) / 2 - a ∨ k * (a + b - 1) / 2 - a < 0 :=
    le_or_gt _ _
  rcases hnn with h | h
  · rw [max_eq_right h]
    constructor <;> intro hlt <;> nlinarith [hlt, hk]
  · rw [max_eq_left h.le]
    constructor <;> intro hlt <;> nlinarith [hlt, hk, h]

/-- **Exact criticality of `(1/2,1)`.**  The breaking criterion holds with equality on both sides,
simultaneously for every `k`: the critical input is a fixed point of the transfer, not a coincidence
at one index. -/
theorem critical_input_equality (k : ℝ) :
    k * (2*(1/2 : ℝ) + 2*1 - 3) = 0 ∧ 4*(1/2 : ℝ) - 2 = 0 := by
  constructor <;> ring

/-- A pointwise saving `b < 1` at square-root shift cancillation `a = 1/2` breaks the chord for
every `k > 2`. -/
theorem breaks_of_b_lt_one {k b : ℝ} (hk : 2 < k) (hb : b < 1) :
    k * (2*(1/2 : ℝ) + 2*b - 3) < 4*(1/2 : ℝ) - 2 := by
  have h : 2*(1/2 : ℝ) + 2*b - 3 = 2*(b - 1) := by ring
  rw [h]
  have hneg : b - 1 < 0 := by linarith
  nlinarith [hk, hneg]

/-- Vinogradov's conjectural pointwise size `Δ_k(x,h) ≪ x^{1-1/k}` together with square-root shift
cancellation gives `b = 1 - 1/k < 1`, hence breaks the chord; the resulting exponent is
`1 + max 0 (k/4 - 1)`, which equals `1` for `k ≤ 4` and `3/2` at `k = 6`. -/
theorem transferBound_vinogradov {k : ℝ} (hk : 0 < k) :
    transferBound k (1/2) (1 - 1/k) = 1 + max 0 (k/4 - 1) := by
  unfold transferBound
  have h : k * (1/2 + (1 - 1/k) - 1) / 2 - 1/2 = k/4 - 1 := by
    field_simp
    ring
  rw [h]

section KnownInputs

/-- The published shift-average bound `∑_{h≤H} Δ₃(N,h) ≪ (H² + H^{1/2} N^{13/12}) N^ε`
contributes the exponent pair `(a,b) = (1/2, 13/12)`.  It does **not** break the chord: the
criterion `k(2a+2b-3) < 4a-2` fails at `k = 3`. -/
theorem input_half_thirteen_twelfths_fails :
    ¬ ((3:ℝ) * (2*(1/2 : ℝ) + 2*(13/12) - 3) < 4*(1/2 : ℝ) - 2) := by
  norm_num

/-- With square-root cancellation in the shift average fixed at `a = 1/2`, the chord is broken at
`k = 3` exactly when the second exponent drops below `1`.  So `13/12` must be improved to `1 - δ`:
a saving of `1/12`. -/
theorem input_half_breaks_iff_b_lt_one {b : ℝ} :
    (3:ℝ) * (2*(1/2 : ℝ) + 2*b - 3) < 4*(1/2 : ℝ) - 2 ↔ b < 1 := by
  constructor <;> intro h <;> nlinarith [h]

/-- The published second-moment bound `∑_{h≤H} |Δ₃(N,h)|² ≪ H N^{2-δ}` gives, by Cauchy–Schwarz
over the shifts, the exponent pair `(a,b) = (1, 1 - δ/2)`.  At `k = 3` this breaks the chord
**exactly when `δ > 1/3`**. -/
theorem input_second_moment_breaks_iff {δ : ℝ} :
    (3:ℝ) * (2*(1:ℝ) + 2*(1 - δ/2) - 3) < 4*(1:ℝ) - 2 ↔ 1/3 < δ := by
  constructor <;> intro h <;> nlinarith [h]

/-- Under the conjectural pointwise size `Δ₃(N,h) ≪ N^{2/3+ε}` the second moment would satisfy
`δ = 2/3`; the target `δ > 1/3` is therefore exactly halfway from the published statement to the
conjectural truth. -/
theorem second_moment_conjectural_delta :
    (1:ℝ)/3 < 2/3 ∧ (2:ℝ)/3 - 1/3 = 1/3 := by
  constructor <;> norm_num

end KnownInputs

end HTGeometry
