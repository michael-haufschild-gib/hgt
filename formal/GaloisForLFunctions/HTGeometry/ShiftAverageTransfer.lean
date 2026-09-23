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


section AdditiveDivisorCap

/-- **The additive-divisor route, fed its conjecturally exact input, caps at `1/8`.**
Vinogradov's conjectural pointwise size `Δ_k(x,h) ≪ x^{1-1/k+ε}` together with square-root
cancellation in the shift average is the input `(a,b) = (1/2, 1-1/k)`.  For every `k ≥ 4` the
resulting pointwise exponent `transferBound k (1/2) (1-1/k) / (2k)` is **exactly `1/8`** — a plateau
across all `k ≥ 4`, not a coincidence at one index. -/
theorem vinogradov_cap {k : ℝ} (hk : 4 ≤ k) :
    transferBound k (1/2) (1 - 1/k) / (2*k) = 1/8 := by
  have hk0 : (0:ℝ) < k := by linarith
  rw [transferBound_vinogradov hk0, max_eq_right (by linarith : (0:ℝ) ≤ k/4 - 1)]
  field_simp
  ring

/-- Below `k = 4` the same input gives `1/(2k) ≥ 1/8`, so the minimum over all `k > 0` is attained
at `k = 4` and equals `1/8`. -/
theorem vinogradov_cap_below {k : ℝ} (hk : 0 < k) (hk4 : k ≤ 4) :
    transferBound k (1/2) (1 - 1/k) / (2*k) = 1/(2*k) ∧ 1/8 ≤ 1/(2*k) := by
  constructor
  · rw [transferBound_vinogradov hk, max_eq_left (by linarith : k/4 - 1 ≤ 0)]
    ring
  · rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith

/-- **Consequence.**  Even a complete solution of the `k`-ary additive divisor problem, at its
conjecturally exact strength and for every `k`, yields only `μ(1/2) ≤ 1/8` through the shift-average
transfer — never the Lindelöf hypothesis.  The transfer is irreducibly lossy: the true moment
exponent is `m(k) = 1`, while the transfer delivers `m(k) ≤ k/4` for `k ≥ 4`. -/
theorem vinogradov_cap_is_eighth :
    transferBound 4 (1/2) (1 - 1/4) / (2*(4:ℝ)) = 1/8 ∧
      transferBound 6 (1/2) (1 - 1/6) / (2*(6:ℝ)) = 1/8 ∧
      transferBound 12 (1/2) (1 - 1/12) / (2*(12:ℝ)) = 1/8 := by
  refine ⟨vinogradov_cap (by norm_num), vinogradov_cap (by norm_num),
    vinogradov_cap (by norm_num)⟩

end AdditiveDivisorCap


section ConspiracyExponent

/-- The **conspiracy exponent**.  The off-diagonal of the `2k`-th moment is
`∑_h (D_k(M,h)/M) K(h)` with `K(h) ≪ min(T, M/h)`; note the normalising `1/M`.  Modelling the errors
`Δ_k(M,h)` at their conjectured size `M^{1-1/k}` with independent signs, and using
`∑_{h≤M} K(h)^(2 : ℕ) ≍ 2MT`, the predicted error is

  `(1/M)(2MT)^{1/2} M^{1-1/k} = √2 · T^{1/2} M^{1/2-1/k} = √2 · T^{k/4}`  at `M = T^{k/2}`.

Since the off-diagonal must be `≪ T^{1+ε}`, independent signs suffice exactly when `k ≤ 4`, and for
`k > 4` a further cancellation of strength `T^{c(k)}` is required, where

  `conspiracyExponent k = k/4 - 1`. -/
noncomputable def conspiracyExponent (k : ℝ) : ℝ := k/4 - 1

/-- No conspiracy is needed at or below `k = 4`: the independent-signs model already delivers
`m(k) = 1`, hence `μ(1/2) ≤ 1/8`.  This is why the additive-divisor cap sits exactly at `1/8`
(C44): `k = 4` is the borderline. -/
theorem conspiracyExponent_four : conspiracyExponent 4 = 0 := by
  unfold conspiracyExponent; norm_num

theorem conspiracyExponent_nonpos {k : ℝ} (hk : k ≤ 4) : conspiracyExponent k ≤ 0 := by
  unfold conspiracyExponent; linarith

/-- At `k = 3` the model has room to spare: the sixth moment follows from Vinogradov plus
square-root shift cancellation with no correlations at all. -/
theorem conspiracyExponent_three : conspiracyExponent 3 = -1/4 := by
  unfold conspiracyExponent; norm_num

/-- Beyond `k = 4` a genuine conspiracy is required, growing linearly. -/
theorem conspiracyExponent_pos {k : ℝ} (hk : 4 < k) : 0 < conspiracyExponent k := by
  unfold conspiracyExponent; linarith

theorem conspiracyExponent_six : conspiracyExponent 6 = 1/2 := by
  unfold conspiracyExponent; norm_num

theorem conspiracyExponent_strictMono {j k : ℝ} (h : j < k) :
    conspiracyExponent j < conspiracyExponent k := by
  unfold conspiracyExponent; linarith

end ConspiracyExponent


section ConreyGonekInput

/-- **The Conrey–Gonek input gives Lindelöf.**  Conrey–Gonek predict
`D_k(N,h) = ∫ S(x,h)dx + O(N^{1/2+ε})`, i.e. `|Δ_k(N,h)| ≪ N^{1/2+ε}` — *independent of `k`* and much
stronger than Vinogradov's `N^{1-1/k}`.  With square-root cancellation over the shifts this is the
input `(a,b) = (1/2, 1/2)`, and the transfer then gives `m(k) = 1` for **every** `k`. -/
theorem transferBound_conreyGonek (k : ℝ) :
    transferBound k (1/2) (1/2) = 1 := by
  unfold transferBound
  have h : k * (1/2 + 1/2 - 1) / 2 - 1/2 = -(1/2 : ℝ) := by ring
  rw [h, max_eq_left (by norm_num : -(1/2:ℝ) ≤ 0)]
  ring

/-- The Conrey–Gonek input breaks the chord at every `k > 2`: `k(2a+2b-3) = -k < 0 = 4a-2`. -/
theorem conreyGonek_breaks_chord {k : ℝ} (hk : 0 < k) :
    k * (2*(1/2 : ℝ) + 2*(1/2 : ℝ) - 3) < 4*(1/2 : ℝ) - 2 := by
  have h : 2*(1/2 : ℝ) + 2*(1/2 : ℝ) - 3 = -1 := by norm_num
  rw [h]; linarith [hk]

/-- Contrast: Vinogradov's size `b = 1 - 1/k` caps the same transfer at `1/8` (`vinogradov_cap`),
whereas Conrey–Gonek's `b = 1/2` gives `m(k) = 1`.  The two conjectured sizes therefore lead to
different conclusions, and they are in direct conflict for `k ≥ 3`: `1/2 < 1 - 1/k`. -/
theorem vinogradov_exceeds_conreyGonek {k : ℝ} (hk : 2 < k) : (1:ℝ)/2 < 1 - 1/k := by
  have hk0 : (0:ℝ) < k := by linarith
  have h1 : 1/k < 1/2 := by
    rw [div_lt_div_iff₀ hk0 (by norm_num : (0:ℝ) < 2)]; linarith
  linarith


/-- **Conrey–Gonek's pointwise size alone gives `1/8`.**  Without any cancellation over the shifts
(`a = 1`), the input `(a,b) = (1, 1/2)` gives `m(k) ≤ max(1, k/4)`, hence `μ(1/2) ≤ 1/8` — the same
exponent Vinogradov's size gives *with* square-root shift cancellation. -/
theorem transferBound_conreyGonek_pointwise (k : ℝ) :
    transferBound k 1 (1/2) = 1 + max 0 (k/4 - 1) := by
  unfold transferBound
  have h : k * (1 + 1/2 - 1) / 2 - 1 = k/4 - 1 := by ring
  rw [h]

/-- So the two hypotheses separate cleanly: Conrey–Gonek's size gives `1/8`, and adding square-root
cancellation over the shifts upgrades it to the full moment conjecture. -/
theorem conreyGonek_separation {k : ℝ} (hk : 4 ≤ k) :
    transferBound k 1 (1/2) / (2*k) = 1/8 ∧ transferBound k (1/2) (1/2) = 1 := by
  constructor
  · rw [transferBound_conreyGonek_pointwise, max_eq_right (by linarith : (0:ℝ) ≤ k/4 - 1)]
    have hk0 : (0:ℝ) < k := by linarith
    field_simp
    ring
  · exact transferBound_conreyGonek k

end ConreyGonekInput


section FirstPowerSaving

/-- With **no** cancellation over the shifts, a first power saving `Δ₃(x,h) ≪ x^{1-δ}` gives
`m(3) ≤ 3/2 - 3δ/2`. -/
theorem transferBound_first_saving_no_cancellation {δ : ℝ} (h1 : δ ≤ 1/3) :
    transferBound 3 1 (1 - δ) = 3/2 - 3*δ/2 := by
  unfold transferBound
  have h : (3:ℝ) * (1 + (1 - δ) - 1) / 2 - 1 = 1/2 - 3*δ/2 := by ring
  rw [h, max_eq_right (by linarith : (0:ℝ) ≤ 1/2 - 3*δ/2)]
  ring

/-- With square-root cancellation over the shifts, the same saving gives `m(3) ≤ 5/4 - 3δ/2`. -/
theorem transferBound_first_saving_sqrt {δ : ℝ} (h1 : δ ≤ 1/6) :
    transferBound 3 (1/2) (1 - δ) = 5/4 - 3*δ/2 := by
  unfold transferBound
  have h : (3:ℝ) * (1/2 + (1 - δ) - 1) / 2 - 1/2 = 1/4 - 3*δ/2 := by ring
  rw [h, max_eq_right (by linarith : (0:ℝ) ≤ 1/4 - 3*δ/2)]
  ring

/-- **Any** positive saving breaks the chord `m(3) = 5/4`, once square-root shift cancellation is
available; without it the threshold is `δ > 1/6`. -/
theorem first_saving_breaks_chord {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1/6) :
    transferBound 3 (1/2) (1 - δ) < 5/4 ∧
      (transferBound 3 1 (1 - δ) < 5/4 ↔ 1/6 < δ) := by
  constructor
  · rw [transferBound_first_saving_sqrt h1]; linarith
  · rw [transferBound_first_saving_no_cancellation (by linarith : δ ≤ 1/3)]
    constructor <;> intro h <;> linarith

/-- The chord value at `k = 3` is `5/4`, so these comparisons are against the known bound. -/
theorem chord_at_three : momentChord (2*(3:ℝ)) = 5/4 := by
  unfold momentChord; norm_num

end FirstPowerSaving

end HTGeometry
