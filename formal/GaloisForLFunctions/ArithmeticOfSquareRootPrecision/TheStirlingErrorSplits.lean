import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.MonotoneErrorsInvertAtMertensPrecision

/-!
# The Stirling error splits into a monotone part and a sawtooth

The count is the inversion of the Chebyshev identity: `ψ(n) = I_n(log ⌊·⌋!)`
(`psi_eq_inversionOp_log_factorial`). Write `F(t) = t log t − t`. The identity function splits as

`log ⌊y⌋! = F(y) + G(y) + h(y)`  (`log_factorial_floor_eq`),

* `G(y) = log ⌊y⌋! − F(⌊y⌋)`, **monotone** (`monotoneOn_stirlingStep`): `g(n + 1) − g(n) =
  1 − n log(1 + 1/n) ≥ 0`, and `0 ≤ G(y) ≤ 1 + ½ log y` (Stirling);
* `h(y) = F(⌊y⌋) − F(y)`, a **sawtooth** with `−log y ≤ h(y) ≤ 0` for `y ≥ 1`
  (`sawtooth_bounds`), by convexity of `t log t`.

**The Stirling split** (`abs_psi_sub_smooth_sub_sawtooth_le`): if `|M(k)| ≤ K` for `k ≤ n`, then

`|ψ(n) − I_n(F) − I_n(h)| ≤ 3 (1 + ½ log n) K`.

The monotone part of the Stirling error is inverted at Mertens precision. All further precision of
Chebyshev's method lives in two inversions: of the smooth main term `F` and of the sawtooth `h`, whose
amplitude is only `log y` but which oscillates at every integer.
-/

noncomputable section

open Real Finset

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The smooth main term `F(t) = t log t − t`. -/
def stirlingMain (t : ℝ) : ℝ := t * Real.log t - t

/-- The integer Stirling step `g(n) = log n! − F(n)`. -/
def stirlingStep (n : ℕ) : ℝ := Real.log (n.factorial : ℕ) - stirlingMain n

/-- The monotone part `G(y) = g(⌊y⌋)`. -/
def stirlingMonotone (y : ℝ) : ℝ := stirlingStep ⌊y⌋₊

/-- The sawtooth `h(y) = F(⌊y⌋) − F(y)`. -/
def stirlingSawtooth (y : ℝ) : ℝ := stirlingMain ⌊y⌋₊ - stirlingMain y

theorem log_factorial_floor_eq (y : ℝ) :
    Real.log ((⌊y⌋₊).factorial : ℕ) = stirlingMain y + stirlingMonotone y + stirlingSawtooth y := by
  unfold stirlingMonotone stirlingSawtooth stirlingStep; ring

/-- `g(n + 1) ≥ g(n)`: `g(n + 1) − g(n) = 1 − n log(1 + 1/n) ≥ 0`. -/
theorem stirlingStep_le_succ (n : ℕ) : stirlingStep n ≤ stirlingStep (n + 1) := by
  unfold stirlingStep stirlingMain
  rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity)
    (by exact_mod_cast (Nat.factorial_pos n).ne')]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- `n (log (n+1) − log n) ≤ 1` from `log t ≤ t − 1` at `t = (n+1)/n`
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n ≤ 1 / n := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at h
    push_cast
    have : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  have hmul : (n : ℝ) * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hlog hn0.le
    rwa [mul_one_div_cancel hn0.ne'] at this
  push_cast at hmul ⊢
  nlinarith

theorem stirlingStep_mono : Monotone stirlingStep := monotone_nat_of_le_succ stirlingStep_le_succ

/-- **The monotone part is monotone.** -/
theorem monotoneOn_stirlingMonotone : MonotoneOn stirlingMonotone (Set.Ioi 0) :=
  fun _ _ _ _ hxy => stirlingStep_mono (Nat.floor_le_floor hxy)

theorem stirlingStep_zero : stirlingStep 0 = 0 := by simp [stirlingStep, stirlingMain]

/-- `0 ≤ G(y) ≤ 1 + ½ log x` for `0 < y ≤ x`, `x ≥ 1`. -/
theorem stirlingMonotone_bounds {x y : ℝ} (hx : 1 ≤ x) (hy : 0 < y) (hyx : y ≤ x) :
    0 ≤ stirlingMonotone y ∧ stirlingMonotone y ≤ 1 + Real.log x / 2 := by
  unfold stirlingMonotone
  rcases Nat.eq_zero_or_pos ⌊y⌋₊ with h0 | hpos
  · rw [h0, stirlingStep_zero]
    exact ⟨le_rfl, by have := Real.log_nonneg hx; linarith⟩
  have hb := log_factorial_sub_bounds hpos
  have hfl : (⌊y⌋₊ : ℝ) ≤ x := (Nat.floor_le hy.le).trans hyx
  have hl : Real.log ⌊y⌋₊ ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hpos) hfl
  unfold stirlingStep stirlingMain
  constructor <;> linarith [hb.1, hb.2]

/-- **The sawtooth has amplitude `log y`**: `−log y ≤ h(y) ≤ 0` for `y ≥ 1`. -/
theorem sawtooth_bounds {y : ℝ} (hy : 1 ≤ y) :
    -Real.log y ≤ stirlingSawtooth y ∧ stirlingSawtooth y ≤ 0 := by
  set m : ℝ := (⌊y⌋₊ : ℝ) with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast Nat.one_le_floor_iff y |>.mpr hy
  have hmy : m ≤ y := Nat.floor_le (by linarith)
  have hym : y - m < 1 := by rw [hm]; linarith [Nat.lt_floor_add_one y]
  have hm0 : 0 < m := by linarith
  have hy0 : 0 < y := by linarith
  -- tangent line of `t log t` at `m`: `y log y ≥ m log m + (1 + log m)(y − m)`
  have htan : m * Real.log m + (1 + Real.log m) * (y - m) ≤ y * Real.log y := by
    have h := RHTower.one_sub_inv_le_log (show 0 < y / m by positivity)
    rw [Real.log_div hy0.ne' hm0.ne'] at h
    have h' : y * (1 - 1 / (y / m)) ≤ y * (Real.log y - Real.log m) :=
      mul_le_mul_of_nonneg_left h hy0.le
    have : y * (1 - 1 / (y / m)) = y - m := by field_simp
    nlinarith
  -- secant bound: `log y − log m ≤ (y − m)/m`
  have hsec : Real.log y - Real.log m ≤ (y - m) / m := by
    have h := Real.log_le_sub_one_of_pos (show 0 < y / m by positivity)
    rw [Real.log_div hy0.ne' hm0.ne'] at h
    have : y / m - 1 = (y - m) / m := by field_simp
    linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hsec' : m * (Real.log y - Real.log m) ≤ y - m := by
    have := mul_le_mul_of_nonneg_left hsec hm0.le
    rwa [mul_div_cancel₀ _ hm0.ne'] at this
  unfold stirlingSawtooth stirlingMain
  rw [← hm]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hym.le hlogy]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hmy) hlogm]

/-! ### The split of the count -/

theorem inversionOp_add (E₁ E₂ : ℝ → ℝ) (x : ℝ) :
    inversionOp (fun y => E₁ y + E₂ y) x = inversionOp E₁ x + inversionOp E₂ x := by
  simp only [inversionOp, mul_add, sum_add_distrib]

/-- **The count is the inversion of `log ⌊·⌋!`**: `ψ(n) = I_n(log ⌊·⌋!)`. -/
theorem psi_eq_inversionOp_log_factorial (n : ℕ) :
    Chebyshev.psi n = inversionOp (fun y => Real.log ((⌊y⌋₊).factorial : ℕ)) n := by
  rw [psi_eq_sum_moebius_log_factorial, inversionOp, Nat.floor_natCast]
  refine sum_congr rfl fun k hk => ?_
  rw [Nat.floor_div_eq_div]

/-- **The Stirling split.** If `|M(k)| ≤ K` for `k ≤ n`, then
`|ψ(n) − I_n(F) − I_n(h)| ≤ 3 (1 + ½ log n) K`. -/
theorem abs_psi_sub_smooth_sub_sawtooth_le {n : ℕ} (hn : 1 ≤ n) {K : ℝ}
    (hK : ∀ k : ℕ, k ≤ n → |mertens k| ≤ K) :
    |Chebyshev.psi n - inversionOp stirlingMain n - inversionOp stirlingSawtooth n| ≤
      3 * (1 + Real.log n / 2) * K := by
  have hsplit : Chebyshev.psi n = inversionOp stirlingMain n + inversionOp stirlingMonotone n +
      inversionOp stirlingSawtooth n := by
    rw [psi_eq_inversionOp_log_factorial]
    simp_rw [log_factorial_floor_eq]
    rw [inversionOp_add (fun y => stirlingMain y + stirlingMonotone y), inversionOp_add]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : ∀ y, 0 < y → y ≤ (n : ℝ) → |stirlingMonotone y| ≤ 1 + Real.log n / 2 := fun y hy hyn => by
    obtain ⟨h0, h1⟩ := stirlingMonotone_bounds hn1 hy hyn
    rw [abs_of_nonneg h0]; exact h1
  have hmono := abs_inversionOp_le_of_monotoneOn monotoneOn_stirlingMonotone (by linarith) hB
    (by rw [Nat.floor_natCast]; exact hK)
  rw [hsplit]
  calc |inversionOp stirlingMain n + inversionOp stirlingMonotone n + inversionOp stirlingSawtooth n -
        inversionOp stirlingMain n - inversionOp stirlingSawtooth n|
      = |inversionOp stirlingMonotone n| := by ring_nf
    _ ≤ 3 * (1 + Real.log n / 2) * K := hmono

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision

#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.eq_of_chebyshevTransform_eq
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.not_inversion_bounded
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.abs_inversionOp_le_of_monotoneOn
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.not_monotone_inversion_lt_half
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.riemannHypothesis_iff_monotone_inversion
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.sawtooth_bounds
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.abs_psi_sub_smooth_sub_sawtooth_le
