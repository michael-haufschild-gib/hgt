import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.LogarithmicCollisionCells

/-!
# The inverse-square resolution cannot be improved in order

The pairs `(n+1,n+4)` and `(n+2,n+3)` have products differing by two,
both before and after any common translation. Their logarithmic readings
are within `2/(n+1)²`, despite being different unordered pairs.
-/

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

private theorem log_add_two_gap_le {x : ℝ} (hx : 0 < x) :
    |Real.log (x + 2) - Real.log x| ≤ 2 / x := by
  have hxp : 0 < x + 2 := by linarith only [hx]
  have hratio : 0 < (x + 2) / x := div_pos hxp hx
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hxp.ne' hx.ne'] at hlog
  have hmono : Real.log x ≤ Real.log (x + 2) :=
    Real.log_le_log hx (by linarith only [hx])
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  have he : (x + 2) / x - 1 = 2 / x := by field_simp; ring
  linarith only [hlog, he]

/-- Different pairs with the same sum have translated products only two apart. -/
theorem neighbouring_pair_product_gap (n h : ℕ) :
    (n + 2 + h) * (n + 3 + h) = (n + 1 + h) * (n + 4 + h) + 2 := by
  ring

/-- Every translated logarithmic reading of these pairs is close at inverse-square scale. -/
theorem neighbouring_pair_log_gap (n h : ℕ) :
    |Real.log ((n + 2 + h) * (n + 3 + h) : ℕ) -
      Real.log ((n + 1 + h) * (n + 4 + h) : ℕ)| ≤
      2 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have hx : (0 : ℝ) < ((n + 1 + h) * (n + 4 + h) : ℕ) := by positivity
  rw [neighbouring_pair_product_gap, Nat.cast_add, Nat.cast_ofNat]
  refine (log_add_two_gap_le hx).trans ?_
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hbound : (n + 1) ^ 2 ≤ (n + 1 + h) * (n + 4 + h) := by
    simpa only [pow_two] using Nat.mul_le_mul
      (show n + 1 ≤ n + 1 + h by omega) (show n + 1 ≤ n + 4 + h by omega)
  exact_mod_cast hbound

/-- The close pair signatures are genuinely distinct for every `n`. -/
theorem neighbouring_pair_signatures_ne (n : ℕ) :
    pairSignature (n + 1) (n + 4) ≠ pairSignature (n + 2) (n + 3) := by
  rw [ne_eq, pairSignature_eq_iff]
  omega

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
