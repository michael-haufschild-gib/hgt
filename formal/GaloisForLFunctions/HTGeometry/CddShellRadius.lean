import GaloisForLFunctions.HTGeometry.HausdorffKernelSeries

/-!
# The shell radius attached to a CDD coupling

A paired CDD shell is fixed by `B = cosh η = (r + r⁻¹)/2` with `0 < r < 1`.  Solving for `r` gives

`r = B − √(B² − 1)`,

whose conjugate `B + √(B² − 1)` is its reciprocal.  Hence `r ≤ 1/B`, so a coupling family growing
geometrically produces a summable radius family — the finiteness input for the geometric q-ladder
source.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The shell radius attached to a coupling `B`: the root in `(0,1)` of `(r + r⁻¹)/2 = B`. -/
def shellRadius (B : ℝ) : ℝ := B - Real.sqrt (B ^ 2 - 1)

theorem sq_sqrt_shell {B : ℝ} (hB : 1 ≤ B) : Real.sqrt (B ^ 2 - 1) ^ 2 = B ^ 2 - 1 := by
  refine Real.sq_sqrt ?_
  nlinarith

theorem sqrt_shell_nonneg (B : ℝ) : 0 ≤ Real.sqrt (B ^ 2 - 1) := Real.sqrt_nonneg _

/-- The conjugate of the shell radius is its reciprocal. -/
theorem shellRadius_mul_conj {B : ℝ} (hB : 1 ≤ B) :
    shellRadius B * (B + Real.sqrt (B ^ 2 - 1)) = 1 := by
  rw [shellRadius]
  have h := sq_sqrt_shell hB
  nlinarith [h]

theorem shellRadius_pos {B : ℝ} (hB : 1 < B) : 0 < shellRadius B := by
  have hs := sqrt_shell_nonneg B
  have hconj := shellRadius_mul_conj hB.le
  have hsum : 0 < B + Real.sqrt (B ^ 2 - 1) := by linarith
  nlinarith [hconj, hsum]

theorem shellRadius_lt_one {B : ℝ} (hB : 1 < B) : shellRadius B < 1 := by
  have hlt : B - 1 < Real.sqrt (B ^ 2 - 1) := by
    have hnn : (0 : ℝ) ≤ B ^ 2 - 1 := by nlinarith
    have hsq : (B - 1) ^ 2 < B ^ 2 - 1 := by nlinarith
    have := Real.sqrt_lt_sqrt (by nlinarith) hsq
    rwa [Real.sqrt_sq (by linarith)] at this
  rw [shellRadius]
  linarith

/-- The shell radius is at most the reciprocal of its coupling. -/
theorem shellRadius_le_inv {B : ℝ} (hB : 1 < B) : shellRadius B ≤ 1 / B := by
  have hs := sqrt_shell_nonneg B
  have hconj := shellRadius_mul_conj hB.le
  have hr := shellRadius_pos hB
  have hBpos : 0 < B := by linarith
  rw [le_div_iff₀ hBpos]
  nlinarith [hconj, hs, hr]

/-- The shell radius reproduces its coupling as a hyperbolic cosine. -/
theorem shellRadius_add_inv {B : ℝ} (hB : 1 < B) :
    (shellRadius B + (shellRadius B)⁻¹) / 2 = B := by
  have hr := shellRadius_pos hB
  have hconj := shellRadius_mul_conj hB.le
  have hinv : (shellRadius B)⁻¹ = B + Real.sqrt (B ^ 2 - 1) := by
    field_simp at hconj ⊢
    linarith [hconj]
  rw [hinv, shellRadius]
  ring

/-- **The geometric ladder has summable radii.**  If the couplings grow like `C q^{-j}` with
`C > 1` and `0 < q < 1`, the shell radii are dominated by `q^j / C`. -/
theorem shellRadius_geometric_le {C q : ℝ} (hC : 1 < C) (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    shellRadius (C * q ^ (-(j : ℤ))) ≤ q ^ j / C := by
  have hqj : (0 : ℝ) < q ^ j := pow_pos hq0 j
  have hpow : q ^ (-(j : ℤ)) = (q ^ j)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hB : 1 < C * q ^ (-(j : ℤ)) := by
    rw [hpow]
    have hqle : q ^ j ≤ 1 := pow_le_one₀ hq0.le hq1.le
    have hge : (1 : ℝ) ≤ (q ^ j)⁻¹ := by
      rw [le_inv_comm₀ one_pos hqj]
      simpa using hqle
    nlinarith
  refine le_trans (shellRadius_le_inv hB) (le_of_eq ?_)
  rw [hpow]
  field_simp

end

end GaloisForLFunctions.HTGeometry
