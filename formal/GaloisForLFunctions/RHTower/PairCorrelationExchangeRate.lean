import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The exchange rate between pair correlation beyond `1` and the critical-line proportion

In the rank–trace certificate at bandwidth `λ` (sharp taper), the normalised Frobenius norm of the Gram
matrix is

`c(λ) = 1/λ + (2/λ²) ∫₀^λ (λ − α) F(α) dα`,

where `F` is the pair-correlation form factor (`F(α) = α` on `[0, 1]`, the term `1/λ` being the
diagonal), and the certified proportion is `2 − c(λ)`.  If `F ≤ B` on `(1, λ)` then
(`frobenius_density_integral`)

`c(λ) ≤ 2/λ − 2/(3λ²) + B (λ − 1)²/λ²`,

and the best certified proportion over all `λ` is exactly (`certValue_le_opt`, `certValue_at_opt`)

`H*(B) = (2B − 1)/(3B − 2)`,   attained at `λ* = (3B − 2)/(3(B − 1))`.

Consequences:
* every finite bound `B` beats `2/3`, by exactly `1/(3(3B − 2))` (`opt_sub_two_thirds`): the obstruction
  beyond bandwidth one is boundedness of `F` just above `1`, not its value;
* `H*(B) ≥ 3/4` if and only if `B ≤ 2` (`opt_ge_three_quarters_iff`): three quarters on the line is
  equivalent, for this certificate, to `F ≤ 2` on `(1, 4/3)`;
* `H*(1) = 1`: the random-matrix value `F = 1` gives the full proportion in the limit `λ → ∞`;
* three quarters at bandwidth `λ` holds iff `B(λ − 1)² ≤ (5/4)λ² − 2λ + 2/3`
  (`three_quarters_le_certValue_iff`); the right side is `2(λ − 1)² − (3/4)(λ − 4/3)²`
  (`feasibility_le_two`), so no bandwidth tolerates an average `F` above `2`, and even `F = 1` needs
  `λ ≥ 2/√3` (`three_quarters_le_certValue_one_iff`).
-/

open Real intervalIntegral

noncomputable section

namespace RHTower

/-- The certified proportion at bandwidth `λ` when `F ≤ B` beyond `1`. -/
def certValue (lam B : ℝ) : ℝ := 2 - (2 / lam - 2 / (3 * lam ^ 2) + B * (lam - 1) ^ 2 / lam ^ 2)

/-- The optimal proportion `H*(B) = (2B − 1)/(3B − 2)`. -/
def certOpt (B : ℝ) : ℝ := (2 * B - 1) / (3 * B - 2)

/-- **The Frobenius integral with `F = α` on `[0,1]` and `F = B` on `[1, λ]`.** -/
theorem frobenius_density_integral (lam B : ℝ) :
    1 / lam + 2 / lam ^ 2 * ((∫ α in (0:ℝ)..1, (lam - α) * α) + ∫ α in (1:ℝ)..lam, (lam - α) * B)
      = 2 / lam - 2 / (3 * lam ^ 2) + B * (lam - 1) ^ 2 / lam ^ 2 := by
  have h1 : ∫ α in (0:ℝ)..1, (lam - α) * α = lam / 2 - 1 / 3 := by
    have e : (fun α : ℝ => (lam - α) * α) = fun α => lam * α - α ^ 2 := by funext α; ring
    rw [e, integral_sub ((by fun_prop : Continuous fun α : ℝ => lam * α).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun α : ℝ => α ^ 2).intervalIntegrable _ _), integral_const_mul,
      integral_id, integral_pow]
    norm_num; ring
  have h2 : ∫ α in (1:ℝ)..lam, (lam - α) * B = B * (lam - 1) ^ 2 / 2 := by
    have e : (fun α : ℝ => (lam - α) * B) = fun α => B * lam - B * α := by funext α; ring
    rw [e, integral_sub ((by fun_prop : Continuous fun _ : ℝ => B * lam).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun α : ℝ => B * α).intervalIntegrable _ _), integral_const,
      integral_const_mul, integral_id]
    simp only [smul_eq_mul]; ring
  rw [h1, h2]
  rcases eq_or_ne lam 0 with h | h
  · subst h; simp
  · field_simp; ring

/-- **The certified proportion is a concave quadratic in `1/λ`, maximal at `λ*`.** -/
theorem certOpt_sub_certValue {B : ℝ} (hB : 2 / 3 < B) {lam : ℝ} (hlam : lam ≠ 0) :
    certOpt B - certValue lam B
      = (B - 2 / 3) * (1 / lam - 3 * (B - 1) / (3 * B - 2)) ^ 2 := by
  have h3 : 3 * B - 2 ≠ 0 := by intro h; linarith
  have hE : (3 * B - 2) * (3 * B - 2)⁻¹ = 1 := mul_inv_cancel₀ h3
  have hL : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam
  unfold certOpt certValue
  linear_combination (2 * (B - 1) * lam⁻¹ - (B - 2) - 3 * (B - 1) ^ 2 * (3 * B - 2)⁻¹) * hE
    + B * (1 - 2 * lam⁻¹ + lam * lam⁻¹) * hL

theorem certValue_le_opt {B : ℝ} (hB : 2 / 3 < B) {lam : ℝ} (hlam : lam ≠ 0) :
    certValue lam B ≤ certOpt B := by
  have h := certOpt_sub_certValue hB hlam
  have : 0 ≤ (B - 2 / 3) * (1 / lam - 3 * (B - 1) / (3 * B - 2)) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- The optimum is attained at `λ* = (3B − 2)/(3(B − 1))`. -/
theorem certValue_at_opt {B : ℝ} (hB : 1 < B) :
    certValue ((3 * B - 2) / (3 * (B - 1))) B = certOpt B := by
  have hB1 : B - 1 ≠ 0 := by intro h; linarith
  have h3 : 3 * B - 2 ≠ 0 := by intro h; linarith
  have hlam : (3 * B - 2) / (3 * (B - 1)) ≠ 0 := div_ne_zero h3 (mul_ne_zero (by norm_num) hB1)
  have h := certOpt_sub_certValue (by linarith : 2 / 3 < B) hlam
  have e : 1 / ((3 * B - 2) / (3 * (B - 1))) - 3 * (B - 1) / (3 * B - 2) = 0 := by
    rw [one_div_div]; ring
  rw [e] at h
  linarith [h, show (B - 2 / 3) * (0:ℝ) ^ 2 = 0 by ring]

/-- **Every finite bound beats two thirds**, by exactly `1/(3(3B − 2))`. -/
theorem opt_sub_two_thirds {B : ℝ} (hB : 2 / 3 < B) : certOpt B - 2 / 3 = 1 / (3 * (3 * B - 2)) := by
  have h3 : 0 < 3 * B - 2 := by linarith
  unfold certOpt
  rw [div_sub_div _ _ h3.ne' (by norm_num), div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem two_thirds_lt_opt {B : ℝ} (hB : 2 / 3 < B) : 2 / 3 < certOpt B := by
  have h := opt_sub_two_thirds hB
  have : 0 < 1 / (3 * (3 * B - 2)) := by
    have : 0 < 3 * B - 2 := by linarith
    positivity
  linarith

/-- **Three quarters on the line ⟺ `F ≤ 2` beyond one.** -/
theorem opt_ge_three_quarters_iff {B : ℝ} (hB : 2 / 3 < B) : 3 / 4 ≤ certOpt B ↔ B ≤ 2 := by
  have h3 : 0 < 3 * B - 2 := by linarith
  unfold certOpt
  rw [le_div_iff₀ h3]
  constructor <;> intro h <;> linarith

/-- The random-matrix value `B = 1` gives the full proportion. -/
theorem certOpt_one : certOpt 1 = 1 := by unfold certOpt; norm_num

/-- `B = 2` gives exactly three quarters, at `λ* = 4/3`. -/
theorem certValue_four_thirds_two : certValue (4 / 3) 2 = 3 / 4 := by
  unfold certValue; norm_num

/-- **The feasibility region for three quarters.**  For `λ ≠ 0`,
`certValue λ B ≥ 3/4 ⟺ B (λ − 1)² ≤ (5/4) λ² − 2λ + 2/3`. -/
theorem three_quarters_le_certValue_iff {lam B : ℝ} (hlam : lam ≠ 0) :
    3 / 4 ≤ certValue lam B ↔ B * (lam - 1) ^ 2 ≤ 5 / 4 * lam ^ 2 - 2 * lam + 2 / 3 := by
  have hl2 : 0 < lam ^ 2 := by positivity
  have e : certValue lam B - 3 / 4
      = (5 / 4 * lam ^ 2 - 2 * lam + 2 / 3 - B * (lam - 1) ^ 2) / lam ^ 2 := by
    unfold certValue; field_simp; ring
  constructor
  · intro h
    have : 0 ≤ (5 / 4 * lam ^ 2 - 2 * lam + 2 / 3 - B * (lam - 1) ^ 2) / lam ^ 2 := by linarith
    have := (div_nonneg_iff.mp this)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · linarith
    · linarith
  · intro h
    have : 0 ≤ (5 / 4 * lam ^ 2 - 2 * lam + 2 / 3 - B * (lam - 1) ^ 2) / lam ^ 2 :=
      div_nonneg (by linarith) hl2.le
    linarith

/-- **`2` is the universal ceiling**: `(5/4)λ² − 2λ + 2/3 ≤ 2(λ − 1)²` for every `λ`, with equality only at
`λ = 4/3`.  So three quarters is impossible for this certificate if `F` exceeds `2` on average beyond `1`,
whatever the bandwidth. -/
theorem feasibility_le_two (lam : ℝ) :
    5 / 4 * lam ^ 2 - 2 * lam + 2 / 3 = 2 * (lam - 1) ^ 2 - 3 / 4 * (lam - 4 / 3) ^ 2 := by
  ring

/-- **The minimal bandwidth.**  Even with the random-matrix value `B = 1`, three quarters needs
`λ² ≥ 4/3`, i.e. pair correlation up to `2/√3 ≈ 1.1547`. -/
theorem three_quarters_le_certValue_one_iff {lam : ℝ} (hlam : 0 < lam) :
    3 / 4 ≤ certValue lam 1 ↔ 4 / 3 ≤ lam ^ 2 := by
  rw [three_quarters_le_certValue_iff hlam.ne']
  constructor <;> intro h <;> nlinarith

end RHTower
