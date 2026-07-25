/-
The three formulations of the ternary obstruction, and the loop they close.

Three objects are used interchangeably in the literature as "the input" for the sixth moment:

* the shift-average          `A(X,H) = Σ_{h≤H} Δ₃(X,h)`;
* the short-interval mean square  `B(X,h) = ∫_X^{2X}(Δ₃(x+h) − Δ₃(x))² dx`;
* the correlation itself      `D₃(X,h) = Σ_{n≤X} d₃(n)d₃(n+h)`.

Expanding `B` by the Voronoi series for `Δ₃` splits it into a diagonal and an off-diagonal.  The
exponent arithmetic below shows two things.  First, the **diagonal alone already produces the
conjectured answer** `B ≍ X h`, i.e. `β = 1`, comfortably inside the criterion `β < 3/2` that makes
the shift-average route work.  Second, the off-diagonal is `Σ_{j≠0} (Σ_m d₃(m)d₃(m+j)) w(j)` — that
is, `A` again.  So the reduction returns to its own starting point.
-/
import GaloisForLFunctions.HTGeometry.TernaryShiftAverageExponents

namespace HTGeometry

/-- Shift length in the sixth-moment application, as an exponent of `X`. -/
def loopShift : ℚ := 1/3

/-- Exponent of the diagonal of the Voronoi expansion of the short-interval mean square: the two
ranges `m ≤ X²/h³` and `m > X²/h³` each contribute `h X^{-2/3}` to the coefficient sum, and the
prefactor is `X^{5/3}`, giving `X h`. -/
def diagonalMeanSquareBeta : ℚ := 1

/-- **The diagonal already meets the criterion.**  `β = 1 < 3/2`, so if the off-diagonal were
negligible the shift-average route would go through. -/
theorem diagonal_meets_criterion : shortIntervalOutput diagonalMeanSquareBeta < 1 := by
  rw [shortIntervalOutput_lt_one_iff]
  unfold diagonalMeanSquareBeta; norm_num

/-- The diagonal's output exponent is `5/6`, well below the envelope value `1`. -/
theorem diagonal_output : shortIntervalOutput diagonalMeanSquareBeta = 5/6 := by
  unfold shortIntervalOutput diagonalMeanSquareBeta; norm_num

/-- Exponent of the off-diagonal budget at `h = X^{1/3}`: the criterion `β < 3/2` permits
`X^{1+3/2·(1/3)} = X^{3/2}`. -/
def offDiagonalBudget : ℚ := 1 + (3/2) * loopShift

theorem offDiagonalBudget_eq : offDiagonalBudget = 3/2 := by
  unfold offDiagonalBudget loopShift; norm_num

/-- Exponent of the off-diagonal under the first-derivative test alone, with the dual truncated at
`M ≍ X`: the near-diagonal `|m − m'| = j` contributes `m^{2/3}/|j|`, summing to `X^{4/3}·X^{1/3}`. -/
def offDiagonalCrude : ℚ := 4/3 + 1/3

theorem offDiagonalCrude_eq : offDiagonalCrude = 5/3 := by
  unfold offDiagonalCrude; norm_num

/-- **The gap is `X^{1/6}` — the campaign's recurring number.** -/
theorem offDiagonal_gap : offDiagonalCrude - offDiagonalBudget = 1/6 := by
  rw [offDiagonalCrude_eq, offDiagonalBudget_eq]; norm_num

/-- **The loop.**  The diagonal meets the criterion with room to spare, so the entire obstruction is
the off-diagonal; and the off-diagonal, grouped by `j = m' − m`, is `Σ_j (Σ_m d₃(m)d₃(m+j)) w(j)` —
the ternary correlation averaged over shifts, which is the object the reduction started from.  The
three formulations are therefore equivalent modulo their diagonals. -/
theorem reduction_loop :
    shortIntervalOutput diagonalMeanSquareBeta < 1 ∧
    offDiagonalCrude - offDiagonalBudget = 1/6 ∧
    offDiagonalBudget < offDiagonalCrude := by
  refine ⟨diagonal_meets_criterion, offDiagonal_gap, ?_⟩
  rw [offDiagonalCrude_eq, offDiagonalBudget_eq]; norm_num

/-- Running the whole chain at a general shift exponent `θ` (`H = x^θ`) rather than at `1/3`.  The
Voronoi wavelength `L = x^{1/3}` is set by the phase, not by the shift, so the short-interval mean
square is always taken at `h = L`; only the prefactor `H` and the target change.  The criterion on
the mean-square exponent becomes `β < 2 - 3θ/2`. -/
def meanSquareCriterion (θ : ℚ) : ℚ := 2 - 3 * θ / 2

@[simp] theorem meanSquareCriterion_third : meanSquareCriterion (1/3) = 3/2 := by
  unfold meanSquareCriterion; norm_num

/-- The conjectured truth `β = 1` clears the criterion exactly for `θ < 2/3`. -/
theorem meanSquareCriterion_true_beta {θ : ℚ} : (1 : ℚ) < meanSquareCriterion θ ↔ θ < 2/3 := by
  unfold meanSquareCriterion
  constructor <;> intro h <;> linarith

/-- The off-diagonal saving `η` needed for zero gain: exactly `θ/2`, half the shift exponent.  This
confirms the shape conjectured at the end of cycle 55. -/
def zeroGainSaving (θ : ℚ) : ℚ := θ / 2

/-- **But the shift exponent cancels.**  With an off-diagonal saving `η`, the chain yields
`Σ_{h≤H}Δ₃ ≪ x^{θ + 1 - η} = H·x^{1-η}` — a shift exponent of `a = 1`, not `1/2`, for every `θ`.  So
the apparent `θ`-dependence is an artefact of the parametrisation. -/
def chainOutputB (θ η : ℚ) : ℚ := 1 + θ / 2 - η

theorem chainOutput_as_averaged_input (θ η : ℚ) :
    θ / 2 + chainOutputB θ η = θ + (1 - η) := by
  unfold chainOutputB; ring

/-- **The invariant demand.**  Written in `(a,b) = (1, 1-η)` form the requirement is the averaged-input
threshold of `C110`, `η > 1/2 - 1/k`, which at `k = 3` is `1/6` — independently of `θ`. -/
def recurringGap (k : ℚ) : ℚ := 1/2 - 1/k

@[simp] theorem recurringGap_three : recurringGap 3 = 1/6 := by
  unfold recurringGap; norm_num

@[simp] theorem recurringGap_two : recurringGap 2 = 0 := by
  unfold recurringGap; norm_num

/-- **Why `k = 2` is free.**  The recurring gap vanishes exactly at `k = 2`: there the square-root
barrier and the reciprocal of the moment index coincide, so no saving is demanded at all. -/
theorem recurringGap_eq_zero_iff {k : ℚ} (hk : k ≠ 0) : recurringGap k = 0 ↔ k = 2 := by
  unfold recurringGap
  constructor
  · intro h
    field_simp at h
    linarith
  · rintro rfl; norm_num

/-- The gap is strictly increasing in `k`, so every higher moment demands strictly more. -/
theorem recurringGap_strictMono {k l : ℚ} (hk : 0 < k) (hkl : k < l) :
    recurringGap k < recurringGap l := by
  unfold recurringGap
  have hl : (0 : ℚ) < l := lt_trans hk hkl
  have : 1 / l < 1 / k := by
    rw [div_lt_div_iff₀ hl hk]; linarith
  linarith

end HTGeometry
