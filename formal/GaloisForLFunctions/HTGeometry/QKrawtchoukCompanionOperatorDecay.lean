import GaloisForLFunctions.HTGeometry.QKrawtchoukCoefficientLimits

/-!
# Summable control of the companion Jacobi coefficients

The balanced finite matrices from arXiv:2609.24149, Section 8, admit one
geometric envelope after extension by zero to the common sequence space.
The envelope is summable and also controls the limiting coefficients.
This supplies the domination needed to pass from coefficient convergence
to convergence of actual operators in norm.
-/

noncomputable section
open Filter
open scoped Topology

namespace HTGeometry

/-- The limiting bond between coordinates `n` and `n+1`. -/
def alSalamCarlitzJacobiBond (t u : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (alSalamCarlitzLower t u (n + 1))

/-- The finite diagonal extended by zero outside coordinates `0,...,2K`. -/
def qKrawtchoukCompanionBlockDiagonal (t u : ℝ) (K n : ℕ) : ℝ :=
  if n ≤ 2 * K then qKrawtchoukCompanionFiniteDiagonal t u K n else 0

/-- The finite off-diagonal extended by zero outside bonds `0,...,2K-1`. -/
def qKrawtchoukCompanionBlockBond (t u : ℝ) (K n : ℕ) : ℝ :=
  if n < 2 * K then Real.sqrt (qKrawtchoukCompanionFiniteLower t u K (n + 1)) else 0

/-- One summable envelope for the full three-term operator at each coordinate. -/
def alSalamCarlitzJacobiEnvelope (t u : ℝ) (n : ℕ) : ℝ :=
  (2 + 2 * Real.exp u + 2 * Real.exp (u / 2)) * Real.exp (-Real.exp t / 2) ^ n

private theorem half_pow (t : ℝ) (n : ℕ) :
    Real.exp (-Real.exp t / 2) ^ n = Real.exp (-Real.exp t * n / 2) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem base_pow (t : ℝ) (n : ℕ) :
    qKrawtchoukEdgeBase t ^ n = Real.exp (-Real.exp t * n) := by
  rw [qKrawtchoukEdgeBase, ← Real.exp_nat_mul]
  congr 1
  ring

private theorem full_le_half (t : ℝ) (n : ℕ) :
    Real.exp (-Real.exp t * n) ≤ Real.exp (-Real.exp t / 2) ^ n := by
  rw [half_pow]
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ Real.exp t * (n : ℝ) := by positivity
  linarith

private theorem finite_base_le_half (t : ℝ) (K n : ℕ) (hn : n ≤ 2 * K) :
    qKrawtchoukEdgeBase t ^ K ≤ Real.exp (-Real.exp t / 2) ^ n := by
  rw [base_pow, half_pow]
  apply Real.exp_le_exp.mpr
  have h : (n : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hn
  nlinarith [mul_le_mul_of_nonneg_left h (Real.exp_pos t).le]

private theorem diagonal_decay (t u : ℝ) (n : ℕ) :
    |alSalamCarlitzDiagonal t u n| ≤
      (1 + Real.exp u) * Real.exp (-Real.exp t / 2) ^ n := by
  have hc : |1 - Real.exp u| ≤ 1 + Real.exp u := by
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos u]
  rw [alSalamCarlitzDiagonal, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul hc (full_le_half t n) (Real.exp_pos _).le (by positivity)

private theorem bond_decay (t u : ℝ) (n : ℕ) :
    |alSalamCarlitzJacobiBond t u n| ≤
      Real.exp (u / 2) * Real.exp (-Real.exp t / 2) ^ n := by
  rw [alSalamCarlitzJacobiBond, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hs : (Real.exp (u / 2) * Real.exp (-Real.exp t / 2) ^ n) ^ 2 =
      Real.exp u * Real.exp (-Real.exp t * n) := by
    rw [half_pow, pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hs]
  simp only [alSalamCarlitzLower, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have h := mul_le_mul_of_nonneg_left
    (show 1 - Real.exp (-Real.exp t * ((n : ℝ) + 1)) ≤ 1 by
      linarith [Real.exp_pos (-Real.exp t * ((n : ℝ) + 1))])
    (show 0 ≤ Real.exp u * Real.exp (-Real.exp t * (n : ℝ)) by positivity)
  simpa only [mul_one] using h

private theorem finite_diagonal_decay (t u : ℝ) (K n : ℕ) :
    |qKrawtchoukCompanionBlockDiagonal t u K n| ≤
      (2 + 2 * Real.exp u) * Real.exp (-Real.exp t / 2) ^ n := by
  unfold qKrawtchoukCompanionBlockDiagonal
  split_ifs with hn
  · have hc : |Real.exp u - 1| ≤ 1 + Real.exp u := by
      rw [abs_le]
      constructor <;> linarith [Real.exp_pos u]
    have hbase : 0 ≤ qKrawtchoukEdgeBase t ^ K := by rw [base_pow]; positivity
    rw [qKrawtchoukCompanionFiniteDiagonal]
    calc
      _ ≤ |alSalamCarlitzDiagonal t u n| +
          |(Real.exp u - 1) * qKrawtchoukEdgeBase t ^ K| := abs_add_le _ _
      _ = |alSalamCarlitzDiagonal t u n| +
          |Real.exp u - 1| * qKrawtchoukEdgeBase t ^ K := by
        rw [abs_mul, abs_of_nonneg hbase]
      _ ≤ (1 + Real.exp u) * Real.exp (-Real.exp t / 2) ^ n +
          (1 + Real.exp u) * Real.exp (-Real.exp t / 2) ^ n :=
        add_le_add (diagonal_decay t u n)
          (mul_le_mul hc (finite_base_le_half t K n hn) hbase (by positivity))
      _ = _ := by ring
  · simp only [abs_zero]
    positivity

private theorem finite_bond_decay (t u : ℝ) (K n : ℕ) :
    |qKrawtchoukCompanionBlockBond t u K n| ≤
      Real.exp (u / 2) * Real.exp (-Real.exp t / 2) ^ n := by
  unfold qKrawtchoukCompanionBlockBond
  split_ifs with hn
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hcut : qKrawtchoukEdgeCutoff t K (n + 1) ≤ 1 := by
      rw [qKrawtchoukEdgeCutoff_eq]
      linarith [Real.exp_pos (-Real.exp t * (2 * (K : ℝ) - ((n + 1 : ℕ) : ℝ) + 1))]
    have hb : qKrawtchoukCompanionFiniteLower t u K (n + 1) ≤
        alSalamCarlitzLower t u (n + 1) := by
      simpa only [qKrawtchoukCompanionFiniteLower, mul_one] using
        mul_le_mul_of_nonneg_left hcut (alSalamCarlitzLower_succ_pos t u n).le
    apply (Real.sqrt_le_sqrt hb).trans
    simpa only [alSalamCarlitzJacobiBond, abs_of_nonneg (Real.sqrt_nonneg _)] using
      bond_decay t u n
  · simp only [abs_zero]
    positivity

/-- Geometric decay makes the common Jacobi envelope summable. -/
theorem summable_alSalamCarlitzJacobiEnvelope (t u : ℝ) :
    Summable (alSalamCarlitzJacobiEnvelope t u) := by
  have hq : Real.exp (-Real.exp t / 2) < 1 := Real.exp_lt_one_iff.mpr (by
    have := Real.exp_pos t
    linarith)
  exact (summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left _

/-- The limiting three-term coefficients fit the summable envelope. -/
theorem alSalamCarlitzJacobi_coeff_bound (t u : ℝ) (n : ℕ) :
    |alSalamCarlitzDiagonal t u n| + 2 * |alSalamCarlitzJacobiBond t u n| ≤
      alSalamCarlitzJacobiEnvelope t u n := by
  have hd := diagonal_decay t u n
  have ha := bond_decay t u n
  have hp : 0 ≤ Real.exp (-Real.exp t / 2) ^ n := by positivity
  have hd' := hd.trans (mul_le_mul_of_nonneg_right
    (show 1 + Real.exp u ≤ 2 + 2 * Real.exp u by linarith [Real.exp_pos u]) hp)
  unfold alSalamCarlitzJacobiEnvelope
  nlinarith

/-- The same summable envelope controls every extended finite matrix. -/
theorem qKrawtchoukCompanionBlock_coeff_bound (t u : ℝ) (K n : ℕ) :
    |qKrawtchoukCompanionBlockDiagonal t u K n| +
        2 * |qKrawtchoukCompanionBlockBond t u K n| ≤
      alSalamCarlitzJacobiEnvelope t u n := by
  have hd := finite_diagonal_decay t u K n
  have ha := finite_bond_decay t u K n
  unfold alSalamCarlitzJacobiEnvelope
  nlinarith

/-- Both coefficients converge on the common coordinate space after zero extension. -/
theorem qKrawtchoukCompanionBlock_coeff_tendsto (t u : ℝ) (n : ℕ) :
    Tendsto (fun K => qKrawtchoukCompanionBlockDiagonal t u K n) atTop
      (𝓝 (alSalamCarlitzDiagonal t u n)) ∧
    Tendsto (fun K => qKrawtchoukCompanionBlockBond t u K n) atTop
      (𝓝 (alSalamCarlitzJacobiBond t u n)) := by
  constructor
  · have hd := qKrawtchoukCompanionFiniteDiagonal_tendsto t u n
    rw [alSalamCarlitzMoment_alpha] at hd
    apply hd.congr'
    filter_upwards [eventually_ge_atTop (n + 1)] with K hK
    simp only [qKrawtchoukCompanionBlockDiagonal, if_pos (show n ≤ 2 * K by omega)]
  · apply ((qKrawtchoukCompanionFiniteLower_tendsto t u (n + 1)).sqrt).congr'
    filter_upwards [eventually_ge_atTop (n + 1)] with K hK
    simp only [qKrawtchoukCompanionBlockBond, if_pos (show n < 2 * K by omega)]

end HTGeometry
