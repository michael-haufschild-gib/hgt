import GaloisForLFunctions.HTGeometry.QKrawtchoukCoefficientLimits

/-!
# Birth and death coordinates for the finite companion matrices

The off-diagonal products of the balanced companion Jacobi matrix factor
into concrete birth and death rates. In these coordinates, geometric
monomials form an invariant polynomial flag: the operator maps degree `j`
to degrees `j` and `j-1`. This is the algebraic input for identifying the
finite spectral branches in arXiv:2609.24149, Remark 8.5.
-/

noncomputable section

namespace HTGeometry

/-- Birth rate, vanishing at the last site of the finite companion block. -/
def qKrawtchoukCompanionBirth (t u : ℝ) (K n : ℕ) : ℝ :=
  Real.exp u * (qKrawtchoukEdgeBase t ^ n - qKrawtchoukEdgeBase t ^ (2 * K))

/-- Death rate, vanishing at the first site. -/
def qKrawtchoukCompanionDeath (t : ℝ) (n : ℕ) : ℝ :=
  1 - qKrawtchoukEdgeBase t ^ n

/-- Geometric monomial of real degree; natural degrees give the polynomial flag. -/
def qKrawtchoukCompanionMode (t j : ℝ) (n : ℕ) : ℝ :=
  Real.exp (Real.exp t * n * j)

/-- The finite tridiagonal expression in birth and death coordinates. -/
def qKrawtchoukCompanionBirthDeath (t u : ℝ) (K : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  qKrawtchoukCompanionBirth t u K n * f (n + 1) +
  qKrawtchoukCompanionDeath t n * f (n - 1) +
  qKrawtchoukCompanionFiniteDiagonal t u K n * f n

/-- Diagonal entry in the geometric monomial basis. -/
def qKrawtchoukCompanionModeLevel (t u : ℝ) (K : ℕ) (j : ℝ) : ℝ :=
  Real.exp (-Real.exp t * j) -
    Real.exp u * Real.exp (-Real.exp t * (2 * (K : ℝ) - j)) +
    (Real.exp u - 1) * qKrawtchoukEdgeBase t ^ K

private theorem base_pow (t : ℝ) (n : ℕ) :
    Real.exp (-Real.exp t * n) = qKrawtchoukEdgeBase t ^ n := by
  rw [qKrawtchoukEdgeBase, ← Real.exp_nat_mul]
  congr 1
  ring

/-- Both missing endpoint transitions vanish exactly. -/
theorem qKrawtchoukCompanionBirthDeath_endpoints (t u : ℝ) (K : ℕ) :
    qKrawtchoukCompanionBirth t u K (2 * K) = 0 ∧
      qKrawtchoukCompanionDeath t 0 = 0 := by
  simp [qKrawtchoukCompanionBirth, qKrawtchoukCompanionDeath]

/-- Every interior bond has strictly positive birth and death factors. -/
theorem qKrawtchoukCompanionBirthDeath_pos (t u : ℝ) (K : ℕ) (n : Fin (2 * K)) :
    0 < qKrawtchoukCompanionBirth t u K n ∧
      0 < qKrawtchoukCompanionDeath t (n + 1) := by
  have hn : (n : ℝ) < 2 * (K : ℝ) := by exact_mod_cast n.isLt
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have ht := Real.exp_pos t
  constructor
  · apply mul_pos (Real.exp_pos u)
    rw [sub_pos, ← base_pow, ← base_pow]
    apply Real.exp_lt_exp.mpr
    push_cast
    nlinarith
  · rw [qKrawtchoukCompanionDeath, sub_pos, ← base_pow]
    apply Real.exp_lt_one_iff.mpr
    push_cast
    nlinarith

/-- The concrete lower Jacobi coefficient is the product of adjacent rates. -/
theorem qKrawtchoukCompanionBirthDeath_bond (t u : ℝ) (K n : ℕ) :
    qKrawtchoukCompanionBirth t u K n * qKrawtchoukCompanionDeath t (n + 1) =
      qKrawtchoukCompanionFiniteLower t u K (n + 1) := by
  have hi : qKrawtchoukEdgeBase t ^ n * Real.exp (Real.exp t * n) = 1 := by
    rw [← base_pow, ← Real.exp_add]
    simp
  have hp : qKrawtchoukEdgeBase t ^ (2 * K) = (qKrawtchoukEdgeBase t ^ K) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  unfold qKrawtchoukCompanionBirth qKrawtchoukCompanionDeath
    qKrawtchoukCompanionFiniteLower alSalamCarlitzLower qKrawtchoukEdgeCutoff
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  rw [base_pow, show Real.exp (-Real.exp t * ((n : ℝ) + 1)) =
    qKrawtchoukEdgeBase t ^ (n + 1) by simpa using base_pow t (n + 1), hp]
  calc
    Real.exp u * (qKrawtchoukEdgeBase t ^ n - (qKrawtchoukEdgeBase t ^ K) ^ 2) *
        (1 - qKrawtchoukEdgeBase t ^ (n + 1)) =
      Real.exp u * (qKrawtchoukEdgeBase t ^ n -
        (qKrawtchoukEdgeBase t ^ K) ^ 2 *
          (qKrawtchoukEdgeBase t ^ n * Real.exp (Real.exp t * n))) *
        (1 - qKrawtchoukEdgeBase t ^ (n + 1)) := by rw [hi, mul_one]
    _ = _ := by ring

private theorem mode_forward (t j : ℝ) (n : ℕ) :
    qKrawtchoukCompanionMode t j (n + 1) =
      Real.exp (Real.exp t * j) * qKrawtchoukCompanionMode t j n := by
  unfold qKrawtchoukCompanionMode
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

private theorem death_mode_backward (t j : ℝ) (n : ℕ) :
    qKrawtchoukCompanionDeath t n * qKrawtchoukCompanionMode t j (n - 1) =
      qKrawtchoukCompanionDeath t n *
        (Real.exp (-Real.exp t * j) * qKrawtchoukCompanionMode t j n) := by
  cases n with
  | zero => simp [qKrawtchoukCompanionDeath]
  | succ n =>
      congr 1
      unfold qKrawtchoukCompanionMode
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring

private theorem mode_lower (t j : ℝ) (n : ℕ) :
    qKrawtchoukCompanionMode t (j - 1) n =
      qKrawtchoukEdgeBase t ^ n * qKrawtchoukCompanionMode t j n := by
  rw [← base_pow]
  unfold qKrawtchoukCompanionMode
  rw [← Real.exp_add]
  congr 1
  ring

/-- Exact triangular action on the geometric monomials, including both endpoints. -/
theorem qKrawtchoukCompanionBirthDeath_mode (t u j : ℝ) (K n : ℕ) :
    qKrawtchoukCompanionBirthDeath t u K (qKrawtchoukCompanionMode t j) n =
      qKrawtchoukCompanionModeLevel t u K j * qKrawtchoukCompanionMode t j n +
      (Real.exp u * Real.exp (Real.exp t * j) - Real.exp (-Real.exp t * j) +
        1 - Real.exp u) * qKrawtchoukCompanionMode t (j - 1) n := by
  have he : Real.exp (-Real.exp t * (2 * (K : ℝ) - j)) =
      qKrawtchoukEdgeBase t ^ (2 * K) * Real.exp (Real.exp t * j) := by
    rw [← base_pow, ← Real.exp_add]
    congr 1
    push_cast
    ring
  unfold qKrawtchoukCompanionBirthDeath
  rw [mode_forward, death_mode_backward, mode_lower]
  unfold qKrawtchoukCompanionBirth qKrawtchoukCompanionDeath
    qKrawtchoukCompanionFiniteDiagonal alSalamCarlitzDiagonal
    qKrawtchoukCompanionModeLevel
  rw [base_pow, he]
  ring

end HTGeometry
