import GaloisForLFunctions.RHTower.TruncatedJetWeylBoundary

/-!
# Cubic quantum Serre relations for truncated jets

The affine `sl₂` Serre polynomial has coefficient `q + 1 + q⁻¹`, with
`q` the square of the quantum parameter. In a diagonal basis it factors into
three eigenvalue differences. Applied to the geometric jet clock, this gives
an exact boundary obstruction and explains why Serre closure is weaker than
Weyl closure. The relation is the one used in Huang–Chen–Ding–Xu,
arXiv:2611.06256.
-/

noncomputable section

open Matrix RHTower

namespace GaloisForLFunctions.BiarithmeticGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cubic affine quantum Serre polynomial. -/
def quantumSerre (q : ℂˣ) (X Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  X ^ 3 * Y - ((q : ℂ) + 1 + (q : ℂ)⁻¹) • (X ^ 2 * Y * X) +
    ((q : ℂ) + 1 + (q : ℂ)⁻¹) • (X * Y * X ^ 2) - Y * X ^ 3

/-- In a diagonal basis, only eigenvalue ratios `1`, `q`, and `q⁻¹` survive. -/
theorem quantumSerre_diagonal_apply (q : ℂˣ) (a : ι → ℂ)
    (B : Matrix ι ι ℂ) (i j : ι) :
    quantumSerre q (diagonal a) B i j =
      (a i - a j) * (a i - (q : ℂ) * a j) *
        (a i - (q : ℂ)⁻¹ * a j) * B i j := by
  simp only [quantumSerre, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.diagonal_pow, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Pi.pow_apply, smul_eq_mul]
  have hq : (q : ℂ) ≠ 0 := Units.ne_zero q
  field_simp
  ring

/-- An exact entrywise classification of matrices satisfying the diagonal Serre relation. -/
theorem quantumSerre_diagonal_eq_zero_iff (q : ℂˣ) (a : ι → ℂ)
    (B : Matrix ι ι ℂ) :
    quantumSerre q (diagonal a) B = 0 ↔
      ∀ i j, a i = a j ∨ a i = (q : ℂ) * a j ∨
        a i = (q : ℂ)⁻¹ * a j ∨ B i j = 0 := by
  constructor
  · intro h i j
    have he := congrFun (congrFun h i) j
    simpa only [quantumSerre_diagonal_apply, Matrix.zero_apply,
      mul_eq_zero, sub_eq_zero, or_assoc] using he
  · intro h
    ext i j
    simpa only [quantumSerre_diagonal_apply, Matrix.zero_apply,
      mul_eq_zero, sub_eq_zero, or_assoc] using h i j

/-- The whole Serre defect of a completed jet is concentrated at the wrap entry. -/
theorem quantumSerre_jet_apply (n : ℕ) (q : ℂˣ) (h : ℂ)
    (i j : Fin (n + 1)) :
    quantumSerre q (truncatedJetClock n q) (boundaryCompletedJetShift n h) i j =
      if (i : ℕ) = 0 ∧ (j : ℕ) = n then
        (1 - (q : ℂ) ^ n) * (1 - (q : ℂ) ^ (n + 1)) *
          (1 - (q : ℂ)⁻¹ * (q : ℂ) ^ n) * h else 0 := by
  rw [truncatedJetClock, quantumSerre_diagonal_apply]
  by_cases hs : (j : ℕ) + 1 = (i : ℕ)
  · have hw : ¬ ((i : ℕ) = 0 ∧ (j : ℕ) = n) := by omega
    rw [if_neg hw, ← hs, pow_succ]
    simp only [mul_comm ((q : ℂ) ^ (j : ℕ)) (q : ℂ), sub_self, mul_zero, zero_mul]
  · by_cases hw : (i : ℕ) = 0 ∧ (j : ℕ) = n
    · rw [boundaryCompletedJetShift, if_neg hs, if_pos hw, if_pos hw,
        hw.1, hw.2, pow_zero, pow_succ]
      ring
    · simp only [boundaryCompletedJetShift, hs, if_false, hw, mul_zero]

/-- Every one-sided truncated jet satisfies the cubic Serre relation. -/
theorem quantumSerre_oneSidedJet (n : ℕ) (q : ℂˣ) :
    quantumSerre q (truncatedJetClock n q) (boundaryCompletedJetShift n 0) = 0 := by
  ext i j
  simp only [quantumSerre_jet_apply, mul_zero, ite_self, Matrix.zero_apply]

/-- Serre closure has three scalar resonance alternatives, while Weyl closure
has only the middle one. The statement also includes a vanishing wrap. -/
theorem quantumSerre_jet_eq_zero_iff (n : ℕ) (q : ℂˣ) (h : ℂ) :
    quantumSerre q (truncatedJetClock n q) (boundaryCompletedJetShift n h) = 0 ↔
      (q : ℂ) ^ n = 1 ∨ (q : ℂ) ^ (n + 1) = 1 ∨
        (q : ℂ)⁻¹ * (q : ℂ) ^ n = 1 ∨ h = 0 := by
  have hc :
      (1 - (q : ℂ) ^ n) * (1 - (q : ℂ) ^ (n + 1)) *
        (1 - (q : ℂ)⁻¹ * (q : ℂ) ^ n) * h = 0 ↔
      (q : ℂ) ^ n = 1 ∨ (q : ℂ) ^ (n + 1) = 1 ∨
        (q : ℂ)⁻¹ * (q : ℂ) ^ n = 1 ∨ h = 0 := by
    simp only [mul_eq_zero, sub_eq_zero, eq_comm (a := (1 : ℂ)), or_assoc]
  constructor
  · intro he
    apply hc.mp
    have he' := congrFun (congrFun he (0 : Fin (n + 1))) (Fin.last n)
    simpa only [quantumSerre_jet_apply, Fin.val_zero, Fin.val_last, and_self,
      if_true, Matrix.zero_apply] using he'
  · intro he
    ext i j
    simp only [quantumSerre_jet_apply, hc.mpr he, ite_self, Matrix.zero_apply]

end GaloisForLFunctions.BiarithmeticGeometry
