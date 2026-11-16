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

private theorem quantumSerre_of_weyl (q : ℂˣ) (X Y : Matrix ι ι ℂ)
    (h : X * Y = (q : ℂ) • (Y * X)) : quantumSerre q X Y = 0 := by
  have hp (k : ℕ) : X ^ k * Y = (q : ℂ) ^ k • (Y * X ^ k) := by
    induction k with
    | zero => simp only [pow_zero, one_mul, mul_one, one_smul]
    | succ k hk =>
      rw [pow_succ, mul_assoc, h, Matrix.mul_smul, ← mul_assoc, hk,
        Matrix.smul_mul, smul_smul, mul_assoc, ← pow_succ,
        mul_comm (q : ℂ), ← pow_succ]
  have h₂ : X ^ 2 * Y * X = (q : ℂ) ^ 2 • (Y * X ^ 3) := by
    rw [hp, Matrix.smul_mul, mul_assoc, ← pow_succ]
  have h₁ : X * Y * X ^ 2 = (q : ℂ) • (Y * X ^ 3) := by
    rw [h, Matrix.smul_mul, mul_assoc,
      show X * X ^ 2 = X ^ 3 by noncomm_ring]
  have hc : (q : ℂ) ^ 3 - ((q : ℂ) + 1 + (q : ℂ)⁻¹) * (q : ℂ) ^ 2 +
      ((q : ℂ) + 1 + (q : ℂ)⁻¹) * (q : ℂ) - 1 = 0 := by
    have hq : (q : ℂ) ≠ 0 := Units.ne_zero q
    field_simp
    ring
  unfold quantumSerre
  rw [hp, h₂, h₁, smul_smul, smul_smul]
  calc
    _ = ((q : ℂ) ^ 3 - ((q : ℂ) + 1 + (q : ℂ)⁻¹) * (q : ℂ) ^ 2 +
        ((q : ℂ) + 1 + (q : ℂ)⁻¹) * (q : ℂ) - 1) • (Y * X ^ 3) := by module
    _ = 0 := by rw [hc, zero_smul]

/-- The nilpotent jet shift and its clock satisfy both affine Serre relations. -/
theorem quantumSerre_oneSidedJet_both (n : ℕ) (q : ℂˣ) :
    quantumSerre q (truncatedJetClock n q) (boundaryCompletedJetShift n 0) = 0 ∧
      quantumSerre q (boundaryCompletedJetShift n 0) (truncatedJetClock n q) = 0 := by
  refine ⟨quantumSerre_oneSidedJet n q, ?_⟩
  have h := truncatedJetClock_oneSidedShift_weyl n (q : ℂ)
  have hi : boundaryCompletedJetShift n 0 * truncatedJetClock n q =
      ((q⁻¹ : ℂˣ) : ℂ) •
        (truncatedJetClock n q * boundaryCompletedJetShift n 0) := by
    rw [h, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero q), one_smul]
  have hs := quantumSerre_of_weyl q⁻¹ _ _ hi
  have hc : ((q⁻¹ : ℂˣ) : ℂ) + 1 + (((q⁻¹ : ℂˣ) : ℂ))⁻¹ =
      (q : ℂ) + 1 + (q : ℂ)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, inv_inv]
    ring
  simpa only [quantumSerre, hc] using hs

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

#print axioms GaloisForLFunctions.BiarithmeticGeometry.quantumSerre_diagonal_eq_zero_iff
#print axioms GaloisForLFunctions.BiarithmeticGeometry.quantumSerre_oneSidedJet_both
#print axioms GaloisForLFunctions.BiarithmeticGeometry.quantumSerre_jet_eq_zero_iff
