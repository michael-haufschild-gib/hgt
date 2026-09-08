import GaloisForLFunctions.HTGeometry.CPVTwoModeFock
import Mathlib

/-!
# The paper's exact normalized pseudo-spin commutators

The number-difference sector `d` has Bargmann index `(d+1)/2`.
Rescaling the actual Fock operators gives precisely equation (4) of
arXiv:2601.07437, and their normalized spectrum is `1 + n/K`.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

/-- Bargmann index of the charge-`d` sector. -/
def bargmannIndex (d : ℕ) : ℝ := ((d : ℝ) + 1) / 2

/-- Quantumness parameter of the sector. -/
def quantumScale (d : ℕ) : ℝ := 2 / ((d : ℝ) + 1)

/-- Normalized raising generator. -/
def normalizedCreate (d : ℕ) : FockEnd := (2 / ((d : ℂ) + 1)) • pairCreate
/-- Normalized lowering generator. -/
def normalizedAnn (d : ℕ) : FockEnd := (2 / ((d : ℂ) + 1)) • pairAnn
/-- Normalized energy generator. -/
def normalizedCartan (d : ℕ) : FockEnd := (1 / ((d : ℂ) + 1)) • pairCartan

/-- The Bargmann range required by the positive discrete series. -/
theorem bargmannIndex_lower_bound (d : ℕ) : (1 / 2 : ℝ) ≤ bargmannIndex d := by
  unfold bargmannIndex
  have h : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  linarith

/-- Quantumness is exactly inverse Bargmann index. -/
theorem quantumScale_eq_inv (d : ℕ) : quantumScale d = (bargmannIndex d)⁻¹ := by
  unfold quantumScale bargmannIndex
  field_simp

/-- Quantumness is positive at every finite sector index. -/
theorem quantumScale_pos (d : ℕ) : 0 < quantumScale d := by unfold quantumScale; positivity

/-- The controlled classical scaling has quantumness tending to zero. -/
theorem quantumScale_tendsto_zero :
    Filter.Tendsto quantumScale Filter.atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  convert! h using 1 <;> simp only [mul_one_div, mul_zero]
  rfl

/-- Equation (4): the Cartan/raising commutator has coefficient `1/K`. -/
theorem normalizedCartan_create (d : ℕ) :
    normalizedCartan d * normalizedCreate d - normalizedCreate d * normalizedCartan d =
      (quantumScale d : ℂ) • normalizedCreate d := by
  simp only [normalizedCartan, normalizedCreate, smul_mul_assoc, Algebra.mul_smul_comm,
    smul_smul]
  rw [mul_comm (2 / ((d : ℂ) + 1)) (1 / ((d : ℂ) + 1))]
  erw [← smul_sub, pairCartan_create, smul_smul]
  simp only [quantumScale, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  congr 1
  ring

/-- Equation (4): the Cartan/lowering commutator has coefficient `-1/K`. -/
theorem normalizedCartan_ann (d : ℕ) :
    normalizedCartan d * normalizedAnn d - normalizedAnn d * normalizedCartan d =
      (-(quantumScale d : ℂ)) • normalizedAnn d := by
  simp only [normalizedCartan, normalizedAnn, smul_mul_assoc, Algebra.mul_smul_comm,
    smul_smul]
  rw [mul_comm (2 / ((d : ℂ) + 1)) (1 / ((d : ℂ) + 1))]
  erw [← smul_sub, pairCartan_ann, smul_smul]
  simp only [quantumScale, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  congr 1
  ring

/-- Equation (4): the raising/lowering commutator has coefficient `-2/K`. -/
theorem normalizedCreate_ann (d : ℕ) :
    normalizedCreate d * normalizedAnn d - normalizedAnn d * normalizedCreate d =
      (-2 * (quantumScale d : ℂ)) • normalizedCartan d := by
  simp only [normalizedCreate, normalizedAnn, smul_mul_assoc, Algebra.mul_smul_comm,
    smul_smul]
  erw [← smul_sub, pairCreate_ann]
  simp only [normalizedCartan, smul_smul, smul_neg, quantumScale, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  rw [← neg_smul]
  congr 1
  ring

/-- Exact normalized pseudo-spin spectrum on every actual charge-sector state. -/
theorem normalizedCartan_spectrum (d n : ℕ) :
    normalizedCartan d (pairState d n) =
      (1 + (n : ℂ) / (bargmannIndex d : ℂ)) • pairState d n := by
  rw [normalizedCartan, LinearMap.smul_apply, pairCartan_state, smul_smul]
  congr 1
  unfold bargmannIndex
  push_cast
  have hd : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast (by positivity : (d : ℝ) + 1 ≠ 0)
  field_simp
  ring

/-- Unscaled Casimir has the paper's value `K(K-1)` on the entire charge sector. -/
theorem bargmannCasimir_spectrum (d n : ℕ) :
    ((1 / 4 : ℂ) • (pairCartan * pairCartan - (2 : ℂ) • pairCartan -
      (4 : ℂ) • (pairCreate * pairAnn))) (pairState d n) =
      ((bargmannIndex d * (bargmannIndex d - 1) : ℝ) : ℂ) • pairState d n := by
  rw [LinearMap.smul_apply, pairCasimir_state, smul_smul]
  congr 1
  unfold bargmannIndex
  push_cast
  ring

/-- Every charge-sector ladder vector is nonzero in the actual Fock domain. -/
theorem pairState_ne_zero (d n : ℕ) : pairState d n ≠ 0 := by
  unfold pairState
  exact mul_ne_zero (pow_ne_zero _ (MvPolynomial.X_ne_zero false))
    (pow_ne_zero _ (MvPolynomial.X_ne_zero true))

end GaloisForLFunctions.HTGeometry.CPV
