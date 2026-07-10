import GaloisForLFunctions.RHTower.ShearedSeamGaugeTrivialization

/-!
# FE-semilinear exhaustion of upper torsion shears

The constant sheared presentation fails the full functional-equation audit.  This module classifies
the entire upper-unit-shear family

`A_f=[[X^m,f(X)],[0,1]]`.

With target coefficient parity `diag(-1,1)`, the forced order-`m` source parity, and local-coordinate
reflection `X |-> -X`, the presentation is FE-semilinearly equivariant exactly when `f` is odd:

`f(-X)=-f(X)`.

But the elementary row gauge `U_f=[[1,f],[0,1]]` splits `A_f`, and it preserves the target FE action
under exactly the same oddness condition.  Therefore every FE-compatible upper-unit shear is
FE-semilinearly row-equivalent to the split torsion presentation.  Replacing the constant shear by
an odd polynomial cannot produce the missing completed extension class.
-/

noncomputable section
namespace RHTower

open Matrix Polynomial

/-- The full upper-unit-shear family over the local divisor polynomial ring. -/
def upperShearPresentation (m : ℕ) (f : Polynomial ℚ) :
    Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  !![X ^ m, f; 0, 1]

/-- Elementary row gauge splitting the upper shear. -/
def upperShearRowGauge (f : Polynomial ℚ) :
    Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  !![1, f; 0, 1]

def upperShearRowGaugeInv (f : Polynomial ℚ) :
    Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  !![1, -f; 0, 1]

theorem upperShearRowGauge_mul_inv (f : Polynomial ℚ) :
    upperShearRowGauge f * upperShearRowGaugeInv f = 1 := by
  rw [upperShearRowGauge, upperShearRowGaugeInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem upperShearRowGauge_inv_mul (f : Polynomial ℚ) :
    upperShearRowGaugeInv f * upperShearRowGauge f = 1 := by
  rw [upperShearRowGauge, upperShearRowGaugeInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Every upper-unit shear is absolutely row-equivalent to the split presentation. -/
theorem upperShearPresentation_eq_gauge_mul_split (m : ℕ) (f : Polynomial ℚ) :
    upperShearPresentation m f =
      upperShearRowGauge f * splitTorsionPresentation (R := ℚ) m := by
  rw [upperShearPresentation, upperShearRowGauge, splitTorsionPresentation,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The splitting row gauge is FE-semilinear exactly when its shear polynomial is odd. -/
theorem upperShearRowGauge_feSemilinear_iff (f : Polynomial ℚ) :
    FESemilinearIntertwines feCoefficientParity feCoefficientParity
      (upperShearRowGauge f) ↔ f.comp (-X) = -f := by
  constructor
  · intro h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) => M 0 1) h
    simp [reflectPolynomialMatrix, feCoefficientParity,
      upperShearRowGauge, Matrix.mul_apply, Fin.sum_univ_two] at h01
    exact neg_eq_iff_eq_neg.mp h01
  · intro hf
    rw [FESemilinearIntertwines]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectPolynomialMatrix, feCoefficientParity, upperShearRowGauge,
        Matrix.mul_apply, Fin.sum_univ_two, hf]

/-- **FE equation for an upper shear.**  The presentation intertwines the fixed target and forced
source actions exactly when the off-diagonal polynomial is odd under `X |-> -X`. -/
theorem upperShearPresentation_feSemilinear_iff (m : ℕ) (f : Polynomial ℚ) :
    FESemilinearIntertwines feCoefficientParity (splitSourceFEParity m)
      (upperShearPresentation m f) ↔ f.comp (-X) = -f := by
  constructor
  · intro h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) => M 0 1) h
    simp [reflectPolynomialMatrix, feCoefficientParity,
      splitSourceFEParity, upperShearPresentation, Matrix.mul_apply,
      Fin.sum_univ_two] at h01
    exact neg_eq_iff_eq_neg.mp h01
  · intro hf
    rw [FESemilinearIntertwines]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectPolynomialMatrix, feCoefficientParity, splitSourceFEParity,
        upperShearPresentation, Matrix.mul_apply, Fin.sum_univ_two, hf]
    rw [show (-X : Polynomial ℚ) = (-1) * X by ring_nf, mul_pow]
    ring_nf

/-- FE-semilinear row equivalence through an invertible target gauge. -/
def FESemilinearRowEquivalent
    (targetParity A B : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) : Prop :=
  ∃ U V,
    FESemilinearIntertwines targetParity targetParity U ∧
      U * V = 1 ∧ V * U = 1 ∧ A = U * B

/-- **Upper-shear exhaustion.**  Every FE-semilinear upper-unit shear is FE-semilinearly row
equivalent to the split torsion presentation. -/
theorem upperShearPresentation_feSemilinearly_split {m : ℕ} {f : Polynomial ℚ}
    (hA : FESemilinearIntertwines feCoefficientParity (splitSourceFEParity m)
      (upperShearPresentation m f)) :
    FESemilinearRowEquivalent feCoefficientParity (upperShearPresentation m f)
      (splitTorsionPresentation (R := ℚ) m) := by
  have hf := (upperShearPresentation_feSemilinear_iff m f).mp hA
  exact ⟨upperShearRowGauge f, upperShearRowGaugeInv f,
    (upperShearRowGauge_feSemilinear_iff f).mpr hf,
    upperShearRowGauge_mul_inv f, upperShearRowGauge_inv_mul f,
    upperShearPresentation_eq_gauge_mul_split m f⟩

end RHTower
