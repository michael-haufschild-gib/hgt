import GaloisForLFunctions.HTGeometry.CoefficientwisePowerSeriesDerivation
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Scalar-linear coefficient clocks on formal flows

The existing native coefficientwise derivative already pays the convolution
Leibniz rule. Giving it a derivation parameter retains the chosen scalar
field and permits different coefficient clocks on the same formal series.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The native coefficientwise operator, bundled over the original scalar ring. -/
def paperFormalCoefficientDerivation (D : Derivation k A A) :
    Derivation k (PowerSeries A) (PowerSeries A) := by
  letI : Differential A := ⟨D.restrictScalars ℤ⟩
  exact
    { toFun := PowerSeriesDeriv.coeffwiseAdd
      map_add' := map_add _
      map_smul' := fun c f => by
        ext n
        rw [PowerSeriesDeriv.coeff_coeffwiseAdd, PowerSeries.coeff_smul,
          PowerSeries.coeff_smul, PowerSeriesDeriv.coeff_coeffwiseAdd]
        exact D.map_smul c _
      map_one_eq_zero' := PowerSeriesDeriv.coeffwiseAdd_one
      leibniz' := PowerSeriesDeriv.coeffwiseAdd_mul }

/-- The parameterized clock acts literally on every arithmetic coefficient. -/
@[simp] theorem paperFormalCoefficientDerivation_coeff (D : Derivation k A A)
    (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (paperFormalCoefficientDerivation D f) =
      D (PowerSeries.coeff n f) :=
  PowerSeries.coeff_mk (R := A) n (fun m => D (PowerSeries.coeff m f))

/-- Constants in formal time retain their original coefficient derivative. -/
@[simp] theorem paperFormalCoefficientDerivation_C (D : Derivation k A A) (a : A) :
    paperFormalCoefficientDerivation D (PowerSeries.C a) = PowerSeries.C (D a) := by
  ext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

/-- The formal time coordinate itself is fixed by every coefficient clock. -/
@[simp] theorem paperFormalCoefficientDerivation_X (D : Derivation k A A) :
    paperFormalCoefficientDerivation D PowerSeries.X = 0 := by
  letI : Differential A := ⟨D.restrictScalars ℤ⟩
  exact PowerSeriesDeriv.coeffwiseAdd_X (K := A)

/-- Coefficient clocks commute with differentiation in the independent formal time. -/
theorem paperFormalCoefficientDerivation_time_commute (D : Derivation k A A)
    (f : PowerSeries A) :
    paperFormalCoefficientDerivation D (PowerSeries.derivative A f) =
      PowerSeries.derivative A (paperFormalCoefficientDerivation D f) := by
  ext n
  simp [PowerSeries.coeff_derivative, Derivation.leibniz, smul_eq_mul, mul_comm]

/-- The formal-time Euler operator counts exact coefficient order over any coefficient ring. -/
theorem paperFormalTimeEuler_coeff (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative A f) =
      n • PowerSeries.coeff n f := by
  cases n with
  | zero => simp
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      simp [nsmul_eq_mul, mul_comm]

end

end GaloisForLFunctions.HTGeometry
