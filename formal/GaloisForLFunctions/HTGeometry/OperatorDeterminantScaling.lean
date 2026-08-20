/-
# Rescaling an operator rescales the spectral variable of its regularized determinant

The order-`p` regularized exponent is a power series in `z` whose `m`-th coefficient carries
`tr(Tᵐ)`, so replacing `T` by `cT` multiplies that coefficient by `cᵐ`: the exponent depends on
`cz` alone.  For a linear operator pencil this turns the restriction to a line through the origin
into the one-variable determinant with the line parameter as spectral variable, which is what
reduces the multivariable completion law to the one-variable one at every order.

Main results:
* `opTrace_pow_smul` — the power traces of a rescaled operator.
* `opSchattenDetExp_smul`, `opSchattenDet_smul` — **`det_p(1 − z·cT) = det_p(1 − (cz)T)`**.
* `pencilOperator`, `pencilOperator_smul` — a linear operator pencil and its homogeneity.
* `opSchattenDet_pencil_line` — **the line restriction of a pencil determinant is the one-variable
  determinant**.
-/
import GaloisForLFunctions.HTGeometry.SchattenOperatorDeterminant
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem opTrace_pow_smul (c : ℂ) (T : H →L[ℂ] H) (m : ℕ) :
    opTrace ((c • T) ^ m) = c ^ m * opTrace (T ^ m) := by
  rw [smul_pow, opTrace_smul]

/-- **Rescaling the operator rescales the spectral variable.** -/
theorem opSchattenDetExp_smul (p : ℕ) (c : ℂ) (T : H →L[ℂ] H) (z : ℂ) :
    opSchattenDetExp p (c • T) z = opSchattenDetExp p T (c * z) := by
  show tracePowerDetExp p (fun m => opTrace ((c • T) ^ m)) z
      = tracePowerDetExp p (fun m => opTrace (T ^ m)) (c * z)
  rw [tracePowerDetExp, tracePowerDetExp]
  refine tsum_congr fun k => ?_
  rw [opTrace_pow_smul, mul_pow]
  ring

/-- **The order-`p` determinant of a rescaled operator.** -/
theorem opSchattenDet_smul (p : ℕ) (c : ℂ) (T : H →L[ℂ] H) (z : ℂ) :
    opSchattenDet p (c • T) z = opSchattenDet p T (c * z) := by
  show Complex.exp (- opSchattenDetExp p (c • T) z)
      = Complex.exp (- opSchattenDetExp p T (c * z))
  rw [opSchattenDetExp_smul]

/-! ## Linear operator pencils -/

/-- A linear operator pencil `A(v) = ∑ᵢ vᵢ Aᵢ`. -/
def pencilOperator {m : ℕ} (A : Fin m → (H →L[ℂ] H)) (v : Fin m → ℂ) : H →L[ℂ] H :=
  ∑ i, v i • A i

omit [CompleteSpace H] in
theorem pencilOperator_smul {m : ℕ} (A : Fin m → (H →L[ℂ] H)) (c : ℂ) (v : Fin m → ℂ) :
    pencilOperator A (fun i => c * v i) = c • pencilOperator A v := by
  rw [pencilOperator, pencilOperator, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]

/-- **The line restriction of a pencil determinant is the one-variable determinant.** -/
theorem opSchattenDet_pencil_line {m : ℕ} (p : ℕ) (A : Fin m → (H →L[ℂ] H))
    (v : Fin m → ℂ) (t : ℂ) :
    opSchattenDet p (pencilOperator A (fun i => t * v i)) 1
      = opSchattenDet p (pencilOperator A v) t := by
  rw [pencilOperator_smul, opSchattenDet_smul, mul_one]

end

end GaloisForLFunctions.HTGeometry
