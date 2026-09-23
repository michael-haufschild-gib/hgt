/-
# Coordinate-free Fredholm determinant germs

For a Hilbert--Schmidt operator `T`, every power `T^(n+2)` is trace class.  The local
Hilbert--Carleman exponent is therefore determined without choosing a matrix representation:

`sum_(n>=0) z^(n+2)/(n+2) Tr(T^(n+2))`.

This module packages that trace-coordinate germ and its degree-one correction.  It deliberately
does not call the corrected object an entire Fredholm determinant: the logarithmic power series is
only the germ at zero.  Entire determinant theory requires an independent product construction.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

noncomputable section

namespace HTGeometry

open ContinuousLinearMap
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The coordinate-free Hilbert--Carleman exponent germ of a bounded operator.  It is meaningful
for Hilbert--Schmidt operators because every displayed power is a product of two
Hilbert--Schmidt operators. -/
def operatorFredholmExpGerm (T : H →L[ℂ] H) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * opTrace (T ^ (n + 2))

/-- The coordinate-free regularized determinant germ `det_2(1-zT)`. -/
def operatorFredholmDet2Germ (T : H →L[ℂ] H) (z : ℂ) : ℂ :=
  Complex.exp (-operatorFredholmExpGerm T z)

/-- The degree-one-corrected determinant germ.  For a trace-class operator this is the germ at
zero of the ordinary Fredholm determinant `det(1-zT)`. -/
def operatorFredholmDet1Germ (T : H →L[ℂ] H) (z : ℂ) : ℂ :=
  operatorFredholmDet2Germ T z * Complex.exp (-(z * opTrace T))

/-- Exact diagonal Hilbert--Schmidt pairing, including the vanishing imaginary part. -/
theorem hsInner_self_eq_ofReal_hsNormSq
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    hsInner T T = (hsNormSq T : ℂ) := by
  apply Complex.ext
  · exact hsInner_self_re hT
  · rw [Complex.ofReal_im]
    change (∑' i, inner ℂ (T (hsBasis ℂ H i)) (T (hsBasis ℂ H i))).im = 0
    rw [Complex.im_tsum (hT.summable_inner hT (hsBasis ℂ H))]
    have hzero :
        (fun i => (inner ℂ (T (hsBasis ℂ H i)) (T (hsBasis ℂ H i))).im) =
          fun _ => 0 := by
      funext i
      simpa using inner_self_im (𝕜 := ℂ) (T (hsBasis ℂ H i))
    rw [hzero, tsum_zero]

/-- A self-adjoint Hilbert--Schmidt square has trace equal to its squared
Hilbert--Schmidt norm, as an exact complex equality. -/
theorem opTrace_sq_eq_ofReal_hsNormSq
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    (hTadj : ContinuousLinearMap.adjoint T = T) :
    opTrace (T ^ (2 : ℕ)) = (hsNormSq T : ℂ) := by
  have hsq : T ^ (2 : ℕ) = ContinuousLinearMap.adjoint T ∘L T := by
    rw [pow_two, ContinuousLinearMap.mul_def, hTadj]
  rw [hsq, opTrace_adjoint_comp_self, hsInner_self_eq_ofReal_hsNormSq hT]

/-- Equality of every trace coordinate from degree two identifies the two
Hilbert--Carleman exponent germs. -/
theorem operatorFredholmExpGerm_eq_of_powerTrace_eq
    {S T : H →L[ℂ] H}
    (htrace : ∀ n : ℕ, opTrace (S ^ (n + 2)) = opTrace (T ^ (n + 2)))
    (z : ℂ) :
    operatorFredholmExpGerm S z = operatorFredholmExpGerm T z := by
  unfold operatorFredholmExpGerm
  apply tsum_congr
  intro n
  rw [htrace n]

/-- Equality of all trace coordinates from degree two identifies the regularized determinant
germs. -/
theorem operatorFredholmDet2Germ_eq_of_powerTrace_eq
    {S T : H →L[ℂ] H}
    (htrace : ∀ n : ℕ, opTrace (S ^ (n + 2)) = opTrace (T ^ (n + 2)))
    (z : ℂ) :
    operatorFredholmDet2Germ S z = operatorFredholmDet2Germ T z := by
  rw [operatorFredholmDet2Germ, operatorFredholmDet2Germ,
    operatorFredholmExpGerm_eq_of_powerTrace_eq htrace z]

/-- Equality of the degree-one trace together with all higher trace coordinates identifies the
ordinary determinant germs. -/
theorem operatorFredholmDet1Germ_eq_of_trace_eq
    {S T : H →L[ℂ] H}
    (hzero : opTrace S = opTrace T)
    (htrace : ∀ n : ℕ, opTrace (S ^ (n + 2)) = opTrace (T ^ (n + 2)))
    (z : ℂ) :
    operatorFredholmDet1Germ S z = operatorFredholmDet1Germ T z := by
  rw [operatorFredholmDet1Germ, operatorFredholmDet1Germ,
    operatorFredholmDet2Germ_eq_of_powerTrace_eq htrace z, hzero]

end HTGeometry
