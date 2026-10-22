import GaloisForLFunctions.HTGeometry.ComplexInverseFamilyDerivative
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeParametricDerivatives

/-!
# Holomorphic finite-prime theta resolvent

The literal finite Euler product is invertible on the open right half-plane.  Banach-algebra
inversion therefore turns its established product derivative into the exact derivative of the
physical resolvent.  The resulting anti-logarithmic derivative is exactly the factor's left
logarithmic derivative, closing the inverse-family part of the theta-cusp carrier law.
-/

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Total ring-inverse realization of the complex finite-prime resolvent family. -/
def finitePrimeEvenResolventFamilyAtC (s : ℂ) (N : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  Ring.inverse (finitePrimeEvenLocalFactorAtC s N)

/-- The total ring inverse agrees with the proof-relevant physical resolvent on `Re s > 0`. -/
theorem finitePrimeEvenResolventFamilyAtC_eq
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    finitePrimeEvenResolventFamilyAtC s N =
      finitePrimeEvenResolventAtC s hs N := by
  let u := (finitePrimeEvenLocalFactorAtC_isUnit hs N).unit
  change Ring.inverse (u : evenSubspace →L[ℂ] evenSubspace) =
    (↑(u⁻¹) : evenSubspace →L[ℂ] evenSubspace)
  exact Ring.inverse_unit u

/-- Derivative of the total complex finite-prime resolvent family. -/
def finitePrimeEvenResolventFamilyAtCDeriv (s : ℂ) (N : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  complexInvFamilyDeriv
    (fun z ↦ finitePrimeEvenLocalFactorAtC z N)
    (fun z ↦ finitePrimeEvenLocalFactorAtCDeriv z N) s

/-- Exact derivative of the total finite-prime resolvent family on the open right half-plane. -/
theorem hasDerivAt_finitePrimeEvenResolventFamilyAtC
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    HasDerivAt (fun z ↦ finitePrimeEvenResolventFamilyAtC z N)
      (finitePrimeEvenResolventFamilyAtCDeriv s N) s := by
  exact hasDerivAt_complexInvFamily
    (C := fun z ↦ finitePrimeEvenLocalFactorAtC z N)
    (C₁ := fun z ↦ finitePrimeEvenLocalFactorAtCDeriv z N)
    (hasDerivAt_finitePrimeEvenLocalFactorAtC s N)
    (finitePrimeEvenLocalFactorAtC_isUnit hs N)

/-- Closed resolvent derivative formula on `Re s > 0`. -/
theorem finitePrimeEvenResolventFamilyAtCDeriv_eq
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    finitePrimeEvenResolventFamilyAtCDeriv s N =
      -(finitePrimeEvenResolventAtC s hs N *
          finitePrimeEvenLocalFactorAtCDeriv s N *
          finitePrimeEvenResolventAtC s hs N) := by
  rw [finitePrimeEvenResolventFamilyAtCDeriv, complexInvFamilyDeriv]
  change -(finitePrimeEvenResolventFamilyAtC s N *
      finitePrimeEvenLocalFactorAtCDeriv s N *
      finitePrimeEvenResolventFamilyAtC s N) = _
  rw [finitePrimeEvenResolventFamilyAtC_eq hs N]

/-- The anti-logarithmic derivative of the resolvent is exactly the left logarithmic derivative
of the finite Euler factor. -/
theorem neg_resolventDeriv_mul_localFactor_eq_logDeriv
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    -(finitePrimeEvenResolventFamilyAtCDeriv s N) *
        finitePrimeEvenLocalFactorAtC s N =
      finitePrimeEvenLocalFactorAtCLogDeriv s hs N := by
  rw [finitePrimeEvenResolventFamilyAtCDeriv_eq hs N, neg_neg,
    finitePrimeEvenLocalFactorAtCLogDeriv]
  calc
    (finitePrimeEvenResolventAtC s hs N *
          finitePrimeEvenLocalFactorAtCDeriv s N *
          finitePrimeEvenResolventAtC s hs N) *
        finitePrimeEvenLocalFactorAtC s N =
      finitePrimeEvenResolventAtC s hs N *
        finitePrimeEvenLocalFactorAtCDeriv s N *
          (finitePrimeEvenResolventAtC s hs N *
            finitePrimeEvenLocalFactorAtC s N) := by
        simp only [mul_assoc]
    _ = finitePrimeEvenResolventAtC s hs N *
        finitePrimeEvenLocalFactorAtCDeriv s N := by
      rw [finitePrimeEvenResolventAtC_mul_localFactor, mul_one]

end RHTower
