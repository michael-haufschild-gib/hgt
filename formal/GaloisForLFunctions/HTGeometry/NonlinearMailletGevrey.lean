import GaloisForLFunctions.HTGeometry.NonlinearMailletShift

/-!
# Maillet's theorem for a nonlinear analytic algebraic differential equation

Every formal solution of

```text
P(t, θF, …, θ^m F) = 0 ,      θ = t d/dt ,
```

with convergent coefficients and a nonzero indicial polynomial along a truncation of the solution
is Gevrey of a finite integral order.  This is the nondegenerate case of the estimate proved at an
arbitrary leading shift, read at shift zero.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- **Maillet's theorem, nonlinear case.**  A formal solution of an analytic algebraic differential
equation whose linearization along a truncation of order at least the order of the equation has a
nonzero indicial polynomial is Gevrey of a finite integral order. -/
theorem exists_isGevreySeries_of_isFormalEulerADESolution {m N : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : IsAnalyticDifferentialPolynomial P)
    {F : PowerSeries ℂ} (hsol : IsFormalEulerADESolution P F)
    (hNm : m ≤ N)
    (hΦ : shiftPolynomial (linearizationCoeff P (truncPowerSeries N F)) 0 ≠ 0) :
    ∃ r : ℕ, IsGevreySeries (r : ℝ) F :=
  exists_isGevreySeries_of_isFormalEulerADESolution_shift (v := 0) P hP hsol (by omega)
    (fun μ hμ => absurd hμ (by omega)) hΦ

end GaloisForLFunctions.HTGeometry
