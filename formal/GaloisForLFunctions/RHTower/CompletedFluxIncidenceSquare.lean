import GaloisForLFunctions.RHTower.CompletedFluxPrimeArchDecomposition

/-!
# The completed-flux incidence square reads multiplicity squared

The removable completed local flux germ has center value `-ord_ρ(Xi)`.  Squaring it produces an
analytic reflection-invariant germ with center value `ord_ρ(Xi)^2`.  On the open strip, the existing
prime--archimedean germ decomposition expands its square into three source incidence terms:

* prime--prime;
* twice prime--archimedean;
* archimedean--archimedean.

This is the local symmetric-incidence seed required by a quadratic reflection-anomaly route.  It
does not construct an equivariant fixed-point subtraction, a finite-window character, or a source
annihilation theorem.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- Square of the removable completed local flux germ. -/
def completedFluxIncidenceSquareGermAt (ρ x : ℂ) : ℂ :=
  (completedFluxGermAt ρ x) ^ 2

/-- The incidence-square germ is analytic at its filled center. -/
theorem completedFluxIncidenceSquareGermAt_analyticAt_zero (ρ : ℂ) :
    AnalyticAt ℂ (completedFluxIncidenceSquareGermAt ρ) 0 := by
  exact (completedFluxGermAt_analyticAt_zero ρ).pow 2

/-- Its center value is exactly the square of the finite local Xi order. -/
theorem completedFluxIncidenceSquareGermAt_zero (ρ : ℂ) :
    completedFluxIncidenceSquareGermAt ρ 0 =
      ((analyticOrderAt xi ρ).toNat : ℂ) ^ 2 := by
  simp [completedFluxIncidenceSquareGermAt]

/-- The local square is invariant under functional-equation reflection in reflected coordinates. -/
theorem completedFluxIncidenceSquareGermAt_reflection (ρ x : ℂ) :
    completedFluxIncidenceSquareGermAt (1 - ρ) (-x) =
      completedFluxIncidenceSquareGermAt ρ x := by
  simp [completedFluxIncidenceSquareGermAt, completedFluxGermAt_reflection]

/-- On the strip, the incidence square is the square of the exact continued prime plus
archimedean/boundary source germ. -/
theorem completedFluxIncidenceSquareGermAt_eq_primeArch_square_eventually
    {ρ : ℂ} (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    completedFluxIncidenceSquareGermAt ρ =ᶠ[nhds 0]
      fun x => (infinitePrimeFluxGermAt ρ x + archimedeanBoundaryFluxGermAt ρ x) ^ 2 := by
  filter_upwards [completedFluxGermAt_eq_prime_add_archimedean_eventually hstrip] with x hx
  simp [completedFluxIncidenceSquareGermAt, hx]

/-- Expanded symmetric incidence law: prime--prime plus twice prime--archimedean plus
archimedean--archimedean. -/
theorem completedFluxIncidenceSquareGermAt_eq_incidence_decomposition_eventually
    {ρ : ℂ} (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    completedFluxIncidenceSquareGermAt ρ =ᶠ[nhds 0]
      fun x => (infinitePrimeFluxGermAt ρ x) ^ 2 +
        2 * infinitePrimeFluxGermAt ρ x * archimedeanBoundaryFluxGermAt ρ x +
        (archimedeanBoundaryFluxGermAt ρ x) ^ 2 := by
  filter_upwards [completedFluxGermAt_eq_prime_add_archimedean_eventually hstrip] with x hx
  rw [completedFluxIncidenceSquareGermAt, hx]
  ring

end

end RHTower
