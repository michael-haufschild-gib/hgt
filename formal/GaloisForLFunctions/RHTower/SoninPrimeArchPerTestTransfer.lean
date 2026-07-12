import GaloisForLFunctions.RHTower.SoninAllPrimeHankelCollapse
import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant

/-!
# Per-test Sonin to prime--Gamma trace-Hankel transfer

The all-prime Sonin residual construction gives an unconditional nonnegative trace-Hankel value
for every real polynomial.  The normalized continued prime--Gamma germ gives a second, independently
source-defined trace-Hankel value, whose integer-polynomial positivity implies RH.

It is therefore enough to supply an explicit positive aperture schedule, allowed to depend on the
integer test polynomial, along which the Sonin Gram value converges to the corresponding
prime--Gamma value.  The schedule is an argument of the coupling predicate rather than an
existential selector, so a caller must construct it before applying the transfer theorem.
-/

open Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- A source-side coupling between the positive all-prime Sonin trace-Hankel functional and the
normalized continued prime--Gamma trace-Hankel functional.  The aperture schedule is explicit and
may depend on the countable integer-polynomial test. -/
def SoninPrimeArchPerTestTraceHankelCoupling
    (aperture : Polynomial ℤ → ℕ → ℝ) : Prop :=
  (∀ p j, 0 < aperture p j) ∧
    ∀ p : Polynomial ℤ,
      Tendsto
        (fun j : ℕ =>
          (soninAllPrimeTraceHankel (aperture p j)
            (p.map (Int.castRingHom ℝ))).re)
        atTop
        (nhds (primeArchSourceTraceHankel
          (p.map (Int.castRingHom ℝ))).re)

/-- Per-test convergence from the nonnegative Sonin Gram values forces countable positivity of the
fixed prime--Gamma trace-Hankel functional. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_soninPerTestCoupling
    {aperture : Polynomial ℤ → ℕ → ℝ}
    (h : SoninPrimeArchPerTestTraceHankelCoupling aperture) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  exact ge_of_tendsto (h.2 p) (Eventually.of_forall fun j =>
    soninAllPrimeTraceHankel_re_nonneg (aperture p j)
      (p.map (Int.castRingHom ℝ)))

/-- **Source-to-source top-down chain.**  An explicit per-test positive-aperture coupling from the
all-prime Sonin Gram functional to the normalized continued prime--Gamma trace-Hankel functional
proves the Riemann hypothesis. -/
theorem riemannHypothesis_of_soninPrimeArchPerTestTraceHankelCoupling
    {aperture : Polynomial ℤ → ℕ → ℝ}
    (h : SoninPrimeArchPerTestTraceHankelCoupling aperture) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_soninPerTestCoupling h)

end

end RHTower
