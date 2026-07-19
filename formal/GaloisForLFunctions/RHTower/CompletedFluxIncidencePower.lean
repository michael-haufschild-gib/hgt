import GaloisForLFunctions.RHTower.CompletedFluxPrimeArchDecomposition

/-!
# All-order completed-flux incidence powers

Every natural power of the removable completed-flux germ is analytic, reads the corresponding
signed Xi multiplicity moment at its center, is invariant under functional-equation reflection in
reflected coordinates, and has the exact binomial prime--archimedean source decomposition.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- The order-`m` completed-flux incidence germ. -/
def completedFluxIncidencePowerGermAt (m : ℕ) (rho x : ℂ) : ℂ :=
  completedFluxGermAt rho x ^ m

/-- Every completed-flux incidence power is analytic at its filled center. -/
theorem completedFluxIncidencePowerGermAt_analyticAt_zero
    (m : ℕ) (rho : ℂ) :
    AnalyticAt ℂ (completedFluxIncidencePowerGermAt m rho) 0 := by
  exact (completedFluxGermAt_analyticAt_zero rho).pow m

/-- The center of the order-`m` hierarchy is the signed `m`th Xi multiplicity moment. -/
theorem completedFluxIncidencePowerGermAt_zero (m : ℕ) (rho : ℂ) :
    completedFluxIncidencePowerGermAt m rho 0 =
      (-1 : ℂ) ^ m * ((analyticOrderAt xi rho).toNat : ℂ) ^ m := by
  rw [completedFluxIncidencePowerGermAt, completedFluxGermAt_zero, neg_pow]

/-- Even incidence powers read the positive multiplicity moment. -/
theorem completedFluxIncidencePowerGermAt_zero_of_even
    {m : ℕ} (hm : Even m) (rho : ℂ) :
    completedFluxIncidencePowerGermAt m rho 0 =
      ((analyticOrderAt xi rho).toNat : ℂ) ^ m := by
  rw [completedFluxIncidencePowerGermAt_zero, hm.neg_one_pow, one_mul]

/-- Odd incidence powers read the negative multiplicity moment forced by the flux residue. -/
theorem completedFluxIncidencePowerGermAt_zero_of_odd
    {m : ℕ} (hm : Odd m) (rho : ℂ) :
    completedFluxIncidencePowerGermAt m rho 0 =
      -((analyticOrderAt xi rho).toNat : ℂ) ^ m := by
  rw [completedFluxIncidencePowerGermAt_zero, hm.neg_one_pow, neg_one_mul]

/-- Functional-equation reflection preserves every order of the incidence hierarchy. -/
theorem completedFluxIncidencePowerGermAt_reflection
    (m : ℕ) (rho x : ℂ) :
    completedFluxIncidencePowerGermAt m (1 - rho) (-x) =
      completedFluxIncidencePowerGermAt m rho x := by
  rw [completedFluxIncidencePowerGermAt, completedFluxIncidencePowerGermAt,
    completedFluxGermAt_reflection]

/-- On the open strip, every incidence power is the corresponding power of the exact continued
prime plus archimedean/boundary source germ. -/
theorem completedFluxIncidencePowerGermAt_eq_primeArch_pow_eventually
    (m : ℕ) {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    completedFluxIncidencePowerGermAt m rho =ᶠ[nhds 0]
      fun x => (infinitePrimeFluxGermAt rho x +
        archimedeanBoundaryFluxGermAt rho x) ^ m := by
  filter_upwards [completedFluxGermAt_eq_prime_add_archimedean_eventually hstrip] with x hx
  rw [completedFluxIncidencePowerGermAt, hx]

/-- **All-order source incidence law.**  The order-`m` completed-flux germ is the exact binomial
sum of its prime and archimedean incidence strata. -/
theorem completedFluxIncidencePowerGermAt_eq_incidence_decomposition_eventually
    (m : ℕ) {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    completedFluxIncidencePowerGermAt m rho =ᶠ[nhds 0]
      fun x => ∑ j ∈ Finset.range (m + 1),
        infinitePrimeFluxGermAt rho x ^ j *
          archimedeanBoundaryFluxGermAt rho x ^ (m - j) *
            (m.choose j : ℂ) := by
  filter_upwards [completedFluxGermAt_eq_prime_add_archimedean_eventually hstrip] with x hx
  rw [completedFluxIncidencePowerGermAt, hx, add_pow]

end


end RHTower
