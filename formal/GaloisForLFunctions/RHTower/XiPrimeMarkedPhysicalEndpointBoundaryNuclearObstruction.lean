import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointCorrectionTraceClass
import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureFusion
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Nuclear obstruction at the physical ordinary-prime boundary

The valuation-resolved correction to the physical endpoint is absolutely nuclear, but the
remaining literal ordinary-prime frequency expansion is not.  Its coefficient at `r` is
`log(r)/r`; dressing the corresponding phase by the fixed square-summable physical endpoint
vector gives a positive rank-one atom whose operator norm is `log(r)/r` times one fixed positive
endpoint energy.  Euler's divergence of the prime harmonic series therefore makes the sum of
these norms diverge.

This is an obstruction to the direct absolutely nuclear source-frequency construction, not a
proof that every conditionally renormalized operator with the same matrix coefficients fails to
be trace class.  Route K must obtain a real boundary cancellation before taking trace norms.
-/

open scoped BigOperators InnerProductSpace

namespace RHTower

noncomputable section

/-- The physical ordinary-prime endpoint has divergent total mass. -/
theorem not_summable_physicalPrimeEndpointWeight :
    ¬ Summable (fun p : Nat.Primes => physicalPrimeEndpointWeight p) := by
  intro hsum
  let c : ℝ := Real.log 2
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hlower : ∀ p : Nat.Primes,
      c * (1 / (p : ℝ)) ≤ physicalPrimeEndpointWeight p := by
    intro p
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have hlog : c ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hp2
    rw [physicalPrimeEndpointWeight]
    simpa [one_div, div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hlog
        (by positivity : (0 : ℝ) ≤ ((p : ℝ))⁻¹))
  have hscaled : Summable (fun p : Nat.Primes => c * (1 / (p : ℝ))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hlower hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff hc.ne').mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

/-- Literal ordinary-prime boundary atom at source frequency `log r`. -/
def routeKPhysicalEndpointBoundaryRankOne
    (r : Nat.Primes) : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  (physicalPrimeEndpointWeight r : ℂ) •
    InnerProductSpace.rankOne ℂ
      (routeKPhysicalEndpointCorrectionPhaseVector (r, 0))
      (routeKPhysicalEndpointCorrectionPhaseVector (r, 0))

/-- Every boundary atom has the physical coefficient times the same endpoint energy. -/
theorem norm_routeKPhysicalEndpointBoundaryRankOne
    (r : Nat.Primes) :
    ‖routeKPhysicalEndpointBoundaryRankOne r‖ =
      physicalPrimeEndpointWeight r *
        (∑' p : Nat.Primes, physicalPrimeEndpointWeight p ^ 2) := by
  rw [routeKPhysicalEndpointBoundaryRankOne, norm_smul,
    InnerProductSpace.norm_rankOne, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (physicalPrimeEndpointWeight_pos r), ← pow_two,
    norm_sq_routeKPhysicalEndpointCorrectionPhaseVector]

private theorem routeKPhysicalEndpointEnergy_pos :
    0 < ∑' p : Nat.Primes, physicalPrimeEndpointWeight p ^ 2 := by
  let two : Nat.Primes := ⟨2, by norm_num⟩
  rw [← norm_sq_routeKPhysicalEndpointCorrectionPhaseVector (two, 0)]
  apply sq_pos_of_pos
  rw [norm_pos_iff]
  intro hzero
  have hvalue := congrArg
    (fun v : RouteKPrimeHilbert => v two) hzero
  rw [routeKPhysicalEndpointCorrectionPhaseVector_apply] at hvalue
  have hweight : (physicalPrimeEndpointWeight two : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (physicalPrimeEndpointWeight_pos two).ne'
  have hprod :
      (physicalPrimeEndpointWeight two : ℂ) *
          Complex.exp
            (((-routeKPhysicalEndpointCorrectionFrequency (two, 0) *
              Real.log (two : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero hweight (Complex.exp_ne_zero _)
  exact hprod (by simpa using hvalue)

/-- **Sharp direct-construction obstruction.** The literal ordinary-prime boundary atoms are not
absolutely summable in operator norm, hence the direct rank-one source-frequency series is not an
absolutely nuclear construction. -/
theorem not_summable_norm_routeKPhysicalEndpointBoundaryRankOne :
    ¬ Summable (fun r : Nat.Primes =>
      ‖routeKPhysicalEndpointBoundaryRankOne r‖) := by
  intro hsum
  have henergy :
      (∑' p : Nat.Primes, physicalPrimeEndpointWeight p ^ 2) ≠ 0 :=
    ne_of_gt routeKPhysicalEndpointEnergy_pos
  have hscaled : Summable (fun r : Nat.Primes =>
      physicalPrimeEndpointWeight r *
        (∑' p : Nat.Primes, physicalPrimeEndpointWeight p ^ 2)) :=
    hsum.congr (fun r => norm_routeKPhysicalEndpointBoundaryRankOne r)
  have hphysical : Summable
      (fun r : Nat.Primes => physicalPrimeEndpointWeight r) :=
    (summable_mul_right_iff henergy).mp hscaled
  exact not_summable_physicalPrimeEndpointWeight hphysical

end

end RHTower
