import GaloisForLFunctions.HTGeometry.HelsonOppositeEulerNorm
import GaloisForLFunctions.HTGeometry.FiniteGaugeTailCharge

/-!
# Finite Euler gauges between Helson sheets

Finite changes of prime phase become exact finite, holomorphic, nonvanishing Euler gauges.  The
same-sheet theorem below identifies the ratio of the two Helson Dirichlet series.  Combining it
with the opposite-sheet norm law gives the corresponding norm identity for phases that are
opposite away from finitely many primes.
-/

noncomputable section

open Complex ArithmeticFunction LSeries

namespace GaloisForLFunctions.HTGeometry

/-- The exponential prime-decay coordinate is the usual complex power at a positive integer. -/
theorem analyticPrimeDecay_nat_eq_cpow (n : ℕ) (hn : 0 < n) (s : ℂ) :
    GaloisForLFunctions.analyticPrimeDecay (n : ℝ) s = (n : ℂ) ^ (-s) := by
  rw [GaloisForLFunctions.analyticPrimeDecay,
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne')]
  rw [← Complex.ofReal_natCast, Complex.ofReal_log (by exact_mod_cast hn.le)]
  congr 1
  ring

/-- **Same-sheet analytic gauge law.**  Prime phases equal off a finite set have Helson Dirichlet
series differing by exactly the associated finite Euler gauge. -/
theorem LSeries_phaseChar_eq_mul_finiteEulerGaugeRatio_of_eq_off_finset
    {u v : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1)
    (hv : ∀ p : ℕ, Nat.Prime p → ‖v p‖ = 1)
    (P : Finset Nat.Primes)
    (hP : ∀ p : Nat.Primes, p ∉ P → u (p : ℕ) = v (p : ℕ))
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => phaseChar v n) s =
      LSeries (fun n => phaseChar u n) s *
        GaloisForLFunctions.finiteEulerGaugeRatio P
          (fun p : Nat.Primes => ((p : ℕ) : ℝ))
          (fun p : Nat.Primes => u (p : ℕ))
          (fun p : Nat.Primes => v (p : ℕ)) s := by
  classical
  have hs0 : s ∈ GaloisForLFunctions.positiveHalfPlane := by
    exact lt_trans (by norm_num) hs
  have hgauge : HasProd
      (fun p : Nat.Primes =>
        GaloisForLFunctions.localEulerGaugeRatio ((p : ℕ) : ℝ)
          (u (p : ℕ)) (v (p : ℕ)) s)
      (GaloisForLFunctions.finiteEulerGaugeRatio P
        (fun p : Nat.Primes => ((p : ℕ) : ℝ))
        (fun p : Nat.Primes => u (p : ℕ))
        (fun p : Nat.Primes => v (p : ℕ)) s) := by
    rw [GaloisForLFunctions.finiteEulerGaugeRatio]
    refine hasProd_prod_of_ne_finset_one ?_
    intro p hp
    rw [GaloisForLFunctions.localEulerGaugeRatio, hP p hp]
    apply div_self
    exact GaloisForLFunctions.one_sub_phase_mul_analyticPrimeDecay_ne_zero
      (by exact_mod_cast p.2.one_lt) (hv (p : ℕ) p.2) hs0
  have hprod := (hasProd_phaseEuler hu hs).mul hgauge
  have hshape :
      (fun p : Nat.Primes =>
        (1 - u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ *
          GaloisForLFunctions.localEulerGaugeRatio ((p : ℕ) : ℝ)
            (u (p : ℕ)) (v (p : ℕ)) s) =
      (fun p : Nat.Primes =>
        (1 - v (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) := by
    funext p
    rw [GaloisForLFunctions.localEulerGaugeRatio,
      analyticPrimeDecay_nat_eq_cpow (p : ℕ) p.2.pos]
    have hu0 : 1 - u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := by
      simpa [analyticPrimeDecay_nat_eq_cpow (p : ℕ) p.2.pos] using
        (GaloisForLFunctions.one_sub_phase_mul_analyticPrimeDecay_ne_zero
          (show (1 : ℝ) < ((p : ℕ) : ℝ) by exact_mod_cast p.2.one_lt)
          (hu (p : ℕ) p.2) hs0)
    have hv0 : 1 - v (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := by
      simpa [analyticPrimeDecay_nat_eq_cpow (p : ℕ) p.2.pos] using
        (GaloisForLFunctions.one_sub_phase_mul_analyticPrimeDecay_ne_zero
          (show (1 : ℝ) < ((p : ℕ) : ℝ) by exact_mod_cast p.2.one_lt)
          (hv (p : ℕ) p.2) hs0)
    field_simp
  rw [hshape] at hprod
  exact HasProd.unique (hasProd_phaseEuler hv hs) hprod

/-- **Opposite-sheet analytic gauge law.**  Prime phases opposite off a finite set have product
equal to `ζ(2s)` times exactly the finite defect gauge. -/
theorem
    LSeries_phaseChar_mul_eq_riemannZeta_two_mul_mul_finiteEulerGaugeRatio_of_opposite_off_finset
    {u v : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1)
    (hv : ∀ p : ℕ, Nat.Prime p → ‖v p‖ = 1)
    (hsq : ∀ p : ℕ, Nat.Prime p → u p ^ 2 = 1)
    (P : Finset Nat.Primes)
    (hP : ∀ p : Nat.Primes, p ∉ P → v (p : ℕ) = -u (p : ℕ))
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => phaseChar u n) s * LSeries (fun n => phaseChar v n) s =
      riemannZeta (2 * s) *
        GaloisForLFunctions.finiteEulerGaugeRatio P
          (fun p : Nat.Primes => ((p : ℕ) : ℝ))
          (fun p : Nat.Primes => -u (p : ℕ))
          (fun p : Nat.Primes => v (p : ℕ)) s := by
  have hneg : ∀ p : ℕ, Nat.Prime p → ‖-u p‖ = 1 := by
    intro p hp
    simpa using hu p hp
  have hsame := LSeries_phaseChar_eq_mul_finiteEulerGaugeRatio_of_eq_off_finset
    hneg hv P (fun p hp => (hP p hp).symm) hs
  have hnorm := LSeries_phaseChar_mul_opposite_eq_riemannZeta_two_mul hu hsq hs
  rw [hsame]
  rw [← mul_assoc, hnorm]

end GaloisForLFunctions.HTGeometry
