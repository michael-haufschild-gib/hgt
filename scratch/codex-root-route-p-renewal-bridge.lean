import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePWeightedChebyshevCredit
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinRieszMobiusRenewal
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszExponentialCoherentTrace

open scoped BigOperators Chebyshev
open ArithmeticFunction

namespace RHTower

private theorem routeP_sum_Icc_two_eq_range_shift
    (f : ℕ → ℝ) (K : ℕ) :
    (∑ n ∈ Finset.Icc 2 (K + 2), f n) =
      ∑ j ∈ Finset.range (K + 1), f (j + 2) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]

private theorem routeP_unitRiesz_atom_moment (x n : ℕ)
    (hx : 0 < x) (hn : 0 < n) :
    ((x : ℝ) / 2) *
        (vonMangoldt n * unitApertureCriticalPrimeWeight (x : ℝ) n) =
      vonMangoldt n *
        (Real.sqrt (x : ℝ) - Real.sqrt (n : ℝ)) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : Real.sqrt (x : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hxR).ne'
  have hr2 : Real.sqrt (x : ℝ) ^ (2 : ℕ) = (x : ℝ) := Real.sq_sqrt hxR.le
  rw [unitApertureCriticalPrimeWeight_eq_riesz hxR hnR,
    Real.sqrt_div hnR.le (x : ℝ)]
  field_simp [hr]
  nth_rewrite 1 [← hr2]
  ring

theorem routeP_unitRiesz_renewal_moment_bridge (K : ℕ) :
    ((K + 2 : ℕ) : ℝ) / 2 *
        unitRieszVonMangoldtRenewal (((K + 2 : ℕ) : ℝ)) (K + 2) =
      Real.sqrt ((K + 2 : ℕ) : ℝ) *
        Chebyshev.psi ((K + 2 : ℕ) : ℝ) -
      routePSqrtChebyshevMoment K := by
  unfold unitRieszVonMangoldtRenewal routePSqrtChebyshevMoment
  rw [routeP_sum_Icc_two_eq_range_shift, Finset.mul_sum,
    ← centroidAtomExcess_vonMangoldt_shift_two K,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have h := routeP_unitRiesz_atom_moment (K + 2) (j + 2) (by omega) (by omega)
  convert h using 1
  push_cast
  ring

theorem routePWeightedChebyshevNullCredit_eq_centered_unitRiesz_renewal (K : ℕ) :
    routePWeightedChebyshevNullCredit K =
      ((K + 2 : ℕ) : ℝ) * Real.sqrt ((K + 2 : ℕ) : ℝ) / 3 -
        ((K + 2 : ℕ) : ℝ) / 2 *
          unitRieszVonMangoldtRenewal (((K + 2 : ℕ) : ℝ)) (K + 2) := by
  rw [routeP_unitRiesz_renewal_moment_bridge]
  unfold routePWeightedChebyshevNullCredit
  ring

theorem routePWeightedChebyshevNullCredit_eq_unitRiesz_resolvent_source (K : ℕ) :
    routePWeightedChebyshevNullCredit K =
      -(((K + 2 : ℕ) : ℝ) / 2) *
        criticalMellinChebyshevResolventSource
          (Real.log (((K + 2 : ℕ) : ℝ))) := by
  have hx : (0 : ℝ) < ((K + 2 : ℕ) : ℝ) := by positivity
  have hprime :
      unitRieszVonMangoldtRenewal (((K + 2 : ℕ) : ℝ)) (K + 2) =
        GaloisForLFunctions.RHTower.unitRieszCoherentPrimeEnergy
          (((K + 2 : ℕ) : ℝ)) (K + 2) :=
    GaloisForLFunctions.RHTower.unitRieszVonMangoldtRenewal_eq_coherentPrimeEnergy
      hx (by rfl)
  have hsource :
      criticalMellinChebyshevResolventSource
          (Real.log (((K + 2 : ℕ) : ℝ))) =
        unitRieszVonMangoldtRenewal (((K + 2 : ℕ) : ℝ)) (K + 2) -
          (2 / 3) * Real.sqrt (((K + 2 : ℕ) : ℝ)) := by
    rw [GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventSource_log_nat_eq_coherentPrime_sub_polar
      (show 1 ≤ K + 2 by omega),
      ← hprime,
      GaloisForLFunctions.RHTower.unitRieszCoherentPolarEnergy_eq hx]
  rw [routePWeightedChebyshevNullCredit_eq_centered_unitRiesz_renewal,
    hsource]
  ring

end RHTower
