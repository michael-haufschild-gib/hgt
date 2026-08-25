import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaLogPrimeHarmonicXiDivisorNoGo
import GaloisForLFunctions.RHTower.XiOrderedPrimeTraceClassRelocation
import GaloisForLFunctions.RHTower.PrimeDiagonalSingularValues

/-!
# Route-P prime-harmonic trace-class relocation no-go

Bertola's Malgrange-form construction and subsequent Hankel-composition Riemann--Hilbert theory
realize infinite-dimensional tau functions through trace-class Fredholm corrections.  This file
tests that spectrum-moving escape on the corpus's literal Route-P genus-one Stokes carrier.

The positive depth-zero Route-P eigenvalue at prime `p` is `8 * w(p,0) = 2/p`.  Under canonical
prime marking, the smooth Riemann--von Mangoldt reciprocal is `1/T_n`.  The corpus bounds
`T_n = O(n)`, while the prime number theorem gives `n/p_n -> 0`.  Hence the Route-P multiplier is
eventually at most half of the RVM multiplier.  Their difference retains half of the non-summable
RVM tail, so it is not trace class.

Ordered Xi reciprocals differ from the RVM skeleton by an absolutely summable sequence.  The same
obstruction therefore holds for Xi itself.  Any viable irregular-RH transport from this source
must carry genus-one spectral density or genuinely mix prime sectors; a prime-marked trace-class
diagonal correction cannot do it.  No RH assumption or fitted Xi coefficient is used.
-/

open scoped BigOperators InnerProductSpace Nat.Prime
open Filter

namespace RHTower

noncomputable section

/-- Positive depth-zero eigenvalue of the balanced Route-P prime-harmonic Stokes carrier. -/
def routePPrimitiveGammaJuliaDepthZeroStokesMultiplier (p : Nat.Primes) : ℝ :=
  8 * routePPrimitiveGammaJuliaLogCofinalTraceWeight (p, 0)

/-- The literal depth-zero Stokes multiplier is exactly `2/p`. -/
theorem routePPrimitiveGammaJuliaDepthZeroStokesMultiplier_eq (p : Nat.Primes) :
    routePPrimitiveGammaJuliaDepthZeroStokesMultiplier p = 2 / (p : ℝ) := by
  rw [routePPrimitiveGammaJuliaDepthZeroStokesMultiplier,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero]
  ring

/-- Canonically ordered Route-P depth-zero Stokes spectrum is asymptotically negligible against
the RVM reciprocal spectrum.  The half-bound is the exact tail comparison needed below. -/
theorem eventually_routePPrimitiveGammaJuliaDepthZeroStokesMultiplier_le_half_routeKPrimeRVM :
    ∀ᶠ n : ℕ in atTop,
      routePPrimitiveGammaJuliaDepthZeroStokesMultiplier (nthPrimeSubtype n) ≤
        routeKPrimeRVMReciprocal (nthPrimeSubtype n) / 2 := by
  let C : ℝ := 2 * routeKRVMBase * Real.exp 1
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos two_pos routeKRVMBase_pos) (Real.exp_pos 1)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / ((Nat.nth Nat.Prime n : ℕ) : ℝ) < (8 * C)⁻¹ := by
    exact tendsto_natCast_div_nthPrime.eventually_lt_const (inv_pos.mpr (by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hnsmall hn
  have hp : 0 < ((Nat.nth Nat.Prime n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.prime_nth_prime n).pos
  have hT : 0 < routeKRVMQuantile n :=
    routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)
  have h8C : 0 < 8 * C := by positivity
  have h8Cn : 8 * C * (n : ℝ) < ((Nat.nth Nat.Prime n : ℕ) : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hnsmall (mul_pos h8C hp)
    field_simp [h8C.ne', hp.ne'] at hmul
    nlinarith
  have hncast : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hquant := routeKRVMQuantile_le_linear n
  change routeKRVMQuantile n ≤ C * ((n : ℝ) + 1) at hquant
  have hfour : 4 * routeKRVMQuantile n < ((Nat.nth Nat.Prime n : ℕ) : ℝ) := by
    nlinarith
  rw [routePPrimitiveGammaJuliaDepthZeroStokesMultiplier_eq,
    routeKPrimeRVMReciprocal, routeKPrimeRVMIndex_nthPrimeSubtype]
  rw [show (routeKRVMQuantile n)⁻¹ / 2 =
      1 / (2 * routeKRVMQuantile n) by field_simp [hT.ne']]
  change 2 / ((Nat.nth Nat.Prime n : ℕ) : ℝ) ≤
    1 / (2 * routeKRVMQuantile n)
  rw [div_le_div_iff₀ hp (mul_pos (by norm_num) hT)]
  nlinarith

/-- No `ℓ¹` diagonal correction relocates the canonically prime-marked depth-zero Route-P Stokes
spectrum to the smooth RVM reciprocal spectrum. -/
theorem not_summable_abs_routeKPrimeRVMReciprocal_sub_routePPrimitiveDepthZeroStokes :
    ¬ Summable (fun p : Nat.Primes =>
      |routeKPrimeRVMReciprocal p -
        routePPrimitiveGammaJuliaDepthZeroStokesMultiplier p|) := by
  intro hprime
  have hnat : Summable (fun n : ℕ =>
      |routeKPrimeRVMReciprocal (nthPrimeSubtype n) -
        routePPrimitiveGammaJuliaDepthZeroStokesMultiplier (nthPrimeSubtype n)|) := by
    have hcomp := nthPrimeEquiv.summable_iff.mpr hprime
    simpa [Function.comp_def, nthPrimeEquiv] using hcomp
  obtain ⟨N, hN⟩ := eventually_atTop.1
    eventually_routePPrimitiveGammaJuliaDepthZeroStokesMultiplier_le_half_routeKPrimeRVM
  have htail : Summable (fun n : ℕ =>
      |routeKPrimeRVMReciprocal (nthPrimeSubtype (n + N)) -
        routePPrimitiveGammaJuliaDepthZeroStokesMultiplier
          (nthPrimeSubtype (n + N))|) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff N).mpr hnat
  have hhalf : Summable (fun n : ℕ =>
      routeKPrimeRVMReciprocal (nthPrimeSubtype (n + N)) / 2) := by
    refine Summable.of_nonneg_of_le
      (fun _ => div_nonneg (routeKPrimeRVMReciprocal_pos _).le (by norm_num))
      (fun n => ?_) htail
    have hle := hN (n + N) (by omega)
    have hdiff : 0 ≤ routeKPrimeRVMReciprocal (nthPrimeSubtype (n + N)) -
        routePPrimitiveGammaJuliaDepthZeroStokesMultiplier
          (nthPrimeSubtype (n + N)) := by
      linarith [routeKPrimeRVMReciprocal_pos (nthPrimeSubtype (n + N))]
    rw [abs_of_nonneg hdiff]
    linarith
  have htailRVM : Summable (fun n : ℕ =>
      routeKPrimeRVMReciprocal (nthPrimeSubtype (n + N))) := by
    exact (hhalf.mul_left 2).congr (fun _ => by ring)
  have htailQuantile : Summable (fun n : ℕ =>
      (routeKRVMQuantile (n + N))⁻¹) := by
    simpa [routeKPrimeRVMReciprocal, routeKPrimeRVMIndex_nthPrimeSubtype] using htailRVM
  exact not_summable_routeKRVMQuantile_reciprocal
    ((summable_nat_add_iff N).mp htailQuantile)

/-- Ordered Xi-to-RVM relocation is trace class, but ordered Xi-to-Route-P depth-zero relocation
is not.  Thus the missing arithmetic density cannot be an IIKS/Fredholm trace-class diagonal
correction over the literal prime-harmonic Stokes background. -/
theorem not_summable_abs_xiOrderedPrimeReciprocal_sub_routePPrimitiveDepthZeroStokes :
    ¬ Summable (fun p : Nat.Primes =>
      |xiOrderedPrimeReciprocal p -
        routePPrimitiveGammaJuliaDepthZeroStokesMultiplier p|) := by
  intro hxi
  apply not_summable_abs_routeKPrimeRVMReciprocal_sub_routePPrimitiveDepthZeroStokes
  apply Summable.of_nonneg_of_le
  · exact fun _ => abs_nonneg _
  · intro p
    calc
      |routeKPrimeRVMReciprocal p -
          routePPrimitiveGammaJuliaDepthZeroStokesMultiplier p| =
          |(routeKPrimeRVMReciprocal p - xiOrderedPrimeReciprocal p) +
            (xiOrderedPrimeReciprocal p -
              routePPrimitiveGammaJuliaDepthZeroStokesMultiplier p)| := by ring_nf
      _ ≤ |routeKPrimeRVMReciprocal p - xiOrderedPrimeReciprocal p| +
          |xiOrderedPrimeReciprocal p -
            routePPrimitiveGammaJuliaDepthZeroStokesMultiplier p| := abs_add_le _ _
      _ = |xiOrderedPrimeReciprocal p - routeKPrimeRVMReciprocal p| +
          |xiOrderedPrimeReciprocal p -
            routePPrimitiveGammaJuliaDepthZeroStokesMultiplier p| := by
        rw [abs_sub_comm (routeKPrimeRVMReciprocal p) (xiOrderedPrimeReciprocal p)]
  · exact summable_abs_xiOrderedPrimeReciprocal_sub_routeKPrimeRVMReciprocal.add hxi

/-- **Irregular-RH trace-class relocation capstone.** Both smooth RVM and ordered Xi targets are
separated from the source-native depth-zero Route-P Stokes spectrum by a non-`ℓ¹` displacement. -/
theorem routePPrimitive_GammaJulia_logPrimeHarmonic_traceClassRelocationNoGo :
    (¬ Summable (fun p : Nat.Primes =>
      |routeKPrimeRVMReciprocal p -
        routePPrimitiveGammaJuliaDepthZeroStokesMultiplier p|)) ∧
    (¬ Summable (fun p : Nat.Primes =>
      |xiOrderedPrimeReciprocal p -
        routePPrimitiveGammaJuliaDepthZeroStokesMultiplier p|)) := by
  exact ⟨not_summable_abs_routeKPrimeRVMReciprocal_sub_routePPrimitiveDepthZeroStokes,
    not_summable_abs_xiOrderedPrimeReciprocal_sub_routePPrimitiveDepthZeroStokes⟩

end

end RHTower
