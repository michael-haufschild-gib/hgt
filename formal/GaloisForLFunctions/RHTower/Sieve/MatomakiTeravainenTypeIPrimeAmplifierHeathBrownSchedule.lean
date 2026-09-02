import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierSchedule

/-!
# Height routing for the Heath--Brown Type-I prime amplifier

The Section 5.1 degree gives `P^ell ≤ P T^(1/10)`.  Since `2^ell ≤ P^ell`, the complete support
`(2P)^ell` lies below `T` as soon as the polylogarithmic prime scale satisfies `P ≤ T^(2/5)`.
This discharges the last block-height premise of the specialized Type-I receiver.
-/

namespace RHTower.Sieve

noncomputable section

/-- The canonical Section 5.1 power has complete support below the height. -/
theorem mtTypeIPrimeDegree_fullSupport_le_height
    {P : ℕ} {T : ℝ} (hP : 2 ≤ P) (hT : 1 ≤ T)
    (hPT : (P : ℝ) ≤ T ^ (2 / 5 : ℝ)) :
    ((((2 * P) ^ mtTypeIPrimeDegree P T : ℕ) : ℝ)) ≤ T := by
  let ell := mtTypeIPrimeDegree P T
  have hwindow := mtTypeIPrimeDegree_power_window hP hT
  have hPpow : (((P ^ ell : ℕ) : ℝ)) ≤ (P : ℝ) * T ^ (1 / 10 : ℝ) := by
    simpa only [ell] using hwindow.2
  have htwoNat : 2 ^ ell ≤ P ^ ell :=
    Nat.pow_le_pow_left hP ell
  have htwo : (((2 ^ ell : ℕ) : ℝ)) ≤ (((P ^ ell : ℕ) : ℝ)) := by
    exact_mod_cast htwoNat
  have htwoUpper : (((2 ^ ell : ℕ) : ℝ)) ≤
      (P : ℝ) * T ^ (1 / 10 : ℝ) := htwo.trans hPpow
  have hhalf : (P : ℝ) * T ^ (1 / 10 : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
    calc
      (P : ℝ) * T ^ (1 / 10 : ℝ) ≤
          T ^ (2 / 5 : ℝ) * T ^ (1 / 10 : ℝ) := by gcongr
      _ = T ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add (by positivity : 0 < T)]
        norm_num
  calc
    ((((2 * P) ^ ell : ℕ) : ℝ)) =
        (((2 ^ ell : ℕ) : ℝ)) * (((P ^ ell : ℕ) : ℝ)) := by
      push_cast
      rw [mul_pow]
    _ ≤ ((P : ℝ) * T ^ (1 / 10 : ℝ)) ^ 2 := by
      nlinarith [htwoUpper, hPpow,
        show 0 ≤ (((2 ^ ell : ℕ) : ℝ)) by positivity,
        show 0 ≤ (((P ^ ell : ℕ) : ℝ)) by positivity,
        show 0 ≤ (P : ℝ) * T ^ (1 / 10 : ℝ) by positivity]
    _ ≤ (T ^ (1 / 2 : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hhalf 2
    _ = T := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity : 0 ≤ T)]
      norm_num

/-- Source-facing Type-I receiver at the canonical degree, with block-height fully discharged. -/
theorem setIntegral_mtTypeI_primeAmplifier_heathBrown_sourceDegree
    (a : ℕ → ℂ) (A P N N' : ℕ) (T V eta : ℝ)
    (hP : 2 ≤ P) (hN : 2 ≤ N) (hNN' : N < N') (hN'le : N' ≤ 2 * N)
    (hT : 2 ≤ T) (hPT : (P : ℝ) ≤ T ^ (2 / 5 : ℝ))
    (hV : 0 < V) (heta : 0 < eta) :
    let ell := mtTypeIPrimeDegree P T
    (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
        ‖mtWattCoefficientBlock a A t‖ ^ 2 *
          ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
      ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownBlockMomentBound
          eta a A P ell N N' T V r := by
  dsimp only
  apply setIntegral_mtTypeI_primeAmplifier_heathBrown_of_fullSupport_le
    a A P (mtTypeIPrimeDegree P T) N N' T V eta (one_le_two.trans hP)
      (mtTypeIPrimeDegree_pos hP (by linarith)) hN hNN' hN'le hT hV heta
  exact mtTypeIPrimeDegree_fullSupport_le_height hP (one_le_two.trans hT) hPT

end

end RHTower.Sieve
