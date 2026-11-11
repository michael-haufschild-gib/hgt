import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailCombLimit
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ArithmeticPowerProfileMellinIntegral
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OrderedDirichletMellinPairing
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorEnergyPaysTheCriticalZeros
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorSymbolSplitsAtTheZeros

/-!
# The prime-error Mellin integral of a power tail

RH gives the prime-error row every growth exponent above one half.
Squaring and summing against the pronic weight supplies the existing
Mellin continuation theorem's energy bound. Ordered Abel summation then
identifies the power-tail integral with `-ζ'/ζ-ζ` at `1-a`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Complex
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity
open TransHorizonIncidenceMechanics

theorem exists_primeErrorRow_power_bound_of_rh (hRH : RiemannHypothesis)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |primeErrorRow N| ≤ C * (N : ℝ) ^ σ := by
  obtain ⟨C, hC, hbound⟩ := RHTower.exists_abs_sum_vonMangoldtMinusOne_le_of_converges
    (show 0 < σ by linarith only [hσ])
    (RHTower.riemannHypothesis_iff_vonMangoldtMinusOne_converges.mp hRH σ hσ)
  refine ⟨C, hC, fun N => ?_⟩
  have he : primeErrorRow N = ∑ n ∈ range N, RHTower.vonMangoldtMinusOne n := by
    change RHTower.sourcePartialSum (fun n => ArithmeticFunction.vonMangoldt n - 1) N = _
    rw [← RHTower.sum_range_succ_eq_sourcePartialSum
      (fun n => ArithmeticFunction.vonMangoldt n - 1)]
    rfl
  rw [he]
  exact hbound N

/-- RH pays every positive subunit power bound for the pronic prime-error energy. -/
theorem exists_primeErrorRow_energy_bound_of_rh (hRH : RiemannHypothesis)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ,
      (∑ n ∈ Icc 1 N, primeErrorRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
        D * ((N : ℝ) + 1) ^ κ := by
  obtain ⟨C, hC, hbound⟩ := exists_primeErrorRow_power_bound_of_rh hRH
    (show 1 / 2 < (1 + κ) / 2 by linarith only [hκ])
  refine ⟨C ^ 2 / κ, by positivity, fun N => ?_⟩
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      primeErrorRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ C ^ 2 * (n : ℝ) ^ (κ - 1) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hsquare := pow_le_pow_left₀ (abs_nonneg (primeErrorRow n)) (hbound n) 2
    rw [sq_abs, mul_pow] at hsquare
    have hpow : ((n : ℝ) ^ ((1 + κ) / 2)) ^ 2 = (n : ℝ) ^ (1 + κ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      norm_num
    rw [hpow] at hsquare
    calc
      _ ≤ primeErrorRow n ^ 2 / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hn0)
          (by nlinarith only [hn0])
      _ ≤ (C ^ 2 * (n : ℝ) ^ (1 + κ)) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hsquare (sq_nonneg _)
      _ = _ := by
        rw [mul_div_assoc, show (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) by rw [Real.rpow_two],
          ← Real.rpow_sub hn0]
        congr 2
        norm_num <;> ring
  have hp := (powerTailPrefix_sub_integral_bounds
    (show 0 < 1 - κ by linarith only [hκ1])
    (show 1 - κ < 1 by linarith only [hκ]) (Nat.cast_nonneg N)).2
  have hsum : (∑ n ∈ Icc 1 N, (n : ℝ) ^ (κ - 1)) ≤ (N : ℝ) ^ κ / κ := by
    simp only [powerTailPrefix, Nat.floor_natCast, powerTailWeight,
      show -(1 - κ) = κ - 1 by ring, show 1 - (1 - κ) = κ by ring] at hp
    linarith only [hp]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, C ^ 2 * (n : ℝ) ^ (κ - 1) := sum_le_sum hterm
    _ = C ^ 2 * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (κ - 1) := (mul_sum _ _ _).symm
    _ ≤ C ^ 2 * ((N : ℝ) ^ κ / κ) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (C ^ 2 / κ) * (N : ℝ) ^ κ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) hκ.le) (by positivity)

/-- The weighted prime-deviation integral has the continued prime-error symbol. -/
theorem mul_primePowerMellinIntegral_eq (hRH : RiemannHypothesis)
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    (1 - 2 * (a : ℂ)) *
      ((∫ t in Set.Ioc (0 : ℝ) 1,
        arithmeticPowerProfile (2 * a) (powerTailPrimeDeviation a) t : ℝ) : ℂ) =
      -deriv riemannZeta (1 - (a : ℂ)) / riemannZeta (1 - (a : ℂ)) -
        riemannZeta (1 - (a : ℂ)) := by
  let κ : ℝ := 1 / 2 - a
  have hκ : 0 < κ := by dsimp only [κ]; linarith only [ha2]
  have hκ1 : κ < 1 := by dsimp only [κ]; linarith only [ha]
  have hσ : 1 / 2 < (1 + κ) / 2 := by linarith only [hκ]
  have hσa : (1 + κ) / 2 < 1 - a := by dsimp only [κ]; linarith only [ha2]
  obtain ⟨C, hC, hbound⟩ := exists_primeErrorRow_power_bound_of_rh hRH hσ
  obtain ⟨D, hD, henergy⟩ := exists_primeErrorRow_energy_bound_of_rh hRH hκ hκ1
  have hs0 : 0 < (1 - (a : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith only [ha2]
  have hs1 : 1 - (a : ℂ) ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hh
    linarith only [ha, hh]
  have hζ := ArithmeticCorrespondencePositivity.riemannZeta_ne_zero_of_riemannHypothesis hRH
    (s := 1 - (a : ℂ)) (by
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith only [ha2])
  have hsymbol := complexMellinPairing_primeErrorRow_eq hD hκ.le henergy
    (s := 1 - (a : ℂ)) (by simpa only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      using hσa) hs1 hζ
  have hordered := tendsto_orderedDirichlet_complexMellinPairing
    (b := fun n => ArithmeticFunction.vonMangoldt n - 1) hC hbound hs0
    (by simpa only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] using hσa)
  change Tendsto _ atTop (𝓝 (complexMellinPairing primeErrorRow (1 - (a : ℂ)))) at hordered
  rw [hsymbol] at hordered
  obtain ⟨β, B, hβ, hsub, hB, hprime⟩ := exists_powerTailPrimeDeviation_bound_of_rh hRH ha ha2
  have hreal := tendsto_weighted_sums_arithmeticPowerProfile
    (show 0 ≤ 2 * a by linarith only [ha]) hβ
    (show 0 < 2 * a + β by linarith only [ha, hβ]) hsub hB hprime
  have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hcast' : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      ((ArithmeticFunction.vonMangoldt n - 1 : ℝ) : ℂ) * (n : ℂ) ^ (-(1 - (a : ℂ)))) atTop
      (𝓝 ((1 - 2 * (a : ℂ)) *
        ((∫ t in Set.Ioc (0 : ℝ) 1,
          arithmeticPowerProfile (2 * a) (powerTailPrimeDeviation a) t : ℝ) : ℂ))) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_ofNat] at hcast
    refine hcast.congr fun N => ?_
    simp only [Function.comp_apply, Complex.ofReal_sum]
    apply sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnne : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have hdev : powerTailPrimeDeviation a n =
        powerTailWeight a n * (ArithmeticFunction.vonMangoldt n - 1) := by
      change powerTailWeight a n *
        (ArithmeticFunction.vonMangoldt n - (ζ : ArithmeticFunction ℝ) n) = _
      simp [hnne]
    have he : powerTailPrimeDeviation a n * (n : ℝ) ^ (-(1 - 2 * a)) =
        (ArithmeticFunction.vonMangoldt n - 1) * (n : ℝ) ^ (-(1 - a)) := by
      rw [hdev, powerTailWeight, mul_right_comm, ← Real.rpow_add hn0,
        show -a + -(1 - 2 * a) = -(1 - a) by ring, mul_comm]
    rw [he, Complex.ofReal_mul, Complex.ofReal_cpow hn0.le]
    push_cast <;> rfl
  exact tendsto_nhds_unique hcast' hordered

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
