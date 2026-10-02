import GaloisForLFunctions.RHTower.RoutePPrimitiveDepthRadialGraphCollapse
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicVarianceBalance

/-!
# A physical Route P moment survives radial graph collapse

The exact binomial packets already vanish in every polynomial radial graph energy. Their
literal matched parabolic second moment has an explicit two-exponential formula and stays
separated from zero at even orders. Thus these graph energies cannot control this actual
source coordinate. The complete matched-minus-quantile signed pairing remains unestimated.
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower
noncomputable section

private theorem matched_second_arithmetic (n : ℕ) (hn : 0 < n) :
    ccmActualHeadMatchedParabolicMoment n 2 =
      criticalMellinAtomWeight n * (2 * n + criticalMellinAtomWeight n ^ 2 / 6) := by
  have hc := ccmActualHeadMatchedPolarCentroid_sq n hn
  have hw := ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight n
  have hm : ccmActualHeadMatchedParabolicMoment n 2 =
      criticalMellinAtomWeight n * ccmActualHeadMatchedPolarCentroid n ^ 2 / 2 +
        criticalMellinAtomWeight n ^ 3 / 24 := by
    rw [ccmActualHeadMatchedParabolicMoment, ccmActualHeadMatchedPolarCentroid,
      ← hw]
    simp [ccmParabolicMoment]
    ring
  rw [hm, hc]
  ring

private theorem depth_weight_amplitude (p : Nat.Primes) (e : ℕ) :
    (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) : ℂ) =
      (Real.sqrt (Real.log (p : ℝ)) : ℂ) *
        finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e)) := by
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).le
  rw [criticalMellinAtomWeight_eq_div_sqrt, finiteVonMangoldtDepthOneAmplitude,
    xiGammaEulerValuationNat, vonMangoldt_prime_pow_succ_eq_log (p, e), Real.sqrt_div hlog]
  have hs := Real.sq_sqrt hlog
  have hsC : (Real.sqrt (Real.log (p : ℝ)) : ℂ) ^ 2 = (Real.log (p : ℝ) : ℂ) := by
    exact_mod_cast hs
  simp only [Complex.ofReal_div]
  rw [← mul_div_assoc, ← pow_two, hsC]

private theorem depth_weight_sq (p : Nat.Primes) (e : ℕ) :
    criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) ^ 2 =
      Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ (e + 1) := by
  rw [criticalMellinAtomWeight_eq_div_sqrt, xiGammaEulerValuationNat,
    vonMangoldt_prime_pow_succ_eq_log (p, e), div_pow, Real.sq_sqrt (by positivity),
    Nat.cast_pow]

private theorem depth_weight_sq_shift (p : Nat.Primes) (e j : ℕ) :
    criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e + j)) ^ 2 =
      criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) ^ 2 *
        ((p : ℝ)⁻¹) ^ j := by
  rw [depth_weight_sq, depth_weight_sq]
  rw [show e + j + 1 = (e + 1) + j by omega, pow_add]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

private theorem depth_coefficient_weight (p : Nat.Primes) (e N j : ℕ) :
    routePDepthBinomialCoefficient p e N j *
      (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e + j)) : ℂ) =
      (-1 : ℂ) ^ j * (N.choose j : ℂ) *
        (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) : ℂ) := by
  rw [routePDepthBinomialCoefficient, depth_weight_amplitude, depth_weight_amplitude]
  field_simp [finiteVonMangoldtDepthOneAmplitude_primitive_ne_zero (p, e + j)]

/-- Literal matched parabolic second coordinate of the finite depth packet. -/
def routePDepthBinomialMatchedSecondMoment (p : Nat.Primes) (e N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), routePDepthBinomialCoefficient p e N j *
    (ccmActualHeadMatchedParabolicMoment (xiGammaEulerValuationNat (p, e + j)) 2 : ℂ)

private theorem alternating_binomial (x : ℂ) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ j * (N.choose j : ℂ) * x ^ j) =
      (1 - x) ^ N := by
  rw [show 1 - x = -x + 1 by ring, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  rw [neg_eq_neg_one_mul, mul_pow]
  simp only [one_pow, mul_one]
  ring

/-- Exact physical moment of the source-native binomial packet. -/
theorem routePDepthBinomialMatchedSecondMoment_eq (p : Nat.Primes) (e N : ℕ) :
    routePDepthBinomialMatchedSecondMoment p e N =
      (2 * (p : ℝ) ^ (e + 1) *
        criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) * (1 - (p : ℝ)) ^ N +
        criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) ^ 3 / 6 *
          (1 - (p : ℝ)⁻¹) ^ N : ℝ) := by
  let w := criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e))
  have hterm (j : ℕ) : routePDepthBinomialCoefficient p e N j *
      (ccmActualHeadMatchedParabolicMoment (xiGammaEulerValuationNat (p, e + j)) 2 : ℂ) =
      (2 * (p : ℂ) ^ (e + 1) * (w : ℂ)) *
          ((-1 : ℂ) ^ j * (N.choose j : ℂ) * (p : ℂ) ^ j) +
        ((w : ℂ) ^ 3 / 6) *
          ((-1 : ℂ) ^ j * (N.choose j : ℂ) * ((p : ℂ)⁻¹) ^ j) := by
    rw [matched_second_arithmetic _ (by
      unfold xiGammaEulerValuationNat
      exact pow_pos p.property.pos _)]
    push_cast
    rw [← mul_assoc, depth_coefficient_weight]
    have hsq := congrArg (fun x : ℝ => (x : ℂ)) (depth_weight_sq_shift p e j)
    simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_inv] at hsq
    rw [hsq]
    have hn : (xiGammaEulerValuationNat (p, e + j) : ℂ) =
        (p : ℂ) ^ (e + 1) * (p : ℂ) ^ j := by
      simp only [xiGammaEulerValuationNat]
      push_cast
      rw [show e + j + 1 = (e + 1) + j by omega, pow_add]
    rw [hn]
    push_cast
    dsimp [w]
    ring
  unfold routePDepthBinomialMatchedSecondMoment
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    alternating_binomial, alternating_binomial]
  dsimp [w]
  push_cast
  ring

private theorem depth_weight_pos (p : Nat.Primes) (e : ℕ) :
    0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
  rw [criticalMellinAtomWeight_eq_div_sqrt, xiGammaEulerValuationNat,
    vonMangoldt_prime_pow_succ_eq_log (p, e)]
  apply div_pos
  · exact Real.log_pos (by exact_mod_cast p.property.one_lt)
  · apply Real.sqrt_pos.mpr
    exact_mod_cast pow_pos p.property.pos (e + 1)

/-- The physical second moment remains separated from zero along even packet orders. -/
theorem routePDepthBinomialMatchedSecondMoment_even_lower (p : Nat.Primes) (e N : ℕ) :
    2 * (p : ℝ) ^ (e + 1) * criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) ≤
      (routePDepthBinomialMatchedSecondMoment p e (2 * N)).re := by
  rw [routePDepthBinomialMatchedSecondMoment_eq, Complex.ofReal_re]
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hw := depth_weight_pos p e
  have hmain : 1 ≤ (1 - (p : ℝ)) ^ (2 * N) := by
    rw [pow_mul]
    exact one_le_pow₀ (by nlinarith : (1 : ℝ) ≤ (1 - (p : ℝ)) ^ 2)
  have htail : 0 ≤ (1 - (p : ℝ)⁻¹) ^ (2 * N) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hbase : 0 ≤ 2 * (p : ℝ) ^ (e + 1) *
      criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hmain hbase
  have hlast : 0 ≤ criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) ^ 3 / 6 *
      (1 - (p : ℝ)⁻¹) ^ (2 * N) := by positivity
  linarith

/-- Polynomial radial graph completion cannot continuously recover this literal RP source
moment. The witness consists entirely of the finite binomial depth packets. -/
theorem not_routePMatchedSecondMoment_controlled_by_radialGraph
    (p : Nat.Primes) (e : ℕ) :
    ¬ ∃ (R : ℕ) (C : ℝ), ∀ N : ℕ,
      ‖routePDepthBinomialMatchedSecondMoment p e N‖ ^ 2 ≤
        C * ∑ r ∈ Finset.range (R + 1),
          routePRadialGraphEnergy r (routePDepthBinomialPacket p e N) := by
  rintro ⟨R, C, hC⟩
  let b : ℝ := 2 * (p : ℝ) ^ (e + 1) *
    criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e))
  have hb : 0 < b := by
    have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
    have hw := depth_weight_pos p e
    dsimp [b]
    positivity
  have htwo : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    exact eventually_atTop.mpr ⟨B, by omega⟩
  have hs := tendsto_finsetSum (Finset.range (R + 1))
    (fun r _ => (tendsto_routePRadialGraphEnergy_depthBinomialPacket p e r).comp htwo)
  have ht : Tendsto (fun N => C * ∑ r ∈ Finset.range (R + 1),
      routePRadialGraphEnergy r (routePDepthBinomialPacket p e (2 * N)))
      atTop (nhds 0) := by
    simpa using hs.const_mul C
  obtain ⟨N, hN⟩ := (ht.eventually_lt_const (sq_pos_of_pos hb)).exists
  have hnorm : b ≤ ‖routePDepthBinomialMatchedSecondMoment p e (2 * N)‖ :=
    (routePDepthBinomialMatchedSecondMoment_even_lower p e N).trans (Complex.re_le_norm _)
  have hsq := pow_le_pow_left₀ hb.le hnorm 2
  have h := hC (2 * N)
  linarith

end
end RHTower
