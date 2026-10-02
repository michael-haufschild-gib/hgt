import GaloisForLFunctions.RHTower.RoutePDepthMatchedMomentNonclosability

/-!
# Moving-depth physical moments invisible to the complete Xi carrier

After division by the actual positive critical mass, a primitive depth jet tends
strongly to zero on the entire Xi divisor. Its physical mass remains one, while
its first and second moments grow on distinct radial scales. The exact centroid
remainder tends to zero. These facts support finite source stencils retaining
independent physical boundary coordinates; no signed history floor is asserted.
-/

open Complex Set Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section

def routePDepthMassNormalizedXiJet (p : Nat.Primes) (e : ℕ) :
    DeningerArithmeticJetHilbert :=
  routePDeningerUpperSquaredCauchyJet (-(Real.sqrt (Real.log (p : ℝ)) : ℂ)⁻¹)
    (routePPrimitiveDeningerUpperPoint (p, e) 0)

theorem routeP_depth_frequency (p : Nat.Primes) (e : ℕ) :
    xiGammaEulerPrimitiveLogFrequency (p, e) = ((e : ℝ) + 1) * Real.log (p : ℝ) := by
  simp [xiGammaEulerPrimitiveLogFrequency, xiGammaEulerValuationNat, Real.log_pow]

private theorem depth_point_eq (p : Nat.Primes) (e : ℕ) :
    (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ) =
      (xiGammaEulerPrimitiveLogFrequency (p, e) : ℂ) * I := by
  simp [routePPrimitiveDeningerUpperPoint_coe, routePPrimitiveBurnolCenteredMode]

private theorem depth_gap (p : Nat.Primes) (e : ℕ) :
    routePDeningerUpperSpectralGap (routePPrimitiveDeningerUpperPoint (p, e) 0) =
      ((e : ℝ) + 1) * Real.log (p : ℝ) - 1 / 2 := by
  rw [routePDeningerUpperSpectralGap, depth_point_eq]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  rw [routeP_depth_frequency]

private theorem depth_cauchy_le_base (p : Nat.Primes) (e : ℕ) (q : XiZeroCopy) :
    ‖xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ)
      (xiSpectralPoint q)‖ ≤
    ‖xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint (p, 0) 0 : ℂ)
      (xiSpectralPoint q)‖ := by
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hfreq : xiGammaEulerPrimitiveLogFrequency (p, 0) ≤
      xiGammaEulerPrimitiveLogFrequency (p, e) := by
    simp only [routeP_depth_frequency, Nat.cast_zero, zero_add, one_mul]
    nlinarith [Nat.cast_nonneg (α := ℝ) e]
  have hq := (xiSpectralPoint_im_mem_openHalf q).2
  have hb := half_lt_xiGammaEulerPrimitiveLogFrequency (p, 0)
  have hnorm : ‖xiSpectralPoint q -
      (routePPrimitiveDeningerUpperPoint (p, 0) 0 : ℂ)‖ ≤
      ‖xiSpectralPoint q - (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ)‖ := by
    have hsq (j : ℕ) : ‖xiSpectralPoint q -
        (routePPrimitiveDeningerUpperPoint (p, j) 0 : ℂ)‖ ^ 2 =
        (xiSpectralPoint q).re ^ 2 +
          ((xiSpectralPoint q).im - xiGammaEulerPrimitiveLogFrequency (p, j)) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, depth_point_eq]
      simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, sub_zero, mul_one, add_zero]
      ring
    have h0 := hsq 0
    have he := hsq e
    nlinarith [norm_nonneg (xiSpectralPoint q -
      (routePPrimitiveDeningerUpperPoint (p, 0) 0 : ℂ)),
      norm_nonneg (xiSpectralPoint q -
      (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ))]
  have hpos : 0 < ‖xiSpectralPoint q -
      (routePPrimitiveDeningerUpperPoint (p, 0) 0 : ℂ)‖ :=
    (routePDeningerUpperSpectralGap_pos _).trans
      (routePDeningerUpperSpectralGap_lt_norm_sub _ _)
  simp only [xiWeilCauchyTest, norm_inv]
  exact inv_anti₀ hpos hnorm

theorem tendsto_routePDepthMassNormalizedXiJet (p : Nat.Primes) :
    Tendsto (routePDepthMassNormalizedXiJet p) atTop (nhds 0) := by
  let A : ℂ := -(Real.sqrt (Real.log (p : ℝ)) : ℂ)⁻¹
  let g := fun e => routePDeningerUpperSpectralGap (routePPrimitiveDeningerUpperPoint (p, e) 0)
  let M := ∑' q : XiZeroCopy,
    ‖xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint (p, 0) 0 : ℂ) (xiSpectralPoint q)‖ ^ 2
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hg : Tendsto g atTop atTop := by
    simp only [g, depth_gap]
    have h : Tendsto (fun e : ℕ => ((e : ℝ) + 1) * Real.log (p : ℝ)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const hp
    convert tendsto_atTop_add_const_right atTop (-1 / 2 : ℝ) h using 1
    funext e
    ring
  have hi : Tendsto (fun e => (g e)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp hg
  have hb (e : ℕ) : ‖routePDepthMassNormalizedXiJet p e‖ ^ 2 ≤
      ‖A‖ ^ 2 * (g e)⁻¹ ^ 2 * M := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    calc
      _ ≤ ∑' q : XiZeroCopy, (‖A‖ ^ 2 * (g e)⁻¹ ^ 2) *
          ‖xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint (p, 0) 0 : ℂ)
            (xiSpectralPoint q)‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun q => ?_)
          (HilbertSchmidt.summable_coe_sq _)
          ((XiWeilSquareSummable_cauchy _).mul_left _)
        change ‖A * xiWeilCauchyTest
          (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ) (xiSpectralPoint q) ^ 2‖ ^ 2 ≤ _
        have h1 := norm_xiWeilCauchyTest_upper_le_gap_inv
          (routePPrimitiveDeningerUpperPoint (p, e) 0) q
        have h2 := depth_cauchy_le_base p e q
        rw [norm_mul, norm_pow]
        calc
          _ = ‖A‖ ^ 2 * ‖xiWeilCauchyTest
              (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ) (xiSpectralPoint q)‖ ^ 2 *
              ‖xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ)
                (xiSpectralPoint q)‖ ^ 2 := by ring
          _ ≤ _ := by gcongr
      _ = _ := tsum_mul_left
  have hlim : Tendsto (fun e => ‖A‖ ^ 2 * (g e)⁻¹ ^ 2 * M) atTop (nhds 0) := by
    simpa using ((hi.pow 2).const_mul (‖A‖ ^ 2)).mul_const M
  have hs := squeeze_zero (fun e => sq_nonneg _) hb hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_zero, Real.sqrt_zero, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hs.sqrt

theorem routeP_depth_weight_pos (p : Nat.Primes) (e : ℕ) :
    0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
  rw [criticalMellinAtomWeight_eq_div_sqrt, xiGammaEulerValuationNat,
    vonMangoldt_prime_pow_succ_eq_log (p, e)]
  exact div_pos (Real.log_pos (by exact_mod_cast p.property.one_lt))
    (Real.sqrt_pos.mpr (by exact_mod_cast pow_pos p.property.pos (e + 1)))

theorem routeP_depth_weight_amplitude (p : Nat.Primes) (e : ℕ) :
    (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) : ℂ) =
      (Real.sqrt (Real.log (p : ℝ)) : ℂ) *
        finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e)) := by
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).le
  rw [criticalMellinAtomWeight_eq_div_sqrt, finiteVonMangoldtDepthOneAmplitude,
    xiGammaEulerValuationNat, vonMangoldt_prime_pow_succ_eq_log (p, e), Real.sqrt_div hlog]
  have hsC : (Real.sqrt (Real.log (p : ℝ)) : ℂ) ^ 2 = (Real.log (p : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hlog
  simp only [Complex.ofReal_div]
  rw [← mul_div_assoc, ← pow_two, hsC]

theorem routePDepthMassNormalizedXiJet_eq (p : Nat.Primes) (e : ℕ) :
    routePDepthMassNormalizedXiJet p e =
      (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) : ℂ)⁻¹ •
        routePDeningerUpperSquaredCauchyJet
          (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e)))
          (routePPrimitiveDeningerUpperPoint (p, e) 0) := by
  apply lp.ext
  funext q
  change _ = (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) : ℂ)⁻¹ *
    (routePDeningerUpperSquaredCauchyJet
      (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e)))
      (routePPrimitiveDeningerUpperPoint (p, e) 0) q)
  simp only [routePDepthMassNormalizedXiJet, routePDeningerUpperSquaredCauchyJet,
    xiWeilEvaluationLp_apply,
    routePDeningerUpperSquaredCauchyTest, routeP_depth_weight_amplitude]
  field_simp [finiteVonMangoldtDepthOneAmplitude_primitive_ne_zero (p, e)]

theorem routeP_matched_second_arithmetic (n : ℕ) (hn : 0 < n) :
    ccmActualHeadMatchedParabolicMoment n 2 =
      criticalMellinAtomWeight n * (2 * n + criticalMellinAtomWeight n ^ 2 / 6) := by
  have hc := ccmActualHeadMatchedPolarCentroid_sq n hn
  have hw := ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight n
  have hm : ccmActualHeadMatchedParabolicMoment n 2 =
      criticalMellinAtomWeight n * ccmActualHeadMatchedPolarCentroid n ^ 2 / 2 +
        criticalMellinAtomWeight n ^ 3 / 24 := by
    rw [ccmActualHeadMatchedParabolicMoment, ccmActualHeadMatchedPolarCentroid, ← hw]
    simp [ccmParabolicMoment]
    ring
  rw [hm, hc]
  ring

def routePDepthRadius (p : Nat.Primes) (N : ℕ) : ℝ := (p : ℝ) ^ (N + 1)

theorem routePDepthRadius_pos (p : Nat.Primes) (N : ℕ) : 0 < routePDepthRadius p N := by
  exact pow_pos (by exact_mod_cast p.property.pos) _

theorem routePDepthRadius_tendsto (p : Nat.Primes) :
    Tendsto (routePDepthRadius p) atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt
    (by exact_mod_cast p.property.one_lt : (1 : ℝ) < p)).comp (tendsto_add_atTop_nat 1)

theorem routeP_even_depth_node (p : Nat.Primes) (N : ℕ) :
    (xiGammaEulerValuationNat (p, 2 * N + 1) : ℝ) = routePDepthRadius p N ^ 2 := by
  simp only [xiGammaEulerValuationNat, Nat.cast_pow, routePDepthRadius, ← pow_mul]
  congr 1
  omega

theorem routeP_even_depth_weight (p : Nat.Primes) (N : ℕ) :
    criticalMellinAtomWeight (xiGammaEulerValuationNat (p, 2 * N + 1)) =
      Real.log (p : ℝ) / routePDepthRadius p N := by
  have hw : ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, 2 * N + 1)) =
      Real.log (p : ℝ) := by
    exact vonMangoldt_prime_pow_succ_eq_log (p, 2 * N + 1)
  rw [criticalMellinAtomWeight_eq_div_sqrt, hw,
    routeP_even_depth_node, Real.sqrt_sq (routePDepthRadius_pos p N).le]

def routePDepthCentroidRemainder (p : Nat.Primes) (N : ℕ) : ℝ :=
  ccmActualHeadMatchedPolarCentroid (xiGammaEulerValuationNat (p, 2 * N + 1)) -
    2 * routePDepthRadius p N

theorem routePDepthCentroidRemainder_bounds (p : Nat.Primes) (N : ℕ) :
    0 ≤ routePDepthCentroidRemainder p N ∧
      routePDepthCentroidRemainder p N ≤
        criticalMellinAtomWeight (xiGammaEulerValuationNat (p, 2 * N + 1)) / 2 := by
  have hs := ccmActualHeadMatchedPolarCentroid_sq
    (xiGammaEulerValuationNat (p, 2 * N + 1))
    (by exact pow_pos p.property.pos _)
  rw [routeP_even_depth_node] at hs
  have hc := ccmActualHeadMatchedPolarCentroid_pos (xiGammaEulerValuationNat (p, 2 * N + 1))
  have hr := routePDepthRadius_pos p N
  have hw := routeP_depth_weight_pos p (2 * N + 1)
  unfold routePDepthCentroidRemainder
  constructor <;> nlinarith [sq_nonneg
    (ccmActualHeadMatchedPolarCentroid (xiGammaEulerValuationNat (p, 2 * N + 1)) -
      2 * routePDepthRadius p N)]

theorem tendsto_routePDepthCentroidRemainder (p : Nat.Primes) :
    Tendsto (routePDepthCentroidRemainder p) atTop (nhds 0) := by
  have hi := tendsto_inv_atTop_zero.comp (routePDepthRadius_tendsto p)
  have hw : Tendsto (fun N => criticalMellinAtomWeight
      (xiGammaEulerValuationNat (p, 2 * N + 1)) / 2) atTop (nhds 0) := by
    simp_rw [routeP_even_depth_weight, div_eq_mul_inv]
    simpa using (hi.const_mul (Real.log (p : ℝ))).mul_const (2 : ℝ)⁻¹
  exact squeeze_zero (fun N => (routePDepthCentroidRemainder_bounds p N).1)
    (fun N => (routePDepthCentroidRemainder_bounds p N).2) hw

end
end RHTower
