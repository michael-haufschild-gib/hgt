import GaloisForLFunctions.RHTower.RoutePDepthBinomialLaplaceControl

/-!
# Literal primitive depth packets vanish in the complete Xi jet carrier

The binomial residual uses the exact primitive amplitudes and squared-Cauchy source jets.
Its Laplace incidence holds at every copy of the Xi divisor, without restricting zeros to
one side of the strip. Positive-slope Laplace domination and unconditional Cauchy square
summability prove strong convergence to zero. This concerns the source domain; it does not
provide the signed Route-P history floor.
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower
noncomputable section

def routePPrimitiveXiLaplaceRate (pe : Nat.Primes × ℕ) (q : XiZeroCopy) : ℂ :=
  I * xiSpectralPoint q + (xiGammaEulerPrimitiveLogFrequency pe : ℂ)

private theorem rate_re_pos (pe : Nat.Primes × ℕ) (q : XiZeroCopy) :
    0 < (routePPrimitiveXiLaplaceRate pe q).re := by
  have hf := half_lt_xiGammaEulerPrimitiveLogFrequency pe
  have hq := (xiSpectralPoint_im_mem_openHalf q).2
  simp only [routePPrimitiveXiLaplaceRate, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, Complex.ofReal_re]
  linarith

private theorem cauchy_eq (pe : Nat.Primes × ℕ) (q : XiZeroCopy) :
    xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint pe 0 : ℂ)
      (xiSpectralPoint q) = I * (routePPrimitiveXiLaplaceRate pe q)⁻¹ := by
  rw [xiWeilCauchyTest, routePPrimitiveDeningerUpperPoint_coe]
  simp only [routePPrimitiveBurnolCenteredMode, Complex.ofReal_zero, mul_zero, add_zero]
  have heq : xiSpectralPoint q - (xiGammaEulerPrimitiveLogFrequency pe : ℂ) * I =
      -I * routePPrimitiveXiLaplaceRate pe q := by
    dsimp [routePPrimitiveXiLaplaceRate]
    ring_nf
    simp [I_sq]
  rw [heq, mul_inv]
  simp [inv_neg, Complex.inv_I]

private theorem primitive_integrand_eq (pe : Nat.Primes × ℕ) (q : XiZeroCopy) (t : ℝ) :
    Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) *
        routePPrimitiveBurnolWindowFeature pe 0 t =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        (Complex.exp (-(routePPrimitiveXiLaplaceRate pe q * (t : ℂ))) * (t : ℂ)) := by
  rw [routePPrimitiveBurnolWindowFeature_eq_resolvedRadialGeneratorMode]
  simp only [Complex.ofReal_zero, mul_zero, add_zero, xiWardResolvedRadialGeneratorMode,
    xiWardResolvedRadialMode]
  rw [show -(routePPrimitiveXiLaplaceRate pe q * (t : ℂ)) =
      -(I * xiSpectralPoint q * (t : ℂ)) -
        (xiGammaEulerPrimitiveLogFrequency pe : ℂ) * (t : ℂ) by
    dsimp [routePPrimitiveXiLaplaceRate]; ring, sub_eq_add_neg, Complex.exp_add]
  ring

private theorem integrable_primitive (pe : Nat.Primes × ℕ) (q : XiZeroCopy) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) *
      routePPrimitiveBurnolWindowFeature pe 0 t) (Ioi 0) := by
  simp_rw [primitive_integrand_eq]
  refine ((integrable_routePDepthLaplace (lam := 1) (by norm_num) 0
    (rate_re_pos pe q)).const_mul
      (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe))).congr ?_
  filter_upwards with t
  simp [routePDepthCutoff]

/-- The primitive squared-Cauchy reporter has its literal Laplace incidence at every Xi copy,
including the left and central parts of the strip. -/
theorem routePPrimitiveSquaredJet_allXi_apply (pe : Nat.Primes × ℕ) (q : XiZeroCopy) :
    routePDeningerUpperSquaredCauchyJet
        (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe))
        (routePPrimitiveDeningerUpperPoint pe 0) q =
      ∫ t : ℝ in Ioi 0, Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) *
        routePPrimitiveBurnolWindowFeature pe 0 t := by
  have hfun : (fun t : ℝ => Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) *
        routePPrimitiveBurnolWindowFeature pe 0 t) =
      fun t : ℝ => finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) *
          xiWardResolvedRadialGeneratorMode (xiGammaEulerPrimitiveLogFrequency pe : ℂ) t) := by
    funext t
    rw [routePPrimitiveBurnolWindowFeature_eq_resolvedRadialGeneratorMode]
    simp only [Complex.ofReal_zero, mul_zero, add_zero]
    ring
  rw [hfun, integral_const_mul,
    integral_xiWardResolvedRadialGeneratorMode_laplace (rate_re_pos pe q),
    routePDeningerUpperSquaredCauchyJet, xiWeilEvaluationLp_apply,
    routePDeningerUpperSquaredCauchyTest, cauchy_eq]
  change -_ * (I * (routePPrimitiveXiLaplaceRate pe q)⁻¹) ^ 2 =
    _ * (routePPrimitiveXiLaplaceRate pe q)⁻¹ ^ 2
  ring_nf
  simp [I_sq]

/-- The exact source coefficients applied to the actual complete-divisor primitive jets. -/
def routePDepthBinomialXiJet (p : Nat.Primes) (e N : ℕ) : DeningerArithmeticJetHilbert :=
  ∑ j ∈ Finset.range (N + 1), routePDepthBinomialCoefficient p e N j •
    routePDeningerUpperSquaredCauchyJet
      (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e + j)))
      (routePPrimitiveDeningerUpperPoint (p, e + j) 0)

theorem routePDepthBinomialXiJet_apply (p : Nat.Primes) (e N : ℕ) (q : XiZeroCopy) :
    routePDepthBinomialXiJet p e N q =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e)) *
        routePDepthLaplace (Real.log (p : ℝ)) N (routePPrimitiveXiLaplaceRate (p, e) q) := by
  classical
  simp only [routePDepthBinomialXiJet, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, routePPrimitiveSquaredJet_allXi_apply]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · rw [routePDepthLaplace, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    have hp := routePDepthBinomialPacket_eq p e N t
    have heq : (∑ j ∈ Finset.range (N + 1), routePDepthBinomialCoefficient p e N j *
        (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) *
          routePPrimitiveBurnolWindowFeature (p, e + j) 0 t)) =
        Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) * routePDepthBinomialPacket p e N t := by
      rw [routePDepthBinomialPacket, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq, hp]
    rw [← mul_assoc, primitive_integrand_eq]
    simp only [routePDepthCutoff, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  · intro j hj
    exact (integrable_primitive (p, e + j) q).const_mul _

private theorem depth_log_prime_pos (p : Nat.Primes) : 0 < Real.log (p : ℝ) := by
  apply Real.log_pos
  exact_mod_cast p.property.one_lt

theorem norm_routePDepthBinomialXiJet_apply_le (p : Nat.Primes) (e N : ℕ) (q : XiZeroCopy) :
    ‖routePDepthBinomialXiJet p e N q‖ ≤
      (‖finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e))‖ *
        (xiGammaEulerPrimitiveLogFrequency (p, e) - 1 / 2) *
        routePDepthRealBudget (Real.log (p : ℝ)) N
          (xiGammaEulerPrimitiveLogFrequency (p, e) - 1 / 2)) *
      ‖xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ)
        (xiSpectralPoint q)‖ := by
  have ha : 0 < xiGammaEulerPrimitiveLogFrequency (p, e) - 1 / 2 :=
    sub_pos.mpr (half_lt_xiGammaEulerPrimitiveLogFrequency (p, e))
  have haz : xiGammaEulerPrimitiveLogFrequency (p, e) - 1 / 2 ≤
      (routePPrimitiveXiLaplaceRate (p, e) q).re := by
    have hq := (xiSpectralPoint_im_mem_openHalf q).2
    simp only [routePPrimitiveXiLaplaceRate, Complex.add_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, Complex.ofReal_re]
    linarith
  rw [routePDepthBinomialXiJet_apply, norm_mul, cauchy_eq, norm_mul, norm_I, one_mul, norm_inv]
  have h := mul_le_mul_of_nonneg_left
    (norm_routePDepthLaplace_le (depth_log_prime_pos p) ha N haz)
    (norm_nonneg (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e))))
  simpa only [div_eq_mul_inv, mul_assoc] using h

/-- The literal coefficient-exact binomial residual tends strongly to zero on the entire Xi
divisor. No RH assumption is used to restrict the sampling set. -/
theorem tendsto_routePDepthBinomialXiJet (p : Nat.Primes) (e : ℕ) :
    Tendsto (routePDepthBinomialXiJet p e) atTop (nhds 0) := by
  let a := xiGammaEulerPrimitiveLogFrequency (p, e) - 1 / 2
  let A := finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e))
  let w := routePPrimitiveDeningerUpperPoint (p, e) 0
  let b : ℕ → ℝ := fun N => ‖A‖ * a * routePDepthRealBudget (Real.log (p : ℝ)) N a
  let M : ℝ := ∑' q : XiZeroCopy, ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ 2
  have ha : 0 < a := sub_pos.mpr (half_lt_xiGammaEulerPrimitiveLogFrequency (p, e))
  have hb : Tendsto b atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_routePDepthRealBudget (depth_log_prime_pos p) ha).const_mul (‖A‖ * a)
  have hsq (N : ℕ) : ‖routePDepthBinomialXiJet p e N‖ ^ 2 ≤ b N ^ 2 * M := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    calc
      _ ≤ ∑' q : XiZeroCopy, b N ^ 2 *
          ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun q => ?_)
          (HilbertSchmidt.summable_coe_sq (routePDepthBinomialXiJet p e N))
          ((XiWeilSquareSummable_cauchy (w : ℂ)).mul_left (b N ^ 2))
        calc
          _ ≤ (b N * ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖) ^ 2 := by
            apply pow_le_pow_left₀ (norm_nonneg _)
            exact norm_routePDepthBinomialXiJet_apply_le p e N q
          _ = _ := mul_pow _ _ _
      _ = b N ^ 2 * M := tsum_mul_left
  have hlim : Tendsto (fun N => b N ^ 2 * M) atTop (nhds 0) := by
    simpa using (hb.pow 2).mul_const M
  have hsqzero := squeeze_zero (fun N => sq_nonneg ‖routePDepthBinomialXiJet p e N‖) hsq hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_zero, Real.sqrt_zero, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hsqzero.sqrt

end
end RHTower
