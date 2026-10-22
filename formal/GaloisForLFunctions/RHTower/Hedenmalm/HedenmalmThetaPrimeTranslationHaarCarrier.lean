import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPrimeTranslationFixedFibre
import GaloisForLFunctions.HTGeometry.TranslationModulus

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmIntervalAnomaly

namespace HedenmalmThetaSource

theorem intervalMass_add_eq_shiftIntegral
    (S : PositiveDensitySource) {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    intervalMass S x (x + a) = ∫ s in Ioc (0 : ℝ) a, S.k (x + s) := by
  rw [intervalMass, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le ha,
    intervalIntegral.integral_comp_add_left]
  simp

theorem continuous_intervalMass_add
    (S : PositiveDensitySource) {a : ℝ} (ha : 0 ≤ a) :
    Continuous (fun x : ℝ => intervalMass S x (x + a)) := by
  have hfun : (fun x : ℝ => intervalMass S x (x + a)) = fun x =>
      S.mass * (S.cdfFun (x + a) - S.cdfFun x) := by
    funext x
    exact (mass_mul_cdfFun_sub S (by linarith)).symm
  rw [hfun]
  have hcdf : Continuous S.cdfFun := S.continuous_cdfFun
  fun_prop

theorem integrable_intervalMass_add
    (S : PositiveDensitySource) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun x : ℝ => intervalMass S x (x + a)) volume := by
  have hjoint := integrable_uncurry_norm_shear S.k S.integrable_k a
  have houter : Integrable
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) a, ‖S.k (x + s)‖) volume :=
    hjoint.swap.integral_prod_left
  refine houter.congr ?_
  filter_upwards with x
  rw [intervalMass_add_eq_shiftIntegral S ha]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  rw [Real.norm_eq_abs, abs_of_pos (S.pos_k _)]

theorem integral_intervalMass_add
    (S : PositiveDensitySource) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : ℝ, intervalMass S x (x + a)) = a * S.mass := by
  have hjoint := integrable_uncurry_norm_shear S.k S.integrable_k a
  have hswap := integral_integral_swap hjoint
  have hshear := integral_integral_shear_eq S.k ha
  have hleft :
      (∫ s in Ioc (0 : ℝ) a, ∫ x : ℝ, ‖S.k (x + s)‖) = a * S.mass := by
    rw [hshear]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      change ‖S.k x‖ = S.k x
      rw [Real.norm_eq_abs, abs_of_pos (S.pos_k x)])
  calc
    (∫ x : ℝ, intervalMass S x (x + a)) =
        ∫ x : ℝ, ∫ s in Ioc (0 : ℝ) a, ‖S.k (x + s)‖ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [intervalMass_add_eq_shiftIntegral S ha]
      refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
      rw [Real.norm_eq_abs, abs_of_pos (S.pos_k _)]
    _ = ∫ s in Ioc (0 : ℝ) a, ∫ x : ℝ, ‖S.k (x + s)‖ := hswap.symm
    _ = a * S.mass := hleft

theorem intervalMass_add_nonneg
    (S : PositiveDensitySource) {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    0 ≤ intervalMass S x (x + a) := by
  rw [← mass_mul_cdfFun_sub S (by linarith)]
  exact mul_nonneg S.mass_pos.le (sub_nonneg.mpr (S.strictMono_cdfFun.monotone (by linarith)))

theorem intervalMass_add_le_mass
    (S : PositiveDensitySource) {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    intervalMass S x (x + a) ≤ S.mass := by
  rw [← mass_mul_cdfFun_sub S (by linarith)]
  have hFx := S.cdfFun_mem_Ioo x
  have hFxa := S.cdfFun_mem_Ioo (x + a)
  have hdiff : S.cdfFun (x + a) - S.cdfFun x ≤ 1 := by
    linarith [hFx.1, hFxa.2]
  simpa using mul_le_mul_of_nonneg_left hdiff S.mass_pos.le

theorem integrable_sq_intervalMass_add
    (S : PositiveDensitySource) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun x : ℝ => intervalMass S x (x + a) ^ 2) volume := by
  have hW := integrable_intervalMass_add S ha
  refine Integrable.mono' (hW.const_mul S.mass)
    ((continuous_intervalMass_add S ha).pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  have h0 := intervalMass_add_nonneg S ha x
  have hM := intervalMass_add_le_mass S ha x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- Every positive-integer anomaly is an ordinary Haar-`L²(ℝ)` vector for every positive
density source, even though P-G104 proves that the theta anomaly is excluded from the reciprocal
source-weighted fibre. -/
theorem integerAnomaly_memLp_haar
    (S : PositiveDensitySource) {n : ℕ} (hn : 1 ≤ n) :
    MemLp (integerAnomaly S n) 2 (volume : Measure ℝ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hc : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_pos_of_pos hnpos _).le
  have hsq := integrable_sq_intervalMass_add S hlog
  have hcont : Continuous (fun x : ℝ => integerAnomaly S n x) := by
    have hfun : (fun x : ℝ => integerAnomaly S n x) = fun x =>
        Complex.I * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) *
          intervalMass S x (x + Real.log n) : ℝ)) : ℂ) := by
      funext x
      exact integerAnomaly_eq_intervalMass S hn x
    rw [hfun]
    have hwindow := continuous_intervalMass_add S hlog
    fun_prop
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  refine (hsq.const_mul (((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)).congr ?_
  filter_upwards with x
  rw [integerAnomaly_eq_intervalMass S hn, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hc (intervalMass_add_nonneg S hlog x))]
  ring

theorem integrable_integerAnomaly_haar
    (S : PositiveDensitySource) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (integerAnomaly S n) (volume : Measure ℝ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hwindow := integrable_intervalMass_add S hlog
  have hfun : (fun x : ℝ => integerAnomaly S n x) = fun x =>
      Complex.I * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (intervalMass S x (x + Real.log n) : ℂ) := by
    funext x
    rw [integerAnomaly_eq_intervalMass S hn]
    push_cast
    ring
  change Integrable (fun x : ℝ => integerAnomaly S n x) volume
  rw [hfun]
  exact hwindow.ofReal.const_mul _

/-- Exact Haar `L¹` mass of the prime anomaly.  Completion changes carrier, not arithmetic
normalization: interval width is literally `log n`. -/
theorem integral_norm_integerAnomaly_haar
    (S : PositiveDensitySource) {n : ℕ} (hn : 1 ≤ n) :
    (∫ x : ℝ, ‖integerAnomaly S n x‖) =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n * S.mass := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hc : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_pos_of_pos hnpos _).le
  have hpoint : (fun x : ℝ => ‖integerAnomaly S n x‖) = fun x =>
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * intervalMass S x (x + Real.log n) := by
    funext x
    rw [integerAnomaly_eq_intervalMass S hn, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hc (intervalMass_add_nonneg S hlog x))]
  rw [hpoint, integral_const_mul, integral_intervalMass_add S hlog]
  ring

/-- Sharp carrier phase transition for every nontrivial integer translation: the theta anomaly is
an honest Haar-`L²(ℝ)` vector, but it is excluded from the fixed reciprocal-source Hilbert fibre.
Thus the obstruction in P-G104 is caused by the carrier, not by a failure of square-integrability
of the arithmetic anomaly itself. -/
theorem thetaIntegerAnomaly_haar_memLp_and_fixedSource_not_memLp
    {n : ℕ} (hn : 2 ≤ n) :
    MemLp (integerAnomaly thetaSource n) 2 (volume : Measure ℝ) ∧
      ¬ MemLp (integerAnomaly thetaSource n) 2
        (volume.withDensity (realDensity (sourceWeight thetaSource))) := by
  exact ⟨integerAnomaly_memLp_haar thetaSource (hn.trans' one_le_two),
    integerAnomaly_not_memLp_fixedSource hn⟩

end HedenmalmThetaSource
end
end RHTower
