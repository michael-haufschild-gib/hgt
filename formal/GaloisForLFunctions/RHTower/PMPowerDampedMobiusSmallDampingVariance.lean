import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCovarianceCancellation

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
noncomputable section
namespace RHTower

theorem pm_prod_one_sub_ge {ι : Type*} (s : Finset ι) (d : ι → ℝ)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) :
    1 - ∑ i ∈ s, d i ≤ ∏ i ∈ s, (1-d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hd1 i))
    have hn := mul_nonneg (hd0 i) (Finset.sum_nonneg (s := s) fun j hj => hd0 j)
    nlinarith

theorem pm_hasProd_one_sub_bounds {ι : Type*} {d : ι → ℝ} {C : ℝ}
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) (hs : Summable d)
    (hp : HasProd (fun i => 1-d i) C) : 1-(∑' i, d i) ≤ C ∧ C ≤ 1 := by
  have ht : Tendsto (fun s : Finset ι => ∏ i ∈ s, (1-d i)) atTop (𝓝 C) := hp
  constructor
  · apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    apply Filter.Eventually.of_forall
    intro s
    exact (sub_le_sub_left (hs.sum_le_tsum s (fun i hi => hd0 i)) 1).trans
      (pm_prod_one_sub_ge s d hd0 hd1)
  · apply le_of_tendsto_of_tendsto ht tendsto_const_nhds
    apply Filter.Eventually.of_forall
    intro s
    exact Finset.prod_le_one (fun i hi => sub_nonneg.mpr (hd1 i))
      (fun i hi => by linarith [hd0 i])

def pmPowerDampedVariancePrimeDeficit (ε : ℝ) (p : Nat.Primes) : ℝ :=
  (((p : ℝ)^(-ε) - ((p : ℝ)^(-ε))^2) / ((p : ℝ)-(p : ℝ)^(-ε)))^2

theorem pmPowerDampedVariancePrimeDeficit_bounds {ε : ℝ} (hε : 0 ≤ ε) (p : Nat.Primes) :
    0 ≤ pmPowerDampedVariancePrimeDeficit ε p ∧
      pmPowerDampedVariancePrimeDeficit ε p ≤ 1 ∧
        pmPowerDampedVariancePrimeDeficit ε p ≤ 4/(p : ℝ)^2 := by
  let t := (p : ℝ)^(-ε)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hp0.le _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr hε)
  have hn0 : 0 ≤ t-t^2 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hn1 : t-t^2 ≤ 1 := by nlinarith [sq_nonneg t]
  have hd1 : (1 : ℝ) ≤ (p : ℝ)-t := by linarith
  have hd0 : 0 < (p : ℝ)-t := by linarith
  have hq0 : 0 ≤ (t-t^2)/((p : ℝ)-t) := div_nonneg hn0 hd0.le
  have hq1 : (t-t^2)/((p : ℝ)-t) ≤ 1 := (div_le_one hd0).mpr (by linarith)
  have hq2 : (t-t^2)/((p : ℝ)-t) ≤ 2/(p : ℝ) := by
    calc
      _ ≤ 1/((p : ℝ)-t) := div_le_div_of_nonneg_right hn1 hd0.le
      _ ≤ _ := (div_le_div_iff₀ hd0 hp0).mpr (by nlinarith)
  change 0 ≤ ((t-t^2)/((p : ℝ)-t))^2 ∧
    ((t-t^2)/((p : ℝ)-t))^2 ≤ 1 ∧ ((t-t^2)/((p : ℝ)-t))^2 ≤ 4/(p : ℝ)^2
  refine ⟨sq_nonneg _, by nlinarith, ?_⟩
  calc
    _ ≤ (2/(p : ℝ))^2 := pow_le_pow_left₀ hq0 hq2 2
    _ = _ := by rw [div_pow]; norm_num

theorem summable_pm_variance_prime_majorant :
    Summable (fun p : Nat.Primes => 4/(p : ℝ)^2) := by
  have hn : Summable (fun n : ℕ => 1/(n : ℝ)^2) := by
    simpa only [Real.rpow_two] using
      (Real.summable_one_div_nat_rpow (p := (2 : ℝ))).mpr (by norm_num)
  convert! (hn.subtype Nat.Prime).mul_left (4 : ℝ) using 1
  funext p
  simp only [Function.comp_def, mul_one_div]

theorem summable_pmPowerDampedVariancePrimeDeficit {ε : ℝ} (hε : 0 ≤ ε) :
    Summable (pmPowerDampedVariancePrimeDeficit ε) :=
  Summable.of_nonneg_of_le (fun p => (pmPowerDampedVariancePrimeDeficit_bounds hε p).1)
    (fun p => (pmPowerDampedVariancePrimeDeficit_bounds hε p).2.2)
    summable_pm_variance_prime_majorant

theorem tendsto_pmPowerDampedVariancePrimeDeficit (p : Nat.Primes) :
    Tendsto (fun ε : ℝ => pmPowerDampedVariancePrimeDeficit ε p) (𝓝[>] 0) (𝓝 0) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hc : Continuous (fun ε : ℝ => (p : ℝ)^(-ε)) :=
    (Real.continuous_const_rpow hp0).comp continuous_neg
  have ht : Tendsto (fun ε : ℝ => (p : ℝ)^(-ε)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := ((ht.sub (ht.pow 2)).div (tendsto_const_nhds.sub ht)
    (sub_ne_zero.mpr (ne_of_gt hp1))).pow 2
  simpa [pmPowerDampedVariancePrimeDeficit] using h

theorem tendsto_tsum_pmPowerDampedVariancePrimeDeficit :
    Tendsto (fun ε : ℝ => ∑' p : Nat.Primes, pmPowerDampedVariancePrimeDeficit ε p)
      (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence summable_pm_variance_prime_majorant
    tendsto_pmPowerDampedVariancePrimeDeficit (show ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ p : Nat.Primes, ‖pmPowerDampedVariancePrimeDeficit ε p‖ ≤ 4/(p : ℝ)^2 from by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        intro p
        have h := pmPowerDampedVariancePrimeDeficit_bounds (show 0 ≤ ε from le_of_lt hε) p
        rw [Real.norm_eq_abs, abs_of_nonneg h.1]
        exact h.2.2)
  simpa using h

theorem pmPowerDampedDivisorDensity_re_ne_zero {ε : ℝ} (hε : 0 < ε) :
    (pmPowerDampedDivisorDensity ε).re ≠ 0 := by
  intro hz
  apply pmPowerDampedDivisorDensity_ne_zero hε
  rw [pmPowerDampedDivisorDensity_eq_ofReal_re hε, hz]
  simp

theorem pm_prime_rpow_double (ε : ℝ) (p : Nat.Primes) :
    (p : ℝ)^(-(2*ε)) = ((p : ℝ)^(-ε))^2 := by
  rw [← Real.rpow_natCast ((p : ℝ)^(-ε)) 2, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p)]
  congr 1
  ring

def pmPowerDampedVarianceCorrection (ε : ℝ) : ℝ :=
  pmPowerDampedSecondDensity ε * (pmPowerDampedDivisorDensity (2*ε)).re /
    (pmPowerDampedDivisorDensity ε).re ^ 2

theorem pmPowerDampedVarianceCorrection_hasProd {ε : ℝ} (hε : 0 < ε) :
    HasProd (fun p : Nat.Primes => 1-pmPowerDampedVariancePrimeDeficit ε p)
      (pmPowerDampedVarianceCorrection ε) := by
  have hnum : Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S,
      (1-pmPowerDampedSecondWeight ε p/(p : ℝ)) * (1-(p : ℝ)^(-(2*ε))/(p : ℝ)))
      atTop (𝓝 (pmPowerDampedSecondDensity ε * (pmPowerDampedDivisorDensity (2*ε)).re)) :=
    (pmPowerDampedSecondDensity_hasProd hε).mul
      (pmPowerDampedDivisorDensity_hasProd_real (by linarith : 0 < 2*ε))
  have hden : Tendsto (fun S : Finset Nat.Primes =>
      ∏ p ∈ S, (1-(p : ℝ)^(-ε)/(p : ℝ))^2) atTop
      (𝓝 ((pmPowerDampedDivisorDensity ε).re ^ 2)) :=
    (pmPowerDampedDivisorDensity_hasProd_real hε).pow 2
  have h := hnum.div hden (pow_ne_zero 2 (pmPowerDampedDivisorDensity_re_ne_zero hε))
  change Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S,
    (1-pmPowerDampedVariancePrimeDeficit ε p)) atTop (𝓝 (pmPowerDampedVarianceCorrection ε))
  apply h.congr
  intro S
  dsimp only [Pi.div_apply]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [pm_prime_rpow_double]
  let t := (p : ℝ)^(-ε)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hd : (p : ℝ)-t ≠ 0 := by linarith
  have hf : 1-t/(p : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr ((div_lt_one hp0).mpr (by linarith)))
  change ((1-(2*t-t^2)/(p : ℝ))*(1-t^2/(p : ℝ)))/(1-t/(p : ℝ))^2 =
    1-((t-t^2)/((p : ℝ)-t))^2
  field_simp [hp0.ne', hd, hf]
  ring

theorem pmPowerDampedVarianceCorrection_bounds {ε : ℝ} (hε : 0 < ε) :
    1-(∑' p : Nat.Primes, pmPowerDampedVariancePrimeDeficit ε p) ≤
        pmPowerDampedVarianceCorrection ε ∧ pmPowerDampedVarianceCorrection ε ≤ 1 :=
  pm_hasProd_one_sub_bounds
    (fun p => (pmPowerDampedVariancePrimeDeficit_bounds hε.le p).1)
    (fun p => (pmPowerDampedVariancePrimeDeficit_bounds hε.le p).2.1)
    (summable_pmPowerDampedVariancePrimeDeficit hε.le)
    (pmPowerDampedVarianceCorrection_hasProd hε)

theorem tendsto_pmPowerDampedVarianceCorrection :
    Tendsto pmPowerDampedVarianceCorrection (𝓝[>] 0) (𝓝 1) := by
  have hlo : Tendsto
      (fun ε : ℝ => 1-(∑' p : Nat.Primes, pmPowerDampedVariancePrimeDeficit ε p))
      (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub tendsto_tsum_pmPowerDampedVariancePrimeDeficit
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (pmPowerDampedVarianceCorrection_bounds hε).1
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (pmPowerDampedVarianceCorrection_bounds hε).2

theorem tendsto_pmPowerDampedDivisorDensity_re_div_parameter :
    Tendsto (fun ε : ℝ => (pmPowerDampedDivisorDensity ε).re/ε) (𝓝[>] 0) (𝓝 1) := by
  have hz : Tendsto (fun ε : ℝ => 1+(ε : ℂ)) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    have hc : Continuous (fun ε : ℝ => 1+(ε : ℂ)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hu := zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hz
  rw [zetaResidueUnit_one] at hu
  have hunit : Tendsto (fun ε : ℝ => 1/zetaResidueUnit (1+(ε : ℂ)))
      (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    convert! (tendsto_const_nhds (x := (1 : ℂ))).div hu one_ne_zero using 1
    simp only [div_one]
  have hc : Tendsto (fun ε : ℝ => pmPowerDampedDivisorDensity ε/(ε : ℂ))
      (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    apply hunit.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have he : 1+(ε : ℂ) ≠ 1 := by
      intro hh
      have hh0 : (ε : ℂ) = 0 := by linear_combination hh
      exact (ne_of_gt hε) (Complex.ofReal_eq_zero.mp hh0)
    have heq : zetaResidueUnit (1+(ε : ℂ)) = (ε : ℂ)*riemannZeta (1+(ε : ℂ)) := by
      rw [zetaResidueUnit, Function.update_of_ne he]
      congr 1
      ring
    rw [heq, pmPowerDampedDivisorDensity, div_div]
    congr 1
    ring
  have hr : Tendsto (fun ε : ℝ => (pmPowerDampedDivisorDensity ε/(ε : ℂ)).re)
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Complex.one_re] using (Complex.continuous_re.tendsto _).comp hc
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [pmPowerDampedDivisorDensity_eq_ofReal_re hε, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [Complex.ofReal_re]

theorem tendsto_pmPowerDampedSecondDensity_div_parameter :
    Tendsto (fun ε : ℝ => pmPowerDampedSecondDensity ε/ε) (𝓝[>] 0) (𝓝 (1/2 : ℝ)) := by
  have hd : Tendsto (fun ε : ℝ => 2*ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun ε : ℝ => 2*ε) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < 2*ε
      exact mul_pos (by norm_num) (show 0 < ε from hε)
  have hα := tendsto_pmPowerDampedDivisorDensity_re_div_parameter
  have hα2 := hα.comp hd
  have h := (tendsto_pmPowerDampedVarianceCorrection.mul (hα.pow 2)).div
    (hα2.const_mul 2) (by norm_num : (2 : ℝ)*1 ≠ 0)
  have hl : Tendsto (fun ε : ℝ => pmPowerDampedVarianceCorrection ε *
      ((pmPowerDampedDivisorDensity ε).re/ε)^2 /
        (2*((pmPowerDampedDivisorDensity (2*ε)).re/(2*ε)))) (𝓝[>] 0) (𝓝 (1/2 : ℝ)) := by
    convert! h using 1
    simp only [one_pow, mul_one]
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hpos : 0 < ε := hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have ha := pmPowerDampedDivisorDensity_re_ne_zero hε
  have ha2 := pmPowerDampedDivisorDensity_re_ne_zero (by linarith : 0 < 2*ε)
  dsimp only [pmPowerDampedVarianceCorrection]
  field_simp

theorem tendsto_pmPowerDampedDivisorVariance_div_parameter :
    Tendsto (fun ε : ℝ => pmPowerDampedDivisorVariance ε/ε) (𝓝[>] 0) (𝓝 (1/2 : ℝ)) := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun ε : ℝ => ((pmPowerDampedDivisorDensity ε).re/ε)^2*ε)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_pmPowerDampedDivisorDensity_re_div_parameter.pow 2).mul he
  have h := tendsto_pmPowerDampedSecondDensity_div_parameter.sub hz
  simpa only [sub_zero] using h.congr' (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := ne_of_gt hε
    dsimp only [pmPowerDampedDivisorVariance]
    field_simp)

end RHTower
