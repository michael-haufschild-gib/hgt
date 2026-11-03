import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderHasAnExactEnergyIdentity

/-!
# Cubic and quartic lag energy inside the Gamma remainder

The reciprocal sinh and cosh factors retain positive fourth-order terms
on the half-unit interval. They give
`r(t) ≥ t³/960 + t⁴/192` for the exact retained Gamma remainder on `0<t≤1`.
Integrating keeps two positive lag energies beyond the exterior mass reserve.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory

private theorem reciprocal_hyperbolic_lower {z : ℝ} (h0 : 0 < z) (h1 : z ≤ 1/2) :
    1-z^2/6+z^4/60 ≤ z / Real.sinh z ∧
      1-z^2/2+z^4/6 ≤ 1 / Real.cosh z := by
  have hz : |z| ≤ 1 := by rw [abs_of_pos h0]; linarith only [h1]
  have hzn : |-z| ≤ 1 := by rwa [abs_neg]
  have hp := exp_le_taylor_six hz
  have hm := exp_le_taylor_six hzn
  have hm' := taylor_six_le_exp hzn
  rw [abs_neg, abs_of_pos h0] at hm hm'
  rw [abs_of_pos h0] at hp
  have hS : Real.sinh z ≤ z+z^3/6+z^5/120+z^6/617 := by
    rw [Real.sinh_eq]
    nlinarith only [hp, hm']
  have hC : Real.cosh z ≤ 1+z^2/2+z^4/24+z^6/617 := by
    rw [Real.cosh_eq]
    nlinarith only [hp, hm]
  have hz2 : z^2 ≤ 1/4 := by nlinarith only [h0, h1]
  have hz4 : z^4 ≤ 1/16 := by
    have h := pow_le_pow_left₀ (sq_nonneg z) hz2 2
    simpa only [← pow_mul] using h
  have hA0 : 0 ≤ 1-z^2/6+z^4/60 := by nlinarith only [hz2, sq_nonneg (z^2)]
  have hA1 : 1-z^2/6+z^4/60 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hz2 (sq_nonneg z)
    nlinarith only [h, sq_nonneg z]
  have hB0 : 0 ≤ 1-z^2/2+z^4/6 := by nlinarith only [hz2, sq_nonneg (z^2)]
  have hB1 : 1-z^2/2+z^4/6 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hz2 (sq_nonneg z)
    nlinarith only [h, sq_nonneg z]
  constructor
  · apply (le_div_iff₀ (Real.sinh_pos_iff.mpr h0)).mpr
    have hs := mul_le_mul_of_nonneg_left hS hA0
    have hr := mul_le_mul_of_nonneg_right hA1 (show 0 ≤ z^6/617 by positivity)
    have hpoly : (1-z^2/6+z^4/60)*(z+z^3/6+z^5/120)+z^6/617 ≤ z := by
      have he : (1-z^2/6+z^4/60)*(z+z^3/6+z^5/120)+z^6/617-z =
          z^5*(-1/360+z/617+z^2/720+z^4/7200) := by ring
      have hb : -1/360+z/617+z^2/720+z^4/7200 ≤ (0 : ℝ) := by
        linarith only [h1, hz2, hz4]
      have hn := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ z^5 by positivity) hb
      rw [← he] at hn
      linarith only [hn]
    nlinarith only [hs, hr, hpoly]
  · apply (le_div_iff₀ (Real.cosh_pos z)).mpr
    have hc := mul_le_mul_of_nonneg_left hC hB0
    have hr := mul_le_mul_of_nonneg_right hB1 (show 0 ≤ z^6/617 by positivity)
    have hpoly : (1-z^2/2+z^4/6)*(1+z^2/2+z^4/24)+z^6/617 ≤ (1 : ℝ) := by
      have he : (1-z^2/2+z^4/6)*(1+z^2/2+z^4/24)+z^6/617-1 =
          z^4*(-1/24+z^2/16+z^4/144+z^2/617) := by ring
      have hb : -1/24+z^2/16+z^4/144+z^2/617 ≤ (0 : ℝ) := by
        linarith only [hz2, hz4]
      have hn := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ z^4 by positivity) hb
      rw [← he] at hn
      linarith only [hn]
    nlinarith only [hc, hr, hpoly]

/-- The exact Gamma remainder retains positive cubic and quartic lag weights. -/
theorem retainedGammaRemainderWeight_ge_higher_lags {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    t^3/960+t^4/192 ≤ retainedGammaRemainderWeight t := by
  obtain ⟨hs, hc⟩ := reciprocal_hyperbolic_lower
    (z := t/2) (by linarith only [ht.1]) (by linarith only [ht.2])
  have hden : Real.sinh (t/2) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith only [ht.1])).ne'
  have he : archLevySinhWeight t =
      1/(2*Real.sinh (t/2))+1/(2*Real.cosh (t/2)) := by
    rw [archLevySinhWeight, exp_half_div_sinh_eq ht.1,
      archLevyDensity_eq_inv_sinh_add_inv_cosh ht.1]
    ring
  have hm := mul_le_mul_of_nonneg_left hs (le_of_lt (one_div_pos.mpr ht.1))
  have heq : 1/t * ((t/2)/Real.sinh (t/2)) = 1/(2*Real.sinh (t/2)) := by
    field_simp [ht.1.ne', hden]
    <;> ring
  rw [heq] at hm
  unfold retainedGammaRemainderWeight
  rw [he]
  have hp : 1/t*(1-(t/2)^2/6+(t/2)^4/60) + (1-(t/2)^2/2+(t/2)^4/6)/2 =
      1/t+1/2-t/24-t^2/16+t^3/960+t^4/192 := by
    field_simp [ht.1.ne']
    <;> ring
  linarith only [hm, hc, hp]

/-- Higher lag energies are paid by the discarded local Gamma term itself. -/
theorem retainedGammaRemainder_ge_higher_lags {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) :
    (∫ t in Ioc (0 : ℝ) 1, t^3*((∫ x, F x^2)-autocorr F t))/960 +
      (∫ t in Ioc (0 : ℝ) 1, t^4*((∫ x, F x^2)-autocorr F t))/192 ≤
        ∫ t in Ioc (0 : ℝ) 1, retainedGammaRemainderWeight t *
          ((∫ x, F x^2)-autocorr F t) := by
  have hd : Continuous (fun t => (∫ x, F x^2)-autocorr F t) :=
    continuous_const.sub (_root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs)
  have hi3 : IntegrableOn (fun t => t^3*((∫ x, F x^2)-autocorr F t)) (Ioc (0 : ℝ) 1) :=
    ((continuous_pow 3).mul hd).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi4 : IntegrableOn (fun t => t^4*((∫ x, F x^2)-autocorr F t)) (Ioc (0 : ℝ) 1) :=
    ((continuous_pow 4).mul hd).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiR := (retainedGammaRemainder_integrable_nonneg hF hcs).1
  simp only [autocorr_zero_eq] at hiR
  rw [← integral_div, ← integral_div, ← integral_add (hi3.div_const 960) (hi4.div_const 192)]
  apply setIntegral_mono_on ((hi3.div_const 960).add (hi4.div_const 192)) hiR measurableSet_Ioc
  intro t ht
  have hn : 0 ≤ (∫ x, F x^2)-autocorr F t := by
    have h := (le_abs_self (autocorr F t)).trans (abs_autocorr_le_zero hcs hF.continuous t)
    simpa only [autocorr_zero_eq] using sub_nonneg.mpr h
  have h := mul_le_mul_of_nonneg_right (retainedGammaRemainderWeight_ge_higher_lags ht) hn
  nlinarith only [h]

/-- The odd unit-window form retains both higher lag energies as well as its exterior reserve. -/
theorem weilQuad_ge_retainedOddGamma_add_higher_lags {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-(1/2 : ℝ)) (1/2))
    (ho : ∀ x, F (-x) = -F x) :
    retainedOddGammaLowerForm F + (∫ x, F x^2)/64 +
      (∫ t in Ioc (0 : ℝ) 1, t^3*((∫ x, F x^2)-autocorr F t))/960 +
      (∫ t in Ioc (0 : ℝ) 1, t^4*((∫ x, F x^2)-autocorr F t))/192 ≤ weilQuad F := by
  have hcs : HasCompactSupport F := HasCompactSupport.intro isCompact_Icc
    (fun x hx => image_eq_zero_of_notMem_tsupport fun ht => hx (hs ht))
  have hR := retainedGammaRemainder_ge_higher_lags hF hcs
  have hmass : 0 ≤ ∫ x, F x^2 := integral_nonneg fun x => sq_nonneg (F x)
  have htail : (1/128 : ℝ) ≤ retainedGammaTailReserve := gamma_tail_one_reserve.le
  have hp := mul_le_mul_of_nonneg_right htail hmass
  rw [weilQuad_eq_retainedOddGamma_add_remainder hF hs ho]
  linarith only [hR, hp]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedGammaRemainderWeight_ge_higher_lags
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedGammaRemainder_ge_higher_lags
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_ge_retainedOddGamma_add_higher_lags
