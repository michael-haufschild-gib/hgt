import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderHasAnExactEnergyIdentity

/-!
# Cubic and quartic lag energy inside the Gamma remainder

The reciprocal sinh and cosh factors retain positive fourth-order terms
on the half-unit interval. They give
`r(t) ≥ t³/960 + t⁴/192` for the exact retained Gamma remainder on `0<t≤1`.
Integrating keeps two positive lag energies beyond the exterior mass reserve.
Five exterior Laplace modes strengthen that reserve. Odd correlation cancellation
also converts the local terms into an explicit mass and first-moment credit.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory BiScaleUncertainty LatticeSectionTheory SpacingScaleHarmonicAnalysis

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
    norm_num only [← pow_mul] at h
    exact h
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
  rw [heq] at hm
  unfold retainedGammaRemainderWeight
  rw [he]
  have hp : 1/t*(1-(t/2)^2/6+(t/2)^4/60) + (1-(t/2)^2/2+(t/2)^4/6)/2 =
      1/t+1/2-t/24-t^2/16+t^3/960+t^4/192 := by
    field_simp [ht.1.ne']
    ring
  have hcHalf := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 1/2)
  have hcEq : (1/2 : ℝ)*(1/Real.cosh (t/2)) = 1/(2*Real.cosh (t/2)) := by ring
  rw [hcEq] at hcHalf
  linarith only [hm, hcHalf, hp]

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
  dsimp only [Pi.add_apply]
  have hn : 0 ≤ (∫ x, F x^2)-autocorr F t := by
    have h := (le_abs_self (autocorr F t)).trans (abs_autocorr_le_zero hcs hF.continuous t)
    simpa only [autocorr_zero_eq] using sub_nonneg.mpr h
  have h := mul_le_mul_of_nonneg_right (retainedGammaRemainderWeight_ge_higher_lags ht) hn
  nlinarith only [h]


/-- Odd correlation cancellation converts higher lags into mass and first-moment reserves. -/
theorem retainedGammaRemainder_ge_moment_reserve {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : tsupport F ⊆ Icc (-(1/2 : ℝ)) (1/2)) (ho : ∀ x, F (-x) = -F x) :
    (17/23040)*(∫ x, F x^2)+(13/3840)*(∫ x, x*F x)^2 ≤
      ∫ t in Ioc (0 : ℝ) 1, retainedGammaRemainderWeight t*((∫ x, F x^2)-autocorr F t) := by
  let E := ∫ x, F x^2
  let D := fun t => E-autocorr F t
  have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs
  have hd : Continuous D := continuous_const.sub hc
  have hiD : IntegrableOn D (Ioc (0 : ℝ) 1) :=
    hd.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi2 : IntegrableOn (fun t => t^2*D t) (Ioc (0 : ℝ) 1) :=
    ((continuous_pow 2).mul hd).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiR := (retainedGammaRemainder_integrable_nonneg hF hcs).1
  simp only [autocorr_zero_eq] at hiR
  have hzero := LatticeSectionTheory.odd_autocorr_integral_zero ⟨hF, hcs⟩ hs ho
  norm_num at hzero
  have hD : (∫ t in Ioc (0 : ℝ) 1, D t) = E := by
    change (∫ t in Ioc (0 : ℝ) 1, E-autocorr F t) = E
    rw [integral_sub (f := fun _ : ℝ => E) (g := autocorr F)
      (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self), hzero, sub_zero, setIntegral_const]
    norm_num
  have hD2 := LatticeSectionTheory.unit_odd_jump_second_moment hF hcs hs ho
  simp only [autocorr_zero_eq] at hD2
  change (∫ t in Ioc (0 : ℝ) 1, t^2*D t) = E/3+(∫ x, x*F x)^2 at hD2
  have hiP : IntegrableOn (fun t => (13/3840)*(t^2*D t)-(1/2560)*D t) (Ioc (0 : ℝ) 1) :=
    (hi2.const_mul _).sub (hiD.const_mul _)
  have h := setIntegral_mono_on hiP hiR measurableSet_Ioc (fun t ht => by
    have hn : 0 ≤ D t := by
      have hb := (le_abs_self (autocorr F t)).trans (abs_autocorr_le_zero hcs hF.continuous t)
      simpa only [autocorr_zero_eq] using sub_nonneg.mpr hb
    have hpoly : (13/3840)*t^2-1/2560 ≤ t^3/960+t^4/192 := by
      have hsq : 0 ≤ (t-1/2)^2*(t+1/4)/960+(t^2-1/4)^2/192 := by
        have ht0 := ht.1
        positivity
      nlinarith only [hsq]
    have hp := mul_le_mul_of_nonneg_right
      (hpoly.trans (retainedGammaRemainderWeight_ge_higher_lags ht)) hn
    dsimp only [D, E] at hp ⊢
    nlinarith only [hp])
  rw [integral_sub (hi2.const_mul _) (hiD.const_mul _),
    integral_const_mul, integral_const_mul, hD2, hD] at h
  dsimp only [E, D] at h
  linarith only [h]

private theorem exp_neg_half_lower : (60653/100000 : ℝ) ≤ Real.exp (-(1/2 : ℝ)) := by
  have h := exp_le_taylor_seven (x := (1/2 : ℝ)) (by norm_num)
  norm_num at h
  have hu : Real.exp (1/2 : ℝ) ≤ 100000/60653 := by linarith only [h]
  rw [Real.exp_neg, ← one_div]
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  linarith only [hu]

private theorem gamma_five_modes_le {t : ℝ} (ht : 0 < t) :
    Real.exp (-(1/2 : ℝ)*t) + Real.exp (-(5/2 : ℝ)*t) +
      Real.exp (-(9/2 : ℝ)*t) + Real.exp (-(13/2 : ℝ)*t) +
      Real.exp (-(17/2 : ℝ)*t) ≤ archLevyDensity t := by
  have h := Summable.sum_le_tsum (Finset.range 5)
    (fun n _ => (Real.exp_pos (-(2*(n : ℝ)+1/2)*t)).le)
    (hasSum_archLevyDensity ht).summable
  rw [← _root_.RHTower.ArchimedeanAnomaly.archLevyDensity_eq_tsum ht] at h
  norm_num [Finset.sum_range_succ] at h
  simpa only [neg_mul] using h

/-- Five positive Laplace modes retain an explicit lower bound for the exterior Gamma tail. -/
theorem gamma_tail_one_five_modes :
    2*(Real.exp (-(1/2 : ℝ)) + Real.exp (-(1/2 : ℝ))^5/5 +
      Real.exp (-(1/2 : ℝ))^9/9 + Real.exp (-(1/2 : ℝ))^13/13 +
      Real.exp (-(1/2 : ℝ))^17/17) ≤ archLevyAntideriv 1 := by
  have h0 := integrableOn_exp_mul_Ioi (by norm_num : -(1/2 : ℝ) < 0) 1
  have h1 := integrableOn_exp_mul_Ioi (by norm_num : -(5/2 : ℝ) < 0) 1
  have h2 := integrableOn_exp_mul_Ioi (by norm_num : -(9/2 : ℝ) < 0) 1
  have h3 := integrableOn_exp_mul_Ioi (by norm_num : -(13/2 : ℝ) < 0) 1
  have h4 := integrableOn_exp_mul_Ioi (by norm_num : -(17/2 : ℝ) < 0) 1
  have hw := WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi
    (by norm_num : (0 : ℝ) < 1)
  have h := setIntegral_mono_on ((((h0.add h1).add h2).add h3).add h4) hw measurableSet_Ioi
    (fun t ht => gamma_five_modes_le (lt_trans zero_lt_one ht))
  simp only [Pi.add_apply] at h
  rw [integral_add
      (f := fun x : ℝ => Real.exp (-(1/2 : ℝ)*x)+Real.exp (-(5/2 : ℝ)*x)+
        Real.exp (-(9/2 : ℝ)*x)+Real.exp (-(13/2 : ℝ)*x))
      (g := fun x : ℝ => Real.exp (-(17/2 : ℝ)*x)) (((h0.add h1).add h2).add h3) h4,
    integral_add
      (f := fun x : ℝ => Real.exp (-(1/2 : ℝ)*x)+Real.exp (-(5/2 : ℝ)*x)+Real.exp (-(9/2 : ℝ)*x))
      (g := fun x : ℝ => Real.exp (-(13/2 : ℝ)*x)) ((h0.add h1).add h2) h3,
    integral_add
      (f := fun x : ℝ => Real.exp (-(1/2 : ℝ)*x)+Real.exp (-(5/2 : ℝ)*x))
      (g := fun x : ℝ => Real.exp (-(9/2 : ℝ)*x)) (h0.add h1) h2,
    integral_add (f := fun x : ℝ => Real.exp (-(1/2 : ℝ)*x))
      (g := fun x : ℝ => Real.exp (-(5/2 : ℝ)*x)) h0 h1,
    integral_exp_mul_Ioi (by norm_num : -(1/2 : ℝ) < 0),
    integral_exp_mul_Ioi (by norm_num : -(5/2 : ℝ) < 0),
    integral_exp_mul_Ioi (by norm_num : -(9/2 : ℝ) < 0),
    integral_exp_mul_Ioi (by norm_num : -(13/2 : ℝ) < 0),
    integral_exp_mul_Ioi (by norm_num : -(17/2 : ℝ) < 0),
    WeilLevyCoshCrossover.integral_archLevyDensity_Ioi (by norm_num : (0 : ℝ) < 1)] at h
  have he5 : Real.exp (-(5/2 : ℝ)) = Real.exp (-(1/2 : ℝ))^5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he9 : Real.exp (-(9/2 : ℝ)) = Real.exp (-(1/2 : ℝ))^9 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he13 : Real.exp (-(13/2 : ℝ)) = Real.exp (-(1/2 : ℝ))^13 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he17 : Real.exp (-(17/2 : ℝ)) = Real.exp (-(1/2 : ℝ))^17 := by
    rw [← Real.exp_nat_mul]; norm_num
  simp only [mul_one, he5, he9, he13, he17] at h
  linarith only [h]

/-- Five exterior modes strengthen the mass reserve beyond the first three-mode bound. -/
theorem gamma_tail_one_stronger_reserve : (193/20000 : ℝ) < retainedGammaTailReserve := by
  have he := exp_neg_half_lower
  have he5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 60653/100000) he 5
  have he9 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 60653/100000) he 9
  have he13 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 60653/100000) he 13
  have he17 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 60653/100000) he 17
  have hc : Real.log 2 + Real.pi/4 - 1/4 + 1/96 + 193/20000 <
      2*((60653/100000 : ℝ)+(60653/100000 : ℝ)^5/5+
        (60653/100000 : ℝ)^9/9+(60653/100000 : ℝ)^13/13+
        (60653/100000 : ℝ)^17/17) := by
    have hl := Real.log_two_lt_d9
    have hp := Real.pi_lt_d6
    norm_num at hl hp ⊢
    linarith only [hl, hp]
  unfold retainedGammaTailReserve
  linarith only [gamma_tail_one_five_modes, hc, he, he5, he9, he13, he17]

/-- The odd unit-window form retains both higher lag energies as well as its exterior reserve. -/
theorem weilQuad_ge_retainedOddGamma_add_higher_lags {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-(1/2 : ℝ)) (1/2))
    (ho : ∀ x, F (-x) = -F x) :
    retainedOddGammaLowerForm F + (193/10000)*(∫ x, F x^2) +
      (∫ t in Ioc (0 : ℝ) 1, t^3*((∫ x, F x^2)-autocorr F t))/960 +
      (∫ t in Ioc (0 : ℝ) 1, t^4*((∫ x, F x^2)-autocorr F t))/192 ≤ weilQuad F := by
  have hcs : HasCompactSupport F := HasCompactSupport.intro isCompact_Icc
    (fun x hx => image_eq_zero_of_notMem_tsupport fun ht => hx (hs ht))
  have hR := retainedGammaRemainder_ge_higher_lags hF hcs
  have hmass : 0 ≤ ∫ x, F x^2 := integral_nonneg fun x => sq_nonneg (F x)
  have htail : (193/20000 : ℝ) ≤ retainedGammaTailReserve := gamma_tail_one_stronger_reserve.le
  have hp := mul_le_mul_of_nonneg_right htail hmass
  rw [weilQuad_eq_retainedOddGamma_add_remainder hF hs ho]
  linarith only [hR, hp]


/-- The first two odd correlation identities supply a uniform Gamma reserve and a moment credit. -/
theorem weilQuad_ge_retainedOddGamma_add_moment_reserve {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-(1/2 : ℝ)) (1/2))
    (ho : ∀ x, F (-x) = -F x) :
    retainedOddGammaLowerForm F+(193/10000+17/23040)*(∫ x, F x^2)+
      (13/3840)*(∫ x, x*F x)^2 ≤ weilQuad F := by
  have hcs : HasCompactSupport F := HasCompactSupport.intro isCompact_Icc
    (fun x hx => image_eq_zero_of_notMem_tsupport fun ht => hx (hs ht))
  have hR := retainedGammaRemainder_ge_moment_reserve hF hcs hs ho
  have hmass : 0 ≤ ∫ x, F x^2 := integral_nonneg fun x => sq_nonneg (F x)
  have hp := mul_le_mul_of_nonneg_right gamma_tail_one_stronger_reserve.le hmass
  rw [weilQuad_eq_retainedOddGamma_add_remainder hF hs ho]
  linarith only [hR, hp]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.gamma_tail_one_stronger_reserve
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedGammaRemainderWeight_ge_higher_lags
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedGammaRemainder_ge_higher_lags
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_ge_retainedOddGamma_add_higher_lags

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_ge_retainedOddGamma_add_moment_reserve
