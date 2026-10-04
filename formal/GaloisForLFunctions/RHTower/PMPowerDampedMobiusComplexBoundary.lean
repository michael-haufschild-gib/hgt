import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDerivativeBoundary
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDyadicResolvent

/-!
# Isolated Hilbert admission on the imaginary damping axis

The finite Möbius Fermi source extends literally to complex damping and agrees
with the real source on real parameters. Its cleared Mellin identity shows that
Hilbert admission at imaginary damping transports critical zeta zeros vertically.
An unconditional critical zero and analytic zero isolation therefore make zero
the only admitted imaginary damping parameter in a neighborhood of the origin.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
noncomputable section
namespace RHTower

/-- Literal complex power damping of the Möbius coefficients. -/
def pmComplexDampedMobiusCoeff (z : ℂ) (n : ℕ) : ℂ :=
  (moebius n : ℂ) * (n : ℂ)^(-z)

/-- The complete finite physical Fermi source at complex damping. -/
def pmComplexDampedFermiSource (z : ℂ) (t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 ⌊1/t⌋₊,
    pmComplexDampedMobiusCoeff z d * fermiNymanGen (d : ℝ) t)

theorem pmComplexDampedMobiusCoeff_ofReal (ε : ℝ) (n : ℕ) :
    pmComplexDampedMobiusCoeff (ε : ℂ) n = pmPowerDampedMobiusCoeff ε n := by
  unfold pmComplexDampedMobiusCoeff pmPowerDampedMobiusCoeff
  rw [Complex.ofReal_mul,Complex.ofReal_intCast,Complex.ofReal_cpow (Nat.cast_nonneg n),
    Complex.ofReal_neg,Complex.ofReal_natCast]

theorem pmComplexDampedFermiSource_ofReal (ε t : ℝ) :
    pmComplexDampedFermiSource (ε : ℂ) t = pmPowerDampedFermiSource ε t := by
  simp only [pmComplexDampedFermiSource,pmComplexDampedMobiusCoeff_ofReal,
    pmPowerDampedMobiusCoeff,pmPowerDampedFermiSource]

theorem pmComplexDampedFermiSource_eq_zero_of_one_lt (z : ℂ) {t : ℝ} (ht : 1 < t) :
    pmComplexDampedFermiSource z t = 0 := by
  have hf : ⌊1/t⌋₊ = 0 := Nat.floor_eq_zero.mpr
    ((div_lt_one (lt_trans zero_lt_one ht)).mpr ht)
  unfold pmComplexDampedFermiSource
  rw [hf]
  simp

theorem pmComplexDampedFermiSource_eq_dilation (z : ℂ) {t : ℝ} (ht : 0 < t) :
    pmComplexDampedFermiSource z t =
      -pmWeightedDilationSource (pmComplexDampedMobiusCoeff z) (fermiNymanGen 1) t := by
  have hcut : (1 : ℝ) < ((⌊1/t⌋₊ : ℝ)+1)*t :=
    (div_lt_iff₀ ht).mp (Nat.lt_floor_add_one (1/t))
  rw [pmWeightedDilationSource_eq_sum _ _ ⌊1/t⌋₊ (θ := 1) ht (fun x hx =>
    fermiNymanGen_eq_zero_of_inv_lt (by norm_num) (by simpa using hx)) hcut]
  unfold pmComplexDampedFermiSource
  congr 1
  simp_rw [← pm_fermiNymanGen_dilate]
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc,Finset.mem_range] at hn ⊢
    omega
  · intro n hn hnot
    have hn0 : n = 0 := by
      simp only [Finset.mem_Icc,Finset.mem_range] at hn hnot
      omega
    subst n
    simp [pmComplexDampedMobiusCoeff]

theorem pmComplexDampedMobiusCoeff_term (z s : ℂ) (n : ℕ) :
    LSeries.term (pmComplexDampedMobiusCoeff z) s n =
      LSeries.term (fun n => (moebius n : ℂ)) (s+z) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn,pmComplexDampedMobiusCoeff,
    Complex.cpow_neg,Complex.cpow_add _ _ (by exact_mod_cast hn : (n : ℂ) ≠ 0)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem pmComplexDampedMobiusCoeff_lSeriesSummable (z : ℂ) {s : ℂ}
    (hs : 1 < (s+z).re) : LSeriesSummable (pmComplexDampedMobiusCoeff z) s := by
  change Summable (LSeries.term (pmComplexDampedMobiusCoeff z) s)
  rw [funext (pmComplexDampedMobiusCoeff_term z s)]
  exact ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs

theorem pmComplexDampedMobiusCoeff_lSeries (z : ℂ) {s : ℂ}
    (hs : 1 < (s+z).re) :
    LSeries (pmComplexDampedMobiusCoeff z) s = 1/riemannZeta (s+z) := by
  have heq : LSeries (pmComplexDampedMobiusCoeff z) s =
      LSeries (fun n => (moebius n : ℂ)) (s+z) :=
    tsum_congr (pmComplexDampedMobiusCoeff_term z s)
  rw [heq]
  apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).mpr
  have h := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at h
  simpa only [mul_comm] using h

private theorem pmcd_seed_support (t : ℝ) (ht : 1 < t) : fermiNymanGen 1 t = 0 :=
  fermiNymanGen_eq_zero_of_inv_lt (by norm_num) (by simpa using ht)

private theorem pmcd_seed_mellin {s : ℂ} (hs : 1/2 < s.re) (hi : 0 < s.im) :
    mellin (fermiNymanGen 1) s = -(1-(2 : ℂ)^(1-s))*riemannZeta s/s := by
  let U : Set ℂ := {w | 1/2 < w.re ∧ 0 < w.im}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hf := pm_analyticOnNhd_mellin_of_memLp
    (memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)) pmcd_seed_support
  have hleft : AnalyticOnNhd ℂ (mellin (fermiNymanGen 1)) U :=
    fun w hw => hf w hw.1
  have hright : AnalyticOnNhd ℂ (fun w => -(1-(2 : ℂ)^(1-w))*riemannZeta w/w) U := by
    intro w hw
    have hw0 : w ≠ 0 := ne_zero_of_re_pos (by linarith [hw.1])
    have hw1 : w ≠ 1 := by intro he; have hh := hw.2; simp [he] at hh
    have hp : AnalyticAt ℂ (fun v : ℂ => (2 : ℂ)^(1-v)) w := by
      simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
      exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).cexp'
    have hz : AnalyticAt ℂ riemannZeta w :=
      ((differentiableOn_riemannZeta).analyticOnNhd isOpen_compl_singleton) w hw1
    exact (((analyticAt_const.sub hp).neg).mul hz).div analyticAt_id hw0
  let w₀ : ℂ := 3/4+I
  have hw₀ : w₀ ∈ U := by norm_num [w₀,U]
  have he : (mellin (fermiNymanGen 1)) =ᶠ[𝓝 w₀]
      (fun w => -(1-(2 : ℂ)^(1-w))*riemannZeta w/w) := by
    filter_upwards [hU.mem_nhds hw₀,
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds
        (show w₀.re < 1 by norm_num [w₀])] with w hw hw1
    have hh := mellin_fermiNymanGen (by linarith [hw.1] : 0 < w.re) hw1
      (by norm_num : (0 : ℝ) < 1)
    simpa only [Complex.ofReal_one,Complex.one_cpow,one_mul,neg_div,neg_mul] using hh
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    ((convex_halfSpace_re_gt (1/2)).inter (convex_halfSpace_im_gt 0)).isPreconnected
    hw₀ he ⟨hs,hi⟩

/-- Absolute dilation interchange identifies the actual source Mellin transform. -/
theorem hasMellin_pmComplexDampedFermiSource (z : ℂ) {s : ℂ}
    (hs : 1 < s.re) (hi : 0 < s.im) (hsz : 1 < (s+z).re) :
    HasMellin (pmComplexDampedFermiSource z) s
      ((1-(2 : ℂ)^(1-s))*riemannZeta s/(s*riemannZeta (s+z))) := by
  have hseed := pm_mellinConvergent_of_memLp
    (memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)) pmcd_seed_support
    (by linarith : 1/2 < s.re)
  have h := pmWeightedDilationSource_hasMellin (pmComplexDampedMobiusCoeff z)
    (fermiNymanGen 1) (by simp [pmComplexDampedMobiusCoeff])
    (pmComplexDampedMobiusCoeff_lSeriesSummable z hsz) hseed
  have hn : mellin (pmComplexDampedFermiSource z) s =
      -mellin (pmWeightedDilationSource (pmComplexDampedMobiusCoeff z) (fermiNymanGen 1)) s := by
    unfold mellin
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (t : ℂ)^(s-1) • pmComplexDampedFermiSource z t =
      -((t : ℂ)^(s-1) • pmWeightedDilationSource (pmComplexDampedMobiusCoeff z) (fermiNymanGen 1) t)
    rw [pmComplexDampedFermiSource_eq_dilation z ht,smul_neg]
  constructor
  · apply h.1.neg.congr_fun _ measurableSet_Ioi
    intro t ht
    change -((t : ℂ)^(s-1) • _) = (t : ℂ)^(s-1) • pmComplexDampedFermiSource z t
    rw [pmComplexDampedFermiSource_eq_dilation z ht,smul_neg]
  · rw [hn,h.2,pmComplexDampedMobiusCoeff_lSeries z hsz,pmcd_seed_mellin (by linarith) hi]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

/-- Admission continues the cleared identity to the common upper half-plane. -/
theorem pmComplexDampedFermiSource_cleared_mellin
    {z : ℂ} (hz : z.re = 0)
    (hf : MemLp (pmComplexDampedFermiSource z) 2 (volume.restrict (Ioi 0)))
    {s : ℂ} (hs : 1/2 < s.re) (hi : 0 < s.im) (hiz : 0 < (s+z).im) :
    riemannZeta (s+z)*mellin (pmComplexDampedFermiSource z) s =
      (1-(2 : ℂ)^(1-s))*riemannZeta s/s := by
  let U : Set ℂ := {w | 1/2 < w.re ∧ 0 < w.im ∧ -z.im < w.im}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt continuous_const Complex.continuous_im))
  have hA := pm_analyticOnNhd_mellin_of_memLp hf
    (fun _ ht => pmComplexDampedFermiSource_eq_zero_of_one_lt z ht)
  have hseed := pm_analyticOnNhd_mellin_of_memLp
    (memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)) pmcd_seed_support
  have hl : AnalyticOnNhd ℂ (fun w => riemannZeta (w+z)*mellin (pmComplexDampedFermiSource z) w) U := by
    intro w hw
    have hwz : w+z ≠ 1 := by
      intro he
      have he' := congrArg Complex.im he
      simp only [Complex.add_im,Complex.one_im] at he'
      linarith [hw.2.2]
    have hzeta := (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) (w+z) hwz
    have hcomp : AnalyticAt ℂ (fun v : ℂ => riemannZeta (v+z)) w :=
      hzeta.comp (f := fun v : ℂ => v+z) (analyticAt_id.add analyticAt_const)
    exact hcomp.mul (hA w hw.1)
  have hr : AnalyticOnNhd ℂ (fun w => -mellin (fermiNymanGen 1) w) U :=
    fun w hw => (hseed w hw.1).neg
  let w₀ : ℂ := 2+((max 0 (-z.im)+1 : ℝ) : ℂ)*I
  have hw₀ : w₀ ∈ U := by
    norm_num [U,w₀]
    constructor <;> linarith [le_max_left (0 : ℝ) (-z.im),le_max_right (0 : ℝ) (-z.im)]
  have he : (fun w => riemannZeta (w+z)*mellin (pmComplexDampedFermiSource z) w)
      =ᶠ[𝓝 w₀] (fun w => -mellin (fermiNymanGen 1) w) := by
    filter_upwards [hU.mem_nhds hw₀,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show 1 < w₀.re by norm_num [w₀])] with w hw hwr
    have hwsz : 1 < (w+z).re := by simpa only [Complex.add_re,hz,add_zero] using hwr
    have hw0 : w ≠ 0 := ne_zero_of_re_pos (by linarith)
    rw [(hasMellin_pmComplexDampedFermiSource z hwr hw.2.1 hwsz).2,
      pmcd_seed_mellin hw.1 hw.2.1]
    field_simp [hw0,riemannZeta_ne_zero_of_one_lt_re hwsz]
  have heq := hl.eqOn_of_preconnected_of_eventuallyEq hr
    ((convex_halfSpace_re_gt (1/2)).inter
      ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_im_gt (-z.im)))).isPreconnected
    hw₀ he (show s ∈ U from ⟨hs,hi,by simp only [Complex.add_im] at hiz; linarith⟩)
  calc
    _ = -mellin (fermiNymanGen 1) s := heq
    _ = _ := by rw [pmcd_seed_mellin hs hi]; ring

private theorem pmcd_zeta_slope {ρ : ℂ} (hρ : ρ ≠ 1) (hzero : riemannZeta ρ = 0) :
    Tendsto (fun δ : ℝ => riemannZeta (ρ+(δ : ℂ))/(δ : ℂ))
      (𝓝[>] 0) (𝓝 (deriv riemannZeta ρ)) := by
  have hd : HasDerivAt (fun w : ℂ => riemannZeta (ρ+w)) (deriv riemannZeta ρ) 0 := by
    have hz : HasDerivAt riemannZeta (deriv riemannZeta ρ) (ρ+0) := by
      simpa only [add_zero] using (differentiableAt_riemannZeta hρ).hasDerivAt
    have hi : HasDerivAt (fun w : ℂ => ρ+w) 1 0 :=
      (hasDerivAt_id (0 : ℂ)).const_add ρ
    simpa only [mul_one] using! hz.comp (0 : ℂ) hi
  have hdr : HasDerivAt (fun t : ℝ => riemannZeta (ρ+(t : ℂ))) (deriv riemannZeta ρ) 0 :=
    hd.comp_ofReal
  simpa only [zero_add,Complex.ofReal_zero,add_zero,hzero,sub_zero,
    Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm] using
      hdr.tendsto_slope_zero_right

/-- Imaginary-damped admission transports every admissible critical zero;
no simplicity hypothesis is needed. -/
theorem pmComplexDampedFermiSource_critical_zero_transport
    {z ρ : ℂ} (hz : z.re = 0)
    (hf : MemLp (pmComplexDampedFermiSource z) 2 (volume.restrict (Ioi 0)))
    (hρ : ρ.re = 1/2) (hρi : 0 < ρ.im) (hzero : riemannZeta ρ = 0)
    (hρz : 0 < (ρ-z).im) : riemannZeta (ρ-z) = 0 := by
  have hρ1 : ρ ≠ 1 := by intro he; have hh := hρ; simp [he] at hh
  have hs : (ρ-z).re = 1/2 := by simp only [Complex.sub_re,hz,sub_zero,hρ]
  have hs0 : ρ-z ≠ 0 := ne_zero_of_re_pos (by rw [hs]; norm_num)
  have hs1 : ρ-z ≠ 1 := by intro he; have hh := hs; simp [he] at hh
  have hl := (pmcd_zeta_slope hρ1 hzero).mul
    (pm_mellin_L2_boundary_decay hf
      (fun _ ht => pmComplexDampedFermiSource_eq_zero_of_one_lt z ht) hs)
  rw [mul_zero] at hl
  have hleft : Tendsto (fun δ : ℝ => riemannZeta (ρ+(δ : ℂ))*
      mellin (pmComplexDampedFermiSource z) (ρ-z+(δ : ℂ))) (𝓝[>] 0) (𝓝 0) := by
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hn : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show (0 : ℝ) < δ from hδ).ne'
    rw [← mul_assoc,div_mul_cancel₀ _ hn]
  let E : ℂ → ℂ := fun w => (1-(2 : ℂ)^(1-w))*riemannZeta w/w
  have hE : ContinuousAt E (ρ-z) := by
    have hp : ContinuousAt (fun w : ℂ => (2 : ℂ)^(1-w)) (ρ-z) := by
      simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
      fun_prop
    exact ((continuousAt_const.sub hp).mul (differentiableAt_riemannZeta hs1).continuousAt).div
      continuousAt_id hs0
  have hshift : Tendsto (fun δ : ℝ => ρ-z+(δ : ℂ)) (𝓝[>] 0) (𝓝 (ρ-z)) := by
    simpa only [Complex.ofReal_zero,add_zero] using
      tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0 |>.mono_left nhdsWithin_le_nhds)
  have heq : (fun δ : ℝ => riemannZeta (ρ+(δ : ℂ))*
      mellin (pmComplexDampedFermiSource z) (ρ-z+(δ : ℂ))) =ᶠ[𝓝[>] 0]
        (fun δ => E (ρ-z+(δ : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0 < δ at hδ
    have hh := pmComplexDampedFermiSource_cleared_mellin hz hf
      (s := ρ-z+(δ : ℂ)) (by simp only [Complex.add_re,Complex.ofReal_re,hs]; linarith)
      (by simpa using hρz) (by simpa using hρi)
    simpa only [show ρ-z+(δ : ℂ)+z = ρ+(δ : ℂ) by ring] using hh
  have hEzero : E (ρ-z) = 0 := tendsto_nhds_unique (hE.tendsto.comp hshift) (hleft.congr' heq)
  have hh := congrArg (fun v : ℂ => v*(ρ-z)) hEzero
  dsimp only [E] at hh
  rw [div_mul_cancel₀ _ hs0,zero_mul] at hh
  exact (mul_eq_zero.mp hh).resolve_left (one_sub_two_cpow_ne_zero (by rw [hs]; norm_num))

theorem memLp_pmComplexDampedFermiSource_zero :
    MemLp (pmComplexDampedFermiSource 0) 2 (volume.restrict (Ioi 0)) := by
  have he : pmComplexDampedFermiSource 0 =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      pmSupportedDyadicHaar := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases ht1 : t ≤ 1
    · have hh : pmComplexDampedFermiSource 0 t = pmPowerDampedFermiSource 0 t := by
        simpa using pmComplexDampedFermiSource_ofReal 0 t
      rw [hh,pmPowerDampedFermiSource_zero_eq_haar ⟨ht,ht1⟩,
        pmSupportedDyadicHaar,indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht,ht1⟩)]
    · rw [pmComplexDampedFermiSource_eq_zero_of_one_lt 0 (lt_of_not_ge ht1),
        pmSupportedDyadicHaar_eq_zero (lt_of_not_ge ht1)]
  exact (memLp_congr_ae he).mpr memLp_pmSupportedDyadicHaar

/-- Every sufficiently small nonzero imaginary damping fails canonical L² admission. -/
theorem exists_pmComplexDampedFermiSource_imaginary_gap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, 0 < |y| → |y| < δ →
      ¬ MemLp (pmComplexDampedFermiSource ((y : ℂ)*I)) 2 (volume.restrict (Ioi 0)) := by
  obtain ⟨T,hT,hzeros⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨γ,hγ,hzero⟩ := hzeros T le_rfl
  let ρ := linePt γ
  have hρ : ρ.re = 1/2 := by norm_num [ρ,linePt]
  have hρi : 0 < ρ.im := by
    simpa only [ρ,linePt,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using
        hT.trans_le hγ.1
  have hp := (analyticAt_zetaResidueUnit ρ).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (not_eventually_zetaResidueUnit_eq_zero ρ)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhdsWithin_iff.mp hp
  refine ⟨min r ρ.im,lt_min hr hρi,?_⟩
  intro y hy hyδ hf
  have hyr : |y| < r := hyδ.trans_le (min_le_left _ _)
  have hyρ : |y| < ρ.im := hyδ.trans_le (min_le_right _ _)
  have hshift : 0 < (ρ-(y : ℂ)*I).im := by
    simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
      Complex.ofReal_im,Complex.I_re,mul_one,mul_zero]
    linarith [le_abs_self y]
  have hzero' := pmComplexDampedFermiSource_critical_zero_transport (by simp) hf hρ hρi hzero hshift
  have hne : ρ-(y : ℂ)*I ≠ ρ := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
      Complex.ofReal_im,Complex.I_re,mul_one,mul_zero] at hi
    have hy0 : y = 0 := by linarith
    simp [hy0] at hy
  have hd : dist (ρ-(y : ℂ)*I) ρ < r := by
    rw [dist_eq_norm,show (ρ-(y : ℂ)*I)-ρ = -((y : ℂ)*I) by ring,
      norm_neg,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    exact hyr
  exact (hball ⟨hd,by simpa only [mem_compl_iff,mem_singleton_iff] using hne⟩)
    (zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero hzero')

/-- Zero is the unique admitted imaginary damping parameter near the origin. -/
theorem exists_pmComplexDampedFermiSource_imaginary_memLp_iff_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y| < δ →
      (MemLp (pmComplexDampedFermiSource ((y : ℂ)*I)) 2 (volume.restrict (Ioi 0)) ↔ y = 0) := by
  obtain ⟨δ,hδ,hgap⟩ := exists_pmComplexDampedFermiSource_imaginary_gap
  refine ⟨δ,hδ,?_⟩
  intro y hy
  constructor
  · intro hf
    by_contra hn
    exact hgap y (abs_pos.mpr hn) hy hf
  · rintro rfl
    simpa using memLp_pmComplexDampedFermiSource_zero

end RHTower
