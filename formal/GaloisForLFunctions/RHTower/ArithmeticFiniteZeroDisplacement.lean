import GaloisForLFunctions.RHTower.ArithmeticFiniteSourceContour

/-!
# The complete arithmetic displacement law for finite-head zeros

The centered tail determines the exact normalized finite-source error. Along every cofinal
cutoff sequence and every converging sequence of literal finite-head zeros, analytic-order
factorization gives a nonzero complex displacement limit. A logarithmic drift estimate freezes
the moving exponent at the limiting zeta zero, retaining its cutoff phase and full multiplicity.
Actual cofinal zero sequences realize the law at every nontrivial zero. The distance scale is
therefore explicit, but the original zero's real part is not determined; RH remains open.
-/

noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped Topology BigOperators
namespace RHTower.DeletionMixedRefinement

/-- The leading coefficient of the complete finite Bernoulli correction. -/
def finiteTailLeadingCoefficient (s : ℂ) : ℂ := s*(s+1)*(s+2)/720

/-- Exact normalized error, including the full remaining tail phase. -/
theorem scaled_finiteCutoffZeta_error {N : ℕ} (hN : 1≤N) {s : ℂ}
    (hs : 0<s.re) (hs1 : s≠1) :
    (N:ℂ)^(s+3)*(finiteCutoffZeta N s-riemannZeta s)=
      finiteTailLeadingCoefficient s*centeredTailPhase N s := by
  rw [finiteCutoffZeta_sub_zeta hN hs hs1]
  have he := centeredTailPhase_mul_eq_centered_tail (by linarith : -1<s.re) hN
  unfold finiteTailLeadingCoefficient
  linear_combination -(s*(s+1)/720)*he

/-- The complete normalized tail tends to one along cofinal cutoffs and varying spectral points. -/
theorem tendsto_centeredTailPhase_of_tendsto {K : ℕ→ℕ} (hK : Tendsto K atTop atTop)
    {z : ℕ→ℂ} {rho : ℂ} (hz : Tendsto z atTop (𝓝 rho)) (hrho : 0<rho.re) :
    Tendsto (fun j => centeredTailPhase (K j) (z j)) atTop (𝓝 1) := by
  have hnorm : Tendsto (fun j => ‖z j+3‖) atTop (𝓝 ‖rho+3‖) :=
    (hz.add_const 3).norm
  have hB : ∀ᶠj in atTop, ‖z j+3‖≤‖rho+3‖+1 :=
    ((tendsto_order.1 hnorm).2 _ (by linarith)).mono (fun _ h => h.le)
  have hNr : Tendsto (fun j => (K j:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hK
  have hcut := hNr.eventually_ge_atTop (‖rho+3‖+1)
  have hre : ∀ᶠj in atTop, 0<(z j).re :=
    (tendsto_order.1 (Complex.continuous_re.tendsto rho |>.comp hz)).1 0 hrho
  have hbound : ∀ᶠj in atTop,
      ‖centeredTailPhase (K j) (z j)-1‖ ≤ (4*(‖rho+3‖+1)/5)/(K j:ℝ) := by
    filter_upwards [hB,hcut,hre,hK.eventually (eventually_ge_atTop 1)] with j hB hcut hre hN
    have ht : |(z j).im|≤K j := by
      have h := Complex.abs_im_le_norm (z j+3)
      norm_num at h
      exact h.trans (hB.trans hcut)
    have hb := norm_centeredTailPhase_sub_one_le_linear (by linarith : -1<(z j).re) hN ht
    calc
      _ ≤ 4*‖z j+3‖/(5*(K j:ℝ)) := hb
      _ ≤ (4*(‖rho+3‖+1)/5)/(K j:ℝ) := by
        rw [div_div]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hzero : Tendsto (fun j => ‖centeredTailPhase (K j) (z j)-1‖) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound
      ((tendsto_const_div_atTop_nhds_zero_nat (4*(‖rho+3‖+1)/5)).comp hK)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hzero

/-- A moving spectral point retains a definite complex leading error coefficient. -/
theorem tendsto_scaled_finiteCutoffZeta_error {K : ℕ→ℕ} (hK : Tendsto K atTop atTop)
    {z : ℕ→ℂ} {rho : ℂ} (hz : Tendsto z atTop (𝓝 rho)) (hrho : 0<rho.re)
    (hrho1 : rho≠1) :
    Tendsto (fun j => (K j:ℂ)^(z j+3)*(finiteCutoffZeta (K j) (z j)-riemannZeta (z j)))
      atTop (𝓝 (finiteTailLeadingCoefficient rho)) := by
  have hB : Continuous finiteTailLeadingCoefficient := by
    unfold finiteTailLeadingCoefficient
    fun_prop
  have hlim := (hB.tendsto rho |>.comp hz).mul (tendsto_centeredTailPhase_of_tendsto hK hz hrho)
  simp only [mul_one] at hlim
  apply hlim.congr'
  have hre := (tendsto_order.1 (Complex.continuous_re.tendsto rho |>.comp hz)).1 0 hrho
  filter_upwards [hre,hz.eventually (eventually_ne_nhds hrho1),hK.eventually (eventually_ge_atTop 1)]
    with j hre hne hN
  exact (scaled_finiteCutoffZeta_error hN hre hne).symm

/-- Every converging sequence of literal finite-head zeros has a multiplicity-sensitive
complex displacement law, initially normalized at the moving point. -/
theorem tendsto_moving_scaled_finite_zero {m : ℕ} {rho : ℂ} {g : ℂ→ℂ}
    (hrho : 0<rho.re) (hrho1 : rho≠1) (hg : ContinuousAt g rho) (hg0 : g rho≠0)
    (hfactor : riemannZeta =ᶠ[𝓝 rho] fun s => (s-rho)^m*g s)
    {K : ℕ→ℕ} (hK : Tendsto K atTop atTop) {z : ℕ→ℂ} (hz : Tendsto z atTop (𝓝 rho))
    (hzero : ∀ᶠj in atTop, finiteCutoffResidual (K j) (z j)=0) :
    Tendsto (fun j => (K j:ℂ)^(z j+3)*(z j-rho)^m) atTop
      (𝓝 (-finiteTailLeadingCoefficient rho/g rho)) := by
  have hgseq := hg.tendsto.comp hz
  have he := tendsto_scaled_finiteCutoffZeta_error hK hz hrho hrho1
  have hlim := he.neg.div hgseq hg0
  apply hlim.congr'
  filter_upwards [hzero,hz.eventually hfactor,hgseq.eventually (eventually_ne_nhds hg0)]
    with j hzero hfactor hg0
  have hf : finiteCutoffZeta (K j) (z j)=0 := by simp [finiteCutoffZeta,hzero]
  dsimp only [Function.comp_apply] at hg0
  dsimp only [Pi.div_apply,Function.comp_apply]
  rw [hf,zero_sub,hfactor,mul_neg,neg_neg,←mul_assoc,mul_div_cancel_right₀ _ hg0]

/-- A bounded moving displacement forces its logarithmic phase drift to vanish. -/
theorem tendsto_finite_zero_log_drift {m : ℕ} (hm : 0 < m) {rho L : ℂ}
    {K : ℕ→ℕ} (hK : Tendsto K atTop atTop) {z : ℕ→ℂ} (hz : Tendsto z atTop (𝓝 rho))
    (hrho : 0<rho.re)
    (hscale : Tendsto (fun j => (K j:ℂ)^(z j+3)*(z j-rho)^m) atTop (𝓝 L)) :
    Tendsto (fun j => (z j-rho)*(Real.log (K j):ℂ)) atTop (𝓝 0) := by
  have hNr : Tendsto (fun j => (K j:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hK
  have hre := (tendsto_order.1 (Complex.continuous_re.tendsto rho |>.comp hz)).1 0 hrho
  have hB := (tendsto_order.1 hscale.norm).2 (‖L‖+1) (by linarith)
  have hbound : ∀ᶠj in atTop, ‖z j-rho‖^m ≤ (‖L‖+1)/(K j:ℝ)^2 := by
    filter_upwards [hre,hB,hK.eventually (eventually_ge_atTop 1)] with j hre hB hN
    dsimp only [Function.comp_apply] at hre
    have hNp : (0:ℝ)<K j := by exact_mod_cast (show 0<K j by omega)
    have hNr : (1:ℝ)≤K j := by exact_mod_cast hN
    rw [norm_mul,norm_pow,Complex.norm_natCast_cpow_of_pos (show 0<K j by omega),
      show (z j+3).re=(z j).re+3 by simp] at hB
    have hp : (K j:ℝ)^2≤(K j:ℝ)^((z j).re+3) := by
      rw [←Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    apply (le_div_iff₀ (sq_pos_of_pos hNp)).mpr
    calc
      _ ≤ ‖z j-rho‖^m*(K j:ℝ)^((z j).re+3) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ ‖L‖+1 := by nlinarith [hB.le]
  have hloglim : Tendsto (fun j => (Real.log (K j))^m/(K j:ℝ)^2) atTop (𝓝 0) := by
    have h : Tendsto (fun j => (Real.log (K j))^(m:ℝ)/(K j:ℝ)^(2:ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_rpow_atTop (m:ℝ) (by norm_num : (0:ℝ)<2)).tendsto_div_nhds_zero.comp hNr
    simpa only [Real.rpow_natCast,Real.rpow_two] using h
  have hpow : Tendsto (fun j => (‖z j-rho‖*Real.log (K j))^m) atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [hK.eventually (eventually_ge_atTop 1)] with j hN
      exact pow_nonneg (mul_nonneg (norm_nonneg _) (Real.log_nonneg (by exact_mod_cast hN))) m
    · filter_upwards [hbound,hK.eventually (eventually_ge_atTop 1)] with j hb hN
      have hl : 0≤Real.log (K j) := Real.log_nonneg (by exact_mod_cast hN)
      calc
        _ = ‖z j-rho‖^m*Real.log (K j)^m := mul_pow _ _ _
        _ ≤ ((‖L‖+1)/(K j:ℝ)^2)*Real.log (K j)^m :=
          mul_le_mul_of_nonneg_right hb (pow_nonneg hl m)
        _ = (‖L‖+1)*(Real.log (K j)^m/(K j:ℝ)^2) := by ring
    · simpa using hloglim.const_mul (‖L‖+1)
  have hroot := hpow.rpow_const_nhds_zero (show 0<(m:ℝ)⁻¹ by positivity)
  have hlognorm : Tendsto (fun j => ‖z j-rho‖*Real.log (K j)) atTop (𝓝 0) := by
    apply hroot.congr'
    filter_upwards [hK.eventually (eventually_ge_atTop 1)] with j hN
    exact Real.pow_rpow_inv_natCast
      (mul_nonneg (norm_nonneg _) (Real.log_nonneg (by exact_mod_cast hN))) hm.ne'
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply hlognorm.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop 1)] with j hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hN))]

/-- Vanishing logarithmic drift makes the moving complex power agree asymptotically
with the power fixed at the limiting zero. -/
theorem tendsto_finite_zero_power_correction {rho : ℂ}
    {K : ℕ→ℕ} (hK : Tendsto K atTop atTop) {z : ℕ→ℂ}
    (hdrift : Tendsto (fun j => (z j-rho)*(Real.log (K j):ℂ)) atTop (𝓝 0)) :
    Tendsto (fun j => (K j:ℂ)^(rho-z j)) atTop (𝓝 1) := by
  have he := (Complex.continuous_exp.tendsto (-0)).comp hdrift.neg
  simp only [neg_zero,Complex.exp_zero] at he
  apply he.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop 1)] with j hN
  have hlog : Complex.log (K j:ℂ)=(Real.log (K j):ℂ) := by
    simp
  dsimp only [Function.comp_apply]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (show K j≠0 by omega)),hlog]
  congr 1
  ring

/-- The complete finite-head splitting law has a fixed-center complex normalization. -/
theorem tendsto_fixed_scaled_finite_zero {m : ℕ} (hm : 0 < m) {rho : ℂ} {g : ℂ→ℂ}
    (hrho : 0<rho.re) (hrho1 : rho≠1) (hg : ContinuousAt g rho) (hg0 : g rho≠0)
    (hfactor : riemannZeta =ᶠ[𝓝 rho] fun s => (s-rho)^m*g s)
    {K : ℕ→ℕ} (hK : Tendsto K atTop atTop) {z : ℕ→ℂ} (hz : Tendsto z atTop (𝓝 rho))
    (hzero : ∀ᶠj in atTop, finiteCutoffResidual (K j) (z j)=0) :
    Tendsto (fun j => (K j:ℂ)^(rho+3)*(z j-rho)^m) atTop
      (𝓝 (-finiteTailLeadingCoefficient rho/g rho)) := by
  have hmove := tendsto_moving_scaled_finite_zero hrho hrho1 hg hg0 hfactor hK hz hzero
  have hdrift := tendsto_finite_zero_log_drift hm hK hz hrho hmove
  have hcorr := tendsto_finite_zero_power_correction hK hdrift
  have hlim := hcorr.mul hmove
  simp only [one_mul] at hlim
  apply hlim.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop 1)] with j hN
  rw [←mul_assoc,←Complex.cpow_add _ _ (by exact_mod_cast (show K j≠0 by omega)),
    show rho-z j+(z j+3)=rho+3 by ring]

/-- The actual leading correction cannot vanish in the positive half-plane. -/
theorem finiteTailLeadingCoefficient_ne_zero {s : ℂ} (hs : 0<s.re) :
    finiteTailLeadingCoefficient s≠0 := by
  have h0 : s≠0 := by intro h; rw [h] at hs; norm_num at hs
  have h1 : s+1≠0 := by intro h; have := congrArg Complex.re h; norm_num at this; linarith
  have h2 : s+2≠0 := by intro h; have := congrArg Complex.re h; norm_num at this; linarith
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) (by norm_num)

/-- Every actual nontrivial zeta zero has a nonzero, multiplicity-sensitive leading
coefficient governing all convergent finite-head zero sequences. -/
theorem exists_finite_zero_displacement_coefficient (rho : RiemannGaussian.NontrivialZetaZero) :
    ∃g : ℂ→ℂ, AnalyticAt ℂ g rho.1 ∧ g rho.1≠0 ∧
      (riemannZeta =ᶠ[𝓝 rho.1] fun s =>
        (s-rho.1)^(RiemannGaussian.analyticZetaZeroMultiplicity rho)*g s) ∧
      -finiteTailLeadingCoefficient rho.1/g rho.1≠0 ∧
      ∀ (K : ℕ→ℕ) (z : ℕ→ℂ), Tendsto K atTop atTop → Tendsto z atTop (𝓝 rho.1) →
        (∀ᶠj in atTop, finiteCutoffResidual (K j) (z j)=0) →
        Tendsto (fun j => (K j:ℂ)^(rho.1+3)*
          (z j-rho.1)^(RiemannGaussian.analyticZetaZeroMultiplicity rho)) atTop
          (𝓝 (-finiteTailLeadingCoefficient rho.1/g rho.1)) := by
  obtain ⟨g,hg,hg0,hfactor⟩ :=
    (RiemannGaussian.analyticAt_riemannZeta_nontrivialZero rho).analyticOrderAt_ne_top.mp
      (RiemannGaussian.analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)
  simp only [smul_eq_mul] at hfactor
  have hrho := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  refine ⟨g,hg,hg0,hfactor,div_ne_zero (neg_ne_zero.mpr
    (finiteTailLeadingCoefficient_ne_zero hrho)) hg0,?_⟩
  intro K z hK hz hzero
  exact tendsto_fixed_scaled_finite_zero (RiemannGaussian.analyticZetaZeroMultiplicity_positive rho)
    hrho rho.2.2.2 hg.continuousAt hg0 hfactor hK hz hzero

/-- Actual cofinal finite-head zero sequences realize the nonzero complex displacement law
at every nontrivial zeta zero; no choice of a simple zero is needed. -/
theorem exists_cofinal_finite_zero_displacement_limit (rho : RiemannGaussian.NontrivialZetaZero) :
    ∃ (K : ℕ→ℕ) (z : ℕ→ℂ) (A : ℂ), Tendsto K atTop atTop ∧
      Tendsto z atTop (𝓝 rho.1) ∧
      (∀j, j≤K j ∧ z j≠rho.1 ∧ finiteCutoffResidual (K j) (z j)=0) ∧ A≠0 ∧
      Tendsto (fun j => (K j:ℂ)^(rho.1+3)*
        (z j-rho.1)^(RiemannGaussian.analyticZetaZeroMultiplicity rho)) atTop (𝓝 A) := by
  have hex : ∀j : ℕ, ∃N : ℕ, ∃z : ℂ, j≤N ∧ 0<dist z rho.1 ∧
      dist z rho.1<1/((j:ℝ)+1) ∧ finiteCutoffResidual N z=0 := by
    intro j
    have he := eventually_exists_finiteCutoffResidual_zero_near rho
      (show 0<1/((j:ℝ)+1) by positivity)
    obtain ⟨N,hN,hz⟩ := ((eventually_ge_atTop j).and he).exists
    obtain ⟨z,hpos,hnear,hzero⟩ := hz
    exact ⟨N,z,hN,hpos,hnear,hzero⟩
  choose K z hK hdist hnear hzero using hex
  have hKt : Tendsto K atTop atTop := tendsto_atTop_mono hK tendsto_id
  have hzt : Tendsto z atTop (𝓝 rho.1) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun j => (hnear j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨g,_,_,_,hA,huniv⟩ := exists_finite_zero_displacement_coefficient rho
  exact ⟨K,z,-finiteTailLeadingCoefficient rho.1/g rho.1,hKt,hzt,
    fun j => ⟨hK j,dist_pos.mp (hdist j),hzero j⟩,hA,
    huniv K z hKt hzt (Eventually.of_forall hzero)⟩

/-- The exact complex displacement law determines the positive distance scale, with
exponent divided by the full analytic multiplicity. -/
theorem tendsto_finite_zero_distance_scale {m : ℕ} (hm : 0 < m) {rho L : ℂ}
    {K : ℕ→ℕ} (hK : Tendsto K atTop atTop) {z : ℕ→ℂ}
    (hscale : Tendsto (fun j => (K j:ℂ)^(rho+3)*(z j-rho)^m) atTop (𝓝 L)) :
    Tendsto (fun j => (K j:ℝ)^((rho.re+3)/(m:ℝ))*dist (z j) rho) atTop
      (𝓝 (‖L‖^((m:ℝ)⁻¹))) := by
  have hr := hscale.norm.rpow_const (Or.inr (show 0≤(m:ℝ)⁻¹ by positivity))
  apply hr.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop 1)] with j hN
  rw [norm_mul,norm_pow,Complex.norm_natCast_cpow_of_pos (show 0<K j by omega),
    show (rho+3).re=rho.re+3 by simp,
    Real.mul_rpow (by positivity : (0:ℝ)≤(K j:ℝ)^(rho.re+3)) (by positivity),
    Real.pow_rpow_inv_natCast (norm_nonneg _) hm.ne',
    ←Real.rpow_mul (by positivity : (0:ℝ)≤K j),←div_eq_mul_inv,dist_eq_norm]

end RHTower.DeletionMixedRefinement
