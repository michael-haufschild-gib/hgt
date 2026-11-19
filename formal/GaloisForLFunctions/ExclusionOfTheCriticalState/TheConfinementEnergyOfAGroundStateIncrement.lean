import GaloisForLFunctions.ExclusionOfTheCriticalState.TheModulusOfContinuityOfTheStateIsCarriedByTheWall

/-!
# Confinement energy of a ground-state increment

At the threshold the squared translation difference in the exponential weight is
`o(h)`. The Gamma form takes up the full linear energy of the increment. To see
this, compare the unweighted modulus at two lags `h` and `s = h log(1/h)`.
Below frequency `1/s` the larger lag bounds the quadratic Fourier multiplier.
Above it the Gamma multiplier is at least `log(1/s) − O(1)`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower ArithmeticPositivityTheory

private abbrev lagLoss (h r : ℝ) := 1 - Real.cos (h*r)
private abbrev logScale (h : ℝ) := Real.log (1/h)
private abbrev offset := factorialSpanGammaOffset + Real.log 2
private abbrev increment (F : ℝ → ℝ) (h u : ℝ) := F u + (-1) * F (u+h)
private abbrev sqMass (F : ℝ → ℝ) (h : ℝ) := ∫ u, (F u - F (u+h))^2

private theorem lag_multiplier_bound {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (h r : ℝ) :
    logScale s * lagLoss h r ≤ lagLoss h r * EF.gammaBracket r +
      offset * lagLoss h r + (2*(h/s)^2*logScale s) * lagLoss s r := by
  have hL : 0 ≤ logScale s := Real.log_nonneg ((le_div_iff₀ hs).2 (by simpa using hs₁))
  have hnon := one_sub_cos_mul_nonneg h r
  by_cases hr : |r| ≤ 1/s
  · have hsr : |s*r| ≤ 1 := by
      rw [abs_mul, abs_of_pos hs, ← le_div_iff₀' hs]
      exact hr
    have hsmall := mul_le_mul_of_nonneg_left (sq_div_four_le_one_sub_cos hsr)
      (show 0 ≤ 2*(h/s)^2 by positivity)
    have he : 2*(h/s)^2*((s*r)^2/4) = h^2/2*r^2 := by field_simp; ring
    rw [he] at hsmall
    have hb := mul_le_mul_of_nonneg_left ((one_sub_cos_mul_le_sq h r).trans hsmall) hL
    have hγ := mul_nonneg hnon (show 0 ≤ EF.gammaBracket r + offset by
      linarith only [gammaBracket_ge_neg_offset r])
    linarith only [hb, hγ]
  · have hγ := gammaBracket_ge_log_of_le_abs (one_div_pos.mpr hs) (le_of_not_ge hr)
    have hb := mul_le_mul_of_nonneg_left (show logScale s ≤ EF.gammaBracket r + offset by
      dsimp only [logScale,offset]; linarith only [hγ, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]) hnon
    have hcorr := mul_nonneg (mul_nonneg (show 0 ≤ 2*(h/s)^2 by positivity) hL)
      (one_sub_cos_mul_nonneg s r)
    linarith only [hb,hcorr]

private theorem two_lag_arch_bound {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s) (hs₁ : s ≤ 1) :
    logScale s * sqMass F h ≤ archForm (increment F h) + offset * sqMass F h +
      (2*(h/s)^2*logScale s) * sqMass F s := by
  let Φ := fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2
  have hi : Integrable Φ := integrable_norm_sq_paperFT_cx hd.integrable hd.sq
  have hj : Integrable (fun r => Φ r * EF.gammaBracket r) := hd.gamma
  have hhI := integrable_one_sub_cos_mul hi h
  have hsI := integrable_one_sub_cos_mul hi s
  have hγI := integrable_one_sub_cos_mul hj h
  let k := 2*(h/s)^2*logScale s
  have hb := integral_mono ((hhI).const_mul (logScale s))
    ((hγI.add (hhI.const_mul offset)).add (hsI.const_mul k)) (fun r => by
      have e := mul_le_mul_of_nonneg_right (lag_multiplier_bound hs hs₁ h r) (sq_nonneg ‖paperFT (cx F) r‖)
      change logScale s * (lagLoss h r * Φ r) ≤ lagLoss h r * (Φ r * EF.gammaBracket r) +
        offset * (lagLoss h r * Φ r) + k * (lagLoss s r * Φ r)
      dsimp only [Φ,k]; linarith only [e])
  rw [integral_add' (hγI.add (hhI.const_mul offset)) (hsI.const_mul k),
    integral_add' hγI (hhI.const_mul offset), integral_const_mul, integral_const_mul,
    integral_const_mul] at hb
  dsimp only [Φ,k] at hb
  rw [integral_one_sub_cos_mul_norm_sq_paperFT hd hh,
    integral_one_sub_cos_mul_norm_sq_paperFT hd hs.le,
    integral_one_sub_cos_mul_norm_sq_paperFT_mul_gammaBracket hd.integrable h] at hb
  apply le_of_mul_le_mul_left (a := Real.pi) _ Real.pi_pos
  dsimp only [sqMass,increment]
  linarith only [hb]

private theorem exp_increment_slope :
    Tendsto (fun h : ℝ => (Real.exp (8*h)-1)/h) (𝓝[>] 0) (𝓝 8) := by
  have hd := ((hasDerivAt_const_mul (x := (0:ℝ)) 8).exp).tendsto_slope_zero_right
  simpa only [zero_add,mul_zero,Real.exp_zero,one_mul,smul_eq_mul,div_eq_inv_mul] using hd

/-- The full energy of an inward translation difference has slope eight
times the confinement energy of the ground state. -/
theorem criticalState_tendsto_fullEnergy_increment_div {W : ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) :
    Tendsto (fun h : ℝ => criticalHalfLineFullEnergy W (fun u => F u + (-1)*F (u+h))/h)
      (𝓝[>] 0) (𝓝 (8 * criticalAliasCoefficient W * ∫ u : ℝ, F u^2 * Real.exp (-(8*u)))) := by
  have he := (exp_increment_slope.mul_const (criticalAliasCoefficient W)).mul_const
    (∫ u : ℝ, F u^2 * Real.exp (-(8*u)))
  refine he.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [criticalState_fullEnergy_increment hW ht hF (le_of_lt (show 0 < h from hh))]
  ring

/-- The exponential confinement contributes zero to the first-order energy of
a translation difference of the threshold ground state. -/
theorem criticalState_tendsto_weighted_sq_increment_div {W : ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) :
    Tendsto (fun h : ℝ => (∫ u, (F u - F (u+h))^2 * Real.exp (-(8*u)))/h)
      (𝓝[>] 0) (𝓝 0) := by
  let a := criticalAliasCoefficient W
  let M := ∫ u : ℝ, F u^2 * Real.exp (-(8*u))
  let Q := 8*a*M
  let D := sqMass F
  let V := fun h : ℝ => ∫ u, (F u - F (u+h))^2 * Real.exp (-(8*u))
  let N := fun h : ℝ => logScale h / h * D h
  let s := fun h : ℝ => h * logScale h
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha : 0 < a := criticalAliasCoefficient_positive hW
  have hN : Tendsto N (𝓝[>] 0) (𝓝 Q) := criticalState_tendsto_log_div_mul_sq_increment hW ht hF
  have hinv : Tendsto (fun h : ℝ => 1/h) (𝓝[>] 0) atTop := by
    simpa only [one_div] using (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  have hL : Tendsto logScale (𝓝[>] 0) atTop := Real.tendsto_log_atTop.comp hinv
  have hLi := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hL
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hs0 : Tendsto s (𝓝[>] 0) (𝓝 0) := by
    simpa [s,logScale,Function.comp_def,div_eq_mul_inv,mul_comm] using hratio.comp hinv
  have hp : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hLp := hL.eventually_gt_atTop 0
  have hsp : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < s h :=
    hp.mp (hLp.mono fun h hL' hh => mul_pos hh hL')
  have hs : Tendsto s (𝓝[>] 0) (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hs0,hsp⟩
  have hD : Tendsto (fun h => D h/h) (𝓝[>] 0) (𝓝 0) := by
    have htD := hLi.mul hN
    rw [zero_mul] at htD
    refine htD.congr' ?_
    filter_upwards [hLp] with h hL'
    change (logScale h)⁻¹ * (logScale h/h * D h) = D h/h
    field_simp [hL'.ne']
  have hlogratio : Tendsto (fun h => logScale (s h)/logScale h) (𝓝[>] 0) (𝓝 1) := by
    have hr := (tendsto_const_nhds (x := (1:ℝ))).sub (hratio.comp hL)
    rw [sub_zero] at hr
    refine hr.congr' ?_
    filter_upwards [hp,hLp] with h hh hL'
    change 1 - Real.log (logScale h)/logScale h = Real.log (1/(h*logScale h))/logScale h
    rw [one_div, Real.log_inv, Real.log_mul hh.ne' hL'.ne']
    have he : Real.log h = -logScale h := by simp [logScale, one_div]
    rw [he]; field_simp; ring
  have hmain := hlogratio.mul hN
  have hcorr := (hLi.mul (hN.comp hs)).const_mul 2
  obtain ⟨B,_,hB⟩ := criticalHalfLineFullEnergy_arch_coercive_remainder hW
  have hE := (exp_increment_slope.const_mul a).mul_const M
  let U := fun h => a*((Real.exp (8*h)-1)/h)*M + (B+offset)*(D h/h) +
    2*((logScale h)⁻¹*N (s h)) - (logScale (s h)/logScale h)*N h
  have hU : Tendsto U (𝓝[>] 0) (𝓝 0) := by
    have hu := ((hE.add (hD.const_mul (B+offset))).add hcorr).sub hmain
    simpa only [U, Q, Function.comp_apply, mul_zero, zero_mul, one_mul, add_zero,
      mul_comm a (8:ℝ), sub_self] using hu
  have hV : Tendsto (fun h => a/2*(V h/h)) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' _ _ hU
    · filter_upwards [hp] with h hh
      exact mul_nonneg (by positivity) (div_nonneg (integral_nonneg fun u =>
        mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hh.le)
    · filter_upwards [hp,hLp,hsp,hs0.eventually_le_const (show (0:ℝ) < 1 by norm_num)] with h hh hl hsh hs₁
      have hc := hB (criticalHalfLineEnergyDomain_increment hd hh.le)
      rw [criticalState_fullEnergy_increment hW ht hF hh.le] at hc
      have hb := two_lag_arch_bound hd hh.le hsh hs₁
      simp only [neg_one_mul,← sub_eq_add_neg] at hc
      change archForm (fun u => F u - F (u+h)) + a/2*V h ≤
        a*(Real.exp (8*h)-1)*M+B*D h at hc
      change logScale (s h)*D h ≤ archForm (fun u => F u + (-1)*F (u+h)) +
        offset*D h + (2*(h/s h)^2*logScale (s h))*D (s h) at hb
      simp only [neg_one_mul,← sub_eq_add_neg] at hb
      have hslope : h*U h = a*(Real.exp (8*h)-1)*M + (B+offset)*D h +
          2*(h/s h)^2*logScale (s h)*D (s h) - logScale (s h)*D h := by
        dsimp only [U,N,s]; field_simp [hh.ne',hl.ne']
      apply le_of_mul_le_mul_left (a := h) _ hh
      rw [hslope, show h*(a/2*(V h/h)) = a/2*V h by field_simp]
      linarith only [hc,hb]
  have hf := hV.const_mul (a/2)⁻¹
  simpa only [mul_zero, ← mul_assoc,inv_mul_cancel₀ (div_pos ha (by norm_num : (0:ℝ)<2)).ne',
    one_mul] using hf

#print axioms criticalState_tendsto_fullEnergy_increment_div
#print axioms criticalState_tendsto_weighted_sq_increment_div

end GaloisForLFunctions.ExclusionOfTheCriticalState
