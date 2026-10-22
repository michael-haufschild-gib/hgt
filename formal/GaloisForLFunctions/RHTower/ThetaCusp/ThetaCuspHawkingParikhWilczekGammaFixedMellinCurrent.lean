import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaMobiusMellinBridge
import GaloisForLFunctions.RHTower.ChronologicalWeightedMellin
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology Asymptotics
noncomputable section

def pwGammaRayLogCurrent (x : ℝ) : ℂ := -(Real.log x:ℂ)*pwGammaRaySource x

def pwGammaMobiusFixedMellinCurrent (z : ℂ) (x : ℝ) : ℂ :=
  pwGammaMobiusTiltCurrent z x-(Real.log x:ℂ)*pwGammaMobiusTilt z x

private theorem pwGamma_log_exp_mellin {s : ℂ} (hs : 0<s.re) :
    MellinConvergent (fun x : ℝ => (Real.log x:ℂ)*(Real.exp (-x):ℂ)) s := by
  have h := (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ)
    (f := fun x => (Real.exp (-x):ℂ)) (a := s.re+1) (b := 0) ?_ ?_ (lt_add_one _) ?_ hs).1
  · simpa only [← Complex.coe_smul,smul_eq_mul] using h
  · exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousOn.locallyIntegrableOn measurableSet_Ioi
  · rw [← isBigO_norm_left]
    simp_rw [Complex.norm_real,isBigO_norm_left]
    simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
  · simp_rw [neg_zero,Real.rpow_zero]
    refine isBigO_const_of_tendsto (?_ : Tendsto _ _ (𝓝 (1:ℂ))) one_ne_zero
    rw [(by simp : (1:ℂ)=(Real.exp (-0):ℂ))]
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousWithinAt

private theorem pwGamma_log_mellin_point (s : ℂ) {x : ℝ} (hx : 0<x) :
    (x:ℂ)^(s-1)*pwGammaRayLogCurrent x =
      -((x:ℂ)^((s+1/2)-1)*((Real.log x:ℂ)*(Real.exp (-x):ℂ))) := by
  rw [pwGammaRayLogCurrent,pwGammaRaySource_eq hx,Complex.ofReal_mul,
    Real.sqrt_eq_rpow,Complex.ofReal_cpow hx.le]
  rw [show (s+(1:ℂ)/2)-1=(s-1)+(1/2:ℝ) by push_cast;ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
  ring

theorem pwGammaRayLogCurrent_mellinConvergent {s : ℂ} (hs : -(1/2:ℝ)<s.re) :
    MellinConvergent pwGammaRayLogCurrent s := by
  have hp : 0<(s+(1:ℂ)/2).re := by simp only [Complex.add_re,Complex.div_ofNat_re,Complex.one_re];linarith
  have hi : IntegrableOn (fun x : ℝ => -((x:ℂ)^((s+1/2)-1)*
      ((Real.log x:ℂ)*(Real.exp (-x):ℂ)))) (Ioi 0) := (pwGamma_log_exp_mellin hp).neg
  exact hi.congr_fun (fun x hx => (pwGamma_log_mellin_point s hx).symm) measurableSet_Ioi

theorem pwGammaRayLogCurrent_mellin {s : ℂ} (hs : -(1/2:ℝ)<s.re) :
    mellin pwGammaRayLogCurrent s = -deriv Complex.Gamma (s+1/2) := by
  have hp : 0<(s+(1:ℂ)/2).re := by simp only [Complex.add_re,Complex.div_ofNat_re,Complex.one_re];linarith
  have hg := Complex.hasDerivAt_GammaIntegral hp
  have he : Complex.Gamma =ᶠ[𝓝 (s+1/2)] Complex.GammaIntegral := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp] with y hy
    exact Complex.Gamma_eq_integral hy
  have hd := (hg.congr_of_eventuallyEq he).deriv
  unfold mellin
  simp only [smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGamma_log_mellin_point s hx),integral_neg]
  rw [hd]

theorem pwGammaMobiusFixedMellinCurrent_weighted_source (z : ℂ) {x : ℝ} (hx : 0<x) :
    chronologicalMobiusWeightedSource (fun t : ℝ => (t:ℂ)^(-z)*pwGammaRayLogCurrent t) x =
      (x:ℂ)^(-z)*pwGammaMobiusFixedMellinCurrent z x := by
  have hM := pwGammaMobiusTilt_summable z hx
  have hC := pwGammaMobiusTiltCurrent_summable z hx
  unfold chronologicalMobiusWeightedSource pwGammaMobiusFixedMellinCurrent
  rw [mul_sub,pwGammaMobiusTiltCurrent_eq_global_atoms,pwGammaMobiusTilt_eq_global_atoms,
    ← tsum_mul_left,← tsum_mul_left,← tsum_mul_left,← Summable.tsum_sub]
  · apply tsum_congr
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [pwGammaRayLogCurrent,pwGammaMobiusGlobalAtom,pwGammaMobiusGlobalCurrentAtom]
    · have hnr : (0:ℝ)<n := by exact_mod_cast hn
      have hnc : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
      have he : Complex.exp (-z*(Real.log (n:ℝ):ℂ))=(n:ℂ)^(-z) := by
        rw [Complex.cpow_def_of_ne_zero hnc,Complex.ofReal_log hnr.le]
        push_cast
        congr 1
        ring
      simp only [pwGammaRayLogCurrent,pwGammaMobiusGlobalCurrentAtom,pwGammaMobiusGlobalAtom]
      rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hnr.le hx.le,Real.log_mul hnr.ne' hx.ne',he]
      push_cast
      ring
  · exact (hC.mul_left _)
  · exact ((hM.mul_left _).mul_left _)

theorem pwGammaMobiusFixedMellinCurrent_hasMellin {z s : ℂ}
    (hs : -(1/2:ℝ)<s.re) (hu : 1<(z+s).re) :
    HasMellin (pwGammaMobiusFixedMellinCurrent z) s
      (-deriv Complex.Gamma (s+1/2)*(riemannZeta (z+s))⁻¹) := by
  let W : ℝ → ℂ := fun x => (x:ℂ)^(-z) • pwGammaRayLogCurrent x
  have hw : MellinConvergent W (z+s) := by
    apply MellinConvergent.cpow_smul.mpr
    rw [show (z+s)+(-z)=s by ring]
    exact pwGammaRayLogCurrent_mellinConvergent hs
  have h := chronologicalMobiusWeightedSource_hasMellin W hu hw
  have he (x : ℝ) (hx : 0<x) :
      (x:ℂ)^((z+s)-1)*chronologicalMobiusWeightedSource W x =
        (x:ℂ)^(s-1)*pwGammaMobiusFixedMellinCurrent z x := by
    dsimp only [W,smul_eq_mul]
    rw [pwGammaMobiusFixedMellinCurrent_weighted_source z hx,← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 2
    ring
  have hW : mellin W (z+s)=mellin pwGammaRayLogCurrent s := by
    rw [show W=(fun x : ℝ => (x:ℂ)^(-z) • pwGammaRayLogCurrent x) from rfl,
      mellin_cpow_smul]
    congr 1
    ring
  refine ⟨?_,?_⟩
  · exact h.1.congr_fun (fun x hx => he x hx) measurableSet_Ioi
  · calc
      _ = mellin (chronologicalMobiusWeightedSource W) (z+s) :=
        setIntegral_congr_fun measurableSet_Ioi (fun x hx => (he x hx).symm)
      _ = _ := by rw [h.2,hW,pwGammaRayLogCurrent_mellin hs]

theorem pwGammaMobiusFixedMellinCurrent_source_hasDerivAt (z u : ℂ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (fun b : ℂ => (x:ℂ)^(u-b-1)*pwGammaMobiusTilt b x)
      ((x:ℂ)^(u-z-1)*pwGammaMobiusFixedMellinCurrent z x) z := by
  have hp := (((hasDerivAt_const z u).sub (hasDerivAt_id z)).sub_const 1).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have h := hp.mul (pwGammaMobiusTilt_hasDerivAt z hx)
  apply h.congr_deriv
  dsimp only [Pi.sub_apply,id_eq]
  simp only [pwGammaMobiusFixedMellinCurrent,zero_sub,neg_mul,mul_neg,
    Complex.ofReal_log hx.le]
  ring

theorem pwGammaMobiusFixedMellinCurrent_normalized_hasMellin {z s : ℂ}
    (hs : -(1/2:ℝ)<s.re) (hu : 1<(z+s).re) :
    HasMellin (fun x => Complex.Gamma (s+1/2)*pwGammaMobiusFixedMellinCurrent z x+
      deriv Complex.Gamma (s+1/2)*pwGammaMobiusTilt z x) s 0 := by
  have hc := pwGammaMobiusFixedMellinCurrent_hasMellin hs hu
  have hm := pwGammaMobiusTilt_mellinConvergent hs hu
  have hh := hasMellin_add (hc.1.const_smul (Complex.Gamma (s+1/2)))
    (hm.const_smul (deriv Complex.Gamma (s+1/2)))
  refine ⟨hh.1,?_⟩
  change mellin (fun x => Complex.Gamma (s+1/2) • pwGammaMobiusFixedMellinCurrent z x+
    deriv Complex.Gamma (s+1/2) • pwGammaMobiusTilt z x) s=0
  rw [hh.2,mellin_const_smul,mellin_const_smul,hc.2,pwGammaMobiusTilt_mellin hs hu]
  simp only [smul_eq_mul]
  ring

end
end RHTower
