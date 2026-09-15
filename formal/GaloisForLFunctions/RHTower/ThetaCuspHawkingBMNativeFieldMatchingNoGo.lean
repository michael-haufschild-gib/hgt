import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullCanonicalSourceEncodingNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalRetardedIdentity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceHermitianCurrent
import GaloisForLFunctions.RHTower.ZetaTrivialZeroSimple

/-! Original retarded-field amplitude recovery and literal-carrier matching obstruction. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMNativeFieldMatching
open D4BMJointSource D4BMModularCore D4BMGlobalAngularResponse D4BMLaplaceRadial
open D4BMOriginalCausalPotential D4BMOriginalRetardedIdentity
noncomputable section
set_option autoImplicit false


private theorem lambda_completed (z : ℂ) (hz : z.im ≠ 0) :
    reflectedCompletedLambda z = completedRiemannZeta z := by
  have h0 : z ≠ 0 := by intro h; exact hz (by rw [h]; rfl)
  rw [reflectedCompletedLambda, riemannZeta_def_of_ne_zero h0]
  exact mul_div_cancel₀ _ (gammaR_ne_zero_of_im_ne hz)

private theorem principal_expansion (q : XiZeroCopy) (y : ℝ) :
    principal (center q) ![0,y] =
      reflectedCompletedLambda (2*(q.1:ℂ)-1)*power (1-(q.1:ℂ)) y+
      reflectedCompletedLambda (2*(q.1:ℂ))*power (q.1:ℂ) y := by
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantCoefficient,
    d4BMCompletedEisensteinCuspConstantMaassFactor,d4BMCompletedEisensteinCuspWeylExponent,
    d4BMCuspSign,D4BMGlobalAngularResponse.center,Bool.false_eq_true,↓reduceIte,mul_one,Matrix.cons_val_one,
    Matrix.cons_val_zero,power]
  congr 2 <;> ring

/-- The original scalar source is nonzero somewhere at every actual Xi copy. -/
theorem exists_original_scalar_ne_zero (q : XiZeroCopy) :
    ∃ X y : ℝ, 0<y ∧ scalar (center q) ![X,y] ≠ 0 := by
  by_contra! h
  have hp (y : ℝ) (hy : 0<y) :
      reflectedCompletedLambda (2*(q.1:ℂ)-1)*power (1-(q.1:ℂ)) y+
      reflectedCompletedLambda (2*(q.1:ℂ))*power (q.1:ℂ) y = 0 := by
    have hm := mean_scalar (center q) hy
    rw [principal_expansion] at hm
    have he : (fun X => scalar (center q) ![X,y]) = fun _ => 0 := funext (fun X => h X y hy)
    rw [he] at hm
    simpa [D4BMCuspProjection.mean] using hm.symm
  let A := reflectedCompletedLambda (2*(q.1:ℂ)-1)
  let B := reflectedCompletedLambda (2*(q.1:ℂ))
  have h0 : A+B=0 := by simpa [A,B,power] using hp 1 (by norm_num)
  have hd := ((power_derivatives (1-(q.1:ℂ)) (by norm_num : (0:ℝ)<1)).1.const_mul A).add
    ((power_derivatives (q.1:ℂ) (by norm_num : (0:ℝ)<1)).1.const_mul B)
  have he : (fun y => A*power (1-(q.1:ℂ)) y+B*power (q.1:ℂ) y) =ᶠ[𝓝 (1:ℝ)]
      (fun _ => 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0:ℝ)<1)] with y hy
    exact hp y hy
  have hd0 := hd.congr_of_eventuallyEq he.symm
  have h1 : A*(1-(q.1:ℂ))+B*(q.1:ℂ)=0 := by
    simpa [powerFirst,power] using hd0.unique (hasDerivAt_const (1:ℝ) (0:ℂ))
  have hr : 2*(q.1:ℂ)-1 ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    norm_num at hi
    exact xi_divisor_support_im_ne_zero q.1 hi
  have hA : A=0 := by
    apply (mul_eq_zero.mp (show A*(2*(q.1:ℂ)-1)=0 by linear_combination (q.1:ℂ)*h0-h1)).resolve_right hr
  have hB : B=0 := by linear_combination h0-hA
  have hi : (2*(q.1:ℂ)).im ≠ 0 := by simpa using xi_divisor_support_im_ne_zero q.1
  have hi' : (2*(q.1:ℂ)-1).im ≠ 0 := by simpa using hi
  rcases le_total (1/2:ℝ) (q.1:ℂ).re with hq | hq
  · have hn := completedRiemannZeta_ne_zero_of_one_le_re (s:=2*(q.1:ℂ)) (by
      norm_num [Complex.mul_re]; linarith)
    exact hn ((lambda_completed _ hi).symm.trans hB)
  · have hn := completedRiemannZeta_ne_zero_of_one_le_re (s:=1-(2*(q.1:ℂ)-1)) (by
      norm_num [Complex.mul_re]; linarith)
    rw [completedRiemannZeta_one_sub] at hn
    exact hn ((lambda_completed _ hi').symm.trans hA)

private theorem source_constant_ne_zero (q : XiZeroCopy) (br : Bool) :
    (5*physicalRate q br^2+15*physicalRate q br+4)/4 ≠ (0:ℂ) := by
  have hs : -2 < (physicalRate q br).re ∧ (physicalRate q br).re < -1 := by
    have hq := xi_divisor_support_re_mem_open_unit q.1
    cases br <;> norm_num [physicalRate] <;> constructor <;> linarith
  have hm := mul_neg_of_neg_of_pos (show (physicalRate q br).re+1<0 by linarith)
    (show 0<(physicalRate q br).re+2 by linarith)
  intro hz
  have hh := congrArg Complex.re hz
  norm_num [Complex.div_re,Complex.mul_re,pow_two] at hh
  nlinarith [sq_nonneg (physicalRate q br).im]

theorem timeOriginalForcing_quadratic (q : XiZeroCopy) (br : Bool) (a : ℂ)
    (τ t : ℝ) (z : Fin 2 → ℝ) :
    timeOriginalForcing q br a τ t z = a^2*timeOriginalForcing q br 1 τ t z := by
  unfold timeOriginalForcing D4BMJointSource.originalForcing sourceAmplitude
  ring

/-- Every original Xi source forces the physical interior, with the fixed onset retained. -/
theorem exists_original_forcing_ne_zero (q : XiZeroCopy) (br : Bool) :
    ∃ t X k : ℝ, t<0 ∧ timeOriginalForcing q br 1 (2-t) t ![X,Real.exp k] ≠ 0 := by
  obtain ⟨X,y,hy,hscalar⟩ := exists_original_scalar_ne_zero q
  let z : Fin 2 → ℝ := ![X,y]
  let J := fullSquarePotential q z
  let K := fullGradientEnergy q z/2
  let s := physicalRate q br
  have hJ : J ≠ 0 := by
    dsimp only [J,fullSquarePotential,z]
    exact mul_ne_zero (by norm_num) (mul_ne_zero hscalar hscalar)
  let P : ℝ → ℂ := fun t => ((5*s^2+15*s+4)/4)*J+
    s*(s-1)*(radialUnit t:ℂ)^2/4*((s+2)^2*J-K)
  have hP0 : P 0 ≠ 0 := by
    simpa [P,radialUnit] using mul_ne_zero (source_constant_ne_zero q br) hJ
  have hP : ContinuousAt P 0 := by
    have hu := (radialUnit_hasDerivAt 0).continuousAt
    dsimp only [P]
    fun_prop
  have hev : ∀ᶠ t in 𝓝[<] (0:ℝ), t<0 ∧ P t≠0 := by
    filter_upwards [self_mem_nhdsWithin,
      (hP.eventually_ne hP0).filter_mono nhdsWithin_le_nhds] with t ht hpt
    exact ⟨ht,hpt⟩
  obtain ⟨t,ht,hpt⟩ := hev.exists
  have hu := radialUnit_bounds t ht
  have hu0 : (radialUnit t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu.1)
  have hweight : 1-(radialUnit t:ℂ)^2 ≠ 0 := by
    have h : (1:ℝ)-(radialUnit t)^2>0 := by nlinarith
    exact_mod_cast (ne_of_gt h)
  have hA : sourceAmplitude s 0 1 1 t ≠ 0 := by
    simpa [sourceAmplitude] using power_ne_zero (2*s) (radialUnit_add_one_pos t)
  have hF : D4BMJointSource.originalForcing s 0 1 1 J K t ≠ 0 := by
    change -2*(1-(radialUnit t:ℂ)^2)*(radialUnit t:ℂ)*sourceAmplitude s 0 1 1 t*P t ≠ 0
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hweight) hu0) hA) hpt
  refine ⟨t,X,Real.log y,ht,?_⟩
  rw [Real.exp_log hy]
  change D4BMJointSource.originalForcing s 0 1 1 J K t*timeOnset (2*s) ((2-t)+t) ≠ 0
  rw [show (2-t)+t=2 by ring,timeOnset,Real.smoothTransition.one_of_one_le (by norm_num)]
  simpa only [Complex.ofReal_one,one_mul] using mul_ne_zero hF (Complex.exp_ne_zero _)

private theorem forcing_eq_of_potential_eq (q : XiZeroCopy) (br : Bool) (a b : ℂ)
    (he : ∀ p r : ℝ, 0<p → p<r → ∀ X k : ℝ,
      originalPotential q br a p r X k=originalPotential q br b p r X k)
    (p r : ℝ) (hp : 0<p) (hpr : p<r) (X k : ℝ) :
    timeOriginalForcing q br a ((p+r)/2) ((p-r)/2) ![X,Real.exp k]=
      timeOriginalForcing q br b ((p+r)/2) ((p-r)/2) ![X,Real.exp k] := by
  have hd : deriv (fun v => deriv (fun u => originalPotential q br a u v X k) p) r=
      deriv (fun v => deriv (fun u => originalPotential q br b u v X k) p) r := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds hpr] with v hv
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds (show p∈Ioo 0 v from ⟨hp,hv⟩)] with u hu
    exact he u v hu.1 hu.2 X k
  have hangular : originalPotential q br a p r=originalPotential q br b p r :=
    funext (fun X => funext (fun k => he p r hp hpr X k))
  have ha := originalPotential_wave q br a hp hpr.le X k
  have hb := originalPotential_wave q br b hp hpr.le X k
  rw [hd,hangular] at ha
  exact ha.symm.trans hb


/-- The original wave operator supplies a local, amplitude-independent observation
that recovers the full squared source amplitude at every Xi copy. -/
theorem exists_originalPotential_amplitude_observation (q : XiZeroCopy) (br : Bool) :
    ∃ r X k : ℝ, 2<r ∧ ∃ c : ℂ, c≠0 ∧ ∀ a : ℂ,
      (4*deriv (fun v => deriv (fun u => originalPotential q br a u v X k) 2) r-
        angularLaplacian (originalPotential q br a 2 r) X k/
          (Real.cosh ((2-r)/2):ℂ)^2)/c = a^2 := by
  obtain ⟨t,X,k,ht,hF⟩ := exists_original_forcing_ne_zero q br
  refine ⟨2-2*t,X,k,by linarith,timeOriginalForcing q br 1 (2-t) t ![X,Real.exp k],hF,?_⟩
  intro a
  rw [originalPotential_wave q br a (by norm_num) (by linarith),
    show (2+(2-2*t))/2=2-t by ring,show (2-(2-2*t))/2=t by ring,
    timeOriginalForcing_quadratic q br a,mul_div_cancel_right₀ _ hF]

/-- Complete physical retarded fields distinguish exactly squared source amplitudes. -/
theorem originalPotential_amplitude_fibres (q : XiZeroCopy) (br : Bool) (a b : ℂ) :
    (∀ p r : ℝ, 0<p → p<r → ∀ X k : ℝ,
      originalPotential q br a p r X k=originalPotential q br b p r X k) ↔ a^2=b^2 := by
  constructor
  · intro he
    obtain ⟨t,X,k,ht,hF⟩ := exists_original_forcing_ne_zero q br
    have h := forcing_eq_of_potential_eq q br a b he 2 (2-2*t) (by norm_num) (by linarith) X k
    rw [show (2+(2-2*t))/2=2-t by ring,show (2-(2-2*t))/2=t by ring,
      timeOriginalForcing_quadratic q br a,timeOriginalForcing_quadratic q br b] at h
    exact mul_right_cancel₀ hF h
  · intro hab p r hp hpr X k
    have hsource : timeOriginalForcing q br a=timeOriginalForcing q br b := by
      funext τ t z
      rw [timeOriginalForcing_quadratic q br a,timeOriginalForcing_quadratic q br b,hab]
    let pN : NNReal := ⟨p,hp.le⟩
    let wN : NNReal := ⟨r-p,(sub_pos.mpr hpr).le⟩
    have ha := originalPotential_eq_retarded q br a pN wN X k
    have hb := originalPotential_eq_retarded q br b pN wN X k
    rw [hsource] at ha
    have h := ha.trans hb.symm
    change originalPotential q br a p (p+(r-p)) X k=originalPotential q br b p (p+(r-p)) X k at h
    rw [show p+(r-p)=r by ring] at h
    exact h

/-- The unchanged source carrier cannot determine the original causal potential,
even if only nonzero amplitudes and the open physical wedge are requested. -/
theorem not_exists_originalPotential_source_decoder :
    ¬ ∃ decode : XiZeroCopy → HBXiPeierlsCarrier → ℝ → ℝ → ℝ → ℝ → ℂ,
      ∀ (q : XiZeroCopy) (a : ℂ), a≠0 → ∀ p r : ℝ, 0<p → p<r → ∀ X k : ℝ,
        decode q (hbXiPeierlsPlusSource a q) p r X k=originalPotential q true a p r X k := by
  rintro ⟨decode,h⟩
  obtain ⟨q,hq,_⟩ := exists_critical_canonicalQNMValue_ne_zero
  have he : ∀ p r : ℝ, 0<p → p<r → ∀ X k : ℝ,
      originalPotential q true 1 p r X k=originalPotential q true 2 p r X k := by
    intro p r hp hpr X k
    have h1 := h q 1 one_ne_zero p r hp hpr X k
    have h2 := h q 2 (by norm_num) p r hp hpr X k
    rw [hbXiPeierlsPlusSource_critical_amplitudes q hq 1] at h1
    rw [hbXiPeierlsPlusSource_critical_amplitudes q hq 2] at h2
    exact h1.symm.trans h2
  have hz := (originalPotential_amplitude_fibres q true 1 2).mp he
  norm_num at hz

end
end RHTower.D4BMNativeFieldMatching
