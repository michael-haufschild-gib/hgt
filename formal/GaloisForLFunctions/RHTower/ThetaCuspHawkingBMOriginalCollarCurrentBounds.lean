import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCharacteristicTransform
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCornerForcing

/-!
# Original source-current and radial-reader horizon errors

The original causal scalar retains its arithmetic coefficient and onset lift.
On the physical collar, genuine ingoing-time differentiation adds both null
partials; the lift's radial derivative terms cancel. Its value and time slope
approach their actual horizon traces at one uniform geometric rate.

The unchanged normalizable reader retains both exact horizon branches. Combining
its error with the original scalar-current slot and the full forcing gives
exponentially decaying remainders throughout their convergence half-planes.
The forcing estimate is pointwise in the angular variable. Complete angular
finite-part assembly and the unbounded temporal/metric/QNM comparison remain open.
-/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalCollarCurrentBounds
open D4BMJointSource D4BMModularCore D4BMOriginalCausalAdmission
open D4BMOriginalHorizonTimeTrace D4BMOriginalCharacteristicTransform
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private theorem reader_re_nonneg (q : XiZeroCopy) :
    0 ≤ (D4BMOriginalCirclePeriod.readerExponent q).re := by
  have hr := (xi_divisor_support_re_mem_open_unit q.1).2
  norm_num [D4BMOriginalCirclePeriod.readerExponent]
  linarith

private theorem unit_collar_limit :
    Tendsto (fun L : ℝ => radialUnit (-L/2)) atTop (𝓝 (1:ℝ)) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have hform (L : ℝ) : radialUnit (-L/2)=(1-Real.exp (-L))/(1+Real.exp (-L)) := by
    apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (-L)))).mpr
    have h := radialUnit_one_sub (-L/2)
    rw [show 2*(-L/2) = -L by ring] at h
    nlinarith
  simp_rw [hform]
  convert! (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he)
    (by norm_num : (1:ℝ)+0 ≠ 0) using 1
  norm_num

private def liftProfile (s amp : ℂ) (u : ℝ) : ℂ :=
  (-s*(s-1)/4)*(D4BMLaplaceRadial.power (2*s) (1+u)*amp^2*(u:ℂ)^3)

private theorem differentiable_unit_collar_error (F : ℝ → ℂ) (hd : DifferentiableAt ℝ F 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop,
      ‖F (radialUnit (-L/2))-F 1‖ ≤ B*Real.exp (-L) := by
  obtain ⟨B,hB,hb⟩ := hd.isBigO_sub.exists_pos
  refine ⟨2*B,by positivity,?_⟩
  filter_upwards [unit_collar_limit.eventually hb.bound,eventually_gt_atTop (0:ℝ)] with L h hL
  have hu := (radialUnit_bounds (-L/2) (by linarith)).2
  have he := radialUnit_one_sub (-L/2)
  rw [show 2*(-L/2) = -L by ring] at he
  have hn : ‖radialUnit (-L/2)-(1:ℝ)‖ = 1-radialUnit (-L/2) := by
    rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hu.le)]
    ring
  rw [hn,he] at h
  apply h.trans
  calc
    _ ≤ B*(Real.exp (-L)*2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith : 1+radialUnit (-L/2) ≤ 2)
        (Real.exp_nonneg _)) hB.le
    _ = _ := by ring

/-- The unchanged lift approaches its horizon coefficient at the geometric collar rate. -/
theorem lift_coefficient_error (s amp : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop,
      ‖liftCoefficient s amp L-liftHorizon s amp‖ ≤ B*Real.exp (-L) := by
  have hp := ((D4BMLaplaceRadial.power_derivatives (2*s)
    (by norm_num : 0 < 1+(1:ℝ))).1.scomp 1
      ((hasDerivAt_id (1:ℝ)).const_add 1)).differentiableAt
  have hd : DifferentiableAt ℝ (liftProfile s amp) 1 := by
    unfold liftProfile
    fun_prop
  simpa only [liftProfile,liftCoefficient,radialLift,sourceAmplitude,zero_mul,
    Complex.exp_zero,one_mul,mul_one,one_add_one_eq_two,Complex.ofReal_one,one_pow,
    liftHorizon] using differentiable_unit_collar_error (liftProfile s amp) hd

/-- The full scalar along the actual collar; its lift radius stays fixed as time varies. -/
theorem original_scalar_on_collar (q : XiZeroCopy) (br : Bool) (amp : ℂ) (L p : ℝ) :
    originalScalar q br amp p (p+L) = physicalSelfSourceCoefficient q*
      (collarValue (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp L p+
        liftCoefficient (physicalRate q br) amp L*timeOnset (2*physicalRate q br) p) := by
  simp only [originalScalar,D4BMOriginalCausalPotential.nullLift,liftCoefficient,collarValue,
    show (p-(p+L))/2 = -L/2 by ring]

/-- Genuine ingoing-time differentiation retains both null derivatives and cancels lift-radius jets. -/
theorem original_collar_hasDerivAt (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    {L p : ℝ} (hL : 0 < L) (hp : 0 < p) :
    HasDerivAt (fun a => originalScalar q br amp a (a+L))
      (physicalSelfSourceCoefficient q*
        (collarFirst (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp L p+
         collarSecond (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp L p+
         liftCoefficient (physicalRate q br) amp L*timeOnsetFirst (2*physicalRate q br) p)) p := by
  simp_rw [original_scalar_on_collar]
  exact ((collarValue_hasDerivAt_time _ _ _ hp hL).add
    ((timeOnset_hasDerivAt (2*physicalRate q br) p).const_mul
      (liftCoefficient (physicalRate q br) amp L))).const_mul (physicalSelfSourceCoefficient q)

private theorem reduced_collar_error (q : XiZeroCopy) (br : Bool) (amp m : ℂ)
    (hm : 0 ≤ m.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L p : ℝ, 0 < L → 0 < p →
      ‖collarValue (-m) (physicalRate q br) amp L p-reducedTrace q br amp m p‖+
      ‖collarFirst (-m) (physicalRate q br) amp L p+
        collarSecond (-m) (physicalRate q br) amp L p-reducedSlope q br amp m p‖ ≤
        B*Real.exp (-L)*Real.exp (m.re*p) := by
  obtain ⟨C,hC,h⟩ := physical_null_horizon_traces q br amp m hm
  obtain ⟨D,hD,hd⟩ := physical_null_derivatives_bound q br amp m hm
  refine ⟨2*C+D,by positivity,?_⟩
  intro L p hL hp
  obtain ⟨H,Hp,hH,hHp,hb⟩ := h p hp
  have htrace : reducedTrace q br amp m p=H := hH.limUnder_eq
  have hslope : reducedSlope q br amp m p=Hp := hHp.limUnder_eq
  have hpr : p ≤ p+L := by linarith
  have hr : 0 < p+L := by linarith
  have hf := (original_null_first (-m) (physicalRate q br) amp hp hr.le).deriv
  have hs := (original_null_second (-m) (physicalRate q br) amp hp.le hr).deriv
  have hv := (hb (p+L) hpr).1
  have hvp := (hb (p+L) hpr).2
  have hvr := (hd p (p+L) hp hpr).2.1
  rw [hf] at hvp
  rw [hs] at hvr
  have herr : p-(p+L) = -L := by ring
  rw [herr] at hv hvp hvr
  have hv' : ‖collarValue (-m) (physicalRate q br) amp L p-H‖ ≤
      C*Real.exp (-L)*Real.exp (m.re*p) := by
    simpa only [collarValue,norm_sub_rev] using hv
  have hvp' : ‖collarFirst (-m) (physicalRate q br) amp L p-Hp‖ ≤
      C*Real.exp (-L)*Real.exp (m.re*p) := by
    simpa only [collarFirst,nullFirst,norm_sub_rev] using hvp
  have hvr' : ‖collarSecond (-m) (physicalRate q br) amp L p‖ ≤
      D*Real.exp (-L)*Real.exp (m.re*p) := hvr
  rw [htrace,hslope]
  calc
    _ ≤ ‖collarValue (-m) (physicalRate q br) amp L p-H‖+
        (‖collarFirst (-m) (physicalRate q br) amp L p-Hp‖+
          ‖collarSecond (-m) (physicalRate q br) amp L p‖) := by
      apply add_le_add le_rfl
      rw [show collarFirst (-m) (physicalRate q br) amp L p+
          collarSecond (-m) (physicalRate q br) amp L p-Hp =
          (collarFirst (-m) (physicalRate q br) amp L p-Hp)+
            collarSecond (-m) (physicalRate q br) amp L p by ring]
      exact norm_add_le _ _
    _ ≤ _ := by nlinarith

private theorem onset_pair_bounded (q : XiZeroCopy) (br : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ,
      ‖timeOnset (2*physicalRate q br) p‖+‖timeOnsetFirst (2*physicalRate q br) p‖ ≤ B := by
  have hr := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hr
  obtain ⟨B,hB,h⟩ := timeOnset_pair_bound (2*physicalRate q br) 0 (by linarith)
  refine ⟨B,hB,?_⟩
  simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one] using h

/-- One source-derived bound controls the value and genuine time-derivative horizon errors
for all positive ingoing times, uniformly on all sufficiently long collars. -/
theorem original_collar_value_slope_error (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p : ℝ, 0 < p →
      ‖originalScalar q br amp p (p+L)-horizonTrace q br amp p‖+
      ‖deriv (fun a => originalScalar q br amp a (a+L)) p-horizonSlope q br amp p‖ ≤
        B*Real.exp (-L)*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p) := by
  let m := D4BMOriginalCirclePeriod.readerExponent q
  let s := physicalRate q br
  let C := physicalSelfSourceCoefficient q
  obtain ⟨A,hA,ha⟩ := reduced_collar_error q br amp m (reader_re_nonneg q)
  obtain ⟨B,hB,hb⟩ := lift_coefficient_error s amp
  obtain ⟨D,hD,hd⟩ := onset_pair_bounded q br
  refine ⟨‖C‖*(A+B*D),by positivity,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with L hLerr hL p hp
  let V := collarValue (-m) s amp L p-reducedTrace q br amp m p
  let P := collarFirst (-m) s amp L p+collarSecond (-m) s amp L p-reducedSlope q br amp m p
  let E := liftCoefficient s amp L-liftHorizon s amp
  let O := timeOnset (2*s) p
  let O' := timeOnsetFirst (2*s) p
  have hvalue : originalScalar q br amp p (p+L)-horizonTrace q br amp p=C*(V+E*O) := by
    rw [original_scalar_on_collar,horizonTrace]
    dsimp only [C,V,E,O,m,s]
    ring
  have hslope : deriv (fun a => originalScalar q br amp a (a+L)) p-horizonSlope q br amp p=
      C*(P+E*O') := by
    rw [(original_collar_hasDerivAt q br amp hL hp).deriv,D4BMOriginalHorizonTimeTrace.horizonSlope]
    dsimp only [C,P,E,O',m,s]
    ring
  have hvp : ‖V‖+‖P‖ ≤ A*Real.exp (-L)*Real.exp (m.re*p) := ha L p hL hp
  have he : ‖E‖ ≤ B*Real.exp (-L) := hLerr
  have ho : ‖O‖+‖O'‖ ≤ D := hd p
  have hexp : 1 ≤ Real.exp (m.re*p) := Real.one_le_exp (mul_nonneg (reader_re_nonneg q) hp.le)
  rw [hvalue,hslope,norm_mul,norm_mul]
  calc
    _ ≤ ‖C‖*(‖V‖+‖E‖*‖O‖)+‖C‖*(‖P‖+‖E‖*‖O'‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (by simpa only [norm_mul] using norm_add_le V (E*O)) (norm_nonneg C)
      · exact mul_le_mul_of_nonneg_left (by simpa only [norm_mul] using norm_add_le P (E*O')) (norm_nonneg C)
    _ = ‖C‖*((‖V‖+‖P‖)+‖E‖*(‖O‖+‖O'‖)) := by ring
    _ ≤ ‖C‖*(A*Real.exp (-L)*Real.exp (m.re*p)+(B*Real.exp (-L))*D) :=
      mul_le_mul_of_nonneg_left (add_le_add hvp
        (mul_le_mul he ho (by positivity) (by positivity))) (norm_nonneg C)
    _ ≤ ‖C‖*(A*Real.exp (-L)*Real.exp (m.re*p)+(B*Real.exp (-L))*D*Real.exp (m.re*p)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg C)
      apply add_le_add le_rfl
      exact le_mul_of_one_le_right (by positivity) hexp
    _ = _ := by ring

/-- The source slot entering the physical static current has the same integrable horizon error. -/
theorem original_collar_current_slot_error (q : XiZeroCopy) (br : Bool) (amp w : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p : ℝ, 0 < p →
      ‖(deriv (fun a => originalScalar q br amp a (a+L)) p+w*originalScalar q br amp p (p+L))-
        (horizonSlope q br amp p+w*horizonTrace q br amp p)‖ ≤
        B*Real.exp (-L)*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p) := by
  obtain ⟨B,hB,hb⟩ := original_collar_value_slope_error q br amp
  refine ⟨(1+‖w‖)*B,by positivity,?_⟩
  filter_upwards [hb] with L h p hp
  have he := h p hp
  let v := originalScalar q br amp p (p+L)-horizonTrace q br amp p
  let d := deriv (fun a => originalScalar q br amp a (a+L)) p-horizonSlope q br amp p
  have halg : (deriv (fun a => originalScalar q br amp a (a+L)) p+w*originalScalar q br amp p (p+L))-
      (horizonSlope q br amp p+w*horizonTrace q br amp p)=d+w*v := by
    dsimp only [d,v]
    ring
  rw [halg]
  calc
    _ ≤ ‖d‖+‖w‖*‖v‖ := by simpa only [norm_mul] using norm_add_le d (w*v)
    _ ≤ (1+‖w‖)*(‖v‖+‖d‖) := by nlinarith [norm_nonneg v,norm_nonneg d,norm_nonneg w]
    _ ≤ (1+‖w‖)*(B*Real.exp (-L)*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

open D4BMLaplaceRadial

private def readerProfile (w chi : ℂ) (u : ℝ) : ℂ :=
  power w (1+u)*gaussFactor w chi false ((1-u^2:ℝ):ℂ)

private theorem reader_profile_differentiable (w chi : ℂ) :
    DifferentiableAt ℝ (readerProfile w chi) 1 := by
  have hp := ((power_derivatives w (by norm_num : 0 < 1+(1:ℝ))).1.scomp 1
    ((hasDerivAt_id (1:ℝ)).const_add 1)).differentiableAt
  have hg : DifferentiableAt ℝ (fun b : ℝ => gaussFactor w chi false (b:ℂ)) (1-(1:ℝ)^2) := by
    norm_num only [one_pow,sub_self]
    exact (gaussFactor_derivatives_continued (w:=w) (chi:=chi) (z:=0) false (by simp)).1.comp_ofReal.differentiableAt
  have hc := hg.comp 1 (show DifferentiableAt ℝ (fun u : ℝ => 1-u^2) 1 by fun_prop)
  exact hp.mul hc

private theorem reader_profile_one (w chi : ℂ) : readerProfile w chi 1=power w 2 := by
  simp only [readerProfile,one_pow,sub_self,Complex.ofReal_zero,gaussFactor_zero,mul_one,one_add_one_eq_two]

private theorem reader_profile_collar_error (w chi : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop,
      ‖readerProfile w chi (radialUnit (-L/2))-power w 2‖ ≤ B*Real.exp (-L) := by
  simpa only [reader_profile_one] using
    differentiable_unit_collar_error (readerProfile w chi) (reader_profile_differentiable w chi)

private theorem horizon_profile_factor (w chi : ℂ) (x : ℝ) (hx : x < 0) :
    horizon w chi (horizonCoordinate x) = Complex.exp (w*(x:ℂ))*readerProfile w chi (radialUnit x) := by
  rw [horizon,dress,horizonPower_tortoise w x hx]
  simp only [readerProfile,horizonCoordinate,mul_assoc]

/-- Exact two-branch normalization of the unchanged outer radial reader on a physical collar. -/
private theorem normalizable_reader_collar_decomposition (w chi : ℂ) (hw : w.im ≠ 0)
    {L : ℝ} (hL : 0 < L) :
    Complex.exp (w*((-L/2:ℝ):ℂ))*tortoiseMode true w chi (-L/2) =
      horizonRegularCoefficient w chi (normalizable w chi) (normalizableFirst w chi)*
        Complex.exp (2*w*((-L/2:ℝ):ℂ))*readerProfile w chi (radialUnit (-L/2))+
      (connection w chi/(2*w))*readerProfile (-w) chi (radialUnit (-L/2)) := by
  have hx : -L/2 < 0 := by linarith
  have hz := horizonCoordinate_interior (-L/2) hx
  have hr := (original_homogeneous_horizon_representation w chi hw
    (fun b hb => (normalizable_derivatives_continued hb).1)
    (fun b hb => (normalizable_derivatives_continued hb).2)
    (fun b hb => normalizable_equation_continued hb) hz).1
  rw [normalizable_opposite_coefficient w chi hw] at hr
  have hplus : Complex.exp (w*((-L/2:ℝ):ℂ))*Complex.exp (w*((-L/2:ℝ):ℂ))=
      Complex.exp (2*w*((-L/2:ℝ):ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hminus : Complex.exp (w*((-L/2:ℝ):ℂ))*Complex.exp ((-w)*((-L/2:ℝ):ℂ))=1 := by
    rw [← Complex.exp_add,← add_mul,add_neg_cancel,zero_mul,Complex.exp_zero]
  simp only [tortoiseMode,radialMode,if_true,hr,horizon_profile_factor w chi (-L/2) hx,
    horizon_profile_factor (-w) chi (-L/2) hx]
  calc
    _ = horizonRegularCoefficient w chi (normalizable w chi) (normalizableFirst w chi)*
          (Complex.exp (w*((-L/2:ℝ):ℂ))*Complex.exp (w*((-L/2:ℝ):ℂ)))*readerProfile w chi (radialUnit (-L/2))+
        (connection w chi/(2*w))*
          (Complex.exp (w*((-L/2:ℝ):ℂ))*Complex.exp ((-w)*((-L/2:ℝ):ℂ)))*readerProfile (-w) chi (radialUnit (-L/2)) := by ring
    _ = _ := by rw [hplus,hminus,mul_one]

/-- The actual reader error retains both geometric decay and the regular horizon branch. -/
theorem normalizable_reader_collar_error (w chi : ℂ) (hw : w.im ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop,
      ‖Complex.exp (w*((-L/2:ℝ):ℂ))*tortoiseMode true w chi (-L/2)-
        (connection w chi/(2*w))*power (-w) 2‖ ≤
          B*(Real.exp (-L)+Real.exp (-w.re*L)) := by
  obtain ⟨P,hP,hp⟩ := reader_profile_collar_error w chi
  obtain ⟨M,hM,hm⟩ := reader_profile_collar_error (-w) chi
  let A := horizonRegularCoefficient w chi (normalizable w chi) (normalizableFirst w chi)
  let beta := connection w chi/(2*w)
  let K := ‖power w 2‖+P
  refine ⟨‖A‖*K+‖beta‖*M,by dsimp [K]; positivity,?_⟩
  filter_upwards [hp,hm,eventually_gt_atTop (0:ℝ)] with L hpL hmL hL
  have heL : Real.exp (-L) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show -L ≤ 0 by linarith)
  have hpbound : ‖readerProfile w chi (radialUnit (-L/2))‖ ≤ K := by
    have hn := norm_sub_norm_le (readerProfile w chi (radialUnit (-L/2))) (power w 2)
    have hh := hpL.trans (mul_le_mul_of_nonneg_left heL hP)
    dsimp only [K]
    nlinarith
  have henorm : ‖Complex.exp (2*w*((-L/2:ℝ):ℂ))‖=Real.exp (-w.re*L) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    norm_num
    ring
  rw [normalizable_reader_collar_decomposition w chi hw hL]
  change ‖A*Complex.exp (2*w*((-L/2:ℝ):ℂ))*readerProfile w chi (radialUnit (-L/2))+
    beta*readerProfile (-w) chi (radialUnit (-L/2))-beta*power (-w) 2‖ ≤ _
  rw [show A*Complex.exp (2*w*((-L/2:ℝ):ℂ))*readerProfile w chi (radialUnit (-L/2))+
      beta*readerProfile (-w) chi (radialUnit (-L/2))-beta*power (-w) 2 =
      A*Complex.exp (2*w*((-L/2:ℝ):ℂ))*readerProfile w chi (radialUnit (-L/2))+
        beta*(readerProfile (-w) chi (radialUnit (-L/2))-power (-w) 2) by ring]
  calc
    _ ≤ ‖A‖*Real.exp (-w.re*L)*‖readerProfile w chi (radialUnit (-L/2))‖+
        ‖beta‖*‖readerProfile (-w) chi (radialUnit (-L/2))-power (-w) 2‖ := by
      simpa only [norm_mul,henorm] using norm_add_le
        (A*Complex.exp (2*w*((-L/2:ℝ):ℂ))*readerProfile w chi (radialUnit (-L/2)))
        (beta*(readerProfile (-w) chi (radialUnit (-L/2))-power (-w) 2))
    _ ≤ ‖A‖*Real.exp (-w.re*L)*K+‖beta‖*(M*Real.exp (-L)) := add_le_add
      (mul_le_mul_of_nonneg_left hpbound (by positivity))
      (mul_le_mul_of_nonneg_left hmL (norm_nonneg _))
    _ ≤ _ := by
      have hK : 0 ≤ K := by dsimp [K]; positivity
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg A) hK) (Real.exp_nonneg (-L)),
        mul_nonneg (mul_nonneg (norm_nonneg beta) hM) (Real.exp_nonneg (-w.re*L))]


/-- The horizon value and its actual time derivative keep the original source growth exponent. -/
theorem original_horizon_value_slope_growth (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ, 0 < p →
      ‖horizonTrace q br amp p‖+‖D4BMOriginalHorizonTimeTrace.horizonSlope q br amp p‖ ≤
        B*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p) := by
  let m := D4BMOriginalCirclePeriod.readerExponent q
  let s := physicalRate q br
  let C := physicalSelfSourceCoefficient q
  let ell := liftHorizon s amp
  obtain ⟨A,hA,ha⟩ := reduced_trace_growth q br amp m (reader_re_nonneg q)
  obtain ⟨B,hB,hb⟩ := onset_pair_bounded q br
  refine ⟨‖C‖*(A+‖ell‖*B),by positivity,?_⟩
  intro p hp
  have he : 1 ≤ Real.exp (m.re*p) := Real.one_le_exp (mul_nonneg (reader_re_nonneg q) hp.le)
  let V := reducedTrace q br amp m p
  let P := reducedSlope q br amp m p
  let O := timeOnset (2*s) p
  let O' := timeOnsetFirst (2*s) p
  have hvp : ‖V‖+‖P‖ ≤ A*Real.exp (m.re*p) := ha p hp
  have ho : ‖O‖+‖O'‖ ≤ B := hb p
  change ‖C*(V+ell*O)‖+‖C*(P+ell*O')‖ ≤ _
  simp only [norm_mul]
  calc
    _ ≤ ‖C‖*(‖V‖+‖ell‖*‖O‖)+‖C‖*(‖P‖+‖ell‖*‖O'‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (by simpa only [norm_mul] using norm_add_le V (ell*O)) (norm_nonneg C)
      · exact mul_le_mul_of_nonneg_left (by simpa only [norm_mul] using norm_add_le P (ell*O')) (norm_nonneg C)
    _ = ‖C‖*((‖V‖+‖P‖)+‖ell‖*(‖O‖+‖O'‖)) := by ring
    _ ≤ ‖C‖*(A*Real.exp (m.re*p)+‖ell‖*B) :=
      mul_le_mul_of_nonneg_left (add_le_add hvp (mul_le_mul_of_nonneg_left ho (norm_nonneg ell))) (norm_nonneg C)
    _ ≤ ‖C‖*(A*Real.exp (m.re*p)+(‖ell‖*B)*Real.exp (m.re*p)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (le_mul_of_one_le_right (by positivity) he)) (norm_nonneg C)
    _ = _ := by ring

private theorem horizon_current_slot_growth (q : XiZeroCopy) (br : Bool) (amp w : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ, 0 < p →
      ‖D4BMOriginalHorizonTimeTrace.horizonSlope q br amp p+w*horizonTrace q br amp p‖ ≤
        B*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p) := by
  obtain ⟨B,hB,hb⟩ := original_horizon_value_slope_growth q br amp
  refine ⟨(1+‖w‖)*B,by positivity,?_⟩
  intro p hp
  have he := hb p hp
  let H := horizonTrace q br amp p
  let P := D4BMOriginalHorizonTimeTrace.horizonSlope q br amp p
  calc
    _ ≤ ‖P‖+‖w‖*‖H‖ := by simpa only [H,P,norm_mul] using norm_add_le P (w*H)
    _ ≤ (1+‖w‖)*(‖H‖+‖P‖) := by nlinarith [norm_nonneg H,norm_nonneg P,norm_nonneg w]
    _ ≤ (1+‖w‖)*(B*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

private theorem damped_reader_product_error (w chi : ℂ) (hw : w.im ≠ 0) (hwr : 0 ≤ w.re)
    (G : ℝ) (f : ℝ → ℝ → ℂ) (F : ℝ → ℂ)
    (hf : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ L : ℝ in atTop, ∀ p : ℝ, 0 < p →
      ‖f L p-F p‖ ≤ A*Real.exp (-L)*Real.exp (G*p))
    (hF : ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ, 0 < p → ‖F p‖ ≤ B*Real.exp (G*p)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p : ℝ, 0 < p →
      ‖Complex.exp (-w*(p:ℂ))*(Complex.exp (w*((-L/2:ℝ):ℂ))*
          tortoiseMode true w chi (-L/2)*f L p-
        (connection w chi/(2*w))*power (-w) 2*F p)‖ ≤
          B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(w.re-G)*p) := by
  obtain ⟨A,hA,ha⟩ := hf
  obtain ⟨B,hB,hb⟩ := hF
  obtain ⟨D,hD,hd⟩ := normalizable_reader_collar_error w chi hw
  let N := (connection w chi/(2*w))*power (-w) 2
  let K := ‖N‖+2*D
  refine ⟨K*A+D*B,by dsimp [K]; positivity,?_⟩
  filter_upwards [ha,hd,eventually_gt_atTop (0:ℝ)] with L haL hdL hL p hp
  let n := Complex.exp (w*((-L/2:ℝ):ℂ))*tortoiseMode true w chi (-L/2)
  let S := Real.exp (-L)+Real.exp (-w.re*L)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hS2 : S ≤ 2 := by
    have h1 : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : Real.exp (-w.re*L) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hwr) hL.le)
    dsimp only [S]
    linarith
  have hn : ‖n‖ ≤ K := by
    have ht := norm_sub_norm_le n N
    have hm : ‖n-N‖ ≤ D*S := hdL
    have hd2 := mul_le_mul_of_nonneg_left hS2 hD
    dsimp only [K]
    linarith
  have hnN : ‖n-N‖ ≤ D*S := hdL
  have hfp := haL p hp
  have hFp := hb p hp
  have hE : ‖Complex.exp (-w*(p:ℂ))‖=Real.exp (-w.re*p) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hnorm : ‖n*f L p-N*F p‖ ≤ (K*A+D*B)*S*Real.exp (G*p) := by
    rw [show n*f L p-N*F p=n*(f L p-F p)+(n-N)*F p by ring]
    calc
      _ ≤ ‖n‖*‖f L p-F p‖+‖n-N‖*‖F p‖ := by simpa only [norm_mul] using norm_add_le (n*(f L p-F p)) ((n-N)*F p)
      _ ≤ K*(A*Real.exp (-L)*Real.exp (G*p))+(D*S)*(B*Real.exp (G*p)) :=
        add_le_add (mul_le_mul hn hfp (norm_nonneg _) (by dsimp [K]; positivity))
          (mul_le_mul hnN hFp (norm_nonneg _) (by positivity))
      _ ≤ K*(A*S*Real.exp (G*p))+(D*S)*(B*Real.exp (G*p)) := by
        have hK : 0 ≤ K := by dsimp [K]; positivity
        have hs : Real.exp (-L) ≤ S := by
          dsimp only [S]
          exact le_add_of_nonneg_right (Real.exp_nonneg _)
        gcongr
      _ = _ := by ring
  change ‖Complex.exp (-w*(p:ℂ))*(n*f L p-N*F p)‖ ≤ _
  rw [norm_mul,hE]
  calc
    _ ≤ Real.exp (-w.re*p)*((K*A+D*B)*S*Real.exp (G*p)) := mul_le_mul_of_nonneg_left hnorm (Real.exp_nonneg _)
    _ = (K*A+D*B)*S*(Real.exp (-w.re*p)*Real.exp (G*p)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- Actual source value, actual time derivative and both branches of the physical radial reader
give one uniform error for the scalar-current slot throughout the convergence half-plane. -/
theorem original_source_reader_current_error (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im ≠ 0) (hwr : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p : ℝ, 0 < p →
      ‖Complex.exp (-w*(p:ℂ))*(Complex.exp (w*((-L/2:ℝ):ℂ))*
          tortoiseMode true w (physicalRadialFrequency q) (-L/2)*
            (deriv (fun a => originalScalar q br amp a (a+L)) p+w*originalScalar q br amp p (p+L))-
        (connection w (physicalRadialFrequency q)/(2*w))*power (-w) 2*
          (D4BMOriginalHorizonTimeTrace.horizonSlope q br amp p+w*horizonTrace q br amp p))‖ ≤
        B*(Real.exp (-L)+Real.exp (-w.re*L))*
          Real.exp (-(w.re-(D4BMOriginalCirclePeriod.readerExponent q).re)*p) :=
  damped_reader_product_error w (physicalRadialFrequency q) hw ((reader_re_nonneg q).trans hwr.le) _ _ _
    (original_collar_current_slot_error q br amp w) (horizon_current_slot_growth q br amp w)

/-- The same reader estimate applies directly to the full original forcing, at every angular point. -/
theorem original_full_forcing_reader_error (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im ≠ 0) (hwr : 0 ≤ w.re) (z : D4BMHorizon.Point) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p : ℝ, 0 < p →
      ‖Complex.exp (-w*(p:ℂ))*(Complex.exp (w*((-L/2:ℝ):ℂ))*
          tortoiseMode true w (physicalRadialFrequency q) (-L/2)*
            (timeOriginalForcing q br amp (p+L/2) (-L/2) z/(horizonCoordinate (-L/2):ℂ))-
        (connection w (physicalRadialFrequency q)/(2*w))*power (-w) 2*
          D4BMOriginalCornerForcing.forcingTrace (physicalRate q br) amp
            (fullSquarePotential q z) (fullGradientEnergy q z/2) p)‖ ≤
        B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(w.re-(2*physicalRate q br).re)*p) := by
  apply damped_reader_product_error w (physicalRadialFrequency q) hw hwr
  · obtain ⟨B,hB,hb⟩ := D4BMOriginalCornerForcing.original_full_forcing_collar_bound q br amp z
    refine ⟨B,hB.le,?_⟩
    filter_upwards [hb] with L h p hp
    exact h p
  · let s := physicalRate q br
    let F := D4BMOriginalCornerForcing.forcingProfile s amp (fullSquarePotential q z) (fullGradientEnergy q z/2) 1
    obtain ⟨B,hB,hb⟩ := timeOnset_pair_bound (2*s) (-(2*s).re) (by simp)
    refine ⟨‖F‖*B,by positivity,?_⟩
    intro p hp
    have h := (le_add_of_nonneg_right (norm_nonneg (timeOnsetFirst (2*s) p))).trans (hb p)
    simp only [neg_neg] at h
    change ‖F*timeOnset (2*s) p‖ ≤ _
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (norm_nonneg F)

end
end RHTower.D4BMOriginalCollarCurrentBounds
