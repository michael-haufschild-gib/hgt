import GaloisForLFunctions.RHTower.ThetaFinitePairCurrentCoefficients
import GaloisForLFunctions.RHTower.ThetaFinitePairCurrentCenterProfile

/-! The center profile is the exact first node variation of the full canonical
current. The proof clears packet denominators before taking the node limit. -/

noncomputable section
open Set MeasureTheory Filter Topology
namespace RHTower.ThetaFiniteTransport

local notation "k" => thetaCuspFullSource
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "c₂" => thetaCuspLogCurvatureJetTwo
local notation "H" => thetaTailFirstMomentKernel
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "I" => ThetaConfluent.derivativeMass

private theorem center_ne : J ≠ 0 := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
  exact (ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0).ne'

private theorem shifted_derivative {f : ℝ → ℝ} {d t : ℝ} (h : HasDerivAt f d t) :
    HasDerivAt (fun x => f (t+x)) d 0 := by
  have h' : HasDerivAt f d (t+0) := by simpa only [add_zero] using h
  convert! h'.comp 0 ((hasDerivAt_id (0:ℝ)).const_add t) using 1
  simp only [mul_one]

private theorem kernel_first_diagonal (t : ℝ) : ThetaJoint.firstLeft t t=-t*k t^2 := by
  let f := thetaCuspSchwartzReal
  let d := SchwartzMap.derivCLM ℝ ℝ f
  have h0 : ThetaJoint.correlation f f 0 0+
      2*ThetaJoint.correlation (ThetaJoint.weighted d) f 0 0=0 := by
    simpa only [ThetaJoint.firstLeft,ThetaJoint.kernel,sub_self,zero_mul,zero_add] using
      ThetaJoint.firstLeft_origin
  have hi0 : IntervalIntegrable (fun u => f u*f u) volume 0 t :=
    (f.continuous.mul f.continuous).intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun u => u*d u*f u) volume 0 t :=
    ((continuous_id.mul d.continuous).mul f.continuous).intervalIntegrable _ _
  have hd (u : ℝ) : HasDerivAt (fun r => r*f r^2)
      (f u*f u+2*(u*d u*f u)) u := by
    convert! (hasDerivAt_id u).mul ((f.hasDerivAt u).pow 2) using 1
    change f u*f u+2*(u*deriv (f : ℝ → ℝ) u*f u)=_
    simp only [id_eq,Pi.pow_apply]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hd u) (hi0.add (hi1.const_mul 2))
  rw [intervalIntegral.integral_add hi0 (hi1.const_mul 2),
    intervalIntegral.integral_const_mul] at hint
  simp only [zero_mul,sub_zero] at hint
  change ThetaJoint.correlation f f t t+ThetaJoint.kernel d f t t=-t*f t^2
  simp only [ThetaJoint.kernel,sub_self,zero_mul,zero_add]
  rw [ThetaJoint.correlation_movingTail f f,
    ThetaJoint.correlation_movingTail (ThetaJoint.weighted d) f]
  simp only [sub_self,zero_add,ThetaJoint.weighted_apply]
  linarith only [h0,hint]

private def packetNumerator (x t : ℝ) : ℝ := k t*k (t+x)-(H 0 x/J)*k t^2
private def balanceNumerator (x t : ℝ) : ℝ := (H 0 x/J)*H t t-H t (t+x)

private theorem packetNumerator_zero (t : ℝ) : packetNumerator 0 t=0 := by
  simp only [packetNumerator,add_zero,div_self center_ne,one_mul,pow_two,sub_self]

private theorem balanceNumerator_zero (t : ℝ) : balanceNumerator 0 t=0 := by
  simp only [balanceNumerator,add_zero,div_self center_ne,one_mul,sub_self]

private theorem packetNumerator_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y => packetNumerator y t)
      (-p (t+x)*k t*k (t+x)-(ThetaJoint.firstLeft x 0/J)*k t^2) x := by
  have hk := (actualSource_hasDerivAt (t+x)).comp x ((hasDerivAt_id x).const_add t)
  convert! (hk.const_mul (k t)).sub
    (((ThetaJoint.source_hasDerivAt_right 0 x).div_const J).mul_const (k t^2)) using 1
  simp only [mul_one]
  ring

private theorem balanceNumerator_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y => balanceNumerator y t)
      ((ThetaJoint.firstLeft x 0/J)*H t t-ThetaJoint.firstLeft (t+x) t) x := by
  have hH := (ThetaJoint.source_hasDerivAt_right t (t+x)).comp x
    ((hasDerivAt_id x).const_add t)
  convert! (((ThetaJoint.source_hasDerivAt_right 0 x).div_const J).mul_const (H t t)).sub hH using 1
  simp only [mul_one]

private theorem packetNumerator_second (t : ℝ) : HasDerivAt
    (fun x => -p (t+x)*k t*k (t+x)-(ThetaJoint.firstLeft x 0/J)*k t^2)
    (k t^2*(p t^2-c t+2*I/J)) 0 := by
  have hp := shifted_derivative (hasDerivAt_thetaCuspLogDecaySlope t)
  have hk := shifted_derivative (actualSource_hasDerivAt t)
  convert! (((hp.neg.mul_const (k t)).mul hk).sub
    (((ThetaJoint.firstLeft_hasDerivAt_left 0 0).div_const J).mul_const (k t^2))) using 1
  simp only [Pi.neg_apply,ThetaJoint.secondLeft_origin,add_zero]
  ring

private theorem balanceNumerator_second (t : ℝ) : HasDerivAt
    (fun x => (ThetaJoint.firstLeft x 0/J)*H t t-ThetaJoint.firstLeft (t+x) t)
    (-2*(I/J)*H t t-ThetaJoint.secondLeft t t) 0 := by
  have hH := shifted_derivative (ThetaJoint.firstLeft_hasDerivAt_left t t)
  convert! (((ThetaJoint.firstLeft_hasDerivAt_left 0 0).div_const J).mul_const (H t t)).sub hH using 1
  simp only [ThetaJoint.secondLeft_origin]
  ring

private theorem secondTaylor_limit {f g : ℝ → ℝ} {d : ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : HasDerivAt g d 0) :
    Tendsto (fun x => (f x-f 0-g 0*x)/x^2) (𝓝[>] 0) (𝓝 (d/2)) := by
  have hq : Tendsto (fun x => (g x-g 0)/x) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_add,smul_eq_mul,inv_mul_eq_div] using hg.tendsto_slope_zero_right
  have hq' : Tendsto (fun x => (g x-g 0)/(2*x)) (𝓝[>] 0) (𝓝 (d/2)) := by
    convert! hq.div_const 2 using 1
    funext x; ring
  apply HasDerivAt.lhopital_zero_nhdsGT
    (Eventually.of_forall fun x => by
      convert! ((hf x).sub_const (f 0)).sub ((hasDerivAt_id x).const_mul (g 0)) using 1
      simp only [mul_one])
    (Eventually.of_forall fun x => by
      convert! (hasDerivAt_id x).pow 2 using 1; simp only [id_eq]; ring)
    ?_ ?_ ?_ hq'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (ne_of_gt hx)
  · have hfT : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
      (hf 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hxT : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa only [sub_self,mul_zero,sub_zero] using
      (hfT.sub_const (f 0)).sub (hxT.const_mul (g 0))
  · simpa using (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝[>] 0)).mono_right
      nhdsWithin_le_nhds |>.pow 2

/-- The positive center profile is the exact diagonal node derivative of the full current. -/
theorem finiteCanonicalCurrent_node_ratio_limit {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x => finiteCanonicalCurrent x x t/x) (𝓝[>] 0) (𝓝 (centerCurrentProfile t)) := by
  have hA := (diagonalPacketCoefficient_hasDerivAt_zero ht).tendsto_slope_zero_right
  have hD := (diagonalPrimitiveCoefficient_hasDerivAt_zero ht).tendsto_slope_zero_right
  simp only [zero_add,smul_eq_mul,inv_mul_eq_div,
    diagonalPacketCoefficient_zero,diagonalPrimitiveCoefficient_zero] at hA hD
  have hQ := (packetNumerator_hasDerivAt 0 t).tendsto_slope_zero_right
  simp only [zero_add,smul_eq_mul,inv_mul_eq_div,packetNumerator_zero,sub_zero,
    add_zero,ThetaJoint.firstLeft_origin,zero_div,zero_mul] at hQ
  have hR := (balanceNumerator_hasDerivAt 0 t).tendsto_slope_zero_right
  simp only [zero_add,smul_eq_mul,inv_mul_eq_div,balanceNumerator_zero,sub_zero,
    add_zero,ThetaJoint.firstLeft_origin,zero_div,zero_mul,zero_sub] at hR
  simp only [kernel_first_diagonal,neg_mul,neg_neg] at hR
  have hQ2 := secondTaylor_limit (fun x => packetNumerator_hasDerivAt x t) (packetNumerator_second t)
  simp only [packetNumerator_zero,sub_zero,add_zero,ThetaJoint.firstLeft_origin,
    zero_div,zero_mul] at hQ2
  have hR2 := secondTaylor_limit (fun x => balanceNumerator_hasDerivAt x t) (balanceNumerator_second t)
  simp only [balanceNumerator_zero,sub_zero,add_zero,ThetaJoint.firstLeft_origin,
    zero_div,zero_mul,zero_sub] at hR2
  simp only [kernel_first_diagonal,neg_mul,neg_neg] at hR2
  have hk : Tendsto (fun x => k t*k (t+x)) (𝓝[>] 0) (𝓝 (k t^2)) := by
    have h : Tendsto (fun x => k t*k (t+x)) (𝓝[>] 0) (𝓝 (k t*k (t+0))) :=
      (((contDiff_thetaCuspFullSource.continuous.comp
      (continuous_const.add continuous_id)).tendsto 0).const_mul (k t)).mono_left nhdsWithin_le_nhds
    simpa only [add_zero,pow_two] using h
  have h := ((((hA.mul hQ).add (hD.mul hR)).add (hQ2.const_mul (-t*c t))).add
    (hR2.const_mul (-p t*c t))).div hk (pow_ne_zero 2 (thetaCuspFullSource_pos_all t).ne')
  have he :
      (((-c t/2-t*v t/2+t*c 0*c t/p t-c 0*c t/(2*p t^2))*(-p t*k t*k t)+
      (c₂ t/12+c 0*v t/(2*p t)-p t*v t/2-c t^2/2+c 0*c t-c 0*c t^2/(2*p t^2))*(t*k t^2))+
      (-t*c t)*(k t^2*(p t^2-c t+2*I/J)/2)+
      (-p t*c t)*((-(2*(I/J)*H t t)-ThetaJoint.secondLeft t t)/2))/(k t^2)=
      centerCurrentProfile t := by
    unfold centerCurrentProfile centerPrimitiveVariation
    field_simp [center_ne,(ThetaSturmCrossing.slope_pos ht).ne',(thetaCuspFullSource_pos_all t).ne']
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  simp only [Pi.div_apply]
  rw [finiteCanonicalCurrent_diagonal hx0 ht.le]
  unfold packetNumerator balanceNumerator normalizedPacket transportPrimitive
  rw [prefixBalance_eq_tail]
  rw [add_comm x t]
  field_simp [hx0.ne',center_ne,(thetaCuspFullSource_pos_all t).ne',
    (thetaCuspFullSource_pos_all (t+x)).ne']
  ring

/-- Positive actual current values occur at positive nodes approaching the center. -/
theorem exists_positive_finiteCanonicalCurrent_diagonal :
    ∃ t x : ℝ, 0 < t ∧ 0 < x ∧ 0 < finiteCanonicalCurrent x x t := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hL⟩ := (hpos.and centerCurrentProfile_eventually_pos).exists
  have h := (finiteCanonicalCurrent_node_ratio_limit ht).eventually (lt_mem_nhds hL)
  obtain ⟨x,hx,hI⟩ := (hpos.and h).exists
  exact ⟨t,x,ht,hx,(div_pos_iff_of_pos_right hx).mp hI⟩

private theorem transportMoment_hasDerivAt_node (x : ℝ) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (fun z => transportMoment x z t)
      (((y*c (t+y)-(p (t+y)-p t))/y^2)*transportPrimitive x t) y := by
  have hp := (hasDerivAt_thetaCuspLogDecaySlope (t+y)).comp y ((hasDerivAt_id y).const_add t)
  have hr : HasDerivAt (fun z => ThetaSturmCrossing.secant z t)
      ((y*c (t+y)-(p (t+y)-p t))/y^2) y := by
    convert! (hp.sub_const (p t)).div (hasDerivAt_id y) hy.ne' using 1
    simp only [mul_one,id_eq,Function.comp_apply]
    ring
  have he : (fun z => transportMoment x z t)=
      (fun z => normalizedPacket x t+ThetaSturmCrossing.secant z t*transportPrimitive x t) := by
    funext z
    unfold transportMoment ThetaSturmCrossing.secant
    rw [add_comm z t]
  rw [he]
  exact (hr.mul_const (transportPrimitive x t)).const_add (normalizedPacket x t)

private theorem transportMoment_hasDerivAt_time {x : ℝ} (hx : 0 < x) (y t : ℝ) :
    HasDerivAt (transportMoment x y)
      ((p (t+x)-p t)*(normalizedPacket x t-1/x)+
        ThetaSturmCrossing.secantJet y t*transportPrimitive x t+
        ThetaSturmCrossing.secant y t*(1+2*t*normalizedPacket x t+
          (p t+p (t+x))*transportPrimitive x t)) t := by
  have he : transportMoment x y=(fun u => normalizedPacket x u+
      ThetaSturmCrossing.secant y u*transportPrimitive x u) := by
    funext u
    unfold transportMoment ThetaSturmCrossing.secant
    rw [add_comm y u]
  rw [he]
  convert! (normalizedPacket_hasDerivAt hx t).add
    ((ThetaSturmCrossing.secant_hasDerivAt y t).mul (transportPrimitive_hasDerivAt hx t)) using 1
  rw [add_comm x t]
  ring

/-- Identification with the differential current of the actual transported Schur moment. -/
theorem finiteCanonicalCurrent_eq_deriv {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    finiteCanonicalCurrent x y t=
      deriv (fun z => transportMoment x z t) y-
        finiteCanonicalSpeed x y t*deriv (transportMoment x y) t-
        finiteCanonicalSpeedJet x y t*transportMoment x y t := by
  rw [(transportMoment_hasDerivAt_node x hy t).deriv,
    (transportMoment_hasDerivAt_time hx y t).deriv]
  unfold finiteCanonicalCurrent matchedCurrentCoefficient primitiveCurrentCoefficient
    transportMoment ThetaSturmCrossing.secant
  rw [add_comm y t]
  field_simp [hx.ne',hy.ne']
  ring

/-- The pointwise negative-current conjecture fails inside the strictly ordered chamber. -/
theorem exists_positive_finiteCanonicalCurrent :
    ∃ t x y : ℝ, 0 < t ∧ 0 < x ∧ x < y ∧ 0 < finiteCanonicalCurrent x y t := by
  obtain ⟨t,x,ht,hx,hpos⟩ := exists_positive_finiteCanonicalCurrent_diagonal
  have hp : Continuous p := continuous_iff_continuousAt.mpr
    fun u => (hasDerivAt_thetaCuspLogDecaySlope u).continuousAt
  have hc : Continuous c := continuous_iff_continuousAt.mpr
    fun u => (hasDerivAt_thetaCuspLogCurvature u).continuousAt
  have hsum : p (t+x)+p (t+x) ≠ 0 :=
    (add_pos (ThetaSturmCrossing.slope_pos (add_pos ht hx))
      (ThetaSturmCrossing.slope_pos (add_pos ht hx))).ne'
  have hcont : ContinuousAt (fun y => finiteCanonicalCurrent x y t) x := by
    have hx0 : x ≠ 0 := hx.ne'
    have hpx : ContinuousAt (fun y => p y) x := hp.continuousAt
    have hcx : ContinuousAt (fun y => c y) x := hc.continuousAt
    have hpt : ContinuousAt (fun y => p (t+y)) x :=
      (hp.comp (continuous_const.add continuous_id)).continuousAt
    have hct : ContinuousAt (fun y => c (t+y)) x :=
      (hc.comp (continuous_const.add continuous_id)).continuousAt
    unfold finiteCanonicalCurrent matchedCurrentCoefficient primitiveCurrentCoefficient
      finiteCanonicalSpeed finiteCanonicalSpeedJet ThetaSturmCrossing.secant ThetaSturmCrossing.secantJet
    fun_prop (disch := positivity)
  have he : ∀ᶠ y in 𝓝[>] x, 0 < finiteCanonicalCurrent x y t :=
    (hcont.tendsto.eventually (lt_mem_nhds hpos)).filter_mono nhdsWithin_le_nhds
  have hgt : ∀ᶠ y : ℝ in 𝓝[>] x, x < y := self_mem_nhdsWithin
  obtain ⟨y,hxy,hy⟩ := (hgt.and he).exists
  exact ⟨t,x,y,ht,hx,hxy,hy⟩

end RHTower.ThetaFiniteTransport
