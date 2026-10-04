import GaloisForLFunctions.RHTower.ThetaFinitePairCurrentGerm

/-! Compact source averages remove the apparent node singularities of the
literal transport packets. Both extensions have jointly continuous node jets,
including the coupled node/source-time corner. -/

noncomputable section
open Set MeasureTheory
namespace RHTower.ThetaFiniteTransport
open GaloisForLFunctions.HTGeometry

local notation "k" => thetaCuspFullSource
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "H" => thetaTailFirstMomentKernel
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "I" => ThetaConfluent.derivativeMass

private theorem cont_p : Continuous p := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt
private theorem cont_c : Continuous c := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvature t).continuousAt
private theorem center_ne : J ≠ 0 := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
  exact (ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0).ne'

def compactNodeAverage (n : ℕ) (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, u^n*f (u*x) t

theorem compactNodeAverage_continuous (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : Continuous fun z : ℝ × ℝ => f z.1 z.2) :
    Continuous fun z : ℝ × ℝ => compactNodeAverage n f z.1 z.2 := by
  unfold compactNodeAverage
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_snd.pow n).mul
    (hf.comp ((continuous_snd.mul continuous_fst.fst).prodMk continuous_fst.snd))

theorem compactNodeAverage_hasDerivAt (n : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Continuous fun z : ℝ × ℝ => f z.1 z.2)
    (hg : Continuous fun z : ℝ × ℝ => g z.1 z.2)
    (hd : ∀ x t, HasDerivAt (fun z => f z t) (g x t) x) (x t : ℝ) :
    HasDerivAt (fun z => compactNodeAverage n f z t)
      (compactNodeAverage (n+1) g x t) x := by
  unfold compactNodeAverage
  refine hasDerivAt_parametric_intervalIntegral
    (f := fun z u => u^n*f (u*z) t)
    (f' := fun z u => u^(n+1)*g (u*z) t) ?_ ?_ ?_ 0 1 x
  · exact (continuous_snd.pow n).mul
      (hf.comp ((continuous_snd.mul continuous_fst).prodMk continuous_const))
  · exact (continuous_snd.pow (n+1)).mul
      (hg.comp ((continuous_snd.mul continuous_fst).prodMk continuous_const))
  · intro z u
    convert! ((hd (u*z) t).comp z ((hasDerivAt_id z).const_mul u)).const_mul (u^n) using 1
    simp only [pow_succ]
    ring

theorem compactNodeAverage_zero (n : ℕ) (f : ℝ → ℝ → ℝ) (t : ℝ) :
    compactNodeAverage n f 0 t=f 0 t/(n+1) := by
  simp only [compactNodeAverage,mul_zero,intervalIntegral.integral_mul_const,integral_pow,
    one_pow,zero_pow (Nat.succ_ne_zero _),sub_zero]
  ring

private theorem compactNodeAverage_mul {f g : ℝ → ℝ} (hg : Continuous g)
    (hd : ∀ z, HasDerivAt f (g z) z) (x : ℝ) :
    x*compactNodeAverage 0 (fun z _ => g z) x 0=f x-f 0 := by
  have hi : IntervalIntegrable (fun u => x*g (u*x)) volume 0 1 :=
    (continuous_const.mul (hg.comp (continuous_id.mul continuous_const))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (f := fun u => f (u*x))
    (f' := fun u => x*g (u*x)) (fun u _ => by
      convert! (hd (u*x)).comp u ((hasDerivAt_id u).mul_const x) using 1
      ring) hi
  simpa only [compactNodeAverage,pow_zero,one_mul,intervalIntegral.integral_const_mul,
    zero_mul] using h

private def packetNodeIntegrand (x t : ℝ) : ℝ :=
  -p (t+x)*k (t+x)-ThetaJoint.firstLeft x 0/J*k t
private def packetNodeIntegrandJet (x t : ℝ) : ℝ :=
  (p (t+x)^2-c (t+x))*k (t+x)-ThetaJoint.secondLeft x 0/J*k t
private def primitiveNodeIntegrand (x t : ℝ) : ℝ :=
  ThetaJoint.firstLeft x 0/J*H t t-ThetaJoint.firstLeft (t+x) t
private def primitiveNodeIntegrandJet (x t : ℝ) : ℝ :=
  ThetaJoint.secondLeft x 0/J*H t t-ThetaJoint.secondLeft (t+x) t

private theorem packetNodeIntegrand_continuous :
    Continuous fun z : ℝ × ℝ => packetNodeIntegrand z.1 z.2 := by
  unfold packetNodeIntegrand
  exact (((cont_p.comp (continuous_snd.add continuous_fst)).neg).mul
    (thetaCuspSchwartzReal.continuous.comp (continuous_snd.add continuous_fst))).sub
    (((ThetaJoint.firstLeft_continuous.comp
      (continuous_fst.prodMk continuous_const)).div_const J).mul
        (thetaCuspSchwartzReal.continuous.comp continuous_snd))

private theorem packetNodeIntegrandJet_continuous :
    Continuous fun z : ℝ × ℝ => packetNodeIntegrandJet z.1 z.2 := by
  unfold packetNodeIntegrandJet
  exact ((((cont_p.comp (continuous_snd.add continuous_fst)).pow 2).sub
    (cont_c.comp (continuous_snd.add continuous_fst))).mul
      (thetaCuspSchwartzReal.continuous.comp (continuous_snd.add continuous_fst))).sub
    (((ThetaJoint.secondLeft_continuous.comp
      (continuous_fst.prodMk continuous_const)).div_const J).mul
        (thetaCuspSchwartzReal.continuous.comp continuous_snd))

private theorem primitiveNodeIntegrand_continuous :
    Continuous fun z : ℝ × ℝ => primitiveNodeIntegrand z.1 z.2 := by
  unfold primitiveNodeIntegrand
  exact (((ThetaJoint.firstLeft_continuous.comp
    (continuous_fst.prodMk continuous_const)).div_const J).mul
      (ThetaJoint.source_kernel_continuous.comp (continuous_snd.prodMk continuous_snd))).sub
    (ThetaJoint.firstLeft_continuous.comp
      ((continuous_snd.add continuous_fst).prodMk continuous_snd))

private theorem primitiveNodeIntegrandJet_continuous :
    Continuous fun z : ℝ × ℝ => primitiveNodeIntegrandJet z.1 z.2 := by
  unfold primitiveNodeIntegrandJet
  exact (((ThetaJoint.secondLeft_continuous.comp
    (continuous_fst.prodMk continuous_const)).div_const J).mul
      (ThetaJoint.source_kernel_continuous.comp (continuous_snd.prodMk continuous_snd))).sub
    (ThetaJoint.secondLeft_continuous.comp
      ((continuous_snd.add continuous_fst).prodMk continuous_snd))

private theorem packetNodeIntegrand_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun z => packetNodeIntegrand z t) (packetNodeIntegrandJet x t) x := by
  have hp := (hasDerivAt_thetaCuspLogDecaySlope (t+x)).comp x ((hasDerivAt_id x).const_add t)
  have hk := (actualSource_hasDerivAt (t+x)).comp x ((hasDerivAt_id x).const_add t)
  convert! ((hp.neg.mul hk).sub
    (((ThetaJoint.firstLeft_hasDerivAt_left x 0).div_const J).mul_const (k t))) using 1
  simp only [packetNodeIntegrandJet,mul_one,Function.comp_apply,Pi.neg_apply]
  ring

private theorem primitiveNodeIntegrand_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun z => primitiveNodeIntegrand z t) (primitiveNodeIntegrandJet x t) x := by
  have h := (ThetaJoint.firstLeft_hasDerivAt_left (t+x) t).comp x ((hasDerivAt_id x).const_add t)
  convert! (((ThetaJoint.firstLeft_hasDerivAt_left x 0).div_const J).mul_const (H t t)).sub h using 1
  simp only [primitiveNodeIntegrandJet,mul_one]

def packetExtension (x t : ℝ) : ℝ :=
  compactNodeAverage 0 packetNodeIntegrand x t/k (t+x)
def primitiveExtension (x t : ℝ) : ℝ :=
  compactNodeAverage 0 primitiveNodeIntegrand x t/(k t*k (t+x))
def packetExtensionJet (x t : ℝ) : ℝ :=
  (compactNodeAverage 1 packetNodeIntegrandJet x t+
    p (t+x)*compactNodeAverage 0 packetNodeIntegrand x t)/k (t+x)
def primitiveExtensionJet (x t : ℝ) : ℝ :=
  (compactNodeAverage 1 primitiveNodeIntegrandJet x t+
    p (t+x)*compactNodeAverage 0 primitiveNodeIntegrand x t)/(k t*k (t+x))

theorem packetExtension_continuous : Continuous fun z : ℝ × ℝ => packetExtension z.1 z.2 :=
  (compactNodeAverage_continuous 0 packetNodeIntegrand_continuous).div
    (thetaCuspSchwartzReal.continuous.comp (continuous_snd.add continuous_fst))
    (fun z => (thetaCuspFullSource_pos_all (z.2+z.1)).ne')

theorem primitiveExtension_continuous : Continuous fun z : ℝ × ℝ => primitiveExtension z.1 z.2 :=
  (compactNodeAverage_continuous 0 primitiveNodeIntegrand_continuous).div
    ((thetaCuspSchwartzReal.continuous.comp continuous_snd).mul
      (thetaCuspSchwartzReal.continuous.comp (continuous_snd.add continuous_fst)))
    (fun z => mul_ne_zero (thetaCuspFullSource_pos_all z.2).ne'
      (thetaCuspFullSource_pos_all (z.2+z.1)).ne')

theorem packetExtensionJet_continuous : Continuous fun z : ℝ × ℝ => packetExtensionJet z.1 z.2 :=
  ((compactNodeAverage_continuous 1 packetNodeIntegrandJet_continuous).add
    ((cont_p.comp (continuous_snd.add continuous_fst)).mul
      (compactNodeAverage_continuous 0 packetNodeIntegrand_continuous))).div
    (thetaCuspSchwartzReal.continuous.comp (continuous_snd.add continuous_fst))
    (fun z => (thetaCuspFullSource_pos_all (z.2+z.1)).ne')

theorem primitiveExtensionJet_continuous : Continuous fun z : ℝ × ℝ => primitiveExtensionJet z.1 z.2 :=
  ((compactNodeAverage_continuous 1 primitiveNodeIntegrandJet_continuous).add
    ((cont_p.comp (continuous_snd.add continuous_fst)).mul
      (compactNodeAverage_continuous 0 primitiveNodeIntegrand_continuous))).div
    ((thetaCuspSchwartzReal.continuous.comp continuous_snd).mul
      (thetaCuspSchwartzReal.continuous.comp (continuous_snd.add continuous_fst)))
    (fun z => mul_ne_zero (thetaCuspFullSource_pos_all z.2).ne'
      (thetaCuspFullSource_pos_all (z.2+z.1)).ne')

theorem packetExtension_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun z => packetExtension z t) (packetExtensionJet x t) x := by
  have h := compactNodeAverage_hasDerivAt 0 packetNodeIntegrand_continuous
    packetNodeIntegrandJet_continuous packetNodeIntegrand_hasDerivAt x t
  have hk := (actualSource_hasDerivAt (t+x)).comp x ((hasDerivAt_id x).const_add t)
  convert! h.div hk (thetaCuspFullSource_pos_all (t+x)).ne' using 1
  simp only [packetExtensionJet,mul_one,Function.comp_apply]
  field_simp [(thetaCuspFullSource_pos_all (t+x)).ne']
  ring

theorem primitiveExtension_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun z => primitiveExtension z t) (primitiveExtensionJet x t) x := by
  have h := compactNodeAverage_hasDerivAt 0 primitiveNodeIntegrand_continuous
    primitiveNodeIntegrandJet_continuous primitiveNodeIntegrand_hasDerivAt x t
  have hk := ((actualSource_hasDerivAt (t+x)).comp x ((hasDerivAt_id x).const_add t)).const_mul (k t)
  convert! h.div hk (mul_ne_zero (thetaCuspFullSource_pos_all t).ne'
    (thetaCuspFullSource_pos_all (t+x)).ne') using 1
  simp only [primitiveExtensionJet,mul_one,Function.comp_apply]
  field_simp [(thetaCuspFullSource_pos_all t).ne',(thetaCuspFullSource_pos_all (t+x)).ne']
  ring

theorem packetExtension_eq {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    packetExtension x t=normalizedPacket x t := by
  have hd (z : ℝ) : HasDerivAt (fun z => k (t+z)-H 0 z/J*k t) (packetNodeIntegrand z t) z := by
    convert! ((actualSource_hasDerivAt (t+z)).comp z ((hasDerivAt_id z).const_add t)).sub
      (((ThetaJoint.source_hasDerivAt_right 0 z).div_const J).mul_const (k t)) using 1
    simp only [packetNodeIntegrand,mul_one]
  have he := compactNodeAverage_mul
    (packetNodeIntegrand_continuous.comp (continuous_id.prodMk continuous_const)) hd x
  change x*compactNodeAverage 0 packetNodeIntegrand x t=_ at he
  simp only [add_zero,div_self center_ne,one_mul,sub_self,sub_zero] at he
  unfold packetExtension normalizedPacket
  rw [add_comm x t]
  field_simp [hx,center_ne,(thetaCuspFullSource_pos_all (t+x)).ne'] at he ⊢
  nlinarith only [he]

theorem primitiveExtension_eq {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    primitiveExtension x t=transportPrimitive x t := by
  have hd (z : ℝ) : HasDerivAt (fun z => H 0 z/J*H t t-H t (t+z)) (primitiveNodeIntegrand z t) z := by
    convert! (((ThetaJoint.source_hasDerivAt_right 0 z).div_const J).mul_const (H t t)).sub
      ((ThetaJoint.source_hasDerivAt_right t (t+z)).comp z ((hasDerivAt_id z).const_add t)) using 1
    simp only [primitiveNodeIntegrand,mul_one]
  have he := compactNodeAverage_mul
    (primitiveNodeIntegrand_continuous.comp (continuous_id.prodMk continuous_const)) hd x
  change x*compactNodeAverage 0 primitiveNodeIntegrand x t=_ at he
  simp only [add_zero,div_self center_ne,one_mul,sub_self,sub_zero] at he
  unfold primitiveExtension transportPrimitive
  rw [prefixBalance_eq_tail,add_comm x t]
  field_simp [hx,center_ne,(thetaCuspFullSource_pos_all t).ne',
    (thetaCuspFullSource_pos_all (t+x)).ne'] at he ⊢
  nlinarith only [he]

theorem packetExtension_zero (t : ℝ) : packetExtension 0 t=-p t := by
  simp only [packetExtension,compactNodeAverage_zero,packetNodeIntegrand,add_zero,
    ThetaJoint.firstLeft_origin,zero_div,zero_mul,sub_zero,Nat.cast_zero,zero_add,div_one]
  field_simp [(thetaCuspFullSource_pos_all t).ne']

theorem packetExtensionJet_zero (t : ℝ) :
    packetExtensionJet 0 t=I/J-(c t+p t^2)/2 := by
  simp only [packetExtensionJet,compactNodeAverage_zero,packetNodeIntegrand,
    packetNodeIntegrandJet,add_zero,ThetaJoint.firstLeft_origin,ThetaJoint.secondLeft_origin,
    zero_div,zero_mul,sub_zero,Nat.cast_zero,Nat.cast_one,zero_add,div_one]
  field_simp [center_ne,(thetaCuspFullSource_pos_all t).ne']
  ring

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

theorem primitiveExtension_zero (t : ℝ) : primitiveExtension 0 t=t := by
  simp only [primitiveExtension,compactNodeAverage_zero,primitiveNodeIntegrand,add_zero,
    kernel_first_diagonal,Nat.cast_zero,zero_add,div_one]
  field_simp [center_ne,(thetaCuspFullSource_pos_all t).ne']
  ring

theorem primitiveExtensionJet_zero (t : ℝ) :
    primitiveExtensionJet 0 t=centerPrimitiveVariation t := by
  simp only [primitiveExtensionJet,compactNodeAverage_zero,primitiveNodeIntegrand,
    primitiveNodeIntegrandJet,add_zero,ThetaJoint.secondLeft_origin,kernel_first_diagonal,
    Nat.cast_zero,Nat.cast_one,zero_add,div_one]
  unfold centerPrimitiveVariation
  field_simp [center_ne,(thetaCuspFullSource_pos_all t).ne']
  ring

end RHTower.ThetaFiniteTransport
