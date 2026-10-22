import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFutureSeedHorizonCap
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalCapWeakWave
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Fixed source-radius representation of the original characteristic horizon caps. -/
namespace RHTower.D4BMFixedSourceHorizon
open Set Filter Topology MeasureTheory
open D4BMHorizon D4BMModularCore D4BMJointSource D4BMNativeCircle
open D4BMGlobalAngularResponse
open scoped ContDiff
noncomputable section
set_option autoImplicit false

def sourceDen (x h : ℝ) : ℝ := Real.cosh x*Real.exp h+Real.sinh x
def sourceTime (tau x h : ℝ) : ℝ := tau+Real.log (sourceDen x h)
def sourceJac (x h : ℝ) : ℝ := Real.cosh x*Real.exp h/sourceDen x h

def tailBase (x z : ℝ) : ℝ := Real.cosh x+z*Real.sinh x

theorem tailBase_pos (x z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) : 0<tailBase x z := by
  have he := Real.cosh_add_sinh x
  have hc := Real.cosh_pos x
  have hx := Real.exp_pos x
  have hm := mul_nonneg hz.1 hx.le
  by_cases h : z=1
  · subst z
    simpa only [tailBase,one_mul,he] using hx
  · have hz1 : z<1 := lt_of_le_of_ne hz.2 h
    have hp := mul_pos (sub_pos.mpr hz1) hc
    dsimp only [tailBase]
    nlinarith

/-- Smooth amplitude of the entire late horizon tail, including source infinity z=0. -/
def tailWeight (s : ℂ) (z : Fin 3 → ℝ) : ℂ :=
  s*Complex.exp (s*((z 0+Real.log (tailBase (z 1) (z 2)):ℝ):ℂ))*
    (Real.cosh (z 1)/tailBase (z 1) (z 2):ℝ)

theorem tailWeight_smooth (s : ℂ) (z : Fin 3 → ℝ) (hz : z 2 ∈ Icc (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (tailWeight s) z := by
  have hp := tailBase_pos (z 1) (z 2) hz
  have ht : ContDiffAt ℝ ∞ (fun y : Fin 3 → ℝ => y 0+Real.log (tailBase (y 1) (y 2))) z := by
    unfold tailBase at *
    fun_prop (disch := positivity)
  have hj : ContDiffAt ℝ ∞ (fun y : Fin 3 → ℝ => Real.cosh (y 1)/tailBase (y 1) (y 2)) z := by
    unfold tailBase at *
    fun_prop (disch := positivity)
  have htC : ContDiffAt ℝ ∞ (fun y : Fin 3 → ℝ =>
      ((y 0+Real.log (tailBase (y 1) (y 2)):ℝ):ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z ht
  have hjC : ContDiffAt ℝ ∞ (fun y : Fin 3 → ℝ =>
      (((Real.cosh (y 1)/tailBase (y 1) (y 2)):ℝ):ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hj
  exact (contDiffAt_const.mul (contDiffAt_const.mul htC).cexp).mul hjC

theorem sourceDen_pos (x h : ℝ) (hh : 0 ≤ h) : 0 < sourceDen x h := by
  have he := Real.one_le_exp_iff.mpr hh
  have hm := mul_le_mul_of_nonneg_left he (Real.cosh_pos x).le
  have hx := Real.exp_pos x
  rw [← Real.cosh_add_sinh x] at hx
  dsimp [sourceDen]
  nlinarith

private theorem sourceTime_derivative (tau x h : ℝ) (hh : 0 ≤ h) :
    HasDerivAt (sourceTime tau x) (sourceJac x h) h := by
  have hd := (((Real.hasDerivAt_exp h).const_mul (Real.cosh x)).add_const
    (Real.sinh x)).log (sourceDen_pos x h hh).ne'
  exact hd.const_add tau

private theorem sourceTime_image (tau x : ℝ) :
    sourceTime tau x '' Ioi (0:ℝ)=Ioi (tau+x) := by
  ext v
  constructor
  · rintro ⟨h,hh,rfl⟩
    have he : Real.exp x < sourceDen x h := by
      rw [← Real.cosh_add_sinh x]
      dsimp only [sourceDen]
      nlinarith [Real.cosh_pos x,Real.one_lt_exp_iff.mpr hh]
    have hl := Real.log_lt_log (Real.exp_pos x) he
    rw [Real.log_exp] at hl
    change tau+x<tau+Real.log (sourceDen x h)
    linarith
  · intro hv
    change tau+x<v at hv
    let z := (Real.exp (v-tau)-Real.sinh x)/Real.cosh x
    have hz : 1<z := by
      dsimp only [z]
      rw [lt_div_iff₀ (Real.cosh_pos x)]
      have he := Real.exp_lt_exp.mpr (show x<v-tau by linarith)
      rw [← Real.cosh_add_sinh x] at he
      linarith
    refine ⟨Real.log z,Real.log_pos hz,?_⟩
    have hd : sourceDen x (Real.log z)=Real.exp (v-tau) := by
      rw [sourceDen,Real.exp_log (by linarith : 0<z)]
      dsimp only [z]
      field_simp [(Real.cosh_pos x).ne']
      ring
    rw [sourceTime,hd,Real.log_exp]
    ring

private theorem sourceTime_inj (tau x : ℝ) : InjOn (sourceTime tau x) (Ioi (0:ℝ)) := by
  intro a ha b hb he
  have hl : Real.log (sourceDen x a)=Real.log (sourceDen x b) := add_left_cancel he
  have hd := congrArg Real.exp hl
  rw [Real.exp_log (sourceDen_pos x a ha.le),Real.exp_log (sourceDen_pos x b hb.le)] at hd
  have he' : Real.exp a=Real.exp b := by
    dsimp only [sourceDen] at hd
    exact mul_left_cancel₀ (Real.cosh_pos x).ne' (add_right_cancel hd)
  exact Real.exp_injective he'

theorem horizonArgument_sourceTime (tau x h : ℝ) (hh : 0 ≤ h) :
    D4BMFutureHorizon.horizonArgument tau x (sourceTime tau x h)=Real.exp h := by
  rw [D4BMFutureHorizon.horizonArgument,sourceTime,add_sub_cancel_left,
    Real.exp_log (sourceDen_pos x h hh)]
  dsimp only [sourceDen]
  field_simp [(Real.cosh_pos x).ne']
  ring

/-- Exact original characteristic change of source time, including its Jacobian. -/
theorem sourceTime_integral (F M : ℝ → ℂ) (tau x : ℝ) :
    (∫ v in Ioi (tau+x),F v*M (D4BMFutureHorizon.horizonArgument tau x v))=
      ∫ h in Ioi (0:ℝ),(sourceJac x h:ℂ)*F (sourceTime tau x h)*M (Real.exp h) := by
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun h (hh : h ∈ Ioi (0:ℝ)) => (sourceTime_derivative tau x h hh.le).hasDerivWithinAt)
    (sourceTime_inj tau x) (fun v => F v*M (D4BMFutureHorizon.horizonArgument tau x v))
  rw [sourceTime_image] at hi
  rw [hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h hh
  dsimp only
  rw [abs_of_pos (show 0<sourceJac x h from
    div_pos (mul_pos (Real.cosh_pos x) (Real.exp_pos h)) (sourceDen_pos x h hh.le)),
    Complex.real_smul,horizonArgument_sourceTime tau x h hh.le]
  ring

def sourceArm (s : ℂ) (tau x : ℝ) (M : ℝ → ℂ) : ℂ :=
  ∫ v in Ioi (0:ℝ),timeOnsetFirst s v*
    (if tau+x ≤ v then M (D4BMFutureHorizon.horizonArgument tau x v) else 0)

def fixedArm (s : ℂ) (tau x : ℝ) (M : ℝ → ℂ) : ℂ :=
  ∫ h in Ioi (0:ℝ),(sourceJac x h:ℂ)*timeOnsetFirst s (sourceTime tau x h)*M (Real.exp h)

/-- Original positive source time and characteristic gate are both retained. -/
theorem sourceArm_eq_fixedArm (s : ℂ) (tau x : ℝ) (M : ℝ → ℂ) :
    sourceArm s tau x M=fixedArm s tau x M := by
  let N := fun v => timeOnsetFirst s v*
    (if tau+x ≤ v then M (D4BMFutureHorizon.horizonArgument tau x v) else 0)
  have h0 : sourceArm s tau x M=∫ v : ℝ,N v := by
    change (∫ v in Ioi (0:ℝ),N v)=_
    rw [← integral_Ici_eq_integral_Ioi]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    simp only [mem_Ici,not_le] at hv
    simp only [N,timeOnsetFirst_zero_of_neg s hv,zero_mul]
  have h1 : (∫ v in Ioi (tau+x),timeOnsetFirst s v*M (D4BMFutureHorizon.horizonArgument tau x v))=
      ∫ v : ℝ,N v := by
    rw [← integral_Ici_eq_integral_Ioi]
    calc
      _ = ∫ v in Ici (tau+x),N v := by
        apply setIntegral_congr_fun measurableSet_Ici
        intro v hv
        change tau+x ≤ v at hv
        simp only [N,if_pos hv]
      _ = _ := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro v hv
        simp only [mem_Ici] at hv
        simp only [N,if_neg hv,mul_zero]
  rw [h0,← h1,sourceTime_integral]
  rfl

/-- All late target dependence is confined to one smooth compact-parameter weight.
The original exponential source rate is unchanged. -/
theorem late_weight_factorization (s : ℂ) (tau x h : ℝ) (hh : 0 ≤ h)
    (hv : 1<sourceTime tau x h) :
    (sourceJac x h:ℂ)*timeOnsetFirst s (sourceTime tau x h)=
      Complex.exp (s*(h:ℂ))*tailWeight s ![tau,x,Real.exp (-h)] := by
  have hz : Real.exp (-h) ∈ Icc (0:ℝ) 1 :=
    ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by linarith)⟩
  have hu := tailBase_pos x (Real.exp (-h)) hz
  have hd : sourceDen x h=Real.exp h*tailBase x (Real.exp (-h)) := by
    unfold sourceDen tailBase
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos h).ne']
  have ht : sourceTime tau x h=tau+h+Real.log (tailBase x (Real.exp (-h))) := by
    rw [sourceTime,hd,Real.log_mul (Real.exp_pos h).ne' hu.ne',Real.log_exp]
    ring
  have hj : sourceJac x h=Real.cosh x/tailBase x (Real.exp (-h)) := by
    rw [sourceJac,hd]
    field_simp [(Real.exp_pos h).ne',hu.ne']
  have hf : timeOnsetFirst s (sourceTime tau x h)=s*Complex.exp (s*(sourceTime tau x h:ℂ)) := by
    rw [timeOnsetFirst,Real.smoothTransition.one_of_one_le hv.le,
      GaloisForLFunctions.HTGeometry.deriv_smoothTransition_eq_zero_of_notMem
        (show sourceTime tau x h ∉ Icc (0:ℝ) 1 from fun hv' => (not_le_of_gt hv) hv'.2)]
    simp only [Complex.ofReal_zero,Complex.ofReal_one,mul_one,zero_add]
  rw [hf,hj,ht]
  change _=Complex.exp (s*(h:ℂ))*
    (s*Complex.exp (s*((tau+Real.log (tailBase x (Real.exp (-h))):ℝ):ℂ))*
      (Real.cosh x/tailBase x (Real.exp (-h)):ℝ))
  rw [show tau+h+Real.log (tailBase x (Real.exp (-h)))=
    h+(tau+Real.log (tailBase x (Real.exp (-h)))) by ring,
    Complex.ofReal_add,mul_add,Complex.exp_add]
  ring

def fixedSquareArm (q : XiZeroCopy) (branch : Bool) (tau x X k : ℝ) : ℂ :=
  fixedArm (2*physicalRate q branch) tau x
    (fun z => mean q (Real.arcosh (max 1 z)) X k)

def fixedSeedArm (q : XiZeroCopy) (branch : Bool) (tau x X k : ℝ) : ℂ :=
  fixedArm (2*physicalRate q branch) tau x
    (fun z => D4BMFullAngularCircle.angularMean q branch (Real.arcosh (max 1 z)) X k)

/-- The complete lift cap, with original onset and both characteristic arms. -/
theorem liftCap_eq_fixed (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) :
    D4BMFutureHorizon.capBoundaryField q branch amp tau x X k=
      -D4BMFutureHorizon.liftTraceCoefficient q branch amp*
        (fixedSquareArm q branch tau x X k-fixedSquareArm q branch tau (-x) X k) := by
  have ha (y : ℝ) : D4BMFutureHorizon.boundaryArm q branch (tau+y) y X k=
      fixedSquareArm q branch tau y X k := by
    have hs := D4BMOriginalCapWave.boundaryArm_source_integral q branch tau y X k
    change D4BMFutureHorizon.boundaryArm q branch (tau+y) y X k=
      sourceArm (2*physicalRate q branch) tau y
        (fun z => mean q (Real.arcosh (max 1 z)) X k) at hs
    exact hs.trans (sourceArm_eq_fixedArm _ _ _ _)
  rw [D4BMFutureHorizon.capBoundaryField,ha x,
    show tau-x=tau+(-x) by ring,ha (-x)]

/-- The complete seed cap uses the same source-radius coordinate as the lift cap. -/
theorem seedCap_eq_fixed (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) :
    D4BMFutureSeedHorizon.seedCapField q branch amp tau x X k=
      -D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
        (fixedSeedArm q branch tau x X k-fixedSeedArm q branch tau (-x) X k) := by
  have h := D4BMFutureSeedHorizon.seedCapField_arms q branch amp tau x X k
  change D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
    sourceArm (2*physicalRate q branch) tau x
      (fun z => D4BMFullAngularCircle.angularMean q branch (Real.arcosh (max 1 z)) X k)-
    D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
      sourceArm (2*physicalRate q branch) tau (-x)
        (fun z => D4BMFullAngularCircle.angularMean q branch (Real.arcosh (max 1 z)) X k)=
      -D4BMFutureSeedHorizon.seedCapField q branch amp tau x X k at h
  rw [sourceArm_eq_fixedArm,sourceArm_eq_fixedArm] at h
  change D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*fixedSeedArm q branch tau x X k-
    D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*fixedSeedArm q branch tau (-x) X k=
      -D4BMFutureSeedHorizon.seedCapField q branch amp tau x X k at h
  linear_combination h

/-- The horizon contribution in the actual future reconstruction has this exact
combined source weight. No field or horizon arm is discarded. -/
theorem combinedCap_eq_fixed (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) :
    D4BMFutureSeedHorizon.seedCapField q branch amp tau x X k-
      parameter q branch*D4BMFutureHorizon.capBoundaryField q branch amp tau x X k=
    parameter q branch*D4BMLaplaceRadial.power (2*physicalRate q branch) 2*amp^(2 : ℕ)*
      ((fixedSeedArm q branch tau x X k-fixedSeedArm q branch tau (-x) X k)-
       (physicalRate q branch*(physicalRate q branch-1)/4)*
         (fixedSquareArm q branch tau x X k-fixedSquareArm q branch tau (-x) X k)) := by
  rw [seedCap_eq_fixed,liftCap_eq_fixed]
  unfold D4BMFutureSeedHorizon.seedTraceCoefficient D4BMFutureHorizon.liftTraceCoefficient
  ring

end
end RHTower.D4BMFixedSourceHorizon
