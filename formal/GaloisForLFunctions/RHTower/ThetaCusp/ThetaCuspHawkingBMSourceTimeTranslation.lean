import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPastSourceResponse

/-!
Finite physical-time translation of the original source and derived future fields.
The fixed onset leaves an exact source defect on a finite ingoing-time strip.
Its full Dirichlet response is absolutely admitted. The original reduced future
response, lift and both cap arms have the same late source character. The past
horizon instead retains the admitted difference of the actual source data.
No source frequency or physical clock is changed. These identities do not assert
an advanced wave equation, complete nonlinear-action invariance, or extinction.
-/

open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMSourceTimeTranslation
open D4BMJointSource D4BMFullSourceAdvanced D4BMFutureHorizon D4BMCausalKernel
open D4BMModularCore D4BMNativeCircle
noncomputable section
set_option autoImplicit false

/-- Original source character under the same physical time translation. -/
def sourceFactor (q : XiZeroCopy) (branch : Bool) (T : ℝ) : ℂ :=
  Complex.exp ((2*physicalRate q branch)*(T:ℂ))

/-- The finite translation defect of the original fixed onset. -/
def onsetDefect (v : ℂ) (T u : ℝ) : ℂ :=
  timeOnset v (u+T)-Complex.exp (v*(T:ℂ))*timeOnset v u

def onsetFirstDefect (v : ℂ) (T u : ℝ) : ℂ :=
  timeOnsetFirst v (u+T)-Complex.exp (v*(T:ℂ))*timeOnsetFirst v u

theorem onsetDefect_hasDerivAt (v : ℂ) (T u : ℝ) :
    HasDerivAt (onsetDefect v T) (onsetFirstDefect v T u) u :=
  (HasDerivAt.comp_add_const u T (timeOnset_hasDerivAt v (u+T))).sub
    ((timeOnset_hasDerivAt v u).const_mul (Complex.exp (v*(T:ℂ))))

private theorem onset_late (v : ℂ) (u : ℝ) (hu : 1 < u) :
    timeOnset v u=Complex.exp (v*(u:ℂ)) := by
  simp only [timeOnset,Real.smoothTransition.one_of_one_le hu.le,Complex.ofReal_one,one_mul]

private theorem onsetFirst_late (v : ℂ) (u : ℝ) (hu : 1 < u) :
    timeOnsetFirst v u=v*Complex.exp (v*(u:ℂ)) := by
  rw [timeOnsetFirst,Real.smoothTransition.one_of_one_le hu.le,
    deriv_smoothTransition_eq_zero_of_notMem (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.2)]
  simp only [Complex.ofReal_zero,Complex.ofReal_one,mul_one,zero_add]

private theorem onset_step (v : ℂ) (T u : ℝ) (hT : 0 ≤ T) (hu : 1 < u) :
    timeOnset v (u+T)=Complex.exp (v*(T:ℂ))*timeOnset v u := by
  rw [onset_late v (u+T) (by linarith),onset_late v u hu,
    Complex.ofReal_add,mul_add,Complex.exp_add,mul_comm]

private theorem onsetFirst_step (v : ℂ) (T u : ℝ) (hT : 0 ≤ T) (hu : 1 < u) :
    timeOnsetFirst v (u+T)=Complex.exp (v*(T:ℂ))*timeOnsetFirst v u := by
  rw [onsetFirst_late v (u+T) (by linarith),onsetFirst_late v u hu,
    Complex.ofReal_add,mul_add,Complex.exp_add]
  ring

/-- Both the onset defect and its actual derivative have the same finite source-time support. -/
theorem onsetDefect_zero_outside (v : ℂ) (T u : ℝ) (hT : 0 ≤ T)
    (hu : u < -T ∨ 1 < u) : onsetDefect v T u=0 ∧ onsetFirstDefect v T u=0 := by
  rcases hu with hu | hu
  · have h0 : u < 0 := by linarith
    have h1 : u+T < 0 := by linarith
    simp only [onsetDefect,onsetFirstDefect,timeOnset_zero_of_nonpos v h0.le,
      timeOnset_zero_of_nonpos v h1.le,timeOnsetFirst_zero_of_neg v h0,
      timeOnsetFirst_zero_of_neg v h1,mul_zero,sub_self,and_self]
  · simp only [onsetDefect,onsetFirstDefect,onset_step v T u hT hu,
      onsetFirst_step v T u hT hu,sub_self,and_self]

/-- Original full reduced forcing defect, retaining the first-onset cross term. -/
def reducedDefect (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (T τ y : ℝ) : ℂ :=
  reducedCoefficient (physicalRate q branch) 0 amp 1 y*
    onsetDefect (2*physicalRate q branch) T (τ+y)+
  2*radialLiftFirst (physicalRate q branch) 0 amp 1 y*
    onsetFirstDefect (2*physicalRate q branch) T (τ+y)

theorem reducedDefect_eq (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (T τ y : ℝ) :
    reducedDefect q branch amp T τ y=
      timeReducedCoefficient (physicalRate q branch) amp (τ+T) y-
        sourceFactor q branch T*timeReducedCoefficient (physicalRate q branch) amp τ y := by
  simp only [reducedDefect,onsetDefect,onsetFirstDefect,timeReducedCoefficient,sourceFactor]
  rw [show τ+T+y=τ+y+T by ring]
  ring

theorem reducedDefect_zero_outside (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T τ y : ℝ) (hT : 0 ≤ T) (hu : τ+y < -T ∨ 1 < τ+y) :
    reducedDefect q branch amp T τ y=0 := by
  obtain ⟨h0,h1⟩ := onsetDefect_zero_outside (2*physicalRate q branch) T (τ+y) hT hu
  simp only [reducedDefect,h0,h1,mul_zero,add_zero]

/-- The unreduced forcing retains its original full square and gradient channels. -/
theorem originalForcing_translation (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T τ y : ℝ) (z : D4BMHorizon.Point) :
    timeOriginalForcing q branch amp (τ+T) y z-
      sourceFactor q branch T*timeOriginalForcing q branch amp τ y z=
      originalForcing (physicalRate q branch) 0 amp 1
        (D4BMModularCore.fullSquarePotential q z) (D4BMModularCore.fullGradientEnergy q z/2) y*
        onsetDefect (2*physicalRate q branch) T (τ+y) := by
  simp only [timeOriginalForcing,onsetDefect,sourceFactor]
  rw [show τ+T+y=τ+y+T by ring]
  ring

/-- The complete original Dirichlet kernel applied to the actual source translation defect. -/
def defectDensity (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T τ x X k : ℝ) (p : ℝ × ℝ) : ℂ :=
  nativeDirichletCausalKernel q p.1 x p.2 X k*reducedDefect q branch amp T (τ+p.1) p.2

private theorem defectDensity_eq (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T τ x X k : ℝ) (p : ℝ × ℝ) :
    defectDensity q branch amp T τ x X k p=
      density q branch amp (τ+T) x X k p-sourceFactor q branch T*density q branch amp τ x X k p := by
  rw [defectDensity,reducedDefect_eq]
  simp only [density]
  rw [show τ+p.1+T=τ+T+p.1 by ring]
  ring

theorem defectDensity_integrable (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T τ x X k : ℝ) :
    IntegrableOn (defectDensity q branch amp T τ x X k) (Ioi 0 ×ˢ Iio 0) := by
  have he : defectDensity q branch amp T τ x X k=(fun p =>
      density q branch amp (τ+T) x X k p-sourceFactor q branch T*density q branch amp τ x X k p) :=
    funext (defectDensity_eq q branch amp T τ x X k)
  rw [he]
  exact (density_integrable q branch amp (τ+T) x X k).sub
    ((density_integrable q branch amp τ x X k).const_mul (sourceFactor q branch T))

/-- Exact finite translation identity in the established full reduced Bochner response. -/
theorem response_translation (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (T τ x X k : ℝ) :
    response q branch amp (τ+T) x X k-sourceFactor q branch T*response q branch amp τ x X k=
      ∫ p in Ioi 0 ×ˢ Iio 0,defectDensity q branch amp T τ x X k p := by
  simp_rw [defectDensity_eq]
  rw [integral_sub (density_integrable q branch amp (τ+T) x X k)
    ((density_integrable q branch amp τ x X k).const_mul (sourceFactor q branch T)),integral_const_mul]
  rfl

private theorem kernel_zero_before_target (q : XiZeroCopy) (τ x h y X k : ℝ)
    (hx : x < 0) (hbefore : τ+h+y < τ+x) :
    nativeDirichletCausalKernel q h x y X k=0 := by
  have hd : ¬ |x-y| ≤ h := by linarith [le_abs_self (x-y)]
  have hi : ¬ |x+y| ≤ h := by linarith [neg_le_abs (x+y)]
  simp only [nativeDirichletCausalKernel,if_neg hd,if_neg hi,sub_self,zero_div]

/-- On the late ingoing region neither causal arm reaches the finite onset defect. -/
theorem defectDensity_late_zero (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T τ x X k : ℝ) (hT : 0 ≤ T) (hx : x < 0) (hu : 1 < τ+x) (p : ℝ × ℝ) :
    defectDensity q branch amp T τ x X k p=0 := by
  by_cases hp : 1 < τ+p.1+p.2
  · simp only [defectDensity,reducedDefect_zero_outside q branch amp T (τ+p.1) p.2 hT (Or.inr hp),mul_zero]
  · have hk := kernel_zero_before_target q τ x p.1 p.2 X k hx (by linarith)
    simp only [defectDensity,hk,zero_mul]

/-- Late translation of the actual future response, with the original source rate unchanged. -/
theorem response_late_translation (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T τ x X k : ℝ) (hT : 0 ≤ T) (hx : x < 0) (hu : 1 < τ+x) :
    response q branch amp (τ+T) x X k=sourceFactor q branch T*response q branch amp τ x X k := by
  apply sub_eq_zero.mp
  rw [response_translation]
  simp only [defectDensity_late_zero q branch amp T τ x X k hT hx hu,integral_zero]

/-- The cap arm obeys the same finite translation law on its actual late source interval. -/
theorem boundaryArm_late_translation (q : XiZeroCopy) (branch : Bool)
    (T v x X k : ℝ) (hT : 0 ≤ T) (hv : 1 < v) :
    boundaryArm q branch (v+T) x X k=sourceFactor q branch T*boundaryArm q branch v x X k := by
  unfold boundaryArm
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  simp only [boundaryDensity]
  rw [show v+T+r=(v+r)+T by ring,
    onsetFirst_step (2*physicalRate q branch) T (v+r) hT (by linarith [show (0:ℝ)<r from hr])]
  dsimp only [sourceFactor]
  ring

/-- Both original direct/image cap arms are retained under late physical time translation. -/
theorem cap_late_translation (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T τ x X k : ℝ) (hT : 0 ≤ T) (hx : x < 0) (hu : 1 < τ+x) :
    capBoundaryField q branch amp (τ+T) x X k=
      sourceFactor q branch T*capBoundaryField q branch amp τ x X k := by
  simp only [capBoundaryField]
  rw [show τ+T+x=(τ+x)+T by ring,show τ+T-x=(τ-x)+T by ring,
    boundaryArm_late_translation q branch T (τ+x) x X k hT hu,
    boundaryArm_late_translation q branch T (τ-x) (-x) X k hT (by linarith)]
  ring

/-- The explicit original lift follows the same late source character. -/
theorem lift_late_translation (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T τ x : ℝ) (z : D4BMHorizon.Point) (hT : 0 ≤ T) (hu : 1 < τ+x) :
    timeLiftField q branch amp (τ+T) x z=sourceFactor q branch T*timeLiftField q branch amp τ x z := by
  simp only [timeLiftField,timeRadialLift]
  rw [show τ+T+x=(τ+x)+T by ring,onset_step (2*physicalRate q branch) T (τ+x) hT hu]
  dsimp only [sourceFactor]
  ring

/-- Translation of the derived cap-corrected future field at the original physical time. -/
theorem corrected_future_late_translation (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T τ x X k : ℝ) (hT : 0 ≤ T) (hx : x < 0) (hu : 1 < τ+x) :
    timeLiftField q branch amp (τ+T) x ![X,Real.exp k]+response q branch amp (τ+T) x X k-
      capBoundaryField q branch amp (τ+T) x X k=
    sourceFactor q branch T*(timeLiftField q branch amp τ x ![X,Real.exp k]+
      response q branch amp τ x X k-capBoundaryField q branch amp τ x X k) := by
  rw [lift_late_translation q branch amp T τ x _ hT hu,
    response_late_translation q branch amp T τ x X k hT hx hu,
    cap_late_translation q branch amp T τ x X k hT hx hu]
  ring

/-- The actual defect integral has the difference of the original past data as its horizon value. -/
theorem defect_response_past_horizon (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (T v X k : ℝ) :
    Tendsto (fun x => ∫ p in Ioi 0 ×ˢ Iio 0,defectDensity q branch amp T (v+x) x X k p) atBot
      (𝓝 (D4BMPastSourceResponse.pastResponse q branch amp (v+T) X k-
        sourceFactor q branch T*D4BMPastSourceResponse.pastResponse q branch amp v X k)) := by
  have h := (D4BMPastSourceResponse.response_past_horizon q branch amp (v+T) X k).sub
    ((D4BMPastSourceResponse.response_past_horizon q branch amp v X k).const_mul (sourceFactor q branch T))
  apply h.congr'
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [← response_translation,show v+x+T=v+T+x by ring])

end
end RHTower.D4BMSourceTimeTranslation
