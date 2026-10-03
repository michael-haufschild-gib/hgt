import GaloisForLFunctions.RHTower.ThetaTailJointCorrelation
import GaloisForLFunctions.RHTower.ThetaConfluentCoordinateEnergy

/-! Literal joint derivatives of the tail kernel, through the mixed fourth-order
entries needed for the two-axis center Schur extension. -/

noncomputable section
open MeasureTheory Set
namespace RHTower.ThetaJoint
open ThetaConfluent ThetaCoordinate

private abbrev s := thetaCuspSchwartzReal
private abbrev d := SchwartzMap.derivCLM ℝ ℝ s
private abbrev dd := SchwartzMap.derivCLM ℝ ℝ d
private abbrev ddd := SchwartzMap.derivCLM ℝ ℝ dd

def firstLeft (x y : ℝ) : ℝ := correlation s s x y + kernel d s x y
def secondLeft (x y : ℝ) : ℝ := 2*correlation d s x y + kernel dd s x y
def thirdLeft (x y : ℝ) : ℝ := 3*correlation dd s x y + kernel ddd s x y
def mixed (x y : ℝ) : ℝ :=
  correlation d s x y + correlation s d x y + kernel d d x y
def mixedRight (x y : ℝ) : ℝ :=
  2*correlation d d x y + correlation s dd x y + kernel d dd x y
def mixedBoth (x y : ℝ) : ℝ :=
  2*correlation dd d x y + 2*correlation d dd x y + kernel dd dd x y
def mixedRightTwice (x y : ℝ) : ℝ :=
  3*correlation d dd x y + correlation s ddd x y + kernel d ddd x y

theorem firstLeft_continuous : Continuous fun p : ℝ × ℝ => firstLeft p.1 p.2 :=
  (correlation_continuous s s).add (kernel_continuous d s)

theorem secondLeft_continuous : Continuous fun p : ℝ × ℝ => secondLeft p.1 p.2 :=
  ((correlation_continuous d s).const_mul 2).add (kernel_continuous dd s)

theorem thirdLeft_continuous : Continuous fun p : ℝ × ℝ => thirdLeft p.1 p.2 :=
  ((correlation_continuous dd s).const_mul 3).add (kernel_continuous ddd s)

theorem mixed_continuous : Continuous fun p : ℝ × ℝ => mixed p.1 p.2 :=
  ((correlation_continuous d s).add (correlation_continuous s d)).add
    (kernel_continuous d d)

theorem mixedRight_continuous : Continuous fun p : ℝ × ℝ => mixedRight p.1 p.2 :=
  (((correlation_continuous d d).const_mul 2).add (correlation_continuous s dd)).add
    (kernel_continuous d dd)

theorem mixedBoth_continuous : Continuous fun p : ℝ × ℝ => mixedBoth p.1 p.2 :=
  (((correlation_continuous dd d).const_mul 2).add
    ((correlation_continuous d dd).const_mul 2)).add (kernel_continuous dd dd)

theorem mixedRightTwice_continuous :
    Continuous fun p : ℝ × ℝ => mixedRightTwice p.1 p.2 :=
  (((correlation_continuous d dd).const_mul 3).add (correlation_continuous s ddd)).add
    (kernel_continuous d ddd)

theorem source_hasDerivAt_left (x y : ℝ) :
    HasDerivAt (fun x => thetaTailFirstMomentKernel x y) (firstLeft x y) x := by
  rw [show (fun x => thetaTailFirstMomentKernel x y) = (fun x => kernel s s x y)
    from funext fun x => (source_kernel_eq x y).symm]
  exact kernel_hasDerivAt_left s s x y

theorem source_hasDerivAt_right (x y : ℝ) :
    HasDerivAt (thetaTailFirstMomentKernel x) (firstLeft y x) y := by
  rw [show thetaTailFirstMomentKernel x = (fun y => thetaTailFirstMomentKernel y x)
    from funext (thetaTailFirstMomentKernel_comm x)]
  exact source_hasDerivAt_left y x

theorem firstLeft_hasDerivAt_left (x y : ℝ) :
    HasDerivAt (fun x => firstLeft x y) (secondLeft x y) x := by
  convert! (correlation_hasDerivAt_left s s x y).add
    (kernel_hasDerivAt_left d s x y) using 1
  simp only [secondLeft]
  ring

theorem firstLeft_hasDerivAt_right (x y : ℝ) :
    HasDerivAt (firstLeft x) (mixed x y) y := by
  convert! (correlation_hasDerivAt_right s s x y).add
    (kernel_hasDerivAt_right d s x y) using 1
  simp only [mixed]
  ring

theorem secondLeft_hasDerivAt_left (x y : ℝ) :
    HasDerivAt (fun x => secondLeft x y) (thirdLeft x y) x := by
  convert! ((correlation_hasDerivAt_left d s x y).const_mul 2).add
    (kernel_hasDerivAt_left dd s x y) using 1
  simp only [thirdLeft]
  ring

theorem mixed_symm (x y : ℝ) : mixed x y = mixed y x := by
  unfold mixed
  rw [correlation_symm d s x y, correlation_symm s d x y, kernel_symm d d x y]
  ring

theorem mixed_hasDerivAt_right (x y : ℝ) :
    HasDerivAt (mixed x) (mixedRight x y) y := by
  convert! ((correlation_hasDerivAt_right d s x y).add
    (correlation_hasDerivAt_right s d x y)).add (kernel_hasDerivAt_right d d x y) using 1
  simp only [mixedRight]
  ring

theorem mixed_hasDerivAt_left (x y : ℝ) :
    HasDerivAt (fun x => mixed x y) (mixedRight y x) x := by
  rw [show (fun x => mixed x y) = mixed y from funext fun x => mixed_symm x y]
  exact mixed_hasDerivAt_right y x

theorem mixedRight_hasDerivAt_left (x y : ℝ) :
    HasDerivAt (fun x => mixedRight x y) (mixedBoth x y) x := by
  convert! (((correlation_hasDerivAt_left d d x y).const_mul 2).add
    (correlation_hasDerivAt_left s dd x y)).add (kernel_hasDerivAt_left d dd x y) using 1
  simp only [mixedBoth]
  ring

theorem mixedRight_hasDerivAt_right (x y : ℝ) :
    HasDerivAt (mixedRight x) (mixedRightTwice x y) y := by
  convert! (((correlation_hasDerivAt_right d d x y).const_mul 2).add
    (correlation_hasDerivAt_right s dd x y)).add (kernel_hasDerivAt_right d dd x y) using 1
  simp only [mixedRightTwice]
  ring

private theorem d_zero : d 0 = 0 := by
  change deriv thetaCuspFullSource 0 = 0
  simpa only [iteratedDeriv_one] using
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 1) ⟨0,rfl⟩

private theorem corr_sd : correlation s d 0 0 = -thetaCuspFullSource 0^2/2 := by
  have h := correlation_origin_parts s s
  rw [correlation_symm d s] at h
  change correlation s d 0 0 = -(s 0)^2/2
  nlinarith only [h]

private theorem corr_d_dd : correlation d dd 0 0 = 0 := by
  have h := correlation_origin_parts d d
  rw [correlation_symm dd d, d_zero] at h
  linarith only [h]

private theorem kernel_dd : kernel d d 0 0 = 2*derivativeMass := by
  simp only [kernel, correlation, sub_self, zero_mul, zero_add, weighted_apply]
  congr 1
  unfold derivativeMass
  apply integral_congr_ae
  filter_upwards with t
  change t*deriv thetaCuspFullSource t*deriv thetaCuspFullSource t = _
  ring

private theorem kernel_dd_dd : kernel dd dd 0 0 = 2*secondMass := by
  simp only [kernel, correlation, sub_self, zero_mul, zero_add, weighted_apply]
  congr 1
  unfold secondMass
  apply integral_congr_ae
  filter_upwards with t
  change t*deriv (deriv thetaCuspFullSource) t*deriv (deriv thetaCuspFullSource) t = _
  ring

private theorem kernel_d_ddd : kernel d ddd 0 0 = -2*secondMass := by
  simp only [kernel, correlation, sub_self, zero_mul, zero_add, weighted_apply]
  change 2*(∫ t in Ioi 0,
    t*deriv thetaCuspFullSource t*deriv (deriv (deriv thetaCuspFullSource)) t) = _
  rw [mixed_third_integral]
  ring

theorem firstLeft_origin : firstLeft 0 0 = 0 := by
  unfold firstLeft
  rw [kernel_symm d s, kernel_origin_diagonal]
  ring

theorem secondLeft_origin : secondLeft 0 0 = -2*derivativeMass := by
  have h := kernel_origin_parts d s
  rw [kernel_dd] at h
  unfold secondLeft
  linarith only [h]

theorem mixed_origin : mixed 0 0 = centerEntry := by
  unfold mixed centerEntry
  rw [correlation_symm d s, corr_sd, kernel_dd]
  ring

theorem mixedRight_origin : mixedRight 0 0 = 0 := by
  have h := correlation_origin_parts s d
  rw [d_zero] at h
  unfold mixedRight
  rw [kernel_origin_diagonal]
  linarith only [h]

theorem mixedBoth_origin : mixedBoth 0 0 = 2*secondMass := by
  unfold mixedBoth
  rw [correlation_symm dd d, corr_d_dd, kernel_dd_dd]
  ring

theorem mixedRightTwice_origin : mixedRightTwice 0 0 =
    thetaCuspLogCurvature 0*thetaCuspFullSource 0^2-2*secondMass := by
  have h := correlation_origin_parts s dd
  have hz : dd 0 = -thetaCuspLogCurvature 0*thetaCuspFullSource 0 := source_second_center
  change correlation s ddd 0 0 = -s 0*dd 0-correlation d dd 0 0 at h
  rw [hz, corr_d_dd] at h
  unfold mixedRightTwice
  rw [corr_d_dd, h, kernel_d_ddd]
  change 3*0+(-thetaCuspFullSource 0*(-thetaCuspLogCurvature 0*thetaCuspFullSource 0)-0)+
    -2*secondMass = _
  ring

end RHTower.ThetaJoint
