import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceFullForcingContinuation

/-! The continued cusp subtraction is an actual differentiated field of the original wave operator. -/
open Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open Complex D4BMLaplaceRadial D4BMModularCore D4BMGlobalAngularResponse D4BMHorizon D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def continuedExplicitFieldFirst (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (t : ℝ) (z : Point) : ℂ :=
  radialLiftFirst (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*fullSquarePotential q z+
    ∑ i : Fin 3, continuedPrincipalDifferenceFirst q branch w a i t*cutoffPower (principalExponent q i) z

def continuedExplicitFieldSecond (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (t : ℝ) (z : Point) : ℂ :=
  radialLiftSecond (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*fullSquarePotential q z+
    ∑ i : Fin 3, continuedPrincipalDifferenceSecond q branch w a i t*cutoffPower (principalExponent q i) z

theorem continuedExplicitField_hasDerivAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (t : ℝ) (ht : t < 0) (z : Point) :
    HasDerivAt (fun x => continuedExplicitField q branch w a x z) (continuedExplicitFieldFirst q branch w a t z) t ∧
      HasDerivAt (fun x => continuedExplicitFieldFirst q branch w a x z) (continuedExplicitFieldSecond q branch w a t z) t := by
  constructor
  · exact ((radialLift_hasDerivAt _ _ _ _ t).mul_const _).add
      (HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
        (continuedPrincipalDifference_hasDerivAt q branch w a hw hwre i t ht).1.mul_const _))
  · exact ((radialLiftFirst_hasDerivAt _ _ _ _ t).mul_const _).add
      (HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
        (continuedPrincipalDifference_hasDerivAt q branch w a hw hwre i t ht).2.mul_const _))

theorem continuedExplicitField_secondDerivative (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (t : ℝ) (ht : t < 0) (z : Point) :
    deriv (deriv (fun x => continuedExplicitField q branch w a x z)) t = continuedExplicitFieldSecond q branch w a t z := by
  have he : deriv (fun x => continuedExplicitField q branch w a x z) =ᶠ[𝓝 t]
      (fun x => continuedExplicitFieldFirst q branch w a x z) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
    exact (continuedExplicitField_hasDerivAt q branch w a hw hwre x hx z).1.deriv
  rw [he.deriv_eq]
  exact (continuedExplicitField_hasDerivAt q branch w a hw hwre t ht z).2.deriv

private theorem continued_laplacian_sum {ι : Type*} (s : Finset ι) (f : ι → Point → ℂ)
    (z : Point) (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) :
    hyperbolicLaplacian (fun x => ∑ i ∈ s, f i x) z = ∑ i ∈ s, hyperbolicLaplacian (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty,zero_mul] using
      (hyperbolicLaplacian_const_mul (f := fun _ : Point => (1:ℂ)) (z := z) contDiffAt_const (0:ℂ))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [hyperbolicLaplacian_add (hf i (Finset.mem_insert_self _ _))
      (ContDiffAt.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

theorem continuedExplicitField_laplacian (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (t : ℝ) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian (continuedExplicitField q branch w a t) z =
      radialLift (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*scalarLaplacian (fullSquarePotential q) z+
      ∑ i : Fin 3, continuedPrincipalDifference q branch w a i t*
        scalarLaplacian (cutoffPower (principalExponent q i)) z := by
  have hQ : ContDiffAt ℝ 2 (fullSquarePotential q) z := fullSquarePotential_smooth q z hz 2
  have hP (i : Fin 3) : ContDiffAt ℝ 2 (cutoffPower (principalExponent q i)) z :=
    ((contDiff_infty.mp sourceCutoff_smooth) 2).contDiffAt.mul
      ((height_cpow_contDiffOn (principalExponent q i) 2).contDiffAt
        ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz))
  simp_rw [scalarLaplacian_eq _ z hz]
  change hyperbolicLaplacian (continuedExplicitField q branch w a t) z =
    radialLift (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*hyperbolicLaplacian (fullSquarePotential q) z+
      ∑ i : Fin 3, continuedPrincipalDifference q branch w a i t*
        hyperbolicLaplacian (cutoffPower (principalExponent q i)) z
  unfold continuedExplicitField
  rw [hyperbolicLaplacian_add (contDiffAt_const.mul hQ)
    (ContDiffAt.sum (fun i _ => contDiffAt_const.mul (hP i))),
    hyperbolicLaplacian_const_mul hQ,continued_laplacian_sum _ _ z (fun i _ => contDiffAt_const.mul (hP i))]
  simp_rw [hyperbolicLaplacian_const_mul (hP _)]

/-- The separated expression is exactly the full differentiated field, not assigned derivative slots. -/
theorem continuedExplicitField_wave (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (t : ℝ) (ht : t < 0) (z : Point) (hz : 0 < z 1) :
    fieldWave w (continuedExplicitField q branch w a) t z = continuedExplicitSeparatedWave q branch w a t z := by
  unfold fieldWave
  rw [continuedExplicitField_secondDerivative q branch w a hw hwre t ht z,continuedExplicitField_laplacian q branch w a t z hz]
  unfold continuedExplicitSeparatedWave separatedScalarWave
  simp_rw [(radialLift_derivatives (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w)).2,
    continuedPrincipalDifference_secondDerivative q branch w a hw hwre _ t ht]
  dsimp only [continuedExplicitField,continuedExplicitFieldSecond,horizonCoordinate]
  push_cast
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  ring

/-- The complete original forcing equals the actual differentiated continued field plus
its full cutoff residual on one punctured frequency neighborhood, uniformly in spatial points. -/
theorem originalForcing_continuedField_germ (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) :
    ∀ᶠ u in 𝓝[≠] w, ∀ t < 0, ∀ z : UpperHalfPlane,
      originalForcing (physicalRate q branch) u a (continuedOnset (physicalRate q branch) u)
          (fullSquarePotential q (coordinates z)) (fullGradientEnergy q (coordinates z)/2) t =
        fieldWave u (continuedExplicitField q branch u a) t (coordinates z)+
          continuedCuspResidualForcing q branch u a (t,z) := by
  have hi := (Complex.continuous_im.continuousAt.eventually_ne hw).filter_mono
    (show 𝓝[≠] w ≤ 𝓝 w from inf_le_left)
  have hr := (Complex.continuous_re.continuousAt.eventually_const_lt hwre).filter_mono
    (show 𝓝[≠] w ≤ 𝓝 w from inf_le_left)
  have hc : ∀ᶠ u in 𝓝[≠] w, ∀ i : Fin 3, connection u (principalFrequency q i) ≠ 0 :=
    Filter.eventually_all.mpr (fun i => connection_eventually_ne_zero w (principalFrequency q i) hw)
  filter_upwards [hi,hr,hc] with u hui hur huc
  intro t ht z
  rw [continuedExplicitField_wave q branch u a hui hur t ht _ z.im_pos]
  exact originalForcing_continuedExplicitResidual q branch u a hui hur huc t ht z

/-- At both fundamental QNMs of every Xi copy, the full original source has its exact
continued field/cutoff decomposition with actual radial and metric angular derivatives. -/
theorem originalForcing_allXi_fundamental_continuedField (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
    ∀ᶠ u in 𝓝[≠] w, ∀ t < 0, ∀ z : UpperHalfPlane,
      originalForcing (physicalRate q branch) u a (continuedOnset (physicalRate q branch) u)
          (fullSquarePotential q (coordinates z)) (fullGradientEnergy q (coordinates z)/2) t =
        fieldWave u (continuedExplicitField q branch u a) t (coordinates z)+
          continuedCuspResidualForcing q branch u a (t,z) := by
  have hq := thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q
  have hs := abs_im_xiSpectralPoint_lt_half q
  rw [abs_lt] at hs
  intro w hw
  have hstrip : w.im ≠ 0 ∧ -2 < w.re := by
    simp only [mem_insert_iff,mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;>
      simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,thetaCuspHawkingTopologicalBlackHoleQNMMinus,
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum,thetaCuspHawkingTopologicalBlackHoleConformalDecay,
        Complex.mul_im,Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
        Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,Complex.add_im,Complex.div_re,Complex.div_im]
    all_goals norm_num
    · exact ⟨hq,by linarith [hs.1]⟩
    · exact ⟨hq,by linarith [hs.2]⟩
  exact originalForcing_continuedField_germ q branch w a hstrip.1 hstrip.2

end
end RHTower.D4BMJointSource
