import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceExplicitResidual

/-! The explicit cusp subtraction is a genuine differentiated field for the original wave operator. -/
open Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse D4BMHorizon D4BMAngularSeries
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def explicitFieldFirst (q : XiZeroCopy) (branch : Bool) (w a T : ℂ) (t : ℝ) (z : Point) : ℂ :=
  radialLiftFirst (physicalRate q branch) w a T t*fullSquarePotential q z+
    ∑ i : Fin 3, principalDifferenceFirst q branch w a T i t*cutoffPower (principalExponent q i) z

def explicitFieldSecond (q : XiZeroCopy) (branch : Bool) (w a T : ℂ) (t : ℝ) (z : Point) : ℂ :=
  radialLiftSecond (physicalRate q branch) w a T t*fullSquarePotential q z+
    ∑ i : Fin 3, principalDifferenceSecond q branch w a T i t*cutoffPower (principalExponent q i) z

theorem explicitField_hasDerivAt (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (t : ℝ) (ht : t < 0) (z : Point) :
    HasDerivAt (fun x => explicitField q branch w a T x z) (explicitFieldFirst q branch w a T t z) t ∧
      HasDerivAt (fun x => explicitFieldFirst q branch w a T x z) (explicitFieldSecond q branch w a T t z) t := by
  constructor
  · exact ((radialLift_hasDerivAt _ _ _ _ t).mul_const _).add
      (HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
        (principalDifference_hasDerivAt q branch w a T hw i t ht).1.mul_const _))
  · exact ((radialLiftFirst_hasDerivAt _ _ _ _ t).mul_const _).add
      (HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
        (principalDifference_hasDerivAt q branch w a T hw i t ht).2.mul_const _))

theorem explicitField_secondDerivative (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (t : ℝ) (ht : t < 0) (z : Point) :
    deriv (deriv (fun x => explicitField q branch w a T x z)) t = explicitFieldSecond q branch w a T t z := by
  have he : deriv (fun x => explicitField q branch w a T x z) =ᶠ[𝓝 t]
      (fun x => explicitFieldFirst q branch w a T x z) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
    exact (explicitField_hasDerivAt q branch w a T hw x hx z).1.deriv
  rw [he.deriv_eq]
  exact (explicitField_hasDerivAt q branch w a T hw t ht z).2.deriv

private theorem laplacian_sum {ι : Type*} (s : Finset ι) (f : ι → Point → ℂ)
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

theorem explicitField_laplacian (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (t : ℝ) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian (explicitField q branch w a T t) z =
      radialLift (physicalRate q branch) w a T t*scalarLaplacian (fullSquarePotential q) z+
      ∑ i : Fin 3, principalDifference q branch w a T i t*
        scalarLaplacian (cutoffPower (principalExponent q i)) z := by
  have hQ : ContDiffAt ℝ 2 (fullSquarePotential q) z := fullSquarePotential_smooth q z hz 2
  have hP (i : Fin 3) : ContDiffAt ℝ 2 (cutoffPower (principalExponent q i)) z :=
    ((contDiff_infty.mp sourceCutoff_smooth) 2).contDiffAt.mul
      ((height_cpow_contDiffOn (principalExponent q i) 2).contDiffAt
        ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz))
  simp_rw [scalarLaplacian_eq _ z hz]
  change hyperbolicLaplacian (explicitField q branch w a T t) z =
    radialLift (physicalRate q branch) w a T t*hyperbolicLaplacian (fullSquarePotential q) z+
      ∑ i : Fin 3, principalDifference q branch w a T i t*
        hyperbolicLaplacian (cutoffPower (principalExponent q i)) z
  unfold explicitField
  rw [hyperbolicLaplacian_add (contDiffAt_const.mul hQ)
    (ContDiffAt.sum (fun i _ => contDiffAt_const.mul (hP i))),
    hyperbolicLaplacian_const_mul hQ,laplacian_sum _ _ z (fun i _ => contDiffAt_const.mul (hP i))]
  simp_rw [hyperbolicLaplacian_const_mul (hP _)]

/-- Original scalar wave with actual radial and metric angular derivatives. -/
def fieldWave (w : ℂ) (U : ℝ → Point → ℂ) (t : ℝ) (z : Point) : ℂ :=
  w^2*U t z-deriv (deriv (fun x => U x z)) t-(horizonCoordinate t:ℂ)*scalarLaplacian (U t) z

/-- The angular coefficient is exactly the squared weight in the constructed joint energy domain. -/
theorem horizonCoordinate_jointWeight (t : ℝ) (ht : t < 0) :
    (horizonCoordinate t:ℂ) = D4BMJointWave.angularWeight t^2 := by
  have hr := D4BMJointWave.tortoiseRadius_exterior t ht
  have hr0 : (D4BMJointWave.tortoiseRadius t:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < D4BMJointWave.tortoiseRadius t))
  rw [D4BMJointWave.angularWeight_original_coefficient t ht,horizonCoordinate,radialUnit_inverse_radius]
  push_cast
  field_simp

/-- The separated expression is exactly the full differentiated field, not assigned derivative slots. -/
theorem explicitField_wave (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (t : ℝ) (ht : t < 0) (z : Point) (hz : 0 < z 1) :
    fieldWave w (explicitField q branch w a T) t z = explicitSeparatedWave q branch w a T t z := by
  unfold fieldWave
  rw [explicitField_secondDerivative q branch w a T hw t ht z,explicitField_laplacian q branch w a T t z hz]
  unfold explicitSeparatedWave separatedScalarWave
  simp_rw [(radialLift_derivatives (physicalRate q branch) w a T).2,
    principalDifference_secondDerivative q branch w a T hw _ t ht]
  dsimp only [explicitField,explicitFieldSecond,horizonCoordinate]
  push_cast
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  ring

end
end RHTower.D4BMJointSource
