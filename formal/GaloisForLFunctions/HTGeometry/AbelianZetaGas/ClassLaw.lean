import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModeExpectation

/-!
# The zeta-Gibbs law as a measure on the class space

The isomorphism classes of finite abelian groups form a countable set, so they carry the discrete
measurable structure; the zeta-Gibbs law is then the atomic measure whose mass at a class is the
class mass of the gas.  This is the carrier the Kullback–Leibler evaluation of Theorem 8.1 needs.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

instance : MeasurableSpace AbelianZetaGroupClass := ⊤

instance : MeasurableSingletonClass AbelianZetaGroupClass := ⟨fun _ => trivial⟩

/-- The zeta-Gibbs law as an atomic measure on the class space. -/
def classLaw (θ : AbelianZetaParameters) : Measure AbelianZetaGroupClass :=
  Measure.sum fun A => abelianZetaClassMass θ A • Measure.dirac A

theorem classLaw_singleton (θ : AbelianZetaParameters) (A : AbelianZetaGroupClass) :
    classLaw θ {A} = abelianZetaClassMass θ A := by
  classical
  rw [classLaw, Measure.sum_apply _ (MeasurableSet.singleton A)]
  rw [tsum_eq_single A (fun B hB => ?_)]
  · simp
  · rw [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton A),
      Set.indicator_of_notMem (by simpa using hB)]
    simp

/-- The class law is a probability measure in the convergence chamber. -/
theorem classLaw_univ (θ : AbelianZetaConvergentParameters) :
    classLaw θ.toAbelianZetaParameters Set.univ = 1 := by
  classical
  rw [classLaw, Measure.sum_apply _ MeasurableSet.univ]
  have hterm : ∀ A : AbelianZetaGroupClass,
      (abelianZetaClassMass θ.toAbelianZetaParameters A • Measure.dirac A) Set.univ
        = abelianZetaClassMass θ.toAbelianZetaParameters A := by
    intro A
    rw [Measure.smul_apply]
    simp
  rw [tsum_congr hterm]
  exact θ.tsum_classMass_eq_one

/-! ## Positivity and absolute continuity -/

theorem classMass_pos (θ : AbelianZetaConvergentParameters) (A : AbelianZetaGroupClass) :
    0 < abelianZetaClassMass θ.toAbelianZetaParameters A := by
  rw [θ.classMass_eq_ennNormalizer_mul_twoObservableWeight A]
  refine ENNReal.mul_pos (AbelianZetaConvergentParameters.ennNormalizer_ne_zero θ) ?_
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  rw [abelianZetaTwoObservableWeight]
  have hord : (0 : ℝ) < (A.order : ℝ) := by exact_mod_cast A.order_pos
  have hsoc : (0 : ℝ) < (A.socleOrder : ℝ) := by exact_mod_cast A.socleOrder_pos
  positivity

theorem classLaw_apply (θ : AbelianZetaParameters) (s : Set AbelianZetaGroupClass) :
    classLaw θ s = ∑' A : AbelianZetaGroupClass,
      abelianZetaClassMass θ A * s.indicator (fun _ => (1 : ℝ≥0∞)) A := by
  classical
  rw [classLaw, Measure.sum_apply _ (by trivial)]
  refine tsum_congr fun A => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ (by trivial)]
  simp only [smul_eq_mul]
  rfl

/-- **The class laws of any two convergent parameter points are mutually absolutely continuous.** -/
theorem classLaw_absolutelyContinuous (θ θ' : AbelianZetaConvergentParameters) :
    classLaw θ'.toAbelianZetaParameters ≪ classLaw θ.toAbelianZetaParameters := by
  classical
  intro s hs
  rw [classLaw_apply] at hs ⊢
  rw [ENNReal.tsum_eq_zero] at hs ⊢
  intro A
  have hA := hs A
  rcases mul_eq_zero.mp hA with hzero | hind
  · exact absurd hzero (classMass_pos θ A).ne'
  · rw [hind, mul_zero]

/-! ## The atomwise mass ratio of the canonical tilt -/

/-- The canonical unit tilt, in the convergence chamber. -/
def tiltConv (σ : EulerSigma) : AbelianZetaConvergentParameters where
  toAbelianZetaParameters := tiltParameters σ
  firstDepth := by
    have h := σ.one_lt
    have hp := σ.pos
    show (1 : ℝ) < σ.val + σ.val
    linarith

/-- **The atomwise mass of the canonical tilt.**  The class mass of the unit tilt is its normaliser
times the untilted Gibbs weight times `|soc A|^{−σ}`. -/
theorem classMass_tiltConv (σ : EulerSigma) (A : AbelianZetaGroupClass) :
    abelianZetaClassMass (tiltConv σ).toAbelianZetaParameters A
      = (tiltConv σ).ennNormalizer
        * ENNReal.ofReal (abelianZetaTwoObservableWeight
            (AbelianZetaParameters.temperatureParameters σ.val σ.pos) A
          * ((A.socleOrder : ℝ) ^ (-σ.val))) := by
  rw [(tiltConv σ).classMass_eq_ennNormalizer_mul_twoObservableWeight A]
  congr 2
  exact twoObservableWeight_tiltParameters σ A

/-! ## The tilt as a density -/

theorem withDensity_singleton (μ : Measure AbelianZetaGroupClass)
    (d : AbelianZetaGroupClass → ℝ≥0∞) (A : AbelianZetaGroupClass) :
    (μ.withDensity d) {A} = d A * μ {A} := by
  rw [withDensity_apply d (by trivial), lintegral_singleton]

/-- The constant in the Radon–Nikodym density of the canonical tilt. -/
def densityConst (σ : EulerSigma) : ℝ≥0∞ :=
  (tiltConv σ).ennNormalizer / (temperatureConv σ).ennNormalizer

/-- **The canonical unit tilt is a density against the untilted law.** -/
theorem classLaw_tiltConv_eq_withDensity (σ : EulerSigma) :
    classLaw (tiltConv σ).toAbelianZetaParameters
      = (classLaw (temperatureConv σ).toAbelianZetaParameters).withDensity
        (fun A => densityConst σ * ENNReal.ofReal ((A.socleOrder : ℝ) ^ (-σ.val))) := by
  refine Measure.ext_of_singleton fun A => ?_
  rw [classLaw_singleton, withDensity_singleton, classLaw_singleton,
    classMass_tiltConv σ A,
    (temperatureConv σ).classMass_eq_ennNormalizer_mul_twoObservableWeight A]
  have hw : (0 : ℝ) ≤ abelianZetaTwoObservableWeight
      (AbelianZetaParameters.temperatureParameters σ.val σ.pos) A :=
    AbelianZetaConvergentParameters.twoObservableWeight_nonneg _ A
  have hs : (0 : ℝ) ≤ ((A.socleOrder : ℝ) ^ (-σ.val)) := Real.rpow_nonneg (by positivity) _
  rw [ENNReal.ofReal_mul hw]
  have hne : (temperatureConv σ).ennNormalizer ≠ 0 :=
    AbelianZetaConvergentParameters.ennNormalizer_ne_zero _
  have htop : (temperatureConv σ).ennNormalizer ≠ ⊤ := by
    rw [AbelianZetaConvergentParameters.ennNormalizer]
    exact ENNReal.coe_ne_top
  have hc : (tiltConv σ).ennNormalizer / (temperatureConv σ).ennNormalizer
      * (temperatureConv σ).ennNormalizer = (tiltConv σ).ennNormalizer :=
    ENNReal.div_mul_cancel hne htop
  have hweq : abelianZetaTwoObservableWeight (temperatureConv σ).toAbelianZetaParameters A
      = abelianZetaTwoObservableWeight
          (AbelianZetaParameters.temperatureParameters σ.val σ.pos) A := rfl
  rw [densityConst, hweq]
  conv_lhs => rw [← hc]
  ring


end

end GaloisForLFunctions.HTGeometry
