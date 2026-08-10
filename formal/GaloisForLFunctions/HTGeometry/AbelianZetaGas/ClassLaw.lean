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

end

end GaloisForLFunctions.HTGeometry
