import GaloisForLFunctions.RHTower.PaperZetaCycleVaryingPeriods
import GaloisForLFunctions.RHTower.PaperZetaCyclePhysicalReconstruction
import GaloisForLFunctions.RHTower.CCM.CCMArithmeticPrimeFredholmTrace

/-! # Simultaneous reconstruction of arithmetic-prime Fredholm traces

All actual prime/grade source objects form a countable family. Their native
arithmetic coefficients reconstruct the traces at a common normalized phase or
a common physical height. The grade coefficient and completed-Xi receiver are
unchanged by normalization.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry
open scoped BigOperators SchwartzMap

namespace CCMArithmeticPrimeFredholmCycle

instance paperCountablePrimeFredholmCycle : Countable CCMArithmeticPrimeFredholmCycle := by
  apply Function.Injective.countable (f := fun X : CCMArithmeticPrimeFredholmCycle =>
    (X.prime, X.grade))
  rintro ⟨p, m⟩ ⟨q, n⟩ h
  rcases Prod.mk.inj h with ⟨rfl, rfl⟩
  rfl

/-- Unit-circle normalization preserves the actual Fredholm-grade source coefficient. -/
theorem paperUnitTrace_grade_formula (X : CCMArithmeticPrimeFredholmCycle)
    (f : DeningerMeyerCap) :
    fourierCoeff (paperZetaCycleUnitTrace X.zetaCircleLength f) X.grade =
      (1 / (X.zetaCircleLength : ℝ)) •
        (riemannZeta (ccmZetaCircleCriticalPoint X.zetaCircleLength X.grade) *
          mellin (f : 𝓢(ℝ, ℂ)) (ccmZetaCircleCriticalPoint X.zetaCircleLength X.grade)) := by
  rw [paperZetaCycleUnitTrace_fourierCoeff]
  exact X.primeFredholm_sourceTrace_formula f

/-- The existing Xi receiver is exactly the same after placing all cycles on one circle. -/
theorem paperXi_eq_zero_iff_unitTrace (X : CCMArithmeticPrimeFredholmCycle) :
    XiC (X.horizontalOrientation : ℂ) = 0 ↔
      ∀ f : DeningerMeyerCap,
        fourierCoeff (paperZetaCycleUnitTrace X.zetaCircleLength f) X.grade = 0 := by
  simp only [paperZetaCycleUnitTrace_fourierCoeff]
  exact X.completedXi_horizontalOrientation_eq_zero_iff_sourceTrace

/-- Every prime, every nonzero grade, and every cap in a prescribed countable family
are reconstructed simultaneously at normalized phase. -/
theorem paperAllPrimes_common_unit_span_reconstruction
    {κ : Type*} [Countable κ] (f : CCMArithmeticPrimeFredholmCycle → κ → DeningerMeyerCap) :
    ∃ E : Set UnitAddCircle, MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ (S : Finset (CCMArithmeticPrimeFredholmCycle × κ))
        (c : CCMArithmeticPrimeFredholmCycle × κ → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j *
          paperZetaCycleUnitArithmeticSum j.1.zetaCircleLength (f j.1 j.2) N x)
          atTop (𝓝 (∑ j ∈ S, c j * paperZetaCycleUnitTrace j.1.zetaCircleLength (f j.1 j.2) x)) :=
  paperZetaCycle_varying_periods_common_span_reconstruction
    (fun j : CCMArithmeticPrimeFredholmCycle × κ => j.1.zetaCircleLength)
    (fun j => f j.1 j.2)

/-- The same physical real height works for every prime/grade and every finite mixture. -/
theorem paperAllPrimes_common_physical_span_reconstruction
    {κ : Type*} [Countable κ] (f : CCMArithmeticPrimeFredholmCycle → κ → DeningerMeyerCap) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ (S : Finset (CCMArithmeticPrimeFredholmCycle × κ))
        (c : CCMArithmeticPrimeFredholmCycle × κ → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j * paperZetaCycleArithmeticSum j.1.zetaCircleLength
          (f j.1 j.2) N (t : AddCircle (j.1.zetaCircleLength : ℝ)))
          atTop (𝓝 (∑ j ∈ S, c j * ccmZetaCycleTrace j.1.zetaCircleLength (f j.1 j.2)
            (t : AddCircle (j.1.zetaCircleLength : ℝ)))) :=
  paperZetaCycle_common_physical_span_reconstruction
    (fun j : CCMArithmeticPrimeFredholmCycle × κ => j.1.zetaCircleLength)
    (fun j => f j.1 j.2)

/-- The common real exceptional set also covers any prescribed countable family of flows. -/
theorem paperAllPrimes_flow_common_physical_span_reconstruction
    {κ ι : Type*} [Countable κ] [Countable ι]
    (f : CCMArithmeticPrimeFredholmCycle → κ → DeningerMeyerCap) (a : ι → ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ (S : Finset ((CCMArithmeticPrimeFredholmCycle × κ) × ι))
        (c : (CCMArithmeticPrimeFredholmCycle × κ) × ι → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j * paperZetaCycleArithmeticSum j.1.1.zetaCircleLength
          (deningerMeyerCapFlow (a j.2) (f j.1.1 j.1.2)) N
            (t : AddCircle (j.1.1.zetaCircleLength : ℝ)))
          atTop (𝓝 (∑ j ∈ S, c j * ((Real.exp (a j.2 / 2) : ℝ) : ℂ) *
            ccmZetaCycleTrace j.1.1.zetaCircleLength (f j.1.1 j.1.2)
              ((t - a j.2 : ℝ) : AddCircle (j.1.1.zetaCircleLength : ℝ)))) :=
  paperZetaCycle_flow_common_physical_span_reconstruction
    (fun j : CCMArithmeticPrimeFredholmCycle × κ => j.1.zetaCircleLength)
    (fun j => f j.1 j.2) a

end CCMArithmeticPrimeFredholmCycle
end
end RHTower
