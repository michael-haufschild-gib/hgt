import GaloisForLFunctions.HTGeometry.FamilyMobiusGauge
import GaloisForLFunctions.HTGeometry.ExponentialFullIndependence
import GaloisForLFunctions.HTGeometry.MovingCanonicalUpperEndDifferentialIndependence
import GaloisForLFunctions.HTGeometry.HerglotzDiscreteSupportFreeness
import GaloisForLFunctions.HTGeometry.ParabolicOrbitCircleClosure

/-!
# The Cayley outer gauge

The Cayley exponential `chi(w) = exp((w - i) / (w + i))` is an invertible rational map followed by
the exponential.  Both steps already have gauges: a differential relation among Mobius images
descends to the family, and exponentials of a differentially independent analytic family stay
independent.  So a family with values in the closed upper half plane keeps its differential
independence after passing to Cayley exponentials.

Applied to the translates of a Cauchy transform this turns the corpus's residual freeness of the
Cauchy family into residual freeness of the associated bounded outer functions.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

theorem add_I_ne_zero_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) : w + Complex.I ≠ 0 := by
  intro hzero
  have hw' : w = -Complex.I := by linear_combination hzero
  rw [hw'] at hw
  simp at hw
  linarith

/-- **The Cayley outer gauge.**  If an analytic family whose values avoid `-i` satisfies no
differential relation on a connected domain, neither does the family of its Cayley exponentials. -/
theorem not_familyDifferentiallyAlgebraicOn_cayleyOuter {m : ℕ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {g : Fin m → ℂ → ℂ} (hg : ∀ i, AnalyticOnNhd ℂ (g i) U)
    (hden : ∀ i, ∀ w ∈ U, g i w + Complex.I ≠ 0)
    (hfree : ¬ FamilyDifferentiallyAlgebraicOn g U) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i w => Complex.exp ((g i w - Complex.I) / (g i w + Complex.I))) U := by
  have hdenM : ∀ i, ∀ w ∈ U, (1 : ℂ) * g i w + Complex.I ≠ 0 := by
    intro i w hw
    rw [one_mul]
    exact hden i w hw
  have hsigma : ∀ i, AnalyticOnNhd ℂ
      (fun w => ((1 : ℂ) * g i w + -Complex.I) / ((1 : ℂ) * g i w + Complex.I)) U := by
    intro i
    refine AnalyticOnNhd.div ?_ ?_ ?_
    · exact (analyticOnNhd_const.mul (hg i)).add analyticOnNhd_const
    · exact (analyticOnNhd_const.mul (hg i)).add analyticOnNhd_const
    · intro w hw
      exact hdenM i w hw
  have hmob : ¬ FamilyDifferentiallyAlgebraicOn
      (fun i w => ((1 : ℂ) * g i w + -Complex.I) / ((1 : ℂ) * g i w + Complex.I)) U := by
    intro hrel
    refine hfree (familyDifferentiallyAlgebraicOn_of_mobius hUo
      (fun i w hw => ((hg i) w hw).contDiffAt) ?_ hdenM hrel)
    intro hzero
    have : (2 : ℂ) * Complex.I = 0 := by linear_combination hzero
    simp at this
  have hexp := not_familyDifferentiallyAlgebraicOn_exp hUo hUc hUne hsigma hmob
  intro hrel
  refine hexp (familyDifferentiallyAlgebraicOn_congr_of_isOpen hUo (fun i z _ => ?_) hrel)
  congr 2 <;> ring

/-! ## The outer functions of a translated Cauchy family -/

theorem analyticOnNhd_cauchyTransform_translate (ν : Measure ℝ) [IsFiniteMeasure ν] {m : ℕ}
    (shift : InjectiveShiftConfiguration (Fin m)) (i : Fin m) :
    AnalyticOnNhd ℂ (fun z => cauchyTransform ν (z + shift.1 i))
      (commonUpperTranslationDomain shift) := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_commonUpperTranslationDomain shift)
  intro z hz
  exact ((contDiffAt_cauchyTransform_translate ν (shift.1 i) (hz i).ne').differentiableAt
    (by simp)).differentiableWithinAt

/-- **Residual freeness passes to the outer functions.**  If the translated Cauchy family has no
differential relation, neither has the family of its Cayley exponentials -- the bounded invertible
outer functions of the card. -/
theorem not_familyDifferentiallyAlgebraicOn_outerCauchyTranslates {m : ℕ}
    (ν : Measure ℝ) [IsFiniteMeasure ν] (shift : InjectiveShiftConfiguration (Fin m))
    (hfree : ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => cauchyTransform ν (z + shift.1 i)) (commonUpperTranslationDomain shift)) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => Complex.exp ((cauchyTransform ν (z + shift.1 i) - Complex.I)
        / (cauchyTransform ν (z + shift.1 i) + Complex.I)))
      (commonUpperTranslationDomain shift) := by
  obtain ⟨z₀, hz₀, -⟩ := commonUpperTranslationDomain_meets_upperTail shift 0
  refine not_familyDifferentiallyAlgebraicOn_cayleyOuter
    (isOpen_commonUpperTranslationDomain shift)
    (commonUpperTranslationDomain_isPreconnected shift) ⟨z₀, hz₀⟩
    (analyticOnNhd_cauchyTransform_translate ν shift) ?_ hfree
  intro i w hw
  exact add_I_ne_zero_of_im_nonneg (im_cauchyTransform_nonneg ν (hw i))

/-- **Residual outer freeness.**  For every infinite-support base measure and strictly positive
integrable density, one dense residual set of bounded exponential parameters makes every finite
family of distinct translates of the associated bounded invertible outer function differentially
algebraically independent. -/
theorem outerCauchy_fullTranslationFreeness_denseResidual
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t) :
    ∃ Ufree : Set (Lp ℝ ⊤ μ), Dense Ufree ∧ Ufree ∈ residual (Lp ℝ ⊤ μ) ∧
      ∀ u ∈ Ufree, ∀ (m : ℕ) (shift : InjectiveShiftConfiguration (Fin m)),
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z => Complex.exp
            ((cauchyTransform (expWeightedMeasure μ w u) (z + shift.1 i) - Complex.I)
              / (cauchyTransform (expWeightedMeasure μ w u) (z + shift.1 i) + Complex.I)))
          (commonUpperTranslationDomain shift) := by
  have hbase := herglotz_fullTranslationCauchyFamilyFreeness_denseResidual μ hμ w hw hwpos
  obtain ⟨hdense, hres, hfree⟩ := hbase
  refine ⟨_, hdense, hres, ?_⟩
  intro u hu m shift
  letI : IsFiniteMeasure (expWeightedMeasure μ w u) :=
    isFiniteMeasure_expWeightedMeasure μ w hw (fun t => (hwpos t).le) u
  exact not_familyDifferentiallyAlgebraicOn_outerCauchyTranslates _ shift (hfree u hu m shift)

end

end GaloisForLFunctions.HTGeometry
