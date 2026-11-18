import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellVariancePayment
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The singular boundary of Gaussian approximation for complete cells

The density assumption in Darijani–Soufian–Beyerer, arXiv:2611.16022,
Proposition 2.18, matters for complete logarithmic cells. Their profiles
have finite range. Under any probability sampling of position, both
directions of relative entropy against a nondegenerate Gaussian are infinite.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

private def simpleCell (a : ℕ) : SimpleFunc ℝ ℝ :=
  (SimpleFunc.const ℝ 1).restrict (Ico (Real.log a) (Real.log ((a+1:ℕ):ℝ)))

private theorem simpleCell_apply (a : ℕ) (x : ℝ) : simpleCell a x = rawCell a x := by
  simp only [simpleCell,SimpleFunc.coe_restrict _ measurableSet_Ico,SimpleFunc.coe_const,rawCell] <;> rfl

private def pairSimple (q d : ℕ → ℝ) (X : ℕ) : SimpleFunc ℝ ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    (q a) • (simpleCell (2*a) + simpleCell (2*a+1)) +
    (d a) • (haarLeftCoeff a • simpleCell (2*a) - haarRightCoeff a • simpleCell (2*a+1))

private theorem eval_simple_sum {ι : Type*} (s : Finset ι) (f : ι → SimpleFunc ℝ ℝ) (x : ℝ) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, SimpleFunc.add_apply, ih]

private theorem pairSimple_eq (q d : ℕ → ℝ) (X : ℕ) :
    ⇑(pairSimple q d X) = completePairProfile q d X := by
  funext x
  simp only [pairSimple,eval_simple_sum,SimpleFunc.add_apply,SimpleFunc.smul_apply,
    SimpleFunc.sub_apply,smul_eq_mul,simpleCell_apply,Finset.sum_add_distrib,
    completePairProfile,averageSectionProfile,coarseProfile,haarSectionProfile,haarProfile]

/-- The whole profile, including the exterior zero, has finite range. -/
theorem finite_range_completePairProfile (q d : ℕ → ℝ) (X : ℕ) :
    (range (completePairProfile q d X)).Finite := by
  rw [← pairSimple_eq]
  exact (pairSimple q d X).finite_range

/-- Every probability sampling gives full mass to a finite Gaussian-null
set. The target Gaussian may have any location and positive variance. -/
theorem cell_gaussian_separating_set (q d : ℕ → ℝ) (X : ℕ) (μ : ProbabilityMeasure ℝ) (m l : ℝ) :
    ∃ S : Set ℝ, S.Finite ∧ ((μ : Measure ℝ).map (completePairProfile q d X)) S = 1 ∧
      gaussianReal m (Real.toNNReal (Real.exp l)) S = 0 := by
  let F := pairSimple q d X
  refine ⟨range F,F.finite_range,?_,?_⟩
  · rw [← pairSimple_eq,Measure.map_apply F.measurable F.finite_range.measurableSet,
      Set.preimage_range,measure_univ]
  · have hσ : Real.toNNReal (Real.exp l) ≠ 0 := (Real.toNNReal_pos.mpr (Real.exp_pos l)).ne'
    exact gaussianReal_absolutelyContinuous m hσ (F.finite_range.measure_zero (μ := volume))

/-- Finite Gaussian log-score fitting of the step values coexists with
infinite measure-theoretic KL divergence in both directions. -/
theorem cell_gaussian_kl_infinite (q d : ℕ → ℝ) (X : ℕ) (μ : ProbabilityMeasure ℝ) (m l : ℝ) :
    let P := (μ : Measure ℝ).map (completePairProfile q d X)
    let Q := gaussianReal m (Real.toNNReal (Real.exp l))
    klDiv P Q = ⊤ ∧ klDiv Q P = ⊤ := by
  intro P Q
  obtain ⟨S,hfin,hP,hQ⟩ := cell_gaussian_separating_set q d X μ m l
  change P S = 1 at hP
  change Q S = 0 at hQ
  have hF : Measurable (completePairProfile q d X) := pairSimple_eq q d X ▸ (pairSimple q d X).measurable
  haveI : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map hF.aemeasurable
  constructor
  · apply klDiv_of_not_ac
    intro h
    exact one_ne_zero (hP.symm.trans (h hQ))
  · have hPc : P Sᶜ = 0 := by rw [prob_compl_eq_one_sub hfin.measurableSet,hP,tsub_self]
    have hQc : Q Sᶜ = 1 := by rw [prob_compl_eq_one_sub hfin.measurableSet,hQ,tsub_zero]
    apply klDiv_of_not_ac
    intro h
    exact one_ne_zero (hQc.symm.trans (h hPc))

#print axioms finite_range_completePairProfile
#print axioms cell_gaussian_separating_set
#print axioms cell_gaussian_kl_infinite
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
