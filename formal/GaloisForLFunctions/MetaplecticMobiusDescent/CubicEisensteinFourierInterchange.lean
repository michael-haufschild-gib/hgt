/-
Cubic Eisenstein Fourier interchange adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicTraceFourierPeriodization
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicEisensteinSeries

/-!
# Fourier integration of the actual Eisenstein series

A bounded cusp fundamental domain gives a uniform integral-row majorant.
Its summability for `Re s>2` permits exchanging the actual Eisenstein
sum with horizontal Fourier integration by dominated convergence.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped BigOperators Classical ENNReal MatrixGroups Matrix
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma continuous_inverse_upper_operator (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => rowOperator (upperSection z v hv)⁻¹) := by
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_pi
  intro i
  simp only [rowOperator_apply,upperSection,
    Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  fin_cases i <;> simp only [] <;> fun_prop

lemma continuous_upper_rowBound (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => rowBound (upperSection z v hv)) :=
  continuous_const.mul (continuous_const.add (continuous_inverse_upper_operator v hv).norm)

lemma exists_upper_rowBound (v : ℝ) (hv : 0 < v) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ periodDomain, rowBound (upperSection z v hv) ≤ C := by
  let R : ℝ := ∑ i : Fin 2, ‖periodBasis i‖
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) R).bddAbove_image
    (continuous_upper_rowBound v hv).continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro z hz
  apply (hC ?_).trans (le_max_right _ _)
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz,rfl⟩

lemma continuous_upper_summand (v : ℝ) (hv : 0 < v) (s : ℂ) (x : CuspCosets) :
    Continuous (fun z : ℂ => summand (upperSection z v hv) s x) := by
  simp_rw [summand_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    apply continuous_const.div
    · unfold heightDenominator
      fun_prop
    · intro z
      exact (heightDenominator_pos z v hv _ (embeddedRow_ne_zero x)).ne'
  · exact continuous_const
  · intro z
    apply Complex.ofReal_mem_slitPlane.mpr
    exact div_pos hv (heightDenominator_pos z v hv _ (embeddedRow_ne_zero x))

lemma upper_summable_majorant (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    ∃ M : CuspCosets → ℝ, Summable M ∧ (∀ x,0 ≤ M x) ∧
      ∀ z ∈ periodDomain, ∀ x, ‖summand (upperSection z v hv) s x‖ ≤ M x := by
  obtain ⟨C,hC,hbound⟩ := exists_upper_rowBound v hv
  refine ⟨fun x => C^(2*s.re)*‖rowCoordinates (cosetRow x)‖^(-(2*s.re)),?_,?_,?_⟩
  · have hsumm := summable_integer_four_rpow (2*s.re) (by linarith)
    have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
      rowCoordinates_injective.comp cosetRow_injective
    exact (hsumm.comp_injective hinj).mul_left _
  · intro x
    positivity
  · intro z hz x
    apply (norm_summand_bound (upperSection z v hv) s (by linarith) x).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (rowBound_pos _).le (hbound z hz) (by linarith)) (by positivity)

lemma periodDomain_finiteMeasure : IsFiniteMeasure (volume.restrict periodDomain) := by
  constructor
  rw [Measure.restrict_apply_univ,periodDomain_volume]
  exact ENNReal.ofReal_lt_top

theorem hasSum_integral_upperEisenstein (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    HasSum (fun x : CuspCosets => ∫ z in periodDomain,
      summand (upperSection z v hv) s x*tracePhase (-freq*z))
      (∫ z in periodDomain,upperEisenstein z v hv s*tracePhase (-freq*z)) := by
  let : Countable CuspCosets :=
    (rowCoordinates_injective.comp cosetRow_injective).countable
  let := periodDomain_finiteMeasure
  obtain ⟨M,hM,hMnonneg,hbound⟩ := upper_summable_majorant v hv s hs
  have hchar : Continuous (fun z : ℂ => tracePhase (-freq*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  have hsum := hasSum_integral_of_dominated_convergence
    («μ» := volume.restrict periodDomain)
    (fun (x : CuspCosets) (_ : ℂ) => M x)
    (fun x => ((continuous_upper_summand v hv s x).mul hchar).aestronglyMeasurable.restrict)
    (fun x => (ae_restrict_mem periodDomain_measurable).mono fun z hz => by
      simpa only [Pi.mul_apply,norm_mul,tracePhase_norm,mul_one] using hbound z hz x)
    (Eventually.of_forall fun _ => hM)
    (integrable_const (∑' x,M x))
    (Eventually.of_forall fun z => (summable_summand (upperSection z v hv) s hs).hasSum.mul_right
      (tracePhase (-freq*z)))
  exact hsum

theorem integral_upperEisenstein_eq_sum (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    (∫ z in periodDomain,upperEisenstein z v hv s*tracePhase (-freq*z))=
      ∑' x : CuspCosets,∫ z in periodDomain,
        summand (upperSection z v hv) s x*tracePhase (-freq*z) :=
  (hasSum_integral_upperEisenstein v hv s freq hs).tsum_eq.symm

#print axioms upper_summable_majorant
#print axioms hasSum_integral_upperEisenstein
#print axioms integral_upperEisenstein_eq_sum
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
