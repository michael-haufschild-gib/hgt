import GaloisForLFunctions.HTGeometry.FisherOneCornerCodiagonalContraction

/-!
# Finite one-corner common Hardy reporter

The pointwise joined-codiagonal contraction is assembled into one actual
`L²((0,∞), du)` source.  Its Laplace transform is computed simultaneously at
every right-half-plane node as the finite sum of the exact oriented semigroup
divided differences.  Thus the finite common-test problem has no hidden
nodewise choice; the remaining Route-R problem is the infinite arithmetic
Gamma/co-Poisson reporter mate.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι]

private theorem integrableOn_Ioi_indicator_Ioc_const_complex
    {a b : ℝ} {c : ℂ} :
    IntegrableOn
      (fun u : ℝ => if a < u ∧ u ≤ b then c else 0) (Ioi 0) := by
  rw [show (fun u : ℝ => if a < u ∧ u ≤ b then c else 0) =
      (Ioc a b).indicator (fun _ => c) by
    funext u
    simp [indicator, mem_Ioc]]
  exact ((integrableOn_const (by simp [Real.volume_Ioc]) :
    IntegrableOn (fun _ : ℝ => c) (Ioc a b))).integrable_indicator
      measurableSet_Ioc |>.integrableOn

private theorem integrableOn_Ioi_indicator_Ioc_const_real
    {a b c : ℝ} :
    IntegrableOn
      (fun u : ℝ => if a < u ∧ u ≤ b then c else 0) (Ioi 0) := by
  rw [show (fun u : ℝ => if a < u ∧ u ≤ b then c else 0) =
      (Ioc a b).indicator (fun _ => c) by
    funext u
    simp [indicator, mem_Ioc]]
  exact ((integrableOn_const (by simp [Real.volume_Ioc]) :
    IntegrableOn (fun _ : ℝ => c) (Ioc a b))).integrable_indicator
      measurableSet_Ioc |>.integrableOn

private theorem measurable_indicator_Ioc_const_complex
    {a b : ℝ} {c : ℂ} :
    Measurable (fun u : ℝ => if a < u ∧ u ≤ b then c else 0) := by
  rw [show (fun u : ℝ => if a < u ∧ u ≤ b then c else 0) =
      (Ioc a b).indicator (fun _ => c) by
    funext u
    simp [indicator, mem_Ioc]]
  exact measurable_const.indicator measurableSet_Ioc

private theorem measurable_finsetSum_complex
    {κ : Type*} (s : Finset κ) (F : κ → ℝ → ℂ)
    (hF : ∀ k ∈ s, Measurable (F k)) :
    Measurable (fun u => ∑ k ∈ s, F k u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hFa : Measurable (F a) := hF a (by simp)
      have hFs : Measurable (fun u => ∑ k ∈ s, F k u) :=
        ih (fun k hk => hF k (by simp [hk]))
      simp only [Finset.sum_insert ha]
      change Measurable (F a + fun u => ∑ k ∈ s, F k u)
      exact hFa.add hFs

/-- The finite one-corner Fisher density is integrable on the complete
positive cutoff ray. -/
theorem integrableOn_finiteFisherOneCornerCoareaDensity
    (p h : ι → ℝ) (m : ℝ) :
    IntegrableOn (finiteFisherOneCornerCoareaDensity p h m) (Ioi 0) := by
  unfold finiteFisherOneCornerCoareaDensity
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact integrableOn_Ioi_indicator_Ioc_const_real

/-- The finite joined codiagonal is a measurable scalar cutoff field. -/
theorem measurable_finiteFisherOneCornerJoinedCodiagonal
    (p h : ι → ℝ) (m : ℝ) (d : ι → ℂ) :
    Measurable (finiteFisherOneCornerJoinedCodiagonal p h m d) := by
  unfold finiteFisherOneCornerJoinedCodiagonal
  apply measurable_finsetSum_complex
  intro i _
  apply measurable_finsetSum_complex
  intro j _
  exact measurable_indicator_Ioc_const_complex

private theorem finiteFisherOneCornerCoareaDensity_nonneg
    (p h : ι → ℝ) (m u : ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ finiteFisherOneCornerCoareaDensity p h m u := by
  unfold finiteFisherOneCornerCoareaDensity finiteFisherPairAmplitudeSq
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (hp i) (hp j)) (sq_nonneg _))
  · norm_num

/-- The finite joined codiagonal is one square-integrable half-line source,
not a family chosen separately at each Hardy node. -/
theorem finiteFisherOneCornerJoinedCodiagonal_memLp
    (p h : ι → ℝ) (m : ℝ) (d : ι → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hpone : ∑ i, p i = 1)
    (hd : ∀ i, ‖d i‖ ≤ 1) :
    MemLp (finiteFisherOneCornerJoinedCodiagonal p h m d) 2
      halfLineLaplaceMeasure := by
  let f := finiteFisherOneCornerJoinedCodiagonal p h m d
  have hfmeas : AEStronglyMeasurable f halfLineLaplaceMeasure := by
    exact (measurable_finiteFisherOneCornerJoinedCodiagonal p h m d)
      |>.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hfmeas).2
  have hdensity : Integrable
      (finiteFisherOneCornerCoareaDensity p h m)
      halfLineLaplaceMeasure := by
    change IntegrableOn
      (finiteFisherOneCornerCoareaDensity p h m) (Ioi 0)
    exact integrableOn_finiteFisherOneCornerCoareaDensity p h m
  refine Integrable.mono'
    (hdensity.const_mul (1 / 2 : ℝ)) (hfmeas.norm.pow 2) ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_sq_finiteFisherOneCornerJoinedCodiagonal_le_half_density
    p h m d u hp hpone hd

/-- The literal finite common-Hardy reporter. -/
def finiteFisherOneCornerCommonHardyReporter
    (p h : ι → ℝ) (m : ℝ) (d : ι → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hpone : ∑ i, p i = 1)
    (hd : ∀ i, ‖d i‖ ≤ 1) :
    Lp ℂ 2 halfLineLaplaceMeasure :=
  (finiteFisherOneCornerJoinedCodiagonal_memLp
    p h m d hp hpone hd).toLp
      (finiteFisherOneCornerJoinedCodiagonal p h m d)

private theorem norm_sq_toLp_eq_integral_norm_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  have key := inner_self_eq_norm_sq (𝕜 := ℂ) (hf.toLp f)
  rw [MeasureTheory.L2.inner_def] at key
  have hint :
      (∫ a, inner ℂ ((hf.toLp f : α → ℂ) a)
          ((hf.toLp f : α → ℂ) a) ∂μ) =
        ((∫ a, ‖f a‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with a ha
    rw [ha, RCLike.inner_apply, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [hint] at key
  simpa using key.symm

/-- Global finite common-reporter energy law. -/
theorem norm_sq_finiteFisherOneCornerCommonHardyReporter_le_half_holonomy
    (p h : ι → ℝ) (m : ℝ) (d : ι → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hpone : ∑ i, p i = 1)
    (hh : ∀ i, 0 ≤ h i) (hd : ∀ i, ‖d i‖ ≤ 1) :
    ‖finiteFisherOneCornerCommonHardyReporter
        p h m d hp hpone hd‖ ^ 2 ≤
      (1 / 2 : ℝ) * finiteFisherSignedHolonomyEnergy p h m := by
  let f := finiteFisherOneCornerJoinedCodiagonal p h m d
  let hf := finiteFisherOneCornerJoinedCodiagonal_memLp
    p h m d hp hpone hd
  rw [finiteFisherOneCornerCommonHardyReporter,
    norm_sq_toLp_eq_integral_norm_sq hf]
  have hfsq : Integrable (fun u => ‖f u‖ ^ 2)
      halfLineLaplaceMeasure :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hdensity : Integrable
      (finiteFisherOneCornerCoareaDensity p h m)
      halfLineLaplaceMeasure := by
    change IntegrableOn
      (finiteFisherOneCornerCoareaDensity p h m) (Ioi 0)
    exact integrableOn_finiteFisherOneCornerCoareaDensity p h m
  calc
    (∫ u, ‖f u‖ ^ 2 ∂halfLineLaplaceMeasure) ≤
        ∫ u, (1 / 2 : ℝ) *
          finiteFisherOneCornerCoareaDensity p h m u
          ∂halfLineLaplaceMeasure := by
      apply integral_mono_ae hfsq (hdensity.const_mul (1 / 2 : ℝ))
      filter_upwards with u
      exact norm_sq_finiteFisherOneCornerJoinedCodiagonal_le_half_density
        p h m d u hp hpone hd
    _ = (1 / 2 : ℝ) *
        (∫ u in Ioi 0,
          finiteFisherOneCornerCoareaDensity p h m u) := by
      rw [halfLineLaplaceMeasure, integral_const_mul]
    _ = (1 / 2 : ℝ) * finiteFisherSignedHolonomyEnergy p h m := by
      rw [integral_finiteFisherOneCornerCoareaDensity hh]

private theorem integrable_halfLine_exp_mul_indicator
    (a b : ℝ) (k w : ℂ) :
    Integrable
      (fun u : ℝ => Complex.exp (-w * (u : ℂ)) *
        (if a < u ∧ u ≤ b then k else 0))
      halfLineLaplaceMeasure := by
  rw [show (fun u : ℝ => Complex.exp (-w * (u : ℂ)) *
      (if a < u ∧ u ≤ b then k else 0)) =
      (Ioc a b).indicator
        (fun u : ℝ => Complex.exp (-w * (u : ℂ)) * k) by
    funext u
    simp [indicator, mem_Ioc]]
  have hcont : Continuous
      (fun u : ℝ => Complex.exp (-w * (u : ℂ)) * k) := by
    fun_prop
  have hint : IntegrableOn
      (fun u : ℝ => Complex.exp (-w * (u : ℂ)) * k) (Ioc a b) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  exact (hint.integrable_indicator measurableSet_Ioc).mono_measure
    Measure.restrict_le_self

private theorem integral_halfLine_exp_mul_indicator_eq_oriented
    {a b : ℝ} (ha : 0 ≤ a) (k w : ℂ) :
    (∫ u : ℝ, Complex.exp (-w * (u : ℂ)) *
        (if a < u ∧ u ≤ b then k else 0)
        ∂halfLineLaplaceMeasure) =
      orientedCutoffLaplaceCoefficient a b k w := by
  by_cases hab : a ≤ b
  · rw [orientedCutoffLaplaceCoefficient, if_pos hab,
      halfLineLaplaceMeasure]
    rw [show (fun u : ℝ => Complex.exp (-w * (u : ℂ)) *
        (if a < u ∧ u ≤ b then k else 0)) =
        (Ioc a b).indicator
          (fun u : ℝ => Complex.exp (-w * (u : ℂ)) * k) by
      funext u
      simp [indicator, mem_Ioc]]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hinter : Ioi 0 ∩ Ioc a b = Ioc a b := by
      ext u
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · exact fun hu => hu.2
      · exact fun hu => ⟨ha.trans_lt hu.1, hu⟩
    rw [hinter, intervalIntegral.integral_of_le hab]
  · rw [orientedCutoffLaplaceCoefficient, if_neg hab]
    have hnone : ∀ u : ℝ, ¬ (a < u ∧ u ≤ b) := by
      intro u hu
      exact hab (hu.1.le.trans hu.2)
    simp [hnone]

/-- The one common reporter has, at every right-half-plane node, the exact
finite hard-cut/soft-damping codiagonal as its Laplace column. -/
theorem halfLineLaplaceTransform_finiteFisherOneCornerCommonHardyReporter_eq
    (p h : ι → ℝ) (m : ℝ) (d : ι → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hpone : ∑ i, p i = 1)
    (hh : ∀ i, 0 ≤ h i) (hd : ∀ i, ‖d i‖ ≤ 1)
    (w : ℂ) (hw : 0 < w.re) :
    halfLineLaplaceTransform
        (finiteFisherOneCornerCommonHardyReporter
          p h m d hp hpone hd) w hw =
      ∑ i, ∑ j,
        semigroupDividedDifferenceCoefficient (h j) (h i)
          (((p i * p j * (h i + h j - 2 * m) : ℝ) : ℂ) *
            (d i + d j)) w := by
  rw [halfLineLaplaceTransform_eq_integral]
  let f := finiteFisherOneCornerJoinedCodiagonal p h m d
  let hf := finiteFisherOneCornerJoinedCodiagonal_memLp
    p h m d hp hpone hd
  have hcoe := hf.coeFn_toLp
  rw [integral_congr_ae (by
    filter_upwards [hcoe] with u hu
    rw [finiteFisherOneCornerCommonHardyReporter, hu])]
  unfold finiteFisherOneCornerJoinedCodiagonal
  rw [show (fun a : ℝ => Complex.exp (-w * (a : ℂ)) *
      ∑ i, ∑ j,
        if h j < a ∧ a ≤ h i then
          (((p i * p j * (h i + h j - 2 * m) : ℝ) : ℂ) *
            (d i + d j))
        else 0) =
      fun a : ℝ => ∑ i, ∑ j,
        Complex.exp (-w * (a : ℂ)) *
          (if h j < a ∧ a ≤ h i then
            (((p i * p j * (h i + h j - 2 * m) : ℝ) : ℂ) *
              (d i + d j))
          else 0) by
    funext a
    simp only [Finset.mul_sum]]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_halfLine_exp_mul_indicator_eq_oriented
        (hh j)]
      apply orientedCutoffLaplaceCoefficient_eq_dividedDifference
      intro hw0
      subst w
      simp at hw
    · intro j _
      exact integrable_halfLine_exp_mul_indicator
        (h j) (h i)
          (((p i * p j * (h i + h j - 2 * m) : ℝ) : ℂ) *
            (d i + d j)) w
  · intro i _
    exact integrable_finsetSum Finset.univ (fun j _ =>
      integrable_halfLine_exp_mul_indicator
        (h j) (h i)
          (((p i * p j * (h i + h j - 2 * m) : ℝ) : ℂ) *
            (d i + d j)) w)

end GaloisForLFunctions.HTGeometry
