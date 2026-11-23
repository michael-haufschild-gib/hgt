import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.SmallTimeLaw.PowerIdentity

/-! # Positive Gaussian mass at every positive first-passage deadline -/
open MeasureTheory ProbabilityTheory Filter Set Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Positive dilations of every strictly positive deadline cover the
coefficient space. Each dilation preserves Gaussian null sets. -/
theorem deadline_pos (F : (ι → ℝ) → ℝ) (hf : Measurable F)
    (hom : ∀ a > (0:ℝ), ∀ x, a*F (a • x)=F x) {t : ℝ} (ht : 0<t) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    0 < μ {x | F x ≤ t} := by
  intro μ
  let E := {x | F x ≤ t}
  have hm : MeasurableSet E := measurableSet_le hf measurable_const
  apply pos_iff_ne_zero.mpr
  intro he
  let a (n : ℕ) : ℝ := (n:ℝ)+1
  have ha n : 0 < a n := by dsimp only [a]; positivity
  let A (n : ℕ) := (fun x : ι → ℝ => a n • x) ⁻¹' E
  have hzero (n) : μ (A n)=0 := by
    have hl := gaussian_inverse_scale_law (ι:=ι) (inv_pos.mpr (ha n))
    simp only [inv_inv] at hl
    change μ ((fun x : ι → ℝ => a n • x) ⁻¹' E)=0
    rw [←Measure.map_apply (f:=fun x : ι → ℝ => a n • x) (by fun_prop) hm,hl]
    exact withDensity_absolutelyContinuous _ _ he
  have hU : (⋃ n, A n)=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n,hn⟩ := exists_nat_gt (F x/t)
    apply mem_iUnion.mpr
    refine ⟨n,(mul_le_mul_iff_right₀ (ha n)).mp ?_⟩
    rw [hom _ (ha n)]
    exact ((div_lt_iff₀ ht).mp hn).le.trans (mul_le_mul_of_nonneg_right
      (by dsimp only [a]; linarith : (n:ℝ) ≤ a n) ht.le)
  have hh := measure_iUnion_null hzero
  rw [hU,measure_univ] at hh
  exact one_ne_zero hh

/-- The leading exponential probability coefficient is positive. Only
the threshold event needs positive mass; the weight can vanish elsewhere. -/
theorem passage_weight_positive (F : (ι → ℝ) → ℝ) (hf : Measurable F)
    (hom : ∀ a > (0:ℝ), ∀ x, a*F (a • x)=F x) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    0 < essSup (unitWeight F) μ := by
  intro μ
  let E := {x | F x ≤ 1}
  have hmass : 0 < μ E := deadline_pos F hf hom zero_lt_one
  have hbound (x) : unitWeight F x ≤ 1 := by
    by_cases h : x∈E
    · rw [unitWeight,indicator_of_mem h]
      exact exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) two_pos.le)
    · rw [unitWeight,indicator_of_notMem h]; exact zero_le_one
  apply lt_of_not_ge
  intro hh
  have hn : ∀ᵐ x ∂μ, x∉E := by
    filter_upwards [ae_le_essSup_of_le_one μ hbound] with x hx
    intro he
    rw [unitWeight,indicator_of_mem he] at hx
    exact (exp_pos _).not_ge (hx.trans hh)
  exact hmass.ne' (by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hn)

#print axioms deadline_pos
#print axioms passage_weight_positive
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
