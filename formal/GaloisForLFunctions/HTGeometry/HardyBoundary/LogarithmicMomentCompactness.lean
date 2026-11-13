import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PhysicalAndFourierTailsGiveCompactness

/-!
# Compactness from physical and logarithmic Fourier moments

A bounded physical first moment controls the spatial cutoff error. A bounded
logarithmic Fourier moment controls the spectral cutoff error. Together they
give compact closure in L², without a common compact support.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open RHTower
namespace GaloisForLFunctions.HTGeometry

/-- Removing a measurable spatial set leaves exactly its complementary square mass. -/
theorem norm_sq_sub_indicatorCutoff_eq_tail (s : Set ℝ) (hs : MeasurableSet s) (f : SoninL2) :
    ‖f - indicatorCutoff s hs f‖ ^ 2 =
      ∫ x, sᶜ.indicator (fun x => ‖f x‖ ^ 2) x := by
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f (indicatorCutoff s hs f), indicatorCutoff_ae s hs f]
    with x hsub hcut
  rw [hsub, Pi.sub_apply, hcut]
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_notMem (show x ∉ sᶜ from fun h => h hx),
      sub_self, norm_zero, zero_pow two_ne_zero]
  · rw [indicator_of_notMem hx, indicator_of_mem (show x ∈ sᶜ from hx), sub_zero]

/-- The first moment bounds the square error of a central spatial cutoff. -/
theorem mul_norm_sq_sub_indicatorCutoff_le_firstMoment (f : SoninL2)
    (hi : Integrable (fun x : ℝ => |x| * ‖f x‖ ^ 2)) (a : ℝ) :
    a * ‖f - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f‖ ^ 2 ≤
      ∫ x, |x| * ‖f x‖ ^ 2 := by
  rw [norm_sq_sub_indicatorCutoff_eq_tail, ← integral_const_mul]
  have hplain : Integrable (fun x : ℝ => ‖f x‖ ^ 2) :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  apply integral_mono ((hplain.indicator (measurableSet_centralInterval a).compl).const_mul a) hi
  intro x
  dsimp only
  by_cases hx : x ∈ (centralInterval a)ᶜ
  · rw [indicator_of_mem hx]
    have habs : a ≤ |x| := by
      have hn : ¬ |x| ≤ a := fun h => hx (abs_le.mp h)
      exact (lt_of_not_ge hn).le
    exact mul_le_mul_of_nonneg_right habs (sq_nonneg ‖f x‖)
  · rw [indicator_of_notMem hx, mul_zero]
    exact mul_nonneg (abs_nonneg x) (sq_nonneg ‖f x‖)

/-- Logarithmic Fourier energy bounds the square error of an exponential spectral cutoff. -/
theorem mul_norm_sq_sub_fourierCutoff_le_logMoment (f : SoninL2)
    (hi : Integrable (suzukiHlogDensity f)) (A : ℝ) :
    A * ‖f - fourierCutoff (centralInterval (Real.exp A))
      (measurableSet_centralInterval (Real.exp A)) f‖ ^ 2 ≤ suzukiHlogMoment f := by
  rw [norm_sq_sub_fourierCutoff_central_eq_tailIntegral, ← integral_const_mul]
  have hplain : Integrable (fun ξ : ℝ => ‖fourierUnitary f ξ‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  apply integral_mono
    ((hplain.indicator (measurableSet_centralInterval (Real.exp A)).compl).const_mul A) hi
  intro ξ
  dsimp only
  by_cases hξ : ξ ∈ (centralInterval (Real.exp A))ᶜ
  · rw [indicator_of_mem hξ]
    exact mul_le_mul_of_nonneg_right (le_suzukiLogWeight_of_mem_exp_tail A ξ hξ)
      (sq_nonneg ‖fourierUnitary f ξ‖)
  · rw [indicator_of_notMem hξ, mul_zero]
    exact suzukiHlogDensity_nonneg f ξ

/-- Uniform bounds on mass and both moments give compact closure in L². -/
theorem isCompact_closure_of_firstMoment_and_logMoment (S : Set SoninL2) {B M L : ℝ}
    (hbound : ∀ f ∈ S, ‖f‖ ≤ B)
    (hfirst : ∀ f ∈ S, Integrable (fun x : ℝ => |x| * ‖f x‖ ^ 2) ∧
      (∫ x, |x| * ‖f x‖ ^ 2) ≤ M)
    (hlog : ∀ f ∈ S, Integrable (suzukiHlogDensity f) ∧ suzukiHlogMoment f ≤ L) :
    IsCompact (closure S) := by
  apply CriticalArithmeticCorrelationTheory.isCompact_closure_of_uniform_physical_and_fourier_tails
    S hbound
  · intro ε hε
    let a : ℝ := (max M 0 + 1) / ε ^ 2
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    have ha : 0 < a := div_pos (by linarith only [le_max_right M 0]) hε2
    have hscale : a * ε ^ 2 = max M 0 + 1 := div_mul_cancel₀ _ hε2.ne'
    refine ⟨a, ha, ?_⟩
    intro f hf
    have hb := (mul_norm_sq_sub_indicatorCutoff_le_firstMoment f (hfirst f hf).1 a).trans
      (hfirst f hf).2
    have hstrict : a * ‖f - indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) f‖ ^ 2 < a * ε ^ 2 := by
      rw [hscale]
      exact hb.trans_lt (by linarith only [le_max_left M 0])
    have hs : ‖f - indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) f‖ ^ 2 < ε ^ 2 := by
      by_contra hnot
      exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (le_of_not_gt hnot) ha.le)) hstrict
    nlinarith only [hs, hε, norm_nonneg (f - indicatorCutoff (centralInterval a)
      (measurableSet_centralInterval a) f)]
  · intro ε hε
    let A : ℝ := (max L 0 + 1) / ε ^ 2
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hA : 0 < A := div_pos (by linarith only [le_max_right L 0]) hε2
    have hscale : A * ε ^ 2 = max L 0 + 1 := div_mul_cancel₀ _ hε2.ne'
    refine ⟨Real.exp A, Real.exp_pos A, ?_⟩
    intro f hf
    have hb := (mul_norm_sq_sub_fourierCutoff_le_logMoment f (hlog f hf).1 A).trans (hlog f hf).2
    have hstrict : A * ‖f - fourierCutoff (centralInterval (Real.exp A))
        (measurableSet_centralInterval (Real.exp A)) f‖ ^ 2 < A * ε ^ 2 := by
      rw [hscale]
      exact hb.trans_lt (by linarith only [le_max_left L 0])
    have hs : ‖f - fourierCutoff (centralInterval (Real.exp A))
        (measurableSet_centralInterval (Real.exp A)) f‖ ^ 2 < ε ^ 2 := by
      by_contra hnot
      exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (le_of_not_gt hnot) hA.le)) hstrict
    nlinarith only [hs, hε, norm_nonneg (f - fourierCutoff (centralInterval (Real.exp A))
      (measurableSet_centralInterval (Real.exp A)) f)]

#print axioms isCompact_closure_of_firstMoment_and_logMoment
end GaloisForLFunctions.HTGeometry
