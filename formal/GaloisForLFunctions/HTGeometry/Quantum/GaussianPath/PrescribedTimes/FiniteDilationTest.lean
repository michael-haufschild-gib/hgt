import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # A finite dilation test for a Gaussian event -/
open Set MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
noncomputable section
variable {ι : Type*} {q : ℕ}
private abbrev X (ι : Type*) := ι → ℝ

/-- Number of sampled dilations that belong to the event. -/
def dilationCount (b : Fin q → ℝ) (E : Set (X ι)) (x : X ι) : ℝ :=
  ∑ j, ((fun z : X ι => b j • z) ⁻¹' E).indicator (fun _ => (1:ℝ)) x

private theorem measurable_count (b : Fin q → ℝ) {E : Set (X ι)} (hE : MeasurableSet E) :
    Measurable (dilationCount b E) :=
  Finset.measurable_sum _ fun j _ => measurable_const.indicator (hE.preimage (measurable_id.const_smul (b j)))

/-- Certify a hit by testing its grid from every possible sampled anchor. -/
def testedDilationEvent (b : Fin q → ℝ) (M : ℝ) (E : Set (X ι)) : Set (X ι) :=
  E ∩ ⋂ i, {x | M*dilationCount (fun j => b j / b i) E x ≤ 2*(q:ℝ)}

theorem measurable_testedDilationEvent (b : Fin q → ℝ) (M : ℝ) {E : Set (X ι)} (hE : MeasurableSet E) :
    MeasurableSet (testedDilationEvent b M E) :=
  hE.inter (MeasurableSet.iInter fun i =>
    measurableSet_le (measurable_const.mul (measurable_count (fun j => b j / b i) hE)) measurable_const)

private theorem count_le_of_test (b : Fin q → ℝ) (hb : ∀ i, b i ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) (E : Set (X ι)) (x : X ι) :
    M*dilationCount b (testedDilationEvent b M E) x ≤ 2*(q:ℝ) := by
  classical
  let B := testedDilationEvent b M E
  by_cases h : ∃ i, b i • x ∈ B
  · obtain ⟨i,hi⟩ := h
    have hrow := mem_iInter.mp hi.2 i
    apply le_trans (mul_le_mul_of_nonneg_left _ hM) hrow
    apply Finset.sum_le_sum
    intro j _
    have he : (b j/b i) • b i • x = b j • x := by rw [smul_smul,div_mul_cancel₀ _ (hb _)]
    simp only [indicator_apply,mem_preimage,he]
    change (if b j • x ∈ B then (1:ℝ) else 0) ≤ (if b j • x ∈ E then 1 else 0)
    by_cases hj : b j • x ∈ B
    · rw [if_pos hj,if_pos hj.1]
    · rw [if_neg hj]
      split <;> norm_num
  · have hz : dilationCount b B x = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (show x ∉ (fun y : X ι => b i • y) ⁻¹' B from fun hx => h ⟨i,hx⟩) _
    change M*dilationCount b B x ≤ _
    rw [hz,mul_zero]
    positivity

/-- Gaussian dilation domination turns the deterministic count on each ray
into a probability bound. Only the dimension enters the factor 2^m. -/
theorem gaussian_tested_dilation_mass [Fintype ι] (hq : 0 < q) (b : Fin q → ℝ) (hb : ∀ i, b i ∈ Icc 1 2)
    {M : ℝ} (hM : 0 ≤ M) {E : Set (X ι)} (hE : MeasurableSet E) :
    let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
    M*μ.real (testedDilationEvent b M E) ≤ (2:ℝ)^(Fintype.card ι)*2 := by
  classical
  intro μ
  let B := testedDilationEvent b M E
  let m := Fintype.card ι
  let S (i : Fin q) := (fun x : X ι => b i • x) ⁻¹' B
  have hB : MeasurableSet B := measurable_testedDilationEvent b M hE
  have hS (i : Fin q) : MeasurableSet (S i) := hB.preimage (measurable_id.const_smul (b i))
  let f (i : Fin q) := (S i).indicator (fun _ => (1:ℝ))
  have hf (i : Fin q) : Integrable (f i) μ := (integrable_const _).indicator (hS i)
  have hmass (i : Fin q) : μ.real B ≤ (2:ℝ)^m*μ.real (S i) :=
    (gaussian_dilation_comparison (hb i).1 B hB).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans (hb i).1) (hb i).2 _) ENNReal.toReal_nonneg)
  have hsum : (q:ℝ)*μ.real B ≤ (2:ℝ)^m*(∑ i, μ.real (S i)) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hmass i)
  have hi : M*(∑ i, μ.real (S i)) ≤ 2*(q:ℝ) := by
    have hconv (i) : ∫ x, f i x ∂μ = μ.real (S i) := integral_indicator_one (hS i)
    rw [show (∑ i, μ.real (S i)) = ∫ x, ∑ i, f i x ∂μ by rw [integral_finsetSum Finset.univ (fun i _ => hf i)]; simp only [hconv]]
    rw [← integral_const_mul]
    apply le_trans (integral_mono ((integrable_finsetSum _ (fun i _ => hf i)).const_mul M) (integrable_const (2*(q:ℝ)))
      (fun x => count_le_of_test b (fun i => (zero_lt_one.trans_le (hb i).1).ne') hM E x))
    simp
  apply le_of_mul_le_mul_left _ (show (0:ℝ)<q by exact_mod_cast hq)
  calc
    _ = M*((q:ℝ)*μ.real B) := by ring
    _ ≤ M*((2:ℝ)^m*(∑ i, μ.real (S i))) := mul_le_mul_of_nonneg_left hsum hM
    _ = (2:ℝ)^m*(M*(∑ i, μ.real (S i))) := by ring
    _ ≤ (2:ℝ)^m*(2*(q:ℝ)) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

#print axioms gaussian_tested_dilation_mass
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
