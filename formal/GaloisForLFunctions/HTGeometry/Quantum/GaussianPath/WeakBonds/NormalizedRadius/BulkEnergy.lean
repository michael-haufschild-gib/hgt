import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.BoxMass

/-! # A uniform lower bound on the energy of the uncut Gaussian coordinates -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NormalizedRadius
noncomputable section

def bulkMass : ℝ := (gaussianReal 0 1).real (Icc 1 2)

theorem bulkMass_pos : 0 < bulkMass :=
  ENNReal.toReal_pos (gaussianReal_Icc_pos (by norm_num : (1:ℝ)<2)).ne' (measure_ne_top _ _)

/-- A positive fraction of samples carry energy proportional to the number
of coordinates. Count the entries in [1,2] and use their common marginal. -/
theorem bulk_energy_mass (ι : Type*) [Fintype ι] [Nonempty ι] :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    let m : ℝ := Fintype.card ι
    bulkMass/2 ≤ μ.real {x | m*(bulkMass/2) ≤ ∑ i, (x i)^2} := by
  classical
  intro μ m
  let E := {x : ι → ℝ | m*(bulkMass/2) ≤ ∑ i, (x i)^2}
  let S (i : ι) := (fun x : ι → ℝ => x i) ⁻¹' Icc 1 2
  let f (i : ι) := (S i).indicator (1 : (ι → ℝ) → ℝ)
  let g := E.indicator (1 : (ι → ℝ) → ℝ)
  have hS (i : ι) : MeasurableSet (S i) := (measurable_pi_apply i) measurableSet_Icc
  have hE : MeasurableSet E := measurableSet_le measurable_const (by fun_prop)
  have hf (i : ι) : Integrable (f i) μ := (integrable_const _).indicator (hS i)
  have hg : Integrable g μ := (integrable_const _).indicator hE
  have hp (i : ι) : (∫ x, f i x ∂μ)=bulkMass := by
    rw [show (∫ x, f i x ∂μ)=μ.real (S i) from integral_indicator_one (hS i)]
    exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).measureReal_preimage
      measurableSet_Icc.nullMeasurableSet
  have hm : 0 < m := Nat.cast_pos.mpr Fintype.card_pos
  have hcount (x : ι → ℝ) : ∑ i, f i x ≤ m*(bulkMass/2)+m*g x := by
    by_cases hx : x∈E
    · rw [show g x=1 from indicator_of_mem hx _,mul_one]
      have hi (i : ι) : f i x≤1 := by
        by_cases h : x ∈ S i
        · exact (show f i x = 1 from indicator_of_mem h _).le
        · rw [show f i x = 0 from indicator_of_notMem h _]
          exact zero_le_one
      have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hi i)
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
      exact h.trans (le_add_of_nonneg_left (mul_nonneg hm.le (half_pos bulkMass_pos).le))
    · rw [show g x=0 from indicator_of_notMem hx _,mul_zero,add_zero]
      apply le_trans _ (le_of_not_ge hx)
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : x∈S i
      · rw [show f i x=1 from indicator_of_mem hi _]
        have h : 1≤x i := hi.1
        nlinarith only [sq_nonneg (x i-1),h]
      · rw [show f i x=0 from indicator_of_notMem hi _]
        exact sq_nonneg _
  have h := integral_mono (integrable_finsetSum _ (fun i _ => hf i))
    ((integrable_const _).add (hg.const_mul m)) hcount
  rw [integral_finsetSum _ (fun i _ => hf i)] at h
  change (∑ i, ∫ x, f i x ∂μ) ≤ ∫ x, m*(bulkMass/2)+m*g x ∂μ at h
  rw [integral_add (integrable_const (m*(bulkMass/2))) (hg.const_mul m),
    integral_const_mul m g,show (∫ x, g x ∂μ)=μ.real E from integral_indicator_one hE] at h
  simp only [hp,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,integral_const,probReal_univ,one_smul] at h
  change m*bulkMass ≤ m*(bulkMass/2)+m*μ.real E at h
  apply (mul_le_mul_iff_right₀ hm).mp
  linarith only [h]

#print axioms bulk_energy_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NormalizedRadius
