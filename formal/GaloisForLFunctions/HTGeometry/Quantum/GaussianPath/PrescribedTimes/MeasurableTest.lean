import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GridOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.PrefixPrices
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.WindowEvent

/-! # Summable Gaussian probabilities for tested circuit excursions -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
noncomputable section

private theorem mass_le_geometric {k m e : ℕ} {z : ℝ}
    (hprice : m+1+k ≤ e) (h : (2:ℝ)^e*z ≤ (2:ℝ)^m*2) :
    z ≤ (1/2:ℝ)^k := by
  rw [one_div,inv_pow,← one_div,le_div_iff₀ (by positivity)]
  apply le_of_mul_le_mul_left _ (show (0:ℝ)<2^e by positivity)
  calc
    _ = ((2:ℝ)^e*z)*2^k := (mul_assoc _ _ _).symm
    _ ≤ (2:ℝ)^m*2*2^k := mul_le_mul_of_nonneg_right h (by positivity)
    _ = (2:ℝ)^(m+1+k) := by rw [pow_add,pow_succ]
    _ ≤ (2:ℝ)^e := pow_le_pow_right₀ (by norm_num) hprice
    _ = _ := (mul_one _).symm

/-- Summable failure of the dilation test for arbitrary measurable prefix
events. No independence of different prefix lengths is needed. -/
theorem gaussian_path_eventually_outside_measurable_test
    (E : (k : ℕ) → Set (PrefixIndex (k+1) → ℝ)) (hm : ∀ k, MeasurableSet (E k))
    (q : ℕ → ℕ) (hq : ∀ k, 0 < q k) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      x ∉ testedDilationEvent (rayGrid (q k)) ((2:ℝ)^(2^(k+3)/1024)) (E k) := by
  classical
  let B (k : ℕ) := testedDilationEvent (rayGrid (q k)) ((2:ℝ)^(2^(k+3)/1024)) (E k)
  let x (k : ℕ) (ω : PathPauliDisorder) := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let bad (k : ℕ) : Set PathPauliDisorder := if 64 ≤ k then x k ⁻¹' B k else ∅
  have hprob (k : ℕ) : pathPauliDisorderLaw (bad k) ≤ (1/2:ℝ≥0∞)^k := by
    by_cases hk : 64 ≤ k
    · let μ := Measure.pi (fun _ : PrefixIndex (k+1) => gaussianReal 0 1)
      have hE := hm k
      have hB : MeasurableSet (B k) := measurable_testedDilationEvent _ _ hE
      have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
      have he : pathPauliDisorderLaw (x k ⁻¹' B k) = μ (B k) := hmp.measure_preimage hB.nullMeasurableSet
      have hz : μ.real (B k) ≤ (1/2:ℝ)^k :=
        mass_le_geometric (prefix_dilation_price k hk)
          (gaussian_tested_dilation_mass (M := (2:ℝ)^(2^(k+3)/1024)) (hq k) (rayGrid (q k)) rayGrid_mem (by positivity) hE)
      rw [show bad k = x k ⁻¹' B k from if_pos hk,he,← ENNReal.ofReal_toReal (measure_ne_top μ (B k))]
      apply (ENNReal.ofReal_le_ofReal hz).trans_eq
      rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),one_div,ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
      norm_num
    · simp [bad,hk]
  have hgood : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω ∉ bad k := by
    apply ae_eventually_notMem
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hprob)
    simp only [one_div,ENNReal.tsum_geometric_two]
    norm_num
  filter_upwards [hgood] with ω hw
  filter_upwards [hw,eventually_ge_atTop 64] with k h hk
  simpa only [bad,if_pos hk,mem_preimage,x,B] using h

#print axioms gaussian_path_eventually_outside_measurable_test
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
