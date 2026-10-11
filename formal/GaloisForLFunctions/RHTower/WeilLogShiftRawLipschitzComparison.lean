import GaloisForLFunctions.RHTower.WeilLogShiftRawTransportLaw

/-! Uniform comparison of unbounded Lipschitz observables on the two finite raw laws. -/

open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalRawLipschitz_integral_gap (r k : ℕ) (L : NNReal)
    (f : ℝ → ℝ) (hf : LipschitzWith L f) :
    |(∫ x, f x ∂(finiteWeilCanonicalRawIndexLaw r k : Measure ℝ)) -
      (∫ x, f x ∂(finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ))| ≤
      (L : ℝ) * finiteWeilCanonicalRawFluctuationGap r k := by
  rw [finiteWeilCanonicalRawIndexLaw, finiteWeilCanonicalRawCorrectionLaw,
    finiteWeilCanonicalObservableLaw_integral_real,
    finiteWeilCanonicalObservableLaw_integral_real, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin (r + 1), |finiteWeilCanonicalEdgeMass r k i * f (finiteWeilCanonicalRawIndexValue r k i) -
        finiteWeilCanonicalEdgeMass r k i * f (finiteWeilCanonicalRawCorrectionValue r k i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        ((L : ℝ) * |finiteWeilCanonicalFluctuationResidualValue r k i|) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul, abs_of_pos (finiteWeilCanonicalEdgeMass_pos r k i)]
      apply mul_le_mul_of_nonneg_left _ (finiteWeilCanonicalEdgeMass_pos r k i).le
      have h := hf.dist_le_mul (finiteWeilCanonicalRawIndexValue r k i)
        (finiteWeilCanonicalRawCorrectionValue r k i)
      rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (finiteWeilCanonicalRawIndexValue r k i)
        (finiteWeilCanonicalRawCorrectionValue r k i)] at h
      exact h
    _ = _ := by
      unfold finiteWeilCanonicalRawFluctuationGap
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

def finiteWeilCanonicalRawLipschitzDual (r k : ℕ) : ℝ :=
  lipschitzDual (finiteWeilCanonicalRawIndexLaw r k : Measure ℝ)
    (finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ)

theorem finiteWeilCanonicalRawLipschitzDual_bddAbove (r k : ℕ) :
    BddAbove (Set.range fun f : {f : ℝ → ℝ // LipschitzWith 1 f} =>
      (∫ x, (f : ℝ → ℝ) x ∂(finiteWeilCanonicalRawIndexLaw r k : Measure ℝ)) -
        (∫ x, (f : ℝ → ℝ) x ∂(finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ))) := by
  refine ⟨finiteWeilCanonicalRawFluctuationGap r k, ?_⟩
  rintro _ ⟨f, rfl⟩
  have h := finiteWeilCanonicalRawLipschitz_integral_gap r k 1 (f : ℝ → ℝ) f.property
  simp only [NNReal.coe_one, one_mul] at h
  exact (le_abs_self _).trans h

theorem finiteWeilCanonicalRawLipschitzDual_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalRawLipschitzDual r k := by
  have h := le_ciSup (finiteWeilCanonicalRawLipschitzDual_bddAbove r k)
    (⟨fun _ => (0 : ℝ), (LipschitzWith.const 0).weaken zero_le_one⟩ :
      {f : ℝ → ℝ // LipschitzWith 1 f})
  simpa only [finiteWeilCanonicalRawLipschitzDual, lipschitzDual, integral_zero, sub_self] using h

theorem finiteWeilCanonicalRawLipschitzDual_le_gap (r k : ℕ) :
    finiteWeilCanonicalRawLipschitzDual r k ≤ finiteWeilCanonicalRawFluctuationGap r k := by
  letI : Nonempty {f : ℝ → ℝ // LipschitzWith 1 f} :=
    ⟨⟨fun _ => 0, (LipschitzWith.const 0).weaken zero_le_one⟩⟩
  unfold finiteWeilCanonicalRawLipschitzDual lipschitzDual
  apply ciSup_le
  intro f
  have h := finiteWeilCanonicalRawLipschitz_integral_gap r k 1 (f : ℝ → ℝ) f.property
  simp only [NNReal.coe_one, one_mul] at h
  exact (le_abs_self _).trans h

end RHTower
