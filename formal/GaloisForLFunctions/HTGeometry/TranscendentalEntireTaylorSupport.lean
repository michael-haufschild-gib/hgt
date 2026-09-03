import GaloisForLFunctions.HTGeometry.TranscendentalEntireOrderOne
import GaloisForLFunctions.HTGeometry.EntireOrderTwoSeries

namespace GaloisForLFunctions.HTGeometry

/-- A transcendental entire function has nonzero Taylor coefficients beyond every finite cutoff. -/
theorem exists_taylorCoeff_ne_zero_ge_of_transcendentalEntire
    {f : ℂ → ℂ} (hf : TranscendentalEntire f) (M : ℕ) :
    ∃ n, M ≤ n ∧ taylorCoeff f n ≠ 0 := by
  by_contra hnone
  apply hf.2
  have hzero : ∀ n : ℕ, M ≤ n → taylorCoeff f n = 0 := by
    intro n hn
    by_contra hne
    exact hnone ⟨n, hn, hne⟩
  classical
  refine ⟨∑ n ∈ Finset.range M,
    Polynomial.C (taylorCoeff f n) * Polynomial.X ^ n, fun z => ?_⟩
  have hsum := hasSum_taylorCoeff hf.1 z
  have hfin : HasSum (fun n : ℕ => taylorCoeff f n * z ^ n)
      (∑ n ∈ Finset.range M, taylorCoeff f n * z ^ n) := by
    refine hasSum_sum_of_ne_finset_zero ?_
    intro n hn
    rw [hzero n (by simpa using Finset.mem_range.not.mp hn), zero_mul]
  have hvalue := hsum.unique hfin
  rw [hvalue, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun n _ => by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- In particular, a transcendental entire Taylor expansion has a nonzero coefficient. -/
theorem exists_taylorCoeff_ne_zero_of_transcendentalEntire
    {f : ℂ → ℂ} (hf : TranscendentalEntire f) :
    ∃ n, taylorCoeff f n ≠ 0 := by
  obtain ⟨n, _, hn⟩ := exists_taylorCoeff_ne_zero_ge_of_transcendentalEntire hf 0
  exact ⟨n, hn⟩

end GaloisForLFunctions.HTGeometry
