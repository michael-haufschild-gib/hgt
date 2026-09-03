import GaloisForLFunctions.HTGeometry.EulerCompositionPolynomialRigidity
import GaloisForLFunctions.HTGeometry.TranscendentalEntireOrderOne

namespace GaloisForLFunctions.HTGeometry

/-- A transcendental entire function has nonzero Taylor coefficients beyond every finite cutoff. -/
theorem exists_taylorCoeff_ne_zero_ge_of_transcendentalEntire
    {f : ℂ → ℂ} (hf : TranscendentalEntire f) (M : ℕ) :
    ∃ n, M ≤ n ∧ taylorCoeff f n ≠ 0 := by
  by_contra hnone
  apply hf.2
  apply exists_polynomial_of_eventually_taylorCoeff_eq_zero hf.1
  intro n hn
  by_contra hne
  exact hnone ⟨n, hn, hne⟩

/-- In particular, a transcendental entire Taylor expansion has a nonzero coefficient. -/
theorem exists_taylorCoeff_ne_zero_of_transcendentalEntire
    {f : ℂ → ℂ} (hf : TranscendentalEntire f) :
    ∃ n, taylorCoeff f n ≠ 0 := by
  obtain ⟨n, _, hn⟩ := exists_taylorCoeff_ne_zero_ge_of_transcendentalEntire hf 0
  exact ⟨n, hn⟩

end GaloisForLFunctions.HTGeometry
