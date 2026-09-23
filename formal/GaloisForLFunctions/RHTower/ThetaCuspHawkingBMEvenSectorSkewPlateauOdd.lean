import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewPlateauHarmonic

/-!
# Rate-swap oddness and conjugation of the plateau kernel at every harmonic

The two-rate horizon plateau kernel `skewPlateauMu s μ` is odd under the rate swap `s ↦ −3 − s` at
every harmonic `μ` (`skewPlateauMu_reflect`: the numerator is odd and the denominator
`128(2−μ)²(μ−λ₂(s))(μ−λ₂(−3−s))` is invariant, the swap exchanging `λ₂` and `λ₂'`), and it has real
coefficients (`skewPlateauMu_conj`). On the critical line `s = −3/2 + it` the conjugate of `s` is its
rate swap, so for every complex harmonic `skewPlateauMu s (conj μ) = −conj (skewPlateauMu s μ)`
(`skewPlateauMu_line_conj`): at a real harmonic the kernel is purely imaginary
(`skewPlateauMu_line_re_general`), and a conjugate pair of complex harmonics — such as the
eigenvalues `2ρ(2ρ−1)`, `(2−2ρ)(1−2ρ)` of the growing Weyl powers `y^{2ρ}`, `y^{2−2ρ}` of the angular
square, which are conjugate on the line — contributes `K(s,μ) − conj K(s,μ)`, again purely imaginary
when weighted by conjugate coefficients. This completes the on-line phase structure of the plateau
across the square-integrable and the growing channels alike.
-/

set_option autoImplicit false

namespace RHTower.D4BMScalarStream

theorem skewPlateauMuNumerator_reflect (s μ : ℂ) :
    skewPlateauMuNumerator (-3 - s) μ = -skewPlateauMuNumerator s μ := by
  unfold skewPlateauMuNumerator
  ring

theorem skewPlateauMu_denominator_reflect (s μ : ℂ) :
    128 * (2 - μ) ^ (2 : ℕ) * (μ - (2 * (-3 - s) + 1) * (2 * (-3 - s) + 2)) * (μ - (2 * (-3 - s) + 4) * (2 * (-3 - s) + 5)) =
      128 * (2 - μ) ^ (2 : ℕ) * (μ - (2 * s + 1) * (2 * s + 2)) * (μ - (2 * s + 4) * (2 * s + 5)) := by
  ring

/-- The plateau kernel is odd under the rate swap at every harmonic. -/
theorem skewPlateauMu_reflect (s μ : ℂ) : skewPlateauMu (-3 - s) μ = -skewPlateauMu s μ := by
  unfold skewPlateauMu
  rw [skewPlateauMuNumerator_reflect, skewPlateauMu_denominator_reflect, neg_div]

/-- The plateau kernel has real coefficients. -/
theorem skewPlateauMu_conj (s μ : ℂ) :
    skewPlateauMu (starRingEnd ℂ s) (starRingEnd ℂ μ) = starRingEnd ℂ (skewPlateauMu s μ) := by
  unfold skewPlateauMu skewPlateauMuNumerator
  simp only [map_div₀, map_add, map_mul, map_pow, map_neg, map_sub, map_ofNat, map_one]

theorem line_conj (t : ℝ) : starRingEnd ℂ ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) = -3 - ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp only [map_div₀, map_neg, map_ofNat]
  ring

/-- On the critical line, conjugating the harmonic reflects the kernel. -/
theorem skewPlateauMu_line_conj (t : ℝ) (μ : ℂ) :
    skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (starRingEnd ℂ μ) =
      -starRingEnd ℂ (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) μ) := by
  rw [← skewPlateauMu_conj, line_conj, skewPlateauMu_reflect, neg_neg]

/-- At every real harmonic the kernel is purely imaginary on the critical line. -/
theorem skewPlateauMu_line_re_general (t : ℝ) (μ : ℂ) (hμ : starRingEnd ℂ μ = μ) :
    (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) μ).re = 0 := by
  have h := skewPlateauMu_line_conj t μ
  rw [hμ] at h
  have h' := congrArg Complex.re h
  rw [Complex.neg_re, Complex.conj_re] at h'
  linarith

end RHTower.D4BMScalarStream
