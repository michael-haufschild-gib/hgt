import GaloisForLFunctions.RHTower.HeatLadderMoments
import GaloisForLFunctions.RHTower.HeatApertureEchoParity

/-!
# Identification of the ladder coefficients

The averaged singular--regular coefficient of the `k`-th window moment, multiplied by the
Gaussian main term of that moment, is exactly the archimedean echo coefficient `C_k(s)` times the
reflected zeta value `ζ(conj s - k)` and the aperture power `x^{(s+k-1)/2}`.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- The averaged Jonquière leading coefficients. -/
theorem jonquiereLead_avg_pow (s : ℂ) (k : ℕ) :
    ((-I) ^ k) * (jonquiereLead s + (-1 : ℂ) ^ k * jonquiereLeadNeg s) / 2
      = Complex.Gamma (1 - s) * Complex.sin (↑Real.pi * (s + (k : ℂ)) / 2) := by
  have h := jonquiere_lead_avg_identity s k
  rw [jonquiereLead, jonquiereLeadNeg]
  rw [show ((-I) ^ k) * (Complex.Gamma (1 - s) * Complex.exp (↑Real.pi * I * (1 - s) / 2)
      + (-1 : ℂ) ^ k * (Complex.Gamma (1 - s) * Complex.exp (-↑Real.pi * I * (1 - s) / 2))) / 2
      = Complex.Gamma (1 - s) * (((-I) ^ k) * (Complex.exp (↑Real.pi * I * (1 - s) / 2)
          + (-1 : ℂ) ^ k * Complex.exp (-↑Real.pi * I * (1 - s) / 2)) / 2) by ring, h]

/-- Conjugation of the regular Jonquière coefficient. -/
theorem conj_jonquiereRegCoeff (s : ℂ) (k : ℕ) :
    (starRingEnd ℂ) (jonquiereRegCoeff s k)
      = (starRingEnd ℂ) (riemannZeta (s - (k : ℂ))) * ((-I) ^ k) / (Nat.factorial k : ℂ) := by
  rw [jonquiereRegCoeff, map_div₀, map_mul, map_pow, Complex.conj_I]
  congr 1
  rw [map_natCast]

/-- **The `k`-th ladder coefficient is the archimedean echo coefficient.**  This is the card's
`(2)` read off the expansion. -/
theorem heatLadderCross_eq {s : ℂ} (k : ℕ) {x : ℝ} (hx : 0 < x) :
    ((jonquiereLead s * (starRingEnd ℂ) (jonquiereRegCoeff s k)
        + (-1 : ℂ) ^ k * (jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereRegCoeff s k))) / 2)
      * heatMomentTerm x (s - 1 + (k : ℂ))
      = GaloisForLFunctions.heatApertureEchoValue s k
        * ((x : ℝ) : ℂ) ^ ((s + (k : ℂ) - 1) / 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hFne : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hIk : ((-I : ℂ)) ^ k * (I : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    simp [Complex.I_mul_I]
  have havg := jonquiereLead_avg_pow s k
  have hsplit : (((4 * Real.pi * x : ℝ)) : ℂ) ^ ((s - 1 + (k : ℂ)) / 2)
      = (((4 * Real.pi : ℝ)) : ℂ) ^ ((s + (k : ℂ) - 1) / 2)
        * ((x : ℝ) : ℂ) ^ ((s + (k : ℂ) - 1) / 2) := by
    rw [show ((4 * Real.pi * x : ℝ) : ℂ) = (((4 * Real.pi : ℝ)) : ℂ) * ((x : ℝ) : ℂ) by
      push_cast; ring, Complex.mul_cpow_ofReal_nonneg (by positivity) hx.le]
    congr 2 <;> ring
  have hbase : (((4 * Real.pi : ℝ)) : ℂ) ^ ((s + (k : ℂ) - 1) / 2)
      = (4 * (Real.pi : ℂ)) ^ ((s + (k : ℂ) - 1) / 2) := by
    congr 1
    push_cast
    ring
  rw [conj_jonquiereRegCoeff, heatMomentTerm, hsplit, hbase,
    GaloisForLFunctions.heatApertureEchoValue, GaloisForLFunctions.heatApertureEchoCoeff,
    GaloisForLFunctions.heatApertureEchoCore, GaloisForLFunctions.heatApertureBackwardZetaValue,
    ← riemannZeta_conj]
  rw [show (s - 1 + (k : ℂ) + 1) / 2 = (s + (k : ℂ)) / 2 by ring,
    show ((starRingEnd ℂ) s - (k : ℂ)) = (starRingEnd ℂ) (s - (k : ℂ)) by
      rw [map_sub, Complex.conj_natCast]]
  linear_combination (riemannZeta ((starRingEnd ℂ) (s - (k : ℂ)))
      * (4 * (Real.pi : ℂ)) ^ ((s + (k : ℂ) - 1) / 2) * ((x : ℝ) : ℂ) ^ ((s + (k : ℂ) - 1) / 2)
      * Complex.Gamma ((s + (k : ℂ)) / 2)
      / ((Nat.factorial k : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ))) * havg

end RHTower
