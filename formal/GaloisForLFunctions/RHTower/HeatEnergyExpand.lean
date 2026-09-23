import GaloisForLFunctions.RHTower.HeatEnergyPrincipal

/-!
# Expanding the squared principal part

The square of the two-sided Jonquière principal part is a sum of four two-sided power tests, at
exponents `2σ-2`, `s-1`, `conj s - 1` and `0`.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- Conjugation acts on the exponent of a positive real base. -/
theorem conj_ofReal_cpow {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (starRingEnd ℂ) (((r : ℝ) : ℂ) ^ w) = ((r : ℝ) : ℂ) ^ ((starRingEnd ℂ) w) := by
  have hne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne, ← Complex.exp_conj,
    map_mul]
  congr 2
  rw [← Complex.ofReal_log hr.le, Complex.conj_ofReal]

/-- The modulus square of a positive real power. -/
theorem cpow_mul_conj_cpow {r : ℝ} (hr : 0 < r) (w : ℂ) :
    ((r : ℝ) : ℂ) ^ w * (starRingEnd ℂ) (((r : ℝ) : ℂ) ^ w)
      = ((r : ℝ) : ℂ) ^ (((2 * w.re : ℝ)) : ℂ) := by
  have hne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [conj_ofReal_cpow hr, ← Complex.cpow_add _ _ hne]
  congr 1
  rw [Complex.add_conj]

/-- **The four-term expansion of the squared principal part.** -/
theorem germPrincipal_mul_conj (s : ℂ) {θ : ℝ} (hne : θ ≠ 0) :
    germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ)
      = (if 0 < θ then ((‖jonquiereLead s‖ ^ (2 : ℕ) : ℝ) : ℂ)
            else ((‖jonquiereLeadNeg s‖ ^ (2 : ℕ) : ℝ) : ℂ))
          * ((|θ| : ℝ) : ℂ) ^ (((2 * s.re - 2 : ℝ)) : ℂ)
        + (if 0 < θ then jonquiereLead s * (starRingEnd ℂ) (riemannZeta s)
            else jonquiereLeadNeg s * (starRingEnd ℂ) (riemannZeta s))
          * ((|θ| : ℝ) : ℂ) ^ (s - 1)
        + (if 0 < θ then (starRingEnd ℂ) (jonquiereLead s) * riemannZeta s
            else (starRingEnd ℂ) (jonquiereLeadNeg s) * riemannZeta s)
          * ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) s - 1)
        + ((‖riemannZeta s‖ ^ (2 : ℕ) : ℝ) : ℂ) * ((|θ| : ℝ) : ℂ) ^ (0 : ℂ) := by
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hne
  have hne' : (((|θ| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  have hsq := cpow_mul_conj_cpow hpos (s - 1)
  have hre : (2 * (s - 1).re : ℝ) = 2 * s.re - 2 := by
    simp [Complex.sub_re]
    ring
  rw [hre] at hsq
  have hconj := conj_ofReal_cpow hpos (s - 1)
  have hcs : (starRingEnd ℂ) (s - 1) = (starRingEnd ℂ) s - 1 := by
    rw [map_sub, map_one]
  rw [hcs] at hconj

  have habs : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsq2 : ((|θ| : ℝ) : ℂ) ^ (s - 1) * ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) s - 1)
      = ((|θ| : ℝ) : ℂ) ^ (((2 * s.re - 2 : ℝ)) : ℂ) := by
    rw [← hconj]
    exact hsq
  rw [germPrincipal, jonquiereLeadAt, map_add, map_mul, hconj, Complex.cpow_zero]
  by_cases h : 0 < θ
  · rw [if_pos h, if_pos h, if_pos h, if_pos h]
    rw [← habs (jonquiereLead s), ← habs (riemannZeta s), ← hsq2]
    ring
  · rw [if_neg h, if_neg h, if_neg h, if_neg h]
    rw [← habs (jonquiereLeadNeg s), ← habs (riemannZeta s), ← hsq2]
    ring

end RHTower
