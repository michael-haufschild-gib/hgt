import GaloisForLFunctions.RHTower.HeatLadderPrincipal
import GaloisForLFunctions.RHTower.HeatEnergyExpand

/-!
# Expanding the all-order squared principal part

The square of the `K`-th order Jonquière principal part is a finite sum of two-sided power tests
at the exponents `2σ-2`, `s-1+k`, `conj s - 1 + k` and the non-negative integers.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- A real power splits into a sign and a modulus power. -/
theorem ofReal_pow_eq_sign_mul_abs_cpow {θ : ℝ} (hne : θ ≠ 0) (k : ℕ) :
    ((θ : ℝ) : ℂ) ^ k
      = (if 0 < θ then 1 else (-1 : ℂ) ^ k) * ((|θ| : ℝ) : ℂ) ^ ((k : ℕ) : ℂ) := by
  rw [Complex.cpow_natCast]
  by_cases h : 0 < θ
  · rw [if_pos h, abs_of_pos h, one_mul]
  · have hlt : θ < 0 := lt_of_le_of_ne (not_lt.mp h) hne
    rw [if_neg h, abs_of_neg hlt]
    push_cast
    rw [← mul_pow]
    ring

theorem abs_cpow_add {θ : ℝ} (hne : θ ≠ 0) (a b : ℂ) :
    ((|θ| : ℝ) : ℂ) ^ a * ((|θ| : ℝ) : ℂ) ^ b = ((|θ| : ℝ) : ℂ) ^ (a + b) := by
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hne
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]

theorem conj_ofReal_pow (θ : ℝ) (k : ℕ) :
    (starRingEnd ℂ) (((θ : ℝ) : ℂ) ^ k) = ((θ : ℝ) : ℂ) ^ k := by
  rw [map_pow, Complex.conj_ofReal]

/-- The pure singular square. -/
theorem leadSq_expand (s : ℂ) {θ : ℝ} (hne : θ ≠ 0) :
    (jonquiereLeadAt s θ * ((|θ| : ℝ) : ℂ) ^ (s - 1))
        * (starRingEnd ℂ) (jonquiereLeadAt s θ * ((|θ| : ℝ) : ℂ) ^ (s - 1))
      = (if 0 < θ then ((‖jonquiereLead s‖ ^ (2 : ℕ) : ℝ) : ℂ)
          else ((‖jonquiereLeadNeg s‖ ^ (2 : ℕ) : ℝ) : ℂ))
        * ((|θ| : ℝ) : ℂ) ^ (((2 * s.re - 2 : ℝ)) : ℂ) := by
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hne
  have hsq := cpow_mul_conj_cpow hpos (s - 1)
  have hre : (2 * (s - 1).re : ℝ) = 2 * s.re - 2 := by
    simp [Complex.sub_re]
    ring
  rw [hre] at hsq
  have habs : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [map_mul, jonquiereLeadAt]
  by_cases h : 0 < θ
  · rw [if_pos h, if_pos h, ← habs (jonquiereLead s), ← hsq]
    ring
  · rw [if_neg h, if_neg h, ← habs (jonquiereLeadNeg s), ← hsq]
    ring

/-- The singular--regular cross term. -/
theorem leadRegCross_expand (s : ℂ) (K : ℕ) {θ : ℝ} (hne : θ ≠ 0) :
    (jonquiereLeadAt s θ * ((|θ| : ℝ) : ℂ) ^ (s - 1))
        * (starRingEnd ℂ) (jonquiereRegPoly s K θ)
      = ∑ k ∈ Finset.range (K + 1),
          (if 0 < θ then jonquiereLead s * (starRingEnd ℂ) (jonquiereRegCoeff s k)
            else (-1 : ℂ) ^ k * (jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereRegCoeff s k)))
            * ((|θ| : ℝ) : ℂ) ^ (s - 1 + ((k : ℕ) : ℂ)) := by
  rw [jonquiereRegPoly, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, conj_ofReal_pow, ofReal_pow_eq_sign_mul_abs_cpow hne k, jonquiereLeadAt]
  by_cases h : 0 < θ
  · rw [if_pos h, if_pos h, if_pos h, ← abs_cpow_add hne]
    ring
  · rw [if_neg h, if_neg h, if_neg h, ← abs_cpow_add hne]
    ring

/-- The regular--singular cross term. -/
theorem regLeadCross_expand (s : ℂ) (K : ℕ) {θ : ℝ} (hne : θ ≠ 0) :
    jonquiereRegPoly s K θ
        * (starRingEnd ℂ) (jonquiereLeadAt s θ * ((|θ| : ℝ) : ℂ) ^ (s - 1))
      = ∑ k ∈ Finset.range (K + 1),
          (if 0 < θ then (starRingEnd ℂ) (jonquiereLead s) * jonquiereRegCoeff s k
            else (-1 : ℂ) ^ k
              * ((starRingEnd ℂ) (jonquiereLeadNeg s) * jonquiereRegCoeff s k))
            * ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) s - 1 + ((k : ℕ) : ℂ)) := by
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hne
  have hconj := conj_ofReal_cpow hpos (s - 1)
  rw [show (starRingEnd ℂ) (s - 1) = (starRingEnd ℂ) s - 1 by rw [map_sub, map_one]] at hconj
  rw [jonquiereRegPoly, map_mul, hconj, Finset.sum_mul, jonquiereLeadAt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ofReal_pow_eq_sign_mul_abs_cpow hne k]
  by_cases h : 0 < θ
  · rw [if_pos h, if_pos h, if_pos h, ← abs_cpow_add hne]
    ring
  · rw [if_neg h, if_neg h, if_neg h, ← abs_cpow_add hne]
    ring

/-- The regular square. -/
theorem regSq_expand (s : ℂ) (K : ℕ) {θ : ℝ} (hne : θ ≠ 0) :
    jonquiereRegPoly s K θ * (starRingEnd ℂ) (jonquiereRegPoly s K θ)
      = ∑ k ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
          (if 0 < θ then jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)
            else (-1 : ℂ) ^ (k + l)
              * (jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)))
            * ((|θ| : ℝ) : ℂ) ^ (((k + l : ℕ) : ℂ)) := by
  rw [jonquiereRegPoly, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, conj_ofReal_pow, ofReal_pow_eq_sign_mul_abs_cpow hne k,
    ofReal_pow_eq_sign_mul_abs_cpow hne l]
  have hsum : ((|θ| : ℝ) : ℂ) ^ ((k : ℕ) : ℂ) * ((|θ| : ℝ) : ℂ) ^ ((l : ℕ) : ℂ)
      = ((|θ| : ℝ) : ℂ) ^ (((k + l : ℕ) : ℂ)) := by
    rw [abs_cpow_add hne]
    congr 1
    push_cast
    ring
  by_cases h : 0 < θ
  · rw [if_pos h, if_pos h, if_pos h]
    rw [show (1 : ℂ) * ((|θ| : ℝ) : ℂ) ^ ((k : ℕ) : ℂ) = ((|θ| : ℝ) : ℂ) ^ ((k : ℕ) : ℂ) by ring]
    calc jonquiereRegCoeff s k * ((|θ| : ℝ) : ℂ) ^ ((k : ℕ) : ℂ)
          * ((starRingEnd ℂ) (jonquiereRegCoeff s l)
            * (1 * ((|θ| : ℝ) : ℂ) ^ ((l : ℕ) : ℂ)))
        = jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)
            * (((|θ| : ℝ) : ℂ) ^ ((k : ℕ) : ℂ) * ((|θ| : ℝ) : ℂ) ^ ((l : ℕ) : ℂ)) := by ring
      _ = jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)
            * ((|θ| : ℝ) : ℂ) ^ (((k + l : ℕ) : ℂ)) := by rw [hsum]
  · rw [if_neg h, if_neg h, if_neg h]
    have hpowsplit : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ l) = (-1 : ℂ) ^ (k + l) := by
      rw [pow_add]
    calc jonquiereRegCoeff s k * ((-1 : ℂ) ^ k * ((|θ| : ℝ) : ℂ) ^ ((k : ℕ) : ℂ))
          * ((starRingEnd ℂ) (jonquiereRegCoeff s l)
            * ((-1 : ℂ) ^ l * ((|θ| : ℝ) : ℂ) ^ ((l : ℕ) : ℂ)))
        = (((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ l))
            * (jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l))
            * (((|θ| : ℝ) : ℂ) ^ ((k : ℕ) : ℂ) * ((|θ| : ℝ) : ℂ) ^ ((l : ℕ) : ℂ)) := by ring
      _ = (-1 : ℂ) ^ (k + l)
            * (jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l))
            * ((|θ| : ℝ) : ℂ) ^ (((k + l : ℕ) : ℂ)) := by rw [hsum, hpowsplit]

/-- **The full all-order expansion of the squared principal part.** -/
theorem germPrincipalOrder_mul_conj (s : ℂ) (K : ℕ) {θ : ℝ} (hne : θ ≠ 0) :
    germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ)
      = (if 0 < θ then ((‖jonquiereLead s‖ ^ (2 : ℕ) : ℝ) : ℂ)
            else ((‖jonquiereLeadNeg s‖ ^ (2 : ℕ) : ℝ) : ℂ))
          * ((|θ| : ℝ) : ℂ) ^ (((2 * s.re - 2 : ℝ)) : ℂ)
        + (∑ k ∈ Finset.range (K + 1),
            (if 0 < θ then jonquiereLead s * (starRingEnd ℂ) (jonquiereRegCoeff s k)
              else (-1 : ℂ) ^ k * (jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereRegCoeff s k)))
              * ((|θ| : ℝ) : ℂ) ^ (s - 1 + ((k : ℕ) : ℂ)))
        + (∑ k ∈ Finset.range (K + 1),
            (if 0 < θ then (starRingEnd ℂ) (jonquiereLead s) * jonquiereRegCoeff s k
              else (-1 : ℂ) ^ k
                * ((starRingEnd ℂ) (jonquiereLeadNeg s) * jonquiereRegCoeff s k))
              * ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) s - 1 + ((k : ℕ) : ℂ)))
        + (∑ k ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
            (if 0 < θ then jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)
              else (-1 : ℂ) ^ (k + l)
                * (jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)))
              * ((|θ| : ℝ) : ℂ) ^ (((k + l : ℕ) : ℂ))) := by
  rw [← leadSq_expand s hne, ← leadRegCross_expand s K hne, ← regLeadCross_expand s K hne,
    ← regSq_expand s K hne, germPrincipalOrder, map_add]
  ring

end RHTower
