import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeFreeRangePacketNatOrder

/-!
# Monotonicity of fixed-width Route-T tail envelopes

The canonical cutoff only needs to be certified at the smallest admissible relative width.  Every
wider fixed shell width decreases the reciprocal tail power and simultaneously enlarges the
logarithmically normalized defect threshold.  This module formalizes both monotonicities together.
-/

noncomputable section
namespace RHTower.Sieve

/-- A natural-order tail certificate propagates from a positive width `h` to every wider width
`H ≤ 1/4`.  Both the reciprocal-power cost and normalized telescope threshold move favorably. -/
theorem maynardNatOrderTailEnvelope_mono_width
    (r : ℕ) {P C K A h H : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hK : 0 ≤ K) (hA : 0 < A)
    (hh : 0 < h) (hH : 0 < H) (hHquarter : H ≤ 1 / 4) (hhH : h ≤ H)
    (hcut :
      P * (C * (1 / h) ^ (r + 1) * K ^ (-(r : ℝ))) ≤
        A / (2 * (1 + Real.log ((1 / 4) / h) / Real.log 2))) :
    P * (C * (1 / H) ^ (r + 1) * K ^ (-(r : ℝ))) ≤
      A / (2 * (1 + Real.log ((1 / 4) / H) / Real.log 2)) := by
  have hinv : 1 / H ≤ 1 / h := one_div_le_one_div_of_le hh hhH
  have hpow : (1 / H) ^ (r + 1) ≤ (1 / h) ^ (r + 1) :=
    pow_le_pow_left₀ (one_div_nonneg.mpr hH.le) hinv (r + 1)
  have hKpow : 0 ≤ K ^ (-(r : ℝ)) := Real.rpow_nonneg hK _
  have hleft :
      P * (C * (1 / H) ^ (r + 1) * K ^ (-(r : ℝ))) ≤
        P * (C * (1 / h) ^ (r + 1) * K ^ (-(r : ℝ))) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hC) hKpow) hP
  have hhquarter : h ≤ 1 / 4 := hhH.trans hHquarter
  have hratioH : 1 ≤ (1 / 4) / H := (le_div_iff₀ hH).2 (by simpa using hHquarter)
  have hratioMono : (1 / 4) / H ≤ (1 / 4) / h := by
    exact div_le_div_of_nonneg_left (by norm_num) hh hhH
  have hlogMono : Real.log ((1 / 4) / H) ≤ Real.log ((1 / 4) / h) :=
    Real.log_le_log (div_pos (by norm_num) hH) hratioMono
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquotMono :
      Real.log ((1 / 4) / H) / Real.log 2 ≤
        Real.log ((1 / 4) / h) / Real.log 2 :=
    (div_le_div_iff_of_pos_right hlogTwo).2 hlogMono
  have hdenH : 0 < 2 * (1 + Real.log ((1 / 4) / H) / Real.log 2) := by
    have := Real.log_nonneg hratioH
    positivity
  have hdenMono :
      2 * (1 + Real.log ((1 / 4) / H) / Real.log 2) ≤
        2 * (1 + Real.log ((1 / 4) / h) / Real.log 2) := by
    linarith
  have hright :
      A / (2 * (1 + Real.log ((1 / 4) / h) / Real.log 2)) ≤
        A / (2 * (1 + Real.log ((1 / 4) / H) / Real.log 2)) :=
    div_le_div_of_nonneg_left hA.le hdenH hdenMono
  exact hleft.trans (hcut.trans hright)

end RHTower.Sieve
