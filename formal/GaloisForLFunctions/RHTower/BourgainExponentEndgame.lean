/-
# Bourgain's exact exponent arithmetic

Section 4 of Bourgain's proof combines three exponential-sum estimates.
Writing `T > 1`, `M > 0`, and `A = ‖S(T,M)‖`, their power shapes are

* the exponent-pair bound `A ≤ M^(11/18) T^(1/9+ε)`;
* Huxley's bound `A ≤ T^(1/32+ε) M^(103/128)`, available once
  `M > T^(12/31)`;
* Bourgain's decoupling/spacing bound
  `A ≤ M^(1/2) T^(13/84+ε)`, available once `M ≥ T^(17/42)`.

The first bound reaches `M ≤ T^(11/28)`.  Huxley's bound reaches
`M ≤ T^(332/819)`.  The strict overlaps

  `12/31 < 11/28` and `17/42 < 332/819`

therefore close the full range.  This file proves that endgame directly with
real powers.  It introduces no asymptotic notation and loses no additional
epsilon.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace RHTower

/-- Bourgain's critical-line exponent. -/
noncomputable def bourgainZetaExponent : ℝ := 13 / 84

/-- The exponent-pair estimate `(1/9, 13/18)` reaches Bourgain's target up to
`M = T^(11/28)`. -/
theorem exponentPair_bound_le_bourgain
    {T M ε : ℝ} (hT : 0 < T) (hM : 0 < M)
    (hMT : M ≤ T ^ (11 / 28 : ℝ)) :
    M ^ (11 / 18 : ℝ) * T ^ ((1 / 9 : ℝ) + ε) ≤
      M ^ (1 / 2 : ℝ) * T ^ (bourgainZetaExponent + ε) := by
  have hsmall :
      M ^ (1 / 9 : ℝ) ≤ T ^ (11 / 252 : ℝ) := by
    calc
      M ^ (1 / 9 : ℝ) ≤ (T ^ (11 / 28 : ℝ)) ^ (1 / 9 : ℝ) :=
        Real.rpow_le_rpow hM.le hMT (by norm_num)
      _ = T ^ ((11 / 28 : ℝ) * (1 / 9 : ℝ)) := by
        rw [← Real.rpow_mul hT.le]
      _ = T ^ (11 / 252 : ℝ) := by norm_num
  have hMhalf : 0 ≤ M ^ (1 / 2 : ℝ) := Real.rpow_nonneg hM.le _
  have hTpow : 0 ≤ T ^ ((1 / 9 : ℝ) + ε) := Real.rpow_nonneg hT.le _
  calc
    M ^ (11 / 18 : ℝ) * T ^ ((1 / 9 : ℝ) + ε) =
        M ^ (1 / 2 : ℝ) *
          (M ^ (1 / 9 : ℝ) * T ^ ((1 / 9 : ℝ) + ε)) := by
      rw [show (11 / 18 : ℝ) = 1 / 2 + 1 / 9 by norm_num,
        Real.rpow_add hM]
      ring
    _ ≤ M ^ (1 / 2 : ℝ) *
          (T ^ (11 / 252 : ℝ) * T ^ ((1 / 9 : ℝ) + ε)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsmall hTpow) hMhalf
    _ = M ^ (1 / 2 : ℝ) *
          T ^ (bourgainZetaExponent + ε) := by
      rw [← Real.rpow_add hT]
      congr 2
      simp only [bourgainZetaExponent]
      ring

/-- Huxley's estimate reaches Bourgain's target up to
`M = T^(332/819)`. -/
theorem huxley_bound_le_bourgain
    {T M ε : ℝ} (hT : 0 < T) (hM : 0 < M)
    (hMT : M ≤ T ^ (332 / 819 : ℝ)) :
    T ^ ((1 / 32 : ℝ) + ε) * M ^ (103 / 128 : ℝ) ≤
      M ^ (1 / 2 : ℝ) * T ^ (bourgainZetaExponent + ε) := by
  have hsmall :
      M ^ (39 / 128 : ℝ) ≤ T ^ (83 / 672 : ℝ) := by
    calc
      M ^ (39 / 128 : ℝ) ≤
          (T ^ (332 / 819 : ℝ)) ^ (39 / 128 : ℝ) :=
        Real.rpow_le_rpow hM.le hMT (by norm_num)
      _ = T ^ ((332 / 819 : ℝ) * (39 / 128 : ℝ)) := by
        rw [← Real.rpow_mul hT.le]
      _ = T ^ (83 / 672 : ℝ) := by norm_num
  have hMhalf : 0 ≤ M ^ (1 / 2 : ℝ) := Real.rpow_nonneg hM.le _
  have hTpow : 0 ≤ T ^ ((1 / 32 : ℝ) + ε) := Real.rpow_nonneg hT.le _
  calc
    T ^ ((1 / 32 : ℝ) + ε) * M ^ (103 / 128 : ℝ) =
        M ^ (1 / 2 : ℝ) *
          (T ^ ((1 / 32 : ℝ) + ε) * M ^ (39 / 128 : ℝ)) := by
      rw [show (103 / 128 : ℝ) = 1 / 2 + 39 / 128 by norm_num,
        Real.rpow_add hM]
      ring
    _ ≤ M ^ (1 / 2 : ℝ) *
          (T ^ ((1 / 32 : ℝ) + ε) * T ^ (83 / 672 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsmall hTpow) hMhalf
    _ = M ^ (1 / 2 : ℝ) *
          T ^ (bourgainZetaExponent + ε) := by
      rw [← Real.rpow_add hT]
      congr 2
      simp only [bourgainZetaExponent]
      ring

/-- The two rational overlaps used in Bourgain's Section 4 range split. -/
theorem bourgain_range_overlaps :
    (12 / 31 : ℝ) < 11 / 28 ∧
      (17 / 42 : ℝ) < 332 / 819 := by
  constructor <;> norm_num

/-- **Bourgain Section 4 endgame.**

Any nonnegative quantity satisfying the three estimates with their exact
published ranges satisfies the `13/84` target throughout the conductor
range.  The result is abstract in `A`; later modules instantiate it with the
finite logarithmic exponential sum. -/
theorem bourgain_exponent_endgame
    {T M A ε : ℝ} (hT : 1 ≤ T) (hM : 0 < M)
    (hPair :
      A ≤ M ^ (11 / 18 : ℝ) * T ^ ((1 / 9 : ℝ) + ε))
    (hHuxley :
      T ^ (12 / 31 : ℝ) < M →
        A ≤ T ^ ((1 / 32 : ℝ) + ε) * M ^ (103 / 128 : ℝ))
    (hBourgain :
      T ^ (17 / 42 : ℝ) ≤ M →
        A ≤ M ^ (1 / 2 : ℝ) * T ^ (bourgainZetaExponent + ε)) :
    A ≤ M ^ (1 / 2 : ℝ) * T ^ (bourgainZetaExponent + ε) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  by_cases hPairRange : M ≤ T ^ (11 / 28 : ℝ)
  · exact hPair.trans (exponentPair_bound_le_bourgain hT0 hM hPairRange)
  have hHuxleyLower : T ^ (12 / 31 : ℝ) < M := by
    have hpow :
        T ^ (12 / 31 : ℝ) ≤ T ^ (11 / 28 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT (bourgain_range_overlaps.1.le)
    exact lt_of_le_of_lt hpow (lt_of_not_ge hPairRange)
  by_cases hHuxleyRange : M ≤ T ^ (332 / 819 : ℝ)
  · exact (hHuxley hHuxleyLower).trans
      (huxley_bound_le_bourgain hT0 hM hHuxleyRange)
  have hBourgainRange : T ^ (17 / 42 : ℝ) ≤ M := by
    have hpow :
        T ^ (17 / 42 : ℝ) ≤ T ^ (332 / 819 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT (bourgain_range_overlaps.2.le)
    exact hpow.trans (le_of_lt (lt_of_not_ge hHuxleyRange))
  exact hBourgain hBourgainRange

end RHTower
