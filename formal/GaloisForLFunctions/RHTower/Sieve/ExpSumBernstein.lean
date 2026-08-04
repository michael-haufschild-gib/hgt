import GaloisForLFunctions.HTGeometry.TrigPolynomialBernstein
import GaloisForLFunctions.RHTower.Sieve.LargeSieveExpSum

/-!
# Bernstein's inequality for the sieve's exponential sums

A uniform bound on `S(t) = ∑_{n < N} c_n e(n t)` controls its increments with a constant coming
from the spectral degree alone:

`‖S x - S y‖ ≤ 2π(N-1) · sup ‖S‖ · |x - y|`.

Conjugating the increment turns `Re (conj z · S)` into a real trigonometric polynomial of degree
`N-1` bounded by `‖z‖ · sup ‖S‖`, so the real Bernstein inequality applies to it, and its own
increment is `‖z‖²`.  Dividing by `‖z‖` gives the bound.  No cancellation among the coefficients is
used and no integral over the period is formed.
-/

namespace RHTower.Sieve

open GaloisForLFunctions.HTGeometry QuantumAlg

/-- Cosine coefficients of the phase-rotated real part of an exponential sum. -/
noncomputable def rotCos (N : ℕ) (c : Fin N → ℂ) (w : ℂ) : ℕ → ℝ :=
  fun p => if h : p < N then (w * c ⟨p, h⟩).re else 0

/-- Sine coefficients of the phase-rotated real part of an exponential sum. -/
noncomputable def rotSin (N : ℕ) (c : Fin N → ℂ) (w : ℂ) : ℕ → ℝ :=
  fun p => if h : p < N then -(w * c ⟨p, h⟩).im else 0

/-- Reparametrising the circle frequency by `2π` turns it into the plain character. -/
theorem circleFreq_div_two_pi (u : ℝ) :
    circleFreq (u / (2 * Real.pi)) = Complex.exp ((u : ℂ) * Complex.I) := by
  unfold circleFreq
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  congr 1
  push_cast
  field_simp

/-- **The phase-rotated real part of an exponential sum is a real trigonometric polynomial of
degree `N - 1`.** -/
theorem genTrigCost_rot (N : ℕ) (hN : 1 ≤ N) (c : Fin N → ℂ) (w : ℂ) (u : ℝ) :
    genTrigCost (rotCos N c w) (rotSin N c w) (N - 1) u
      = (w * expSum N c (u / (2 * Real.pi))).re := by
  set F : ℕ → ℝ := fun n =>
    rotCos N c w n * Real.cos ((n : ℝ) * u) + rotSin N c w n * Real.sin ((n : ℝ) * u) with hF
  have hterm : ∀ n : Fin N,
      (w * (c n * circleFreq (u / (2 * Real.pi)) ^ (n : ℕ))).re = F (n : ℕ) := by
    intro n
    have hpow : circleFreq (u / (2 * Real.pi)) ^ (n : ℕ)
        = Complex.exp ((((n : ℕ) : ℝ) * u : ℝ) * Complex.I) := by
      rw [circleFreq_div_two_pi, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hassoc : w * (c n * circleFreq (u / (2 * Real.pi)) ^ (n : ℕ))
        = (w * c n) * Complex.exp ((((n : ℕ) : ℝ) * u : ℝ) * Complex.I) := by
      rw [hpow, mul_assoc]
    have hn : ((⟨(n : ℕ), n.isLt⟩ : Fin N)) = n := Fin.eta _ _
    rw [hassoc, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp only [hF, rotCos, rotSin, dif_pos n.isLt, hn]
    ring
  have hre : (w * expSum N c (u / (2 * Real.pi))).re = ∑ n ∈ Finset.range N, F n := by
    unfold expSum
    rw [Finset.mul_sum, Complex.re_sum, Finset.sum_congr rfl (fun n _ => hterm n)]
    exact Fin.sum_univ_eq_sum_range F N
  have hsplit : ∑ n ∈ Finset.range N, F n = F 0 + ∑ n ∈ Finset.Icc 1 (N - 1), F n := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N) F]
    congr 1
  rw [hre, hsplit]
  unfold genTrigCost
  congr 1
  simp [hF, rotCos, rotSin]

/-- Evaluating the rotated trigonometric polynomial at the rescaled point. -/
theorem genTrigCost_rot_two_pi (N : ℕ) (hN : 1 ≤ N) (c : Fin N → ℂ) (w : ℂ) (t : ℝ) :
    genTrigCost (rotCos N c w) (rotSin N c w) (N - 1) (2 * Real.pi * t)
      = (w * expSum N c t).re := by
  rw [genTrigCost_rot N hN c w]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  congr 2
  field_simp

/-- **Bernstein's inequality for an exponential sum.**  A uniform bound on
`S(t) = ∑_{n < N} c_n e(n t)` bounds every increment of `S` by the spectral degree alone; no
hypothesis on the coefficients is used. -/
theorem norm_expSum_sub_le (N : ℕ) (c : Fin N → ℂ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖expSum N c x‖ ≤ M) (x y : ℝ) :
    ‖expSum N c x - expSum N c y‖ ≤ 2 * Real.pi * ((N - 1 : ℕ) : ℝ) * M * |x - y| := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM x)
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hconst : expSum N c x = expSum N c y := by
      interval_cases N <;> simp [expSum]
    rw [hconst, sub_self, norm_zero]
    positivity
  have hN1 : 1 ≤ N := by omega
  have hR : 1 ≤ N - 1 := by omega
  set z : ℂ := expSum N c x - expSum N c y with hz
  rcases eq_or_ne z 0 with hz0 | hz0
  · rw [hz0, norm_zero]
    positivity
  have hnormz : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  set w : ℂ := (starRingEnd ℂ) z with hw
  have hbound : ∀ u : ℝ, |genTrigCost (rotCos N c w) (rotSin N c w) (N - 1) u| ≤ ‖z‖ * M := by
    intro u
    rw [genTrigCost_rot N hN1 c w u]
    calc |(w * expSum N c (u / (2 * Real.pi))).re|
        ≤ ‖w * expSum N c (u / (2 * Real.pi))‖ := Complex.abs_re_le_norm _
      _ = ‖w‖ * ‖expSum N c (u / (2 * Real.pi))‖ := norm_mul _ _
      _ ≤ ‖z‖ * M := by
          rw [hw, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg z)
  have hlip := abs_sub_genTrigCost_le (a := rotCos N c w) (b := rotSin N c w) hR hbound
    (2 * Real.pi * x) (2 * Real.pi * y)
  rw [genTrigCost_rot_two_pi N hN1 c w x, genTrigCost_rot_two_pi N hN1 c w y] at hlip
  have hdiff : (w * expSum N c x).re - (w * expSum N c y).re = ‖z‖ ^ 2 := by
    rw [← Complex.sub_re, ← mul_sub, ← hz, hw, ← Complex.normSq_eq_conj_mul_self]
    simpa using Complex.normSq_eq_norm_sq z
  have habs : |2 * Real.pi * x - 2 * Real.pi * y| = 2 * Real.pi * |x - y| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [hdiff, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2), habs] at hlip
  have hkey : ‖z‖ * ‖z‖ ≤ ‖z‖ * (2 * Real.pi * ((N - 1 : ℕ) : ℝ) * M * |x - y|) := by
    calc ‖z‖ * ‖z‖ = ‖z‖ ^ 2 := by ring
      _ ≤ ((N - 1 : ℕ) : ℝ) * (‖z‖ * M) * (2 * Real.pi * |x - y|) := hlip
      _ = ‖z‖ * (2 * Real.pi * ((N - 1 : ℕ) : ℝ) * M * |x - y|) := by ring
  exact le_of_mul_le_mul_left hkey hnormz

end RHTower.Sieve
