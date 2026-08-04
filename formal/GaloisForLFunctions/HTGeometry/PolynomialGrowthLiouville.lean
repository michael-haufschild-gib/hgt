import GaloisForLFunctions.HTGeometry.FirstOrderMvPoly
import Mathlib.Analysis.Complex.Liouville

/-!
# Liouville's theorem at polynomial growth

An entire function of polynomial growth has vanishing derivatives above the growth degree.  Cauchy's
estimate on a circle of radius `R` bounds the `n`-th derivative by `n!·M·2^d/R^{n-d}`, which tends to
zero when `n` exceeds `d`.

mathlib carries only the bounded case of Liouville's theorem; this is the polynomial-growth
generalisation, which is what identifies an entire algebraic function as a polynomial.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

/-- **Liouville at polynomial growth.**  If `‖f z‖ ≤ M (1 + ‖z‖)^d` everywhere, every derivative of
order above `d` vanishes identically. -/
theorem iteratedDeriv_eq_zero_of_polynomial_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {M : ℝ} {d n : ℕ}
    (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ M * (1 + ‖z‖) ^ d)
    (hn : d < n) (c : ℂ) : iteratedDeriv n f c = 0 := by
  by_contra hne
  have ht : 0 < ‖iteratedDeriv n f c‖ := norm_pos_iff.mpr hne
  have hM : 0 ≤ M := by
    have h := hgrowth 0
    have h0 : (0 : ℝ) ≤ ‖f 0‖ := norm_nonneg _
    by_contra hcon
    have hpow : (0 : ℝ) < (1 + ‖(0 : ℂ)‖) ^ d := by positivity
    nlinarith [h, h0, hpow, not_le.mp hcon]
  set A : ℝ := (n.factorial : ℝ) * (M * 2 ^ d) with hA
  have hA0 : 0 ≤ A := by positivity
  -- the Cauchy estimate on a large circle
  have hkey : ∀ R : ℝ, 1 + ‖c‖ ≤ R → ‖iteratedDeriv n f c‖ * R ^ (n - d) ≤ A := by
    intro R hR
    have hR0 : 0 < R := by
      have : (0 : ℝ) ≤ ‖c‖ := norm_nonneg _
      linarith
    have hdc : DiffContOnCl ℂ f (ball c R) := hf.diffContOnCl
    have hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ M * 2 ^ d * R ^ d := by
      intro z hz
      have hzc : ‖z - c‖ = R := by simpa [mem_sphere_iff_norm] using hz
      have hzn : ‖z‖ ≤ ‖c‖ + R := by
        calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
          _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
          _ = R + ‖c‖ := by rw [hzc]
          _ = ‖c‖ + R := by ring
      have hbase : 1 + ‖z‖ ≤ 2 * R := by linarith
      have hb0 : (0 : ℝ) ≤ 1 + ‖z‖ := by positivity
      have hpow : (1 + ‖z‖) ^ d ≤ (2 * R) ^ d := pow_le_pow_left₀ hb0 hbase d
      have hstep : M * (1 + ‖z‖) ^ d ≤ M * (2 * R) ^ d :=
        mul_le_mul_of_nonneg_left hpow hM
      have hexp : M * (2 * R) ^ d = M * 2 ^ d * R ^ d := by
        rw [mul_pow]
        ring
      calc ‖f z‖ ≤ M * (1 + ‖z‖) ^ d := hgrowth z
        _ ≤ M * (2 * R) ^ d := hstep
        _ = M * 2 ^ d * R ^ d := hexp
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR0 hdc hC
    have hRd : (0 : ℝ) < R ^ n := pow_pos hR0 n
    have hsplit : R ^ n = R ^ d * R ^ (n - d) := by
      rw [← pow_add]
      congr 1
      omega
    rw [le_div_iff₀ hRd, hsplit] at hcauchy
    have hRd0 : (0 : ℝ) < R ^ d := pow_pos hR0 d
    have hgoal : (‖iteratedDeriv n f c‖ * R ^ (n - d)) * R ^ d ≤ A * R ^ d := by
      have h1 : (‖iteratedDeriv n f c‖ * R ^ (n - d)) * R ^ d
          = ‖iteratedDeriv n f c‖ * (R ^ d * R ^ (n - d)) := by ring
      have h2 : A * R ^ d = (n.factorial : ℝ) * (M * 2 ^ d * R ^ d) := by
        rw [hA]; ring
      rw [h1, h2]
      exact hcauchy
    exact le_of_mul_le_mul_right hgoal hRd0
  -- a large radius contradicts positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 + ‖c‖) (A / ‖iteratedDeriv n f c‖))
  have hR1 : 1 + ‖c‖ ≤ (N : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hRA : A / ‖iteratedDeriv n f c‖ < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hRge1 : (1 : ℝ) ≤ (N : ℝ) := by
    have hc0 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg _
    linarith
  have hpow : (N : ℝ) ≤ (N : ℝ) ^ (n - d) := by
    have h1 : (1 : ℕ) ≤ n - d := by omega
    have h2 := pow_le_pow_right₀ hRge1 h1
    simpa using h2
  have hbound := hkey (N : ℝ) hR1
  rw [div_lt_iff₀ ht] at hRA
  nlinarith [hbound, hRA, hpow, ht]

end GaloisForLFunctions.HTGeometry
