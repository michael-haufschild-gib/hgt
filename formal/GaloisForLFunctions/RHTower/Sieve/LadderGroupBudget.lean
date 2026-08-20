import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The ladder groups of the two-range budget, majorised

Both halves of `Sieve/MoebiusTwoRangeWindow.integral_Icc_normSq_logPoly_moebius_le_twoRange`
present the same arithmetic shape: a block count `B j`, a cofactor length `N j`, a cofactor
cardinality `C j ≤ N j + 1`, and a threshold `θ` (or a zero-free-region saving `ρ`).  What the
budget needs from them is only three aggregate quantities:

```text
   S    ≥ ∑_j B j · N j      (the harmonic mass times the length of the sum)
   Bmax ≥ B j                (the largest block)
   PP   ≥ ∑_j B j            (the total number of designated primes)
```

and then every group is a polynomial in `S`, `Bmax`, `PP`, `L`, `θ`, `W`.  Isolating that here
keeps the arithmetic away from the analytic layers, where it would be repeated twice.
-/

namespace RHTower.Sieve

noncomputable section

/-- **The mean-value ladder group.**  `∑_j (θ·B j)²·(5π/2·W + 5e/2·N j)·C j`, majorised by the
three aggregates. -/
theorem ladderGroup_mvt_le {L : ℕ} {W θ S Bmax PP : ℝ} (B Cc Nn : ℕ → ℝ)
    (hW : 0 ≤ W) (hBmax : 0 ≤ Bmax)
    (hB : ∀ j, 0 ≤ B j) (hNn : ∀ j, 0 ≤ Nn j) (_hC0 : ∀ j, 0 ≤ Cc j)
    (hCN : ∀ j ∈ Finset.range L, Cc j ≤ Nn j + 1)
    (hmax : ∀ j ∈ Finset.range L, B j ≤ Bmax)
    (hS : ∑ j ∈ Finset.range L, B j * Nn j ≤ S) (_hS0 : 0 ≤ S)
    (hPP : ∑ j ∈ Finset.range L, B j ≤ PP) :
    2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (θ * B j) ^ 2 * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * Nn j) * Cc j)
      ≤ 5 * Real.pi * (L : ℝ) * θ ^ 2 * W * (Bmax * S + Bmax * PP)
        + 5 * Real.exp 1 * (L : ℝ) * θ ^ 2 * (S ^ 2 + Bmax * S) := by
  classical
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hθ2 : (0 : ℝ) ≤ θ ^ 2 := sq_nonneg θ
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  -- the three aggregate bounds
  have hBN2 : ∑ j ∈ Finset.range L, (B j * Nn j) ^ 2 ≤ S ^ 2 := by
    refine le_trans (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => mul_nonneg (hB j) (hNn j))) ?_
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => mul_nonneg (hB j) (hNn j)) hS 2
  have hB2N : ∑ j ∈ Finset.range L, B j ^ 2 * Nn j ≤ Bmax * S := by
    have hstep : ∑ j ∈ Finset.range L, B j ^ 2 * Nn j
        ≤ ∑ j ∈ Finset.range L, Bmax * (B j * Nn j) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have h1 : B j ^ 2 * Nn j = B j * (B j * Nn j) := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (hmax j hj) (mul_nonneg (hB j) (hNn j))
    refine hstep.trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hS hBmax
  have hB2 : ∑ j ∈ Finset.range L, B j ^ 2 ≤ Bmax * PP := by
    have hstep : ∑ j ∈ Finset.range L, B j ^ 2 ≤ ∑ j ∈ Finset.range L, Bmax * B j := by
      refine Finset.sum_le_sum fun j hj => ?_
      have h1 : B j ^ 2 = B j * B j := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (hmax j hj) (hB j)
    refine hstep.trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hPP hBmax
  -- the per-term majorant
  have hterm : ∀ j ∈ Finset.range L,
      (θ * B j) ^ 2 * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * Nn j) * Cc j)
        ≤ θ ^ 2 * ((5 * Real.pi / 2 * W) * (B j ^ 2 * Nn j + B j ^ 2)
            + (5 * Real.exp 1 / 2) * ((B j * Nn j) ^ 2 + B j ^ 2 * Nn j)) := by
    intro j hj
    have hCle : Cc j ≤ Nn j + 1 := hCN j hj
    have hcoef : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * Nn j := by
      have := hNn j
      positivity
    have hstep : (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * Nn j) * Cc j
        ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * Nn j) * (Nn j + 1) :=
      mul_le_mul_of_nonneg_left hCle hcoef
    have hsq : (θ * B j) ^ 2 = θ ^ 2 * B j ^ 2 := by ring
    rw [hsq]
    have hmul := mul_le_mul_of_nonneg_left hstep
      (mul_nonneg hθ2 (sq_nonneg (B j)) : (0 : ℝ) ≤ θ ^ 2 * B j ^ 2)
    refine hmul.trans (le_of_eq ?_)
    ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)) ?_
  rw [← Finset.mul_sum]
  have hexp : ∑ j ∈ Finset.range L,
      ((5 * Real.pi / 2 * W) * (B j ^ 2 * Nn j + B j ^ 2)
        + (5 * Real.exp 1 / 2) * ((B j * Nn j) ^ 2 + B j ^ 2 * Nn j))
      = (5 * Real.pi / 2 * W) * ((∑ j ∈ Finset.range L, B j ^ 2 * Nn j)
            + ∑ j ∈ Finset.range L, B j ^ 2)
        + (5 * Real.exp 1 / 2) * ((∑ j ∈ Finset.range L, (B j * Nn j) ^ 2)
            + ∑ j ∈ Finset.range L, B j ^ 2 * Nn j) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
  rw [hexp]
  have hA : (5 * Real.pi / 2 * W) * ((∑ j ∈ Finset.range L, B j ^ 2 * Nn j)
        + ∑ j ∈ Finset.range L, B j ^ 2)
      ≤ (5 * Real.pi / 2 * W) * (Bmax * S + Bmax * PP) :=
    mul_le_mul_of_nonneg_left (by linarith [hB2N, hB2]) (by positivity)
  have hBexp : (5 * Real.exp 1 / 2) * ((∑ j ∈ Finset.range L, (B j * Nn j) ^ 2)
        + ∑ j ∈ Finset.range L, B j ^ 2 * Nn j)
      ≤ (5 * Real.exp 1 / 2) * (S ^ 2 + Bmax * S) :=
    mul_le_mul_of_nonneg_left (by linarith [hBN2, hB2N]) (by positivity)
  have hfinal : (2 : ℝ) * (L : ℝ) * (θ ^ 2 * ((5 * Real.pi / 2 * W) * (Bmax * S + Bmax * PP)
        + (5 * Real.exp 1 / 2) * (S ^ 2 + Bmax * S)))
      = 5 * Real.pi * (L : ℝ) * θ ^ 2 * W * (Bmax * S + Bmax * PP)
        + 5 * Real.exp 1 * (L : ℝ) * θ ^ 2 * (S ^ 2 + Bmax * S) := by ring
  have hmul2 : (2 : ℝ) * (L : ℝ) * (θ ^ 2 * ((5 * Real.pi / 2 * W)
          * ((∑ j ∈ Finset.range L, B j ^ 2 * Nn j) + ∑ j ∈ Finset.range L, B j ^ 2)
        + (5 * Real.exp 1 / 2) * ((∑ j ∈ Finset.range L, (B j * Nn j) ^ 2)
            + ∑ j ∈ Finset.range L, B j ^ 2 * Nn j)))
      ≤ (2 : ℝ) * (L : ℝ) * (θ ^ 2 * ((5 * Real.pi / 2 * W) * (Bmax * S + Bmax * PP)
          + (5 * Real.exp 1 / 2) * (S ^ 2 + Bmax * S))) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith [hA, hBexp]) hθ2)
      (by positivity)
  linarith [hmul2, hfinal]

/-- **The Halász–Montgomery ladder group.**  Same three aggregates, with the kernel's far constant
and the logarithmic diagonal factored out. -/
theorem ladderGroup_hm_inner_le {L : ℕ} {ρ S Bmax PP FCmax v Λ : ℝ} (B Cc Nn FC : ℕ → ℝ)
    (hBmax : 0 ≤ Bmax) (hB : ∀ j, 0 ≤ B j) (hNn : ∀ j, 0 ≤ Nn j) (hC0 : ∀ j, 0 ≤ Cc j)
    (hCN : ∀ j ∈ Finset.range L, Cc j ≤ Nn j + 1)
    (hmax : ∀ j ∈ Finset.range L, B j ≤ Bmax)
    (hFC : ∀ j ∈ Finset.range L, FC j ≤ FCmax) (hFC0 : 0 ≤ FCmax)
    (hv : 0 ≤ v) (hΛ : 0 ≤ Λ)
    (hS : ∑ j ∈ Finset.range L, B j * Nn j ≤ S)
    (hPP : ∑ j ∈ Finset.range L, B j ≤ PP) :
    ∑ j ∈ Finset.range L,
        (ρ * B j) ^ 2 * ((2 * Nn j + FC j * v + 48 * Real.pi * Nn j * Λ) * Cc j)
      ≤ ρ ^ 2 * ((2 + 48 * Real.pi * Λ) * (S ^ 2 + Bmax * S)
          + FCmax * v * (Bmax * S + Bmax * PP)) := by
  classical
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hρ2 : (0 : ℝ) ≤ ρ ^ 2 := sq_nonneg ρ
  have hBN2 : ∑ j ∈ Finset.range L, (B j * Nn j) ^ 2 ≤ S ^ 2 := by
    refine le_trans (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => mul_nonneg (hB j) (hNn j))) ?_
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => mul_nonneg (hB j) (hNn j)) hS 2
  have hB2N : ∑ j ∈ Finset.range L, B j ^ 2 * Nn j ≤ Bmax * S := by
    have hstep : ∑ j ∈ Finset.range L, B j ^ 2 * Nn j
        ≤ ∑ j ∈ Finset.range L, Bmax * (B j * Nn j) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have h1 : B j ^ 2 * Nn j = B j * (B j * Nn j) := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (hmax j hj) (mul_nonneg (hB j) (hNn j))
    refine hstep.trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hS hBmax
  have hB2 : ∑ j ∈ Finset.range L, B j ^ 2 ≤ Bmax * PP := by
    have hstep : ∑ j ∈ Finset.range L, B j ^ 2 ≤ ∑ j ∈ Finset.range L, Bmax * B j := by
      refine Finset.sum_le_sum fun j hj => ?_
      have h1 : B j ^ 2 = B j * B j := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (hmax j hj) (hB j)
    refine hstep.trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hPP hBmax
  have hterm : ∀ j ∈ Finset.range L,
      (ρ * B j) ^ 2 * ((2 * Nn j + FC j * v + 48 * Real.pi * Nn j * Λ) * Cc j)
        ≤ ρ ^ 2 * ((2 + 48 * Real.pi * Λ) * ((B j * Nn j) ^ 2 + B j ^ 2 * Nn j)
            + FCmax * v * (B j ^ 2 * Nn j + B j ^ 2)) := by
    intro j hj
    have hCle : Cc j ≤ Nn j + 1 := hCN j hj
    have hFCle : FC j ≤ FCmax := hFC j hj
    have hNj := hNn j
    have hcoef : (2 : ℝ) * Nn j + FC j * v + 48 * Real.pi * Nn j * Λ
        ≤ (2 + 48 * Real.pi * Λ) * Nn j + FCmax * v := by
      nlinarith [mul_le_mul_of_nonneg_right hFCle hv]
    have hcoef0 : (0 : ℝ) ≤ (2 + 48 * Real.pi * Λ) * Nn j + FCmax * v := by positivity
    have hCC : (0 : ℝ) ≤ Cc j := hC0 j
    have hstep : (2 * Nn j + FC j * v + 48 * Real.pi * Nn j * Λ) * Cc j
        ≤ ((2 + 48 * Real.pi * Λ) * Nn j + FCmax * v) * (Nn j + 1) := by
      refine le_trans (mul_le_mul_of_nonneg_right hcoef hCC) ?_
      exact mul_le_mul_of_nonneg_left hCle hcoef0
    have hsq : (ρ * B j) ^ 2 = ρ ^ 2 * B j ^ 2 := by ring
    rw [hsq]
    have hmul := mul_le_mul_of_nonneg_left hstep
      (mul_nonneg hρ2 (sq_nonneg (B j)) : (0 : ℝ) ≤ ρ ^ 2 * B j ^ 2)
    refine hmul.trans (le_of_eq ?_)
    ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hexp : ∑ j ∈ Finset.range L,
      ((2 + 48 * Real.pi * Λ) * ((B j * Nn j) ^ 2 + B j ^ 2 * Nn j)
        + FCmax * v * (B j ^ 2 * Nn j + B j ^ 2))
      = (2 + 48 * Real.pi * Λ) * ((∑ j ∈ Finset.range L, (B j * Nn j) ^ 2)
            + ∑ j ∈ Finset.range L, B j ^ 2 * Nn j)
        + FCmax * v * ((∑ j ∈ Finset.range L, B j ^ 2 * Nn j)
            + ∑ j ∈ Finset.range L, B j ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
  rw [hexp]
  have hA : (2 + 48 * Real.pi * Λ) * ((∑ j ∈ Finset.range L, (B j * Nn j) ^ 2)
        + ∑ j ∈ Finset.range L, B j ^ 2 * Nn j)
      ≤ (2 + 48 * Real.pi * Λ) * (S ^ 2 + Bmax * S) :=
    mul_le_mul_of_nonneg_left (by linarith [hBN2, hB2N]) (by positivity)
  have hBb : FCmax * v * ((∑ j ∈ Finset.range L, B j ^ 2 * Nn j)
        + ∑ j ∈ Finset.range L, B j ^ 2)
      ≤ FCmax * v * (Bmax * S + Bmax * PP) :=
    mul_le_mul_of_nonneg_left (by linarith [hB2N, hB2]) (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith [hA, hBb]) hρ2

end

end RHTower.Sieve
