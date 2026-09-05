import GaloisForLFunctions.RHTower.HighBlockDualWeightRightShift
import GaloisForLFunctions.RHTower.HighBlockDirectTail

/-!
# High-block law, brick B8 (dual side): the reflected series beyond `L`

The reflected series of the displaced Gaussian AFE is
`Σ_n χ(s) (n+1)^{s−1} W_{d,τ}((n+1)x)`, `s = ½ − d + iτ`. With the right-shift decay of the dual
weight and `|χ(s)| |χ(s)^{-1}| = 1`, each term is at most
`C (1+|τ|)^{K+½} x^{−(½−d+K)} (n+1)^{−(1+K)}`, so the tail beyond `L` is
`≤ C (1+|τ|)^{K+½} x^{−(½−d+K)} L^{−K}/K`. On a block with `x ≍ √a`, `L = x a^δ`, this is
`a^{¼ + d/2 − Kδ}`: `K` fixed and large makes the dual tail smaller than any power of `a`.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The `n`-th term of the reflected series of the displaced Gaussian AFE. -/
def highBlockDualTerm (d x τ : ℝ) (n : ℕ) : ℂ :=
  (zetaChi (displacedLinePt d τ) * (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)) *
    smoothAFEZetaDisplacedDualWeight d τ ((n + 1 : ℝ) * x)

/-- Pointwise bound on the reflected terms, uniform in `d ∈ (0, ¼]`, `τ`, `x`. -/
theorem exists_norm_highBlockDualTerm_le {K'' : ℕ} (hK'' : 1 ≤ K'') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d x τ : ℝ), 0 < d → d ≤ 1 / 4 → 0 < x → ∀ n : ℕ,
      ‖highBlockDualTerm d x τ n‖ ≤
        C * (1 + |τ|) ^ ((K'' : ℝ) + 1 / 2) * x ^ (-(1 / 2 - d + K'')) *
          ((n + 1 : ℝ)) ^ (-((K'' : ℝ) + 1)) := by
  obtain ⟨C, hC0, hW⟩ := exists_norm_smoothAFEZetaDisplacedDualWeight_le_rightShift hK''
  refine ⟨C, hC0, fun d x τ hd hd4 hx n => ?_⟩
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hstrip := displacedLinePt_mem_openStrip hd (by linarith) τ
  have hχ : zetaChi (displacedLinePt d τ) ≠ 0 :=
    zetaChi_ne_zero_of_mem_openStrip hstrip.1 hstrip.2
  have hcast : ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) := by push_cast; ring
  have hpow : ‖(n + 1 : ℂ) ^ (displacedLinePt d τ - 1)‖ = (n + 1 : ℝ) ^ (-(1 / 2 + d)) := by
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn1]
    congr 1
    rw [Complex.sub_re, displacedLinePt_re, Complex.one_re]
    ring
  have hWn := hW d τ ((n + 1 : ℝ) * x) hd hd4 (by positivity)
  have hprod : ‖zetaChi (displacedLinePt d τ)‖ * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ = 1 := by
    rw [norm_inv]
    exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr hχ)
  set K : ℝ := 1 / 2 - d + K'' with hKdef
  set p : ℝ := (K'' : ℝ) + 1 / 2 with hpdef
  unfold highBlockDualTerm
  rw [norm_mul, norm_mul, hpow]
  calc ‖zetaChi (displacedLinePt d τ)‖ * (n + 1 : ℝ) ^ (-(1 / 2 + d)) *
        ‖smoothAFEZetaDisplacedDualWeight d τ ((n + 1 : ℝ) * x)‖
      ≤ ‖zetaChi (displacedLinePt d τ)‖ * (n + 1 : ℝ) ^ (-(1 / 2 + d)) *
        (C * (1 + |τ|) ^ p * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
          ((n + 1 : ℝ) * x) ^ (-K)) :=
        mul_le_mul_of_nonneg_left hWn (by positivity)
    _ = C * (1 + |τ|) ^ p *
        (‖zetaChi (displacedLinePt d τ)‖ * ‖(zetaChi (displacedLinePt d τ))⁻¹‖) *
        ((n + 1 : ℝ) ^ (-(1 / 2 + d)) * (n + 1 : ℝ) ^ (-K)) * x ^ (-K) := by
        rw [Real.mul_rpow hn1.le hx.le]
        ring
    _ = C * (1 + |τ|) ^ p * x ^ (-K) * (n + 1 : ℝ) ^ (-((K'' : ℝ) + 1)) := by
        rw [hprod, ← Real.rpow_add hn1,
          show -(1 / 2 + d) + -K = -((K'' : ℝ) + 1) by rw [hKdef]; ring]
        ring

/-- **Dual tail beyond `L`.** -/
theorem exists_norm_highBlockDual_tail_le {K'' : ℕ} (hK'' : 1 ≤ K'') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d x τ : ℝ), 0 < d → d ≤ 1 / 4 → 0 < x → ∀ L : ℕ, 1 ≤ L →
      ‖(∑' n : ℕ, highBlockDualTerm d x τ n) -
          ∑ n ∈ Finset.range L, highBlockDualTerm d x τ n‖ ≤
        C * (1 + |τ|) ^ ((K'' : ℝ) + 1 / 2) * x ^ (-(1 / 2 - d + K'')) *
          ((L : ℝ) ^ (-(K'' : ℝ)) / K'') := by
  obtain ⟨C, hC0, hpoint⟩ := exists_norm_highBlockDualTerm_le hK''
  refine ⟨C, hC0, fun d x τ hd hd4 hx L hL => ?_⟩
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  set σ : ℝ := (K'' : ℝ) + 1 with hσ
  have hσ1 : 1 < σ := by rw [hσ]; linarith
  set B : ℝ := C * (1 + |τ|) ^ ((K'' : ℝ) + 1 / 2) * x ^ (-(1 / 2 - d + K'')) with hB
  have hB0 : 0 ≤ B := by positivity
  let f : ℕ → ℂ := fun n => highBlockDualTerm d x τ n
  have hle : ∀ n : ℕ, ‖f n‖ ≤ B * ((n + 1 : ℝ)) ^ (-σ) := fun n =>
    hpoint d x τ hd hd4 hx n
  have hmaj : Summable (fun n : ℕ => B * ((n + 1 : ℝ)) ^ (-σ)) := by
    have hbase := Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)
    have hshift := (summable_nat_add_iff 1).2 hbase
    refine (hshift.congr ?_).mul_left B
    intro n
    push_cast
    ring
  have hnorm : Summable (fun n : ℕ => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hmaj
  have hsum : Summable f := hnorm.of_norm
  have heq : (∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n = ∑' j : ℕ, f (j + L) := by
    rw [← hsum.sum_add_tsum_nat_add L, add_sub_cancel_left]
  show ‖(∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n‖ ≤ _
  rw [heq]
  have hnormTail : Summable (fun j : ℕ => ‖f (j + L)‖) := (summable_nat_add_iff L).2 hnorm
  have hpow : Summable (fun j : ℕ => (((j + L + 1 : ℕ) : ℝ)) ^ (-σ)) := by
    have hbase := Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)
    simpa [Nat.add_assoc] using (summable_nat_add_iff (L + 1)).2 hbase
  calc ‖∑' j : ℕ, f (j + L)‖ ≤ ∑' j : ℕ, ‖f (j + L)‖ := norm_tsum_le_tsum_norm hnormTail
    _ ≤ ∑' j : ℕ, B * (((j + L + 1 : ℕ) : ℝ)) ^ (-σ) := by
        refine hnormTail.tsum_le_tsum (fun j => ?_) (hpow.mul_left _)
        have h2 : (((j + L + 1 : ℕ) : ℝ)) = ((j + L : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [h2]
        exact hle (j + L)
    _ = B * ∑' j : ℕ, (((j + L + 1 : ℕ) : ℝ)) ^ (-σ) := by rw [tsum_mul_left]
    _ ≤ B * ((L : ℝ) ^ (1 - σ) / (σ - 1)) :=
        mul_le_mul_of_nonneg_left (Sieve.tsum_tail_rpow_neg_le hσ1 hL) hB0
    _ = B * ((L : ℝ) ^ (-(K'' : ℝ)) / K'') := by
        rw [hσ, show (1 : ℝ) - ((K'' : ℝ) + 1) = -(K'' : ℝ) by ring,
          show ((K'' : ℝ) + 1) - 1 = (K'' : ℝ) by ring]

end

end RHTower
