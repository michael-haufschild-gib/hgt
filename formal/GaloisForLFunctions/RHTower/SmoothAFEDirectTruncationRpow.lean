import GaloisForLFunctions.RHTower.SmoothAFEDirectTruncation

/-!
# The direct-edge truncation at an arbitrary decay exponent

The Gaussian cutoff of the smooth approximate functional equation decays faster than any power, so
the direct edge is a finite Dirichlet polynomial up to a tail dominated by the `A + 1/2` power, for
**every** `A > 1/2`.

The tree's earlier truncation fixed `A = 1`, which is borderline for the mollified mean square: with
conductor `x ≍ √T` and polynomial length `N ≍ T^(1/2+θ)`, the tail is negligible only when
`A > 1/(4θ) + 1/2`, and `A = 1` suffices only as `θ → 1/2`.  This version leaves `A` free.
-/

open Complex
open RHTower.Sieve

namespace RHTower

noncomputable section

set_option maxHeartbeats 800000 in
/-- **The truncation bound for the direct edge, at an arbitrary decay exponent.**  Brick 14 fixed
the exponent at `1`, which is borderline for the mollified mean square; the Gaussian cutoff decays
at every exponent, so the tail is dominated by the `A + 1/2` power for every `A > 1/2`. -/
theorem exists_norm_smoothAFEDirectSeries_sub_dirPoly_le_rpow {A : ℝ} (hA : 1 / 2 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {x : ℝ}, 0 < x → ∀ (τ : ℝ) (N : ℕ),
      ‖smoothAFEDirectSeries x τ - dirPoly N (afeDirectCoeff x N) (-τ)‖
        ≤ (K * x ^ A) * ∑' i : ℕ, 1 / ((((i + N : ℕ) : ℝ)) + 1) ^ (A + 1 / 2 : ℝ) := by
  have hA0 : (0 : ℝ) < A := by linarith
  obtain ⟨K, hK, hcut⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := A) hA0
  refine ⟨K, hK, ?_⟩
  intro x hx τ N
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (A + 1 / 2 : ℝ)) :=
    summable_smoothAFEZetaMajorant (by linarith)
  have hshift : Summable (fun i : ℕ => 1 / ((((i + N : ℕ) : ℝ)) + 1) ^ (A + 1 / 2 : ℝ)) :=
    (summable_nat_add_iff N).2 hbase
  have hsummable := smoothAFEDirectWeightedSeries_summable hx τ
  have hterm : ∀ n : ℕ,
      ‖((n : ℂ) + 1) ^ (-linePt τ) * smoothAFECutoff (((n : ℝ) + 1) / x)‖
        ≤ (K * x ^ A) * (1 / ((n : ℝ) + 1) ^ (A + 1 / 2 : ℝ)) := by
    intro n
    have hy : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hratio : (0 : ℝ) < ((n : ℝ) + 1) / x := by positivity
    have hb := hcut hratio
    have hrpow : ((((n : ℝ) + 1) / x)) ^ (-A) = x ^ A / ((n : ℝ) + 1) ^ A := by
      rw [Real.rpow_neg hratio.le, Real.div_rpow hy.le hx.le, inv_div]
    rw [hrpow] at hb
    have hconst : ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) * (K * (x ^ A / ((n : ℝ) + 1) ^ A))
        = (K * x ^ A) * (1 / ((n : ℝ) + 1) ^ (A + 1 / 2 : ℝ)) := by
      have hsum : ((n : ℝ) + 1) ^ (A + 1 / 2 : ℝ)
          = ((n : ℝ) + 1) ^ A * ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hy]
      have hA' : (0 : ℝ) < ((n : ℝ) + 1) ^ A := Real.rpow_pos_of_pos hy _
      have hhalf : (0 : ℝ) < ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hy _
      rw [hsum, show ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) = (((n : ℝ) + 1) ^ ((1 : ℝ) / 2))⁻¹ by
        rw [← Real.rpow_neg hy.le]]
      field_simp
    rw [norm_mul, norm_natSucc_cpow_neg_linePt, ← hconst]
    exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hy.le _)
  have hsplit := hsummable.sum_add_tsum_nat_add N
  have hdiff : smoothAFEDirectSeries x τ - dirPoly N (afeDirectCoeff x N) (-τ)
      = ∑' i : ℕ, ((((i + N : ℕ) : ℂ)) + 1) ^ (-linePt τ) *
          smoothAFECutoff (((((i + N : ℕ) : ℝ)) + 1) / x) := by
    rw [smoothAFEDirectSeries, sum_afeDirectCoeff_eq, ← hsplit]
    ring
  rw [hdiff]
  have htailsummable : Summable (fun i : ℕ => ((((i + N : ℕ) : ℂ)) + 1) ^ (-linePt τ) *
      smoothAFECutoff (((((i + N : ℕ) : ℝ)) + 1) / x)) := (summable_nat_add_iff N).2 hsummable
  refine le_trans (norm_tsum_le_tsum_norm (htailsummable.norm)) ?_
  rw [← hshift.tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => hterm (i + N)) (htailsummable.norm)
    (hshift.mul_left (K * x ^ A))

end

end RHTower
