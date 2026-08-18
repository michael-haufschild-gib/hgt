import GaloisForLFunctions.RHTower.ZetaLineAFESplit
import GaloisForLFunctions.RHTower.HardyZSmoothAFEReal
import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds
import GaloisForLFunctions.RHTower.Sieve.DirichletMVTWindow

/-!
# Truncating the direct Dirichlet edge

The Gaussian cutoff decays faster than any power, so the direct edge of the smooth approximate
functional equation is a finite Dirichlet polynomial up to an absolutely summable tail.  This is
what lets the tree's mean value theorem be applied to it.
-/

open Complex
open RHTower.Sieve

noncomputable section

namespace RHTower

/-- The coefficients of the truncated direct edge. -/
def afeDirectCoeff (x : ℝ) (N : ℕ) : Fin N → ℂ := fun n =>
  (((Real.sqrt (((n : ℕ) : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
    smoothAFECutoff (((((n : ℕ) : ℝ) + 1)) / x)

theorem afeDirectTerm_eq (x : ℝ) (n : ℕ) (τ : ℝ) :
    ((n : ℂ) + 1) ^ (-linePt τ) * smoothAFECutoff (((n : ℝ) + 1) / x)
      = ((((Real.sqrt ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
          smoothAFECutoff (((n : ℝ) + 1) / x)) *
        Complex.exp (((-τ * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((((n : ℝ) + 1 : ℝ)) : ℂ) = ((n : ℂ) + 1) := by push_cast; ring
  have h := cpow_neg_linePt τ hpos
  rw [hcast] at h
  rw [h]
  have hphase : Complex.exp (-I * ((τ * Real.log ((n : ℝ) + 1) : ℝ) : ℂ))
      = Complex.exp (((-τ * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

theorem sum_afeDirectCoeff_eq (x : ℝ) (N : ℕ) (τ : ℝ) :
    dirPoly N (afeDirectCoeff x N) (-τ)
      = ∑ n ∈ Finset.range N,
          ((n : ℂ) + 1) ^ (-linePt τ) * smoothAFECutoff (((n : ℝ) + 1) / x) := by
  rw [dirPoly]
  simp only [afeDirectCoeff]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ((((Real.sqrt ((i : ℝ) + 1))⁻¹ : ℝ) : ℂ) * smoothAFECutoff (((i : ℝ) + 1) / x)) *
      Complex.exp (((-τ * Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * Complex.I)) N]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [afeDirectTerm_eq x n τ]

set_option maxHeartbeats 1600000 in
/-- **The truncation bound for the direct edge.**  The tail beyond `N` is dominated by the
`3/2`-power tail, uniformly in the height. -/
theorem exists_norm_smoothAFEDirectSeries_sub_dirPoly_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {x : ℝ}, 0 < x → ∀ (τ : ℝ) (N : ℕ),
      ‖smoothAFEDirectSeries x τ - dirPoly N (afeDirectCoeff x N) (-τ)‖
        ≤ (K * x) * ∑' i : ℕ, 1 / ((((i + N : ℕ) : ℝ)) + 1) ^ (3 / 2 : ℝ) := by
  obtain ⟨K, hK, hcut⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := (1 : ℝ)) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro x hx τ N
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) :=
    summable_smoothAFEZetaMajorant (by norm_num)
  have hshift : Summable (fun i : ℕ => 1 / ((((i + N : ℕ) : ℝ)) + 1) ^ (3 / 2 : ℝ)) :=
    (summable_nat_add_iff N).2 hbase
  have hsummable := smoothAFEDirectWeightedSeries_summable hx τ
  have hterm : ∀ n : ℕ,
      ‖((n : ℂ) + 1) ^ (-linePt τ) * smoothAFECutoff (((n : ℝ) + 1) / x)‖
        ≤ (K * x) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
    intro n
    have hy : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hratio : (0 : ℝ) < ((n : ℝ) + 1) / x := by positivity
    have hb := hcut hratio
    have hrpow : ((((n : ℝ) + 1) / x)) ^ (-(1 : ℝ)) = x / ((n : ℝ) + 1) := by
      rw [Real.rpow_neg_one, inv_div]
    rw [hrpow] at hb
    have hconst : ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) * (K * (x / ((n : ℝ) + 1)))
        = (K * x) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
      have h1 : ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) = (((n : ℝ) + 1) ^ ((1 : ℝ) / 2))⁻¹ := by
        rw [← Real.rpow_neg hy.le]
      have h2 : ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) * ((n : ℝ) + 1)
          = ((n : ℝ) + 1) ^ ((3 : ℝ) / 2) := by
        nth_rewrite 2 [← Real.rpow_one ((n : ℝ) + 1)]
        rw [← Real.rpow_add hy]
        norm_num
      have hhalf : (0 : ℝ) < ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hy _
      rw [h1, ← h2]
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
    (hshift.mul_left (K * x))

end RHTower

end
