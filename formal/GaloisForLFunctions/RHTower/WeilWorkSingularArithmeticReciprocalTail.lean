import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSharpReciprocal
import GaloisForLFunctions.HTGeometry.DirichletSeriesBoundedPartialSums

/-!
# Uniform tails of the literal reciprocal

Full Weil positivity controls every twisted reciprocal partial sum. Applying
Abel summation with a real weight first gives bounds on partial sums at a
shifted point with arbitrarily small height loss. A second real shift gives
a tail estimate uniform over every growing vertical interval.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem exists_partial_sum_height_bound {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {α ε : ℝ} (hα : 1 / 2 < α) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (t : ℝ),
      ‖dirichletPartialSum
        (fun n => producerMobius (fun n => if 2 ≤ n then lam n else 0) (n + 1))
        N ((α : ℂ) + t * I)‖ ≤ K * (2 + |t|) ^ ε := by
  let η : ℝ := min ((α - 1 / 2) / 2) ε
  let θ : ℝ := 1 / 2 + η
  have hη : 0 < η := lt_min (by linarith) hε
  have hηε : η ≤ ε := min_le_right _ _
  have hθα : θ < α := by
    have := min_le_left ((α - 1 / 2) / 2) ε
    dsimp [θ, η]
    linarith
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith
  obtain ⟨C, hC, hsum⟩ := exists_sharp_twisted_reciprocal_sum_le hW hη
  let b : ℕ → ℂ := producerMobius (fun n => if 2 ≤ n then lam n else 0)
  let L : ℝ := 1 + ‖(α : ℂ)‖ * ∑' i : ℕ, (i : ℝ) ^ (θ - α - 1)
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  refine ⟨C * 2 ^ θ * L, by positivity, fun N t => ?_⟩
  let a : ℕ → ℂ := fun n => b n * (n : ℂ) ^ (-(t : ℂ) * I)
  have ha0 : a 0 = 0 := by simp [a, b, producerMobius_zero]
  have hA : ∀ n : ℕ, 1 ≤ n →
      ‖BoundedPartialSums.partialSum a (n + 1)‖ ≤
        (C * 2 ^ θ * (2 + |t|) ^ η) * (n : ℝ) ^ θ := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : ((n : ℝ) + 1) ^ θ ≤ (2 * (n : ℝ)) ^ θ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hθ
    calc
      _ ≤ C * ((n : ℝ) + 1) ^ θ * (2 + |t|) ^ η := hsum n t
      _ ≤ C * (2 * (n : ℝ)) ^ θ * (2 + |t|) ^ η :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (by positivity)
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
  have hb := BoundedPartialSums.norm_sum_mul_powNeg_le_of_growth hθ
    (show 0 ≤ C * 2 ^ θ * (2 + |t|) ^ η by positivity) ha0 hA
    (z := (α : ℂ)) hθα (N + 1)
  have heq : (∑ n ∈ Finset.range (N + 1), a n * BoundedPartialSums.powNeg (α : ℂ) n) =
      dirichletPartialSum (fun n => b (n + 1)) N ((α : ℂ) + t * I) := by
    rw [Finset.sum_range_succ', ha0, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [a, BoundedPartialSums.powNeg]
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [mul_assoc, ← Complex.cpow_add _ _ hn]
    push_cast
    congr 2
    ring
  rw [heq] at hb
  change ‖dirichletPartialSum (fun n => b (n + 1)) N ((α : ℂ) + t * I)‖ ≤ _
  calc
    _ ≤ (C * 2 ^ θ * L) * (2 + |t|) ^ η := by
      convert hb using 1
      dsimp [L]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by have := abs_nonneg t; linarith) hηε)
      (by positivity)

/-- The literal holomorphic reciprocal has a uniform ordinary-series tail
with arbitrarily small height loss. No coefficient bound is a premise. -/
theorem exists_reciprocal_uniform_tail {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      ∀ (α ε : ℝ), 1 / 2 < α → 0 < ε →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ (σ : ℝ), α < σ → ∀ (N : ℕ) (t : ℝ),
          ‖G ((σ : ℂ) + t * I) - ∑ n ∈ Finset.Icc 1 N,
            LSeries.term (producerMobius (fun n => if 2 ≤ n then lam n else 0))
              ((σ : ℂ) + t * I) n‖ ≤
            K * (2 + |t|) ^ ε * ((N : ℝ) + 1) ^ (α - σ) := by
  obtain ⟨G, hGd, hGL, -, hconv⟩ := exists_ordinary_reciprocal hW
  refine ⟨G, hGd, hGL, fun α ε hα hε => ?_⟩
  obtain ⟨C, hC, hpartial⟩ := exists_partial_sum_height_bound hW hα hε
  refine ⟨4 * C, by positivity, fun σ hσ N t => ?_⟩
  let b : ℕ → ℂ := producerMobius (fun n => if 2 ≤ n then lam n else 0)
  let s : ℂ := (σ : ℂ) + t * I
  let s₀ : ℂ := (α : ℂ) + t * I
  have hs : 1 / 2 < s.re := by dsimp [s]; simpa using hα.trans hσ
  have hs₀ : s₀.re < s.re := by simpa [s, s₀] using hσ
  have hd : s - s₀ = ((σ - α : ℝ) : ℂ) := by dsimp [s, s₀]; push_cast; ring
  have heq : dirichletSum (fun n => b (n + 1)) s = G s := by
    apply tendsto_nhds_unique (tendsto_dirichletSum (reciprocal_dirichletConvergesAt hW hs))
    simpa only [dirichletPartialSum_eq_sum_term] using hconv s hs
  have hb := norm_dirichletSum_sub_partialSum_le (fun M => hpartial M t) hs₀
    (reciprocal_dirichletConvergesAt hW hs) N
  rw [heq, dirichletPartialSum_eq_sum_term, hd] at hb
  have hn : ‖((σ - α : ℝ) : ℂ)‖ = σ - α := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hσ)]
  rw [hn, Complex.ofReal_re, div_self (ne_of_gt (sub_pos.mpr hσ))] at hb
  simp only [neg_sub] at hb
  convert hb using 1
  ring

end RHTower.WeilSingularArithmetic
