import GaloisForLFunctions.RHTower.Sieve.DirichletBilinear
import GaloisForLFunctions.RHTower.Sieve.DirichletConvolutionLinear

/-!
# High-block law: smooth head weights reduce to sharp cutoffs (Abel summation + Cauchy–Schwarz)

For a head `a(n) = g(n) h(n)` (`h` the base coefficients, `g` a smooth weight) convolved with a
mollifier `b`, the coefficient energy is bounded by the total variation of `g` squared times the
largest sharp-cutoff energy:

`Σ_r ‖(a ∗ b)(r)‖² ≤ (Σ_{u<L} |g(u) − g(u+1)|)² · sup_{u<L} Σ_r ‖(h·1_{≤u} ∗ b)(r)‖²`.

No arithmetic enters: `g(n) = Σ_{u ≥ n} Δg(u)` (telescoping), the convolution is linear in the head,
and `‖Σ_u Δg(u) z_u‖² ≤ (Σ|Δg|)(Σ|Δg|‖z_u‖²)`. This is what lets every smooth displaced energy of the
high-block law consume one arithmetic input: the sharp-cutoff Barban–Vehov energy, uniformly in the
head length.
-/

open Finset

namespace RHTower

noncomputable section

/-- Linearity of the Dirichlet convolution in a finite sum of left factors. -/
theorem dirConv_sum_left {ι : Type*} (s : Finset ι) (L N : ℕ) (c : ι → ℂ) (a : ι → Fin L → ℂ)
    (b : Fin N → ℂ) (r : Fin (L * N)) :
    Sieve.dirConv L N (fun n => ∑ u ∈ s, c u * a u n) b r =
      ∑ u ∈ s, c u * Sieve.dirConv L N (a u) b r := by
  classical
  unfold Sieve.dirConv
  set S := (Finset.univ : Finset (Fin L × Fin N)).filter
    (fun q => ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1) with hS
  calc ∑ q ∈ S, (∑ u ∈ s, c u * a u q.1) * b q.2
      = ∑ q ∈ S, ∑ u ∈ s, c u * (a u q.1 * b q.2) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => by ring
    _ = ∑ u ∈ s, ∑ q ∈ S, c u * (a u q.1 * b q.2) := Finset.sum_comm
    _ = ∑ u ∈ s, c u * ∑ q ∈ S, a u q.1 * b q.2 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]

/-- Weighted Cauchy–Schwarz: `‖Σ w z‖² ≤ (Σ|w|)(Σ|w|‖z‖²)`. -/
theorem norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (w z : ι → ℂ) :
    ‖∑ u ∈ s, w u * z u‖ ^ 2 ≤ (∑ u ∈ s, ‖w u‖) * ∑ u ∈ s, ‖w u‖ * ‖z u‖ ^ 2 := by
  have h1 : ‖∑ u ∈ s, w u * z u‖ ≤ ∑ u ∈ s, ‖w u‖ * ‖z u‖ := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun u _ => le_of_eq (norm_mul _ _)
  have h2 : (∑ u ∈ s, ‖w u‖ * ‖z u‖) ^ 2 ≤ (∑ u ∈ s, ‖w u‖) * ∑ u ∈ s, ‖w u‖ * ‖z u‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun u => Real.sqrt ‖w u‖)
      (fun u => Real.sqrt ‖w u‖ * ‖z u‖)
    have e1 : ∀ u, Real.sqrt ‖w u‖ * (Real.sqrt ‖w u‖ * ‖z u‖) = ‖w u‖ * ‖z u‖ := fun u => by
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have e2 : ∀ u, Real.sqrt ‖w u‖ ^ 2 = ‖w u‖ := fun u => Real.sq_sqrt (norm_nonneg _)
    have e3 : ∀ u, (Real.sqrt ‖w u‖ * ‖z u‖) ^ 2 = ‖w u‖ * ‖z u‖ ^ 2 := fun u => by
      rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
    simp only [e1, e2, e3] at this
    exact this
  calc ‖∑ u ∈ s, w u * z u‖ ^ 2 ≤ (∑ u ∈ s, ‖w u‖ * ‖z u‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- The sharp head of length `u + 1`: `h(n)` for `n ≤ u`, zero beyond. -/
def sharpHead (h : ℕ → ℂ) (L u : ℕ) : Fin L → ℂ :=
  fun n => if (n : ℕ) ≤ u then h n else 0

/-- Forward difference of the weight, with `g(L) := 0`. -/
def headDiff (g : ℕ → ℂ) (L u : ℕ) : ℂ :=
  g u - (if u + 1 < L then g (u + 1) else 0)

/-- Telescoping: the smooth head is a combination of sharp heads. -/
theorem smooth_head_eq_sum_sharp (g h : ℕ → ℂ) (L : ℕ) (n : Fin L) :
    g n * h n = ∑ u ∈ Finset.range L, headDiff g L u * sharpHead h L u n := by
  classical
  have hfilt : (Finset.range L).filter (fun u => (n : ℕ) ≤ u) = Finset.Ico (n : ℕ) L := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hsum : ∑ u ∈ Finset.range L, headDiff g L u * sharpHead h L u n =
      h n * ∑ u ∈ Finset.Ico (n : ℕ) L, headDiff g L u := by
    rw [Finset.mul_sum, ← hfilt, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [sharpHead]
    split_ifs <;> ring
  rw [hsum]
  have htel : ∑ u ∈ Finset.Ico (n : ℕ) L, headDiff g L u = g n := by
    set G : ℕ → ℂ := fun v => if v < L then g v else 0 with hG
    have hGu : ∀ u ∈ Finset.Ico (n : ℕ) L, headDiff g L u = G u - G (u + 1) := by
      intro u hu
      rw [Finset.mem_Ico] at hu
      simp only [headDiff, hG, if_pos hu.2]
    rw [Finset.sum_congr rfl hGu, Finset.sum_Ico_eq_sum_range]
    have hshift : ∀ k : ℕ, G ((n : ℕ) + k) - G ((n : ℕ) + k + 1) =
        (fun k => G ((n : ℕ) + k)) k - (fun k => G ((n : ℕ) + k)) (k + 1) := by
      intro k
      simp only [Nat.add_assoc]
    rw [Finset.sum_congr rfl fun k _ => hshift k, Finset.sum_range_sub']
    simp only [hG, add_zero, if_pos n.isLt]
    rw [show (n : ℕ) + (L - (n : ℕ)) = L from Nat.add_sub_cancel' n.isLt.le, if_neg (lt_irrefl L),
      sub_zero]
  rw [htel]
  ring

/-- **Smooth-to-sharp energy transfer.** -/
theorem energy_smooth_le_sharp (L N : ℕ) (g h : ℕ → ℂ) (b : Fin N → ℂ) {C : ℝ}
    (hC : ∀ u ∈ Finset.range L,
      ∑ r : Fin (L * N), ‖Sieve.dirConv L N (sharpHead h L u) b r‖ ^ 2 ≤ C) :
    ∑ r : Fin (L * N), ‖Sieve.dirConv L N (fun n => g n * h n) b r‖ ^ 2 ≤
      (∑ u ∈ Finset.range L, ‖headDiff g L u‖) ^ 2 * C := by
  set W := ∑ u ∈ Finset.range L, ‖headDiff g L u‖ with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hconv : ∀ r : Fin (L * N), Sieve.dirConv L N (fun n => g n * h n) b r =
      ∑ u ∈ Finset.range L, headDiff g L u * Sieve.dirConv L N (sharpHead h L u) b r := by
    intro r
    rw [← dirConv_sum_left]
    congr 1
    funext n
    exact smooth_head_eq_sum_sharp g h L n
  calc ∑ r : Fin (L * N), ‖Sieve.dirConv L N (fun n => g n * h n) b r‖ ^ 2
      = ∑ r : Fin (L * N), ‖∑ u ∈ Finset.range L,
          headDiff g L u * Sieve.dirConv L N (sharpHead h L u) b r‖ ^ 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hconv r]
    _ ≤ ∑ r : Fin (L * N), W * ∑ u ∈ Finset.range L,
          ‖headDiff g L u‖ * ‖Sieve.dirConv L N (sharpHead h L u) b r‖ ^ 2 :=
        Finset.sum_le_sum fun r _ => norm_sum_mul_sq_le _ _ _
    _ = W * ∑ u ∈ Finset.range L, ‖headDiff g L u‖ *
          ∑ r : Fin (L * N), ‖Sieve.dirConv L N (sharpHead h L u) b r‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
    _ ≤ W * ∑ u ∈ Finset.range L, ‖headDiff g L u‖ * C := by
        gcongr with u hu
        exact hC u hu
    _ = W ^ 2 * C := by
        rw [← Finset.sum_mul, ← hW]
        ring

end

end RHTower
