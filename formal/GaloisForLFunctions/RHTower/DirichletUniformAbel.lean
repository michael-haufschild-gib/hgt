import GaloisForLFunctions.RHTower.DirichletHalfPlane
import GaloisForLFunctions.RHTower.DirichletAbscissa
import GaloisForLFunctions.HTGeometry.MultivariableVitali

/-!
# Abel summation is uniform on bounded parts of the half-plane

The corpus already has the pointwise Abel theorem: bounded coefficient partial sums give
convergence of an ordinary Dirichlet series throughout `Re s > 0`.  What the analytic use of that
theorem needs is the *uniform* form, because a locally uniform limit of holomorphic functions is
holomorphic while a pointwise limit need not be.

The block estimate is the pointwise proof run on the segment `[M, N)` instead of `[0, N)`:

```text
‖∑_{M ≤ n < N} a_n (n+1)^{-s}‖  ≤  2C (1 + ‖s‖ / Re s) (M+1)^{-Re s} ,
```

with `C` a bound for the coefficient partial sums.  On a set where `Re s ≥ x > 0` and `‖s‖ ≤ R`
the prefactor is bounded and `(M+1)^{-Re s} ≤ (M+1)^{-x} → 0`, so the partial sums are uniformly
Cauchy there.  Every point of `Re s > 0` has such a neighbourhood, so the convergence is locally
uniform and the sum is holomorphic.

Uniform convergence on a *whole* closed half-plane is false in this generality — the factor `‖s‖`
is unbounded — which is exactly why the abscissa of uniform convergence is a strictly finer
invariant than the abscissa of convergence.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The Abel block estimate: the tail of the partial sums past `M` is uniformly small. -/
theorem norm_dirichletPartialSum_sub_le {a : ℕ → ℂ} {C : ℝ}
    (hC : ∀ N, ‖∑ n ∈ Finset.range N, a n‖ ≤ C) {s : ℂ} (hs : 0 < s.re) {M N : ℕ}
    (hMN : M ≤ N) :
    ‖dirichletPartialSum a N s - dirichletPartialSum a M s‖
      ≤ 2 * C * (1 + ‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := by
  classical
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  set b : ℕ → ℂ := fun i => (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) with hbdef
  have hnormb : ∀ i : ℕ, ‖b i‖ = ((i : ℝ) + 1) ^ (-s.re) := by
    intro i
    rw [hbdef]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _ |>.trans (by simp)
  set K := N - M with hK
  set av : ℕ → ℂ := fun j => a (M + j) with hav
  set bt : ℕ → ℂ := fun j => b (M + j) with hbt
  have hsplit : dirichletPartialSum a N s - dirichletPartialSum a M s
      = ∑ j ∈ Finset.range K, bt j * av j := by
    rw [dirichletPartialSum, dirichletPartialSum,
      ← Finset.sum_Ico_eq_sub (fun n => a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) hMN,
      Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by rw [hbt, hav, hbdef]; ring
  have hÃ : ∀ k : ℕ, ‖∑ j ∈ Finset.range k, av j‖ ≤ 2 * C := by
    intro k
    have heq : ∑ j ∈ Finset.range k, av j
        = (∑ n ∈ Finset.range (M + k), a n) - ∑ n ∈ Finset.range M, a n := by
      rw [← Finset.sum_Ico_eq_sub a (Nat.le_add_right M k), Finset.sum_Ico_eq_sum_range]
      simp [hav]
    rw [heq]
    exact le_trans (norm_sub_le _ _) (by linarith [hC (M + k), hC M])
  have habel := Finset.sum_range_by_parts bt av K
  simp only [smul_eq_mul] at habel
  rw [hsplit, habel]
  have hb1 : ‖bt (K - 1) * ∑ j ∈ Finset.range K, av j‖ ≤ 2 * C * ((M : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul]
    have h1 : ‖bt (K - 1)‖ ≤ ((M : ℝ) + 1) ^ (-s.re) := by
      rw [hbt, hnormb]
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
      push_cast
      have hn : (0 : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    calc ‖bt (K - 1)‖ * ‖∑ j ∈ Finset.range K, av j‖
        ≤ ((M : ℝ) + 1) ^ (-s.re) * (2 * C) :=
          mul_le_mul h1 (hÃ K) (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
      _ = 2 * C * ((M : ℝ) + 1) ^ (-s.re) := by ring
  have hb2 : ‖∑ i ∈ Finset.range (K - 1), (bt (i + 1) - bt i) * ∑ j ∈ Finset.range (i + 1), av j‖
      ≤ 2 * C * (‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range (K - 1),
        ‖(bt (i + 1) - bt i) * ∑ j ∈ Finset.range (i + 1), av j‖
          ≤ (2 * C) * ((‖s‖ / s.re) *
            (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re))) := by
      intro i _
      rw [norm_mul]
      have hincr : ‖bt (i + 1) - bt i‖
          ≤ (‖s‖ / s.re) * (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re)) := by
        rw [norm_sub_rev, hbt, hbdef]
        have hcast1 : ((M + i : ℕ) : ℝ) + 1 = (M : ℝ) + i + 1 := by push_cast; ring
        have hcast2 : ((M + (i + 1) : ℕ) : ℝ) + 1 = (M : ℝ) + i + 2 := by push_cast; ring
        simp only [hcast1, hcast2]
        exact norm_cpow_neg_sub_le hs (by positivity) (by linarith)
      have hnn : (0:ℝ) ≤ (‖s‖ / s.re) *
          (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re)) :=
        le_trans (norm_nonneg _) hincr
      calc ‖bt (i + 1) - bt i‖ * ‖∑ j ∈ Finset.range (i + 1), av j‖
          ≤ ((‖s‖ / s.re) *
              (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re))) * (2 * C) :=
            mul_le_mul hincr (hÃ (i + 1)) (norm_nonneg _) hnn
        _ = (2 * C) * ((‖s‖ / s.re) *
              (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re))) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have htel : ∑ i ∈ Finset.range (K - 1),
        (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re))
        ≤ ((M : ℝ) + 1) ^ (-s.re) := by
      have hf : ∀ i : ℕ, ((M : ℝ) + (i : ℕ) + 2) = ((M : ℝ) + ((i + 1 : ℕ) : ℝ) + 1) := by
        intro i
        push_cast
        ring
      rw [Finset.sum_congr rfl fun i _ => by rw [hf i]]
      rw [Finset.sum_range_sub' (fun i : ℕ => ((M : ℝ) + (i : ℕ) + 1) ^ (-s.re))]
      have : (0:ℝ) ≤ ((M : ℝ) + ((K - 1 : ℕ) : ℝ) + 1) ^ (-s.re) :=
        Real.rpow_nonneg (by positivity) _
      simp only [Nat.cast_zero, add_zero]
      linarith [this]
    have hsnn : (0:ℝ) ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
    have h2C : (0:ℝ) ≤ 2 * C := by linarith
    calc (2 * C) * ((‖s‖ / s.re) * ∑ i ∈ Finset.range (K - 1),
            (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re)))
        ≤ (2 * C) * ((‖s‖ / s.re) * (((M : ℝ) + 1) ^ (-s.re))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htel hsnn) h2C
      _ = 2 * C * (‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := by ring
  calc ‖bt (K - 1) * (∑ j ∈ Finset.range K, av j)
          - ∑ i ∈ Finset.range (K - 1), (bt (i + 1) - bt i) * ∑ j ∈ Finset.range (i + 1), av j‖
      ≤ ‖bt (K - 1) * ∑ j ∈ Finset.range K, av j‖
        + ‖∑ i ∈ Finset.range (K - 1), (bt (i + 1) - bt i) * ∑ j ∈ Finset.range (i + 1), av j‖ :=
        norm_sub_le _ _
    _ ≤ 2 * C * ((M : ℝ) + 1) ^ (-s.re) + 2 * C * (‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := by
        exact add_le_add hb1 hb2
    _ = 2 * C * (1 + ‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := by ring

end GaloisForLFunctions.RHTower

end
