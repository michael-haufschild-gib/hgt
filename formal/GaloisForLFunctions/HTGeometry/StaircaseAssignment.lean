import GaloisForLFunctions.HTGeometry.LogScaleDeterminantNonCancellation

/-!
# Staircase assignment problems have a unique optimum

An exponent matrix of separable form `c i − w j` has a totally degenerate assignment problem: every
permutation gives the same total.  The degeneracy is broken exactly by the positions where the
separable value is *not* attained.  If the positions where it *is* attained form a staircase cut out
by a permutation `K` — entry `(i, j)` is separable when `j ≤ K i` and strictly sub-separable when
`j > K i` — then `K` is the unique optimum, because a permutation dominated pointwise by a
permutation equals it.

This is the combinatorial input the perturbed-determinant criterion of
`LogScaleDeterminantNonCancellation` needs: for a gradient matrix whose rows have strictly
decreasing supports, the assignment optimum is unique and the degeneration goes through.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- **A permutation dominated pointwise by a permutation equals it.** -/
theorem perm_eq_of_le {N : ℕ} (σ K : Equiv.Perm (Fin N)) (h : ∀ i, σ i ≤ K i) : σ = K := by
  classical
  have hsum : ∑ i : Fin N, ((σ i : ℕ) : ℕ) = ∑ i : Fin N, ((K i : ℕ) : ℕ) := by
    rw [Equiv.sum_comp σ (fun j : Fin N => (j : ℕ)), Equiv.sum_comp K (fun j : Fin N => (j : ℕ))]
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin N)), (σ i : ℕ) ≤ (K i : ℕ) := fun i _ => h i
  have := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
  refine Equiv.ext fun i => ?_
  exact Fin.ext (this i (Finset.mem_univ i))

/-- **Staircase uniqueness.**  On the staircase the exponent is separable, off it strictly smaller;
the staircase permutation is then the unique maximiser of the assignment total. -/
theorem unique_max_of_staircase {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] {N : ℕ} (b : Fin N → Fin N → G) (c w : Fin N → G)
    (K : Equiv.Perm (Fin N))
    (heq : ∀ i j, j ≤ K i → b i j = c i - w j)
    (hlt : ∀ i j, K i < j → b i j < c i - w j)
    (σ : Equiv.Perm (Fin N)) (hσ : σ ≠ K) :
    ∑ i, b i (σ i) < ∑ i, b i (K i) := by
  classical
  have hsep : ∀ (τ : Equiv.Perm (Fin N)),
      ∑ i, (c i - w (τ i)) = (∑ i, c i) - ∑ j, w j := by
    intro τ
    rw [Finset.sum_sub_distrib, Equiv.sum_comp τ w]
  have hK : ∑ i, b i (K i) = (∑ i, c i) - ∑ j, w j := by
    rw [Finset.sum_congr rfl (fun i _ => heq i (K i) le_rfl)]
    exact hsep K
  have hle : ∀ i, b i (σ i) ≤ c i - w (σ i) := by
    intro i
    rcases le_or_gt (σ i) (K i) with h | h
    · exact (heq i (σ i) h).le
    · exact (hlt i (σ i) h).le
  obtain ⟨i₀, hi₀⟩ : ∃ i, K i < σ i := by
    by_contra hc
    push Not at hc
    exact hσ (perm_eq_of_le σ K fun i => hc i)
  calc ∑ i, b i (σ i)
      < ∑ i, (c i - w (σ i)) :=
        Finset.sum_lt_sum (fun i _ => hle i) ⟨i₀, Finset.mem_univ _, hlt i₀ (σ i₀) hi₀⟩
    _ = (∑ i, c i) - ∑ j, w j := hsep σ
    _ = ∑ i, b i (K i) := hK.symm

/-- **The staircase degeneration criterion.**  A family of matrices whose measured entry exponents
are separable on a staircase and strictly sub-separable off it has a determinant of exactly the
staircase exponent. -/
theorem hasLogScaleExponent_det_of_staircase
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {N : ℕ} (M : α → Matrix (Fin N) (Fin N) ℂ) (a : Fin N → Fin N → ℝ) (c w : Fin N → ℝ)
    (hM : ∀ i k, HasLogScaleExponent l ρ (fun x => M x i k) (a i k))
    (K : Equiv.Perm (Fin N))
    (heq : ∀ i j, j ≤ K i → a j i = c i - w j)
    (hlt : ∀ i j, K i < j → a j i < c i - w j) :
    HasLogScaleExponent l ρ (fun x => (M x).det) (∑ i, a (K i) i) :=
  hasLogScaleExponent_det_of_unique_max hρ M a hM K
    fun σ hσ => unique_max_of_staircase (fun i j => a j i) c w K heq hlt σ hσ

/-- A staircase exponent matrix forces the determinant to be eventually nonzero. -/
theorem det_ne_zero_of_staircase
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {N : ℕ} (M : α → Matrix (Fin N) (Fin N) ℂ) (a : Fin N → Fin N → ℝ) (c w : Fin N → ℝ)
    (hM : ∀ i k, HasLogScaleExponent l ρ (fun x => M x i k) (a i k))
    (K : Equiv.Perm (Fin N))
    (heq : ∀ i j, j ≤ K i → a j i = c i - w j)
    (hlt : ∀ i j, K i < j → a j i < c i - w j) :
    ∀ᶠ x in l, (M x).det ≠ 0 :=
  (hasLogScaleExponent_det_of_staircase hρ M a c w hM K heq hlt).1

end GaloisForLFunctions.HTGeometry
