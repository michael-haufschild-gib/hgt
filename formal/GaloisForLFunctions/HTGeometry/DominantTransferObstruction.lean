import GaloisForLFunctions.HTGeometry.NewtonIrrationalPositiveVertex

/-!
# A dominant transfer term obstructs a linear equation

The coefficient recursion of `L F = G` reads

```text
∑_{μ ≤ n} Φ_μ(n − μ) f_{n−μ} = g_n .
```

Suppose the coefficients of the solution have a **regular profile**: a positive sequence `Θ` with

```text
|f_k| ≤ Θ k    for every k ,        δ · Θ k ≤ |f_k|    for infinitely many k .
```

The same `Θ` on both sides is what makes the comparison work; two bounds with different geometric
bases would leave an exponential gap between them.

If one shift `ν` transfers strictly more than all the others together — its term is at least `D n`
while the sum of every other term and of `g_n` is `o(D n)` — then reading the recursion at an `n`
for which `n − ν` realises the lower bound gives `δ · D n ≤ o(D n)`, which is impossible for large
`n`.

Nothing here is specific to any equation: the dominance hypotheses are exactly the two estimates a
Newton polygon with a unique leading vertex provides, and the regular profile is exactly what a
closed modulus formula for the coefficients provides.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

/-- **A dominant transfer term is incompatible with a regular coefficient profile.** -/
theorem false_of_dominant_transfer {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ)
    {F G : PowerSeries ℂ} (hsol : eulerLinearOp B F = G)
    (Θ : ℕ → ℝ) (hup : ∀ k, ‖PowerSeries.coeff k F‖ ≤ Θ k)
    {δ : ℝ} (hδ : 0 < δ)
    {S : Set ℕ} (hS : S.Infinite) (hlow : ∀ k ∈ S, δ * Θ k ≤ ‖PowerSeries.coeff k F‖)
    (ν : ℕ) (D : ℕ → ℝ) (hD : ∀ n, 0 < D n)
    (hdom : ∀ᶠ n in atTop,
      D n ≤ ‖(shiftPolynomial B ν).eval (((n - ν : ℕ) : ℕ) : ℂ)‖ * Θ (n - ν))
    (hrest : Tendsto (fun n : ℕ =>
        (‖PowerSeries.coeff n G‖
          + ∑ μ ∈ (Finset.range (n + 1)).erase ν,
              ‖(shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)) / D n)
      atTop (nhds 0)) :
    False := by
  classical
  -- the recursion, indexed by the shift
  have hrec : ∀ n : ℕ,
      ∑ μ ∈ Finset.range (n + 1),
        (shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ) * PowerSeries.coeff (n - μ) F
        = PowerSeries.coeff n G := by
    intro n
    have h := coeff_eulerLinearOp_range B F n
    rw [hsol] at h
    rw [h]
    have hrefl := Finset.sum_range_reflect
      (fun k : ℕ => (shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F)
      (n + 1)
    rw [← hrefl]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : n + 1 - 1 - k = n - k := by omega
    have h2 : n - (n - k) = k := by omega
    rw [h1, h2]
  -- eventual smallness of everything but the dominant term
  have hev : ∀ᶠ n : ℕ in atTop,
      (‖PowerSeries.coeff n G‖
        + ∑ μ ∈ (Finset.range (n + 1)).erase ν,
            ‖(shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)) / D n < δ := by
    have hmem : {x : ℝ | x < δ} ∈ nhds (0 : ℝ) := gt_mem_nhds hδ
    exact hrest hmem
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hdom
  -- an index at which the lower bound is realised
  obtain ⟨k, hkS, hklarge⟩ := hS.exists_gt (max N₁ N₂ + ν)
  set n : ℕ := k + ν with hn
  have hνn : ν ≤ n := by omega
  have hnk : n - ν = k := by omega
  have hnN₁ : N₁ ≤ n := by omega
  have hnN₂ : N₂ ≤ n := by omega
  -- the dominant term is large
  have hbig : δ * D n
      ≤ ‖(shiftPolynomial B ν).eval (((n - ν : ℕ) : ℕ) : ℂ) * PowerSeries.coeff (n - ν) F‖ := by
    rw [norm_mul, hnk]
    have h1 := hN₂ n hnN₂
    rw [hnk] at h1
    have h2 := hlow k hkS
    have h3 : (0 : ℝ) ≤ ‖(shiftPolynomial B ν).eval ((k : ℕ) : ℂ)‖ := norm_nonneg _
    nlinarith [h1, h2, h3, hup k]
  -- but the recursion bounds it by the rest
  have hsmall : ‖(shiftPolynomial B ν).eval (((n - ν : ℕ) : ℕ) : ℂ) * PowerSeries.coeff (n - ν) F‖
      ≤ ‖PowerSeries.coeff n G‖
        + ∑ μ ∈ (Finset.range (n + 1)).erase ν,
            ‖(shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ) := by
    have hmem : ν ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hsplit := Finset.add_sum_erase (Finset.range (n + 1))
      (fun μ : ℕ => (shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ)
        * PowerSeries.coeff (n - μ) F) hmem
    have hval := hrec n
    rw [← hsplit] at hval
    have heq : (shiftPolynomial B ν).eval (((n - ν : ℕ) : ℕ) : ℂ) * PowerSeries.coeff (n - ν) F
        = PowerSeries.coeff n G
          - ∑ μ ∈ (Finset.range (n + 1)).erase ν,
              (shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ) * PowerSeries.coeff (n - μ) F := by
      linear_combination hval
    rw [heq]
    refine le_trans (norm_sub_le _ _) ?_
    refine add_le_add le_rfl ?_
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun μ _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hup (n - μ)) (norm_nonneg _)
  -- the two are incompatible
  have hquot := hN₁ n hnN₁
  rw [div_lt_iff₀ (hD n)] at hquot
  linarith [hbig, hsmall, hquot]

end GaloisForLFunctions.HTGeometry
