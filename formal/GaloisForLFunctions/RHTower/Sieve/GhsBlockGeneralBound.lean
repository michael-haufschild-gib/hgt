import GaloisForLFunctions.RHTower.Sieve.GhsSmallPrimeBlock

/-!
# The per-block bound for an arbitrary block

`ghs_block_bound_uniform` is stated at the endpoints of the geometric partition, where the shape
factor is bounded by `ghs_block_shape_le`.  Nothing else in the argument uses the endpoints, so the
same estimate holds for any block once its shape factor is supplied:

```text
∫_{|y| ≤ n} ‖L(blk)·L(ghsInner f M)·L(g)·x^s/s‖ dy ≤ V·x^σ·ghsBlockConstOf σ Γ ,
```

where `Γ` bounds `((log B − log A + C)/log²⌊N/B⌋)·(log M + log 4)` and the plain mass is dominated
at the same scale.  Taking `Γ = (2 + C)(3 + log 4)` recovers the geometric case, since
`ghsBlockConst σ = ghsBlockConstOf σ ((2 + C)(3 + log 4))` by definition.

This is what a partition whose first block has been trimmed needs.  The mean-square estimate asks
every prime of a block to exceed the height, `n² ≤ q`, which the block `(1, N^{1/2}]` of the
geometric partition does not satisfy; replacing it by `(P, N^{1/2}]` and treating `(1, P]` by the
trivial bound of `GhsSmallPrimeBlock` changes the shape factor, and it is exactly the shape factor
that this statement leaves free.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- The block constant at a prescribed shape bound. -/
def ghsBlockConstOf (σ Γ : ℝ) : ℝ :=
  Real.sqrt ((2 * Real.pi) ^ 2 * (7 / σ ^ 2 + 1) * ((5 / 4) * 701) * (2 * 1750 * Γ))

theorem ghsBlockConstOf_nonneg (σ Γ : ℝ) : 0 ≤ ghsBlockConstOf σ Γ := Real.sqrt_nonneg _

/-- At the geometric shape bound the general constant is the one the geometric partition uses. -/
theorem ghsBlockConst_eq (σ : ℝ) :
    ghsBlockConst σ
      = ghsBlockConstOf σ ((2 + mertensBlockGapConst) * (3 + Real.log 4)) := by
  rw [ghsBlockConst, ghsBlockConstOf]

/-- **The per-block bound at an arbitrary block.** -/
theorem ghs_block_bound_general
    {f g : ℕ → ℂ} {n : ℕ} (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {σ x V : ℝ} (hσ : 1 ≤ σ) (hx : 0 < x) (hV : 0 ≤ V)
    (hgc : Continuous fun t : ℝ => LSeries g ((σ : ℂ) + (t : ℝ) * I))
    (hgb : ∀ y : ℝ, |y| ≤ (n : ℝ) → ‖LSeries g ((σ : ℂ) + (y : ℝ) * I)‖ ≤ V)
    {Ab Bb N M : ℕ} (hn : 1 ≤ n) (hA : 1 ≤ Ab) (hAB : Ab ≤ Bb) (hBN : 2 ≤ N / Bb) (hM : 1 ≤ M)
    (hsq : ∀ q ∈ Nat.primesLE Bb \ Nat.primesLE Ab, (n : ℝ) * (n : ℝ) ≤ (q : ℝ))
    (hbig : ∀ q ∈ Nat.primesLE Bb \ Nat.primesLE Ab,
      4 ≤ Real.log ((q : ℝ) * (1 / (n : ℝ))))
    {κplain Γ : ℝ} (hκ0 : 0 ≤ κplain)
    (hplain : ∑ q ∈ Nat.primesLE Bb \ Nat.primesLE Ab,
        ‖ghsOuterBlock f N Ab Bb q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ κplain)
    (hshape : ((Real.log Bb - Real.log Ab + mertensBlockGapConst)
          / (Real.log ((N / Bb : ℕ) : ℝ)) ^ 2) * (Real.log M + Real.log 4) ≤ Γ)
    (hdom : (5 * (n : ℝ) / 4) * κplain * (Real.log M + Real.log 4) ≤ 1750 * Γ) :
    (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
        ‖LSeries (ghsOuterBlock f N Ab Bb) ((σ : ℂ) + (y : ℝ) * I)
          * LSeries (ghsInner f M) ((σ : ℂ) + (y : ℝ) * I)
          * LSeries g ((σ : ℂ) + (y : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
      ≤ V * x ^ σ * ghsBlockConstOf σ Γ := by
  classical
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  refine le_trans (ghs_block_perron_bound hf hσ hx hV hgc hgb hn hA hAB hBN hsq hbig hM
    hplain) ?_
  set W : ℝ := Real.log Bb - Real.log Ab with hWdef
  set S : ℝ := Real.log ((N / Bb : ℕ) : ℝ) with hSdef
  set L : ℝ := Real.log M + Real.log 4 with hLdef
  set γ : ℝ := V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1) with hγdef
  have hA1R : (1 : ℝ) ≤ (Ab : ℝ) := by exact_mod_cast hA
  have hW0 : (0 : ℝ) ≤ W := by
    have hle : (Ab : ℝ) ≤ (Bb : ℝ) := by exact_mod_cast hAB
    rw [hWdef]
    linarith [Real.log_le_log (by linarith) hle]
  have hC0 := mertensBlockGapConst_nonneg
  have hL0 : (0 : ℝ) ≤ L := by
    have : (0 : ℝ) ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
    have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [hLdef]; linarith
  have hγ0 : (0 : ℝ) ≤ γ := by
    rw [hγdef]
    have h1 : (0 : ℝ) ≤ (x ^ σ) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 7 / σ ^ 2 + 1 := by positivity
    positivity
  have hP0 : (0 : ℝ) ≤ 2 * Real.pi
      * ((5 * 700 / 4) * (2 * ((W + mertensBlockGapConst) / S ^ 2))
        + (5 * (n : ℝ) / 4) * κplain) := by
    have hq : (0 : ℝ) ≤ (W + mertensBlockGapConst) / S ^ 2 := by positivity
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hk : (0 : ℝ) ≤ (5 * (n : ℝ) / 4) * κplain := by positivity
    have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    nlinarith [hq, hk, hπ]
  rw [← Real.sqrt_mul hP0, ghsBlockConstOf]
  have hrest : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 * (7 / σ ^ 2 + 1) * ((5 / 4) * 701)
      * (2 * 1750 * Γ) := by
    have hΓ : (0 : ℝ) ≤ Γ := by nlinarith [hshape, hL0, hW0, hC0,
      (by positivity : (0 : ℝ) ≤ (W + mertensBlockGapConst) / S ^ 2)]
    have h7 : (0 : ℝ) ≤ 7 / σ ^ 2 + 1 := by positivity
    positivity
  have hbound : (2 * Real.pi
        * ((5 * 700 / 4) * (2 * ((W + mertensBlockGapConst) / S ^ 2))
          + (5 * (n : ℝ) / 4) * κplain))
      * (γ * (2 * Real.pi * ((5 / 4) * 701 * L)))
      ≤ (V * x ^ σ) ^ 2 * ((2 * Real.pi) ^ 2 * (7 / σ ^ 2 + 1) * ((5 / 4) * 701)
          * (2 * 1750 * Γ)) := by
    have hA0 : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 * γ * ((5 / 4) * 701) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hshape hA0
    have h2 := mul_le_mul_of_nonneg_left hdom hA0
    have hγeq : γ = (V * x ^ σ) ^ 2 * (7 / σ ^ 2 + 1) := by rw [hγdef]; ring
    rw [hγeq] at h1 h2 ⊢
    nlinarith [h1, h2]
  refine le_trans (Real.sqrt_le_sqrt hbound) (le_of_eq ?_)
  rw [Real.sqrt_mul (sq_nonneg (V * x ^ σ)), Real.sqrt_sq (by positivity)]

end RHTower.Sieve

end
