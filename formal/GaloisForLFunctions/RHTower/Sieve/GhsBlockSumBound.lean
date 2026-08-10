import GaloisForLFunctions.RHTower.Sieve.GhsBlockTelescope

/-!
# The vertical integral of the whole outer range is the sum over the blocks

The decomposition of the outer polynomial, integrated.  The modulus of the triple Perron integrand
factors as `‖A‖·‖B‖·‖f‖·x^σ/‖s‖`, and the first factor obeys the triangle inequality along the
partition, so

```text
∫_{|y| ≤ n} ‖L(outer over (a 0, a K])·L(B)·L(g)·x^s/s‖ dy
  ≤ ∑_{k < K} ∫_{|y| ≤ n} ‖L(ghsOuterBlock f N (a k) (a (k+1)))·L(B)·L(g)·x^s/s‖ dy .
```

Each summand is bounded by `ghs_block_perron_bound`, and with the geometric scales of
`GhsScaleSequence` every bound is the same absolute constant times `V·x^σ`, so the total is
`K` times that — and `K ≍ log log N`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The vertical integral splits over the blocks.** -/
theorem integral_norm_perron_triple_sum_blocks_le
    {f g B : ℕ → ℂ} {sB : Finset ℕ} (hB0 : 0 ∉ sB) (hBsupp : ∀ i : ℕ, B i ≠ 0 → i ∈ sB)
    {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x)
    (hgc : Continuous fun t : ℝ => LSeries g ((σ : ℂ) + (t : ℝ) * I))
    {N n : ℕ} {a : ℕ → ℕ} (ha : Monotone a) (K : ℕ) :
    (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
        ‖LSeries (ghsOuterBlock f N (a 0) (a K)) ((σ : ℂ) + (y : ℝ) * I)
          * LSeries B ((σ : ℂ) + (y : ℝ) * I)
          * LSeries g ((σ : ℂ) + (y : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
      ≤ ∑ k ∈ Finset.range K,
          ∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
            ‖LSeries (ghsOuterBlock f N (a k) (a (k + 1))) ((σ : ℂ) + (y : ℝ) * I)
              * LSeries B ((σ : ℂ) + (y : ℝ) * I)
              * LSeries g ((σ : ℂ) + (y : ℝ) * I)
              * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖ := by
  classical
  have hBc : Continuous fun t : ℝ => LSeries B ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hB0 hBsupp σ
  have hkerc : Continuous fun t : ℝ => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ :=
    continuous_perron_kernel_norm hσ
  -- the common tail of the integrand
  set R : ℝ → ℝ := fun y =>
    ‖LSeries B ((σ : ℂ) + (y : ℝ) * I)‖
      * (‖LSeries g ((σ : ℂ) + (y : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (y : ℝ) * I‖)) with hR
  have hRc : Continuous R := hBc.norm.mul (hgc.norm.mul hkerc)
  have hR0 : ∀ y, 0 ≤ R y := fun y => by
    rw [hR]
    have : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
    positivity
  -- the block polynomials, continuous
  have hAc : ∀ A' B' : ℕ, Continuous fun t : ℝ =>
      LSeries (ghsOuterBlock f N A' B') ((σ : ℂ) + (t : ℝ) * I) := by
    intro A' B'
    exact continuous_LSeries_line_of_support (zero_notMem_block A' B')
      (fun i h => ghsOuterBlock_supp h) σ
  -- the integrands as products
  have hsplit : ∀ (A' B' : ℕ) (y : ℝ),
      ‖LSeries (ghsOuterBlock f N A' B') ((σ : ℂ) + (y : ℝ) * I)
        * LSeries B ((σ : ℂ) + (y : ℝ) * I) * LSeries g ((σ : ℂ) + (y : ℝ) * I)
        * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖
      = ‖LSeries (ghsOuterBlock f N A' B') ((σ : ℂ) + (y : ℝ) * I)‖ * R y := by
    intro A' B' y
    rw [norm_perron_triple_integrand hx, hR]
    ring
  have hcong : ∀ A' B' : ℕ,
      (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
        ‖LSeries (ghsOuterBlock f N A' B') ((σ : ℂ) + (y : ℝ) * I)
          * LSeries B ((σ : ℂ) + (y : ℝ) * I) * LSeries g ((σ : ℂ) + (y : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
      = ∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
          ‖LSeries (ghsOuterBlock f N A' B') ((σ : ℂ) + (y : ℝ) * I)‖ * R y := by
    intro A' B'
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun y _ => hsplit A' B' y
  rw [hcong (a 0) (a K)]
  have hcongsum : ∑ k ∈ Finset.range K,
        (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
          ‖LSeries (ghsOuterBlock f N (a k) (a (k + 1))) ((σ : ℂ) + (y : ℝ) * I)
            * LSeries B ((σ : ℂ) + (y : ℝ) * I) * LSeries g ((σ : ℂ) + (y : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
      = ∑ k ∈ Finset.range K,
          ∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
            ‖LSeries (ghsOuterBlock f N (a k) (a (k + 1))) ((σ : ℂ) + (y : ℝ) * I)‖ * R y :=
    Finset.sum_congr rfl fun k _ => hcong (a k) (a (k + 1))
  rw [hcongsum]
  -- swap the finite sum and the integral
  have hint : ∀ k ∈ Finset.range K, IntegrableOn
      (fun y : ℝ => ‖LSeries (ghsOuterBlock f N (a k) (a (k + 1))) ((σ : ℂ) + (y : ℝ) * I)‖ * R y)
      (Set.Icc (-(n : ℝ)) ((n : ℝ))) := fun k _ => ((hAc (a k) (a (k + 1))).norm.mul
        hRc).integrableOn_Icc
  rw [← MeasureTheory.integral_finsetSum _ hint]
  -- the triangle inequality, pointwise
  have hpoint : ∀ y ∈ Set.Icc (-(n : ℝ)) ((n : ℝ)),
      ‖LSeries (ghsOuterBlock f N (a 0) (a K)) ((σ : ℂ) + (y : ℝ) * I)‖ * R y
        ≤ ∑ k ∈ Finset.range K,
            ‖LSeries (ghsOuterBlock f N (a k) (a (k + 1))) ((σ : ℂ) + (y : ℝ) * I)‖ * R y := by
    intro y _
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hR0 y)
    rw [LSeries_ghsOuterBlock_telescope f N ha K σ y]
    exact norm_sum_le _ _
  refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Icc hpoint
  · exact ((hAc (a 0) (a K)).norm.mul hRc).integrableOn_Icc
  · exact MeasureTheory.integrable_finsetSum _ hint

end RHTower.Sieve

end
