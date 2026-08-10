import GaloisForLFunctions.RHTower.Sieve.HalaszCellAggregateLine

/-!
# The triple Perron integral against the cell aggregate

The two joints compose.  Regrouping the Cauchy–Schwarz puts the long factor with the inner prime
polynomial; the cell decomposition then charges the long factor cell by cell:

```text
∫_b^{b+m} ‖A·B·f·x^s/s‖ dy
  ≤ √(∫_b^{b+m} ‖A‖²) · √( (∑_{k<m} ‖f(σ+iv_k)‖²·x^{2σ}/‖σ+iv_k‖²) · 2π·(prime cell mass of B) ) ,
```

with `v_k` a maximiser on the `k`-th unit cell.  The long factor no longer appears through a
supremum over the whole range: it appears through the aggregate, which is the quantity Halász's
`(1+m)e^{-m}` is made of.  The kernel `1/‖σ+iy‖²` damps the far cells, so the aggregate does not
grow with the length of the range — unlike `sup‖f‖ × length`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The triple Perron integral, bounded by the cell aggregate of the long factor.** -/
theorem exists_cell_bound_integral_norm_perron_triple
    {A B f : ℕ → ℂ} {sA sB : Finset ℕ}
    (hA0 : 0 ∉ sA) (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ sA)
    (hsB : ∀ n ∈ sB, n.Prime) (hB0 : 0 ∉ sB) (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ sB)
    {σ x b : ℝ} (hσ : 0 < σ) (hx : 0 < x)
    (hFc : Continuous fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℝ) * I)) (m : ℕ) :
    ∃ v : ℕ → ℝ,
      (∀ k, k < m → v k ∈ Set.Icc (b + (k : ℝ) * 1) (b + ((k : ℝ) + 1) * 1))
      ∧ (∫ y in Set.Icc b (b + (m : ℝ) * 1),
            ‖LSeries A ((σ : ℂ) + (y : ℝ) * I) * LSeries B ((σ : ℂ) + (y : ℝ) * I)
              * LSeries f ((σ : ℂ) + (y : ℝ) * I)
              * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
          ≤ Real.sqrt (∫ y in Set.Icc b (b + (m : ℝ) * 1),
                ‖LSeries A ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
            * Real.sqrt ((∑ k ∈ Finset.range m,
                  (‖LSeries f ((σ : ℂ) + (v k : ℝ) * I)‖
                    * (x ^ σ / ‖(σ : ℂ) + (v k : ℝ) * I‖)) ^ 2)
                * (2 * Real.pi
                    * primeCellMass (fun n => B n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) sB)) := by
  classical
  set E : ℝ → ℝ := fun y =>
    (‖LSeries f ((σ : ℂ) + (y : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (y : ℝ) * I‖)) ^ 2 with hE
  have hEc : Continuous E := ((hFc.norm.mul (continuous_perron_kernel_norm hσ)).pow 2)
  have hE0 : ∀ t : ℝ, 0 ≤ E t := fun t => by rw [hE]; positivity
  obtain ⟨v, hvmem, hvle⟩ :=
    exists_cell_aggregate_normSq_LSeries_le hsB hB0 hBsupp hEc hE0 σ b m
  refine ⟨v, hvmem, ?_⟩
  have hbm : b ≤ b + (m : ℝ) * 1 := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  -- the second Cauchy–Schwarz factor is the cell integral
  have hrewrite : (∫ y in Set.Icc b (b + (m : ℝ) * 1),
        (‖LSeries B ((σ : ℂ) + (y : ℝ) * I)‖ * ‖LSeries f ((σ : ℂ) + (y : ℝ) * I)‖
          * (x ^ σ / ‖(σ : ℂ) + (y : ℝ) * I‖)) ^ 2)
      = ∫ y in b..(b + (m : ℝ) * 1), E y * ‖LSeries B ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hbm, MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    rw [hE]
    ring
  have hcs := integral_Icc_norm_perron_triple_regrouped_le (A := A) (B := B) (f := f)
    hA0 hAsupp hB0 hBsupp (σ := σ) (x := x) (c := b) (d := b + (m : ℝ) * 1) hσ hx hFc
  refine le_trans hcs ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine Real.sqrt_le_sqrt ?_
  rw [hrewrite]
  exact hvle

end RHTower.Sieve

end
