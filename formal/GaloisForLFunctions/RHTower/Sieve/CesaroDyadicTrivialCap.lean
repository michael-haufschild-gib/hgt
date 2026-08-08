import GaloisForLFunctions.RHTower.Sieve.CesaroDyadicMeanSquare

/-!
# The unconditional Cesàro chain is capped at the trivial bound too

The analytic side of `norm_sum_Icc_mul_log_div_le_cesaro_dyadic` is
`8x^σ√(5πe(1 + log N)) + 12x^σ√(5π)`, and the arithmetic side is `∑_{n ≤ N}E(σ,T,x/n)`: neither mentions
the coefficient sequence.  The bound is therefore subject to the same instantiation argument as the GHS
master bound (`ghs-prime-saving-master-bound-is-trivial.md`).  Taking `f ≡ 1` and `x = N`, the left side
is `∑_{n ≤ N}log(N/n)`, which is at least `⌊N/2⌋·log 2` because every `n ≤ N/2` contributes at least
`log 2`.  Hence

`⌊N/2⌋·log 2 ≤ ∑_{n ≤ N}E(σ,T,N/n) + (1/2π)(8N^σ√(5πe(1 + log N)) + 12N^σ√(5π))`,

so the chain can never assert `‖∑_{n ≤ N}f(n)log(N/n)‖ = o(N)` for any `f`.

This is not a defect of the mean-square estimate — which is sharp, and strictly better than both the
pointwise Euler bound and the damped bound — but of the architecture: `Q` and `κ` are built from `‖a_n‖`,
so the analytic side is blind to the signs, and `|μ(n)| = |1(n)|` on the squarefree integers.  The
`√(log N)` improvements recorded in the companion card are improvements *within* a capped family.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The logarithmic weight has full mass.**  Every `n ≤ N/2` contributes at least `log 2`. -/
theorem sum_Icc_log_div_ge {N : ℕ} :
    ((N / 2 : ℕ) : ℝ) * Real.log 2 ≤ ∑ n ∈ Finset.Icc 1 N, Real.log ((N : ℝ) / n) := by
  classical
  have hsub : Finset.Icc 1 (N / 2) ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, by omega⟩
  have hnn : ∀ n ∈ Finset.Icc 1 N, n ∉ Finset.Icc 1 (N / 2) →
      0 ≤ Real.log ((N : ℝ) / n) := by
    intro n hn _
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
    have h0 : (0 : ℝ) < (n : ℝ) := by linarith
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ h0]
    linarith
  have hlow : ∀ n ∈ Finset.Icc 1 (N / 2), Real.log 2 ≤ Real.log ((N : ℝ) / n) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have h0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hle : 2 * n ≤ N := by omega
    have hleR : 2 * (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ h0]
    linarith
  calc ((N / 2 : ℕ) : ℝ) * Real.log 2
      = ∑ _n ∈ Finset.Icc 1 (N / 2), Real.log 2 := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num
    _ ≤ ∑ n ∈ Finset.Icc 1 (N / 2), Real.log ((N : ℝ) / n) := Finset.sum_le_sum hlow
    _ ≤ ∑ n ∈ Finset.Icc 1 N, Real.log ((N : ℝ) / n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnn

/-- **The unconditional chain is at least the trivial bound.**  Instantiating at the constant sequence
`1` and `x = N`. -/
theorem trivial_le_cesaro_dyadic_bound {N : ℕ} (hN : 1 ≤ N) {σ T : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hT : 1 ≤ T) :
    ((N / 2 : ℕ) : ℝ) * Real.log 2
      ≤ (∑ n ∈ Finset.Icc 1 N, cesaroError σ T ((N : ℝ) / n))
        + (1 / (2 * Real.pi))
          * (8 * (N : ℝ) ^ σ * Real.sqrt (5 * Real.pi * Real.exp 1 * (1 + Real.log N))
            + 12 * (N : ℝ) ^ σ * Real.sqrt (5 * Real.pi)) := by
  classical
  have hone := norm_sum_Icc_mul_log_div_le_cesaro_dyadic (f := fun _ => (1 : ℂ))
    (fun n => by norm_num) hN hσ1 hσ2 hT (le_refl ((N : ℝ)))
  have hcoeff : ∀ n ∈ Finset.Icc 1 N,
      truncSeq (fun _ => (1 : ℂ)) N n * ((Real.log ((N : ℝ) / n) : ℝ) : ℂ)
        = ((Real.log ((N : ℝ) / n) : ℝ) : ℂ) := by
    intro n hn
    rw [truncSeq, if_pos hn, one_mul]
  rw [Finset.sum_congr rfl hcoeff] at hone
  have hsum : (∑ n ∈ Finset.Icc 1 N, ((Real.log ((N : ℝ) / n) : ℝ) : ℂ))
      = ((∑ n ∈ Finset.Icc 1 N, Real.log ((N : ℝ) / n) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at hone
  have hnn : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, Real.log ((N : ℝ) / n) := by
    refine Finset.sum_nonneg fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < (n : ℝ))]
    linarith
  rw [abs_of_nonneg hnn] at hone
  exact le_trans sum_Icc_log_div_ge hone

end RHTower.Sieve
end
