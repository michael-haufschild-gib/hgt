import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationConvolution

/-!
# Finite valuation components of a supported Dirichlet exponential

When every nonzero input coefficient is divisible by p, convolution degree r
is supported on multiples of p^r. A valuation-k component therefore uses only
the first k+1 terms of the exponential. No infinite depth limit is exchanged.
-/

open Complex
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower.WeilSingularArithmetic

theorem dirichletConvPow_eq_zero_of_not_pow_dvd {p : ℕ} {f : ℕ → ℂ}
    (hf : ∀ n, ¬p ∣ n → f n = 0) (r n : ℕ) (hn : ¬p ^ r ∣ n) :
    dirichletConvPow f r n = 0 := by
  induction r generalizing n with
  | zero => exact (hn (by simp)).elim
  | succ r ih =>
    rw [dirichletConvPow_succ, LSeries.convolution_def]
    apply Finset.sum_eq_zero
    intro ab hab
    have he := (Nat.mem_divisorsAntidiagonal.mp hab).1
    by_cases ha : p ∣ ab.1
    · have hb : ¬p ^ r ∣ ab.2 := by
        intro hb
        apply hn
        rw [← he]
        obtain ⟨u, hu⟩ := ha
        obtain ⟨v, hv⟩ := hb
        refine ⟨u * v, ?_⟩
        rw [hu, hv, pow_succ]
        ring
      rw [ih ab.2 hb, mul_zero]
    · rw [hf ab.1 ha, zero_mul]

theorem valuationPart_dirichletConvPow_eq_zero {p : ℕ} {f : ℕ → ℂ}
    (hf : ∀ n, ¬p ∣ n → f n = 0) {k r : ℕ} (hkr : k < r) :
    valuationPart p k (dirichletConvPow f r) = 0 := by
  funext n
  by_cases hv : p ^ k ∣ n ∧ ¬p ^ (k + 1) ∣ n
  · have hn : ¬p ^ r ∣ n := by
      intro hn
      exact hv.2 ((Nat.pow_dvd_pow p (by omega : k + 1 ≤ r)).trans hn)
    simp only [valuationPart, valuationMask, if_pos hv, Complex.ofReal_one,
      one_mul, Pi.zero_apply]
    exact dirichletConvPow_eq_zero_of_not_pow_dvd hf r n hn
  · simp [valuationPart, valuationMask, hv]

/-- Each component is a literal finite exponential polynomial. -/
theorem valuationPart_dirichletExp_finite {p : ℕ} {f : ℕ → ℂ}
    (h0 : f 0 = 0) (h1 : f 1 = 0) (hf : ∀ n, ¬p ∣ n → f n = 0) (k : ℕ) :
    valuationPart p k (dirichletExp f) =
      ∑ r ∈ Finset.range (k + 1),
        ((r.factorial : ℂ)⁻¹) • valuationPart p k (dirichletConvPow f r) := by
  funext n
  change (valuationMask p k n : ℂ) * dirichletExp f n = _
  rw [dirichletExp_eq_tsum h0 h1, ← tsum_mul_left]
  have ht (r : ℕ) : (valuationMask p k n : ℂ) *
      (dirichletConvPow f r n / (r.factorial : ℂ)) =
      valuationPart p k (dirichletConvPow f r) n / (r.factorial : ℂ) := by
    unfold valuationPart
    ring
  simp_rw [ht]
  rw [tsum_eq_sum (s := Finset.range (k + 1))]
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun r _ => by ring
  · intro r hr
    have hkr : k < r := by simp only [Finset.mem_range, not_lt] at hr; omega
    rw [valuationPart_dirichletConvPow_eq_zero hf hkr, Pi.zero_apply, zero_div]

end RHTower.WeilSingularArithmetic
