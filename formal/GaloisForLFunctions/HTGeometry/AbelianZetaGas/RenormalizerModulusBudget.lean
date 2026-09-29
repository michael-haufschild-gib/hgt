import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleCondensedCentralLimit
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModulusBudget

/-!
# Every renormalizer pays the modulus budget

Let `φ_p(t) = Γ_{q_p}(1 + it)` and let `(r_p)` be any family of complex renormalizers such that
`∏_{p ≤ P} φ_p(t) r_p(t)` converges to a nonzero limit `ψ(t)`.  Since
`|∏ φ_p r_p| = e^{-Δ_P(t)} ∏ |r_p|`, the logarithm of the renormalizer modulus differs from the
defect `Δ_P(t) = ∑_{p ≤ P} -log|φ_p(t)|` by `log|∏ φ_p r_p| → log|ψ(t)|`.  Hence
`∏_{p ≤ P} |r_p(t)| = exp(Δ_P(t) + O(1))`.
-/

open Filter
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem norm_qGammaOn_eq_exp_neg_primeDefect (q : RealEulerNome) (t : ℝ) :
    ‖qGammaOn q (1 + (t : ℂ) * Complex.I)‖ = Real.exp (-primeDefect q t) := by
  rw [primeDefect, neg_neg, Real.exp_log (norm_qGammaOn_pos q t)]

/-- `|∏_{p ≤ P} φ_p r_p| = e^{-Δ_P} ∏_{p ≤ P} |r_p|`. -/
theorem norm_prod_renormalized {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (r : Nat.Primes → ℂ) (P : ℕ) :
    ‖∏ p ∈ primeCutoff P, (qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I) * r p)‖
      = Real.exp (-∑ p ∈ primeCutoff P, primeDefect (primeNome hσ p) t)
        * ∏ p ∈ primeCutoff P, ‖r p‖ := by
  rw [norm_prod, ← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [norm_mul, norm_qGammaOn_eq_exp_neg_primeDefect]

/-- **Theorem 2.2, item 2 (GAS3.3).**  If `∏_{p ≤ P} φ_p(t) r_p(t) → ψ ≠ 0`, then
`log ∏_{p ≤ P} |r_p(t)| - Δ_P(t) → log|ψ|`. -/
theorem tendsto_log_renormalizer_sub_defect {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (r : Nat.Primes → ℂ)
    {ψ : ℂ} (hψ : ψ ≠ 0)
    (hconv : Tendsto (fun P : ℕ => ∏ p ∈ primeCutoff P,
      (qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I) * r p)) atTop (𝓝 ψ)) :
    Tendsto (fun P : ℕ => Real.log (∏ p ∈ primeCutoff P, ‖r p‖)
      - ∑ p ∈ primeCutoff P, primeDefect (primeNome hσ p) t) atTop (𝓝 (Real.log ‖ψ‖)) := by
  have hnorm := (continuous_norm.tendsto ψ).comp hconv
  have hψ0 : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hlog := (Real.continuousAt_log hψ0.ne').tendsto.comp hnorm
  refine hlog.congr' ?_
  filter_upwards [hnorm.eventually (lt_mem_nhds hψ0)] with P hP
  simp only [Function.comp_apply] at hP ⊢
  rw [norm_prod_renormalized] at hP ⊢
  have hprod : 0 < ∏ p ∈ primeCutoff P, ‖r p‖ := by
    have hexp := Real.exp_pos (-∑ p ∈ primeCutoff P, primeDefect (primeNome hσ p) t)
    have hnn : 0 ≤ ∏ p ∈ primeCutoff P, ‖r p‖ := Finset.prod_nonneg fun p _ => norm_nonneg _
    rcases hnn.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hP
      exact absurd hP (by linarith)
  rw [Real.log_mul (Real.exp_pos _).ne' hprod.ne', Real.log_exp]
  ring

/-- **(GAS3.3).**  The renormalizer modulus is `exp(Δ_P + O(1))`. -/
theorem exists_bound_log_renormalizer_sub_defect {σ : ℝ} (hσ : 0 < σ) (t : ℝ)
    (r : Nat.Primes → ℂ) {ψ : ℂ} (hψ : ψ ≠ 0)
    (hconv : Tendsto (fun P : ℕ => ∏ p ∈ primeCutoff P,
      (qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I) * r p)) atTop (𝓝 ψ)) :
    ∃ C : ℝ, ∀ᶠ P : ℕ in atTop, |Real.log (∏ p ∈ primeCutoff P, ‖r p‖)
      - ∑ p ∈ primeCutoff P, primeDefect (primeNome hσ p) t| ≤ C := by
  have h := tendsto_log_renormalizer_sub_defect hσ t r hψ hconv
  refine ⟨|Real.log ‖ψ‖| + 1, ?_⟩
  filter_upwards [(h.eventually (Metric.ball_mem_nhds _ one_pos))] with P hP
  rw [Real.dist_eq] at hP
  have := abs_sub_abs_le_abs_sub (Real.log (∏ p ∈ primeCutoff P, ‖r p‖)
    - ∑ p ∈ primeCutoff P, primeDefect (primeNome hσ p) t) (Real.log ‖ψ‖)
  linarith

end GaloisForLFunctions.HTGeometry
