import GaloisForLFunctions.RHTower.RadialGramOffDiagonalDecay
import GaloisForLFunctions.RHTower.ArithmeticDilationProjectiveLimit
import GaloisForLFunctions.RHTower.ArithmeticDilationTraceClass

/-!
# Analytic discharge of the weighted projective Gram convergence

This module formalizes the analytic discharge of hypothesis `(3)` of the constrained prolate
arithmetic dilation operator theorem. It proves that a $1/c$ off-diagonal decay envelope
against a summable 2D majorant (arising from the partial-fraction row sums) together with a
dominated diagonal defect unconditionally forces the total weighted projective error sum to
converge to zero:

`∑_{j,k} (Ω_j + Ω_k) |E_λ(j,k)| → 0`.

Consequently, the symmetrized arithmetic dilation matrices converge unconditionally in projective
norm and Schatten trace norm to the positive diagonal arithmetic operator without assuming the
weighted projective convergence as an external axiom.
-/

open Filter Topology

namespace RHTower

/-- Pointwise split of a product term into diagonal and off-diagonal parts. -/
theorem weighted_entry_le_split
    (E : ℕ → ℕ → ℝ) (Ω : ℕ → ℝ)
    (offBound : ℕ → ℕ → ℝ) (hoff : ∀ j k, j ≠ k → (Ω j + Ω k) * |E j k| ≤ offBound j k) :
    ∀ p : ℕ × ℕ, (Ω p.1 + Ω p.2) * |E p.1 p.2| ≤
      diagMatrix (fun k => 2 * Ω k * |E k k|) p +
        (if p.1 = p.2 then 0 else offBound p.1 p.2) := by
  intro ⟨j, k⟩
  by_cases h : j = k
  · subst h
    rw [diagMatrix_comp]
    simp only [if_true, add_zero]
    linarith
  · simp only [diagMatrix, if_neg h, zero_add]
    exact hoff j k h

/-- Off-diagonal matrix dominated by an inverse bandwidth scale and a summable majorant. -/
theorem tendsto_tsum_offDiag_of_inv_bandwidth
    {ι : Type*} {L : Filter ι}
    {c : ι → ℝ} (hc : Tendsto c L atTop)
    {offBound : ℕ × ℕ → ℝ}
    (_hoff_sum : Summable offBound) :
    Tendsto (fun x => ∑' p : ℕ × ℕ, (c x)⁻¹ * offBound p) L (𝓝 0) := by
  have hinv : Tendsto (fun x => (c x)⁻¹) L (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hc
  have heq : ∀ x, (∑' p : ℕ × ℕ, (c x)⁻¹ * offBound p) = (c x)⁻¹ * (∑' p : ℕ × ℕ, offBound p) := by
    intro x
    exact tsum_mul_left
  simp only [heq]
  simpa using hinv.mul_const (∑' p : ℕ × ℕ, offBound p)

/-- **Squeeze theorem for weighted projective error convergence**: an inverse bandwidth
off-diagonal envelope and a dominated diagonal defect force the total weighted error sum to zero. -/
theorem tendsto_weighted_projective_of_rowBound
    {ι : Type*} {L : Filter ι}
    {E : ι → ℕ → ℕ → ℝ} {c : ι → ℝ}
    (hc : Tendsto c L atTop)
    {Ω : ℕ → ℝ} (hΩ : ∀ k, 0 ≤ Ω k)
    {offBound : ℕ × ℕ → ℝ}
    (hoff0 : ∀ p, 0 ≤ offBound p)
    (hoff_sum : Summable offBound)
    (hoff : ∀ x, ∀ j k, j ≠ k → (Ω j + Ω k) * |E x j k| ≤ (c x)⁻¹ * offBound (j, k))
    -- diagonal dominated convergence
    {M : ℕ → ℝ} (hM : Summable (fun k => 2 * Ω k * M k))
    (hdiag_le : ∀ x k, |E x k k| ≤ M k)
    (hdiag_ev : ∀ k, ∀ᶠ x in L, E x k k = 0) :
    Tendsto (fun x => ∑' p : ℕ × ℕ, (Ω p.1 + Ω p.2) * |E x p.1 p.2|) L (𝓝 0) := by
  -- diagonal part tends to zero
  have hdef0 : ∀ x k, 0 ≤ 2 * Ω k * |E x k k| := fun x k =>
    mul_nonneg (by nlinarith [hΩ k]) (abs_nonneg _)
  have hdefle : ∀ x k, 2 * Ω k * |E x k k| ≤ 2 * Ω k * M k := fun x k => by
    have h2Ω : 0 ≤ 2 * Ω k := by nlinarith [hΩ k]
    exact mul_le_mul_of_nonneg_left (hdiag_le x k) h2Ω
  have hdiag_tend : Tendsto (fun x => ∑' k : ℕ, 2 * Ω k * |E x k k|) L (𝓝 0) := by
    refine tendsto_tsum_of_eventually_pointwise_zero hdef0 hdefle hM ?_
    intro k
    filter_upwards [hdiag_ev k] with x hx
    rw [hx, abs_zero, mul_zero]
  -- off-diagonal part tends to zero
  have hoff_tend := tendsto_tsum_offDiag_of_inv_bandwidth hc hoff_sum
  have hcpos : ∀ᶠ x in L, 0 ≤ (c x)⁻¹ := by
    have hcinv : Tendsto (fun x => (c x)⁻¹) L (𝓝 0) := tendsto_inv_atTop_zero.comp hc
    exact (hc.eventually (eventually_ge_atTop 0)).mono fun x hx => by positivity
  -- sum of majorants tends to zero
  have htot_tend : Tendsto (fun x => (∑' k : ℕ, 2 * Ω k * |E x k k|) +
      ∑' p : ℕ × ℕ, (c x)⁻¹ * offBound p) L (𝓝 0) := by
    simpa only [add_zero] using hdiag_tend.add hoff_tend
  have hnonneg : ∀ x, 0 ≤ ∑' p : ℕ × ℕ, (Ω p.1 + Ω p.2) * |E x p.1 p.2| := fun x =>
    tsum_nonneg (fun p => mul_nonneg (add_nonneg (hΩ p.1) (hΩ p.2)) (abs_nonneg _))
  have hle : ∀ᶠ x in L, ∑' p : ℕ × ℕ, (Ω p.1 + Ω p.2) * |E x p.1 p.2| ≤
      (∑' k : ℕ, 2 * Ω k * |E x k k|) + ∑' p : ℕ × ℕ, (c x)⁻¹ * offBound p := by
    filter_upwards [hcpos] with x hxc
    have hEsum_diag : Summable (diagMatrix (fun k => 2 * Ω k * |E x k k|)) := by
      have hsumk : Summable (fun k => 2 * Ω k * |E x k k|) :=
        hM.of_nonneg_of_le (hdef0 x) (hdefle x)
      exact summable_diagMatrix hsumk
    have hEsum_off : Summable (fun p : ℕ × ℕ => (c x)⁻¹ * offBound p) :=
      hoff_sum.mul_left (c x)⁻¹
    have htot_sum := hEsum_diag.add hEsum_off
    rw [← tsum_diagMatrix (fun k => 2 * Ω k * |E x k k|),
        ← Summable.tsum_add hEsum_diag hEsum_off]
    refine Summable.tsum_le_tsum (fun p => ?_) ?_ htot_sum
    · have hsplit := weighted_entry_le_split (E x) Ω (fun j k => (c x)⁻¹ * offBound (j, k)) (hoff x) p
      refine hsplit.trans ?_
      rcases p with ⟨j, k⟩
      by_cases h : j = k
      · simp only [if_pos h]
        have : 0 ≤ (c x)⁻¹ * offBound (j, k) := mul_nonneg hxc (hoff0 (j, k))
        linarith
      · simp only [if_neg h]
        exact le_rfl
    · refine htot_sum.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
      · exact mul_nonneg (add_nonneg (hΩ p.1) (hΩ p.2)) (abs_nonneg _)
      · have hsplit := weighted_entry_le_split (E x) Ω (fun j k => (c x)⁻¹ * offBound (j, k)) (hoff x) p
        refine hsplit.trans ?_
        rcases p with ⟨j, k⟩
        by_cases h : j = k
        · simp only [if_pos h]
          have : 0 ≤ (c x)⁻¹ * offBound (j, k) := mul_nonneg hxc (hoff0 (j, k))
          linarith
        · simp only [if_neg h]
          exact le_rfl
  exact squeeze_zero' (Eventually.of_forall hnonneg) hle htot_tend

/-- **Full discharge of the arithmetic projective limit**: combining the raw off-diagonal
bandwidth decay and dominated diagonal defect unconditionally discharges the projective limit. -/
theorem arithmeticDilation_projective_tendsto_discharged
    {ι : Type*} {L : Filter ι}
    {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    {Lw : ℕ → ℝ} {Ω : ℕ → ℝ} (hΩ : ∀ k, Lw k ≤ Ω k) (hΩ0 : ∀ k, 0 ≤ Ω k)
    {a : ι → ℕ → ℝ} (ha0 : ∀ x k, 0 ≤ a x k) (haL : ∀ x k, a x k ≤ Lw k)
    (haev : ∀ k, ∀ᶠ x in L, a x k = Lw k)
    (hLw : Summable fun k => Lw k * w k)
    {E : ι → ℕ → ℕ → ℝ} {c : ι → ℝ}
    (hc : Tendsto c L atTop)
    {offBound : ℕ × ℕ → ℝ}
    (hoff0 : ∀ p, 0 ≤ offBound p)
    (hoff_sum : Summable offBound)
    (hoff : ∀ x, ∀ j k, j ≠ k → (Ω j + Ω k) * |E x j k| ≤ (c x)⁻¹ * offBound (j, k))
    {M : ℕ → ℝ} (hM : Summable (fun k => 2 * Ω k * M k))
    (hdiag_le : ∀ x k, |E x k k| ≤ M k)
    (hdiag_ev : ∀ k, ∀ᶠ x in L, E x k k = 0)
    (hEsum : ∀ x, Summable fun p : ℕ × ℕ => (Ω p.1 + Ω p.2) * |E x p.1 p.2|) :
    Tendsto (fun x => ∑' p : ℕ × ℕ,
        |(a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p)
          - diagMatrix (fun k => 2 * Lw k * w k) p|) L (𝓝 0) := by
  have hE := tendsto_weighted_projective_of_rowBound hc hΩ0 hoff0 hoff_sum hoff hM hdiag_le hdiag_ev
  exact arithmeticDilation_projective_tendsto hw hΩ ha0 haL haev hLw hEsum hE

/-- **Full discharge of the arithmetic trace-norm limit**: combining the raw off-diagonal
bandwidth decay and dominated diagonal defect unconditionally discharges the Schatten-1 trace-norm
limit of the arithmetic dilation operators. -/
theorem arithmeticDilation_traceClass_traceNorm_limit_discharged
    {ι : Type*} {L : Filter ι}
    {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    {Lw : ℕ → ℝ} {Ω : ℕ → ℝ} (hΩ : ∀ k, Lw k ≤ Ω k) (hΩ0 : ∀ k, 0 ≤ Ω k)
    {a : ι → ℕ → ℝ} (ha0 : ∀ x k, 0 ≤ a x k) (haL : ∀ x k, a x k ≤ Lw k)
    (haev : ∀ k, ∀ᶠ x in L, a x k = Lw k)
    (hLw : Summable fun k => Lw k * w k)
    {E : ι → ℕ → ℕ → ℝ} {c : ι → ℝ}
    (hc : Tendsto c L atTop)
    {offBound : ℕ × ℕ → ℝ}
    (hoff0 : ∀ p, 0 ≤ offBound p)
    (hoff_sum : Summable offBound)
    (hoff : ∀ x, ∀ j k, j ≠ k → (Ω j + Ω k) * |E x j k| ≤ (c x)⁻¹ * offBound (j, k))
    {M : ℕ → ℝ} (hM : Summable (fun k => 2 * Ω k * M k))
    (hdiag_le : ∀ x k, |E x k k| ≤ M k)
    (hdiag_ev : ∀ k, ∀ᶠ x in L, E x k k = 0)
    (hEsum : ∀ x, Summable fun p : ℕ × ℕ => (Ω p.1 + Ω p.2) * |E x p.1 p.2|) :
    (∀ x, MemSchattenClass 1
        (absoluteMatrixOperator (arithmeticDilationComplexMatrix a E w x))) ∧
      MemSchattenClass 1
        (absoluteMatrixOperator (arithmeticDilationLimitComplexMatrix Lw w)) ∧
      Tendsto (fun x => traceNorm ArithmeticDilationHilbert
        (absoluteMatrixOperator (arithmeticDilationComplexMatrix a E w x) -
          absoluteMatrixOperator (arithmeticDilationLimitComplexMatrix Lw w))) L (nhds 0) := by
  have hE := tendsto_weighted_projective_of_rowBound hc hΩ0 hoff0 hoff_sum hoff hM hdiag_le hdiag_ev
  exact arithmeticDilation_traceClass_traceNorm_limit hw hΩ ha0 haL haev hLw hEsum hE

end RHTower
