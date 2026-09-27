import GaloisForLFunctions.RHTower.XiCriticalPairSourceReserve

/-!
# Strict improvement of the full phase ceiling by actual critical pairs

Hardy's theorem supplies a new positive critical node beyond every finite
selection. Adding it and its Schwarz partner strictly reduces the exact
residual source. The adaptive gap increases, and every positive-order phase
ceiling strictly decreases at every admissible anchor and heat time.

Strict improvement does not assert that the residual tends to zero or that
the ceiling has crossed the independent positive-energy floor.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

/-- Any finite source selection admits a disjoint actual critical pair with exact positive
charge; the resulting residual is strictly smaller. -/
theorem exists_xiCriticalPair_residual_extension (F : Finset XiZeroCopy) :
    ∃ (γ : ℝ) (q : XiZeroCopy) (E : Finset XiZeroCopy),
      0 < γ ∧ xiSpectralPoint q = (γ : ℂ) ∧ F ⊆ E ∧
      xiCriticalFourthTraceResidual E = xiCriticalFourthTraceResidual F - 2 / γ ^ 4 ∧
      xiCriticalFourthTraceResidual E < xiCriticalFourthTraceResidual F := by
  classical
  let R : ℝ := 1 + ∑ p ∈ F, |(xiSpectralPoint p).re|
  have hR : 0 < R := by
    have hsum : 0 ≤ ∑ p ∈ F, |(xiSpectralPoint p).re| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp only [R]
    linarith only [hsum]
  obtain ⟨γ, hγR, hzero⟩ := exists_Xi_zero_gt R
  have hγ : 0 < γ := hR.trans hγR
  have hXi : XiC (γ : ℂ) = 0 := by rw [XiC_ofReal, hzero]; simp
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy γ).mp hXi
  let qC := xiZeroCopyConjEquiv q
  have hnot (p : {p : XiZeroCopy // |(xiSpectralPoint p).re| = γ}) : p.1 ∉ F := by
    intro hp
    have hsum := Finset.single_le_sum (fun r (_ : r ∈ F) => abs_nonneg (xiSpectralPoint r).re) hp
    rw [p.property] at hsum
    dsimp only [R] at hγR
    linarith only [hsum, hγR]
  have hqnot : q ∉ F := hnot ⟨q, by rw [hq, Complex.ofReal_re, abs_of_pos hγ]⟩
  have hCnot : qC ∉ F := hnot ⟨qC, by
    rw [xiSpectralPoint_copyConj, hq, Complex.neg_re, Complex.conj_re,
      Complex.ofReal_re, abs_neg, abs_of_pos hγ]⟩
  have hne : q ≠ qC := xiZeroCopy_ne_conj q
  let E := insert q (insert qC F)
  have hreserve : xiCriticalFourthTraceReserve E =
      xiCriticalFourthTraceReserve F + 2 / γ ^ 4 := by
    unfold xiCriticalFourthTraceReserve
    dsimp only [E]
    rw [Finset.sum_insert (by simp only [Finset.mem_insert, not_or]; exact ⟨hne, hqnot⟩),
      Finset.sum_insert hCnot]
    rw [show xiFourthTraceCriticalAtom qC = xiFourthTraceCriticalAtom q from
      xiFourthTraceCriticalAtom_conj q, xiFourthTraceCriticalAtom_at_real γ ⟨q, hq⟩]
    ring
  have hresidual : xiCriticalFourthTraceResidual E = xiCriticalFourthTraceResidual F - 2 / γ ^ 4 := by
    unfold xiCriticalFourthTraceResidual
    rw [hreserve]
    ring
  refine ⟨γ, q, E, hγ, hq, ?_, hresidual, ?_⟩
  · exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  · rw [hresidual]
    exact sub_lt_self _ (div_pos (by positivity) (pow_pos hγ _))

/-- No finite critical selection exhausts the full source: another actual critical pair remains. -/
theorem xiCriticalFourthTraceResidual_pos (F : Finset XiZeroCopy) :
    0 < xiCriticalFourthTraceResidual F := by
  obtain ⟨_, _, E, _, _, _, _, hstrict⟩ := exists_xiCriticalPair_residual_extension F
  exact (xiCriticalFourthTraceResidual_nonneg E).trans_lt hstrict

/-- Increasing the exact finite source reserve can only increase the certified phase gap. -/
theorem xiCriticalResidualPhaseGap_monotone : Monotone xiCriticalResidualPhaseGap := by
  intro F E hFE
  apply max_le_max_left
  apply sub_le_sub_right
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left (by positivity)
    (xiCriticalFourthTraceResidual_pos E) (xiCriticalFourthTraceResidual_antitone hFE)

theorem xiGaussianFourthTraceEnvelope_pos (n : ℕ) (s : {s : ℝ // 0 < s}) :
    0 < xiGaussianFourthTraceEnvelope (n + 1) s := by
  have hterm : 0 < ((2 * 0 + 2).factorial : ℝ) * (2 / (s : ℝ)) ^ (2 * 0 + 2) :=
    mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
      (pow_pos (div_pos (by positivity) s.property) _)
  have hsum := Finset.single_le_sum
    (s := Finset.range (n + 1))
    (f := fun j => ((2 * j + 2).factorial : ℝ) * (2 / (s : ℝ)) ^ (2 * j + 2))
    (fun j _ => mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (div_nonneg (by positivity) s.property.le) _))
    (Finset.mem_range.mpr (Nat.zero_lt_succ n))
  exact hterm.trans_le hsum

/-- The explicit complete phase budget is antitone in the finite source selection. -/
theorem xiGaussianResidualPhaseBudget_antitone (N : ℕ)
    (s : {s : ℝ // 0 < s}) (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    Antitone (fun F => xiGaussianResidualPhaseBudget F N s t.1) := by
  intro F E hFE
  have hδ := xiCriticalFourthTraceResidual_antitone hFE
  have hgap := xiCriticalResidualPhaseGap_monotone hFE
  have he : Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap E)) ≤
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left hgap (sub_nonneg.mpr t.property))
  unfold xiGaussianResidualPhaseBudget
  apply mul_le_mul_of_nonneg_right _ (xiGaussianFourthTraceEnvelope_nonneg N s)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hδ (by positivity)) he
    (Real.exp_pos _).le
    (mul_nonneg (by positivity) (xiCriticalFourthTraceResidual_nonneg F))

/-- A single actual critical-pair extension strictly improves every nonempty coefficient
family's whole-phase ceiling, simultaneously at all anchor and later heat times. -/
theorem exists_xiCriticalPair_strict_phaseBudget_improvement (F : Finset XiZeroCopy) :
    ∃ E : Finset XiZeroCopy, F ⊆ E ∧
      ∀ (n : ℕ) (s : {s : ℝ // 0 < s})
        (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}),
        xiGaussianResidualPhaseBudget E (n + 1) s t.1 <
          xiGaussianResidualPhaseBudget F (n + 1) s t.1 := by
  obtain ⟨_, _, E, _, _, hFE, _, hδ⟩ := exists_xiCriticalPair_residual_extension F
  refine ⟨E, hFE, ?_⟩
  intro n s t
  have he : Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap E)) ≤
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left
      (xiCriticalResidualPhaseGap_monotone hFE) (sub_nonneg.mpr t.property))
  have hm : xiCriticalFourthTraceResidual E *
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap E)) <
        xiCriticalFourthTraceResidual F *
          Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) :=
    (mul_le_mul_of_nonneg_left he (xiCriticalFourthTraceResidual_nonneg E)).trans_lt
      (mul_lt_mul_of_pos_right hδ (Real.exp_pos _))
  have h := mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_left hm (by positivity : (0 : ℝ) < 42 / 41))
    (xiGaussianFourthTraceEnvelope_pos n s)
  simpa only [xiGaussianResidualPhaseBudget, mul_assoc] using h

end RHTower
