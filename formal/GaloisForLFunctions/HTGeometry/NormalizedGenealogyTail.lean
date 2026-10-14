import GaloisForLFunctions.HTGeometry.NormalizedGenealogyGram

/-! # Head removal and completed tail inversion for genealogy Grams

The recurrence can be read from either end. Removing the first coefficient gives
an exact identity that survives completion and recovers that coefficient from
three consecutive tail values.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology

def genealogyTail (w : ℕ → ℂ) (k : ℕ) : ℕ → ℂ := fun n => w (n + k)

@[simp] theorem genealogyTail_zero (w : ℕ → ℂ) : genealogyTail w 0 = w := rfl

@[simp] theorem genealogyTail_tail (w : ℕ → ℂ) (k j : ℕ) :
    genealogyTail (genealogyTail w k) j = genealogyTail w (j + k) := by
  funext n
  simp only [genealogyTail, Nat.add_assoc]

theorem finiteGenealogyGramValue_head (w : ℕ → ℂ) (N : ℕ) :
    finiteGenealogyGramValue w (N + 2) =
      (2 + ‖w 0‖ ^ 2) * finiteGenealogyGramValue (genealogyTail w 1) (N + 1) -
        ‖w 0‖ ^ 2 * finiteGenealogyGramValue (genealogyTail w 2) N := by
  induction N using Nat.twoStepInduction with
  | zero => norm_num [finiteGenealogyGramValue, genealogyTail]; ring
  | one => norm_num [finiteGenealogyGramValue, genealogyTail]; ring
  | more N hN hN1 =>
      rw [finiteGenealogyGramValue_succ_succ w (N + 2), hN1, hN,
        finiteGenealogyGramValue_succ_succ (genealogyTail w 1) (N + 1),
        finiteGenealogyGramValue_succ_succ (genealogyTail w 2) N]
      simp only [genealogyTail, Nat.add_assoc]
      ring

theorem normalizedGenealogyGram_head (w : ℕ → ℂ) (N : ℕ) :
    normalizedGenealogyGram w (N + 2) =
      normalizedGenealogyGram (genealogyTail w 1) (N + 1) + ‖w 0‖ ^ 2 / 4 *
        (2 * normalizedGenealogyGram (genealogyTail w 1) (N + 1) -
          normalizedGenealogyGram (genealogyTail w 2) N) := by
  simp only [normalizedGenealogyGram, finiteGenealogyGramValue_head, pow_succ]
  field_simp
  ring

theorem normalizedGenealogyGram_tail_le (w : ℕ → ℂ) (N : ℕ) :
    normalizedGenealogyGram (genealogyTail w 1) N ≤ normalizedGenealogyGram w (N + 1) := by
  induction N generalizing w with
  | zero => simp
  | succ N ih =>
      have h := ih (genealogyTail w 1)
      simp only [genealogyTail_tail] at h
      have h1 := one_le_normalizedGenealogyGram (genealogyTail w 1) (N + 1)
      have hp := mul_nonneg (sq_nonneg ‖w 0‖)
        (show 0 ≤ 2 * normalizedGenealogyGram (genealogyTail w 1) (N + 1) -
          normalizedGenealogyGram (genealogyTail w 2) N by linarith)
      rw [normalizedGenealogyGram_head]
      nlinarith

theorem genealogyTail_summable_iff (w : ℕ → ℂ) (k : ℕ) :
    Summable (fun n => ‖genealogyTail w k n‖ ^ 2) ↔ Summable (fun n => ‖w n‖ ^ 2) := by
  exact summable_nat_add_iff (f := fun n => ‖w n‖ ^ 2) k

def normalizedGenealogyTailValue (w : ℕ → ℂ) (k : ℕ) : ℝ :=
  ⨆ N, normalizedGenealogyGram (genealogyTail w k) N

theorem tendsto_normalizedGenealogyTailValue (w : ℕ → ℂ)
    (hs : Summable (fun n => ‖w n‖ ^ 2)) (k : ℕ) :
    Tendsto (normalizedGenealogyGram (genealogyTail w k)) atTop
      (𝓝 (normalizedGenealogyTailValue w k)) :=
  tendsto_atTop_ciSup (normalizedGenealogyGram_monotone _) <|
    (normalizedGenealogyGram_bddAbove_iff _).mpr ((genealogyTail_summable_iff w k).mpr hs)

theorem one_le_normalizedGenealogyTailValue (w : ℕ → ℂ)
    (hs : Summable (fun n => ‖w n‖ ^ 2)) (k : ℕ) :
    1 ≤ normalizedGenealogyTailValue w k := by
  have hb := (normalizedGenealogyGram_bddAbove_iff _).mpr ((genealogyTail_summable_iff w k).mpr hs)
  simpa only [normalizedGenealogyGram_zero, normalizedGenealogyTailValue] using le_ciSup hb 0

theorem normalizedGenealogyTailValue_step_le (w : ℕ → ℂ)
    (hs : Summable (fun n => ‖w n‖ ^ 2)) (k : ℕ) :
    normalizedGenealogyTailValue w (k + 1) ≤ normalizedGenealogyTailValue w k := by
  apply le_of_tendsto_of_tendsto' (tendsto_normalizedGenealogyTailValue w hs (k + 1))
    ((tendsto_add_atTop_iff_nat 1).mpr (tendsto_normalizedGenealogyTailValue w hs k))
  intro N
  simpa only [genealogyTail_tail, Nat.add_comm 1 k] using
    normalizedGenealogyGram_tail_le (genealogyTail w k) N

theorem normalizedGenealogyTailValue_recurrence (w : ℕ → ℂ)
    (hs : Summable (fun n => ‖w n‖ ^ 2)) (k : ℕ) :
    normalizedGenealogyTailValue w k = normalizedGenealogyTailValue w (k + 1) +
      ‖w k‖ ^ 2 / 4 * (2 * normalizedGenealogyTailValue w (k + 1) -
        normalizedGenealogyTailValue w (k + 2)) := by
  have h0 := (tendsto_add_atTop_iff_nat 2).mpr (tendsto_normalizedGenealogyTailValue w hs k)
  have h1 := (tendsto_add_atTop_iff_nat 1).mpr (tendsto_normalizedGenealogyTailValue w hs (k + 1))
  have h2 := tendsto_normalizedGenealogyTailValue w hs (k + 2)
  have he (N : ℕ) : normalizedGenealogyGram (genealogyTail w k) (N + 2) =
      normalizedGenealogyGram (genealogyTail w (k + 1)) (N + 1) +
        ‖w k‖ ^ 2 / 4 * (2 * normalizedGenealogyGram (genealogyTail w (k + 1)) (N + 1) -
          normalizedGenealogyGram (genealogyTail w (k + 2)) N) := by
    simpa only [genealogyTail_tail, Nat.add_comm 1 k, Nat.add_comm 2 k,
      genealogyTail, Nat.zero_add] using normalizedGenealogyGram_head (genealogyTail w k) N
  apply tendsto_nhds_unique h0
  exact Filter.Tendsto.congr (fun N => (he N).symm)
    (h1.add (((h1.const_mul 2).sub h2).const_mul (‖w k‖ ^ 2 / 4)))

theorem normalizedGenealogyTailValue_denominator (w : ℕ → ℂ)
    (hs : Summable (fun n => ‖w n‖ ^ 2)) (k : ℕ) :
    1 ≤ 2 * normalizedGenealogyTailValue w (k + 1) - normalizedGenealogyTailValue w (k + 2) := by
  have h := normalizedGenealogyTailValue_step_le w hs (k + 1)
  have h1 := one_le_normalizedGenealogyTailValue w hs (k + 1)
  linarith

theorem normalizedGenealogyTailValue_recovers_norm_sq (w : ℕ → ℂ)
    (hs : Summable (fun n => ‖w n‖ ^ 2)) (k : ℕ) :
    ‖w k‖ ^ 2 = 4 * (normalizedGenealogyTailValue w k - normalizedGenealogyTailValue w (k + 1)) /
      (2 * normalizedGenealogyTailValue w (k + 1) - normalizedGenealogyTailValue w (k + 2)) := by
  have hd := normalizedGenealogyTailValue_denominator w hs k
  apply (eq_div_iff (by linarith)).mpr
  have h := normalizedGenealogyTailValue_recurrence w hs k
  linarith

theorem normalizedGenealogyTailValue_energy_upper (w : ℕ → ℂ)
    (hs : Summable (fun n => ‖w n‖ ^ 2)) (k : ℕ) :
    normalizedGenealogyTailValue w k ≤ Real.exp ((∑' n, ‖w (n + k)‖ ^ 2) / 2) := by
  apply ciSup_le
  intro N
  cases N with
  | zero => rw [normalizedGenealogyGram_zero]; exact Real.one_le_exp (by positivity)
  | succ N =>
      apply (normalizedGenealogyGram_energy_upper _ N).trans
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right
        (((genealogyTail_summable_iff w k).mpr hs).sum_le_tsum (Finset.range N)
          (fun n _ => sq_nonneg _)) (by norm_num)

theorem normalizedGenealogyTailValue_tendsto_one (w : ℕ → ℂ)
    (hs : Summable (fun n => ‖w n‖ ^ 2)) :
    Tendsto (normalizedGenealogyTailValue w) atTop (𝓝 1) := by
  have ht : Tendsto (fun k => Real.exp ((∑' n, ‖w (n + k)‖ ^ 2) / 2)) atTop (𝓝 1) := by
    simpa only [zero_div, Real.exp_zero, Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_sum_nat_add (fun n => ‖w n‖ ^ 2)).div_const 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (one_le_normalizedGenealogyTailValue w hs) (normalizedGenealogyTailValue_energy_upper w hs)

theorem normalizedGenealogyTailValue_eq_iff (w v : ℕ → ℂ)
    (hw : Summable (fun n => ‖w n‖ ^ 2)) (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    (∀ k, normalizedGenealogyTailValue w k = normalizedGenealogyTailValue v k) ↔
      ∀ k, ‖w k‖ = ‖v k‖ := by
  constructor
  · intro h k
    have hsq : ‖w k‖ ^ 2 = ‖v k‖ ^ 2 := by
      rw [normalizedGenealogyTailValue_recovers_norm_sq w hw k,
        normalizedGenealogyTailValue_recovers_norm_sq v hv k, h k, h (k + 1), h (k + 2)]
    nlinarith [norm_nonneg (w k), norm_nonneg (v k)]
  · intro h k
    apply congrArg (fun f : ℕ → ℝ => ⨆ N, f N)
    funext N
    rw [normalizedGenealogyGram, normalizedGenealogyGram]
    congr 1
    exact (finiteGenealogyGramValue_eq_iff _ _).mpr (fun n => h (n + k)) N

end
end GaloisForLFunctions.HTGeometry
