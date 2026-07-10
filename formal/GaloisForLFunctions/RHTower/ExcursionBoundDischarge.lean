import GaloisForLFunctions.RHTower.RelayLedger

/-!
# Finite excursion-bound discharge by absorbing completion

For a finite signed-depth walk, terminal nonpositivity already forces every upcrossing to
reabsorb by the terminal index.  Thus `ExcursionBound` follows with the list length as budget.
Appending the single push that cancels the final algebraic depth constructs that terminal condition
for every finite list and supplies an unconditional, nonvacuous provider for the excursion Prop.
-/

namespace RHTower

noncomputable section

/-- Algebraic push sums respect concatenation. -/
theorem pushSum_append (xs ys : List ℝ) :
    pushSum (xs ++ ys) = pushSum xs + pushSum ys := by
  induction xs with
  | nil => simp [pushSum]
  | cons x xs ih => simp [pushSum, ih, add_assoc]

/-- A finite walk ending on or below the barrier satisfies the excursion bound with budget equal
to its total number of pushes. -/
theorem excursionBound_of_terminal_nonpos {D₀ : ℝ} {pushes : List ℝ}
    (hend : signedDepth D₀ pushes pushes.length ≤ 0) :
    ExcursionBound D₀ pushes pushes.length := by
  intro m hup
  have hm : m + 1 < pushes.length := by
    by_contra hnot
    have hle : pushes.length ≤ m + 1 := Nat.le_of_not_gt hnot
    have heq : signedDepth D₀ pushes (m + 1) =
        signedDepth D₀ pushes pushes.length := by
      simp [signedDepth, List.take_of_length_le hle]
    have hpos := hup.2
    rw [heq] at hpos
    exact (not_lt_of_ge hend) hpos
  refine ⟨pushes.length - (m + 1), by omega, by omega, ?_⟩
  have hidx : m + 1 + (pushes.length - (m + 1)) = pushes.length := by omega
  simpa [hidx] using hend

/-- The unique final push that cancels the current terminal depth. -/
def absorbingPush (D₀ : ℝ) (pushes : List ℝ) : ℝ :=
  -(D₀ + pushSum pushes)

/-- Canonically complete a finite walk by one terminal absorbing push. -/
def absorbingCompletion (D₀ : ℝ) (pushes : List ℝ) : List ℝ :=
  pushes ++ [absorbingPush D₀ pushes]

/-- The canonical absorbing completion ends exactly on the barrier. -/
theorem signedDepth_absorbingCompletion_terminal (D₀ : ℝ) (pushes : List ℝ) :
    signedDepth D₀ (absorbingCompletion D₀ pushes)
      (absorbingCompletion D₀ pushes).length = 0 := by
  rw [signedDepth, List.take_length, depthAfter_eq_add_pushSum]
  rw [absorbingCompletion, pushSum_append]
  simp [absorbingPush, pushSum]

/-- Every finite push list has an unconditional excursion-bound provider after its canonical
one-step absorbing completion. -/
theorem absorbingCompletion_excursionBound (D₀ : ℝ) (pushes : List ℝ) :
    ExcursionBound D₀ (absorbingCompletion D₀ pushes)
      (absorbingCompletion D₀ pushes).length :=
  excursionBound_of_terminal_nonpos
    (signedDepth_absorbingCompletion_terminal D₀ pushes).le

/-- Length-normalized form of the unconditional completed-walk provider. -/
theorem absorbingCompletion_excursionBound_length_succ (D₀ : ℝ) (pushes : List ℝ) :
    ExcursionBound D₀ (absorbingCompletion D₀ pushes) (pushes.length + 1) := by
  simpa [absorbingCompletion] using absorbingCompletion_excursionBound D₀ pushes

/-! ### Consumers with the excursion hypothesis eliminated -/

/-- No positive run in the completed walk exceeds the canonical list-length excursion budget. -/
theorem run_bounded_absorbingCompletion {D₀ : ℝ} {pushes : List ℝ}
    (hD₀ : D₀ ≤ 0) {s e : ℕ} (hse : s ≤ e)
    (hrun : ∀ m, s ≤ m → m ≤ e →
      0 < signedDepth D₀ (absorbingCompletion D₀ pushes) m) :
    e < s + (pushes.length + 1) :=
  run_bounded_of_excursionBound hD₀
    (absorbingCompletion_excursionBound_length_succ D₀ pushes) hse hrun

/-- The completed walk supplies the upcrossing chain with no ephemerality premise. -/
theorem exists_upcross_chain_absorbingCompletion {D₀ : ℝ} {pushes : List ℝ}
    (hD₀ : D₀ ≤ 0) :
    ∀ (k : ℕ) (levels : ℕ → ℕ),
      (∀ i, i < k → levels i + (pushes.length + 1) ≤ levels (i + 1)) →
      (∀ i, i ≤ k → 0 < signedDepth D₀
        (absorbingCompletion D₀ pushes) (levels i)) →
      ∃ u : ℕ → ℕ,
        (∀ i, i ≤ k → UpcrossAt D₀ (absorbingCompletion D₀ pushes) (u i) ∧
          u i < levels i) ∧
        (∀ i j, i < j → j ≤ k → u i < u j) ∧
        (∀ m, u k < m → m ≤ levels k →
          0 < signedDepth D₀ (absorbingCompletion D₀ pushes) m) :=
  exists_upcross_chain hD₀
    (absorbingCompletion_excursionBound_length_succ D₀ pushes)

/-- The completed walk's separated-presence pattern forces the corresponding upcrossing count
without an `ExcursionBound` argument. -/
theorem card_upcross_ge_of_spread_absorbingCompletion
    {D₀ : ℝ} {pushes : List ℝ} {k : ℕ} {levels : ℕ → ℕ}
    [DecidablePred (UpcrossAt D₀ (absorbingCompletion D₀ pushes))]
    (hD₀ : D₀ ≤ 0)
    (hgap : ∀ i, i < k → levels i + (pushes.length + 1) ≤ levels (i + 1))
    (hpres : ∀ i, i ≤ k →
      0 < signedDepth D₀ (absorbingCompletion D₀ pushes) (levels i)) :
    k + 1 ≤ ((Finset.range (levels k)).filter
      (UpcrossAt D₀ (absorbingCompletion D₀ pushes))).card :=
  card_upcross_ge_of_spread hD₀
    (absorbingCompletion_excursionBound_length_succ D₀ pushes) hgap hpres

/-- Upcrossing-budget form for the canonically completed walk, again with no excursion premise. -/
theorem spread_lt_of_upcross_budget_absorbingCompletion
    {D₀ : ℝ} {pushes : List ℝ} {k M R : ℕ} {levels : ℕ → ℕ}
    [DecidablePred (UpcrossAt D₀ (absorbingCompletion D₀ pushes))]
    (hD₀ : D₀ ≤ 0)
    (hgap : ∀ i, i < k → levels i + (pushes.length + 1) ≤ levels (i + 1))
    (hpres : ∀ i, i ≤ k →
      0 < signedDepth D₀ (absorbingCompletion D₀ pushes) (levels i))
    (hM : levels k ≤ M)
    (hbud : ((Finset.range M).filter
      (UpcrossAt D₀ (absorbingCompletion D₀ pushes))).card ≤ R) :
    k < R :=
  spread_lt_of_upcross_budget hD₀
    (absorbingCompletion_excursionBound_length_succ D₀ pushes) hgap hpres hM hbud

end

end RHTower
