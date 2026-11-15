import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheBestDoublingFactorOfTheMarginIsTwoToTheWidth
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis
import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime

/-!
# The loss of the margin is bounded or polynomial

A level law (`IsLevelLaw ρ a`) bounds the loss of the margin at the ratio `K`: the neutral part of
every window `(ρ(K), (3K + 1)ρ(K)]` plus `a(K)` has at most one negative square. Along block sizes
`K¹⁰ ≤ ρ(K) ≤ K^A`:

* **Bounded loss is the line** (`riemannHypothesis_iff_exists_const_isLevelLaw`): RH iff a constant
  level works (MAFT: RH iff the margins of all windows are bounded below).
* **Exponent zero is bounded loss** (`riemannHypothesis_iff_forall_marginLaw_pos`): RH iff the margin
  law holds at every rate `β > 0`.
* **Factor one is bounded loss** (`riemannHypothesis_iff_doublingLaw_one`): RH iff some doubling law
  `a(2K) ≤ a(K) + c` holds. Such a law allows the cumulative loss `c log₂ K`, and still forces the
  line.
* **No intermediate growth** (`exists_const_isLevelLaw_or_exists_not_marginLaw`): either a constant
  level works or the margin law fails at some rate `β > 0`. Least levels growing like `log K`, or
  like any `K^{o(1)}`, are bounded.

A stage recursion of the margin reaches the line as soon as its loss exponent is zero: no summable
additive loss is needed beyond a factor one.
-/

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  riemannHypothesis_iff_zetaZeroWidth_eq_zero)

variable {ρ : ℕ → ℕ}

/-- A margin law of rate `β` is one of every rate `β' ≥ β`: `C K^β ≤ max(C, 0) K^{β'}` for `K ≥ 1`. -/
theorem MarginLaw.mono_rate {β β' : ℝ} (h : MarginLaw ρ β) (hββ' : β ≤ β') : MarginLaw ρ β' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, IsLevelLaw.mono (a := fun K => C * (K : ℝ) ^ β) hC fun K hK => ?_⟩
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : (K : ℝ) ^ β ≤ (K : ℝ) ^ β' := Real.rpow_le_rpow_of_exponent_le hK1 hββ'
  have h2 : (0 : ℝ) ≤ (K : ℝ) ^ β := Real.rpow_nonneg (by linarith) β
  calc C * (K : ℝ) ^ β ≤ max C 0 * (K : ℝ) ^ β := mul_le_mul_of_nonneg_right (le_max_left C 0) h2
    _ ≤ max C 0 * (K : ℝ) ^ β' := mul_le_mul_of_nonneg_left h1 (le_max_right C 0)

/-- A doubling law with factor one gives doubling laws with every factor above one: the levels
`max(a, 0)` satisfy `a'(2K) ≤ a'(K) + max(c, 0) ≤ λ a'(K) + max(c, 0)`. -/
theorem DoublingLaw.of_one {lam : ℝ} (h : DoublingLaw ρ 1) (hlam : 1 ≤ lam) : DoublingLaw ρ lam := by
  obtain ⟨a, c, hmono, hstep, hlev⟩ := h
  refine ⟨fun K => max (a K) 0, max c 0, fun K L hKL => max_le_max (hmono hKL) le_rfl,
    fun K hK => ?_, hlev.mono fun K _ => le_max_left _ _⟩
  have h1 := hstep K hK
  have h2 : 0 ≤ max (a K) 0 := le_max_right _ _
  have h3 : max (a K) 0 ≤ lam * max (a K) 0 := le_mul_of_one_le_left h2 hlam
  refine max_le ?_ ?_
  · linarith [le_max_left (a K) 0, le_max_left c 0]
  · linarith [le_max_right c 0]

variable (hρ : ∀ K, K ^ 10 ≤ ρ K) {A : ℕ} (hρA : ∀ K, ρ K ≤ K ^ A)
include hρ hρA

/-- **Bounded loss is the line.** RH iff a constant level law holds. -/
theorem riemannHypothesis_iff_exists_const_isLevelLaw :
    RiemannHypothesis ↔ ∃ C : ℝ, IsLevelLaw ρ fun _ => C := by
  have hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K := fun K hK => lt_of_lt_of_le (pow_pos hK 10) (hρ K)
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ :=
      MixingArithmeticOfTheFloorTrees.riemannHypothesis_iff_neutralWindow_margin_bddBelow.1 hRH
    refine ⟨C, fun K hK => hC (3 * K + 1) (ρ K) (3 * K * ρ K) (hρ₁ K hK) ?_ ?_⟩
    · nlinarith [hρ₁ K hK]
    · nlinarith
  · rintro ⟨C, hC⟩
    rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero,
      zetaZeroWidth_eq_zero_iff_forall_doublingLaw hρ hρA]
    intro lam hlam
    refine ⟨fun _ => max C 0, 0, fun _ _ _ => le_rfl, fun K _ => ?_,
      hC.mono fun K _ => le_max_left C 0⟩
    have h0 : 0 ≤ max C 0 := le_max_right C 0
    nlinarith

/-- **Factor one is bounded loss.** RH iff the margin has a doubling law with factor one. -/
theorem riemannHypothesis_iff_doublingLaw_one : RiemannHypothesis ↔ DoublingLaw ρ 1 := by
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ := (riemannHypothesis_iff_exists_const_isLevelLaw hρ hρA).1 hRH
    exact ⟨fun _ => C, 0, fun _ _ _ => le_rfl, fun K _ => by simp, hC⟩
  · intro h
    rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero,
      zetaZeroWidth_eq_zero_iff_forall_doublingLaw hρ hρA]
    exact fun lam hlam => h.of_one hlam.le

/-- **Exponent zero is bounded loss.** RH iff the margin law holds at every positive rate. -/
theorem riemannHypothesis_iff_forall_marginLaw_pos :
    RiemannHypothesis ↔ ∀ β : ℝ, 0 < β → MarginLaw ρ β := by
  have hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K := fun K hK => lt_of_lt_of_le (pow_pos hK 10) (hρ K)
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  constructor
  · intro hw β hβ
    exact marginLaw_of_zetaZeroWidth_lt hρ₁ hρA (by rw [hw]; exact hβ)
  · intro h
    have h0 := (isRuler_marginLaw hρ hρA 0 (Set.mem_Ici.2 le_rfl)).2
      fun ε hε => by rw [zero_add]; exact h ε hε
    exact le_antisymm h0 zetaZeroWidth_nonneg

/-- **No intermediate growth.** Either a constant level works, or the margin law fails at some
positive rate. -/
theorem exists_const_isLevelLaw_or_exists_not_marginLaw :
    (∃ C : ℝ, IsLevelLaw ρ fun _ => C) ∨ ∃ β : ℝ, 0 < β ∧ ¬ MarginLaw ρ β := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl ((riemannHypothesis_iff_exists_const_isLevelLaw hρ hρA).1 hRH)
  · right
    by_contra hcon
    push Not at hcon
    exact hRH ((riemannHypothesis_iff_forall_marginLaw_pos hρ hρA).2 hcon)

#print axioms riemannHypothesis_iff_doublingLaw_one
#print axioms riemannHypothesis_iff_forall_marginLaw_pos
#print axioms exists_const_isLevelLaw_or_exists_not_marginLaw

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
