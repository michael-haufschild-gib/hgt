import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheConfinedFormCountsTheZerosRightOfTheLine
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep

/-!
# The bounded-index stratum of the confined form is Lindelöf-deep

The negative index of the confined form `Q_R = W + a(R) W₈` on half-line tests counts the zeros right
of the line (`confinedIndex_law`). Its bounded stratum is the Krein–Langer class of the Weil kernel:

* **Five sides of one stratum** (`confinedIndexBounded_tfae`). The confined index is bounded over
  all ratios and families of half-line tests iff the Hecke-orbit Weil kernel of `ζ` has finite
  index, iff only finitely many zeros lie off the line, iff the de Bruijn heat counts are bounded,
  iff all zeros above some height lie on the line.
* **The Lindelöf wall** (`lindelof_of_confinedIndexBounded`). A bounded confined index forces the
  Lindelöf hypothesis on the critical line and a zero-free half-plane `Re s > ½ + α`, `α < ½`.
  The finite layer of stage 2 is therefore Lindelöf-deep: proving it needs Lindelöf-strength input,
  while stage 2 only asks to exclude the critical state on it.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry
  HeckeKreinToeplitz _root_.RHTower _root_.RHTower.BacklundConverse _root_.RHTower.LindelofSparse
  _root_.RHTower.DeBruijn

/-- The confined form has bounded negative index over all ratios and all finite families of
half-line tests. -/
def ConfinedIndexBounded : Prop :=
  ∃ N : ℕ, ∀ (R : ℝ) (_ : 0 < R) (S : Finset ℝ) (H : S → ℝ → ℝ), (∀ s, IsHalfLineTest (H s)) →
    hermNegIndex (confinedGram R H) ≤ N

theorem confinedIndexBounded_iff_negIndex_zetaKernel_lt_top :
    ConfinedIndexBounded ↔ negIndex zetaKernel < ⊤ := by
  rw [ConfinedIndexBounded, bddAbove_confinedIndex_iff_finite, negIndex_zetaKernel,
    Set.encard_lt_top_iff]
  rfl

/-- **The bounded stratum of the confined form, seen from five sides.** -/
theorem confinedIndexBounded_tfae :
    [ConfinedIndexBounded,
      negIndex zetaKernel < ⊤,
      FiniteOffLine,
      ∃ M : ℕ, ∀ t, 0 < t → nonrealZeroCount t ≤ M,
      ∃ T₀ : ℝ, ∀ ρ ∈ zetaZeroConfig.carrier, T₀ < |ρ.im| → ρ.re = 1 / 2].TFAE := by
  have h := zetaKernel_finiteIndex_tfae Nat.prime_two Nat.prime_three (by norm_num)
  tfae_have 1 ↔ 2 := confinedIndexBounded_iff_negIndex_zetaKernel_lt_top
  tfae_have 2 ↔ 3 := h.out 0 2
  tfae_have 2 ↔ 4 := h.out 0 3
  tfae_have 2 ↔ 5 := h.out 0 4
  tfae_finish

/-- **The Lindelöf wall of stage 2.** A bounded confined index forces the Lindelöf hypothesis and a
zero-free half-plane `Re s > ½ + α` with `α < ½`. -/
theorem lindelof_of_confinedIndexBounded (h : ConfinedIndexBounded) :
    LindelofCriticalLine ∧ ∃ α : ℝ, α < 1 / 2 ∧ XiZeroHalfPlaneBound α :=
  ⟨lindelof_of_negIndex_zetaKernel_lt_top (confinedIndexBounded_iff_negIndex_zetaKernel_lt_top.mp h),
    quasiRH_of_negIndex_zetaKernel_lt_top (confinedIndexBounded_iff_negIndex_zetaKernel_lt_top.mp h)⟩

#print axioms confinedIndexBounded_tfae
#print axioms lindelof_of_confinedIndexBounded

end GaloisForLFunctions.ExclusionOfTheCriticalState
