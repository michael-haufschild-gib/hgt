import GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimitiveFluxNonnormalGraphReduction
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFlatFluxBlockTail

/-!
# The localized equation and the terminal position bound

Two inputs of the flat-flux localization.

`(9)`: cutting the value equation leaves exactly the Gamma commutator, because the position
multiplier and the bounded prime adjacency both commute with a scalar cutoff — only the jump
operator does not.

`(10)`, position part: on a profile supported past `a` the quadratic form of multiplication by the
position dominates `a` times the squared norm.  Together with the accretivity of the jump operator
and the crude bound for the prime adjacency this is the coercive constant `2(n−1) − ‖B‖` of the
terminal Gamma block; the assembly of the three is the corpus `reInner_sub_ge`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(9)`: cutting leaves only the Gamma commutator -/

/-- **`(9)`.**  If the bounded part of the coefficient commutes with the cutoff, cutting the flux
leaves exactly the Gamma commutator. -/
theorem primitiveFlux_cut_of_commuting {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℝ) (R B M : Module.End ℝ V) (F : V)
    (hBM : ∀ v : V, B (M v) = M (B v)) :
    twoLPlus L (R - B) (M F)
      = M (twoLPlus L (R - B) F) + linearCommutator R M F := by
  have hcomm : linearCommutator (R - B) M F = linearCommutator R M F := by
    show (R - B) (M F) - M ((R - B) F) = R (M F) - M (R F)
    simp only [LinearMap.sub_apply, map_sub, hBM F]
    abel
  have hbase := primitiveFlux_eq_cut_flux L (R - B) M F
  rw [hcomm] at hbase
  rw [← hbase]
  abel


/-- **`(25)`: the cutoff primitive splits into the Gamma and the prime commutator.** -/
theorem linearCommutator_sub {V : Type*} [AddCommGroup V] [Module ℝ V]
    (R B M : Module.End ℝ V) (F : V) :
    linearCommutator (R - B) M F = linearCommutator R M F - linearCommutator B M F := by
  show (R - B) (M F) - M ((R - B) F) = (R (M F) - M (R F)) - (B (M F) - M (B F))
  simp only [LinearMap.sub_apply, map_sub]
  abel

/-! ## `(10)`: the terminal position bound -/

variable {X : Type*} [NormedAddCommGroup X]

/-- **The position quadratic form on a terminal profile.**  A profile vanishing below `a` has
position form at least `a` times its squared norm. -/
theorem lintegral_position_ge {v : ℝ → X} {a : ℝ}
    (hsupp : ∀ L : ℝ, L < a → v L = 0) :
    ENNReal.ofReal a * (∫⁻ L, ‖v L‖ₑ ^ 2)
      ≤ ∫⁻ L, ENNReal.ofReal L * ‖v L‖ₑ ^ 2 := by
  have hzero : ∀ L : ℝ, L < a → ‖v L‖ₑ ^ 2 = 0 := by
    intro L hL
    rw [hsupp L hL]
    simp
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun L => ?_
  rcases lt_or_ge L a with hL | hL
  · rw [hzero L hL]
    simp
  · exact mul_le_mul' (ENNReal.ofReal_le_ofReal hL) le_rfl

/-- The same bound restricted to a block: a profile carried by the block `[n−1, n+2]` has position
form at least `n−1` times its squared norm. -/
theorem lintegral_position_block_ge {v : ℝ → X} {n : ℤ}
    (hsupp : ∀ L : ℝ, L < (n : ℝ) - 1 → v L = 0) :
    ENNReal.ofReal ((n : ℝ) - 1) * (∫⁻ L, ‖v L‖ₑ ^ 2)
      ≤ ∫⁻ L, ENNReal.ofReal L * ‖v L‖ₑ ^ 2 :=
  lintegral_position_ge hsupp

end GaloisForLFunctions.RHTower
