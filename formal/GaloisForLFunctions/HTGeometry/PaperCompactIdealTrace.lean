import GaloisForLFunctions.HTGeometry.PaperTraceConeIdealTransport
import GaloisForLFunctions.HTGeometry.CompactAdjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The compact ideal as an extended trace

The ideal-weight construction assigns zero to compact positive operators and infinity to all
others. Its Gram cost detects exact compactness, is unchanged by compact perturbations, and
retains the full positive-cut criterion. This supplies a trace-cone invariant for operator
completions without replacing compactness by a small essential norm.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open TraceConeClassification Classical
open scoped NNReal ENNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance : PartialOrder (E →L[ℂ] E) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (E →L[ℂ] E) := CStarAlgebra.spectralOrderedRing _

/-- The compact operators as a nonunital star subalgebra. -/
def compactOperatorStarAlgebra : NonUnitalStarSubalgebra ℂ (E →L[ℂ] E) where
  carrier := {T | IsCompactOperator T}
  zero_mem' := isCompactOperator_zero
  add_mem' := fun hS hT => hS.add hT
  smul_mem' := fun c _ hT => hT.smul c
  mul_mem' := fun _ hT => hT.clm_comp _
  star_mem' := fun hT => isCompactOperator_adjoint_rectangular _ hT

/-- The norm-closed two-sided compact ideal. -/
def compactOperatorClosedIdeal : ClosedIdeal (E →L[ℂ] E) :=
  ⟨compactOperatorStarAlgebra E, isClosed_setOf_isCompactOperator,
    fun S _ hT => hT.clm_comp S, fun _ T hS => hS.comp_clm T⟩

/-- The extended lower semicontinuous trace of the compact ideal. -/
def compactOperatorIdealTrace : ExtendedTrace (E →L[ℂ] E) :=
  (compactOperatorClosedIdeal E).weight

/-- A Gram cost which is zero exactly on compact operators. -/
def compactOperatorTraceCost (T : E →L[ℂ] E) : ℝ≥0∞ :=
  compactOperatorIdealTrace E (Positive.starMul T)

variable {E}

/-- The ideal trace has no finite nonzero values. -/
theorem compactOperatorIdealTrace_apply (a : Positive (E →L[ℂ] E)) :
    compactOperatorIdealTrace E a = if IsCompactOperator a.1 then 0 else ∞ :=
  ClosedIdeal.weight_apply _ _

/-- Passing to a Gram operator does not change membership in the compact ideal. -/
theorem compactOperatorTraceCost_eq (T : E →L[ℂ] E) :
    compactOperatorTraceCost E T = if IsCompactOperator T then 0 else ∞ := by
  classical
  rw [compactOperatorTraceCost, compactOperatorIdealTrace_apply]
  have h := closed_ideal_star_mul_mem_iff (compactOperatorStarAlgebra E)
    (compactOperatorClosedIdeal E).2.1 (compactOperatorClosedIdeal E).2.2.1 T
  change IsCompactOperator (star T * T) ↔ IsCompactOperator T at h
  simp only [Positive.starMul, h]

@[simp] theorem compactOperatorTraceCost_eq_zero_iff (T : E →L[ℂ] E) :
    compactOperatorTraceCost E T = 0 ↔ IsCompactOperator T := by
  classical
  rw [compactOperatorTraceCost_eq]
  split <;> simp_all

@[simp] theorem compactOperatorTraceCost_eq_top_iff (T : E →L[ℂ] E) :
    compactOperatorTraceCost E T = ∞ ↔ ¬ IsCompactOperator T := by
  classical
  rw [compactOperatorTraceCost_eq]
  split <;> simp_all

/-- Every finite compact-ideal cost is already zero. -/
theorem compactOperatorTraceCost_lt_top_iff (T : E →L[ℂ] E) :
    compactOperatorTraceCost E T < ∞ ↔ IsCompactOperator T := by
  classical
  rw [compactOperatorTraceCost_eq]
  split <;> simp_all

/-- Compact changes of a completed operator leave the ideal cost unchanged. -/
theorem compactOperatorTraceCost_add_compact (T : E →L[ℂ] E)
    (K : compactOperatorStarAlgebra E) :
    compactOperatorTraceCost E (T + K.1) = compactOperatorTraceCost E T := by
  classical
  have h : IsCompactOperator (T + K.1) ↔ IsCompactOperator T := by
    constructor
    · intro h
      have hsub : IsCompactOperator (T + K.1 - K.1 : E →L[ℂ] E) := h.sub K.2
      simpa only [add_sub_cancel_right] using hsub
    · exact fun h => h.add K.2
  simp only [compactOperatorTraceCost_eq, h]

/-- The ideal cost is insensitive to adjoint reversal. -/
theorem compactOperatorTraceCost_star (T : E →L[ℂ] E) :
    compactOperatorTraceCost E (star T) = compactOperatorTraceCost E T := by
  classical
  have h : IsCompactOperator (star T : E →L[ℂ] E) ↔ IsCompactOperator T := by
    constructor
    · intro h
      have hstar : IsCompactOperator (star (star T) : E →L[ℂ] E) :=
        isCompactOperator_adjoint_rectangular (star T) h
      simpa only [star_star] using hstar
    · exact isCompactOperator_adjoint_rectangular T
  simp only [compactOperatorTraceCost_eq, h]

/-- A sum of positive Gram costs vanishes exactly when both operators are compact. -/
theorem compactOperatorIdealTrace_gram_add_eq_zero_iff (S T : E →L[ℂ] E) :
    compactOperatorIdealTrace E (Positive.add (Positive.starMul S) (Positive.starMul T)) = 0 ↔
      IsCompactOperator S ∧ IsCompactOperator T := by
  rw [(compactOperatorIdealTrace E).map_add]
  change compactOperatorTraceCost E S + compactOperatorTraceCost E T = 0 ↔ _
  simp

/-- The ideal trace recovers the original compact ideal as its finite ideal. -/
theorem compactOperatorIdealTrace_finiteIdeal :
    (compactOperatorIdealTrace E).finiteIdeal = compactOperatorStarAlgebra E :=
  ClosedIdeal.finiteIdeal_weight _

/-- Exact compactness is equivalent to compactness of every strictly positive spectral cut. -/
theorem compactOperator_positive_iff_cuts (a : Positive (E →L[ℂ] E)) :
    IsCompactOperator a.1 ↔
      ∀ ε : ℝ≥0, 0 < ε → IsCompactOperator (Positive.cut a ε).1 := by
  have h := (compactOperatorIdealTrace E).positive_mem_finiteIdeal_iff_cuts a
  rw [compactOperatorIdealTrace_finiteIdeal] at h
  change IsCompactOperator a.1 ↔
    ∀ ε : ℝ≥0, 0 < ε → compactOperatorIdealTrace E (Positive.cut a ε) < ∞ at h
  have hc (b : Positive (E →L[ℂ] E)) :
      compactOperatorIdealTrace E b < ∞ ↔ IsCompactOperator b.1 := by
    rw [compactOperatorIdealTrace_apply]
    split <;> simp_all
  simpa only [hc] using h

end

end GaloisForLFunctions.HTGeometry
