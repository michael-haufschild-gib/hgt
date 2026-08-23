import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.KummerPhaseExcess

/-!
# Hasse classification for a composite Kummer stage

For a composite stage `s * r`, reduction to the outer `s`-stage is the complete invariant modulo
the embedded inner `r`-stage.  This packages the elementary Kummer exact sequence in quotient,
congruence, and existence--uniqueness forms.
-/

namespace HTGeometry.ConstraintFrameRelativity

open GaloisForLFunctions.HTGeometry

/-- The composite Kummer-stage inclusion and reduction are exact in the middle. -/
theorem kummerStage_functionExact (s r : ℕ) :
    Function.Exact (kummerIncl s r) (kummerRed s r).toAddMonoidHom :=
  fun x => kummerRed_eq_zero_iff s r x

/-- Reduction modulo `s` identifies the composite stage modulo the embedded inner stage with the
outer stage. -/
noncomputable def kummerStageHasseQuotientEquiv (s r : ℕ) :
    (ZMod (s * r) ⧸ (kummerIncl s r).range) ≃+ ZMod s :=
  addHasseQuotientEquiv (kummerIncl s r) (kummerRed s r).toAddMonoidHom
    (kummerStage_functionExact s r) (kummerRed_surjective s r)

@[simp] theorem kummerStageHasseQuotientEquiv_mk (s r : ℕ) (x : ZMod (s * r)) :
    kummerStageHasseQuotientEquiv s r (QuotientAddGroup.mk x) = kummerRed s r x :=
  addHasseQuotientEquiv_mk (kummerIncl s r) (kummerRed s r).toAddMonoidHom
    (kummerStage_functionExact s r) (kummerRed_surjective s r) x

/-- Two composite-stage classes have the same outer reduction exactly when their difference comes
from the embedded inner stage. -/
theorem kummerStage_congr_hasse_iff (s r : ℕ) (x y : ZMod (s * r)) :
    x - y ∈ (kummerIncl s r).range ↔ kummerRed s r x = kummerRed s r y :=
  addHasse_congr_iff (kummerIncl s r) (kummerRed s r).toAddMonoidHom
    (kummerStage_functionExact s r) x y

/-- Every outer-stage class lifts to the composite stage, uniquely modulo the embedded inner
stage. -/
theorem kummerStage_exists_unique_mod_inclusion (s r : ℕ) (a : ZMod s) :
    ∃ x : ZMod (s * r), kummerRed s r x = a ∧
      ∀ y : ZMod (s * r), kummerRed s r y = a ↔
        y - x ∈ (kummerIncl s r).range :=
  addHasse_exists_unique_mod_global
    (kummerIncl s r) (kummerRed s r).toAddMonoidHom
    (kummerStage_functionExact s r) (kummerRed_surjective s r) a

end HTGeometry.ConstraintFrameRelativity
