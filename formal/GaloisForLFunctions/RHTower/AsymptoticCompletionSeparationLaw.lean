import GaloisForLFunctions.RHTower.QuantumRecurrenceCoronaLaw
import GaloisForLFunctions.HTGeometry.TailQuotientSeparationLaw

/-!
# Finite-observation / asymptotic-completion separation

Every finite cylinder of complete histories projects onto the whole recurrence
corona.  Consequently, a reporter on asymptotic history classes that is
determined by any fixed finite observation horizon is constant.

This is an exact information boundary: no nonconstant complete-time spectral
invariant can be an exact finite-horizon observable.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The recurrence-asymptotic relation ignores every finite modification of
a history. -/
theorem recurrenceAsymptoticSetoid_tailSaturated :
    TailSaturated recurrenceAsymptoticSetoid := by
  intro u v huv
  exact (recurrenceCoronaClass_eq_iff u v).mp
    (recurrenceCoronaClass_eq_of_eventuallyEq huv)

/-- A recurrence-corona reporter is determined by horizon `N` when histories
agreeing through `N` always receive the same reported value. -/
def RecurrenceCoronaReporterDeterminedBy
    {Y : Type*} (N : ℕ) (F : RecurrenceCorona → Y) : Prop :=
  ∀ u v : ℕ → ℂ,
    (∀ n ≤ N, u n = v n) →
      F (recurrenceCoronaClass u) = F (recurrenceCoronaClass v)

/-- **Finite-observation / asymptotic-completion separation law.** Every map
from the recurrence corona that is determined by one finite observation
horizon is constant. -/
theorem finiteHorizon_recurrenceCoronaReporter_constant
    {Y : Type*} (N : ℕ) (F : RecurrenceCorona → Y)
    (hF : RecurrenceCoronaReporterDeterminedBy N F) :
    ReporterConstant F := by
  intro q₁ q₂
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨w, hprefix, hw⟩ :=
    finiteCylinder_surjective_recurrenceCorona N u q₂
  rw [← hw]
  exact hF u w fun n hn => (hprefix n hn).symm

/-- Every nonconstant recurrence-corona reporter necessarily escapes every
fixed finite observation horizon. -/
theorem nonconstant_recurrenceCoronaReporter_not_determinedBy
    {Y : Type*} (F : RecurrenceCorona → Y)
    (hF : ¬ ReporterConstant F) (N : ℕ) :
    ¬ RecurrenceCoronaReporterDeterminedBy N F := by
  intro hfinite
  exact hF (finiteHorizon_recurrenceCoronaReporter_constant N F hfinite)

/-- No finite-horizon-determined reporter can injectively encode the
recurrence corona. -/
theorem finiteHorizon_recurrenceCoronaReporter_not_injective
    {Y : Type*} (N : ℕ) (F : RecurrenceCorona → Y)
    (hF : RecurrenceCoronaReporterDeterminedBy N F) :
    ¬ Function.Injective F := by
  intro hinjective
  have hconstant := finiteHorizon_recurrenceCoronaReporter_constant N F hF
  apply recurrenceCoronaClass_postHorizonPersistentHistory_ne_zero N
  apply hinjective
  exact hconstant _ _

end

end RHTower
