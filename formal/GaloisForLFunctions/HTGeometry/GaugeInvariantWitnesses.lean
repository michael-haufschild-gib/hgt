import GaloisForLFunctions.HTGeometry.ChronometricGaugeRigidity

/-!
# Gauge-invariant laws exist

The chronometric rigidity theorems assume a law that a field redefinition of the extra sector
cannot change.  Two constructions give all the invariance the statements need: a law that reads
only the metric is invariant under *every* gauge action, and *every* law is invariant under a
trivial action.  Invariance is also closed under postcomposition, so the invariant laws are a
subalgebra of the reporters rather than an isolated example.
-/

namespace GaloisForLFunctions.HTGeometry

section Gauge

variable {Metric : Type u} {Extra : Type u} {Source : Type v} {Gauge : Type*}

/-- **A law that reads only the metric is gauge invariant.** -/
theorem gaugeInvariant_of_metric (act : Gauge → Extra → Extra) (f : Metric → Source) :
    GaugeInvariant act (fun p : Metric × Extra => f p.1) := fun _ _ _ => rfl

/-- A constant law is gauge invariant. -/
theorem gaugeInvariant_const (act : Gauge → Extra → Extra) (s : Source) :
    GaugeInvariant act (fun _ : Metric × Extra => s) := fun _ _ _ => rfl

/-- Every law is invariant under a trivial gauge action. -/
theorem gaugeInvariant_of_act_id {act : Gauge → Extra → Extra}
    (hact : ∀ γ e, act γ e = e) (law : Metric × Extra → Source) :
    GaugeInvariant act law := by
  intro γ g e
  rw [hact γ e]

/-- Gauge invariance is preserved by postcomposition. -/
theorem GaugeInvariant.comp {act : Gauge → Extra → Extra} {law : Metric × Extra → Source}
    (h : GaugeInvariant act law) {Target : Type*} (F : Source → Target) :
    GaugeInvariant act (fun p => F (law p)) := by
  intro γ g e
  show F (law (g, act γ e)) = F (law (g, e))
  rw [h γ g e]

/-- Gauge invariance is inherited by any law that factors through an invariant one. -/
theorem GaugeInvariant.of_eq {act : Gauge → Extra → Extra} {law law' : Metric × Extra → Source}
    (h : GaugeInvariant act law) (heq : ∀ p, law' p = law p) :
    GaugeInvariant act law' := by
  intro γ g e
  rw [heq, heq, h γ g e]

end Gauge

end GaloisForLFunctions.HTGeometry
