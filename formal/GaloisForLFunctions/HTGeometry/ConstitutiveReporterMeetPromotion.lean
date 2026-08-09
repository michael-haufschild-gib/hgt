import GaloisForLFunctions.HTGeometry.ConstitutiveAdmissionRelativePromotion

/-!
# Reporter meet and promotion selection

Pairing conserved reporters intersects their future envelopes.  Strict promotion admissibility
therefore composes by conjunction, and reporter refinement can only remove strict promotions.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

def pairedReporter {α : Type u} {β : Type v} {γ : Type w}
    (r : α → β) (s : α → γ) (x : α) : β × γ :=
  (r x, s x)

theorem futureReporterKernel_paired_iff
    {α : Type u} {β : Type v} {γ : Type w}
    (f g : α → α) (r : α → β) (s : α → γ) (x y : α) :
    FutureReporterKernel f g (pairedReporter r s) x y ↔
      FutureReporterKernel f g r x y ∧ FutureReporterKernel f g s x y := by
  constructor
  · intro h
    constructor
    · intro word
      exact congrArg Prod.fst (h word)
    · intro word
      exact congrArg Prod.snd (h word)
  · rintro ⟨hr, hs⟩ word
    exact Prod.ext (hr word) (hs word)

/-- Strict promotion for a reporter pair exists exactly when it exists for each component. -/
theorem reporterStrictExchangePromotionExists_paired_iff
    {α : Type u} {β : Type v} {γ : Type w}
    (f g : α → α) (r : α → β) (s : α → γ) :
    ReporterStrictExchangePromotionExists f g (pairedReporter r s) ↔
      ReporterStrictExchangePromotionExists f g r ∧
        ReporterStrictExchangePromotionExists f g s := by
  constructor
  · intro hpair
    have hfit :=
      (reporterStrictExchangePromotionExists_iff f g (pairedReporter r s)).1 hpair
    constructor
    · apply (reporterStrictExchangePromotionExists_iff f g r).2
      intro x y hxy
      exact (futureReporterKernel_paired_iff f g r s x y).1 (hfit hxy) |>.1
    · apply (reporterStrictExchangePromotionExists_iff f g s).2
      intro x y hxy
      exact (futureReporterKernel_paired_iff f g r s x y).1 (hfit hxy) |>.2
  · rintro ⟨hr, hs⟩
    have hfitr := (reporterStrictExchangePromotionExists_iff f g r).1 hr
    have hfits := (reporterStrictExchangePromotionExists_iff f g s).1 hs
    apply (reporterStrictExchangePromotionExists_iff f g (pairedReporter r s)).2
    intro x y hxy
    exact (futureReporterKernel_paired_iff f g r s x y).2
      ⟨hfitr hxy, hfits hxy⟩

def ReporterRefines {α : Type u} {β : Type v} {γ : Type w}
    (coarse : α → β) (fine : α → γ) : Prop :=
  ∃ h : γ → β, ∀ x, coarse x = h (fine x)

theorem futureReporterKernel_mono_of_refines
    {α : Type u} {β : Type v} {γ : Type w}
    (f g : α → α) (coarse : α → β) (fine : α → γ)
    (hrefines : ReporterRefines coarse fine) :
    ∀ ⦃x y⦄,
      FutureReporterKernel f g fine x y → FutureReporterKernel f g coarse x y := by
  rintro x y hfine word
  obtain ⟨h, hfactor⟩ := hrefines
  rw [hfactor, hfactor]
  exact congrArg h (hfine word)

theorem reporterStrictExchangePromotionExists_mono_of_refines
    {α : Type u} {β : Type v} {γ : Type w}
    (f g : α → α) (coarse : α → β) (fine : α → γ)
    (hrefines : ReporterRefines coarse fine) :
    ReporterStrictExchangePromotionExists f g fine →
      ReporterStrictExchangePromotionExists f g coarse := by
  intro hfine
  have hfit := (reporterStrictExchangePromotionExists_iff f g fine).1 hfine
  apply (reporterStrictExchangePromotionExists_iff f g coarse).2
  intro x y hxy
  exact futureReporterKernel_mono_of_refines f g coarse fine hrefines (hfit hxy)

def unitReporter {α : Type u} : α → Unit := fun _ => ()

theorem unitReporter_strictPromotion_exists {α : Type u} (f g : α → α) :
    ReporterStrictExchangePromotionExists f g (unitReporter : α → Unit) := by
  apply (reporterStrictExchangePromotionExists_iff_futureCriticalPairs f g unitReporter).2
  intro x word
  rfl

theorem delayedExchange_unitPair_conservation_veto :
    ¬ ReporterStrictExchangePromotionExists delayedExchangeLeft delayedExchangeRight
      (pairedReporter (unitReporter : DelayedExchangeState → Unit) delayedExchangeReporter) := by
  rw [reporterStrictExchangePromotionExists_paired_iff]
  intro h
  exact delayedExchange_no_reporterConserving_strictPromotion h.2

theorem constitutiveReporterMeetPromotionMechanism_closed :
    ReporterStrictExchangePromotionExists delayedExchangeLeft delayedExchangeRight
      (unitReporter : DelayedExchangeState → Unit) ∧
    (¬ ReporterStrictExchangePromotionExists delayedExchangeLeft delayedExchangeRight
      delayedExchangeReporter) ∧
    (¬ ReporterStrictExchangePromotionExists delayedExchangeLeft delayedExchangeRight
      (pairedReporter (unitReporter : DelayedExchangeState → Unit)
        delayedExchangeReporter)) := by
  exact ⟨unitReporter_strictPromotion_exists delayedExchangeLeft delayedExchangeRight,
    delayedExchange_no_reporterConserving_strictPromotion,
    delayedExchange_unitPair_conservation_veto⟩

end GaloisForLFunctions.HTGeometry
