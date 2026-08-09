import GaloisForLFunctions.HTGeometry.ConstitutiveExchangeStrictification
import GaloisForLFunctions.HTGeometry.ConstitutiveExchangeCentralPromotion

/-!
# Reporter-constrained promotion selection

A reporter descends through minimal exchange strictification exactly when it is constant on the
generated exchange congruence.  Any reporter detecting a critical pair is incompatible with an
observer that both executes the laws and makes them commute.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

def ExchangeReporterDescends {α : Type u} {β : Type v}
    (f g : α → α) (r : α → β) : Prop :=
  ∃ rbar : ExchangeQuotient f g → β,
    ∀ x, rbar (exchangeQuotientMap f g x) = r x

theorem exchangeReporter_descends_iff_congruence_constant
    {α : Type u} {β : Type v} (f g : α → α) (r : α → β) :
    ExchangeReporterDescends f g r ↔
      ∀ ⦃x y⦄, ExchangeCongruence f g x y → r x = r y := by
  constructor
  · rintro ⟨rbar, hrbar⟩ x y hxy
    calc
      r x = rbar (exchangeQuotientMap f g x) := (hrbar x).symm
      _ = rbar (exchangeQuotientMap f g y) := congrArg rbar (Quotient.sound hxy)
      _ = r y := hrbar y
  · intro hconstant
    refine ⟨Quotient.lift r hconstant, ?_⟩
    intro x
    rfl

theorem exchangeReporter_descended_unique
    {α : Type u} {β : Type v} (f g : α → α) (r : α → β)
    (rbar₁ rbar₂ : ExchangeQuotient f g → β)
    (h₁ : ∀ x, rbar₁ (exchangeQuotientMap f g x) = r x)
    (h₂ : ∀ x, rbar₂ (exchangeQuotientMap f g x) = r x) :
    rbar₁ = rbar₂ := by
  funext z
  refine Quotient.inductionOn z ?_
  intro x
  exact (h₁ x).trans (h₂ x).symm

theorem no_exchangeReporter_descent_of_detects_criticalPair
    {α : Type u} {β : Type v} (f g : α → α) (r : α → β) (x : α)
    (hdetect : r (f (g x)) ≠ r (g (f x))) :
    ¬ ExchangeReporterDescends f g r := by
  intro hdesc
  have hconstant :=
    (exchangeReporter_descends_iff_congruence_constant f g r).1 hdesc
  exact hdetect (hconstant (exchangeCongruence_contains f g x))

theorem commutingObserver_cannot_preserve_criticalPairReporter
    {α : Type u} {β : Type v} {γ : Type w}
    (q : α → β) (f g : α → α) (F G : β → β) (r : α → γ)
    (hf : ∀ x, q (f x) = F (q x))
    (hg : ∀ x, q (g x) = G (q x))
    (hcomm : ∀ y, F (G y) = G (F y))
    (x : α) (hdetect : r (f (g x)) ≠ r (g (f x))) :
    ¬ ∃ R : β → γ, ∀ z, R (q z) = r z := by
  rintro ⟨R, hR⟩
  have hq : q (f (g x)) = q (g (f x)) := by
    calc
      q (f (g x)) = F (q (g x)) := hf _
      _ = F (G (q x)) := congrArg F (hg x)
      _ = G (F (q x)) := hcomm _
      _ = G (q (f x)) := congrArg G (hf x).symm
      _ = q (g (f x)) := (hg _).symm
  apply hdetect
  calc
    r (f (g x)) = R (q (f (g x))) := (hR _).symm
    _ = R (q (g (f x))) := congrArg R hq
    _ = r (g (f x)) := hR _

/-- Central history reporter in the Heisenberg promotion. -/
def heisCentralReporter (p : Heis) : ℤ := p.z

theorem heisCentralReporter_detects_exchange :
    heisCentralReporter (exchangeGenF * exchangeGenG) = 1 ∧
      heisCentralReporter (exchangeGenG * exchangeGenF) = 0 := by
  constructor <;> rfl

theorem heisCentralReporter_no_strict_factor :
    ¬ ∃ R : ExchangeAbelian → ℤ,
      ∀ p, R (heisExchangeProjection p) = heisCentralReporter p := by
  rintro ⟨R, hR⟩
  have hproj :
      heisExchangeProjection (exchangeGenF * exchangeGenG) =
        heisExchangeProjection (exchangeGenG * exchangeGenF) := by
    simpa only [map_mul] using exchangeGenerators_strict_shadow_commute
  have hreport :
      heisCentralReporter (exchangeGenF * exchangeGenG) =
        heisCentralReporter (exchangeGenG * exchangeGenF) := by
    calc
      heisCentralReporter (exchangeGenF * exchangeGenG) =
          R (heisExchangeProjection (exchangeGenF * exchangeGenG)) := (hR _).symm
      _ = R (heisExchangeProjection (exchangeGenG * exchangeGenF)) := congrArg R hproj
      _ = heisCentralReporter (exchangeGenG * exchangeGenF) := hR _
  norm_num [heisCentralReporter, exchangeGenF, exchangeGenG] at hreport

theorem heisFirstCoordinate_strict_factor :
    ∃ R : ExchangeAbelian → ℤ,
      ∀ p, R (heisExchangeProjection p) = p.x := by
  refine ⟨fun u ↦ u.1, ?_⟩
  intro p
  rfl

theorem heisSecondCoordinate_strict_factor :
    ∃ R : ExchangeAbelian → ℤ,
      ∀ p, R (heisExchangeProjection p) = p.y := by
  refine ⟨fun u ↦ u.2, ?_⟩
  intro p
  rfl

theorem constitutiveExchangePromotionSelectionMechanism_closed
    {α : Type u} {β : Type v} {γ : Type w} :
    (∀ (f g : α → α) (r : α → β),
      ExchangeReporterDescends f g r ↔
        ∀ ⦃x y⦄, ExchangeCongruence f g x y → r x = r y) ∧
    (∀ (q : α → β) (f g : α → α) (F G : β → β) (r : α → γ)
      (_hf : ∀ x, q (f x) = F (q x))
      (_hg : ∀ x, q (g x) = G (q x))
      (_hcomm : ∀ y, F (G y) = G (F y))
      (x : α),
      r (f (g x)) ≠ r (g (f x)) →
        ¬ ∃ R : β → γ, ∀ z, R (q z) = r z) ∧
    (¬ ∃ R : ExchangeAbelian → ℤ,
      ∀ p, R (heisExchangeProjection p) = heisCentralReporter p) ∧
    (∃ R : ExchangeAbelian → ℤ,
      ∀ p, R (heisExchangeProjection p) = p.x) ∧
    (∃ R : ExchangeAbelian → ℤ,
      ∀ p, R (heisExchangeProjection p) = p.y) := by
  exact ⟨exchangeReporter_descends_iff_congruence_constant,
    commutingObserver_cannot_preserve_criticalPairReporter,
    heisCentralReporter_no_strict_factor,
    heisFirstCoordinate_strict_factor,
    heisSecondCoordinate_strict_factor⟩

end GaloisForLFunctions.HTGeometry
