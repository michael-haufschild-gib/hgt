import GaloisForLFunctions.HTGeometry.ConstitutiveUnaryLawRepair

/-!
# Minimal exchange strictification

The critical pairs `f (g x) ~ g (f x)` generate the least equivalence relation preserved by both
unary laws.  On the resulting quotient the induced laws commute, and every observer carrying
commuting descents factors uniquely through this quotient.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Raw critical pairs exposing failure of two unary laws to exchange. -/
def ExchangeSeed {α : Type u} (f g : α → α) : α → α → Prop :=
  fun x y ↦ ∃ z, x = f (g z) ∧ y = g (f z)

/-- The two unary laws whose critical pairs are being strictified. -/
def exchangeLawFamily {α : Type u} (f g : α → α) : Set (α → α) :=
  {f, g}

/-- Least equivalence containing every exchange pair and preserved by both laws. -/
def ExchangeCongruence {α : Type u} (f g : α → α) : α → α → Prop :=
  UnaryLawClosure (exchangeLawFamily f g) (ExchangeSeed f g)

theorem exchangeCongruence_equivalence {α : Type u} (f g : α → α) :
    Equivalence (ExchangeCongruence f g) := by
  exact unaryLawClosure_equivalence _ _

theorem exchangeCongruence_contains {α : Type u} (f g : α → α) (x : α) :
    ExchangeCongruence f g (f (g x)) (g (f x)) := by
  apply unaryLawClosure_contains (exchangeLawFamily f g) (ExchangeSeed f g)
  exact ⟨x, rfl, rfl⟩

theorem exchangeCongruence_preserves_left {α : Type u} (f g : α → α) :
    UnaryPreserves f (ExchangeCongruence f g) := by
  apply unaryLawClosure_preserves (exchangeLawFamily f g) (ExchangeSeed f g)
  simp [exchangeLawFamily]

theorem exchangeCongruence_preserves_right {α : Type u} (f g : α → α) :
    UnaryPreserves g (ExchangeCongruence f g) := by
  apply unaryLawClosure_preserves (exchangeLawFamily f g) (ExchangeSeed f g)
  simp [exchangeLawFamily]

theorem exchangeCongruence_least {α : Type u} {f g : α → α}
    {R : α → α → Prop} (hR : Equivalence R)
    (hf : UnaryPreserves f R) (hg : UnaryPreserves g R)
    (hexchange : ∀ x, R (f (g x)) (g (f x))) :
    ∀ ⦃x y⦄, ExchangeCongruence f g x y → R x y := by
  apply unaryLawClosure_least hR
  · intro x y hxy
    obtain ⟨z, rfl, rfl⟩ := hxy
    exact hexchange z
  · intro h hmem
    have hfg : h = f ∨ h = g := by
      simpa [exchangeLawFamily] using hmem
    rcases hfg with rfl | rfl
    · exact hf
    · exact hg

/-- Setoid underlying the universal strict commuting quotient. -/
def exchangeSetoid {α : Type u} (f g : α → α) : Setoid α where
  r := ExchangeCongruence f g
  iseqv := exchangeCongruence_equivalence f g

/-- Universal quotient on which the two unary laws commute. -/
abbrev ExchangeQuotient {α : Type u} (f g : α → α) :=
  Quotient (exchangeSetoid f g)

def exchangeQuotientMap {α : Type u} (f g : α → α) :
    α → ExchangeQuotient f g :=
  Quotient.mk (exchangeSetoid f g)

def exchangeQuotientLeft {α : Type u} (f g : α → α) :
    ExchangeQuotient f g → ExchangeQuotient f g :=
  Quotient.map f (exchangeCongruence_preserves_left f g)

def exchangeQuotientRight {α : Type u} (f g : α → α) :
    ExchangeQuotient f g → ExchangeQuotient f g :=
  Quotient.map g (exchangeCongruence_preserves_right f g)

@[simp] theorem exchangeQuotientLeft_mk {α : Type u} (f g : α → α) (x : α) :
    exchangeQuotientLeft f g (exchangeQuotientMap f g x) =
      exchangeQuotientMap f g (f x) :=
  rfl

@[simp] theorem exchangeQuotientRight_mk {α : Type u} (f g : α → α) (x : α) :
    exchangeQuotientRight f g (exchangeQuotientMap f g x) =
      exchangeQuotientMap f g (g x) :=
  rfl

theorem exchangeQuotient_commute {α : Type u} (f g : α → α) :
    exchangeQuotientLeft f g ∘ exchangeQuotientRight f g =
      exchangeQuotientRight f g ∘ exchangeQuotientLeft f g := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  apply Quotient.sound
  exact exchangeCongruence_contains f g x

theorem exchangeCongruence_subset_observerKernel_of_commuting_descents
    {α : Type u} {β : Type v} (q : α → β) (f g : α → α) (F G : β → β)
    (hf : ∀ x, q (f x) = F (q x))
    (hg : ∀ x, q (g x) = G (q x))
    (hcomm : ∀ y, F (G y) = G (F y)) :
    ∀ ⦃x y⦄, ExchangeCongruence f g x y → ObserverKernel q x y := by
  apply exchangeCongruence_least (observerKernel_equivalence q)
  · exact observerKernel_preserved_of_descended q f F hf
  · exact observerKernel_preserved_of_descended q g G hg
  · intro x
    change q (f (g x)) = q (g (f x))
    calc
      q (f (g x)) = F (q (g x)) := hf _
      _ = F (G (q x)) := congrArg F (hg x)
      _ = G (F (q x)) := hcomm _
      _ = G (q (f x)) := congrArg G (hf x).symm
      _ = q (g (f x)) := (hg _).symm

/-- Canonical factor of every observer carrying commuting descents. -/
def exchangeObserverFactor {α : Type u} {β : Type v}
    (q : α → β) (f g : α → α) (F G : β → β)
    (hf : ∀ x, q (f x) = F (q x))
    (hg : ∀ x, q (g x) = G (q x))
    (hcomm : ∀ y, F (G y) = G (F y)) : ExchangeQuotient f g → β :=
  Quotient.lift q
    (exchangeCongruence_subset_observerKernel_of_commuting_descents
      q f g F G hf hg hcomm)

@[simp] theorem exchangeObserverFactor_mk {α : Type u} {β : Type v}
    (q : α → β) (f g : α → α) (F G : β → β)
    (hf : ∀ x, q (f x) = F (q x))
    (hg : ∀ x, q (g x) = G (q x))
    (hcomm : ∀ y, F (G y) = G (F y)) (x : α) :
    exchangeObserverFactor q f g F G hf hg hcomm (exchangeQuotientMap f g x) = q x :=
  rfl

theorem exchangeObserverFactor_unique {α : Type u} {β : Type v}
    (q : α → β) (f g : α → α) (F G : β → β)
    (hf : ∀ x, q (f x) = F (q x))
    (hg : ∀ x, q (g x) = G (q x))
    (hcomm : ∀ y, F (G y) = G (F y))
    (k : ExchangeQuotient f g → β)
    (hk : ∀ x, k (exchangeQuotientMap f g x) = q x) :
    k = exchangeObserverFactor q f g F G hf hg hcomm := by
  funext z
  refine Quotient.inductionOn z ?_
  intro x
  change k (exchangeQuotientMap f g x) =
    exchangeObserverFactor q f g F G hf hg hcomm (exchangeQuotientMap f g x)
  rw [hk]
  rfl

theorem exchangeObserverFactor_intertwines_left {α : Type u} {β : Type v}
    (q : α → β) (f g : α → α) (F G : β → β)
    (hf : ∀ x, q (f x) = F (q x))
    (hg : ∀ x, q (g x) = G (q x))
    (hcomm : ∀ y, F (G y) = G (F y)) :
    exchangeObserverFactor q f g F G hf hg hcomm ∘ exchangeQuotientLeft f g =
      F ∘ exchangeObserverFactor q f g F G hf hg hcomm := by
  funext z
  refine Quotient.inductionOn z ?_
  intro x
  exact hf x

theorem exchangeObserverFactor_intertwines_right {α : Type u} {β : Type v}
    (q : α → β) (f g : α → α) (F G : β → β)
    (hf : ∀ x, q (f x) = F (q x))
    (hg : ∀ x, q (g x) = G (q x))
    (hcomm : ∀ y, F (G y) = G (F y)) :
    exchangeObserverFactor q f g F G hf hg hcomm ∘ exchangeQuotientRight f g =
      G ∘ exchangeObserverFactor q f g F G hf hg hcomm := by
  funext z
  refine Quotient.inductionOn z ?_
  intro x
  exact hg x

theorem no_strictly_smaller_exchange_strictification {α : Type u}
    (f g : α → α) (R : α → α → Prop) (hR : Equivalence R)
    (hsmaller : ¬ ∀ ⦃x y⦄, ExchangeCongruence f g x y → R x y) :
    ¬ (UnaryPreserves f R ∧ UnaryPreserves g R ∧
      ∀ x, R (f (g x)) (g (f x))) := by
  rintro ⟨hf, hg, hexchange⟩
  exact hsmaller (exchangeCongruence_least hR hf hg hexchange)

theorem constitutiveExchangeStrictificationMechanism_closed {α : Type u} {β : Type v} :
    (∀ (f g : α → α), Equivalence (ExchangeCongruence f g)) ∧
    (∀ (f g : α → α) (x : α), ExchangeCongruence f g (f (g x)) (g (f x))) ∧
    (∀ (f g : α → α),
      exchangeQuotientLeft f g ∘ exchangeQuotientRight f g =
        exchangeQuotientRight f g ∘ exchangeQuotientLeft f g) ∧
    (∀ (q : α → β) (f g : α → α) (F G : β → β)
      (_hf : ∀ x, q (f x) = F (q x))
      (_hg : ∀ x, q (g x) = G (q x))
      (_hcomm : ∀ y, F (G y) = G (F y)),
      ∀ ⦃x y⦄, ExchangeCongruence f g x y → ObserverKernel q x y) := by
  exact ⟨exchangeCongruence_equivalence, exchangeCongruence_contains,
    exchangeQuotient_commute,
    exchangeCongruence_subset_observerKernel_of_commuting_descents⟩

end GaloisForLFunctions.HTGeometry
