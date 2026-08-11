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

/-- The induced left law is the unique quotient law intertwining the quotient map. -/
theorem exchangeQuotientLeft_unique {α : Type u} (f g : α → α)
    (F : ExchangeQuotient f g → ExchangeQuotient f g)
    (hF : ∀ x, F (exchangeQuotientMap f g x) = exchangeQuotientMap f g (f x)) :
    F = exchangeQuotientLeft f g := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  exact hF x

/-- The induced right law is the unique quotient law intertwining the quotient map. -/
theorem exchangeQuotientRight_unique {α : Type u} (f g : α → α)
    (G : ExchangeQuotient f g → ExchangeQuotient f g)
    (hG : ∀ x, G (exchangeQuotientMap f g x) = exchangeQuotientMap f g (g x)) :
    G = exchangeQuotientRight f g := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  exact hG x

/-! ## Calibration: successor against doubling -/

/-- The successor law. -/
def calibrationSucc (n : ℕ) : ℕ := n + 1

/-- The doubling law. -/
def calibrationDouble (n : ℕ) : ℕ := 2 * n

/-- The two-class partition of the naturals into zero and the positives. -/
def zeroClassRelation (x y : ℕ) : Prop := x = 0 ↔ y = 0

theorem zeroClassRelation_equivalence : Equivalence zeroClassRelation :=
  ⟨fun _ => Iff.rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **Nontrivial strictification.**  For successor against doubling the least exchange congruence
is exactly the zero/positive partition: strictification does not collapse the whole source. -/
theorem calibration_exchangeCongruence_iff (x y : ℕ) :
    ExchangeCongruence calibrationSucc calibrationDouble x y ↔ zeroClassRelation x y := by
  constructor
  · intro hxy
    refine exchangeCongruence_least (f := calibrationSucc) (g := calibrationDouble)
      zeroClassRelation_equivalence ?_ ?_ ?_ hxy
    · intro a b _
      simp [zeroClassRelation, calibrationSucc]
    · intro a b hab
      simpa [zeroClassRelation, calibrationDouble] using hab
    · intro a
      simp [zeroClassRelation, calibrationSucc, calibrationDouble]
  · intro hxy
    have hone : ExchangeCongruence calibrationSucc calibrationDouble 1 2 := by
      simpa [calibrationSucc, calibrationDouble] using
        exchangeCongruence_contains calibrationSucc calibrationDouble 0
    have hsucc : ∀ n : ℕ,
        ExchangeCongruence calibrationSucc calibrationDouble (n + 1) (n + 2) := by
      intro n
      induction n with
      | zero => simpa using hone
      | succ n ih =>
          have := exchangeCongruence_preserves_left calibrationSucc calibrationDouble ih
          simpa [calibrationSucc] using this
    have hall : ∀ n : ℕ,
        ExchangeCongruence calibrationSucc calibrationDouble 1 (n + 1) := by
      intro n
      induction n with
      | zero => exact (exchangeCongruence_equivalence _ _).refl 1
      | succ n ih => exact (exchangeCongruence_equivalence _ _).trans ih (hsucc n)
    rcases Nat.eq_zero_or_pos x with hx | hx
    · have hy : y = 0 := hxy.mp hx
      subst hx; subst hy
      exact (exchangeCongruence_equivalence _ _).refl 0
    · have hy : 0 < y := by
        rcases Nat.eq_zero_or_pos y with hy0 | hy0
        · exact absurd (hxy.mpr hy0) (by omega)
        · exact hy0
      obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, y = b + 1 := ⟨y - 1, by omega⟩
      exact (exchangeCongruence_equivalence _ _).trans
        ((exchangeCongruence_equivalence _ _).symm (hall a)) (hall b)

/-- The calibration quotient has exactly two classes. -/
theorem calibration_quotient_two_classes :
    (∀ n : ℕ,
        exchangeQuotientMap calibrationSucc calibrationDouble n =
          exchangeQuotientMap calibrationSucc calibrationDouble 0 ∨
        exchangeQuotientMap calibrationSucc calibrationDouble n =
          exchangeQuotientMap calibrationSucc calibrationDouble 1) ∧
      exchangeQuotientMap calibrationSucc calibrationDouble 0 ≠
        exchangeQuotientMap calibrationSucc calibrationDouble 1 := by
  constructor
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl rfl
    · refine Or.inr (Quotient.sound ?_)
      refine (calibration_exchangeCongruence_iff n 1).mpr ?_
      constructor
      · intro h; omega
      · intro h; omega
  · intro h
    have := (calibration_exchangeCongruence_iff 0 1).mp (Quotient.exact h)
    have h1 : (1 : ℕ) = 0 := this.mp rfl
    omega

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
