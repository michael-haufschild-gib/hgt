import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- Size of one fibre of a map between finite types. -/
def finiteFiberCount {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (b : β) : ℕ :=
  (Finset.univ.filter fun a => f a = b).card

/-- Squared `ℓ²` mass of all fibres. -/
def finiteFiberEnergy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) : ℕ :=
  ∑ b : β, finiteFiberCount f b ^ (2 : ℕ)

/-- Correlation of the fibre-count vector with an additive translate. -/
def finiteFiberCorrelation {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [AddGroup β] (f : α → β) (l : β) : ℕ :=
  ∑ b : β, finiteFiberCount f (b + l) * finiteFiberCount f b

/-- Translation cannot increase the autocorrelation of a finite fibre-count
vector.  This is the finite Cauchy--Schwarz form of the shifted-moment bound. -/
theorem finiteFiberCorrelation_le_energy
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [AddCommGroup β] (f : α → β) (l : β) :
    finiteFiberCorrelation f l ≤ finiteFiberEnergy f := by
  let R : β → ℕ := finiteFiberCount f
  have hshift : (∑ b : β, R (b + l) ^ (2 : ℕ)) = ∑ b : β, R b ^ (2 : ℕ) := by
    exact Equiv.sum_comp (Equiv.addRight l) (fun b : β => R b ^ (2 : ℕ))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) Finset.univ
    (fun b : β => R (b + l)) R
  rw [hshift] at hc
  have hsquare : (finiteFiberCorrelation f l) ^ (2 : ℕ) ≤
      (finiteFiberEnergy f) ^ (2 : ℕ) := by
    simpa [finiteFiberCorrelation, finiteFiberEnergy, R, pow_two] using hc
  exact (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp hsquare

theorem card_finiteFiber_eq
    {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (b : β) :
    Fintype.card {a : α // f a = b} = finiteFiberCount f b := by
  rw [Fintype.card_of_subtype (Finset.univ.filter fun a => f a = b) (by simp)]
  rfl

/-- The fibre energy is exactly the number of ordered pairs with equal
images. -/
theorem finiteFiberEnergy_eq_card
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) :
    finiteFiberEnergy f = Fintype.card {p : α × α // f p.1 = f p.2} := by
  let e : (Σ b : β, {a : α // f a = b} × {a : α // f a = b}) ≃
      {p : α × α // f p.1 = f p.2} :=
    { toFun := fun z => ⟨(z.2.1.1, z.2.2.1), z.2.1.2.trans z.2.2.2.symm⟩
      invFun := fun p => ⟨f p.1.1, ⟨p.1.1, rfl⟩, ⟨p.1.2, p.2.symm⟩⟩
      left_inv := by
        intro z
        rcases z with ⟨b, ⟨x, hx⟩, ⟨y, hy⟩⟩
        subst b
        rfl
      right_inv := by
        intro p
        apply Subtype.ext
        rfl }
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  unfold finiteFiberEnergy
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.card_prod, ← card_finiteFiber_eq f b, pow_two]

/-- The translated fibre correlation counts ordered pairs whose images
differ by the prescribed translate. -/
theorem finiteFiberCorrelation_eq_card
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [AddCommGroup β] (f : α → β) (l : β) :
    finiteFiberCorrelation f l =
      Fintype.card {p : α × α // f p.1 = f p.2 + l} := by
  let e : (Σ b : β, {a : α // f a = b + l} × {a : α // f a = b}) ≃
      {p : α × α // f p.1 = f p.2 + l} :=
    { toFun := fun z => ⟨(z.2.1.1, z.2.2.1),
        z.2.1.2.trans (congrArg (· + l) z.2.2.2.symm)⟩
      invFun := fun p => ⟨f p.1.2, ⟨p.1.1, p.2⟩, ⟨p.1.2, rfl⟩⟩
      left_inv := by
        intro z
        rcases z with ⟨b, ⟨x, hx⟩, ⟨y, hy⟩⟩
        subst b
        rfl
      right_inv := fun p => Subtype.ext rfl }
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  unfold finiteFiberCorrelation
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.card_prod, ← card_finiteFiber_eq f (b + l),
    ← card_finiteFiber_eq f b]

end

end RHTower.Sieve
