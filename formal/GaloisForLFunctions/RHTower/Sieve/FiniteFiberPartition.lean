import GaloisForLFunctions.RHTower.Sieve.FiniteFiberCorrelation

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def finiteFiberCountWith {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (p : α → Prop) [DecidablePred p] (b : β) : ℕ :=
  (Finset.univ.filter fun a => p a ∧ f a = b).card

def finiteFiberEnergyWith {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) (p : α → Prop) [DecidablePred p] : ℕ :=
  ∑ b : β, finiteFiberCountWith f p b ^ (2 : ℕ)

theorem finiteFiberCount_eq_add_with_not
    {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (p : α → Prop) [DecidablePred p] (b : β) :
    finiteFiberCount f b =
      finiteFiberCountWith f p b + finiteFiberCountWith f (fun a => ¬p a) b := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun a : α => f a = b) p
  simpa [finiteFiberCount, finiteFiberCountWith, Finset.filter_filter,
    and_comm, and_left_comm, and_assoc] using h.symm

theorem add_sq_le_two_sq_add_sq (a b : ℕ) :
    (a + b) ^ (2 : ℕ) ≤ 2 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
  calc
    (a + b) ^ (2 : ℕ) = a ^ (2 : ℕ) + 2 * a * b + b ^ (2 : ℕ) := by ring
    _ ≤ a ^ (2 : ℕ) + (a ^ (2 : ℕ) + b ^ (2 : ℕ)) + b ^ (2 : ℕ) := by
      gcongr
      exact two_mul_le_add_sq a b
    _ = 2 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by ring

/-- Partitioning every fibre into good and bad elements costs only the
binary square factor `2`. -/
theorem finiteFiberEnergy_le_partition
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (p : α → Prop) [DecidablePred p] :
    finiteFiberEnergy f ≤
      2 * (finiteFiberEnergyWith f p +
        finiteFiberEnergyWith f (fun a => ¬p a)) := by
  classical
  unfold finiteFiberEnergy finiteFiberEnergyWith
  calc
    (∑ b : β, finiteFiberCount f b ^ (2 : ℕ)) =
        ∑ b : β, (finiteFiberCountWith f p b +
          finiteFiberCountWith f (fun a => ¬p a) b) ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [finiteFiberCount_eq_add_with_not (p := p)]
    _ ≤ ∑ b : β, 2 *
        (finiteFiberCountWith f p b ^ (2 : ℕ) +
          finiteFiberCountWith f (fun a => ¬p a) b ^ (2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro b _
      exact add_sq_le_two_sq_add_sq _ _
    _ = 2 * ((∑ b : β, finiteFiberCountWith f p b ^ (2 : ℕ)) +
        ∑ b : β, finiteFiberCountWith f (fun a => ¬p a) b ^ (2 : ℕ)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem finiteFiberEnergyWith_eq_card
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (p : α → Prop) [DecidablePred p] :
    finiteFiberEnergyWith f p =
      Fintype.card {z : α × α // p z.1 ∧ p z.2 ∧ f z.1 = f z.2} := by
  classical
  let e : (Σ b : β,
      {a : α // p a ∧ f a = b} × {a : α // p a ∧ f a = b}) ≃
      {z : α × α // p z.1 ∧ p z.2 ∧ f z.1 = f z.2} :=
    { toFun := fun z => ⟨(z.2.1.1, z.2.2.1),
        ⟨z.2.1.2.1, z.2.2.2.1, z.2.1.2.2.trans z.2.2.2.2.symm⟩⟩
      invFun := fun z => ⟨f z.1.1,
        ⟨z.1.1, z.2.1, rfl⟩, ⟨z.1.2, z.2.2.1, z.2.2.2.symm⟩⟩
      left_inv := by
        intro z
        rcases z with ⟨b, ⟨x, hx⟩, ⟨y, hy⟩⟩
        rcases hx with ⟨hpx, rfl⟩
        rfl
      right_inv := fun z => Subtype.ext rfl }
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  unfold finiteFiberEnergyWith
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.card_prod, pow_two]
  congr 1
  · rw [Fintype.card_of_subtype
      (Finset.univ.filter fun a : α => p a ∧ f a = b) (by simp)]
    rfl
  · rw [Fintype.card_of_subtype
      (Finset.univ.filter fun a : α => p a ∧ f a = b) (by simp)]
    rfl

end

end RHTower.Sieve
