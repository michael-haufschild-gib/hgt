import GaloisForLFunctions.RHTower.Sieve.FiniteFiberCorrelation
import Mathlib.Tactic

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

theorem card_transformed_fixed_shift_le_energy
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ]
    [AddCommGroup β] [AddCommGroup γ]
    (f : α → β) (A : β →+ γ) (hA : Function.Injective A)
    (c d : γ) :
    Fintype.card {z : α × α // c + A (f z.1) = d + A (f z.2)} ≤
      finiteFiberEnergy f := by
  by_cases hne : Nonempty {z : α × α // c + A (f z.1) = d + A (f z.2)}
  · let w := Classical.choice hne
    let l : β := f w.1.1 - f w.1.2
    let e : {z : α × α // c + A (f z.1) = d + A (f z.2)} ↪
        {z : α × α // f z.1 = f z.2 + l} :=
      { toFun := fun z => ⟨z.1, by
          have hz := z.2
          have hw := w.2
          dsimp [l]
          have hz' : A (f z.1.1) - A (f z.1.2) = d - c := by
            calc
              A (f z.1.1) - A (f z.1.2) =
                  (c + A (f z.1.1)) - (c + A (f z.1.2)) := by abel
              _ = (d + A (f z.1.2)) - (c + A (f z.1.2)) := by rw [hz]
              _ = d - c := by abel
          have hw' : A (f w.1.1) - A (f w.1.2) = d - c := by
            calc
              A (f w.1.1) - A (f w.1.2) =
                  (c + A (f w.1.1)) - (c + A (f w.1.2)) := by abel
              _ = (d + A (f w.1.2)) - (c + A (f w.1.2)) := by rw [hw]
              _ = d - c := by abel
          have hdiff : f z.1.1 - f z.1.2 = f w.1.1 - f w.1.2 := by
            apply hA
            rw [map_sub, map_sub]
            exact hz'.trans hw'.symm
          calc
            f z.1.1 = (f z.1.1 - f z.1.2) + f z.1.2 :=
              (sub_add_cancel _ _).symm
            _ = (f w.1.1 - f w.1.2) + f z.1.2 := by rw [hdiff]
            _ = f z.1.2 + (f w.1.1 - f w.1.2) := add_comm _ _⟩
        inj' := by
          intro z z' h
          apply Subtype.ext
          exact congrArg
            (fun t : {z : α × α // f z.1 = f z.2 + l} => t.1) h }
    calc
      Fintype.card {z : α × α // c + A (f z.1) = d + A (f z.2)} ≤
          Fintype.card {z : α × α // f z.1 = f z.2 + l} :=
        Fintype.card_le_of_embedding e
      _ = finiteFiberCorrelation f l :=
        (finiteFiberCorrelation_eq_card f l).symm
      _ ≤ finiteFiberEnergy f := finiteFiberCorrelation_le_energy f l
  · letI : IsEmpty {z : α × α // c + A (f z.1) = d + A (f z.2)} :=
      not_nonempty_iff.mp hne
    have hcard : Fintype.card {z : α × α // c + A (f z.1) = d + A (f z.2)} = 0 :=
      Fintype.card_eq_zero
    omega

theorem finiteFiberEnergy_le_of_domain_embedding
    {α α' β : Type*} [Fintype α] [Fintype α'] [Fintype β]
    [DecidableEq β] (e : α ↪ α') (f : α' → β) :
    finiteFiberEnergy (f ∘ e) ≤ finiteFiberEnergy f := by
  rw [finiteFiberEnergy_eq_card, finiteFiberEnergy_eq_card]
  let E : {z : α × α // (f ∘ e) z.1 = (f ∘ e) z.2} ↪
      {z : α' × α' // f z.1 = f z.2} :=
    { toFun := fun z => ⟨(e z.1.1, e z.1.2), z.2⟩
      inj' := by
        intro z w h
        apply Subtype.ext
        apply Prod.ext
        · exact e.injective (congrArg (fun t => t.1.1) h)
        · exact e.injective (congrArg (fun t => t.1.2) h) }
  exact Fintype.card_le_of_embedding E

end

end RHTower.Sieve

