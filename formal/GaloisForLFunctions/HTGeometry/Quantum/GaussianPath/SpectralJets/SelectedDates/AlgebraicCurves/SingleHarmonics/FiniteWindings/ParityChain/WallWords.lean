import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Domain walls of an open Ising chain with two fixed boundary spins -/

namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings.ParityChain

/-- Differences between consecutive spins, including the return to false
at the right endpoint. The left endpoint has prescribed value p. -/
def walls (p : Bool) : List Bool→List Bool
  | [] => [p]
  | b::s => (p ^^ b)::walls b s

def parity : List Bool→Bool
  | [] => false
  | b::s => b ^^ parity s

theorem walls_length (p : Bool) (s : List Bool) : (walls p s).length=s.length+1 := by
  induction s generalizing p with
  | nil => rfl
  | cons b s ih => simp only [walls,List.length_cons,ih]

/-- Every wall word has the parity determined by its two endpoints. -/
theorem parity_walls (p : Bool) (s : List Bool) : parity (walls p s)=p := by
  induction s generalizing p with
  | nil => cases p <;> rfl
  | cons b s ih => simp only [walls,parity,ih]; cases p <;> cases b <;> rfl

/-- A wall word uniquely determines the underlying spins. -/
theorem walls_injective (p : Bool) : Function.Injective (walls p) := by
  intro s
  induction s generalizing p with
  | nil =>
    intro t ht
    have h := congrArg List.length ht
    simp only [walls_length,List.length_nil] at h
    exact (List.length_eq_zero_iff.mp (by omega)).symm
  | cons b s ih =>
    rintro (_|⟨c,t⟩) ht
    · have h := congrArg List.length ht
      simp only [walls_length,List.length_cons,List.length_nil] at h
      omega
    · obtain ⟨h₁,h₂⟩ := List.cons.inj ht
      have hbc : b=c := by cases p <;> cases b <;> cases c <;> simp_all
      subst c
      exact congrArg (List.cons b) (ih b h₂)

/-- Conversely, every nonempty word with the prescribed parity occurs,
including the two constant words whenever their parities agree. -/
theorem walls_realize (p : Bool) (w : List Bool) (hw : w≠[]) (hp : parity w=p) :
    ∃! s, walls p s=w := by
  suffices ∃ s, walls p s=w by
    obtain ⟨s,hs⟩ := this
    exact ⟨s,hs,fun t ht => walls_injective p (ht.trans hs.symm)⟩
  induction w generalizing p with
  | nil => exact (hw rfl).elim
  | cons b w ih =>
    cases w with
    | nil =>
      refine ⟨[],?_⟩
      cases b <;> cases p <;> simp_all [walls,parity]
    | cons c w =>
      let v := p ^^ b
      have hv : parity (c::w)=v := by
        change b ^^ parity (c::w)=p at hp
        cases b <;> cases h : parity (c::w) <;> cases p <;> simp_all [v]
      obtain ⟨s,hs⟩ := ih v (List.cons_ne_nil ..) hv
      refine ⟨v::s,?_⟩
      simp only [walls,hs]
      cases p <;> cases b <;> rfl

/-- The number of negative signs in the wall representation is even
when both exterior spins are fixed to false. -/
theorem wall_count_even (s : List Bool) : (walls false s).count true % 2=0 := by
  have general (w : List Bool) : w.count true %2=(parity w).toNat := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      cases b <;> cases h : parity w <;> simp [parity,List.count_cons,h] at ih ⊢ <;> omega
  simpa only [parity_walls] using general (walls false s)

#print axioms walls_realize
#print axioms wall_count_even
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings.ParityChain
