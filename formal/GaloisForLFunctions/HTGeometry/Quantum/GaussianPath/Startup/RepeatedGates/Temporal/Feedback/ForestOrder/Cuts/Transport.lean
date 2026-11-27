import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.Cuts.Certificate

/-! # Transport of a directed cut through a component merger -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
variable {V : Type*} [DecidableEq V]
variable {R T : V→V→Prop} {A C : Finset V} {a : V} {S : Finset (Port V)}

/-- Transmission either stays in the old component, or enters its joining
output. An input that leaves must already have reached that output. -/
def SideRule (R T : V→V→Prop) (A : Finset V) (a : V) :=
  ∀ i j, T i j → (i∈A ∧ j∈A ∧ R i j) ∨ ((i∈A → R i a) ∧ (j∈A → j=a))

omit [DecidableEq V] in
theorem lift_noExit (h : SideRule R T A a) (ha : a∈A) (hs : S⊆ports A)
    (hp : Sum.inr a∉S) (he : NoExit R A S) : NoExit T C S := by
  intro i _ j _ hij hi
  rcases h i j hij with ⟨hiA,hjA,hr⟩|⟨hout,_⟩
  · exact he i hiA j hjA hr hi
  · have hiA := inl_mem_disjSum.mp (hs hi)
    exact (hp (he i hiA a ha (hout hiA) hi)).elim

omit [DecidableEq V] in
theorem lift_noEntry (h : SideRule R T A a) (hs : S⊆ports A)
    (hp : Sum.inr a∉S) (he : NoEntry R A S) : NoEntry T C S := by
  intro i _ j _ hij hj
  rcases h i j hij with ⟨hiA,hjA,hr⟩|⟨_,hin⟩
  · exact he i hiA j hjA hr hj
  · exact (hp (hin (inr_mem_disjSum.mp (hs hj)) ▸ hj)).elim

/-- All outputs outside A have the same membership in a rerooted cut as
the joining output. This transports a separator at either new output. -/
theorem lift_separator (h : SideRule R T A a) (ha : a∈A) (hs : S⊆ports A)
    (hp : Sum.inr a∉S) (i j : V)
    (he : Separates R A S i (if j∈A then j else a)) : Separates T C S i j := by
  have hm : Sum.inr (if j∈A then j else a)∈S ↔ Sum.inr j∈S := by
    by_cases hj : j∈A
    · simp only [if_pos hj]
    · simp only [if_neg hj]
      exact iff_of_false hp (fun hy => hj (inr_mem_disjSum.mp (hs hy)))
  rcases he with ⟨hx,hy,he⟩|⟨hx,hy,he⟩
  · exact Or.inl ⟨hx,fun hh => hy (hm.mpr hh),lift_noExit h ha hs hp he⟩
  · exact Or.inr ⟨hx,hm.mp hy,lift_noEntry h hs hp he⟩

/-- Deleting the joining output leaves every other output protected
against incoming signals from outside the old component. -/
def wall (A : Finset V) (a : V) := (ports A).erase (Sum.inr a)

theorem wall_noEntry (h : SideRule R T A a) : NoEntry T C (wall A a) := by
  intro i _ j _ hij hy
  obtain ⟨hne,hj⟩ := mem_erase.mp hy
  rcases h i j hij with ⟨hi,_,_⟩|⟨_,hin⟩
  · exact mem_erase.mpr ⟨Sum.inl_ne_inr,inl_mem_disjSum.mpr hi⟩
  · exact (hne (congrArg Sum.inr (hin (inr_mem_disjSum.mp hj)))).elim

theorem wall_separates (h : SideRule R T A a) {i j : V} (hi : i∉A) (hj : j∈A)
    (hne : j≠a) : Separates T C (wall A a) i j := by
  exact Or.inr ⟨fun hh => hi (inl_mem_disjSum.mp (mem_erase.mp hh).2),
    mem_erase.mpr ⟨fun he => hne (Sum.inr.inj he),inr_mem_disjSum.mpr hj⟩,wall_noEntry h⟩

#print axioms lift_separator
#print axioms wall_separates
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
