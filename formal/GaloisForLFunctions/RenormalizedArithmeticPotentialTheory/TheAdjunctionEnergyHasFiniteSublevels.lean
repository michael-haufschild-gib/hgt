import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanAdjunctionEnergiesAreDistinct

/-!
# Properness of the arithmetic adjunction energy

The nonnegative tame correction leaves logarithmic conductor growth as a lower
bound. Thus bounded energy windows contain only finitely many positive conductors.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

theorem log_le_ramanujanAdjunctionEnergy_sub (m : ℕ) :
    Real.log m ≤ ramanujanAdjunctionEnergy m - Real.eulerMascheroniConstant := by
  rw [ramanujanAdjunctionEnergy]
  linarith only [tameDifferent_nonneg m]

/-- Each bounded arithmetic energy sublevel contains finitely many conductors. -/
theorem finite_ramanujanAdjunctionEnergy_sublevel (T : ℝ) :
    {m : ℕ | 0 < m ∧ ramanujanAdjunctionEnergy m < T}.Finite := by
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp (T - Real.eulerMascheroniConstant))
  refine (Set.finite_Iio K).subset ?_
  intro m hm
  have hlog : Real.log m < T - Real.eulerMascheroniConstant :=
    (log_le_ramanujanAdjunctionEnergy_sub m).trans_lt (sub_lt_sub_right hm.2 _)
  have hmexp : (m : ℝ) < Real.exp (T - Real.eulerMascheroniConstant) :=
    (Real.log_lt_iff_lt_exp (by exact_mod_cast hm.1)).mp hlog
  exact_mod_cast hmexp.trans hK

/-- The exact finite conductor set below an energy threshold. -/
def adjunctionEnergySublevel (T : ℝ) : Finset ℕ :=
  (finite_ramanujanAdjunctionEnergy_sublevel T).toFinset

@[simp] theorem mem_adjunctionEnergySublevel (T : ℝ) (m : ℕ) :
    m ∈ adjunctionEnergySublevel T ↔ 0 < m ∧ ramanujanAdjunctionEnergy m < T := by
  simp only [adjunctionEnergySublevel, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- A finite strict sublevel stays a positive distance below its threshold. -/
theorem exists_pos_gap_above_adjunctionEnergySublevel (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m ∈ adjunctionEnergySublevel T,
      ramanujanAdjunctionEnergy m + δ < T := by
  have hfinite : ∀ S : Finset ℕ, (∀ m ∈ S, ramanujanAdjunctionEnergy m < T) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ m ∈ S, ramanujanAdjunctionEnergy m + δ < T := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, zero_lt_one, fun m hm => by simp at hm⟩
    | @insert m S hm ih =>
      intro hS
      obtain ⟨δ, hδ, hgap⟩ := ih (fun n hn => hS n (mem_insert_of_mem hn))
      have hmT := hS m (mem_insert_self m S)
      refine ⟨min δ ((T - ramanujanAdjunctionEnergy m) / 2),
        lt_min hδ (by linarith only [hmT]), fun n hn => ?_⟩
      rcases mem_insert.mp hn with hnm | hn
      · subst n
        have h := min_le_right δ ((T - ramanujanAdjunctionEnergy m) / 2)
        linarith only [h, hmT]
      · have h := min_le_left δ ((T - ramanujanAdjunctionEnergy m) / 2)
        linarith only [h, hgap n hn]
  exact hfinite (adjunctionEnergySublevel T) fun m hm => (mem_adjunctionEnergySublevel T m).mp hm |>.2

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

