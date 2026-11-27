import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Sharp.Weights
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Heat

/-! # Optimal number of consecutive centered heat-trace comparisons -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half

open Finset Real
open _root_.HTGeometry (finiteGibbsPartition)

theorem failure_at_order (n r : ℕ) (hr : 1 ≤ r) (hk : r ≤ cutoff n) :
    ∃ E : Fin n → ℝ, (∑ i, E i)=0 ∧ HeatTests E (r-1) ∧
      finiteGibbsPartition (r : ℝ) E ≠ finiteGibbsPartition (-(r : ℝ)) E := by
  obtain ⟨u,pos,prod_one,agree,fail⟩ := Sharp.exists_first_failure n r hr hk
  let E := fun i => -log (u i)
  have restore : weight E=u := by
    funext i
    exact (by simp only [weight,E,neg_neg,exp_log (pos i)])
  have sum_zero : (∑ i, E i)=0 := by
    simp only [E,sum_neg_distrib,← log_prod (fun i _ => (pos i).ne'),prod_one,log_one,neg_zero]
  have before : HeatTests E (r-1) := (heat_iff_weights E _).mpr (restore ▸ agree)
  refine ⟨E,sum_zero,before,fun at_order => ?_⟩
  have all : HeatTests E r := by
    intro j hj hjr
    rcases hjr.lt_or_eq with h | rfl
    · exact before j hj (by omega)
    · exact at_order
  have tested := (heat_iff_weights E r).mp all r hr le_rfl
  rw [restore] at tested
  exact fail tested

/-- The exact uniform cutoff, including the zero-test dimensions zero, one and two. -/
theorem sufficient_iff (n k : ℕ) :
    (∀ E : Fin n → ℝ, HeatTests (centered E) k → Reflects E) ↔ cutoff n ≤ k := by
  constructor
  · intro all
    by_contra! small
    obtain ⟨E,hs,tested,fail⟩ := failure_at_order n (k+1) (by omega) (by omega)
    have center := centered_eq_of_sum_zero hs
    have ref := all E (by simpa only [center,Nat.add_sub_cancel] using tested)
    have full := (centered_heat_iff_reflects E).mpr ref
    rw [center,Fintype.card_fin] at full
    exact fail (full (k+1) (by omega) (by omega))
  · intro sufficient E tested
    apply (centered_heat_iff_reflects E).mp
    intro j hj hjn
    rw [Fintype.card_fin] at hjn
    exact tested j hj (hjn.trans sufficient)

#print axioms failure_at_order
#print axioms sufficient_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half
