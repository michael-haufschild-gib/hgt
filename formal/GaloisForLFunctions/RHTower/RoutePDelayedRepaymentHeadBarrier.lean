import GaloisForLFunctions.RHTower.RoutePReciprocalHeadMoment
import GaloisForLFunctions.RHTower.MobiusDivisorInheritedPrimeInsertionProducer

/-!
# Actual inherited debt cannot be repaired arbitrarily late within one critical budget

The corpus produces actual omitted primes carrying positive inherited debt.
Successful sufficiently delayed half repayment requires positive reciprocal
helper mass. The reciprocal head moment then forces a later spike of the
literal retained head itself, with every original coefficient preserved.

No restriction on helper cardinality, upper clock, phase, or half-weight mass
is imposed. This obstructs delayed all-cutoff repair; it does not exclude
jointly moving core/cutoff constructions or falsify the native Route-P floor.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower

/-- Actual inherited debts cannot be repaid arbitrarily late under one critical
energy budget. Every successful late half repayment forces a later discrete spike. -/
theorem routeP_delayed_repayment_forces_actual_head_spike :
    ∀ P : Finset ℕ, P.Nonempty → (∀ p ∈ P, p.Prime) → Even P.card → ∀ N : ℕ,
      ∃ r : ℕ, ∃ δ : ℝ, r.Prime ∧ N < r ∧ r ∉ P ∧ 0 < δ ∧
        (∑' n, mobiusDivisorFixedCoreBlockMass P n)+2*δ =
          ∑' n, mobiusDivisorFixedCoreBlockMass (insert r P) n ∧
        ∀ K : ℝ, 0 ≤ K → ∃ τ₁ : ℝ, ∀ τ : ℝ, τ₁ ≤ τ → ∀ S : Finset ℕ,
          (∀ p ∈ S, p.Prime ∧ τ < Real.log p) →
          (∑' n, mobiusDivisorFixedCoreBlockMass (insert r (P ∪ S)) n) ≤
            (∑' n, mobiusDivisorFixedCoreBlockMass P n)+δ →
          ∃ M : ℕ, Real.exp τ < (M : ℝ) ∧
            K*(M : ℝ)^2 < mobiusDivisorSelectionFibre M (insert r (P ∪ S)) ∅ ^ 2 := by
  intro P hP hprime heven N
  obtain ⟨r,δ,η,_,_,τ₀,hr,hNr,hrP,hδ,hη,_,_,hgap,hcost,_⟩ :=
    exists_mobiusDivisorClockDelayedInsertionProducer P hP hprime heven N
  refine ⟨r,δ,hr,hNr,hrP,hδ,hgap,?_⟩
  intro K hK
  let Q := insert r P
  have hQ : ∀ q ∈ Q, q.Prime := by simpa [Q] using And.intro hr hprime
  obtain ⟨B,hB,hspike⟩ := routeP_fresh_reciprocal_mass_forces_head_spike Q hQ hη hK
  let L := (∑ q ∈ Q, (q : ℝ))+1
  have hL : 0 < L := by dsimp [L]; positivity
  let R := max B L
  have hR : 0 < R := hL.trans_le (le_max_right _ _)
  refine ⟨max τ₀ (Real.log R), ?_⟩
  intro τ hτ S hS hrepay
  have hτ₀ : τ₀ ≤ τ := (le_max_left _ _).trans hτ
  have hRτ : R ≤ Real.exp τ := by
    calc
      R = Real.exp (Real.log R) := (Real.exp_log hR).symm
      _ ≤ _ := Real.exp_le_exp.mpr ((le_max_right _ _).trans hτ)
  have hBτ : B ≤ Real.exp τ := (le_max_left _ _).trans hRτ
  have hfresh : ∀ p ∈ S, Real.exp τ < (p : ℝ) := by
    intro p hp
    exact (Real.lt_log_iff_exp_lt (by exact_mod_cast (hS p hp).1.pos)).mp (hS p hp).2
  have hdis : Disjoint Q S := by
    apply Finset.disjoint_left.mpr
    intro p hpQ hpS
    have hpSum : (p : ℝ) ≤ ∑ q ∈ Q, (q : ℝ) :=
      Finset.single_le_sum (fun q _ => Nat.cast_nonneg q) hpQ
    have hpR : (p : ℝ) < R := by
      have hpL : (p : ℝ) < L := by dsimp [L]; linarith
      exact hpL.trans_le (le_max_right _ _)
    exact (not_lt_of_ge (hpR.le.trans hRτ)) (hfresh p hpS)
  have hmass0 := (hcost τ hτ₀ S hS hrepay).1
  have hmass : η ≤ ∑ p ∈ S, 1/(p : ℝ) := by
    apply hmass0.le.trans
    apply sum_le_sum
    intro p hp
    exact one_div_le_one_div_of_le (by exact_mod_cast (hS p hp).1.pos) (by linarith)
  obtain ⟨M,hM,hE⟩ := hspike (Real.exp τ) hBτ S (fun p hp => (hS p hp).1) hdis hfresh hmass
  refine ⟨M,hM,?_⟩
  simpa only [Q, Finset.insert_union] using hE

end RHTower

