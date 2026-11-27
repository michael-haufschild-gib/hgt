import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Packets

/-! # Accumulation of one-comparison false positives at the isometric splitting line -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing

open Finset Real Set
open _root_.HTGeometry (finiteGibbsPartition finiteGibbsStateWeight)

/-- Opposite order-one readings of centered information from a single composite Gibbs
law, evaluated at the damping selected by the prime-gas splitting parameter. -/
def sameReading (S : Finset Nat.Primes) (C : ℝ) (k l : ℕ) (s : ℂ) : Prop :=
  let E := labelEnergy (elementary (S := S))
  let Y := centered (Observation.information (finiteGibbsStateWeight (2*s.re-1) (Mixed.mixedEnergy E C k l)))
  finiteGibbsPartition 1 Y=finiteGibbsPartition (-1) Y

private theorem one_comparison {I : Type*} [Fintype I] (E : I → ℝ) :
    HeatTests E 1 ↔ finiteGibbsPartition 1 E=finiteGibbsPartition (-1) E := by
  refine ⟨fun h => by simpa only [Nat.cast_one] using h 1 le_rfl le_rfl,?_⟩
  intro h j lo hi
  obtain rfl := le_antisymm hi lo
  simpa only [Nat.cast_one] using h

/-- With unequal particle and hole counts a one-probe coincidence on one copy is
preserved for every mixture and every choice of the complementary-energy constant. -/
theorem sameReading_iff (S : Finset Nat.Primes) (C : ℝ) (k l : ℕ) (s : ℂ) :
    sameReading S C k l s ↔ k=l ∨ Coincides (elementary (S := S)) (2*s.re-1) := by
  unfold sameReading
  rw [← one_comparison,Observation.centered_joint_information,Observation.mixed_tests,one_comparison]
  apply or_congr_right
  simp only [Coincides,finiteGibbsPartition,neg_neg,neg_mul,one_mul]

/-- Arbitrarily near each point of the critical line there exist nonisometric splittings
that pass this single comparison for every particle and hole count. Five distinct prime
modes suffice, and their labels may all exceed an arbitrary cutoff. -/
theorem near_line (n M : ℕ) (hn : 5≤n) (y : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ (S : Finset Nat.Primes) (s : ℂ), S.card=n ∧ (∀ p ∈ S, M<p.val) ∧ s.im=y ∧
      s.re-1/2 ∈ Ioo (0 : ℝ) ε ∧ Irrational (2*s.re-1) ∧
      (¬∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ∧
      ∀ C k l, sameReading S C k l s := by
  obtain ⟨S,size,above,t,ht,irr,eq⟩ := small_crossing n M hn (show 0<2*ε by linarith only [hε])
  let s : ℂ := ⟨(1+t)/2,y⟩
  have re : s.re=(1+t)/2 := rfl
  have damping : 2*s.re-1=t := by rw [re]; ring
  refine ⟨S,s,size,above,rfl,⟨?_,?_⟩,damping ▸ irr,?_,?_⟩
  · rw [re]; linarith only [ht.1]
  · rw [re]; linarith only [ht.2]
  · rw [split_isometric_iff,re]
    intro eqline
    linarith only [eqline,ht.1]
  · intro C k l
    rw [sameReading_iff,damping]
    exact Or.inr eq

#print axioms sameReading_iff
#print axioms near_line

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing
