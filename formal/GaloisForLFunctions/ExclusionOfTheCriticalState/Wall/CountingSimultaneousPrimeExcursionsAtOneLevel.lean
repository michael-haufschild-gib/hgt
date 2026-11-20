import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.FiniteWeakMomentComparison
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositePrimeExcursionsOnOneFixedBand

/-!
# A single product threshold in the opposite prime excursions

For each forced joint moment there is an observed product level whose
height times its number of exceedances recovers the moment up to
1+2 log L. Both discrepancies at each exceedance use the same numerator.
This replaces a mixed first moment by a cardinality question without
changing a polynomial exponent.
-/

noncomputable section
open Finset Filter
open scoped Topology
open GaloisForLFunctions.FiniteWeakMoment
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- The product height at H times the number of eligible numerators
attaining at least that height. -/
def jointPrimeLevel (left : Bool) (s a g d T : ℝ) (k L H : ℕ) : ℝ :=
  levelMass (largeOppositePrimeNumerators left s a g d T k L)
    (oppositePrimeProduct left s k L) H

/-- One product level of a nonempty joint sample controls the complete
mixed moment, with an explicit logarithmic loss in the band endpoint. -/
theorem opposite_moment_at_one_level (left : Bool) (s a g d T : ℝ) (k L : ℕ)
    (hne : (largeOppositePrimeNumerators left s a g d T k L).Nonempty) :
    ∃ H ∈ largeOppositePrimeNumerators left s a g d T k L,
      (L:ℝ)*(∑ j ∈ largeOppositePrimeNumerators left s a g d T k L,
        oppositePrimeProduct left s k L j) ≤
      (1+2*Real.log L)*((L:ℝ)*jointPrimeLevel left s a g d T k L H) := by
  let S := largeOppositePrimeNumerators left s a g d T k L
  let f := oppositePrimeProduct left s k L
  have hf (j : ℕ) : 0 ≤ f j := div_nonneg (mul_nonneg (le_max_left ..) (le_max_left ..)) (sq_nonneg _)
  obtain ⟨H,hH,hh,_⟩ := exists_capturing_level hne f (fun j _ => hf j)
  have hs : S ⊆ range (L^2) := (filter_subset _ _).trans (filter_subset _ _)
  have hn := card_le_card hs
  rw [card_range] at hn
  have hr : (0:ℝ) < S.card := Nat.cast_pos.mpr (card_pos.mpr hne)
  have hlog := Real.log_le_log hr (Nat.cast_le.mpr hn)
  rw [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at hlog
  have hconst : (harmonic S.card:ℝ) ≤ 1+2*Real.log L :=
    (harmonic_le_one_add_log S.card).trans (add_le_add (le_refl 1) hlog)
  have hp : 0 ≤ levelMass S f H := mul_nonneg (hf H) (Nat.cast_nonneg _)
  refine ⟨H,hH,?_⟩
  have h := mul_le_mul_of_nonneg_left
    (hh.trans (mul_le_mul_of_nonneg_right hconst hp)) (Nat.cast_nonneg L : 0 ≤ (L:ℝ))
  exact h.trans_eq (by ring)

/-- A failure of RH forces a large single-level count for every sufficiently
small band width. The level and orientation may vary with the scale. -/
theorem rh_or_large_joint_prime_level : RiemannHypothesis ∨
    ∃ a c g d r : ℝ, 0<a ∧ 0<c ∧ 0<g ∧ 0<d ∧ d≤1/4 ∧ 0 < r ∧
      ∀ η : ℝ, 0<η → η ≤ r → ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η)≤Real.log (k i) ∧ Real.log (k i)≤T i) ∧
        let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
        ∀ᶠ i in atTop, ∃ (s : ℝ) (left : Bool) (H : ℕ), (s=1 ∨ s= -1) ∧
          H ∈ largeOppositePrimeNumerators left s a g d (T i) (k i) (L i) ∧
          c*a^2*Real.exp ((1/2+3*g)*T i) < (1+2*Real.log (L i))*
            ((L i:ℝ)*jointPrimeLevel left s a g d (T i) (k i) (L i) H) := by
  obtain hr | ⟨_,_,_,a,c,g,d,r,_,_,_,_,_,ha,hc,hg,hd,hd₁,hr,hseq⟩ :=
    riemannHypothesis_or_fixed_band_opposite_prime_moment
  · exact Or.inl hr
  refine Or.inr ⟨a,c,g,d,r,ha,hc,hg,hd,hd₁,hr,fun η hη hηr => ?_⟩
  obtain ⟨T,k,hT,hk,_,hs⟩ := hseq η hη hηr
  let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
  refine ⟨T,k,hT,hk,?_⟩
  filter_upwards [hs] with i hi
  obtain ⟨_,_,s,left,_,_,hsign,_,_,_,_,_,hp⟩ := hi
  let S := largeOppositePrimeNumerators left s a g d (T i) (k i) (L i)
  have hne : S.Nonempty := by
    by_contra! hempty
    change _ < (L i:ℝ)*(∑ j ∈ S, oppositePrimeProduct left s (k i) (L i) j) at hp
    rw [hempty,sum_empty,mul_zero] at hp
    exact (not_lt_of_ge (by positivity)) hp
  obtain ⟨H,hH,h⟩ := opposite_moment_at_one_level left s a g d (T i) (k i) (L i) hne
  exact ⟨s,left,H,hsign,hH,hp.trans_le h⟩

#print axioms opposite_moment_at_one_level
#print axioms rh_or_large_joint_prime_level

end GaloisForLFunctions.ExclusionOfTheCriticalState
