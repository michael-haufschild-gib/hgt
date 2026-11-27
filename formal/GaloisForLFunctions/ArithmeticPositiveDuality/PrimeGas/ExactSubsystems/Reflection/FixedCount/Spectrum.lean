import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Capacity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HeatTrace
import GaloisForLFunctions.HTGeometry.InfiniteOccupationLaw

/-! # Classification of energy reflections for bounded prime occupations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount

open Finset

/-- The integer energy label retains every coordinate of the packet. -/
def integerLabel (S : Finset Nat.Primes) (x : S → ℕ) : ℕ+ :=
  label ((_root_.HTGeometry.supportedOccupationEquiv S) x).val

theorem integerLabel_injective (S : Finset Nat.Primes) : Function.Injective (integerLabel S) :=
  fun _ _ h => (_root_.HTGeometry.supportedOccupationEquiv S).injective (Subtype.ext (label.injective h))

theorem integerLabel_add (S : Finset Nat.Primes) (x y : S → ℕ) :
    integerLabel S (x+y) = integerLabel S x * integerLabel S y := by
  unfold integerLabel
  rw [← label_add]
  apply congrArg label
  let e := _root_.HTGeometry.finsetSubtypeEmbedding S
  change Finsupp.embDomain e (Finsupp.equivFunOnFinite.symm (x+y)) =
    Finsupp.embDomain e (Finsupp.equivFunOnFinite.symm x) + Finsupp.embDomain e (Finsupp.equivFunOnFinite.symm y)
  rw [← Finsupp.embDomain_add]
  congr 1
  ext i
  rfl

private theorem energyLabel_injective (S : Finset Nat.Primes) :
    Function.Injective (fun u => energy (integerLabel S u)) := by
  intro x y h
  apply integerLabel_injective S
  apply PNat.coe_injective
  have he := congrArg Real.exp h
  simp only [energy, Real.exp_log (Nat.cast_pos.mpr (integerLabel S x).pos),
    Real.exp_log (Nat.cast_pos.mpr (integerLabel S y).pos)] at he
  exact_mod_cast he

variable {S : Finset Nat.Primes} {c : S → ℕ} {m : ℕ}

def level (x : State c m) := integerLabel S (count x)

theorem level_injective : Function.Injective (level (c := c) (m := m)) :=
  fun _ _ h => state_ext (congrFun (integerLabel_injective S h))

/-- The sector contains a state and its energies reflect about a single center. -/
def Reflects (S : Finset Nat.Primes) (c : S → ℕ) (m : ℕ) : Prop :=
  Nonempty (State c m) ∧ ∃ L : ℝ, ∃ R : Equiv.Perm (State c m),
    ∀ x, energy (level x) + energy (level (R x)) = L

/-- Equal paired energies first give equal integer products, then equal paired prime counts.
Attainment of both coordinate endpoints determines every one of those counts. -/
theorem reflecting_map_counts (hne : Nonempty (State c m)) (f : State c m → State c m)
    {L : ℝ} (hf : ∀ x, energy (level x) + energy (level (f x)) = L) (x : State c m) (i : S) :
    count x i + count (f x) i = pairCount c m i := by
  obtain ⟨z⟩ := hne
  let a := count z + count (f z)
  have same (y : State c m) : count y + count (f y) = a := by
    apply energyLabel_injective S
    simp only [a, integerLabel_add, energy_mul]
    exact (hf y).trans (hf z).symm
  have eqv (y : State c m) (j : S) : count y j + count (f y) j = a j := congrFun (same y) j
  exact (eqv x i).trans (congrFun (forced_pair_count ⟨z⟩ f a eqv) i)

/-- All pairs under the explicit occupation reversal have the same integer product. -/
theorem reversal_product (h : ∑ i, pairCount c m i = 2*m) (x : State c m) :
    level x * level (reversal h x) = integerLabel S (pairCount c m) := by
  rw [level, level, ← integerLabel_add]
  exact congrArg (integerLabel S) (funext (partner_pair h x))

/-- Necessary and sufficient arithmetic conditions for an energy-reflecting prime sector. -/
theorem reflection_iff (S : Finset Nat.Primes) (c : S → ℕ) (m : ℕ) :
    Reflects S c m ↔ m ≤ capacity c ∧ (∑ i, pairCount c m i) = 2*m := by
  constructor
  · rintro ⟨hne, L, R, h⟩
    refine ⟨(feasible_iff c m).mp hne, ?_⟩
    obtain ⟨x⟩ := hne
    calc _ = ∑ i, (count x i + count (R x) i) :=
             sum_congr rfl fun i _ => (reflecting_map_counts ⟨x⟩ R h x i).symm
         _ = _ := by rw [sum_add_distrib, count_sum, count_sum]; omega
  · rintro ⟨hm, h⟩
    exact ⟨(feasible_iff c m).mpr hm, energy (integerLabel S (pairCount c m)), reversal h,
      fun x => (energy_mul _ _).symm.trans (congrArg energy (reversal_product h x))⟩

/-- Every reflecting self-map agrees with the canonical involution, including at single-state sectors. -/
theorem reflecting_map_unique (h : ∑ i, pairCount c m i = 2*m) (f : State c m → State c m)
    {L : ℝ} (hf : ∀ x, energy (level x) + energy (level (f x)) = L) :
    f = (reversal h : State c m → State c m) := by
  funext x
  exact state_ext fun i => Nat.add_left_cancel
    ((reflecting_map_counts ⟨x⟩ f hf x i).trans (partner_pair h x i).symm)

#print axioms integerLabel_injective
#print axioms reversal_product
#print axioms reflection_iff
#print axioms reflecting_map_unique

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount
