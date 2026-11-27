import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Gibbs

/-! # One pair of orders for all composite prime occupation sectors -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family

open Finset Set
open FixedCount (State level capacity pairCount)
open _root_.HTGeometry (finiteGibbsStateWeight)

variable {S : Finset Nat.Primes}

private theorem energy_prod {I : Type*} (s : Finset I) (a : I → ℕ+) :
    energy (∏ i ∈ s, a i) = ∑ i ∈ s, energy (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [energy]
  | insert i s hi ih => rw [prod_insert hi,sum_insert hi,energy_mul,ih]

/-- A joint state retains one integer label for every tuple, including tuples
with the same product. Taking its energy therefore counts all degeneracies. -/
def jointLabel (c : S → ℕ) (m n k l : ℕ) (x : (Fin k → State c m) × (Fin l → State c n)) : ℕ+ :=
  (∏ i, level (x.1 i))*(∏ j, level (x.2 j))

theorem filling_integer (c : S → ℕ) (m n k l : ℕ) :
    Mixed.fillingEnergy c m n k l = energy ∘ jointLabel c m n k l := by
  funext x
  rw [Function.comp_apply,jointLabel,energy_mul,energy_prod,energy_prod]
  rfl

/-- On the measured product law the only ambiguities shared by both probes are
intrinsic occupation reversal, an infeasible filling, and balanced replication. -/
theorem filling_iff {r : ℝ} (hr : 0 < r) (good : r ∉ exceptional energy)
    (c : S → ℕ) (m k l : ℕ) (s : ℂ) :
    let P := Mixed.fillingShare c m (capacity c-m) k l s
    lawOrder P 1 ∧ lawOrder P r ↔ (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ∨
      k=l ∨ capacity c < m ∨ (∑ i, pairCount c m i)=2*m := by
  dsimp only
  let n := capacity c-m
  have law := funext (Mixed.filling_gibbs c m n k l s)
  have test := gibbs_pair energy (jointLabel c m n k l) hr good (2*s.re-1)
  dsimp only at test
  rw [← filling_integer c m n k l] at test
  have mid : 2*s.re-1=0 ↔ s.re=1/2 := by constructor <;> intro h <;> linarith only [h]
  rw [law,test,mid,split_isometric_iff,Mixed.filling_reflection_iff]

/-- Every positive interval contains a single calibration working simultaneously
for every capacity vector, filling number, replication and complex parameter. -/
theorem universal_filling {a b : ℝ} (ha : 0 ≤ a) (ab : a < b) :
    ∃ r ∈ Ioo a b, ∀ (S : Finset Nat.Primes) (c : S → ℕ) (m k l : ℕ) (s : ℂ),
      let P := Mixed.fillingShare c m (capacity c-m) k l s
      lawOrder P 1 ∧ lawOrder P r ↔ (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ∨
        k=l ∨ capacity c < m ∨ (∑ i, pairCount c m i)=2*m := by
  obtain ⟨r,between,good⟩ := good_between energy ab
  exact ⟨r,between,fun _ => filling_iff (ha.trans_lt between.1) good⟩

#print axioms filling_integer
#print axioms filling_iff
#print axioms universal_filling

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family
