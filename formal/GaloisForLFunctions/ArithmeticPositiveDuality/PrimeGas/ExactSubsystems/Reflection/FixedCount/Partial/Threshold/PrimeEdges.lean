import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Faces
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Mirror

/-! # Spectral edge differences of an arbitrary bounded prime packet -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold

open Finset Real

variable {S : Finset Nat.Primes}

abbrev price (i : S) := Peak.primeEnergy i
abbrev reversePrice (i : S) := -price i

theorem price_injective (S : Finset Nat.Primes) : Function.Injective (price (S := S)) := by
  intro i j h
  have hh := congrArg exp h
  simp only [price,Peak.primeEnergy,exp_log (Nat.cast_pos.mpr i.val.property.pos),
    exp_log (Nat.cast_pos.mpr j.val.property.pos)] at hh
  apply Subtype.ext
  apply Subtype.ext
  exact_mod_cast hh

theorem reversePrice_injective (S : Finset Nat.Primes) : Function.Injective (reversePrice (S := S)) :=
  fun _ _ h => price_injective S (neg_injective h)

variable {c : S → ℕ} {m : ℕ}

theorem prime_cost (x : State c m) : linearCost price (count x) = energy (level x) := by
  let y : Peak.Boson S m := ⟨fun i => ⟨count x i,Nat.lt_succ_of_le
    ((count_interval x i).2.trans (min_le_left _ _))⟩,count_sum x⟩
  rw [show level x = level y from rfl,Peak.energy_eq_read]
  rfl

theorem reverse_cost (x : State c m) : linearCost reversePrice (count x) = -energy (level x) := by
  rw [← prime_cost x]
  simp only [linearCost,reversePrice,mul_neg,sum_neg_distrib]

/-- Coordinate sums of the two explicit greedy anchors. -/
def center (c : S → ℕ) (m : ℕ) (i : S) := ordinary price c m i + ordinary reversePrice c m i

def lowerEdge (c : S → ℕ) (m : ℕ) :=
  Set.range fun x : State c m => energy (level x)-baseline price c m

def upperEdge (c : S → ℕ) (m : ℕ) :=
  Set.range fun x : State c m => -energy (level x)-baseline reversePrice c m

def differences (A B : Set ℝ) := (A \ B) ∪ (B \ A)

theorem anchors (x : State c m) : ∃ g u : State c m,
    count g = ordinary price c m ∧ count u = ordinary reversePrice c m ∧
    baseline price c m = energy (level g) ∧ baseline reversePrice c m = -energy (level u) ∧
    ∀ y : State c m, energy (level g) ≤ energy (level y) ∧ energy (level y) ≤ energy (level u) := by
  obtain ⟨g,hg,lo⟩ := original_minimum price (price_injective S) x
  obtain ⟨u,hu,hi⟩ := original_minimum reversePrice (reversePrice_injective S) x
  refine ⟨g,u,hg,hu,?_,?_,?_⟩
  · rw [baseline,← hg,prime_cost]
  · rw [baseline,← hu,reverse_cost]
  · intro y
    exact ⟨by simpa only [prime_cost] using lo y,by simpa only [reverse_cost,neg_le_neg_iff] using hi y⟩

private theorem missing (g u x : State c m) (hg : count g = ordinary price c m)
    (hu : count u = ordinary reversePrice c m) :
    violates (center c m) x ↔ ¬∃ y : State c m,
      energy (level x)+energy (level y) = energy (level g)+energy (level u) := by
  have hp : (∃ y : State c m, energy (level x)+energy (level y) = energy (level g)+energy (level u)) ↔
      Inside g u x := by
    constructor
    · rintro ⟨y,hy⟩ i
      have h := (energy_pair_iff g u x y).mp hy i
      have hc := count_cap y i
      omega
    · intro h
      exact ((unique_partner_iff g u x).mpr h).exists
  rw [hp]
  simp only [violates,Inside,center,← hg,← hu,not_forall,not_and_or,not_le]

/-- Arithmetic coordinate violations give both directed differences, before combining their minima. -/
theorem directed_differences (c : S → ℕ) (m : ℕ) :
    lowerEdge c m \ upperEdge c m = outsideOffsets price c (center c m) m ∧
    upperEdge c m \ lowerEdge c m = outsideOffsets reversePrice c (center c m) m := by
  classical
  by_cases hn : Nonempty (State c m)
  · obtain ⟨w⟩ := hn
    obtain ⟨g,u,hg,hu,lo,hi,_⟩ := anchors w
    have lower (x : State c m) : energy (level x)-baseline price c m ∉ upperEdge c m ↔
        violates (center c m) x := by
      rw [missing g u x hg hu]
      apply not_congr
      constructor <;> rintro ⟨y,hy⟩ <;> refine ⟨y,?_⟩
      · change -energy (level y)-baseline reversePrice c m = _ at hy
        linarith only [lo,hi,hy]
      · change -energy (level y)-baseline reversePrice c m = _
        linarith only [lo,hi,hy]
    have upper (x : State c m) : -energy (level x)-baseline reversePrice c m ∉ lowerEdge c m ↔
        violates (center c m) x := by
      rw [missing g u x hg hu]
      apply not_congr
      constructor <;> rintro ⟨y,hy⟩ <;> refine ⟨y,?_⟩
      · change energy (level y)-baseline price c m = _ at hy
        linarith only [lo,hi,hy]
      · change energy (level y)-baseline price c m = _
        linarith only [lo,hi,hy]
    constructor <;> ext z
    · constructor
      · rintro ⟨⟨x,rfl⟩,hx⟩
        exact ⟨x,(lower x).mp hx,by rw [prime_cost]⟩
      · rintro ⟨x,hx,rfl⟩
        rw [prime_cost]
        exact ⟨⟨x,rfl⟩,(lower x).mpr hx⟩
    · constructor
      · rintro ⟨⟨x,rfl⟩,hx⟩
        exact ⟨x,(upper x).mp hx,by rw [reverse_cost]⟩
      · rintro ⟨x,hx,rfl⟩
        rw [reverse_cost]
        exact ⟨⟨x,rfl⟩,(upper x).mpr hx⟩
  · constructor <;> ext z <;> constructor
    all_goals first | rintro ⟨⟨x,_⟩,_⟩; exact (hn ⟨x⟩).elim | rintro ⟨x,_,_⟩; exact (hn ⟨x⟩).elim

#print axioms anchors
#print axioms directed_differences

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold
