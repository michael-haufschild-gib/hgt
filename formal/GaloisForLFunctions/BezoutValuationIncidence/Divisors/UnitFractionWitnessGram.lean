import GaloisForLFunctions.BezoutValuationIncidence.Divisors.CongruenceClassesOfUnitFractionWitnesses
import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerSuccessorForcesTheHeckeWeight
import Mathlib.Algebra.Order.Chebyshev

/-!
# The exact Gram matrix of Type II unit-fraction events

Trybushnyi's square sieve counts intersections of witnesses. On any common
period the signed second moment is a quadratic form whose entries are
computed from the two moduli and offsets alone. Cauchy–Schwarz gives a
coverage bound for arbitrary real weights, including overlapping composite
moduli.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event

instance (e : Event) (n : ℤ) : Decidable (e.holds n) :=
  inferInstanceAs (Decidable (e.modulus ∣ n*(e.c : ℤ)+e.a))

def indicator (e : Event) (n : ℤ) : ℝ := if e.holds n then 1 else 0

private theorem class_iff (e : Event) (n : ℤ) : n ≡ e.residue [ZMOD e.modulus] ↔ e.holds n :=
  Int.modEq_comm.trans (holds_iff e n).symm

/-- Intersection count over a full period P from the congruence compatibility test. -/
def gramEntry (P : ℤ) (e f : Event) : ℤ :=
  if (e.modulus.gcd f.modulus : ℤ) ∣ f.residue-e.residue then P / e.modulus.lcm f.modulus else 0

private theorem pos_of_period {P : ℤ} (e : Event) (hP : 0 < P) (hp : e.modulus ∣ P) :
    0 < e.modulus := by
  have hpos : 0 < (e.K : ℤ)*e.a*e.c*e.d := by positivity
  have hn : e.modulus ≠ 0 := fun he => hP.ne' (zero_dvd_iff.mp (he ▸ hp))
  unfold modulus at *
  omega

/-- Complete-period first moment. -/
theorem indicator_sum (P : ℤ) (e : Event) (hP : 0 < P) (he : e.modulus ∣ P) :
    (∑ n ∈ Ico 0 P, e.indicator n) = ((P/e.modulus : ℤ) : ℝ) := by
  have hc := ArithmeticPositiveDuality.card_Ico_filter_modEq_of_dvd (pos_of_period e hP he) he hP.le e.residue
  have h (n : ℤ) : e.indicator n = if n ≡ e.residue [ZMOD e.modulus] then 1 else 0 := by
    simp only [indicator,class_iff]
  rw [sum_congr rfl fun n _ => h n,← natCast_card_filter]
  exact_mod_cast hc

/-- Complete-period inner products, with zero contribution for incompatible offsets. -/
theorem indicator_inner (P : ℤ) (e f : Event) (hP : 0 < P) (he : e.modulus ∣ P)
    (hf : f.modulus ∣ P) :
    (∑ n ∈ Ico 0 P, e.indicator n * f.indicator n) = (gramEntry P e f : ℝ) := by
  have hc := ArithmeticPositiveDuality.card_Ico_filter_modEq_and_modEq
    (pos_of_period e hP he) (pos_of_period f hP hf) hP.le (Int.coe_lcm_dvd he hf) e.residue f.residue
  have h (n : ℤ) : e.indicator n*f.indicator n =
      if n ≡ e.residue [ZMOD e.modulus] ∧ n ≡ f.residue [ZMOD f.modulus] then 1 else 0 := by
    by_cases h₁ : e.holds n <;> by_cases h₂ : f.holds n <;>
      simp only [indicator,class_iff,h₁,h₂,if_true,if_false,
        and_self,and_false,false_and,mul_one,mul_zero,zero_mul]
  rw [sum_congr rfl fun n _ => h n,← natCast_card_filter]
  change _ = ((if _ then _ else _ : ℤ) : ℝ)
  exact_mod_cast hc

variable {ι : Type*}

/-- Total weight of the events holding at n. -/
def weightAt (S : Finset ι) (e : ι → Event) (w : ι → ℝ) (n : ℤ) :=
  ∑ i ∈ S, w i*(e i).indicator n

theorem weight_sum (P : ℤ) (S : Finset ι) (e : ι → Event) (w : ι → ℝ)
    (hP : 0 < P) (he : ∀ i ∈ S, (e i).modulus ∣ P) :
    (∑ n ∈ Ico 0 P, weightAt S e w n) = ∑ i ∈ S, w i*((P/(e i).modulus : ℤ) : ℝ) := by
  unfold weightAt
  rw [sum_comm]
  exact sum_congr rfl fun i hi => by rw [← mul_sum,indicator_sum P _ hP (he i hi)]

/-- The overlap matrix represents the entire weighted second moment, with no independence assumption. -/
theorem weight_square_sum (P : ℤ) (S : Finset ι) (e : ι → Event) (w : ι → ℝ)
    (hP : 0 < P) (he : ∀ i ∈ S, (e i).modulus ∣ P) :
    (∑ n ∈ Ico 0 P, (weightAt S e w n)^2) =
      ∑ i ∈ S, ∑ j ∈ S, w i*w j*(gramEntry P (e i) (e j) : ℝ) := by
  simp only [weightAt,pow_two,sum_mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [← indicator_inner P _ _ hP (he i hi) (he j hj),mul_sum]
  exact sum_congr rfl fun _ _ => by ring

/-- A lower bound for the number of covered residue classes using just the
individual moduli, their lcms and the compatibility of the offsets. -/
theorem coverage_bound (P : ℤ) (S : Finset ι) (e : ι → Event) (w : ι → ℝ)
    (hP : 0 < P) (he : ∀ i ∈ S, (e i).modulus ∣ P) :
    (∑ i ∈ S, w i*((P/(e i).modulus : ℤ) : ℝ))^2 ≤
      ((#{n ∈ Ico 0 P | ∃ i ∈ S, (e i).holds n} : ℕ) : ℝ)*
      ∑ i ∈ S, ∑ j ∈ S, w i*w j*(gramEntry P (e i) (e j) : ℝ) := by
  classical
  let T := (Ico 0 P).filter (fun n => ∃ i ∈ S, (e i).holds n)
  have hz {n} (hn : n ∈ Ico 0 P) (ht : n ∉ T) : weightAt S e w n = 0 := by
    apply sum_eq_zero
    intro i hi
    have h : ¬ (e i).holds n := fun h => ht (mem_filter.mpr ⟨hn,i,hi,h⟩)
    simp [indicator,h]
  have h₁ := sum_subset (filter_subset _ _ : T ⊆ Ico 0 P) (fun _ hn ht => hz hn ht)
  have h₂ := sum_subset (filter_subset _ _ : T ⊆ Ico 0 P) (fun n hn ht =>
    show weightAt S e w n ^ 2 = 0 by simp only [hz hn ht,zero_pow two_ne_zero])
  rw [← weight_sum P S e w hP he,← weight_square_sum P S e w hP he,← h₁,← h₂]
  exact sq_sum_le_card_mul_sum_sq

end GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event

#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.indicator_sum
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.indicator_inner
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.weight_sum
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.weight_square_sum
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.coverage_bound
