import GaloisForLFunctions.RHTower.RouteEProductTruncatedReservoirMass

/-! # Conditional sampling of distinct labels and the birthday bound -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation

open _root_.RHTower Finset
variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Probability of a repeated label in m independent draws from q. -/
def repeatMass (q : α → ℝ) (m : ℕ) := 1-∑ y : Fin m → α, injectiveTupleWeight q y

/-- The birthday bound retains the exact two-draw collision probability. -/
theorem repeat_le (q : α → ℝ) (hq : ∀ x, 0 ≤ q x) (hn : ∑ x, q x = 1) (m : ℕ) :
    0 ≤ repeatMass q m ∧ repeatMass q m ≤ (m.choose 2:ℝ)*∑ x, q x^2 := by
  have hi := weightedElementarySymmetricUpper m α q hq
  have hb := weightedBirthdayCollisionBound m α q hq
  rw [hn,one_pow] at hi
  rw [hn,one_pow,one_pow,mul_one] at hb
  rw [repeatMass,sum_injectiveTupleWeight]
  exact ⟨sub_nonneg.mpr hi,by linarith only [hb]⟩

theorem repeat_le_max (q : α → ℝ) (hq : ∀ x, 0 ≤ q x) (hn : ∑ x, q x = 1) (m : ℕ)
    {M : ℝ} (hM : ∀ x, q x ≤ M) : repeatMass q m ≤ (m.choose 2:ℝ)*M := by
  have hsq : ∑ x, q x^2 ≤ ∑ x, M*q x :=
    sum_le_sum fun x _ => by rw [sq]; exact mul_le_mul_of_nonneg_right (hM x) (hq x)
  rw [← mul_sum,hn,mul_one] at hsq
  exact (repeat_le q hq hn m).2.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))

/-- Conditioning a finite probability law on retaining outcomes changes any event by at most
the discarded mass. The inequality also covers an empty retained family with zero reading. -/
theorem conditioning_error {ι : Type*} [Fintype ι] (u v : ι → ℝ) (hv : ∀ x, 0 ≤ v x)
    (hvu : ∀ x, v x ≤ u x) (hu : ∑ x, u x = 1) (A : Finset ι) :
    |(∑ x ∈ A, v x)/(∑ x, v x)-(∑ x ∈ A, u x)| ≤ 1-∑ x, v x := by
  let d := ∑ x, v x
  let a := ∑ x ∈ A, v x
  let z := ∑ x ∈ A, (u x-v x)
  have hd : 0 ≤ d := sum_nonneg fun x _ => hv x
  have ha : 0 ≤ a := sum_nonneg fun x _ => hv x
  have had : a ≤ d := sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun x _ _ => hv x)
  have hz : 0 ≤ z := sum_nonneg fun x _ => sub_nonneg.mpr (hvu x)
  have hd₁ : d ≤ 1 := (sum_le_sum fun x _ => hvu x).trans_eq hu
  have hzd : z ≤ 1-d := by
    have h := sum_le_sum_of_subset_of_nonneg (f := fun x => u x-v x) (subset_univ A)
      (fun x _ _ => sub_nonneg.mpr (hvu x))
    simpa only [sum_sub_distrib,hu,z,d] using h
  have dec : (∑ x ∈ A, u x) = a+z := by simp only [a,z,sum_sub_distrib]; ring
  change |a/d-_| ≤ 1-d
  rw [dec,abs_le]
  by_cases h : d = 0
  · have ha' := le_antisymm (had.trans_eq h) ha
    rw [h,ha',zero_div,zero_add,sub_zero]
    rw [h,sub_zero] at hzd
    constructor <;> linarith only [hz,hzd]
  have hpos := lt_of_le_of_ne hd (Ne.symm h)
  have hr := div_nonneg ha hd
  have hr₁ := (div_le_one hpos).mpr had
  have keep : a/d-(a+z) = (1-d)*(a/d)-z := by field_simp [h]; ring
  rw [keep]
  have hm := mul_le_mul_of_nonneg_left hr₁ (sub_nonneg.mpr hd₁)
  rw [mul_one] at hm
  constructor <;> linarith only [hz,hzd,hm,mul_nonneg (sub_nonneg.mpr hd₁) hr]

#print axioms repeat_le
#print axioms repeat_le_max
#print axioms conditioning_error

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation
