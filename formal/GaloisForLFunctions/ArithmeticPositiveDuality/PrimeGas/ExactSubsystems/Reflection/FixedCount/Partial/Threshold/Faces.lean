import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Slice

/-! # Finite list of nearest attainable coordinate violations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {c a : I → ℕ} {m : ℕ}

/-- Each coordinate can violate at most one side of its reflected interval. -/
def pin (c a : I → ℕ) (i : I) := if a i < c i then a i+1 else a i-c i-1

def active (c a : I → ℕ) (m : ℕ) := univ.filter fun i =>
  a i ≠ c i ∧ lower c m i ≤ pin c a i ∧ pin c a i ≤ upper c m i

def violates (a : I → ℕ) (x : State c m) := ∃ i, a i < count x i ∨ count x i+c i < a i

def baseline (e : I → ℝ) (c : I → ℕ) (m : ℕ) := linearCost e (ordinary e c m)

def readings (e : I → ℝ) (c a : I → ℕ) (m : ℕ) :=
  (active c a m).image fun i => sliceCost e c m i (pin c a i)-baseline e c m

def outsideOffsets (e : I → ℝ) (c a : I → ℕ) (m : ℕ) :=
  {z : ℝ | ∃ x : State c m, violates a x ∧ linearCost e (count x)-baseline e c m = z}

omit [DecidableEq I] in
private theorem mem_active (i : I) (hne : a i ≠ c i) (x : State c m) (hx : count x i = pin c a i) :
    i ∈ active c a m :=
  mem_filter.mpr ⟨mem_univ _,hne,(coordinate_values c m i _).mp ⟨x,hx⟩⟩

omit [DecidableEq I] in
private theorem violates_at_pin (i : I) (hi : i ∈ active c a m) (x : State c m) (hx : count x i = pin c a i) :
    violates a x := by
  have hn := (mem_filter.mp hi).2.1
  refine ⟨i,?_⟩
  by_cases h : a i < c i
  · rw [pin,if_pos h] at hx; omega
  · rw [pin,if_neg h] at hx; omega

/-- Every entry is an attained, genuinely unpaired cost for its specified coordinate sums. -/
theorem readings_subset (e : I → ℝ) (he : Function.Injective e) (c a : I → ℕ) (m : ℕ) :
    ↑(readings e c a m) ⊆ outsideOffsets e c a m := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
  obtain ⟨x,hx⟩ := (coordinate_values c m i _).mpr (mem_filter.mp hi).2.2
  obtain ⟨y,hy,hyc,_⟩ := slice_minimum e he x i _ hx
  exact ⟨y,violates_at_pin i hi y hy,by rw [hyc]⟩

/-- If the original optimum lies in the reflected box, every violated half-space
has a nearest attainable face whose minimum is no larger than the given cost. -/
theorem readings_cover (e : I → ℝ) (he : Function.Injective e) (c a : I → ℕ) (m : ℕ)
    (hbox : ∀ i, ordinary e c m i ≤ a i ∧ a i ≤ ordinary e c m i+c i) :
    ∀ z ∈ outsideOffsets e c a m, ∃ v ∈ readings e c a m, v ≤ z := by
  rintro _ ⟨x,⟨i,hi⟩,rfl⟩
  have hcap := count_cap x i
  have h₀ := hbox i
  have nearest : ∃ y : State c m, count y i = pin c a i ∧ linearCost e (count y) ≤ linearCost e (count x) := by
    rcases hi with up | down
    · have hc : a i < c i := by omega
      rw [pin,if_pos hc]
      exact above_wall e he x i _ (by omega) (by omega)
    · have hc : ¬ a i < c i := by omega
      rw [pin,if_neg hc]
      exact below_wall e he x i _ (by omega) (by omega)
  obtain ⟨y,hy,hyc⟩ := nearest
  obtain ⟨_,_,_,hmin⟩ := slice_minimum e he y i _ hy
  refine ⟨_,mem_image.mpr ⟨i,mem_active i (by rcases hi with up | down <;> omega) y hy,rfl⟩,?_⟩
  exact sub_le_sub_right (hmin.trans hyc) _

#print axioms readings_subset
#print axioms readings_cover

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold
