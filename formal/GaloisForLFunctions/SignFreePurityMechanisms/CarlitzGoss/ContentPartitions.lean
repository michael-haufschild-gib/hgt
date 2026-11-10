import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ContentRounding

/-!
# Feasibility of partitions with divisible digit contents

A nonnegative content vector u is a sum of k positive vectors with weighted
residue zero modulo `p^s−1`, followed by one unrestricted positive vector,
exactly when every coordinate of `E⁻¹u` exceeds k.

Positive divisible vectors have integral inverse coordinates at least one.
The converse repeatedly extracts an integral layer, using cyclic rounding.
The resulting criterion is the content-space feasibility step for carry-free
compositions; it does not yet assert optimality of a greedy composition.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {s : ℕ}

/-- A nonzero vector of nonnegative digit counts. -/
def PositiveContent (u : ZMod s → ℤ) : Prop :=
  (∀ h, 0 ≤ u h) ∧ ∃ h, 0 < u h

/-- Digit counts whose weighted residue is zero modulo `p^s−1`. -/
def DivisibleContent (p : ℕ) (u : ZMod s → ℤ) : Prop :=
  PositiveContent u ∧ ((p : ℤ) ^ s - 1) ∣ cyclicWeighted (p : ℤ) u 0

/-- A partition into positive divisible digit-content vectors. -/
inductive DivisiblePartition (p : ℕ) : ℕ → (ZMod s → ℤ) → Prop
  | nil : DivisiblePartition p 0 0
  | cons {k : ℕ} {u v : ZMod s → ℤ} : DivisibleContent p u → DivisiblePartition p k v →
      DivisiblePartition p (k + 1) (u + v)

/-- A divisible prefix of k parts, followed by one unrestricted positive part. -/
def HasContentPrefix (p k : ℕ) (u : ZMod s → ℤ) : Prop :=
  ∃ v w, DivisiblePartition p k v ∧ PositiveContent w ∧ u = v + w

theorem inverseContent_add_int (p : ℕ) (u v : ZMod s → ℤ) (h : ZMod s) :
    inverseContent (p : ℚ) (fun j => ((u + v) j : ℚ)) h =
      inverseContent (p : ℚ) (fun j => (u j : ℚ)) h +
      inverseContent (p : ℚ) (fun j => (v j : ℚ)) h := by
  simp only [Pi.add_apply, Int.cast_add, inverseContent, cyclicWeighted_add, add_div]

theorem inverseContent_zero (p : ℚ) (h : ZMod s) : inverseContent p (0 : ZMod s → ℚ) h = 0 := by
  simp only [inverseContent, cyclicWeighted, Pi.zero_apply, mul_zero, sum_const_zero, zero_div]

variable [NeZero s]

theorem inverseContent_ge_one_of_divisible (p : ℕ) (hp : 2 ≤ p)
    {u : ZMod s → ℤ} (hu : DivisibleContent p u) (h : ZMod s) :
    1 ≤ inverseContent (p : ℚ) (fun j => (u j : ℚ)) h := by
  obtain ⟨a, ha⟩ := (exists_cyclicDifference_eq_iff p hp u).mpr hu.2
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpow : (p : ℚ) ^ s ≠ 1 := ne_of_gt (one_lt_pow₀ hpQ (NeZero.ne s))
  have he : cyclicDifference (p : ℚ) (fun j => (a j : ℚ)) = fun j => (u j : ℚ) := by
    funext j
    have hh := congrFun ha j
    dsimp only [cyclicDifference] at hh ⊢
    exact_mod_cast hh
  have hi : inverseContent (p : ℚ) (fun j => (u j : ℚ)) h = a h := by
    rw [← he, inverseContent_cyclicDifference _ hpow]
  obtain ⟨j, hj⟩ := hu.1.2
  have hpos := inverseContent_pos hpQ (u := fun j => (u j : ℚ))
    (fun j => by exact_mod_cast hu.1.1 j) ⟨j, by exact_mod_cast hj⟩ h
  rw [hi] at hpos ⊢
  have hh : 0 < a h := by exact_mod_cast hpos
  exact_mod_cast (show (1 : ℤ) ≤ a h by omega)

theorem divisibleContent_of_cyclicDifference (p : ℕ) (hp : 2 ≤ p) (a : ZMod s → ℤ)
    (ha : ∀ h, 1 ≤ a h) (hu : ∀ h, 0 ≤ cyclicDifference (p : ℤ) a h) :
    DivisibleContent p (cyclicDifference (p : ℤ) a) := by
  refine ⟨⟨hu, ?_⟩, ?_⟩
  · apply exists_pos_of_cyclicDifference p hp (fun h => (a h : ℚ))
      (cyclicDifference (p : ℤ) a) hu
    · exact_mod_cast (show 0 < a 0 by have := ha 0; omega)
    · funext h
      simp only [cyclicDifference, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  · rw [cyclicWeighted_cyclicDifference]
    exact dvd_mul_right _ _

omit [NeZero s] in
theorem DivisiblePartition.nonneg {p k : ℕ} {u : ZMod s → ℤ}
    (hu : DivisiblePartition p k u) (h : ZMod s) : 0 ≤ u h := by
  induction hu with
  | nil => exact le_rfl
  | @cons k u v hJ hP ih => exact add_nonneg (hJ.1.1 h) ih

theorem DivisiblePartition.inverseContent_ge {p k : ℕ} (hp : 2 ≤ p) {u : ZMod s → ℤ}
    (hu : DivisiblePartition p k u) (h : ZMod s) :
    (k : ℚ) ≤ inverseContent (p : ℚ) (fun j => (u j : ℚ)) h := by
  induction hu with
  | nil =>
    change 0 ≤ inverseContent (p : ℚ) (0 : ZMod s → ℚ) h
    rw [inverseContent_zero]
  | @cons k u v hJ hP ih =>
    rw [inverseContent_add_int]
    have hh := inverseContent_ge_one_of_divisible p hp hJ h
    push_cast
    linarith only [hh, ih]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {s : ℕ} [NeZero s]

/-- An integral inverse-content vector above k splits into k positive divisible parts. -/
theorem divisiblePartition_of_inverseInteger (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k)
    (a : ZMod s → ℤ) (ha : ∀ h, (k : ℤ) ≤ a h)
    (hu : ∀ h, 0 ≤ cyclicDifference (p : ℤ) a h) :
    DivisiblePartition p k (cyclicDifference (p : ℤ) a) := by
  induction k generalizing a with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst k
      have hJ := divisibleContent_of_cyclicDifference p hp a
        (by simpa only [zero_add, Nat.cast_one] using ha) hu
      simpa only [add_zero] using DivisiblePartition.cons hJ (DivisiblePartition.nil (p := p))
    · have hc (h : ZMod s) : (k : ℚ) < (a h : ℚ) := by
        have hh := ha h
        push_cast at hh
        have hz : (k : ℤ) < a h := by omega
        exact_mod_cast hz
      have hE : cyclicDifference (p : ℚ) (fun h => (a h : ℚ)) =
          fun h => ((cyclicDifference (p : ℤ) a h : ℤ) : ℚ) := by
        funext h
        simp only [cyclicDifference, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      obtain ⟨d, hd, hbd, _, _⟩ := exists_integral_content_layer p k hp (by omega)
        (fun h => (a h : ℚ)) (cyclicDifference (p : ℤ) a) hu hc hE
      let v := cyclicDifference (p : ℤ) d
      let w := cyclicDifference (p : ℤ) a - v
      have hP : DivisiblePartition p k v := by
        apply ih (a := d)
        · omega
        · exact fun h => (hd h).1
        · exact fun h => (hbd h).1
      have ha_d (h : ZMod s) : 1 ≤ (a - d) h := by
        have hz : d h < a h := by exact_mod_cast (hd h).2
        change 1 ≤ a h - d h
        omega
      have hwEq : w = cyclicDifference (p : ℤ) (a - d) := by
        funext h
        dsimp only [w, v, cyclicDifference, Pi.sub_apply]
        ring
      have hw : ∀ h, 0 ≤ cyclicDifference (p : ℤ) (a - d) h := by
        intro h
        rw [← hwEq]
        exact sub_nonneg.mpr (hbd h).2
      have hJ : DivisibleContent p w := by
        rw [hwEq]
        exact divisibleContent_of_cyclicDifference p hp (a - d) ha_d hw
      simpa only [w, sub_add_cancel] using DivisiblePartition.cons hJ hP

/-- Feasibility of a divisible prefix is measured by the least inverse-content coordinate. -/
theorem hasContentPrefix_iff (p k : ℕ) (hp : 2 ≤ p) (u : ZMod s → ℤ) :
    HasContentPrefix p k u ↔ (∀ h, 0 ≤ u h) ∧
      ∀ h, (k : ℚ) < inverseContent (p : ℚ) (fun j => (u j : ℚ)) h := by
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpow : (p : ℚ) ^ s ≠ 1 := ne_of_gt (one_lt_pow₀ hpQ (NeZero.ne s))
  constructor
  · rintro ⟨v, w, hP, hw, rfl⟩
    refine ⟨fun h => add_nonneg (hP.nonneg h) (hw.1 h), ?_⟩
    intro h
    rw [inverseContent_add_int]
    have hge := hP.inverseContent_ge hp h
    obtain ⟨j, hj⟩ := hw.2
    have hpos := inverseContent_pos hpQ (u := fun j => (w j : ℚ))
      (fun j => by exact_mod_cast hw.1 j) ⟨j, by exact_mod_cast hj⟩ h
    linarith only [hge, hpos]
  · rintro ⟨hu, hc⟩
    let c := inverseContent (p : ℚ) (fun j => (u j : ℚ))
    have hE : cyclicDifference (p : ℚ) c = fun j => (u j : ℚ) :=
      cyclicDifference_inverseContent _ hpow _
    by_cases hk : k = 0
    · subst k
      refine ⟨0, u, DivisiblePartition.nil, ⟨hu, ?_⟩, ?_⟩
      · exact exists_pos_of_cyclicDifference p hp c u hu
          (by simpa only [Nat.cast_zero] using hc 0) hE
      · exact (zero_add u).symm
    · obtain ⟨d, hd, hbd, _, hrem⟩ := exists_integral_content_layer p k hp (by omega) c u hu hc hE
      have hP := divisiblePartition_of_inverseInteger p k hp (by omega) d
        (fun h => (hd h).1) (fun h => (hbd h).1)
      refine ⟨cyclicDifference (p : ℤ) d, u - cyclicDifference (p : ℤ) d, hP,
        ⟨fun h => sub_nonneg.mpr (hbd h).2, ?_⟩, ?_⟩
      · obtain ⟨h, hh⟩ := hrem
        exact ⟨h, sub_pos.mpr hh⟩
      · funext h
        dsimp only [Pi.add_apply, Pi.sub_apply]
        ring

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.hasContentPrefix_iff
