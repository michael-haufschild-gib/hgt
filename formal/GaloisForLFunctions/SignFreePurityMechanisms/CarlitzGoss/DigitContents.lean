import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Cyclic digit contents and divisibility by `p^s−1`

Group the base-p digits of N by their exponents modulo s. Their weighted sum is
congruent to N modulo `p^s−1`. The cyclic difference `E a(h)=p a(h+1)−a(h)`
has an explicit inverse with positive rational coefficients. Its integral image is
exactly the kernel of that weighted congruence.

Consequently, for N positive and p at least two, `p^s−1` divides N precisely when
its digit-content vector is `E a` for an integral vector whose coordinates are
at least one. This identifies the divisible parts in carry-free compositions.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

variable {s : ℕ}
variable {R : Type*} [CommRing R]

/-- The cyclic difference whose integral image describes digit contents of `(p^s−1)`-multiples. -/
def cyclicDifference (p : R) (a : ZMod s → R) (h : ZMod s) : R :=
  p * a (h + 1) - a h

/-- One cyclic row of the inverse-content numerator. -/
def cyclicWeighted (p : R) (u : ZMod s → R) (h : ZMod s) : R :=
  ∑ k ∈ range s, p ^ k * u (h + k)

theorem cyclicWeighted_cyclicDifference (p : R) (a : ZMod s → R) (h : ZMod s) :
    cyclicWeighted p (cyclicDifference p a) h = (p ^ s - 1) * a h := by
  have ht (n : ℕ) :
      (∑ k ∈ range n, p ^ k * (p * a (h + (k + 1 : ℕ)) - a (h + k))) =
        p ^ n * a (h + n) - a h := by
    induction n with
    | zero => simp only [range_zero, sum_empty, pow_zero, Nat.cast_zero, add_zero, one_mul, sub_self]
    | succ n ih =>
      rw [sum_range_succ, ih, pow_succ]
      ring
  have hh := ht s
  simpa only [cyclicWeighted, cyclicDifference, Nat.cast_add, Nat.cast_one, ← add_assoc,
    ZMod.natCast_self, add_zero, sub_mul, one_mul] using hh

theorem cyclicDifference_cyclicWeighted (p : R) (u : ZMod s → R) (h : ZMod s) :
    cyclicDifference p (cyclicWeighted p u) h = (p ^ s - 1) * u h := by
  rw [← cyclicWeighted_cyclicDifference p u h]
  unfold cyclicDifference cyclicWeighted
  simp only [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [show h + 1 + (k : ZMod s) = h + k + 1 by ring]
  ring

/-- Inverse content is the positive geometric average of cyclically rotated digit counts. -/
def inverseContent (p : ℚ) (u : ZMod s → ℚ) (h : ZMod s) : ℚ :=
  cyclicWeighted p u h / (p ^ s - 1)

theorem inverseContent_cyclicDifference (p : ℚ) (hp : p ^ s ≠ 1)
    (a : ZMod s → ℚ) : inverseContent p (cyclicDifference p a) = a := by
  funext h
  rw [inverseContent, cyclicWeighted_cyclicDifference]
  exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hp)

theorem cyclicDifference_inverseContent (p : ℚ) (hp : p ^ s ≠ 1)
    (u : ZMod s → ℚ) : cyclicDifference p (inverseContent p u) = u := by
  funext h
  dsimp only [cyclicDifference, inverseContent]
  rw [← mul_div_assoc, ← sub_div]
  change cyclicDifference p (cyclicWeighted p u) h / (p ^ s - 1) = u h
  rw [cyclicDifference_cyclicWeighted]
  exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hp)

theorem cyclicDifference_injective (p : ℚ) (hp : p ^ s ≠ 1) :
    Function.Injective (cyclicDifference (s := s) p) := by
  intro a b hab
  have h := congrArg (inverseContent p) hab
  simpa only [inverseContent_cyclicDifference p hp] using h

variable [NeZero s]

theorem inverseContent_pos {p : ℚ} (hp : 1 < p) {u : ZMod s → ℚ}
    (hu : ∀ h, 0 ≤ u h) (hu0 : ∃ h, 0 < u h) (h : ZMod s) :
    0 < inverseContent p u h := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hden : 0 < p ^ s - 1 := sub_pos.mpr (one_lt_pow₀ hp (NeZero.ne s))
  apply div_pos _ hden
  obtain ⟨j, hj⟩ := hu0
  apply sum_pos' (fun k _ => mul_nonneg (pow_nonneg hp0.le k) (hu _))
  refine ⟨(j - h).val, mem_range.mpr (ZMod.val_lt _), ?_⟩
  rw [ZMod.natCast_zmod_val, show h + (j - h) = j by ring]
  exact mul_pos (pow_pos hp0 _) hj

theorem inverseContent_nonneg {p : ℚ} (hp : 1 < p) {u : ZMod s → ℚ}
    (hu : ∀ h, 0 ≤ u h) (h : ZMod s) : 0 ≤ inverseContent p u h := by
  apply div_nonneg
  · exact sum_nonneg fun k _ => mul_nonneg (pow_nonneg (le_trans zero_le_one hp.le) k) (hu _)
  · exact (sub_pos.mpr (one_lt_pow₀ hp (NeZero.ne s))).le

/-- An integral cyclic difference propagates integrality backwards from one coordinate. -/
theorem integral_of_cyclicDifference (p : ℤ) (a : ZMod s → ℚ) (u : ZMod s → ℤ)
    (ha : cyclicDifference (p : ℚ) a = fun h => (u h : ℚ))
    (h0 : ∃ z : ℤ, a 0 = z) (h : ZMod s) : ∃ z : ℤ, a h = z := by
  have hind (n : ℕ) : ∃ z : ℤ, a (-(n : ZMod s)) = z := by
    induction n with
    | zero => simpa only [Nat.cast_zero, neg_zero] using h0
    | succ n ih =>
      obtain ⟨z, hz⟩ := ih
      have he := congrFun ha (-((n + 1 : ℕ) : ZMod s))
      have hi : (-((n + 1 : ℕ) : ZMod s)) + 1 = -(n : ZMod s) := by
        push_cast
        ring
      simp only [cyclicDifference, hi, hz] at he
      refine ⟨p * z - u (-((n + 1 : ℕ) : ZMod s)), ?_⟩
      push_cast at he ⊢
      linarith only [he]
  have hh := hind (-h).val
  simpa only [ZMod.natCast_zmod_val, neg_neg] using hh

/-- The cyclic integer lattice has the single weighted congruence modulo `p^s−1`. -/
theorem exists_cyclicDifference_eq_iff (p : ℕ) (hp : 2 ≤ p) (u : ZMod s → ℤ) :
    (∃ a : ZMod s → ℤ, cyclicDifference (p : ℤ) a = u) ↔
      ((p : ℤ) ^ s - 1) ∣ cyclicWeighted (p : ℤ) u 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [cyclicWeighted_cyclicDifference]
    exact dvd_mul_right _ _
  · intro hu
    have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
    have hpow : (p : ℚ) ^ s ≠ 1 := ne_of_gt (one_lt_pow₀ hpQ (NeZero.ne s))
    let v : ZMod s → ℚ := fun h => u h
    let a := inverseContent (p : ℚ) v
    have he : cyclicDifference (p : ℚ) a = v := cyclicDifference_inverseContent _ hpow v
    obtain ⟨z, hz⟩ := hu
    have hm : ((cyclicWeighted (p : ℤ) u 0 : ℤ) : ℚ) =
        cyclicWeighted (p : ℚ) v 0 := by
      simp only [cyclicWeighted, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast, v]
    have h0 : a 0 = (z : ℚ) := by
      dsimp only [a, inverseContent]
      rw [← hm, hz]
      push_cast
      exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hpow)
    have hall (h : ZMod s) : ∃ z : ℤ, a h = z :=
      integral_of_cyclicDifference (p : ℤ) a u (by exact_mod_cast he) ⟨z, h0⟩ h
    choose b hb using hall
    refine ⟨b, ?_⟩
    funext h
    have hh := congrFun he h
    simp only [cyclicDifference, hb, v] at hh
    exact_mod_cast hh

/-- Digit counts grouped by exponent modulo the extension degree. -/
def digitContent : List ℕ → ZMod s → ℕ
  | [], _ => 0
  | d :: L, h => (if h = 0 then d else 0) + digitContent L (h - 1)

omit [NeZero s] in
theorem cyclicWeighted_add (p : R) (u v : ZMod s → R) (h : ZMod s) :
    cyclicWeighted p (fun j => u j + v j) h = cyclicWeighted p u h + cyclicWeighted p v h := by
  simp only [cyclicWeighted, mul_add, sum_add_distrib]

theorem cyclicWeighted_single_zero (p d : R) :
    cyclicWeighted p (fun h : ZMod s => if h = 0 then d else 0) 0 = d := by
  unfold cyclicWeighted
  rw [sum_eq_single 0]
  · simp only [pow_zero, Nat.cast_zero, add_zero, ite_true, one_mul]
  · intro k hk hk0
    have hne : (k : ZMod s) ≠ 0 := by
      intro he
      have hv := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (mem_range.mp hk), ZMod.val_zero] at hv
      exact hk0 hv
    simp only [zero_add, if_neg hne, mul_zero]
  · intro hnot
    exact (hnot (mem_range.mpr (NeZero.pos s))).elim

omit [NeZero s] in
theorem cyclicWeighted_shift (p : R) (u : ZMod s → R) :
    cyclicWeighted p (fun h => u (h - 1)) 0 =
      p * cyclicWeighted p u 0 - (p ^ s - 1) * u (-1) := by
  have hshift : cyclicWeighted p (fun h => u (h - 1)) 0 = cyclicWeighted p u (-1) := by
    unfold cyclicWeighted
    refine sum_congr rfl fun k _ => ?_
    change p ^ k * u (0 + (k : ZMod s) - 1) = p ^ k * u (-1 + k)
    rw [show (0 : ZMod s) + k - 1 = -1 + k by ring]
  rw [hshift]
  have h := cyclicDifference_cyclicWeighted p u (-1)
  simp only [cyclicDifference, neg_add_cancel] at h
  linear_combination -h

/-- Grouping digits by their exponents modulo `s` preserves their residue modulo `p^s−1`. -/
theorem dvd_ofDigits_sub_weighted_content (p : ℕ) (L : List ℕ) :
    ((p : ℤ) ^ s - 1) ∣ Nat.ofDigits (p : ℤ) L -
      cyclicWeighted (p : ℤ) (fun h : ZMod s => (digitContent L h : ℤ)) 0 := by
  induction L with
  | nil => simp only [Nat.ofDigits, digitContent, Nat.cast_zero, cyclicWeighted,
      mul_zero, sum_const_zero, sub_zero, dvd_zero]
  | cons d L ih =>
    have he : (fun h : ZMod s => (digitContent (d :: L) h : ℤ)) =
        fun h => (if h = 0 then (d : ℤ) else 0) + (digitContent L (h - 1) : ℤ) := by
      funext h
      simp only [digitContent, Nat.cast_add]
      split_ifs <;> rfl
    rw [Nat.ofDigits, he, cyclicWeighted_add, cyclicWeighted_single_zero,
      cyclicWeighted_shift (p : ℤ) (fun h : ZMod s => (digitContent L h : ℤ))]
    have halg (a b c d e : ℤ) : a + b * c - (a + (b * d - e)) = b * (c - d) + e := by ring
    rw [halg]
    exact dvd_add (dvd_mul_of_dvd_right ih (p : ℤ))
      (dvd_mul_right ((p : ℤ) ^ s - 1) (digitContent L (-1) : ℤ))

omit [NeZero s] in
/-- Every positive digit value has a positive residue-class digit count. -/
theorem digitContent_pos_of_ofDigits_pos (p : ℕ) (L : List ℕ)
    (hL : 0 < Nat.ofDigits p L) : ∃ h : ZMod s, 0 < digitContent L h := by
  induction L with
  | nil => simp only [Nat.ofDigits, lt_self_iff_false] at hL
  | cons d L ih =>
    by_cases hd : d = 0
    · have ht : 0 < Nat.ofDigits p L := by
        by_contra hn
        have hz : Nat.ofDigits p L = 0 := by omega
        norm_num only [Nat.ofDigits, hd, hz, Nat.cast_zero, mul_zero, add_zero] at hL
      obtain ⟨h, hh⟩ := ih ht
      refine ⟨h + 1, ?_⟩
      simp only [digitContent, show h + 1 - 1 = h by ring]
      omega
    · refine ⟨0, ?_⟩
      simp only [digitContent, ite_true]
      omega

/-- The digit-content vector of a natural number in base `p`. -/
def contentOf (p N : ℕ) : ZMod s → ℕ := digitContent (Nat.digits p N)

omit [NeZero s] in
theorem contentOf_pos (p N : ℕ) (hN : 0 < N) : ∃ h : ZMod s, 0 < contentOf p N h := by
  exact digitContent_pos_of_ofDigits_pos p (Nat.digits p N)
    (by simpa only [Nat.ofDigits_digits] using hN)

theorem contentOf_divisibility (p N : ℕ) :
    ((p : ℤ) ^ s - 1) ∣ (N : ℤ) ↔
      ((p : ℤ) ^ s - 1) ∣ cyclicWeighted (p : ℤ) (fun h : ZMod s => (contentOf p N h : ℤ)) 0 := by
  have hd := dvd_ofDigits_sub_weighted_content (s := s) p (Nat.digits p N)
  rw [← Nat.coe_ofDigits, Nat.ofDigits_digits] at hd
  change ((p : ℤ) ^ s - 1) ∣ (N : ℤ) -
    cyclicWeighted (p : ℤ) (fun h : ZMod s => (contentOf p N h : ℤ)) 0 at hd
  constructor
  · intro hN
    simpa only [sub_sub_cancel] using dvd_sub hN hd
  · intro hc
    simpa only [sub_add_cancel] using dvd_add hd hc

/-- Positive multiples of `p^s−1` have exactly the positive integral inverse-content vectors. -/
theorem exists_positive_cyclicDifference_content_iff (p N : ℕ) (hp : 2 ≤ p) (hN : 0 < N) :
    (∃ a : ZMod s → ℤ, (∀ h, 1 ≤ a h) ∧
      cyclicDifference (p : ℤ) a = fun h => (contentOf p N h : ℤ)) ↔
      ((p : ℤ) ^ s - 1) ∣ (N : ℤ) := by
  constructor
  · rintro ⟨a, _, ha⟩
    exact (contentOf_divisibility p N).mpr
      ((exists_cyclicDifference_eq_iff p hp _).mp ⟨a, ha⟩)
  · intro hdiv
    obtain ⟨a, ha⟩ := (exists_cyclicDifference_eq_iff p hp _).mpr
      ((contentOf_divisibility p N).mp hdiv)
    refine ⟨a, ?_, ha⟩
    have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
    have hpow : (p : ℚ) ^ s ≠ 1 := ne_of_gt (one_lt_pow₀ hpQ (NeZero.ne s))
    have he : cyclicDifference (p : ℚ) (fun h => (a h : ℚ)) =
        fun h => (contentOf p N h : ℚ) := by
      funext h
      have hh := congrFun ha h
      dsimp only [cyclicDifference] at hh ⊢
      exact_mod_cast hh
    obtain ⟨j, hj⟩ := contentOf_pos (s := s) p N hN
    intro h
    have hpos := inverseContent_pos hpQ
      (u := fun h => (contentOf p N h : ℚ)) (fun _ => Nat.cast_nonneg _)
      ⟨j, by exact_mod_cast hj⟩ h
    rw [← he, inverseContent_cyclicDifference _ hpow] at hpos
    have ha0 : 0 < a h := by exact_mod_cast hpos
    omega

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.exists_positive_cyclicDifference_content_iff
