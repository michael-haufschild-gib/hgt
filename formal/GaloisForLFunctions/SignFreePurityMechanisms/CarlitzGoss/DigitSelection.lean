import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.TopDigits
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.CarryFreeBinomial

/-!
# Binomial nonvanishing selects actual digits

The base-`p` digits of a finite digit collection's value are exactly its
exponent counts. Independent fibre selection realizes every digitwise
subvalue. Lucas's criterion therefore characterizes nonzero binomial
coefficients by subsets of the actual digit collection.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- The nonnegative integer represented by a finite digit collection. -/
def digitValueNat (p : ℕ) (S : Finset (Digit p)) : ℕ := ∑ x ∈ S, p ^ x.1

theorem natCast_digitValueNat (p : ℕ) (S : Finset (Digit p)) :
    (digitValueNat p S : ℤ) = digitValue p S := by
  simp only [digitValueNat, digitValue, tokenValue, Nat.cast_sum, Nat.cast_pow]

theorem digitValueNat_lt_pow {p e : ℕ} (hp : 1 ≤ p) (S : Finset (Digit p))
    (hS : ∀ x ∈ S, x.1 < e) : digitValueNat p S < p ^ e := by
  have h := digitValue_lt_pow hp S hS
  rw [← natCast_digitValueNat] at h
  exact_mod_cast h

/-- A digit collection has exactly its prescribed occurrence count in every base position. -/
theorem digitValueNat_digit {p : ℕ} (hp : 2 ≤ p) (S : Finset (Digit p)) (e : ℕ) :
    digitValueNat p S / p ^ e % p = (digitBlock S e).card := by
  let L := S.filter fun x => x.1 < e
  let H := ∑ x ∈ S.filter (fun x => e < x.1), p ^ (x.1 - (e + 1))
  have hlow : digitValueNat p L < p ^ e :=
    digitValueNat_lt_pow (by omega) L (fun x hx => (mem_filter.mp hx).2)
  have hcard : (digitBlock S e).card < p := by have := card_digitBlock_le S e; omega
  have hs : digitValueNat p S = digitValueNat p L +
      p ^ e * (digitBlock S e).card + p ^ (e + 1) * H := by
    unfold digitValueNat L H digitBlock
    rw [sum_filter, card_filter, sum_filter, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    by_cases hlt : x.1 < e
    · have hne : x.1 ≠ e := by omega
      have hng : ¬ e < x.1 := by omega
      simp only [if_pos hlt, if_neg hne, if_neg hng, mul_zero, add_zero]
    · by_cases he : x.1 = e
      · simp only [he, lt_self_iff_false, ite_false, ite_true, mul_one, zero_add, mul_zero, add_zero]
      · have hgt : e < x.1 := by omega
        simp only [if_neg hlt, if_neg he, if_pos hgt, mul_zero, zero_add]
        rw [← pow_add, Nat.add_sub_of_le (by omega : e + 1 ≤ x.1)]
  have hn : digitValueNat p S = digitValueNat p L +
      p ^ e * ((digitBlock S e).card + p * H) := by
    rw [hs, pow_succ]
    ring
  rw [hn, Nat.add_mul_div_left _ _ (pow_pos (by omega : 0 < p) e),
    Nat.div_eq_of_lt hlow, zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcard]

/-- The first `E` base digits and the remaining quotient reconstruct an integer. -/
theorem sum_digits_add_quotient (p n E : ℕ) :
    (∑ e ∈ range E, (n / p ^ e % p) * p ^ e) + p ^ E * (n / p ^ E) = n := by
  induction E with
  | zero => simp only [range_zero, sum_empty, pow_zero, Nat.div_one, one_mul, zero_add]
  | succ E ih =>
    have hquot : n / p ^ E / p = n / p ^ (E + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
    calc
      _ = (∑ e ∈ range E, (n / p ^ e % p) * p ^ e) +
          p ^ E * ((n / p ^ E % p) + p * (n / p ^ E / p)) := by
        rw [sum_range_succ, hquot, pow_succ]
        ring
      _ = n := by rw [Nat.mod_add_div, ih]

theorem sum_digits_eq_of_lt_pow {p n E : ℕ} (hn : n < p ^ E) :
    (∑ e ∈ range E, (n / p ^ e % p) * p ^ e) = n := by
  have h := sum_digits_add_quotient p n E
  simpa only [Nat.div_eq_of_lt hn, mul_zero, add_zero] using h

/-- Below one full period, residue contents are the actual exponent counts. -/
theorem tokenContent_eq_digitBlock_of_lt {p r : ℕ} [NeZero r]
    (S : Finset (Digit p)) (hS : ∀ x ∈ S, x.1 < r) (h : ZMod r) :
    tokenContent (fun x : Digit p => (x.1 : ZMod r)) S h = ((digitBlock S h.val).card : ℤ) := by
  have he : S.filter (fun x => (x.1 : ZMod r) = h) = digitBlock S h.val := by
    ext x
    simp only [mem_filter, digitBlock]
    constructor
    · rintro ⟨hx, hc⟩
      refine ⟨hx, ?_⟩
      have hv := congrArg ZMod.val hc
      rwa [ZMod.val_natCast_of_lt (hS x hx)] at hv
    · rintro ⟨hx, he⟩
      refine ⟨hx, ?_⟩
      rw [he, ZMod.natCast_zmod_val]
  change ((S.filter (fun x => (x.1 : ZMod r) = h)).card : ℤ) = _
  rw [he]

/-- Digitwise containment is realized by selecting actual digit occurrences. -/
theorem exists_subset_digitValueNat_of_digits_le {p : ℕ} (hp : 2 ≤ p)
    (S : Finset (Digit p)) (k : ℕ)
    (hdigits : ∀ e, k / p ^ e % p ≤ digitValueNat p S / p ^ e % p) :
    ∃ T ⊆ S, digitValueNat p T = k := by
  let R := S.sup Prod.fst + k + 1
  letI : NeZero R := ⟨by dsimp only [R]; omega⟩
  have hS (x : Digit p) (hx : x ∈ S) : x.1 < R := by
    have hle : x.1 ≤ S.sup Prod.fst := le_sup hx
    dsimp only [R]
    omega
  have hkR : k < R := by dsimp only [R]; omega
  have hpow : 2 ^ R ≤ p ^ R := by gcongr
  have hk : k < p ^ R := hkR.trans (Nat.lt_two_pow_self.trans_le hpow)
  let v : ZMod R → ℤ := fun h => (k / p ^ h.val % p : ℕ)
  have hv (h : ZMod R) : v h ≤ tokenContent (fun x : Digit p => (x.1 : ZMod R)) S h := by
    rw [tokenContent_eq_digitBlock_of_lt S hS h]
    have hh := hdigits h.val
    rw [digitValueNat_digit hp S h.val] at hh
    change ((k / p ^ h.val % p : ℕ) : ℤ) ≤ ((digitBlock S h.val).card : ℤ)
    exact_mod_cast hh
  obtain ⟨T, hT, hcontent⟩ := exists_subset_tokenContent
    (fun x : Digit p => (x.1 : ZMod R)) S v (fun h => Nat.cast_nonneg _) hv
  have hTb (x : Digit p) (hx : x ∈ T) : x.1 < R := hS x (hT hx)
  have hTvalue : digitValueNat p T < p ^ R := digitValueNat_lt_pow (by omega) T hTb
  have hcount (e : ℕ) (he : e < R) : (digitBlock T e).card = k / p ^ e % p := by
    have hc := congrFun hcontent (e : ZMod R)
    rw [tokenContent_eq_digitBlock_of_lt T hTb] at hc
    change ((digitBlock T (e : ZMod R).val).card : ℤ) =
      ((k / p ^ (e : ZMod R).val % p : ℕ) : ℤ) at hc
    rw [ZMod.val_natCast_of_lt he] at hc
    exact_mod_cast hc
  refine ⟨T, hT, ?_⟩
  calc
    digitValueNat p T = ∑ e ∈ range R, (digitValueNat p T / p ^ e % p) * p ^ e :=
      (sum_digits_eq_of_lt_pow hTvalue).symm
    _ = ∑ e ∈ range R, (k / p ^ e % p) * p ^ e := by
      apply sum_congr rfl
      intro e he
      rw [digitValueNat_digit hp T e, hcount e (mem_range.mp he)]
    _ = k := sum_digits_eq_of_lt_pow hk

/-- Exact characterization of values selectable from an actual digit collection. -/
theorem exists_subset_digitValueNat_iff {p : ℕ} (hp : 2 ≤ p)
    (S : Finset (Digit p)) (k : ℕ) :
    (∃ T ⊆ S, digitValueNat p T = k) ↔
      ∀ e, k / p ^ e % p ≤ digitValueNat p S / p ^ e % p := by
  constructor
  · rintro ⟨T, hT, rfl⟩ e
    rw [digitValueNat_digit hp T e, digitValueNat_digit hp S e]
    apply card_le_card
    intro x hx
    exact mem_filter.mpr ⟨hT (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩
  · exact exists_subset_digitValueNat_of_digits_le hp S k

/-- A binomial coefficient survives in characteristic `p` exactly when
its lower argument is the value of a subset of the given digit collection. -/
theorem cast_choose_ne_zero_iff_subset {p : ℕ} [Fact p.Prime]
    (K : Type*) [Semiring K] [CharP K p] (S : Finset (Digit p)) (k : ℕ) :
    ((digitValueNat p S).choose k : K) ≠ 0 ↔ ∃ T ⊆ S, digitValueNat p T = k := by
  have hp : p.Prime := Fact.out
  exact (cast_choose_ne_zero_iff_digits_le K (digitValueNat p S) k).trans
    (exists_subset_digitValueNat_iff hp.two_le S k).symm

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
