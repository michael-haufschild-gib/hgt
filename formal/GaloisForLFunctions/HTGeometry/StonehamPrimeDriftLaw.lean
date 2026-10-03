import GaloisForLFunctions.HTGeometry.StonehamPrimeOrbit

/-!
# The class-number drift law of the Stoneham constants

Let `p ≡ 3 (mod 8)` be a prime such that `2` has order `p − 1` modulo `p` and
`p² ∤ 2^{p−1} − 1`, and let `α_p = Σ_{j ≥ 1} p^{−j} 2^{−p^j}`.  Then the base-4 parity drift of
`α_p` at the window ends `Nₖ = (p^{k+1} + 1)/2` is

`D_{α_p}(Nₖ) = p · k · Σ_{0 < r < p/2} (r/p)`  (`drift_stonehamP_windowEnd`).

By Dirichlet's class number formula `Σ_{0<r<p/2} (r/p) = 3 h(−p)` for `p > 3`, so the drift grows
by exactly `3p h(−p)` per window: `33` for `p = 11`, `57` for `p = 19`, `531` for `p = 59`.

If instead `p ≡ 5 (mod 8)` (the only other residue class in which `2` can be a primitive root),
the drift vanishes at every window end (`drift_stonehamP_windowEnd_of_mod_eight_eq_five`), e.g. for
`p = 5, 13`.  Both cases follow from `drift_stonehamP_windowEnd_of_period`: a window is `p` periods
of the orbit, and a period carries `(χ(2A)/2)(χ(−1) − 1) Σ_{q/4<r<q/2} χ(r)` drift.

Mechanism.  Each window consists of `p` periods of the orbit `2Aₖ4ⁱ mod pᵏ`, which is a class of
non-squares.  On a square class the drift weight `w(⌊4r/q⌋)` sums to `−χ(a) Σ_{q/4<r<q/2} χ(r)`
(reflection `r ↦ q − r`); this reduces modulo `p` to `S(1/2) − S(1/4)`, and `S(1/4) = 0` because
`χ(2) = χ(−1) = −1` (doubling argument).
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.StonehamPrimeDrift

open BinaryParityDrift StonehamParityDrift

/-- The drift weight `w(⌊4r/q⌋)` of the first base-4 digit of `r/q`. -/
def quarterWeight (q r : ℕ) : ℤ := digitWeight ((4 * r / q : ℕ) : ℤ)

theorem four_mul_sub_div {q r : ℕ} (hr : r < q) (hndvd : ¬ q ∣ 4 * r) :
    4 * (q - r) / q = 3 - 4 * r / q := by
  have hq : 0 < q := by omega
  have hdm := Nat.div_add_mod (4 * r) q
  have hs : 0 < 4 * r % q := Nat.pos_of_ne_zero fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
  have hsq := Nat.mod_lt (4 * r) hq
  have hD : 4 * r / q ≤ 3 := by
    have : 4 * r / q < 4 := (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
    omega
  have hE : q * (4 * r / q) ≤ 3 * q := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hD
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, mul_comm (4 * r / q)]; omega
  · rw [show 3 - 4 * r / q + 1 = 4 - 4 * r / q by omega, Nat.sub_mul, mul_comm (4 * r / q)]
    omega

theorem quarterWeight_sub {q r : ℕ} (hr : r < q) (hndvd : ¬ q ∣ 4 * r) :
    quarterWeight q (q - r) = -quarterWeight q r := by
  unfold quarterWeight
  have hD : 4 * r / q ≤ 3 := by
    have : 4 * r / q < 4 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    omega
  rw [four_mul_sub_div hr hndvd, Nat.cast_sub hD]
  push_cast
  exact digitWeight_three_sub (by positivity) (by exact_mod_cast hD)

variable {p : ℕ} [hp : Fact p.Prime]

theorem not_pow_dvd_four_mul (hp2 : p ≠ 2) {k r : ℕ} (hr0 : 0 < r) (hr : r < p ^ k) :
    ¬ p ^ k ∣ 4 * r := by
  intro h
  have hcop : Nat.Coprime (p ^ k) 4 := Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h4 => hp2 <|
      (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
        (hp.out.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h4)))
  exact absurd (Nat.le_of_dvd hr0 (hcop.dvd_of_dvd_mul_left h)) (by omega)

/-- `χ(q − r) = χ(−1) χ(r)` for `p ∣ q`. -/
theorem legendreSym_sub_eq {q r : ℕ} (hq : p ∣ q) (hr : r ≤ q) :
    legendreSym p ((q - r : ℕ) : ℤ) = legendreSym p (-1) * legendreSym p r := by
  rw [legendreSym.mod, Nat.cast_sub hr]
  have : ((q : ℤ) - r) % p = (-(r : ℤ)) % p := by
    obtain ⟨c, rfl⟩ := hq
    push_cast
    rw [show (p : ℤ) * c - r = -r + p * c by ring, Int.add_mul_emod_self_left]
  rw [this, ← legendreSym.mod, show -(r : ℤ) = -1 * r by ring, legendreSym.mul]

/-- `χ(q − r) = −χ(r)` for `p ∣ q` when `χ(−1) = −1`. -/
theorem legendreSym_sub (hneg : legendreSym p (-1) = -1) {q r : ℕ} (hq : p ∣ q) (hr : r ≤ q) :
    legendreSym p ((q - r : ℕ) : ℤ) = -legendreSym p r := by
  rw [legendreSym_sub_eq hq hr, hneg]
  ring

theorem legendreSym_natCast_eq_zero {r : ℕ} (h : p ∣ r) : legendreSym p r = 0 := by
  rw [legendreSym.eq_zero_iff, Int.cast_natCast, ZMod.natCast_eq_zero_iff]
  exact h

/-- `Σ_{r<p} (r/p) = 0`. -/
theorem sum_range_legendreSym (hp2 : p ≠ 2) : ∑ r ∈ range p, legendreSym p r = 0 := by
  have hz := quadraticChar_sum_zero (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  rw [← hz]
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine sum_nbij' (fun r => (r : ZMod p)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
  · intro r _; exact mem_univ _
  · intro a _; exact mem_range.mpr (ZMod.val_lt a)
  · intro r hr; exact ZMod.val_cast_of_lt (mem_range.mp hr)
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro r _; simp [legendreSym]

/-- Sums of `(r/p)` are periodic in the upper limit. -/
theorem sum_range_legendreSym_add (hp2 : p ≠ 2) (L c : ℕ) :
    ∑ r ∈ range (L * p + c), legendreSym p r = ∑ r ∈ range c, legendreSym p r := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show (L + 1) * p + c = p + (L * p + c) by ring, sum_range_add, sum_range_legendreSym hp2,
      zero_add, ← ih]
    refine sum_congr rfl fun r _ => ?_
    rw [legendreSym.mod, legendreSym.mod p r]
    push_cast
    rw [show (p : ℤ) + r = r + p * 1 by ring, Int.add_mul_emod_self_left]

theorem sum_range_legendreSym_eq_Ioo (n : ℕ) :
    ∑ r ∈ range n, legendreSym p r = ∑ r ∈ Ioo 0 n, legendreSym p r := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : range n = insert 0 (Ioo 0 n) := by
    ext x; simp only [mem_range, mem_insert, mem_Ioo]; omega
  rw [this, sum_insert (by simp), legendreSym_natCast_eq_zero (dvd_zero p), zero_add]

/-- `S(3/4) = S(1/4)` for odd `χ`. -/
theorem sum_three_quarters_eq (hp4 : p % 4 = 3) (hneg : legendreSym p (-1) = -1) :
    ∑ r ∈ range ((3 * p + 3) / 4), legendreSym p r =
      ∑ r ∈ range ((p + 3) / 4), legendreSym p r := by
  have hp2 : p ≠ 2 := by omega
  have hsplit := sum_Ico_eq_sub (fun r => legendreSym p r) (show (3 * p + 3) / 4 ≤ p by omega)
  rw [sum_range_legendreSym hp2, zero_sub] at hsplit
  have hrefl : ∑ r ∈ Ico ((3 * p + 3) / 4) p, legendreSym p r =
      -∑ r ∈ Ioo 0 ((p + 3) / 4), legendreSym p r := by
    rw [← sum_neg_distrib]
    refine sum_nbij' (fun r => p - r) (fun s => p - s) ?_ ?_ ?_ ?_ ?_
    · intro r hr; simp only [mem_Ico, mem_Ioo] at hr ⊢; omega
    · intro s hs; simp only [mem_Ico, mem_Ioo] at hs ⊢; omega
    · intro r hr; simp only [mem_Ico] at hr; omega
    · intro s hs; simp only [mem_Ioo] at hs; omega
    · intro r hr
      simp only [mem_Ico] at hr
      have := legendreSym_sub hneg (dvd_refl p) (show p - r ≤ p by omega)
      rw [Nat.sub_sub_self hr.2.le] at this
      rw [this]
  rw [sum_range_legendreSym_eq_Ioo ((p + 3) / 4)]
  linarith

/-- **Doubling.**  For `p ≡ 3 (mod 8)`: `Σ_{0<r<p/4} (r/p) = 0`. -/
theorem sum_quarter_eq_zero (hp8 : p % 8 = 3) :
    ∑ r ∈ range ((p + 3) / 4), legendreSym p r = 0 := by
  have hp2 : p ≠ 2 := by omega
  have h2 : legendreSym p 2 = -1 := by
    have hp2' : p % 2 = 1 := by omega
    rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]; simp [hp8, hp2']
  have hneg : legendreSym p (-1) = -1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four (by omega)]
  obtain ⟨u, hu⟩ : ∃ u, p = 8 * u + 3 := ⟨p / 8, by omega⟩
  have hA : (p + 3) / 4 = 2 * u + 1 := by omega
  rw [hA]
  set A := ∑ r ∈ range (2 * u + 1), legendreSym p r with hAdef
  set O := ∑ j ∈ range (2 * u + 1), legendreSym p ((2 * j + 1 : ℕ) : ℤ) with hO
  have hmul : ∀ r : ℕ, legendreSym p ((2 * r : ℕ) : ℤ) = -legendreSym p r := by
    intro r; push_cast; rw [legendreSym.mul, h2]; ring
  -- `E = −A + O`
  have hE : ∑ r ∈ range (2 * (2 * u + 1)), legendreSym p r = -A + O := by
    rw [sum_range_two_mul, sum_add_distrib]
    simp only [hmul, sum_neg_distrib]
    rfl
  -- `Σ_{r<4u+2} χ(2r) = −A + Σ χ(4u + 2 + 2i) = −A − O`
  have hhigh : ∑ i ∈ range (2 * u + 1), legendreSym p ((2 * (2 * u + 1 + i) : ℕ) : ℤ) = -O := by
    calc ∑ i ∈ range (2 * u + 1), legendreSym p ((2 * (2 * u + 1 + i) : ℕ) : ℤ)
        = ∑ i ∈ range (2 * u + 1), -legendreSym p ((2 * (2 * u + 1 - 1 - i) + 1 : ℕ) : ℤ) := by
          refine sum_congr rfl fun i hi => ?_
          rw [mem_range] at hi
          have := legendreSym_sub hneg (dvd_refl p) (show 2 * (2 * u + 1 - 1 - i) + 1 ≤ p by omega)
          rw [show p - (2 * (2 * u + 1 - 1 - i) + 1) = 2 * (2 * u + 1 + i) by omega] at this
          exact this
      _ = -O := by
          rw [sum_neg_distrib, hO,
            sum_range_reflect (fun j => legendreSym p ((2 * j + 1 : ℕ) : ℤ)) (2 * u + 1)]
  have hD : ∑ r ∈ range (2 * (2 * u + 1)), legendreSym p ((2 * r : ℕ) : ℤ) = -A - O := by
    rw [show 2 * (2 * u + 1) = (2 * u + 1) + (2 * u + 1) by ring, sum_range_add, hhigh]
    simp only [hmul, sum_neg_distrib]
    rw [hAdef]
    ring
  have hD' : ∑ r ∈ range (2 * (2 * u + 1)), legendreSym p ((2 * r : ℕ) : ℤ) =
      -∑ r ∈ range (2 * (2 * u + 1)), legendreSym p r := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun r _ => hmul r
  rw [hE] at hD'
  linarith

/-! ### The drift weight on the units -/

theorem one_lt_prime_pow {k : ℕ} (hk : 1 ≤ k) : 1 < p ^ k :=
  Nat.one_lt_pow (by omega) hp.out.one_lt

/-- The drift weight sums to zero over the units modulo `pᵏ`. -/
theorem sum_units_quarterWeight (hp2 : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    ∑ r ∈ range (p ^ k) with (p ^ k).Coprime r, quarterWeight (p ^ k) r = 0 := by
  have hq1 := one_lt_prime_pow (p := p) hk
  have hpos : ∀ r ∈ {r ∈ range (p ^ k) | (p ^ k).Coprime r}, 0 < r := by
    intro r hr
    rw [mem_filter] at hr
    rcases Nat.eq_zero_or_pos r with rfl | h
    · rw [Nat.coprime_zero_right] at hr; omega
    · exact h
  have hrefl : ∑ r ∈ range (p ^ k) with (p ^ k).Coprime r, quarterWeight (p ^ k) r =
      -∑ r ∈ range (p ^ k) with (p ^ k).Coprime r, quarterWeight (p ^ k) r := by
    rw [← sum_neg_distrib]
    refine sum_nbij' (fun r => p ^ k - r) (fun r => p ^ k - r) ?_ ?_ ?_ ?_ ?_
    · intro r hr
      have h0 := hpos r hr
      simp only [mem_filter, mem_range] at hr ⊢
      exact ⟨by omega, (Nat.coprime_self_sub_right hr.1.le).mpr hr.2⟩
    · intro r hr
      have h0 := hpos r hr
      simp only [mem_filter, mem_range] at hr ⊢
      exact ⟨by omega, (Nat.coprime_self_sub_right hr.1.le).mpr hr.2⟩
    · intro r hr; simp only [mem_filter, mem_range] at hr; omega
    · intro r hr; simp only [mem_filter, mem_range] at hr; omega
    · intro r hr
      have h0 := hpos r hr
      simp only [mem_filter, mem_range] at hr
      rw [quarterWeight_sub hr.1 (not_pow_dvd_four_mul hp2 h0 hr.1), neg_neg]
  linarith

/-- The `χ`-twisted drift weight over the units: `(χ(−1) − 1) Σ_{q/4<r<q/2} χ(r)`. -/
theorem sum_units_legendre_quarterWeight_eq (hp2 : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    ∑ r ∈ range (p ^ k) with (p ^ k).Coprime r, legendreSym p r * quarterWeight (p ^ k) r =
      (legendreSym p (-1) - 1) *
        ∑ r ∈ Ico ((p ^ k + 3) / 4) ((p ^ k + 1) / 2), legendreSym p r := by
  set q := p ^ k with hqdef
  have hq1 : 1 < q := one_lt_prime_pow hk
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (Odd.pow (hp.out.odd_of_ne_two hp2))
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  -- restrict to `0 < r < q`
  have hU : ∑ r ∈ range q with q.Coprime r, legendreSym p r * quarterWeight q r =
      ∑ r ∈ Ioo 0 q, legendreSym p r * quarterWeight q r := by
    rw [sum_filter_of_ne]
    · have : range q = insert 0 (Ioo 0 q) := by
        ext x; simp only [mem_range, mem_insert, mem_Ioo]; omega
      rw [this, sum_insert (by simp), legendreSym_natCast_eq_zero (dvd_zero p), zero_mul,
        zero_add]
    · intro r _ hr
      refine Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h => ?_)
      exact hr (by rw [legendreSym_natCast_eq_zero h, zero_mul])
  set T : ℤ → ℤ := fun d => ∑ r ∈ Ioo 0 q,
    legendreSym p r * (if ((4 * r / q : ℕ) : ℤ) = d then 1 else 0) with hT
  have hsplit : ∑ r ∈ Ioo 0 q, legendreSym p r * quarterWeight q r = T 2 - T 1 := by
    simp only [hT, ← sum_sub_distrib, ← mul_sub]
    rfl
  -- reflection exchanges the digit levels `1` and `2`
  have hsq : legendreSym p (-1) ^ 2 = 1 := legendreSym.sq_one p (by
    rw [Int.cast_neg, Int.cast_one, neg_ne_zero]; exact one_ne_zero)
  have hT21 : T 2 = legendreSym p (-1) * T 1 := by
    simp only [hT]
    rw [mul_sum]
    refine sum_nbij' (fun r => q - r) (fun r => q - r) ?_ ?_ ?_ ?_ ?_
    · intro r hr; simp only [mem_Ioo] at hr ⊢; omega
    · intro r hr; simp only [mem_Ioo] at hr ⊢; omega
    · intro r hr; simp only [mem_Ioo] at hr; omega
    · intro r hr; simp only [mem_Ioo] at hr; omega
    · intro r hr
      simp only [mem_Ioo] at hr
      have hD : 4 * r / q ≤ 3 := by
        have : 4 * r / q < 4 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
        omega
      have hsub := four_mul_sub_div hr.2 (not_pow_dvd_four_mul hp2 hr.1 hr.2)
      rw [legendreSym_sub_eq hpq hr.2.le, hsub, Nat.cast_sub hD, Nat.cast_ofNat]
      have : ((3 : ℤ) - ((4 * r / q : ℕ) : ℤ) = 1) ↔ (((4 * r / q : ℕ) : ℤ) = 2) := by omega
      simp only [this]
      linear_combination (-(legendreSym p r * if ((4 * r / q : ℕ) : ℤ) = 2 then 1 else 0)) * hsq
  -- the level `1` is the interval `[q/4, q/2)`
  have hT1 : T 1 = ∑ r ∈ Ico ((q + 3) / 4) ((q + 1) / 2), legendreSym p r := by
    simp only [hT, mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    congr 1
    ext r
    simp only [mem_filter, mem_Ioo, mem_Ico]
    have h1 : 1 ≤ 4 * r / q ↔ 1 * q ≤ 4 * r := Nat.le_div_iff_mul_le (by omega)
    have h2 : 4 * r / q < 2 ↔ 4 * r < 2 * q := Nat.div_lt_iff_lt_mul (by omega)
    constructor
    · rintro ⟨⟨_, _⟩, h⟩
      have h' : 4 * r / q = 1 := by exact_mod_cast h
      omega
    · rintro ⟨ha, hb⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have : 4 * r / q = 1 := by omega
      rw [this]; rfl
  rw [hU, hsplit, hT21, hT1]
  ring

/-- The `χ`-twisted drift weight over the units: `−2 Σ_{q/4<r<q/2} χ(r)` for odd `χ`. -/
theorem sum_units_legendre_quarterWeight (hp2 : p ≠ 2) (hneg : legendreSym p (-1) = -1)
    {k : ℕ} (hk : 1 ≤ k) :
    ∑ r ∈ range (p ^ k) with (p ^ k).Coprime r, legendreSym p r * quarterWeight (p ^ k) r =
      -2 * ∑ r ∈ Ico ((p ^ k + 3) / 4) ((p ^ k + 1) / 2), legendreSym p r := by
  rw [sum_units_legendre_quarterWeight_eq hp2 hk, hneg]
  ring

/-- Reduction modulo `p` for odd `χ`: the twisted interval sum equals `S(1/2) − S(1/4)`. -/
theorem sum_Ico_quarter_half_eq_sub (hp4 : p % 4 = 3) {k : ℕ} (hk : 1 ≤ k) :
    ∑ r ∈ Ico ((p ^ k + 3) / 4) ((p ^ k + 1) / 2), legendreSym p r =
      ∑ r ∈ range ((p + 1) / 2), legendreSym p r -
        ∑ r ∈ range ((p + 3) / 4), legendreSym p r := by
  have hp2 : p ≠ 2 := by omega
  have hneg : legendreSym p (-1) = -1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four hp4]
  have hq : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ]; congr 1; omega
  have hmodd : p ^ (k - 1) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (hp.out.odd_of_ne_two hp2))
  rw [sum_Ico_eq_sub _ (by omega)]
  -- the upper limit `(q + 1)/2`
  have hhalf : ∑ r ∈ range ((p ^ k + 1) / 2), legendreSym p r =
      ∑ r ∈ range ((p + 1) / 2), legendreSym p r := by
    obtain ⟨L, hL⟩ : ∃ L, p ^ (k - 1) = 2 * L + 1 := ⟨p ^ (k - 1) / 2, by omega⟩
    have hX : p ^ k = 2 * (L * p) + p := by rw [hq, hL]; ring
    rw [show (p ^ k + 1) / 2 = L * p + (p + 1) / 2 by omega, sum_range_legendreSym_add hp2]
  -- the lower limit `(q + 3)/4`
  have hquarter : ∑ r ∈ range ((p ^ k + 3) / 4), legendreSym p r =
      ∑ r ∈ range ((p + 3) / 4), legendreSym p r := by
    obtain ⟨L, hL⟩ : ∃ L, p ^ (k - 1) = 4 * L + 1 ∨ p ^ (k - 1) = 4 * L + 3 :=
      ⟨p ^ (k - 1) / 4, by omega⟩
    rcases hL with hL | hL
    · have hX : p ^ k = 4 * (L * p) + p := by rw [hq, hL]; ring
      rw [show (p ^ k + 3) / 4 = L * p + (p + 3) / 4 by omega, sum_range_legendreSym_add hp2]
    · have hX : p ^ k = 4 * (L * p) + 3 * p := by rw [hq, hL]; ring
      rw [show (p ^ k + 3) / 4 = L * p + (3 * p + 3) / 4 by omega, sum_range_legendreSym_add hp2,
        sum_three_quarters_eq hp4 hneg]
  rw [hhalf, hquarter]

/-- Reduction modulo `p`: the twisted interval sum equals `S(1/2) − S(1/4) = S(1/2)`. -/
theorem sum_Ico_quarter_half (hp8 : p % 8 = 3) {k : ℕ} (hk : 1 ≤ k) :
    ∑ r ∈ Ico ((p ^ k + 3) / 4) ((p ^ k + 1) / 2), legendreSym p r =
      ∑ r ∈ range ((p + 1) / 2), legendreSym p r := by
  rw [sum_Ico_quarter_half_eq_sub (by omega) hk, sum_quarter_eq_zero hp8, sub_zero]

/-! ### The drift law -/

theorem legendreSym_stonehamPA {k : ℕ} (hk : 1 ≤ k) : legendreSym p (stonehamPA p k) = 1 := by
  rw [legendreSym.mod, ← Int.natCast_mod, stonehamPA_mod hp.out.two_le hk, Nat.cast_one,
    legendreSym.at_one]

theorem not_dvd_two_mul_stonehamPA (hp2 : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    ¬ p ∣ 2 * stonehamPA p k := by
  intro h
  rcases hp.out.dvd_mul.mp h with h2 | hA
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2)
  · have := stonehamPA_mod hp.out.two_le hk
    rw [Nat.mod_eq_zero_of_dvd hA] at this
    exact absurd this (by norm_num)

/-- **One period of the window orbit carries drift `Σ_{0<r<p/2} (r/p)`.** -/
theorem sum_period_quarterWeight (hp8 : p % 8 = 3)
    (hord : ∀ d < p - 1, 0 < d → ¬ p ∣ 2 ^ d - 1) (hwief : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1)
    {k : ℕ} (hk : 1 ≤ k) :
    ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)),
        quarterWeight (p ^ k) (2 * stonehamPA p k * 4 ^ i % p ^ k) =
      ∑ r ∈ range ((p + 1) / 2), legendreSym p r := by
  have hp2 : p ≠ 2 := by omega
  have h2 : legendreSym p 2 = -1 := by
    have hp2' : p % 2 = 1 := by omega
    rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]; simp [hp8, hp2']
  have hneg : legendreSym p (-1) = -1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four (by omega)]
  have h := two_mul_sum_four_orbit hp2 hord hwief h2 hk (not_dvd_two_mul_stonehamPA hp2 hk)
    (quarterWeight (p ^ k))
  rw [sum_units_quarterWeight hp2 hk, sum_units_legendre_quarterWeight hp2 hneg hk,
    sum_Ico_quarter_half hp8 hk] at h
  have hχa : legendreSym p ((2 * stonehamPA p k : ℕ) : ℤ) = -1 := by
    push_cast; rw [legendreSym.mul, h2, legendreSym_stonehamPA hk]; ring
  rw [hχa] at h
  linarith

/-- The period `(p − 1)/2 · p^{k−1}` of `4` modulo `pᵏ`. -/
def FourPeriod (p : ℕ) : Prop := ∀ k, 1 ≤ k → p ^ k ∣ 4 ^ ((p - 1) / 2 * p ^ (k - 1)) - 1

/-- If `2` is a primitive root modulo `p²`, then `4` has period `(p − 1)/2 · p^{k−1}`. -/
theorem fourPeriod_of_primitive_root (hp2 : p ≠ 2)
    (hord : ∀ d < p - 1, 0 < d → ¬ p ∣ 2 ^ d - 1) (hwief : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1) :
    FourPeriod p := by
  intro k hk
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have h4P : 4 ^ ((p - 1) / 2 * p ^ (k - 1)) = 2 ^ ((p - 1) * p ^ (k - 1)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← mul_assoc]
    congr 2; omega
  rw [h4P]; exact (pow_dvd_two_pow_sub_one_iff hp2 hord hwief hk).mpr dvd_rfl

omit hp in
theorem orbit_four_add_mul_period (hper : FourPeriod p)
    {k : ℕ} (hk : 1 ≤ k) (a b i : ℕ) :
    a * 4 ^ (b * ((p - 1) / 2 * p ^ (k - 1)) + i) % p ^ k = a * 4 ^ i % p ^ k := by
  set P := (p - 1) / 2 * p ^ (k - 1) with hP
  have h1 : p ^ k ∣ 4 ^ P - 1 := hper k hk
  have hmod : 4 ^ P % p ^ k = 1 % p ^ k :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr h1).symm
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show (b + 1) * P + i = (b * P + i) + P by ring, pow_add, ← mul_assoc, Nat.mul_mod, hmod,
      ← Nat.mul_mod, mul_one, ih]

theorem sum_range_mul_of_periodic {f : ℕ → ℤ} {P : ℕ} (hf : ∀ b i, f (b * P + i) = f i)
    (B : ℕ) : ∑ i ∈ range (B * P), f i = B * ∑ i ∈ range P, f i := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [show (B + 1) * P = B * P + P by ring, sum_range_add, ih]
    simp only [hf]
    push_cast
    ring

/-- **Each window consists of `p` periods of the orbit.** -/
theorem sum_window_stonehamP_eq (hp2 : p ≠ 2) (hper : FourPeriod p) {k : ℕ} (hk : 1 ≤ k) :
    ∑ i ∈ range (p * ((p - 1) / 2 * p ^ (k - 1))),
        digitWeight (quatDigit (stonehamP p) ((p ^ k + 1) / 2 + i + 1)) =
      p * ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)),
        quarterWeight (p ^ k) (2 * stonehamPA p k * 4 ^ i % p ^ k) := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hW : 2 * (p * ((p - 1) / 2 * p ^ (k - 1))) = p ^ k * (p - 1) := by
    have hv : 2 * ((p - 1) / 2) = p - 1 := by omega
    have hq : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ]; congr 1; omega
    calc 2 * (p * ((p - 1) / 2 * p ^ (k - 1))) = 2 * ((p - 1) / 2) * (p ^ (k - 1) * p) := by
          ring
      _ = p ^ k * (p - 1) := by rw [hv, ← hq, mul_comm]
  rw [sum_congr rfl fun i hi => by
    rw [quatDigit_stonehamP_window hp3 hodd (by have := mem_range.mp hi; omega)]]
  change ∑ i ∈ range (p * ((p - 1) / 2 * p ^ (k - 1))),
      quarterWeight (p ^ k) (2 * stonehamPA p k * 4 ^ i % p ^ k) = _
  have hper := sum_range_mul_of_periodic
    (f := fun i => quarterWeight (p ^ k) (2 * stonehamPA p k * 4 ^ i % p ^ k))
    (P := (p - 1) / 2 * p ^ (k - 1))
    (fun b i => congrArg (quarterWeight (p ^ k))
      (orbit_four_add_mul_period hper hk _ b i))
    p
  rw [hper]

omit hp in
theorem stonehamP_le (hp3 : 3 ≤ p) : stonehamP p ≤ 4 / (3 * p * 2 ^ p) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hb : ∀ j, stonehamPTerm p j ≤ 1 / ((p : ℝ) * 2 ^ p) * (1 / 4 : ℝ) ^ j := by
    intro j
    unfold stonehamPTerm
    rw [one_div_pow, one_div_mul_one_div, one_div_le_one_div (by positivity) (by positivity)]
    have hj := one_add_two_mul_le_pow hp3 j
    have hexp : p + 2 * j ≤ p ^ (j + 1) := by rw [pow_succ]; nlinarith
    have h1 : (2 : ℝ) ^ p * 4 ^ j ≤ 2 ^ (p ^ (j + 1)) := by
      rw [show (4 : ℝ) ^ j = 2 ^ (2 * j) by rw [pow_mul]; norm_num, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) hexp
    have h2 : (p : ℝ) ≤ (p : ℝ) ^ (j + 1) :=
      le_self_pow₀ (by linarith) (by omega)
    calc (p : ℝ) * 2 ^ p * 4 ^ j = p * (2 ^ p * 4 ^ j) := by ring
      _ ≤ (p : ℝ) ^ (j + 1) * 2 ^ (p ^ (j + 1)) := mul_le_mul h2 h1 (by positivity) (by positivity)
  have hg : Summable fun j : ℕ => 1 / ((p : ℝ) * 2 ^ p) * (1 / 4 : ℝ) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc stonehamP p ≤ ∑' j : ℕ, 1 / ((p : ℝ) * 2 ^ p) * (1 / 4 : ℝ) ^ j :=
        Summable.tsum_le_tsum hb (summable_stonehamPTerm (by omega)) hg
    _ = 4 / (3 * p * 2 ^ p) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        field_simp
        norm_num

omit hp in
/-- The digits of `α_p` before the first window vanish. -/
theorem quatDigit_stonehamP_initial (hp3 : 3 ≤ p) (hodd : p % 2 = 1) {m : ℕ}
    (hm : m ≤ (p + 1) / 2) : quatDigit (stonehamP p) m = 0 := by
  unfold quatDigit
  have h0 : 0 ≤ (4 : ℝ) ^ m * stonehamP p :=
    mul_nonneg (by positivity) (tsum_nonneg fun j => (stonehamPTerm_pos (by omega) j).le)
  have h1 : (4 : ℝ) ^ m * stonehamP p < 1 := by
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have h4 : (4 : ℝ) ^ m ≤ 2 ^ (p + 1) := by
      rw [show (4 : ℝ) ^ m = 2 ^ (2 * m) by rw [pow_mul]; norm_num]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hle := stonehamP_le hp3
    calc (4 : ℝ) ^ m * stonehamP p ≤ 2 ^ (p + 1) * (4 / (3 * p * 2 ^ p)) :=
          mul_le_mul h4 hle (tsum_nonneg fun j => (stonehamPTerm_pos (by omega) j).le)
            (by positivity)
      _ = 8 / (3 * p) := by rw [pow_succ]; field_simp; ring
      _ < 1 := by rw [div_lt_one (by positivity)]; linarith
  rw [Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩]
  rfl

/-- **Drift at the window ends from the period sum.**  If every window period carries drift
`c`, then `D_{α_p}((p^{k+1} + 1)/2) = p k c`. -/
theorem drift_stonehamP_windowEnd_of_period (hp2 : p ≠ 2) (hper : FourPeriod p) {c : ℤ}
    (hc : ∀ k, 1 ≤ k → ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)),
      quarterWeight (p ^ k) (2 * stonehamPA p k * 4 ^ i % p ^ k) = c) (k : ℕ) :
    drift (stonehamP p) ((p ^ (k + 1) + 1) / 2) = p * k * c := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  induction k with
  | zero =>
    rw [drift_eq_sum_digitWeight]
    simp only [zero_add, pow_one, Nat.cast_zero, mul_zero, zero_mul]
    refine sum_eq_zero fun n hn => ?_
    rw [quatDigit_stonehamP_initial hp3 hodd (by have := mem_range.mp hn; omega)]
    rfl
  | succ k ih =>
    have hQodd : p ^ (k + 1) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (Nat.odd_iff.mpr hodd))
    have hlen : (p ^ (k + 1 + 1) + 1) / 2 =
        (p ^ (k + 1) + 1) / 2 + p * ((p - 1) / 2 * p ^ (k + 1 - 1)) := by
      obtain ⟨v, hv⟩ : ∃ v, p = 2 * v + 1 := ⟨(p - 1) / 2, by omega⟩
      have hv' : (p - 1) / 2 = v := by omega
      rw [hv']
      have e1 : p ^ (k + 1 + 1) = 2 * (v * p ^ (k + 1)) + p ^ (k + 1) := by
        calc p ^ (k + 1 + 1) = p ^ (k + 1) * p := pow_succ _ _
          _ = p ^ (k + 1) * (2 * v + 1) := by rw [← hv]
          _ = 2 * (v * p ^ (k + 1)) + p ^ (k + 1) := by ring
      have e2 : p * (v * p ^ (k + 1 - 1)) = v * p ^ (k + 1) := by
        rw [Nat.add_sub_cancel, pow_succ]; ring
      rw [e2]
      omega
    have hsplit : drift (stonehamP p) ((p ^ (k + 1 + 1) + 1) / 2) =
        drift (stonehamP p) ((p ^ (k + 1) + 1) / 2) +
          ∑ i ∈ range (p * ((p - 1) / 2 * p ^ (k + 1 - 1))),
            digitWeight (quatDigit (stonehamP p) ((p ^ (k + 1) + 1) / 2 + i + 1)) := by
      rw [hlen, drift_eq_sum_digitWeight, drift_eq_sum_digitWeight, sum_range_add]
    rw [hsplit, ih, sum_window_stonehamP_eq hp2 hper (by omega), hc (k + 1) (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- **The class-number drift law.**  For a prime `p ≡ 3 (mod 8)` for which `2` is a primitive
root modulo `p²`, the parity drift of `α_p` at `(p^{k+1} + 1)/2` is `p k Σ_{0<r<p/2} (r/p)`. -/
theorem drift_stonehamP_windowEnd (hp8 : p % 8 = 3)
    (hord : ∀ d < p - 1, 0 < d → ¬ p ∣ 2 ^ d - 1) (hwief : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1) (k : ℕ) :
    drift (stonehamP p) ((p ^ (k + 1) + 1) / 2) =
      p * k * ∑ r ∈ range ((p + 1) / 2), legendreSym p r :=
  drift_stonehamP_windowEnd_of_period (by omega)
    (fourPeriod_of_primitive_root (by omega) hord hwief)
    (fun _ hk => sum_period_quarterWeight hp8 hord hwief hk) k

/-- For `p ≡ 5 (mod 8)` the character `χ` is even and every period carries zero drift. -/
theorem sum_period_quarterWeight_of_mod_eight_eq_five (hp8 : p % 8 = 5)
    (hord : ∀ d < p - 1, 0 < d → ¬ p ∣ 2 ^ d - 1) (hwief : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1)
    {k : ℕ} (hk : 1 ≤ k) :
    ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)),
      quarterWeight (p ^ k) (2 * stonehamPA p k * 4 ^ i % p ^ k) = 0 := by
  have hp2 : p ≠ 2 := by omega
  have h2 : legendreSym p 2 = -1 := by
    have hp2' : p % 2 = 1 := by omega
    rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]; simp [hp8, hp2']
  have hpos : legendreSym p (-1) = 1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_one_mod_four (by omega)]
  have h := two_mul_sum_four_orbit hp2 hord hwief h2 hk (not_dvd_two_mul_stonehamPA hp2 hk)
    (quarterWeight (p ^ k))
  rw [sum_units_quarterWeight hp2 hk, sum_units_legendre_quarterWeight_eq hp2 hk, hpos] at h
  linarith

/-- **Bounded drift for `p ≡ 5 (mod 8)`.**  If `2` is a primitive root modulo `p²` and
`p ≡ 5 (mod 8)`, the parity drift of `α_p` vanishes at every window end. -/
theorem drift_stonehamP_windowEnd_of_mod_eight_eq_five (hp8 : p % 8 = 5)
    (hord : ∀ d < p - 1, 0 < d → ¬ p ∣ 2 ^ d - 1) (hwief : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1) (k : ℕ) :
    drift (stonehamP p) ((p ^ (k + 1) + 1) / 2) = 0 := by
  rw [drift_stonehamP_windowEnd_of_period (by omega)
    (fourPeriod_of_primitive_root (by omega) hord hwief)
    (fun _ hk => sum_period_quarterWeight_of_mod_eight_eq_five hp8 hord hwief hk) k]
  ring

/-! ### Instances: `h(−11) = h(−19) = 1`, `h(−59) = 3` -/

/-- `D_{α_{11}}((11^{k+1} + 1)/2) = 33k`. -/
theorem drift_stonehamP_eleven (k : ℕ) :
    drift (stonehamP 11) ((11 ^ (k + 1) + 1) / 2) = 33 * k := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  rw [drift_stonehamP_windowEnd (p := 11) (by norm_num) (by decide) (by decide) k]
  have hE : ∑ r ∈ range ((11 + 1) / 2), legendreSym 11 (r : ℤ) = 3 := by
    simp only [show (11 + 1) / 2 = 6 by norm_num, sum_range_succ, sum_range_zero]; norm_num
  rw [hE]; push_cast; ring

/-- `D_{α_{19}}((19^{k+1} + 1)/2) = 57k`. -/
theorem drift_stonehamP_nineteen (k : ℕ) :
    drift (stonehamP 19) ((19 ^ (k + 1) + 1) / 2) = 57 * k := by
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  rw [drift_stonehamP_windowEnd (p := 19) (by norm_num) (by decide) (by decide) k]
  have hE : ∑ r ∈ range ((19 + 1) / 2), legendreSym 19 (r : ℤ) = 3 := by
    simp only [show (19 + 1) / 2 = 10 by norm_num, sum_range_succ, sum_range_zero]; norm_num
  rw [hE]; push_cast; ring

/-- `D_{α_{59}}((59^{k+1} + 1)/2) = 531k`  (`h(−59) = 3`). -/
theorem drift_stonehamP_fifty_nine (k : ℕ) :
    drift (stonehamP 59) ((59 ^ (k + 1) + 1) / 2) = 531 * k := by
  haveI : Fact (Nat.Prime 59) := ⟨by norm_num⟩
  rw [drift_stonehamP_windowEnd (p := 59) (by norm_num) (by decide) (by decide) k]
  have hE : ∑ r ∈ range ((59 + 1) / 2), legendreSym 59 (r : ℤ) = 9 := by
    simp only [show (59 + 1) / 2 = 30 by norm_num, sum_range_succ, sum_range_zero]; norm_num
  rw [hE]; push_cast; ring

/-- `D_{α_5}((5^{k+1} + 1)/2) = 0`. -/
theorem drift_stonehamP_five (k : ℕ) : drift (stonehamP 5) ((5 ^ (k + 1) + 1) / 2) = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact drift_stonehamP_windowEnd_of_mod_eight_eq_five (by norm_num) (by decide) (by decide) k

/-- `D_{α_{13}}((13^{k+1} + 1)/2) = 0`. -/
theorem drift_stonehamP_thirteen (k : ℕ) :
    drift (stonehamP 13) ((13 ^ (k + 1) + 1) / 2) = 0 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact drift_stonehamP_windowEnd_of_mod_eight_eq_five (by norm_num) (by decide) (by decide) k

end GaloisForLFunctions.HTGeometry.StonehamPrimeDrift
