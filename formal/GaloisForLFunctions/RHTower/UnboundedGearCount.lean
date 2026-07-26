/-
# Unbounded gear count: members of the integral multiplicative FE class with arbitrarily many
off-line zero lines

For every bound `n` the class `IntegralMultiplicativeFEClass` contains a member whose zero set
meets at least `n` distinct vertical lines strictly inside the open left half-strip
`0 < Re s < 1/2`.

The mechanism is the base-`2^m` **gear**: the two-factor single-column Dirichlet polynomial
`gear m s = (1 − 2·(2^m)^{−s})(1 − 2^{m−1}·(2^m)^{−s})`.
Its two local factors mirror across the conductor `2·2^{m−1} = 2^m`, giving the exact degree-zero
functional equation `gear m s = (2^m)^{1−2s}·gear m (1−s)`.  Its coefficient stream is supported on
`{1, 2^m, 2^{2m}}` with values `(1, −(2 + 2^{m−1}), 2^m)`: integer-valued and multiplicative, since
the support is a single prime column.  The first factor vanishes where `(2^m)^σ = 2`, i.e. at the
real point `σ = 1/m` — off the critical line for every `m ≥ 3`.

Gears at distinct `m` multiply without leaving the class: the coefficient stream of the product is
the Dirichlet convolution of the factor streams (multiplicative, integral, finite support), the
`L`-series identity holds at every `s` because all supports are finite, and the conductors multiply
(`Q = ∏ 2^m`).  The product over `S = {3, …, n + 3}` therefore lies in the class and vanishes at the
`n + 1` distinct real points `1/m`, `m ∈ S`, all in `(0, 1/2)`: the number of off-line zero lines a
member of the three-way conjunction can carry is unbounded.
-/
import GaloisForLFunctions.RHTower.DegreeZeroOffline
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

noncomputable section

namespace RHTower

open Complex

/-! ### §1 The base-`2^m` gear and its functional equation -/

/-- The **gear at level `m`**: the degree-zero Dirichlet polynomial
`gear m s = (1 − 2·(2^m)^{−s})(1 − 2^{m−1}·(2^m)^{−s})` on the single prime column `2` with
conductor `2^m`. -/
def gear (m : ℕ) : ℂ → ℂ :=
  fun s => (1 - 2 * ((2 : ℂ) ^ m) ^ (-s)) * (1 - (2 : ℂ) ^ (m - 1) * ((2 : ℂ) ^ m) ^ (-s))

/-- **The exact degree-zero functional equation** `gear m s = (2^m)^{1−2s}·gear m (1−s)`.  With
`w = (2^m)^{−s}` the reflected factors read `1 − 2/(2^m w)` and `1 − 2^{m−1}/(2^m w)`; the mirror
identity `2·2^{m−1} = 2^m` turns their product into `gear m s/(2^m w²)`, and `(2^m)^{1−2s} = 2^m w²`
cancels the denominator. -/
theorem gear_fe (m : ℕ) (hm : 3 ≤ m) (s : ℂ) :
    gear m s = ((2 ^ m : ℕ) : ℂ) ^ (1 - 2 * s) * gear m (1 - s) := by
  have hB : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcast : ((2 ^ m : ℕ) : ℂ) = (2 : ℂ) ^ m := by push_cast; ring
  have hcm : (2 : ℂ) ^ m = 2 * (2 : ℂ) ^ (m - 1) := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hBs : ((2 : ℂ) ^ m) ^ s = (((2 : ℂ) ^ m) ^ (-s))⁻¹ := by rw [Complex.cpow_neg, inv_inv]
  have hz : ((2 : ℂ) ^ m) ^ (-(1 - s)) = ((2 : ℂ) ^ m * ((2 : ℂ) ^ m) ^ (-s))⁻¹ := by
    rw [show -(1 - s) = (-1 : ℂ) + s by ring, Complex.cpow_add _ _ hB,
      show (-1 : ℂ) = -(1 : ℂ) by ring, Complex.cpow_neg, Complex.cpow_one, hBs, mul_inv]
  have hq : ((2 : ℂ) ^ m) ^ (1 - 2 * s) = (2 : ℂ) ^ m * (((2 : ℂ) ^ m) ^ (-s)) ^ 2 := by
    rw [show 1 - 2 * s = (1 : ℂ) + (-s + -s) by ring, Complex.cpow_add _ _ hB, Complex.cpow_one,
      Complex.cpow_add _ _ hB, sq]
  rw [hcast]
  simp only [gear, hz, hq]
  rw [hcm]
  have hX : ((2 : ℂ) * (2 : ℂ) ^ (m - 1)) ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by rw [← hcm]; exact hB))
  field_simp
  ring

/-! ### §2 The integer multiplicative coefficient stream and its `L`-series -/

/-- The coefficient stream of `gear m`: supported on `{1, 2^m, 2^{2m}}` with values `1`,
`−(2 + 2^{m−1})`, `2^m`. -/
def gearCoeff (m : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 1 then 1 else if n = 2 ^ m then -(2 + (2 : ℂ) ^ (m - 1))
            else if n = 2 ^ (2 * m) then (2 : ℂ) ^ m else 0, by
    have h1 : (0 : ℕ) ≠ 1 := by norm_num
    have h2 : (0 : ℕ) ≠ 2 ^ m := (pow_pos (by norm_num) m).ne
    have h3 : (0 : ℕ) ≠ 2 ^ (2 * m) := (pow_pos (by norm_num) (2 * m)).ne
    simp only [if_neg h1, if_neg h2, if_neg h3]⟩

private theorem gearCoeff_apply (m n : ℕ) :
    gearCoeff m n = if n = 1 then 1 else if n = 2 ^ m then -(2 + (2 : ℂ) ^ (m - 1))
            else if n = 2 ^ (2 * m) then (2 : ℂ) ^ m else 0 := rfl

/-- For `m ≥ 3` the three support points `1 < 2^m < 2^{2m}` are pairwise distinct. -/
private theorem gearSupp (m : ℕ) (hm : 3 ≤ m) :
    (1 : ℕ) ≠ 2 ^ m ∧ (1 : ℕ) ≠ 2 ^ (2 * m) ∧ (2 ^ m : ℕ) ≠ 2 ^ (2 * m) := by
  refine ⟨?_, ?_, ?_⟩
  · have : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have : 2 ≤ 2 ^ (2 * m) := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have : 2 ^ m < 2 ^ (2 * m) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

/-- The value of `gearCoeff m` at `1` is `1`. -/
theorem gearCoeff_one (m : ℕ) : gearCoeff m 1 = 1 := by rw [gearCoeff_apply, if_pos rfl]

/-- The value of `gearCoeff m` at `2^m` is `−(2 + 2^{m−1})`. -/
theorem gearCoeff_pm (m : ℕ) (hm : 3 ≤ m) : gearCoeff m (2 ^ m) = -(2 + (2 : ℂ) ^ (m - 1)) := by
  obtain ⟨d1, -, -⟩ := gearSupp m hm
  rw [gearCoeff_apply, if_neg d1.symm, if_pos rfl]

/-- The value of `gearCoeff m` at `2^{2m}` is `2^m`. -/
theorem gearCoeff_p2m (m : ℕ) (hm : 3 ≤ m) : gearCoeff m (2 ^ (2 * m)) = (2 : ℂ) ^ m := by
  obtain ⟨-, d2, d3⟩ := gearSupp m hm
  rw [gearCoeff_apply, if_neg d2.symm, if_neg d3.symm, if_pos rfl]

/-- **`gearCoeff m` is multiplicative.**  The support `{1, 2^m, 2^{2m}}` is a single prime column,
so a coprime factorisation of a support point carries all its `2`-mass on one factor; the values
then multiply, and any other coprime product has one vanishing factor. -/
theorem gearCoeff_multiplicative (m : ℕ) (hm : 3 ≤ m) :
    ArithmeticFunction.IsMultiplicative (gearCoeff m) := by
  have hno : ∀ i j : ℕ, i ≠ 0 → j ≠ 0 → ¬ Nat.Coprime ((2 : ℕ) ^ i) (2 ^ j) := by
    intro i j hi hj hc
    have h2 : (2 : ℕ) ∣ Nat.gcd (2 ^ i) (2 ^ j) :=
      Nat.dvd_gcd (dvd_pow_self 2 hi) (dvd_pow_self 2 hj)
    rw [hc.gcd_eq_one] at h2
    exact absurd h2 (by decide)
  constructor
  · exact gearCoeff_one m
  · intro a b hcop
    have hval : ∀ k : ℕ, gearCoeff m k ≠ 0 → k = 1 ∨ k = 2 ^ m ∨ k = 2 ^ (2 * m) := by
      intro k hk
      rw [gearCoeff_apply] at hk
      by_contra hc
      rw [not_or, not_or] at hc
      obtain ⟨p1, p2, p3⟩ := hc
      rw [if_neg p1, if_neg p2, if_neg p3] at hk
      exact hk rfl
    rcases eq_or_ne (a * b) 1 with h1 | h1
    · obtain ⟨ha, hb⟩ := mul_eq_one.mp h1
      subst ha; subst hb; simp [gearCoeff_one]
    rcases eq_or_ne (a * b) (2 ^ m) with h8 | h8
    · rcases coprime_mul_two_pow a b hcop m h8 with rfl | rfl
      · obtain rfl : b = 2 ^ m := by omega
        simp only [one_mul, gearCoeff_one, gearCoeff_pm m hm]
      · obtain rfl : a = 2 ^ m := by omega
        simp only [mul_one, gearCoeff_one, gearCoeff_pm m hm]
    rcases eq_or_ne (a * b) (2 ^ (2 * m)) with h64 | h64
    · rcases coprime_mul_two_pow a b hcop (2 * m) h64 with rfl | rfl
      · obtain rfl : b = 2 ^ (2 * m) := by omega
        simp only [one_mul, gearCoeff_one, gearCoeff_p2m m hm]
      · obtain rfl : a = 2 ^ (2 * m) := by omega
        simp only [mul_one, gearCoeff_one, gearCoeff_p2m m hm]
    · rw [show gearCoeff m (a * b) = 0 by rw [gearCoeff_apply, if_neg h1, if_neg h8, if_neg h64]]
      by_cases ha : gearCoeff m a = 0
      · rw [ha]; ring
      by_cases hb : gearCoeff m b = 0
      · rw [hb]; ring
      exfalso
      rcases hval a ha with r1 | r2 | r3 <;> rcases hval b hb with s1 | s2 | s3 <;> subst_vars
      · exact h1 rfl
      · exact h8 (one_mul _)
      · exact h64 (one_mul _)
      · exact h8 (mul_one _)
      · exact hno m m (by omega) (by omega) hcop
      · exact hno m (2 * m) (by omega) (by omega) hcop
      · exact h64 (mul_one _)
      · exact hno (2 * m) m (by omega) (by omega) hcop
      · exact hno (2 * m) (2 * m) (by omega) (by omega) hcop

/-- **`gearCoeff m` is integer-valued.**  Every value is `1`, `−(2 + 2^{m−1})`, `2^m`, or `0`, and
each is the cast of an integer. -/
theorem gearCoeff_integral (m : ℕ) (n : ℕ) : ∃ k : ℤ, gearCoeff m n = (k : ℂ) := by
  rw [gearCoeff_apply]
  rcases eq_or_ne n 1 with h1 | h1
  · exact ⟨1, by rw [if_pos h1]; norm_num⟩
  rcases eq_or_ne n (2 ^ m) with h2 | h2
  · exact ⟨-(2 + 2 ^ (m - 1)), by rw [if_neg h1, if_pos h2]; push_cast; ring⟩
  rcases eq_or_ne n (2 ^ (2 * m)) with h3 | h3
  · exact ⟨2 ^ m, by rw [if_neg h1, if_neg h2, if_pos h3]; push_cast; ring⟩
  · exact ⟨0, by rw [if_neg h1, if_neg h2, if_neg h3]; norm_num⟩

/-- The Dirichlet series of `gearCoeff m` converges at every `s`: the support `{1, 2^m, 2^{2m}}` is
finite, so the term function vanishes off a finite set. -/
theorem gearCoeff_summable (m : ℕ) (s : ℂ) : LSeriesSummable (fun n => gearCoeff m n) s := by
  apply summable_of_ne_finset_zero (s := ({1, 2 ^ m, 2 ^ (2 * m)} : Finset ℕ))
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  obtain ⟨h1, h2, h3⟩ := hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hpos.ne' _ s, gearCoeff_apply, if_neg h1, if_neg h2, if_neg h3]
    simp

/-- The single-column bridge `(2^{2m})^s = ((2^m)^s)²`, from `log 2^{2m} = 2 log 2^m`. -/
theorem cpow_two_pow_two_mul (m : ℕ) (s : ℂ) :
    ((2 : ℂ) ^ (2 * m)) ^ s = (((2 : ℂ) ^ m) ^ s) ^ 2 := by
  have ha : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have ha2 : (2 : ℂ) ^ (2 * m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hlogm : Complex.log ((2 : ℂ) ^ m) = ((Real.log ((2 : ℝ) ^ m) : ℝ) : ℂ) := by
    rw [show ((2 : ℂ) ^ m) = (((2 : ℝ) ^ m : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_log (by positivity)]
  have hlog2m : Complex.log ((2 : ℂ) ^ (2 * m)) = ((Real.log ((2 : ℝ) ^ (2 * m)) : ℝ) : ℂ) := by
    rw [show ((2 : ℂ) ^ (2 * m)) = (((2 : ℝ) ^ (2 * m) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_log (by positivity)]
  have hr : ((Real.log ((2 : ℝ) ^ (2 * m)) : ℝ) : ℂ) = 2 * ((Real.log ((2 : ℝ) ^ m) : ℝ) : ℂ) := by
    rw [Real.log_pow, Real.log_pow]; push_cast; ring
  rw [sq, ← Complex.cpow_add _ _ ha, Complex.cpow_def_of_ne_zero ha2,
    Complex.cpow_def_of_ne_zero ha, hlog2m, hlogm, hr]
  congr 1; ring

/-- **The `L`-series of `gearCoeff m` is `gear m`.**  The support is `{1, 2^m, 2^{2m}}`, so the
series is the finite sum `1 − (2 + 2^{m−1})·(2^m)^{−s} + 2^m·(2^{2m})^{−s}`, which factors as
`(1 − 2·(2^m)^{−s})(1 − 2^{m−1}·(2^m)^{−s})` via `(2^{2m})^s = ((2^m)^s)²` and the mirror identity
`2·2^{m−1} = 2^m`; valid at every `s`. -/
theorem LSeries_gearCoeff (m : ℕ) (hm : 3 ≤ m) (s : ℂ) :
    LSeries (fun n => gearCoeff m n) s = gear m s := by
  obtain ⟨d1, d2, d3⟩ := gearSupp m hm
  have hsupp : ∀ n ∉ ({1, 2 ^ m, 2 ^ (2 * m)} : Finset ℕ),
      LSeries.term (fun n => gearCoeff m n) s n = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    obtain ⟨h1, h2, h3⟩ := hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hpos.ne' _ s, gearCoeff_apply, if_neg h1, if_neg h2, if_neg h3]
      simp
  have hHS := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hsupp
  have hne1 : (1 : ℕ) ∉ ({2 ^ m, 2 ^ (2 * m)} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨d1, d2⟩
  have hne2 : (2 ^ m : ℕ) ∉ ({2 ^ (2 * m)} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    exact d3
  rw [show LSeries (fun n => gearCoeff m n) s
        = ∑' n, LSeries.term (fun n => gearCoeff m n) s n from rfl, hHS.tsum_eq,
    Finset.sum_insert hne1, Finset.sum_insert hne2, Finset.sum_singleton,
    LSeries.term_of_ne_zero one_ne_zero _ s,
    LSeries.term_of_ne_zero (Nat.two_pow_pos m).ne' _ s,
    LSeries.term_of_ne_zero (Nat.two_pow_pos (2 * m)).ne' _ s,
    gearCoeff_one, gearCoeff_pm m hm, gearCoeff_p2m m hm,
    show ((1 : ℕ) : ℂ) = 1 by norm_num,
    show ((2 ^ m : ℕ) : ℂ) = (2 : ℂ) ^ m by push_cast; ring,
    show ((2 ^ (2 * m) : ℕ) : ℂ) = (2 : ℂ) ^ (2 * m) by push_cast; ring,
    Complex.one_cpow, cpow_two_pow_two_mul]
  have hcm : (2 : ℂ) ^ m = 2 * (2 : ℂ) ^ (m - 1) := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
  simp only [gear, Complex.cpow_neg]
  rw [hcm]
  have hX : ((2 : ℂ) * (2 : ℂ) ^ (m - 1)) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (mul_ne_zero two_ne_zero (pow_ne_zero _ two_ne_zero)))
  field_simp
  ring

/-! ### §3 Gear products: convolution streams, functional equation, class membership -/

/-- The **gear product** over a finite level set `S`: `gearProd S s = ∏_{m ∈ S} gear m s`. -/
def gearProd (S : Finset ℕ) : ℂ → ℂ := fun s => ∏ m ∈ S, gear m s

/-- The coefficient stream of `gearProd S`: the Dirichlet convolution `∏_{m ∈ S} gearCoeff m` in
the arithmetic-function ring. -/
def gearProdCoeff (S : Finset ℕ) : ArithmeticFunction ℂ := ∏ m ∈ S, gearCoeff m

/-- **`gearProdCoeff S` is multiplicative**: Dirichlet convolution preserves multiplicativity, the
convolution unit is multiplicative, and each factor is multiplicative. -/
theorem gearProdCoeff_multiplicative (S : Finset ℕ) (hS : ∀ m ∈ S, 3 ≤ m) :
    ArithmeticFunction.IsMultiplicative (gearProdCoeff S) :=
  Finset.prod_induction (fun m => gearCoeff m) ArithmeticFunction.IsMultiplicative
    (fun _ _ ha hb => ha.mul hb) ArithmeticFunction.isMultiplicative_one
    (fun m hmS => gearCoeff_multiplicative m (hS m hmS))

/-- **`gearProdCoeff S` is integer-valued**: the convolution unit is `{0, 1}`-valued, convolution
preserves integrality, and each factor stream is integer-valued. -/
theorem gearProdCoeff_integral (S : Finset ℕ) : ∀ n, ∃ k : ℤ, gearProdCoeff S n = (k : ℂ) :=
  Finset.prod_induction (fun m => gearCoeff m)
    (fun f : ArithmeticFunction ℂ => ∀ n, ∃ k : ℤ, f n = (k : ℂ))
    (fun a b ha hb => RHTower.intCast_conv_integral a b ha hb)
    (fun n => by
      rw [ArithmeticFunction.one_apply]
      exact if h : n = 1 then ⟨1, by rw [if_pos h]; norm_num⟩
        else ⟨0, by rw [if_neg h]; norm_num⟩)
    (fun m _ => gearCoeff_integral m)

/-- The Dirichlet series of the convolution unit converges at every `s`: its support is `{1}`. -/
private theorem one_lseriesSummable (s : ℂ) :
    LSeriesSummable (fun n => (1 : ArithmeticFunction ℂ) n) s := by
  apply summable_of_ne_finset_zero (s := ({1} : Finset ℕ))
  intro n hn
  rw [Finset.mem_singleton] at hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hpos.ne' _ s, ArithmeticFunction.one_apply, if_neg hn]
    simp

/-- The Dirichlet series of `gearProdCoeff S` converges at every `s`: each factor has finite
support, and convolution preserves summability. -/
theorem gearProdCoeff_summable (S : Finset ℕ) (s : ℂ) :
    LSeriesSummable (fun n => gearProdCoeff S n) s :=
  Finset.prod_induction (fun m => gearCoeff m)
    (fun f : ArithmeticFunction ℂ => LSeriesSummable (fun n => f n) s)
    (fun _ _ ha hb => ArithmeticFunction.LSeriesSummable_mul ha hb)
    (one_lseriesSummable s) (fun m _ => gearCoeff_summable m s)

/-- **The `L`-series of `gearProdCoeff S` is `gearProd S`**, valid at every `s`: all factor streams
have finite support, so each convolution `L`-series factors termwise, and the factor identities are
`LSeries_gearCoeff`. -/
theorem LSeries_gearProdCoeff (S : Finset ℕ) (hS : ∀ m ∈ S, 3 ≤ m) (s : ℂ) :
    LSeries (fun n => gearProdCoeff S n) s = gearProd S s := by
  induction S using Finset.induction_on with
  | empty =>
      rw [show gearProdCoeff ∅ = (1 : ArithmeticFunction ℂ) from Finset.prod_empty,
        ArithmeticFunction.one_eq_delta, LSeries_delta]
      simp [gearProd]
  | insert a T haT ih =>
      have ha3 : 3 ≤ a := hS a (Finset.mem_insert_self a T)
      have hT : ∀ m ∈ T, 3 ≤ m := fun m hm => hS m (Finset.mem_insert_of_mem hm)
      rw [show gearProdCoeff (insert a T) = gearCoeff a * gearProdCoeff T from
          Finset.prod_insert haT,
        ArithmeticFunction.LSeries_mul' (gearCoeff_summable a s) (gearProdCoeff_summable T s),
        LSeries_gearCoeff a ha3 s, ih hT]
      show gear a s * ∏ m ∈ T, gear m s = ∏ m ∈ insert a T, gear m s
      exact (Finset.prod_insert (f := fun m => gear m s) haT).symm

/-- A natural product splits under `cpow`: `((a·b : ℕ) : ℂ)^z = (a : ℂ)^z·(b : ℂ)^z`, since both
bases are casts of nonnegative reals. -/
private theorem natCast_mul_cpow (a b : ℕ) (z : ℂ) :
    ((a * b : ℕ) : ℂ) ^ z = ((a : ℕ) : ℂ) ^ z * ((b : ℕ) : ℂ) ^ z := by
  rw [show ((a * b : ℕ) : ℂ) = (((a : ℝ)) : ℂ) * (((b : ℝ)) : ℂ) by push_cast; ring,
    show ((a : ℕ) : ℂ) = (((a : ℝ)) : ℂ) by push_cast; ring,
    show ((b : ℕ) : ℂ) = (((b : ℝ)) : ℂ) by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

/-- **The exact functional equation of the gear product**, with multiplied conductors:
`gearProd S s = (∏_{m ∈ S} 2^m)^{1−2s}·gearProd S (1−s)`.  Each factor satisfies its own equation
with conductor `2^m`, and the conductor `cpow` splits over the product. -/
theorem gearProd_fe (S : Finset ℕ) (hS : ∀ m ∈ S, 3 ≤ m) (s : ℂ) :
    gearProd S s = ((∏ m ∈ S, 2 ^ m : ℕ) : ℂ) ^ (1 - 2 * s) * gearProd S (1 - s) := by
  induction S using Finset.induction_on with
  | empty => simp [gearProd, Complex.one_cpow]
  | insert a T haT ih =>
      have ha3 : 3 ≤ a := hS a (Finset.mem_insert_self a T)
      have hT : ∀ m ∈ T, 3 ≤ m := fun m hm => hS m (Finset.mem_insert_of_mem hm)
      have ihT := ih hT
      simp only [gearProd] at ihT ⊢
      rw [Finset.prod_insert (f := fun m => gear m s) haT,
        Finset.prod_insert (f := fun m => gear m (1 - s)) haT,
        show ((∏ m ∈ insert a T, 2 ^ m : ℕ) : ℂ) = ((2 ^ a * ∏ m ∈ T, 2 ^ m : ℕ) : ℂ) from by
          rw [Finset.prod_insert haT],
        natCast_mul_cpow, gear_fe a ha3 s, ihT]
      ring

/-- **The gear product lies in the class.**  For a nonempty level set `S ⊆ {3, 4, …}`, witnessed by
the convolution stream `gearProdCoeff S` and conductor `Q = ∏_{m ∈ S} 2^m ≥ 2^{min S} ≥ 2`. -/
theorem gearProd_mem_class (S : Finset ℕ) (hne : S.Nonempty) (hS : ∀ m ∈ S, 3 ≤ m) :
    IntegralMultiplicativeFEClass (gearProd S) := by
  obtain ⟨a0, ha0⟩ := hne
  refine ⟨gearProdCoeff S, gearProdCoeff_multiplicative S hS, gearProdCoeff_integral S,
    fun s => (LSeries_gearProdCoeff S hS s).symm, ∏ m ∈ S, 2 ^ m, ?_, fun s => gearProd_fe S hS s⟩
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ a0 := Nat.pow_le_pow_right (by norm_num) (by have := hS a0 ha0; omega)
    _ ≤ ∏ m ∈ S, 2 ^ m := Finset.single_le_prod' (fun i _ => (Nat.two_pow_pos i)) ha0

/-! ### §4 The off-line zero of each gear at `σ = 1/m` -/

/-- **`gear m` vanishes at the real point `σ = 1/m`.**  There
`(2^m)^{−σ} = exp(−(m log 2)/m) = exp(−log 2) = 1/2`, so the first factor is
`1 − 2·(1/2) = 0`. -/
theorem gear_zero_at (m : ℕ) (hm : 3 ≤ m) : gear m ((1 / m : ℝ) : ℂ) = 0 := by
  have hm0 : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hB : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  have hlog : Complex.log ((2 : ℂ) ^ m) = (((m : ℝ) * Real.log 2 : ℝ) : ℂ) := by
    rw [show ((2 : ℂ) ^ m) = (((2 : ℝ) ^ m : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Real.log_pow]
  have hexp : ((2 : ℂ) ^ m) ^ (-((1 / m : ℝ) : ℂ)) = 1 / 2 := by
    rw [Complex.cpow_def_of_ne_zero hB, hlog]
    have harg : (((m : ℝ) * Real.log 2 : ℝ) : ℂ) * (-((1 / m : ℝ) : ℂ))
        = ((-Real.log 2 : ℝ) : ℂ) := by
      rw [show -((1 / m : ℝ) : ℂ) = ((-(1 / m) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_mul]
      congr 1
      field_simp
    rw [harg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    push_cast
    norm_num
  simp only [gear]
  rw [hexp]
  ring

/-- **The gear product vanishes at `σ = 1/m` for every level `m ∈ S`**: the level-`m` factor is
zero there. -/
theorem gearProd_zero_at (S : Finset ℕ) (hS : ∀ m ∈ S, 3 ≤ m) {m : ℕ} (hmS : m ∈ S) :
    gearProd S ((1 / m : ℝ) : ℂ) = 0 :=
  Finset.prod_eq_zero hmS (gear_zero_at m (hS m hmS))

/-! ### §5 The unbounded gear count -/

/-- **The gear count of the class is unbounded.**  For every `n` the member
`gearProd (Icc 3 (n + 3))` of `IntegralMultiplicativeFEClass` vanishes at the `n + 1` distinct real
points `{1/m : 3 ≤ m ≤ n + 3}`, all strictly inside `(0, 1/2)`: no bound on the number of off-line
vertical lines met by the zero set of a member survives integrality, multiplicativity, and the
exact functional equation. -/
theorem integralMultiplicativeFEClass_gear_count_unbounded (n : ℕ) :
    ∃ f, IntegralMultiplicativeFEClass f ∧ ∃ R : Finset ℝ,
      n ≤ R.card ∧ ∀ σ ∈ R, 0 < σ ∧ σ < 1 / 2 ∧ f ((σ : ℝ) : ℂ) = 0 := by
  set S : Finset ℕ := Finset.Icc 3 (n + 3) with hSdef
  have hS : ∀ m ∈ S, 3 ≤ m := fun m hm => (Finset.mem_Icc.mp hm).1
  have hne : S.Nonempty := ⟨3, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  refine ⟨gearProd S, gearProd_mem_class S hne hS,
    S.image (fun m : ℕ => (1 / m : ℝ)), ?_, ?_⟩
  · have hinj : Set.InjOn (fun m : ℕ => (1 / m : ℝ)) ↑S := by
      intro x _ y _ hxy
      simp only [one_div] at hxy
      exact Nat.cast_injective (inv_inj.mp hxy)
    rw [Finset.card_image_of_injOn hinj, hSdef, Nat.card_Icc]
    omega
  · intro σ hσ
    rw [Finset.mem_image] at hσ
    obtain ⟨m, hmS, rfl⟩ := hσ
    have hm3 : 3 ≤ m := hS m hmS
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
    refine ⟨one_div_pos.mpr hmpos, ?_, gearProd_zero_at S hS hmS⟩
    exact one_div_lt_one_div_of_lt (by norm_num)
      (by exact_mod_cast (by omega : 2 < m) : (2 : ℝ) < m)

end RHTower
