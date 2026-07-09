/-
# A degree-zero member of `FE ∧ multiplicativity ∧ integrality` with off-line strip zeros

An explicit witness that the three-way conjunction — an exact functional equation, full
multiplicativity, and integer coefficients — does **not** confine the divisor to the critical line.

The single-column two-factor Dirichlet polynomial
`dzo s = (1 − 2·8^{−s})(1 − 4·8^{−s})`
has coefficient function supported on `{1, 8, 64}` with values `(1, −6, 8)`: integer-valued and
multiplicative (its support is powers of the single prime `2`, so a coprime factorisation places at
most one nontrivial factor on the `2`-column).  Because the support is finite, its `L`-series equals
`dzo` at every `s`, with no half-plane restriction.

`dzo` satisfies the **exact conductor-`64` degree-zero functional equation**
`dzo s = 8^{1 − 2s}·dzo (1 − s)`:
with `w = 8^{−s}`, the reflected factors read `1 − 2/(8w) = −(1 − 4w)/(4w)` and
`1 − 4/(8w) = −(1 − 2w)/(2w)`, whose product is `dzo s / (8 w²)`, and `8^{1−2s} = 8 w²`.

Its two local roots `2·8^{−s} = 1` and `4·8^{−s} = 1` solve on the reals to `σ = log 2 / log 8 = 1/3`
and `σ = log 4 / log 8 = 2/3` (`log 8 = 3 log 2`): both are simple zeros **inside the open critical
strip and off the line** `Re s = 1/2`.  The local roots have modulus `8^{2/3} > 8^{1/2}`, so the
member violates exactly the tempered half-bound — the fourth coordinate (a depth/growth bound on the
local data, here the hypertranscendence of the member) is the load-bearing one the three-way
conjunction omits.

Read through the deck-charge trichotomy: the class carries off-line charge (a simple, hence odd, zero
at `Re s = 1/3`, base-level charge `(−1)¹ = −1 ≠ 1`), so by `forcesRHParity_iff_categorical` it cannot
force RH-grade parity.  Integrality, multiplicativity, and the functional equation together are blind
to this off-line divisor.
-/
import GaloisForLFunctions.RHTower.GoldilocksTrichotomy
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.LSeries.Basic

noncomputable section

namespace RHTower

open Complex

/-! ### §1 The two-factor single-column degree-zero polynomial and its functional equation -/

/-- The degree-zero Dirichlet polynomial `dzo s = (1 − 2·8^{−s})(1 − 4·8^{−s})`. -/
def dzo : ℂ → ℂ := fun s => (1 - 2 * (8 : ℂ) ^ (-s)) * (1 - 4 * (8 : ℂ) ^ (-s))

/-- **The exact degree-zero functional equation** `dzo s = 8^{1 − 2s}·dzo (1 − s)`.  With `w = 8^{−s}`,
one has `8^{−(1−s)} = (8 w)⁻¹` and `8^{1−2s} = 8 w²`; substituting turns the reflected product into
`dzo s / (8 w²)`, and the `8 w²` prefactor cancels it. -/
theorem dzo_fe (s : ℂ) : dzo s = (8 : ℂ) ^ (1 - 2 * s) * dzo (1 - s) := by
  have h8 : (8 : ℂ) ≠ 0 := by norm_num
  set w := (8 : ℂ) ^ (-s) with hw
  have hw0 : w ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h8)
  have h8s : (8 : ℂ) ^ s = w⁻¹ := by rw [hw, Complex.cpow_neg, inv_inv]
  have hz : (8 : ℂ) ^ (-(1 - s)) = (8 * w)⁻¹ := by
    rw [show -(1 - s) = (-1 : ℂ) + s by ring, Complex.cpow_add _ _ h8,
      show (-1 : ℂ) = -(1 : ℂ) by ring, Complex.cpow_neg, Complex.cpow_one, h8s, mul_inv]
  have hq : (8 : ℂ) ^ (1 - 2 * s) = 8 * w ^ 2 := by
    rw [show 1 - 2 * s = (1 : ℂ) + (-s + -s) by ring, Complex.cpow_add _ _ h8, Complex.cpow_one,
      Complex.cpow_add _ _ h8, hw, sq]
  simp only [dzo, hz, hq]
  field_simp
  ring

/-! ### §2 The integer multiplicative coefficient witness and its `L`-series -/

/-- A coprime factorisation of a prime power is trivial: if `a·b = 2^e` and `gcd a b = 1`, then `a` or
`b` is `1` (two nontrivial factors would both be even, contradicting coprimality). -/
private theorem coprime_mul_two_pow (a b : ℕ) (hab : Nat.Coprime a b) (e : ℕ)
    (hprod : a * b = 2 ^ e) : a = 1 ∨ b = 1 := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨ha1, hb1⟩ := hcon
  have hda : a ∣ 2 ^ e := ⟨b, hprod.symm⟩
  have hdb : b ∣ 2 ^ e := ⟨a, by rw [mul_comm]; exact hprod.symm⟩
  obtain ⟨i, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hda
  obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdb
  have hi : i ≠ 0 := fun h => ha1 (by rw [h, pow_zero])
  have hj : j ≠ 0 := fun h => hb1 (by rw [h, pow_zero])
  have h2 : 2 ∣ Nat.gcd (2 ^ i) (2 ^ j) := Nat.dvd_gcd (dvd_pow_self 2 hi) (dvd_pow_self 2 hj)
  rw [hab.gcd_eq_one] at h2
  exact absurd h2 (by decide)

/-- The integer-valued arithmetic function supported on `{1, 8, 64}` with values `1`, `−6`, `8`.  Its
`L`-series is `dzo`. -/
def dzoCoeff : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 1 then 1 else if n = 8 then -6 else if n = 64 then 8 else 0, by simp⟩

private theorem dzoCoeff_apply (n : ℕ) :
    dzoCoeff n = if n = 1 then 1 else if n = 8 then -6 else if n = 64 then 8 else 0 := rfl

/-- **`dzoCoeff` is multiplicative.**  The support `{1, 8, 64} = {2^0, 2^3, 2^6}` is a single prime
column, so a coprime factorisation of a support point carries all its `2`-mass on one factor; the
values then multiply, and any other coprime product has one vanishing factor. -/
theorem dzoCoeff_multiplicative : ArithmeticFunction.IsMultiplicative dzoCoeff := by
  constructor
  · rw [dzoCoeff_apply]; norm_num
  · intro m n hcop
    have hval : ∀ k : ℕ, dzoCoeff k ≠ 0 → k = 1 ∨ k = 8 ∨ k = 64 := by
      intro k hk
      rw [dzoCoeff_apply] at hk
      by_contra hc
      rw [not_or, not_or] at hc
      obtain ⟨h1, h8', h64'⟩ := hc
      rw [if_neg h1, if_neg h8', if_neg h64'] at hk
      exact hk rfl
    rcases eq_or_ne (m * n) 1 with h1 | h1
    · obtain ⟨hm, hn⟩ := mul_eq_one.mp h1
      subst hm; subst hn; simp [dzoCoeff_apply]
    rcases eq_or_ne (m * n) 8 with h8 | h8
    · rcases coprime_mul_two_pow m n hcop 3 (h8.trans (by norm_num)) with rfl | rfl
      · obtain rfl : n = 8 := by omega
        simp [dzoCoeff_apply]
      · obtain rfl : m = 8 := by omega
        simp [dzoCoeff_apply]
    rcases eq_or_ne (m * n) 64 with h64 | h64
    · rcases coprime_mul_two_pow m n hcop 6 (h64.trans (by norm_num)) with rfl | rfl
      · obtain rfl : n = 64 := by omega
        simp [dzoCoeff_apply]
      · obtain rfl : m = 64 := by omega
        simp [dzoCoeff_apply]
    · rw [show dzoCoeff (m * n) = 0 by rw [dzoCoeff_apply, if_neg h1, if_neg h8, if_neg h64]]
      by_cases hm : dzoCoeff m = 0
      · rw [hm]; ring
      by_cases hn : dzoCoeff n = 0
      · rw [hn]; ring
      exfalso
      rcases hval m hm with hm1 | hm8 | hm64 <;> rcases hval n hn with hn1 | hn8 | hn64 <;>
        subst_vars <;>
        first
          | omega
          | exact absurd hcop (by decide)

/-- **`dzoCoeff` is integer-valued.**  Every value is `1`, `−6`, `8`, or `0`. -/
theorem dzoCoeff_integral (n : ℕ) : ∃ k : ℤ, dzoCoeff n = (k : ℂ) := by
  rw [dzoCoeff_apply]
  rcases eq_or_ne n 1 with h1 | h1
  · exact ⟨1, by rw [if_pos h1]; norm_num⟩
  rcases eq_or_ne n 8 with h8 | h8
  · exact ⟨-6, by rw [if_neg h1, if_pos h8]; norm_num⟩
  rcases eq_or_ne n 64 with h64 | h64
  · exact ⟨8, by rw [if_neg h1, if_neg h8, if_pos h64]; norm_num⟩
  · exact ⟨0, by rw [if_neg h1, if_neg h8, if_neg h64]; norm_num⟩

/-- The single-column bridge `64^s = (8^s)²`, from `log 64 = 2 log 8`. -/
theorem cpow64_eq_sq (s : ℂ) : (64 : ℂ) ^ s = ((8 : ℂ) ^ s) ^ 2 := by
  have h8 : (8 : ℂ) ≠ 0 := by norm_num
  have h64 : (64 : ℂ) ≠ 0 := by norm_num
  have hlog8 : Complex.log 8 = ((Real.log 8 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 8)]; norm_num
  have hlog64 : Complex.log 64 = ((Real.log 64 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 64)]; norm_num
  have hr : ((Real.log 64 : ℝ) : ℂ) = 2 * ((Real.log 8 : ℝ) : ℂ) := by
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [sq, ← Complex.cpow_add _ _ h8, Complex.cpow_def_of_ne_zero h8,
    Complex.cpow_def_of_ne_zero h64, hlog8, hlog64, hr]
  congr 1; ring

/-- **The `L`-series of `dzoCoeff` is `dzo`.**  The support is `{1, 8, 64}`, so the series is the
finite sum `1 − 6·8^{−s} + 8·64^{−s}`, which is `(1 − 2·8^{−s})(1 − 4·8^{−s})` via `64^s = (8^s)²`;
valid at every `s`. -/
theorem LSeries_dzoCoeff (s : ℂ) : LSeries (fun n => dzoCoeff n) s = dzo s := by
  have hsupp : ∀ n ∉ ({1, 8, 64} : Finset ℕ), LSeries.term (fun n => dzoCoeff n) s n = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hpos.ne' _ s]
      have h1 : n ≠ 1 := by rintro rfl; exact hn (by decide)
      have h8 : n ≠ 8 := by rintro rfl; exact hn (by decide)
      have h64 : n ≠ 64 := by rintro rfl; exact hn (by decide)
      rw [dzoCoeff_apply, if_neg h1, if_neg h8, if_neg h64]; simp
  have hHS := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hsupp
  have hW0 : (8 : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  rw [show LSeries (fun n => dzoCoeff n) s
        = ∑' n, LSeries.term (fun n => dzoCoeff n) s n from rfl, hHS.tsum_eq,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    LSeries.term_of_ne_zero (by norm_num) _ s, LSeries.term_of_ne_zero (by norm_num) _ s,
    LSeries.term_of_ne_zero (by norm_num) _ s, dzoCoeff_apply, dzoCoeff_apply, dzoCoeff_apply]
  norm_num [dzo, Complex.one_cpow]
  rw [cpow64_eq_sq, Complex.cpow_neg]
  field_simp
  ring

/-! ### §3 The off-line witness point on `Re s = 1/3` and its simple zero -/

/-- The real witness point `ρdzo = 1/3`, where `8^{−ρdzo} = 8^{−1/3} = 2^{−1} = 1/2`. -/
def ρdzo : ℂ := ((1 / 3 : ℝ) : ℂ)

/-- `dzo` in exponential form: `8^{−s} = exp(−(log 8)·s)`. -/
theorem dzo_eq_exp :
    dzo = fun s => (1 - 2 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s))) *
                   (1 - 4 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s))) := by
  have hlog : Complex.log 8 = ((Real.log 8 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 8)]; norm_num
  funext s
  simp only [dzo]
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (8 : ℂ) ≠ 0), hlog, mul_neg]

/-- At `ρdzo` the exponential factor equals `1/2`: `−(log 8)·(1/3) = −log 2` (`log 8 = 3 log 2`), and
`exp(−log 2) = 1/2`. -/
theorem dzo_cexp_half : Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * ρdzo)) = 1 / 2 := by
  have hlog82 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have hkey : ((Real.log 8 : ℝ) : ℂ) * ρdzo = ((Real.log 2 : ℝ) : ℂ) := by
    simp only [ρdzo, ← Complex.ofReal_mul]
    congr 1
    rw [hlog82]; ring
  rw [hkey, show -(((Real.log 2 : ℝ) : ℂ)) = ((-Real.log 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
  push_cast; norm_num

/-- **`dzo` vanishes at `ρdzo`.**  The first factor is `1 − 2·(1/2) = 0`. -/
theorem dzo_ρdzo_eq_zero : dzo ρdzo = 0 := by
  rw [dzo_eq_exp]
  show (1 - 2 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * ρdzo))) *
       (1 - 4 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * ρdzo))) = 0
  rw [dzo_cexp_half]; ring

/-- **The zero is simple.**  `dzo` is entire; at `ρdzo` the first factor vanishes with derivative
`log 8 ≠ 0` while the second factor is `1 − 4·(1/2) = −1 ≠ 0`, so the product has analytic order `1`
(its derivative there is `log 8·(−1) = −log 8 ≠ 0`). -/
theorem dzo_order_one : analyticOrderAt dzo ρdzo = 1 := by
  rw [dzo_eq_exp]
  have hLcne : ((Real.log 8 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  have han : AnalyticAt ℂ (fun s => (1 - 2 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s))) *
      (1 - 4 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s)))) ρdzo := by
    have hdiff : Differentiable ℂ (fun s => (1 - 2 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s))) *
        (1 - 4 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s)))) :=
      Differentiable.mul
        (((((differentiable_id.const_mul ((Real.log 8 : ℝ) : ℂ)).neg).cexp).const_mul 2).const_sub 1)
        (((((differentiable_id.const_mul ((Real.log 8 : ℝ) : ℂ)).neg).cexp).const_mul 4).const_sub 1)
    exact (hdiff.differentiableOn.analyticOnNhd isOpen_univ) ρdzo (Set.mem_univ ρdzo)
  have hzero : (fun s => (1 - 2 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s))) *
      (1 - 4 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s)))) ρdzo = 0 := by
    show (1 - 2 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * ρdzo))) *
         (1 - 4 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * ρdzo))) = 0
    rw [dzo_cexp_half]; ring
  have h1 : HasDerivAt (fun s : ℂ => -(((Real.log 8 : ℝ) : ℂ) * s)) (-((Real.log 8 : ℝ) : ℂ)) ρdzo := by
    simpa using ((hasDerivAt_id ρdzo).const_mul ((Real.log 8 : ℝ) : ℂ)).neg
  have hd : HasDerivAt (fun s => (1 - 2 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s))) *
      (1 - 4 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s))))
      ((-(2 * (Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * ρdzo)) * (-((Real.log 8 : ℝ) : ℂ))))) *
         (1 - 4 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * ρdzo))) +
       (1 - 2 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * ρdzo))) *
         (-(4 * (Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * ρdzo)) * (-((Real.log 8 : ℝ) : ℂ)))))) ρdzo :=
    (((h1.cexp).const_mul 2).const_sub 1).mul (((h1.cexp).const_mul 4).const_sub 1)
  have hderiv : deriv (fun s => (1 - 2 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s))) *
      (1 - 4 * Complex.exp (-(((Real.log 8 : ℝ) : ℂ) * s)))) ρdzo = -((Real.log 8 : ℝ) : ℂ) := by
    rw [hd.deriv, dzo_cexp_half]; ring
  refine han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero ?_
  rw [hderiv]; exact neg_ne_zero.mpr hLcne

/-- `Re ρdzo = 1/3`. -/
theorem ρdzo_re : ρdzo.re = 1 / 3 := by simp [ρdzo]

/-- `Re ρdzo = 1/3 ≠ 1/2`: the witness is off the critical line. -/
theorem ρdzo_re_ne_half : ρdzo.re ≠ 1 / 2 := by rw [ρdzo_re]; norm_num

/-- `0 < Re ρdzo`: inside the strip on the right of `0`. -/
theorem ρdzo_re_pos : 0 < ρdzo.re := by rw [ρdzo_re]; norm_num

/-- `Re ρdzo < 1`: inside the strip on the left of `1`. -/
theorem ρdzo_re_lt_one : ρdzo.re < 1 := by rw [ρdzo_re]; norm_num

/-! ### §4 The class carries off-line charge, hence no RH-grade parity -/

/-- The **integral multiplicative functional-equation** class: carriers that are the `L`-series of an
integer-valued multiplicative arithmetic function and satisfy an exact conductor-`Q` degree-zero
functional equation `f s = Q^{1 − 2s}·f (1 − s)` for some `Q ≥ 2`. -/
def IntegralMultiplicativeFEClass (f : ℂ → ℂ) : Prop :=
  ∃ a : ArithmeticFunction ℂ, ArithmeticFunction.IsMultiplicative a ∧
    (∀ n, ∃ k : ℤ, a n = (k : ℂ)) ∧ (∀ s, f s = LSeries (fun n => a n) s) ∧
    (∃ Q : ℕ, 2 ≤ Q ∧ ∀ s, f s = (Q : ℂ) ^ (1 - 2 * s) * f (1 - s))

/-- **`dzo` lies in the class**, witnessed by `dzoCoeff` with conductor `Q = 8`. -/
theorem dzo_mem_class : IntegralMultiplicativeFEClass dzo :=
  ⟨dzoCoeff, dzoCoeff_multiplicative, dzoCoeff_integral, fun s => (LSeries_dzoCoeff s).symm,
    8, by norm_num, fun s => by rw [show ((8 : ℕ) : ℂ) = (8 : ℂ) from by norm_num]; exact dzo_fe s⟩

/-- **The class carries nontrivial charge at `ρdzo`.**  `dzo` is in the class and has a simple (odd)
zero there, so its base-level deck charge is `(−1)¹ = −1 ≠ 1`. -/
theorem carriesChargeAt_dzo : CarriesChargeAt IntegralMultiplicativeFEClass ρdzo := by
  refine ⟨dzo, dzo_mem_class, ?_⟩
  rw [carrierCharge_one_eq_neg_one_pow, dzo_order_one, ENat.toNat_one]; norm_num

/-- **The class carries off-line charge.**  The witness `ρdzo` has `Re ρdzo = 1/3 ≠ 1/2`, strictly
inside the open critical strip. -/
theorem integralMultiplicativeFEClass_carriesOffLineCharge :
    CarriesOffLineCharge IntegralMultiplicativeFEClass :=
  ⟨ρdzo, ρdzo_re_ne_half, carriesChargeAt_dzo⟩

/-- **The three-way conjunction cannot force RH-grade parity.**  Parity-forcing by charge is exactly
the charge-free (categorical) cell (`forcesRHParity_iff_categorical`); this class carries off-line
charge, so it is not categorical.  Integrality, multiplicativity, and an exact degree-zero functional
equation together are blind to the off-line divisor of `dzo`. -/
theorem integralMultiplicativeFEClass_not_forcesRHParity :
    ¬ ForcesRHParity IntegralMultiplicativeFEClass := by
  rw [forcesRHParity_iff_categorical]
  exact fun hcat => hcat integralMultiplicativeFEClass_carriesOffLineCharge

end RHTower
