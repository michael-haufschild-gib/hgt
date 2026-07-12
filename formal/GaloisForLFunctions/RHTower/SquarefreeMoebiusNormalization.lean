import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Infinite squarefree Möbius normalization

The squarefree indicator `μ²` is normalized by the Riemann zeta function through the
infinite identity `∑ μ(n)²/n^s = ζ(s)/ζ(2s)`.  This file builds the three faces of that
normalization from a single new primitive, the square dilation of an arithmetic function.

* `RHTower.sqrtPart` — the square dilation: `sqrtPart f (k²) = f k`, vanishing off squares.
  Dilation preserves multiplicativity (`RHTower.isMultiplicative_sqrtPart`), because coprime
  factors of a square are squares.
* `RHTower.sqrtPart_moebius_mul_zeta` — the arithmetic form `sqrtPart μ ⍟ ζ = μ·μ`,
  equivalently `μ(n)² = ∑_{d² ∣ n} μ(d)` (`RHTower.sum_divisors_sqrtPart_moebius`).
* `RHTower.LSeries_sqrtPart` — the analytic dilation law `L(sqrtPart f, s) = L(f, 2s)`,
  with summability transfer `RHTower.LSeriesSummable_sqrtPart_iff`.  In particular the
  dilated Möbius series converges on `re s > 1/2` and represents `ζ(2s)⁻¹` there
  (`RHTower.LSeries_sqrtPart_moebius`).
* `RHTower.LSeries_squarefree_eq_riemannZeta_div` — the L-series form
  `L(μ·μ, s) = ζ(s)/ζ(2s)` on `re s > 1`, with the explicit series
  `RHTower.tsum_squarefree_cpow : ∑' n, [Squarefree n]/n^s = ζ(s)/ζ(2s)` and the product
  form `RHTower.LSeries_squarefree_mul_riemannZeta_two_mul`.
* `RHTower.squarefree_eulerProduct_tprod` — the Euler-product face
  `∏' p, (1 + p^(-s)) = ζ(s)/ζ(2s)` on `re s > 1`.
* `RHTower.LSeries_moebius_eq_inv_riemannZeta` — the companion Möbius normalization
  `L(μ, s) = ζ(s)⁻¹` on `re s > 1`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction LSeries Complex
open scoped LSeries.notation Moebius ArithmeticFunction.zeta

/-! ## The square dilation of an arithmetic function -/

/-- The square dilation of an arithmetic function: `sqrtPart f` takes the value `f k` at
`n = k²` and vanishes off squares.  On Dirichlet series this doubles the variable:
`L(sqrtPart f, s) = L(f, 2s)`. -/
def sqrtPart {R : Type*} [Zero R] (f : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => if n.sqrt * n.sqrt = n then f n.sqrt else 0, by simp⟩

theorem sqrtPart_apply {R : Type*} [Zero R] (f : ArithmeticFunction R) (n : ℕ) :
    sqrtPart f n = if n.sqrt * n.sqrt = n then f n.sqrt else 0 := rfl

@[simp] theorem sqrtPart_apply_sq {R : Type*} [Zero R] (f : ArithmeticFunction R) (k : ℕ) :
    sqrtPart f (k ^ 2) = f k := by
  rw [sqrtPart_apply, Nat.sqrt_eq', if_pos (by rw [← pow_two])]

@[simp] theorem sqrtPart_apply_mul_self {R : Type*} [Zero R] (f : ArithmeticFunction R)
    (k : ℕ) : sqrtPart f (k * k) = f k := by
  rw [sqrtPart_apply, Nat.sqrt_eq, if_pos rfl]

theorem sqrtPart_apply_of_not_isSquare {R : Type*} [Zero R] (f : ArithmeticFunction R)
    {n : ℕ} (h : ¬ IsSquare n) : sqrtPart f n = 0 := by
  rw [sqrtPart_apply, if_neg]
  exact fun hc => h ⟨n.sqrt, hc.symm⟩

/-- Coprime factors of a square are squares. -/
theorem isSquare_and_isSquare_of_coprime_of_isSquare_mul {m n : ℕ}
    (hmn : Nat.Coprime m n) (h : IsSquare (m * n)) : IsSquare m ∧ IsSquare n := by
  obtain ⟨c, hc⟩ := h
  have hc2 : m * n = c ^ 2 := by rw [hc, pow_two]
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hmn) hc2
  obtain ⟨e, he⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hmn.symm)
    (mul_comm m n ▸ hc2)
  exact ⟨⟨d, by rw [hd, pow_two]⟩, ⟨e, by rw [he, pow_two]⟩⟩

/-- The square dilation preserves multiplicativity. -/
theorem isMultiplicative_sqrtPart {R : Type*} [CommMonoidWithZero R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) :
    (sqrtPart f).IsMultiplicative := by
  refine ⟨?_, fun {m n} hmn => ?_⟩
  · rw [show (1 : ℕ) = 1 * 1 from rfl, sqrtPart_apply_mul_self]
    exact hf.map_one
  · by_cases hm : IsSquare m
    · by_cases hn : IsSquare n
      · obtain ⟨a, rfl⟩ := hm
        obtain ⟨b, rfl⟩ := hn
        have hab : Nat.Coprime a b :=
          (hmn.coprime_dvd_left (dvd_mul_right a a)).coprime_dvd_right (dvd_mul_right b b)
        rw [show a * a * (b * b) = a * b * (a * b) by ring, sqrtPart_apply_mul_self,
          sqrtPart_apply_mul_self, sqrtPart_apply_mul_self]
        exact hf.map_mul_of_coprime hab
      · rw [sqrtPart_apply_of_not_isSquare f hn, mul_zero,
          sqrtPart_apply_of_not_isSquare f]
        exact fun hsq =>
          hn (isSquare_and_isSquare_of_coprime_of_isSquare_mul hmn hsq).2
    · rw [sqrtPart_apply_of_not_isSquare f hm, zero_mul,
        sqrtPart_apply_of_not_isSquare f]
      exact fun hsq =>
        hm (isSquare_and_isSquare_of_coprime_of_isSquare_mul hmn hsq).1

/-- The square dilation commutes with coefficient casting from `ℤ`. -/
theorem sqrtPart_intCoe {R : Type*} [AddGroupWithOne R] (f : ArithmeticFunction ℤ) :
    ((sqrtPart f : ArithmeticFunction ℤ) : ArithmeticFunction R) = sqrtPart (f : ArithmeticFunction R) := by
  ext n
  simp only [intCoe_apply, sqrtPart_apply, apply_ite (Int.cast : ℤ → R), Int.cast_zero]

/-- Casting an `ℕ`-valued arithmetic function to `ℂ` through `ℤ` is direct casting. -/
theorem intCoe_natCoe (f : ArithmeticFunction ℕ) :
    (((f : ArithmeticFunction ℤ) : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) = (f : ArithmeticFunction ℂ) := by
  ext n
  simp [natCoe_apply]

/-! ## The arithmetic normalization law: `sqrtPart μ ⍟ ζ = μ·μ` -/

/-- An odd power of a prime is not a square. -/
theorem not_isSquare_prime_pow_odd {p j : ℕ} (hp : p.Prime) (hj : Odd j) :
    ¬ IsSquare (p ^ j) := by
  rintro ⟨c, hc⟩
  have hdvd : c ∣ p ^ j := Dvd.intro c hc.symm
  obtain ⟨t, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  rw [← pow_add] at hc
  have hj' := Nat.pow_right_injective hp.two_le hc
  obtain ⟨u, hu⟩ := hj
  omega

/-- The square-dilated Möbius function at prime powers: `1` at `p⁰`, `-1` at `p²`,
`0` elsewhere. -/
theorem sqrtPart_moebius_apply_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    sqrtPart (μ : ArithmeticFunction ℤ) (p ^ j) =
      if j = 0 then 1 else if j = 2 then -1 else 0 := by
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨u, rfl⟩ := he
    rw [show p ^ (u + u) = (p ^ u) ^ 2 by rw [← pow_mul, mul_two], sqrtPart_apply_sq]
    match u with
    | 0 => simp
    | 1 => rw [pow_one, moebius_apply_prime hp]; norm_num
    | (v + 2) =>
      rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
  · rw [sqrtPart_apply_of_not_isSquare _ (not_isSquare_prime_pow_odd hp ho)]
    obtain ⟨u, hu⟩ := ho
    rw [if_neg (by omega), if_neg (by omega)]

/-- **Infinite squarefree Möbius normalization, arithmetic form.**
The Dirichlet convolution of the square-dilated Möbius function with `ζ` is the
pointwise square of the Möbius function, i.e. the squarefree indicator:
`∑_{d² ∣ n} μ(d) = μ(n)²`. -/
theorem sqrtPart_moebius_mul_zeta :
    sqrtPart (μ : ArithmeticFunction ℤ) * (ζ : ArithmeticFunction ℤ) =
      pmul (μ : ArithmeticFunction ℤ) μ := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((isMultiplicative_sqrtPart isMultiplicative_moebius).mul isMultiplicative_zeta.natCast)
    _ (isMultiplicative_moebius.pmul isMultiplicative_moebius)).mpr fun p i hp => ?_
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, pmul_apply]
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · simp [sqrtPart_moebius_apply_prime_pow hp]
    · rw [Finset.sum_range_succ, Finset.sum_range_one,
        sqrtPart_moebius_apply_prime_pow hp 0, sqrtPart_moebius_apply_prime_pow hp 1,
        pow_one, moebius_apply_prime hp]
      norm_num
  · have hsum : ∑ j ∈ Finset.range (i + 1), sqrtPart (μ : ArithmeticFunction ℤ) (p ^ j)
        = ∑ j ∈ ({0, 2} : Finset ℕ), sqrtPart (μ : ArithmeticFunction ℤ) (p ^ j) := by
      symm
      refine Finset.sum_subset ?_ fun x _ hx => ?_
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_range]
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        rw [sqrtPart_moebius_apply_prime_pow hp x, if_neg hx.1, if_neg hx.2]
    rw [hsum, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 2),
      sqrtPart_moebius_apply_prime_pow hp 0, sqrtPart_moebius_apply_prime_pow hp 2,
      moebius_apply_prime_pow hp (by omega : i ≠ 0)]
    have hne : i ≠ 1 := by omega
    simp [hne]

/-- The classical divisor-sum face of the normalization law:
`∑_{d ∣ n} (sqrtPart μ)(d) = μ(n)²`, the sum extending only over square divisors. -/
theorem sum_divisors_sqrtPart_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, sqrtPart (μ : ArithmeticFunction ℤ) d = μ n * μ n := by
  have h : (sqrtPart (μ : ArithmeticFunction ℤ) * (ζ : ArithmeticFunction ℤ)) n =
      pmul (μ : ArithmeticFunction ℤ) μ n := by rw [sqrtPart_moebius_mul_zeta]
  rwa [coe_mul_zeta_apply, pmul_apply] at h

/-! ## The analytic dilation law: `L(sqrtPart f, s) = L(f, 2s)` -/

/-- Casting a squared natural into `ℂ` and raising to `s` is raising the base to `2s`. -/
theorem natCast_sq_cpow (k : ℕ) (s : ℂ) :
    ((k ^ 2 : ℕ) : ℂ) ^ s = ((k : ℕ) : ℂ) ^ (2 * s) := by
  have h2 : ((2 : ℕ) : ℂ) = (2 : ℂ) := by norm_num
  rw [← h2, Complex.cpow_nat_mul]
  push_cast
  rw [sq, show ((k : ℂ)) = ((k : ℝ) : ℂ) by push_cast; rfl,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg k), sq]

theorem term_sqrtPart_sq (f : ArithmeticFunction ℂ) (s : ℂ) (k : ℕ) :
    term (⇑(sqrtPart f)) s (k ^ 2) = term (⇑f) (2 * s) k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [term_of_ne_zero (pow_ne_zero 2 hk), term_of_ne_zero hk, sqrtPart_apply_sq,
      natCast_sq_cpow]

theorem term_sqrtPart_eq_zero_of_not_isSquare (f : ArithmeticFunction ℂ) (s : ℂ)
    {n : ℕ} (h : ¬ IsSquare n) : term (⇑(sqrtPart f)) s n = 0 := by
  have hn : n ≠ 0 := by rintro rfl; exact h ⟨0, rfl⟩
  rw [term_of_ne_zero hn, sqrtPart_apply_of_not_isSquare f h, zero_div]

private theorem term_sqrtPart_vanish (f : ArithmeticFunction ℂ) (s : ℂ) :
    ∀ x ∉ Set.range (fun k : ℕ => k ^ 2), term (⇑(sqrtPart f)) s x = 0 := by
  intro x hx
  refine term_sqrtPart_eq_zero_of_not_isSquare f s fun hsq => hx ?_
  obtain ⟨r, rfl⟩ := hsq
  exact ⟨r, pow_two r⟩

private theorem sq_injective : Function.Injective (fun k : ℕ => k ^ 2) :=
  Nat.pow_left_injective (by norm_num)

/-- Summability transfer for the square dilation: `L(sqrtPart f)` converges at `s`
exactly when `L f` converges at `2s`. -/
theorem LSeriesSummable_sqrtPart_iff (f : ArithmeticFunction ℂ) (s : ℂ) :
    LSeriesSummable (⇑(sqrtPart f)) s ↔ LSeriesSummable (⇑f) (2 * s) := by
  have hterm : (term (⇑(sqrtPart f)) s) ∘ (fun k : ℕ => k ^ 2) = term (⇑f) (2 * s) :=
    funext fun k => term_sqrtPart_sq f s k
  unfold LSeriesSummable
  rw [← sq_injective.summable_iff (term_sqrtPart_vanish f s), hterm]

/-- **The analytic dilation law.**  The L-series of the square dilation is the original
L-series at the doubled variable: `L(sqrtPart f, s) = L(f, 2s)`. -/
theorem LSeries_sqrtPart (f : ArithmeticFunction ℂ) (s : ℂ) :
    LSeries (⇑(sqrtPart f)) s = LSeries (⇑f) (2 * s) := by
  unfold LSeries
  rw [← sq_injective.tsum_eq
    (Function.support_subset_iff'.mpr (term_sqrtPart_vanish f s))]
  exact tsum_congr fun k => term_sqrtPart_sq f s k

/-! ## Möbius normalization on the half-planes `re s > 1` and `re s > 1/2` -/

/-- The Möbius L-series is the reciprocal of the Riemann zeta function on `re s > 1`. -/
theorem LSeries_moebius_eq_inv_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    L ↗μ s = (riemannZeta s)⁻¹ := by
  have h := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs] at h
  exact eq_inv_of_mul_eq_one_left (mul_comm (L ↗μ s) (riemannZeta s) ▸ h)

private theorem two_mul_re (s : ℂ) : (2 * s).re = 2 * s.re := by
  simp [Complex.mul_re]

private theorem coe_sqrtPart_moebius_intCoe :
    ⇑(sqrtPart ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) =
      ↗(sqrtPart (μ : ArithmeticFunction ℤ)) := by
  rw [← sqrtPart_intCoe]
  funext n
  simp [intCoe_apply]

/-- The square-dilated Möbius series converges on the half-plane `re s > 1/2`. -/
theorem LSeriesSummable_sqrtPart_moebius {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeriesSummable ↗(sqrtPart (μ : ArithmeticFunction ℤ)) s := by
  rw [← coe_sqrtPart_moebius_intCoe]
  rw [LSeriesSummable_sqrtPart_iff]
  have h2 : 1 < (2 * s).re := by rw [two_mul_re]; linarith
  have : ⇑((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) = ↗μ := by
    funext n; simp [intCoe_apply]
  rw [this]
  exact LSeriesSummable_moebius_iff.mpr h2

/-- On `re s > 1/2` the square-dilated Möbius series represents `ζ(2s)⁻¹`. -/
theorem LSeries_sqrtPart_moebius {s : ℂ} (hs : 1 / 2 < s.re) :
    L ↗(sqrtPart (μ : ArithmeticFunction ℤ)) s = (riemannZeta (2 * s))⁻¹ := by
  have h2 : 1 < (2 * s).re := by rw [two_mul_re]; linarith
  have hmu : ⇑((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) = ↗μ := by
    funext n; simp [intCoe_apply]
  rw [← coe_sqrtPart_moebius_intCoe, LSeries_sqrtPart, hmu,
    LSeries_moebius_eq_inv_riemannZeta h2]

private theorem pmul_moebius_intCoe :
    ((pmul (μ : ArithmeticFunction ℤ) μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) =
      sqrtPart ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) *
        (ζ : ArithmeticFunction ℂ) := by
  rw [← sqrtPart_moebius_mul_zeta, intCoe_mul, sqrtPart_intCoe, intCoe_natCoe]

/-- **Infinite squarefree Möbius normalization, product form.**
`L(μ·μ, s) · ζ(2s) = ζ(s)` on `re s > 1`. -/
theorem LSeries_squarefree_mul_riemannZeta_two_mul {s : ℂ} (hs : 1 < s.re) :
    L ↗(pmul (μ : ArithmeticFunction ℤ) μ) s * riemannZeta (2 * s) = riemannZeta s := by
  have h2 : 1 < (2 * s).re := by rw [two_mul_re]; linarith
  have hzsum : LSeriesSummable ⇑((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) s := by
    have : ⇑((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) = ↗ζ := by
      funext n; simp [natCoe_apply]
    rw [this]
    exact LSeriesSummable_zeta_iff.mpr hs
  have hmusum : LSeriesSummable
      ⇑(sqrtPart ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) s := by
    rw [coe_sqrtPart_moebius_intCoe]
    exact LSeriesSummable_sqrtPart_moebius (by linarith)
  have hfun : ↗(pmul (μ : ArithmeticFunction ℤ) μ) =
      ⇑((pmul (μ : ArithmeticFunction ℤ) μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
    funext n; simp [intCoe_apply]
  have hz : L ⇑((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) s = riemannZeta s := by
    have : ⇑((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) = ↗ζ := by
      funext n; simp [natCoe_apply]
    rw [this]
    exact LSeries_zeta_eq_riemannZeta hs
  rw [hfun, pmul_moebius_intCoe, LSeries_mul' hmusum hzsum, hz,
    coe_sqrtPart_moebius_intCoe, LSeries_sqrtPart_moebius (by linarith)]
  field_simp [riemannZeta_ne_zero_of_one_lt_re h2]

/-- **Infinite squarefree Möbius normalization, quotient form.**
`L(μ·μ, s) = ζ(s)/ζ(2s)` on `re s > 1`. -/
theorem LSeries_squarefree_eq_riemannZeta_div {s : ℂ} (hs : 1 < s.re) :
    L ↗(pmul (μ : ArithmeticFunction ℤ) μ) s = riemannZeta s / riemannZeta (2 * s) := by
  have h2 : 1 < (2 * s).re := by rw [two_mul_re]; linarith
  rw [eq_div_iff (riemannZeta_ne_zero_of_one_lt_re h2)]
  exact LSeries_squarefree_mul_riemannZeta_two_mul hs

/-- **Infinite squarefree Möbius normalization, explicit series form.**
`∑' n, [Squarefree n] / n^s = ζ(s)/ζ(2s)` on `re s > 1`. -/
theorem tsum_squarefree_cpow {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (if Squarefree n then 1 / (n : ℂ) ^ s else 0) =
      riemannZeta s / riemannZeta (2 * s) := by
  rw [← LSeries_squarefree_eq_riemannZeta_div hs]
  unfold LSeries
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [not_squarefree_zero]
  · rw [term_of_ne_zero hn]
    simp only [pmul_apply, ← pow_two, moebius_sq]
    split_ifs with h
    · push_cast
      rw [one_div]
    · push_cast
      rw [zero_div]

/-! ## The Euler-product face: `∏' p, (1 + p^(-s)) = ζ(s)/ζ(2s)` -/

/-- The squarefree `cpow` kernel `n ↦ [Squarefree n]·n^(-s)`, packaged as an arithmetic
function so that the general Euler-product machinery applies. -/
def squarefreeCpow (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if Squarefree n then (n : ℂ) ^ (-s) else 0, by simp [not_squarefree_zero]⟩

theorem squarefreeCpow_apply (s : ℂ) (n : ℕ) :
    squarefreeCpow s n = if Squarefree n then (n : ℂ) ^ (-s) else 0 := rfl

/-- Casting a product of naturals into `ℂ` distributes over `cpow`. -/
theorem natCast_mul_cpow (m n : ℕ) (r : ℂ) :
    ((m * n : ℕ) : ℂ) ^ r = ((m : ℕ) : ℂ) ^ r * ((n : ℕ) : ℂ) ^ r := by
  push_cast
  rw [show ((m : ℂ)) = ((m : ℝ) : ℂ) by push_cast; rfl,
    show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

theorem isMultiplicative_squarefreeCpow (s : ℂ) :
    (squarefreeCpow s).IsMultiplicative := by
  refine ⟨?_, fun {m n} hmn => ?_⟩
  · simp [squarefreeCpow_apply]
  · rw [squarefreeCpow_apply, squarefreeCpow_apply, squarefreeCpow_apply]
    by_cases hm : Squarefree m
    · by_cases hn : Squarefree n
      · rw [if_pos hm, if_pos hn, if_pos ((Nat.squarefree_mul hmn).mpr ⟨hm, hn⟩),
          natCast_mul_cpow]
      · rw [if_neg hn, mul_zero, if_neg]
        exact fun hsq => hn hsq.of_mul_right
    · rw [if_neg hm, zero_mul, if_neg]
      exact fun hsq => hm hsq.of_mul_left

theorem summable_norm_squarefreeCpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun n => ‖squarefreeCpow s n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (Real.summable_one_div_nat_rpow.mpr hs)
  rcases eq_or_ne n 0 with rfl | hn
  · rw [ArithmeticFunction.map_zero, norm_zero, Nat.cast_zero,
      Real.zero_rpow (by linarith : (0 : ℝ) < s.re).ne']
    norm_num
  · rw [squarefreeCpow_apply]
    split_ifs with h
    · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), neg_re,
        Real.rpow_neg (Nat.cast_nonneg n), one_div]
    · rw [norm_zero]
      positivity

/-- The local Euler factor of the squarefree kernel at a prime is `1 + p^(-s)`. -/
theorem tsum_squarefreeCpow_prime_pow {s : ℂ} (p : Nat.Primes) :
    ∑' e : ℕ, squarefreeCpow s ((p : ℕ) ^ e) = 1 + (p : ℕ) ^ (-s) := by
  have hp : (p : ℕ).Prime := p.prop
  rw [tsum_eq_sum (s := ({0, 1} : Finset ℕ)) ?_]
  · rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    rw [pow_zero, pow_one, squarefreeCpow_apply, squarefreeCpow_apply,
      if_pos squarefree_one, if_pos hp.squarefree]
    norm_num
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    rw [squarefreeCpow_apply, if_neg]
    intro hsq
    have hdvd : (p : ℕ) * (p : ℕ) ∣ (p : ℕ) ^ e := by
      rw [← pow_two]
      exact pow_dvd_pow _ (by omega)
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq (p : ℕ) hdvd))

/-- **Infinite squarefree Möbius normalization, Euler-product form.**
`∏' p, (1 + p^(-s)) = ζ(s)/ζ(2s)` on `re s > 1`. -/
theorem squarefree_eulerProduct_tprod {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s)) = riemannZeta s / riemannZeta (2 * s) := by
  have h := (isMultiplicative_squarefreeCpow s).eulerProduct_tprod
    (summable_norm_squarefreeCpow hs)
  rw [tprod_congr (fun p => tsum_squarefreeCpow_prime_pow p)] at h
  rw [h, ← tsum_squarefree_cpow hs]
  refine tsum_congr fun n => ?_
  rw [squarefreeCpow_apply]
  split_ifs with hsq
  · rw [Complex.cpow_neg, one_div]
  · rfl
