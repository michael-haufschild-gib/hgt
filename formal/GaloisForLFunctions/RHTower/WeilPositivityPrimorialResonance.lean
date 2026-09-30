import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# Weil positivity excludes weights bounded below on the squarefree integers

For weights `lam : ℕ → ℝ` that are Weil-positive (with the archimedean term of `ζ`), the
multiplicative Toeplitz bound applied to the divisor resonator `c(m) = 1_{m ∣ N}` gives the
**divisor resonance law** (`weil_divisor_resonance_bound`): for an absolute `C₀` and every `N ≥ 1`,
`2 ∑_{n ∣ N, n ≥ 2} lam(n) n^{-1/2} d(N/n) ≤ (log N + C₀) d(N)`, with `d` the divisor function.

At a primorial `N = y#` the left side is a Dirichlet convolution of multiplicative functions.  If
`lam(n) ≥ c n^{-δ}` on the squarefree integers, it is at least `c (M(y#) - d(y#))` with
`M(y#) = ∏_{p ≤ y} (2 + p^{-1/2-δ})` and `d(y#) = 2^{π(y)}`, so
`2c (∏_{p ≤ y} (1 + p^{-1/2-δ}/2) - 1) ≤ log(y#) + C₀ ≤ y log 4 + C₀`
(`primorial_resonance_inequality`).  The product is at least `exp((1/4) ∑_{p ≤ y} p^{-1/2-δ})`, and
Chebyshev's lower bound for `θ(y)` makes the exponent grow like `y^{1/2-δ}/log y`.

**Theorem** (`not_forall_squarefree_le_of_weilPositiveFull`).  For every `c > 0` and `δ < 1/2`, no
full-cone Weil-positive weight system satisfies `lam(n) ≥ c n^{-δ}` for all squarefree `n ≥ 2`.

The same holds after a multiplicative sign twist: with `χ_s(n) = ∏_{p ∣ n} s(p)`, `s(p) = ±1`, the
resonator `χ_s(m) 1_{m ∣ y#}` excludes `χ_s(n) lam(n) ≥ c n^{-δ}` on the squarefree integers
(`not_forall_squarefree_signChar_le_of_weilPositiveFull`); `s ≡ -1` is the Möbius-signed case
(`not_forall_squarefree_moebius_le_of_weilPositiveFull`).
-/

open Complex Finset Filter
open ComplexConjugate

namespace RHTower
namespace PrimorialResonance

/-- The divisor resonator `c(m) = 1_{m ∣ N}`. -/
noncomputable def divisorResonator (N m : ℕ) : ℂ := if m ∣ N then 1 else 0

theorem mem_Icc_of_dvd {N m : ℕ} (hN : 1 ≤ N) (hm : m ∣ N) : m ∈ Icc 1 N := by
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm (by omega)
  exact mem_Icc.mpr ⟨hm0, Nat.le_of_dvd (by omega) hm⟩

theorem sum_Icc_ite_dvd {N : ℕ} (hN : 1 ≤ N) (f : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, (if m ∣ N then f m else 0) = ∑ m ∈ N.divisors, f m := by
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨-, h⟩; exact ⟨h, by omega⟩
  · rintro ⟨h, -⟩; exact ⟨mem_Icc_of_dvd hN h, h⟩

theorem sum_norm_sq_divisorResonator {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Icc 1 N, ‖divisorResonator N m‖ ^ 2 = (N.divisors.card : ℝ) := by
  have h : ∀ m, ‖divisorResonator N m‖ ^ 2 = if m ∣ N then (1 : ℝ) else 0 := fun m => by
    unfold divisorResonator; split_ifs <;> simp
  simp_rw [h]
  rw [sum_Icc_ite_dvd hN, sum_const, nsmul_eq_mul, mul_one]

theorem divisorResonator_mul_conj (N n m : ℕ) :
    divisorResonator N (n * m) * conj (divisorResonator N m) =
      ((if n * m ∣ N then (1 : ℝ) else 0 : ℝ) : ℂ) := by
  unfold divisorResonator
  by_cases h1 : n * m ∣ N
  · have h2 : m ∣ N := (Dvd.intro_left n rfl).trans h1
    simp [h1, h2]
  · simp [h1]

theorem sum_divisorResonator_mul {N n : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Icc 1 N, divisorResonator N (n * m) * conj (divisorResonator N m) =
      ((if n ∣ N then ((N / n).divisors.card : ℝ) else 0 : ℝ) : ℂ) := by
  simp_rw [divisorResonator_mul_conj]
  rw [← Complex.ofReal_sum]
  congr 1
  by_cases hn : n ∣ N
  · rw [if_pos hn]
    have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hn (by omega)
    have hq : 1 ≤ N / n := Nat.div_pos (Nat.le_of_dvd (by omega) hn) hn0
    have key : ∀ m, (n * m ∣ N ↔ m ∣ N / n) := fun m => by
      rw [Nat.dvd_div_iff_mul_dvd hn, mul_comm]
    have hsub : ∀ m, m ∣ N / n → m ∈ Icc 1 N := fun m hm =>
      mem_Icc_of_dvd hN (hm.trans (Nat.div_dvd_of_dvd hn))
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    congr 1
    congr 1
    ext m
    simp only [mem_filter, Nat.mem_divisors, key]
    constructor
    · rintro ⟨-, h⟩; exact ⟨h, by omega⟩
    · rintro ⟨h, -⟩; exact ⟨hsub m h, h⟩
  · rw [if_neg hn]
    refine sum_eq_zero fun m _ => ?_
    rw [if_neg]
    intro h
    exact hn ((Dvd.intro m rfl).trans h)

/-- **Divisor resonance law.**  For Weil-positive weights there is an absolute `C₀` with
`2 ∑_{n ∣ N, n ≥ 2} lam(n) n^{-1/2} d(N/n) ≤ (log N + C₀) d(N)` for every `N ≥ 1`, where `d` counts
divisors: the multiplicative Toeplitz bound for the resonator `1_{m ∣ N}`. -/
theorem weil_divisor_resonance_bound {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    ∃ C₀ : ℝ, ∀ N : ℕ, 1 ≤ N →
      2 * ∑ n ∈ N.divisors with 2 ≤ n, lam n / Real.sqrt n * ((N / n).divisors.card : ℝ) ≤
        (Real.log N + C₀) * N.divisors.card := by
  obtain ⟨C₀, hC⟩ := weil_multiplicativeToeplitz_bound hW
  refine ⟨C₀, fun N hN => ?_⟩
  have hsupp : ∀ m, N < m → divisorResonator N m = 0 := fun m hm => by
    unfold divisorResonator
    rw [if_neg]
    intro h
    exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have h := hC N hN (divisorResonator N) hsupp
  rw [sum_norm_sq_divisorResonator hN] at h
  have hl : ∑ n ∈ Icc 2 N, lam n / Real.sqrt n *
      (∑ m ∈ Icc 1 N, divisorResonator N (n * m) * conj (divisorResonator N m)).re =
      ∑ n ∈ N.divisors with 2 ≤ n, lam n / Real.sqrt n * ((N / n).divisors.card : ℝ) := by
    simp_rw [sum_divisorResonator_mul hN, Complex.ofReal_re]
    have e : ∀ n, lam n / Real.sqrt n * (if n ∣ N then ((N / n).divisors.card : ℝ) else 0) =
        if n ∣ N then lam n / Real.sqrt n * ((N / n).divisors.card : ℝ) else 0 := fun n => by
      split_ifs <;> simp
    simp_rw [e]
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h2, -⟩, hd⟩; exact ⟨⟨hd, by omega⟩, h2⟩
    · rintro ⟨⟨hd, -⟩, h2⟩; exact ⟨⟨h2, Nat.le_of_dvd (by omega) hd⟩, hd⟩
  rw [hl] at h
  exact h

/-! ## Multiplicative sign twists -/

/-- The sign character `χ_s(n) = ∏_{p ∣ n} s(p)`. -/
noncomputable def signChar (s : ℕ → ℝ) (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, s p

theorem signChar_mul (s : ℕ → ℝ) {m n : ℕ} (h : m.Coprime n) :
    signChar s (m * n) = signChar s m * signChar s n := by
  unfold signChar
  rw [h.primeFactors_mul, prod_union h.disjoint_primeFactors]

theorem signChar_sq {s : ℕ → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) (n : ℕ) :
    signChar s n ^ 2 = 1 := by
  unfold signChar
  rw [← prod_pow]
  exact prod_eq_one fun p _ => by rcases hs p with h | h <;> simp [h]

theorem signChar_one_fun (n : ℕ) : signChar (fun _ => 1) n = 1 := by
  unfold signChar; exact prod_const_one

/-- The twisted divisor resonator `c(m) = χ_s(m) 1_{m ∣ N}`. -/
noncomputable def twistedResonator (s : ℕ → ℝ) (N m : ℕ) : ℂ :=
  if m ∣ N then ((signChar s m : ℝ) : ℂ) else 0

theorem sum_norm_sq_twistedResonator {s : ℕ → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) {N : ℕ}
    (hN : 1 ≤ N) : ∑ m ∈ Icc 1 N, ‖twistedResonator s N m‖ ^ 2 = (N.divisors.card : ℝ) := by
  have h : ∀ m, ‖twistedResonator s N m‖ ^ 2 = if m ∣ N then (1 : ℝ) else 0 := fun m => by
    unfold twistedResonator
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, signChar_sq hs]
    · simp
  simp_rw [h]
  rw [sum_Icc_ite_dvd hN, sum_const, nsmul_eq_mul, mul_one]

theorem twistedResonator_mul_conj {s : ℕ → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) {N : ℕ}
    (hsq : Squarefree N) (n m : ℕ) :
    twistedResonator s N (n * m) * conj (twistedResonator s N m) =
      ((if n * m ∣ N then signChar s n else 0 : ℝ) : ℂ) := by
  unfold twistedResonator
  by_cases h1 : n * m ∣ N
  · have h2 : m ∣ N := (Dvd.intro_left n rfl).trans h1
    have hcop : n.Coprime m := (Nat.squarefree_mul_iff.mp (hsq.squarefree_of_dvd h1)).1
    rw [if_pos h1, if_pos h2, if_pos h1, Complex.conj_ofReal, ← Complex.ofReal_mul,
      signChar_mul s hcop, mul_assoc, ← sq, signChar_sq hs, mul_one]
  · simp [h1]

theorem sum_twistedResonator_mul {s : ℕ → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) {N n : ℕ}
    (hN : 1 ≤ N) (hsq : Squarefree N) :
    ∑ m ∈ Icc 1 N, twistedResonator s N (n * m) * conj (twistedResonator s N m) =
      ((if n ∣ N then signChar s n * ((N / n).divisors.card : ℝ) else 0 : ℝ) : ℂ) := by
  simp_rw [twistedResonator_mul_conj hs hsq]
  rw [← Complex.ofReal_sum]
  congr 1
  have hsplit : ∀ m, (if n * m ∣ N then signChar s n else 0) =
      signChar s n * (if n * m ∣ N then (1 : ℝ) else 0) := fun m => by split_ifs <;> simp
  simp_rw [hsplit]
  rw [← mul_sum]
  have h := sum_divisorResonator_mul (N := N) (n := n) hN
  simp_rw [divisorResonator_mul_conj] at h
  rw [← Complex.ofReal_sum] at h
  have h' := Complex.ofReal_injective h
  rw [h']
  split_ifs <;> simp

/-- **Twisted divisor resonance law.**  For Weil-positive weights, every sign pattern `s` on the
primes and every squarefree `N ≥ 1`:
`2 ∑_{n ∣ N, n ≥ 2} χ_s(n) lam(n) n^{-1/2} d(N/n) ≤ (log N + C₀) d(N)`. -/
theorem weil_twisted_divisor_resonance_bound {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    ∃ C₀ : ℝ, ∀ s : ℕ → ℝ, (∀ p, s p = 1 ∨ s p = -1) → ∀ N : ℕ, 1 ≤ N → Squarefree N →
      2 * ∑ n ∈ N.divisors with 2 ≤ n,
          signChar s n * lam n / Real.sqrt n * ((N / n).divisors.card : ℝ) ≤
        (Real.log N + C₀) * N.divisors.card := by
  obtain ⟨C₀, hC⟩ := weil_multiplicativeToeplitz_bound hW
  refine ⟨C₀, fun s hs N hN hsq => ?_⟩
  have hsupp : ∀ m, N < m → twistedResonator s N m = 0 := fun m hm => by
    unfold twistedResonator
    rw [if_neg]
    intro h
    exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have h := hC N hN (twistedResonator s N) hsupp
  rw [sum_norm_sq_twistedResonator hs hN] at h
  have hl : ∑ n ∈ Icc 2 N, lam n / Real.sqrt n *
      (∑ m ∈ Icc 1 N, twistedResonator s N (n * m) * conj (twistedResonator s N m)).re =
      ∑ n ∈ N.divisors with 2 ≤ n,
        signChar s n * lam n / Real.sqrt n * ((N / n).divisors.card : ℝ) := by
    simp_rw [sum_twistedResonator_mul hs hN hsq, Complex.ofReal_re]
    have e : ∀ n, lam n / Real.sqrt n *
        (if n ∣ N then signChar s n * ((N / n).divisors.card : ℝ) else 0) =
        if n ∣ N then signChar s n * lam n / Real.sqrt n * ((N / n).divisors.card : ℝ)
        else 0 := fun n => by
      split_ifs
      · ring
      · simp
    simp_rw [e]
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h2, -⟩, hd⟩; exact ⟨⟨hd, by omega⟩, h2⟩
    · rintro ⟨⟨hd, -⟩, h2⟩; exact ⟨⟨h2, Nat.le_of_dvd (by omega) hd⟩, hd⟩
  rw [hl] at h
  exact h

/-! ## The resonance mass of a primorial -/

/-- `n ↦ n^{-a}` as a real arithmetic function (zero at `0`). -/
noncomputable def rpowNeg (a : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ) ^ (-a), by simp⟩

theorem rpowNeg_apply (a : ℝ) {n : ℕ} (hn : n ≠ 0) : rpowNeg a n = (n : ℝ) ^ (-a) := by
  change (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-a)) = _
  rw [if_neg hn]

theorem isMultiplicative_rpowNeg (a : ℝ) : (rpowNeg a).IsMultiplicative := by
  refine ⟨by rw [rpowNeg_apply a one_ne_zero]; simp, fun {m n} _ => ?_⟩
  by_cases hm : m = 0
  · subst hm; simp [rpowNeg]
  by_cases hn : n = 0
  · subst hn; simp [rpowNeg]
  rw [rpowNeg_apply a (mul_ne_zero hm hn), rpowNeg_apply a hm, rpowNeg_apply a hn]
  push_cast
  exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The resonance mass `∑_{d ∣ N} d^{-a} d(N/d)`, a Dirichlet convolution of multiplicative
functions. -/
noncomputable def resonanceMass (a : ℝ) : ArithmeticFunction ℝ :=
  rpowNeg a * (ArithmeticFunction.sigma 0 : ArithmeticFunction ℝ)

theorem isMultiplicative_resonanceMass (a : ℝ) : (resonanceMass a).IsMultiplicative :=
  (isMultiplicative_rpowNeg a).mul ArithmeticFunction.isMultiplicative_sigma.natCast

theorem resonanceMass_apply (a : ℝ) (N : ℕ) :
    resonanceMass a N = ∑ d ∈ N.divisors, (d : ℝ) ^ (-a) * ((N / d).divisors.card : ℝ) := by
  unfold resonanceMass
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun x y => rpowNeg a x * (ArithmeticFunction.sigma 0 : ArithmeticFunction ℝ) y)]
  refine sum_congr rfl fun d hd => ?_
  rw [rpowNeg_apply a (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)), ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.sigma_zero_apply]

theorem resonanceMass_prime (a : ℝ) {p : ℕ} (hp : p.Prime) :
    resonanceMass a p = 2 + (p : ℝ) ^ (-a) := by
  rw [resonanceMass_apply, hp.divisors, sum_pair (Ne.symm hp.one_lt.ne')]
  rw [Nat.div_one, Nat.div_self hp.pos, hp.divisors, card_pair (Ne.symm hp.one_lt.ne'),
    Nat.divisors_one, card_singleton]
  simp

theorem resonanceMass_primorial (a : ℝ) (y : ℕ) :
    resonanceMass a (primorial y) = ∏ p ∈ y.primesLE, (2 + (p : ℝ) ^ (-a)) := by
  rw [primorial_eq_prod_primesLE, (isMultiplicative_resonanceMass a).map_prod_of_prime _
    fun _ hp => Nat.prime_of_mem_primesLE hp]
  exact prod_congr rfl fun p hp => resonanceMass_prime a (Nat.prime_of_mem_primesLE hp)

theorem card_divisors_primorial (y : ℕ) :
    ((primorial y).divisors.card : ℝ) = 2 ^ y.primesLE.card := by
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 0)).map_prod_of_prime y.primesLE
    fun _ hp => Nat.prime_of_mem_primesLE hp
  rw [← primorial_eq_prod_primesLE, ArithmeticFunction.sigma_zero_apply] at h
  rw [h, ← prod_const]
  push_cast
  refine prod_congr rfl fun q hq => ?_
  rw [ArithmeticFunction.sigma_zero_apply, (Nat.prime_of_mem_primesLE hq).divisors,
    card_pair (Ne.symm (Nat.prime_of_mem_primesLE hq).one_lt.ne')]
  norm_num

/-- Splitting off the divisor `1`: `∑_{n ∣ N, n ≥ 2} n^{-a} d(N/n) = M_a(N) - d(N)`. -/
theorem sum_divisors_two_le_eq (a : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ N.divisors with 2 ≤ n, (n : ℝ) ^ (-a) * ((N / n).divisors.card : ℝ) =
      resonanceMass a N - (N.divisors.card : ℝ) := by
  rw [resonanceMass_apply, ← sum_filter_add_sum_filter_not N.divisors (fun n => 2 ≤ n)]
  have h1 : N.divisors.filter (fun n => ¬ 2 ≤ n) = {1} := by
    ext m
    simp only [mem_filter, Nat.mem_divisors, mem_singleton]
    constructor
    · rintro ⟨⟨hd, -⟩, h2⟩
      have := Nat.pos_of_dvd_of_pos hd (by omega)
      omega
    · rintro rfl; exact ⟨⟨one_dvd N, by omega⟩, by omega⟩
  rw [h1, sum_singleton, Nat.div_one]
  simp

/-- **Primorial resonance inequality.**  If Weil-positive weights satisfy
`χ_s(n) lam(n) ≥ c n^{-δ}` on squarefree `n ≥ 2` for a sign pattern `s` (with `c, δ ≥ 0`), then for
every `y`, `2c (∏_{p ≤ y} (1 + p^{-1/2-δ}/2) - 1) ≤ log(y#) + C₀`. -/
theorem primorial_resonance_inequality {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    ∃ C₀ : ℝ, ∀ s : ℕ → ℝ, (∀ p, s p = 1 ∨ s p = -1) → ∀ c δ : ℝ, 0 ≤ c → 0 ≤ δ →
      (∀ n : ℕ, 2 ≤ n → Squarefree n → c * (n : ℝ) ^ (-δ) ≤ signChar s n * lam n) → ∀ y : ℕ,
        2 * c * (∏ p ∈ y.primesLE, (1 + (p : ℝ) ^ (-(1 / 2 + δ)) / 2) - 1) ≤
          Real.log (primorial y) + C₀ := by
  obtain ⟨C₀, hC⟩ := weil_twisted_divisor_resonance_bound hW
  refine ⟨C₀, fun s hs c δ hc hδ hlow y => ?_⟩
  set N := primorial y with hNdef
  have hN : 1 ≤ N := primorial_pos y
  have h := hC s hs N hN (squarefree_primorial y)
  set a : ℝ := 1 / 2 + δ with ha
  have hterm : ∀ n ∈ N.divisors.filter (fun n => 2 ≤ n),
      c * ((n : ℝ) ^ (-a) * ((N / n).divisors.card : ℝ)) ≤
        signChar s n * lam n / Real.sqrt n * ((N / n).divisors.card : ℝ) := by
    intro n hn
    obtain ⟨hnd, h2⟩ := mem_filter.mp hn
    have hsq : Squarefree n :=
      (squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors hnd)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hl := hlow n h2 hsq
    have hsqrt : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have hsp : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hpow : (n : ℝ) ^ (-a) = (n : ℝ) ^ (-δ) / Real.sqrt n := by
      rw [hsqrt, ha, neg_add, Real.rpow_add hn0, Real.rpow_neg hn0.le (1 / 2)]
      field_simp
    have hcard : (0 : ℝ) ≤ ((N / n).divisors.card : ℝ) := Nat.cast_nonneg _
    rw [hpow, ← mul_assoc, mul_div_assoc']
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hl hsp.le) hcard
  have hlower := sum_le_sum hterm
  rw [← mul_sum, sum_divisors_two_le_eq a hN, resonanceMass_primorial,
    card_divisors_primorial] at hlower
  rw [card_divisors_primorial] at h
  have hτ : (0 : ℝ) < 2 ^ y.primesLE.card := by positivity
  have hratio : ∏ p ∈ y.primesLE, (1 + (p : ℝ) ^ (-a) / 2) =
      (∏ p ∈ y.primesLE, (2 + (p : ℝ) ^ (-a))) / 2 ^ y.primesLE.card := by
    rw [← prod_const, ← prod_div_distrib]
    refine prod_congr rfl fun _ _ => by ring
  rw [hratio]
  have key : 2 * c * ((∏ p ∈ y.primesLE, (2 + (p : ℝ) ^ (-a))) - 2 ^ y.primesLE.card) ≤
      (Real.log N + C₀) * 2 ^ y.primesLE.card := by
    linarith
  rw [div_sub_one hτ.ne', mul_div_assoc', div_le_iff₀ hτ]
  linarith

/-! ## Growth estimates -/

theorem exp_half_le_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp (x / 2) ≤ 1 + x := by
  have hpos : 0 < 1 + x := by linarith
  have hlog : x / 2 ≤ Real.log (1 + x) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos
    have h2 : x / 2 ≤ 1 - (1 + x)⁻¹ := by
      rw [show 1 - (1 + x)⁻¹ = x / (1 + x) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) hpos]
      nlinarith
    linarith
  calc Real.exp (x / 2) ≤ Real.exp (Real.log (1 + x)) := Real.exp_le_exp.mpr hlog
    _ = 1 + x := Real.exp_log hpos

theorem eventually_log_le_mul_rpow {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ ε * x ^ r := by
  have h := (isLittleO_log_rpow_atTop hr).bound hε
  filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hp : 0 ≤ x ^ r := Real.rpow_nonneg (by linarith) r
  rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg hp] at hx
  exact hx

theorem eventually_log_sq_le {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ ε * x ^ b := by
  filter_upwards [eventually_log_le_mul_rpow (r := b / 2) (by linarith) (Real.sqrt_pos.mpr hε),
    eventually_ge_atTop 1] with x hx hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hx0 : 0 < x := by linarith
  have hsq : (Real.sqrt ε * x ^ (b / 2)) ^ 2 = ε * x ^ b := by
    rw [mul_pow, Real.sq_sqrt hε.le, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  calc Real.log x ^ 2 ≤ (Real.sqrt ε * x ^ (b / 2)) ^ 2 := pow_le_pow_left₀ hl hx 2
    _ = ε * x ^ b := hsq

theorem eventually_sqrt_mul_log_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x * Real.log x ≤ ε * x := by
  filter_upwards [eventually_log_le_mul_rpow (r := 1 / 2) (by norm_num) hε,
    eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 ≤ x := by linarith
  have hs : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  calc Real.sqrt x * Real.log x ≤ Real.sqrt x * (ε * x ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg x)
    _ = ε * x := by rw [← hs]; linear_combination ε * hss

theorem eventually_log_add_one_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log (x + 1) ≤ ε * x := by
  have h := (isLittleO_log_rpow_atTop (r := 1) one_pos).bound (show 0 < ε / 2 by linarith)
  filter_upwards [h, eventually_ge_atTop 1, eventually_ge_atTop (2 * Real.log 2 / ε)]
    with x hx hx1 hx2
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg hl, Real.rpow_one, Real.norm_of_nonneg hx0.le] at hx
  have h2x : Real.log (x + 1) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) hx0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hl2 : Real.log 2 ≤ ε / 2 * x := by
    have := (div_le_iff₀ hε).mp hx2
    linarith
  linarith

/-- The explicit lower bound `(x log 2 - log(x+1) - 2√x log x) x^{-a} / (4 log x)` for
`(1/4) ∑_{p ≤ x} p^{-a}`. -/
noncomputable def primeRpowLower (a x : ℝ) : ℝ :=
  (x * Real.log 2 - Real.log (x + 1) - 2 * Real.sqrt x * Real.log x) * x ^ (-a) /
    (4 * Real.log x)

theorem eventually_two_log_le_primeRpowLower {a : ℝ} (ha1 : a < 1) :
    ∀ᶠ x : ℝ in atTop, 2 * Real.log x ≤ primeRpowLower a x := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < 1 - a := by linarith
  filter_upwards [eventually_log_add_one_le (show 0 < Real.log 2 / 4 by positivity),
    eventually_sqrt_mul_log_le (show 0 < Real.log 2 / 8 by positivity),
    eventually_log_sq_le hb (show 0 < Real.log 2 / 16 by positivity),
    eventually_ge_atTop 3] with x h1 h2 h3 hx3
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hnum : Real.log 2 / 2 * x ≤
      x * Real.log 2 - Real.log (x + 1) - 2 * Real.sqrt x * Real.log x := by nlinarith
  have hxa : x * x ^ (-a) = x ^ (1 - a) := by
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
  have hpa : 0 ≤ x ^ (-a) := Real.rpow_nonneg hx0.le _
  have hstep : Real.log 2 / 8 * x ^ (1 - a) / Real.log x ≤ primeRpowLower a x := by
    unfold primeRpowLower
    rw [div_le_div_iff₀ hlx (by positivity)]
    have := mul_le_mul_of_nonneg_right hnum hpa
    rw [← hxa] at *
    nlinarith
  have hfin : 2 * Real.log x ≤ Real.log 2 / 8 * x ^ (1 - a) / Real.log x := by
    rw [le_div_iff₀ hlx]
    nlinarith
  linarith

theorem eventually_linear_lt_exp {a c C : ℝ} (ha1 : a < 1) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x * Real.log 4 + C < 2 * c * (Real.exp (primeRpowLower a x) - 1) := by
  set K : ℝ := (Real.log 4 + |C| + 2 * c) / (2 * c) + 1 with hK
  filter_upwards [eventually_two_log_le_primeRpowLower ha1, eventually_ge_atTop K,
    eventually_ge_atTop 1] with x hL hxK hx1
  have hx0 : 0 < x := by linarith
  have hexp : x * x ≤ Real.exp (primeRpowLower a x) := by
    calc x * x = Real.exp (Real.log x) * Real.exp (Real.log x) := by rw [Real.exp_log hx0]
      _ = Real.exp (2 * Real.log x) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (primeRpowLower a x) := Real.exp_le_exp.mpr hL
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hKc : (Real.log 4 + |C| + 2 * c) < 2 * c * K := by
    rw [hK, mul_add, mul_div_cancel₀ _ (by positivity)]
    linarith
  have hbig : (Real.log 4 + |C| + 2 * c) * x < 2 * c * (x * x) := by
    have : 2 * c * K * x ≤ 2 * c * (x * x) := by
      have := mul_le_mul_of_nonneg_left hxK (show 0 ≤ 2 * c * x by positivity)
      nlinarith
    nlinarith
  have hC : C ≤ |C| * x := (le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg C) hx1)
  have h1 : 2 * c * (x * x - 1) ≤ 2 * c * (Real.exp (primeRpowLower a x) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : 2 * c ≤ 2 * c * x := le_mul_of_one_le_right (by positivity) hx1
  nlinarith

/-! ## Prime sums over the primorial -/

theorem exp_sum_le_prod_one_add {a : ℝ} (ha : 0 ≤ a) (y : ℕ) :
    Real.exp (∑ p ∈ y.primesLE, (p : ℝ) ^ (-a) / 4) ≤
      ∏ p ∈ y.primesLE, (1 + (p : ℝ) ^ (-a) / 2) := by
  rw [Real.exp_sum]
  refine prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun p hp => ?_
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le
  have hle : (p : ℝ) ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  have hnn : 0 ≤ (p : ℝ) ^ (-a) := Real.rpow_nonneg (by linarith) _
  have h := exp_half_le_one_add (x := (p : ℝ) ^ (-a) / 2) (by linarith) (by linarith)
  rw [show (p : ℝ) ^ (-a) / 2 / 2 = (p : ℝ) ^ (-a) / 4 by ring] at h
  exact h

theorem card_mul_rpow_le_sum {a : ℝ} (ha : 0 ≤ a) (y : ℕ) :
    (y.primesLE.card : ℝ) * (y : ℝ) ^ (-a) ≤ ∑ p ∈ y.primesLE, (p : ℝ) ^ (-a) := by
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun p hp => ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
  have hpy : (p : ℝ) ≤ y := by exact_mod_cast Nat.le_of_mem_primesLE hp
  exact Real.rpow_le_rpow_of_nonpos hp0 hpy (by linarith)

theorem sum_log_le_card_mul_log (y : ℕ) :
    ∑ p ∈ y.primesLE, Real.log p ≤ (y.primesLE.card : ℝ) * Real.log y := by
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun p hp => ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
  exact Real.log_le_log hp0 (by exact_mod_cast Nat.le_of_mem_primesLE hp)

/-- `(1/4) ∑_{p ≤ y} p^{-a} ≥ (y log 2 - log(y+1) - 2√y log y) y^{-a} / (4 log y)`, from Chebyshev's
lower bound for `θ(y)`. -/
theorem primeRpowLower_le_sum {a : ℝ} (ha : 0 ≤ a) {y : ℕ} (hy : 3 ≤ y) :
    primeRpowLower a y ≤ ∑ p ∈ y.primesLE, (p : ℝ) ^ (-a) / 4 := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hθ := Chebyshev.theta_ge y
  rw [Chebyshev.theta_eq_sum_primesLE_log] at hθ
  have hcard := sum_log_le_card_mul_log y
  have hsum := card_mul_rpow_le_sum ha y
  have hpa : 0 ≤ (y : ℝ) ^ (-a) := Real.rpow_nonneg hy0.le _
  rw [← sum_div]
  unfold primeRpowLower
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : ((y : ℝ) * Real.log 2 - Real.log (y + 1) - 2 * Real.sqrt y * Real.log y) *
      (y : ℝ) ^ (-a) ≤ (y.primesLE.card : ℝ) * Real.log y * (y : ℝ) ^ (-a) :=
    mul_le_mul_of_nonneg_right (hθ.trans hcard) hpa
  have h2 : (y.primesLE.card : ℝ) * Real.log y * (y : ℝ) ^ (-a) ≤
      (∑ p ∈ y.primesLE, (p : ℝ) ^ (-a)) * Real.log y := by
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right hsum hly.le
  nlinarith

theorem log_primorial_le (y : ℕ) : Real.log (primorial y) ≤ y * Real.log 4 := by
  have h0 : (0 : ℝ) < primorial y := by exact_mod_cast primorial_pos y
  have h4 : (primorial y : ℝ) ≤ (4 : ℝ) ^ y := by exact_mod_cast primorial_le_four_pow y
  calc Real.log (primorial y) ≤ Real.log ((4 : ℝ) ^ y) := Real.log_le_log h0 h4
    _ = y * Real.log 4 := Real.log_pow 4 y

/-! ## The exclusion theorem -/

/-- **No Weil-positive weight system satisfies `χ_s(n) lam(n) ≥ c n^{-δ}` on the squarefree
integers, for any sign pattern `s`, `c > 0` and `δ < 1/2`.**  The resonator `1_{m ∣ y#}` in the multiplicative Toeplitz bound
gives `2c(∏_{p ≤ y}(1 + p^{-1/2-δ}/2) - 1) ≤ log(y#) + C₀ ≤ y log 4 + C₀`, while the product is at
least `exp((1/4)∑_{p ≤ y} p^{-1/2-δ})`, which grows like `exp(c' y^{1/2-δ}/log y)` by Chebyshev's
bound. -/
theorem not_forall_squarefree_signChar_le_of_weilPositive {lam : ℕ → ℝ} (hW : WeilPositive lam)
    {s : ℕ → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) {c δ : ℝ} (hc : 0 < c) (hδ : δ < 1 / 2) :
    ¬ ∀ n : ℕ, 2 ≤ n → Squarefree n → c * (n : ℝ) ^ (-δ) ≤ signChar s n * lam n := by
  intro hlow
  set δ' := max δ 0 with hδ'
  have hδ'0 : 0 ≤ δ' := le_max_right _ _
  have hδ'1 : δ' < 1 / 2 := max_lt hδ (by norm_num)
  have hlow' : ∀ n : ℕ, 2 ≤ n → Squarefree n → c * (n : ℝ) ^ (-δ') ≤ signChar s n * lam n := by
    intro n hn hsq
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hmono : (n : ℝ) ^ (-δ') ≤ (n : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg (le_max_left _ _))
    exact (mul_le_mul_of_nonneg_left hmono hc.le).trans (hlow n hn hsq)
  obtain ⟨C₀, hC⟩ := primorial_resonance_inequality hW
  have hineq := hC s hs c δ' hc.le hδ'0 hlow'
  set a : ℝ := 1 / 2 + δ' with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have ha1 : a < 1 := by rw [ha]; linarith
  have hev := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_linear_lt_exp (C := C₀) ha1 hc)
  obtain ⟨y, hy, hy3⟩ := (hev.and (eventually_ge_atTop 3)).exists
  have h1 := hineq y
  have hprod : Real.exp (primeRpowLower a y) ≤ ∏ p ∈ y.primesLE, (1 + (p : ℝ) ^ (-a) / 2) :=
    (Real.exp_le_exp.mpr (primeRpowLower_le_sum ha0 hy3)).trans (exp_sum_le_prod_one_add ha0 y)
  have h2 : 2 * c * (Real.exp (primeRpowLower a y) - 1) ≤
      2 * c * (∏ p ∈ y.primesLE, (1 + (p : ℝ) ^ (-a) / 2) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 := log_primorial_le y
  linarith

/-- The full-cone twisted form. -/
theorem not_forall_squarefree_signChar_le_of_weilPositiveFull {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {s : ℕ → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) {c δ : ℝ}
    (hc : 0 < c) (hδ : δ < 1 / 2) :
    ¬ ∀ n : ℕ, 2 ≤ n → Squarefree n → c * (n : ℝ) ^ (-δ) ≤ signChar s n * lam n :=
  not_forall_squarefree_signChar_le_of_weilPositive (weilPositive_of_weilPositiveFull hW) hs hc hδ

/-- **No full-cone Weil-positive weight system is bounded below by `c n^{-δ}` on the squarefree
integers `n ≥ 2`, for any `c > 0` and `δ < 1/2`.** -/
theorem not_forall_squarefree_le_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {c δ : ℝ} (hc : 0 < c) (hδ : δ < 1 / 2) :
    ¬ ∀ n : ℕ, 2 ≤ n → Squarefree n → c * (n : ℝ) ^ (-δ) ≤ lam n := by
  intro h
  refine not_forall_squarefree_signChar_le_of_weilPositiveFull hW (s := fun _ => 1)
    (fun _ => Or.inl rfl) hc hδ fun n hn hsq => ?_
  rw [signChar_one_fun, one_mul]
  exact h n hn hsq

/-- **Möbius-signed form.**  No full-cone Weil-positive weight system satisfies
`μ(n) lam(n) ≥ c n^{-δ}` on the squarefree integers `n ≥ 2`, for any `c > 0` and `δ < 1/2`. -/
theorem not_forall_squarefree_moebius_le_of_weilPositiveFull {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {c δ : ℝ} (hc : 0 < c) (hδ : δ < 1 / 2) :
    ¬ ∀ n : ℕ, 2 ≤ n → Squarefree n →
      c * (n : ℝ) ^ (-δ) ≤ (ArithmeticFunction.moebius n : ℝ) * lam n := by
  intro h
  refine not_forall_squarefree_signChar_le_of_weilPositiveFull hW (s := fun _ => -1)
    (fun _ => Or.inr rfl) hc hδ fun n hn hsq => ?_
  have hμ : (ArithmeticFunction.moebius n : ℝ) = signChar (fun _ => -1) n := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    unfold signChar
    rw [prod_const, ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
      (by omega)).mpr hsq, ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
      Nat.toFinset_factors]
    push_cast
    ring
  rw [← hμ]
  exact h n hn hsq

end PrimorialResonance
end RHTower
