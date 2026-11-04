import GaloisForLFunctions.ArithmeticGaugeTheory.AnExplicitPointHasExponentOneHalf
import GaloisForLFunctions.ArithmeticCorrelationGeometry.ThePrimeSourceIsTypicalExceptForItsPole
import GaloisForLFunctions.RHTower.Sieve.ChebyshevErrorPowerBound

/-!
# The pole does not decide the half-power law

The prime source `ψ_y(N) = Σ_{n ≤ N} Λ(n) χ_y(n)` is atypical at the trivial point `0` exactly by
its pole, `ψ_0(N) ~ N`, and RH is the pole-subtracted half-power law at `0`. This module shows that no
property of the pole decides that law: knowing the pole to any precision `N^b` with `b < 1` says
nothing about exponents below `b`.

**Flip points.** For `0 < θ < 1` the block `F_k` (`flipBlock θ k`) is the set of the first
`⌊4^{θk}⌋` primes of `(4^k, 2·4^k]`; the flip point `x_θ` (`flipPoint θ`) has `χ(p) = −1` on the
block primes and `χ(p) = 1` elsewhere. On prime powers `χ_{x_θ}(p^k) = ±1`, so
`ψ_0(N) − ψ_{x_θ}(N) = T_θ(N) = Σ_{n ≤ N} Λ(n)(1 − Re χ_{x_θ}(n)) ≥ 0` (`twistedPsi_zero_sub_flipPoint`).

* **The charge is of size `N^θ`** (`flipCharge_le`, `eventually_flipSize_le_flipCharge`).
  `T_θ(N) ≤ 2 log N · #{flip primes ≤ N} ≤ C N^θ log N`, while `T_θ(2·4^k) ≥ ⌊4^{θk}⌋` for all large
  `k`, since by the prime number theorem the octave eventually holds `⌊4^{θk}⌋` primes.
* **The same pole** (`sharesPoleUpTo_flipPoint`, `tendsto_twistedPsi_flipPoint_div`). `x_θ` agrees
  with `0` up to `(N+1)^b` for every `b > θ`; in particular `ψ_{x_θ}(N)/N → 1`.
* **Exponents** (`not_poleSubtractedPowerLaw_flipPoint`, `poleSubtractedPowerLaw_flipPoint`). Below
  `θ` the two points cannot both satisfy the pole-subtracted power law; above `θ` the law passes
  from `0` to `x_θ`. Under RH the pole-subtracted exponent of `x_θ` is exactly `θ`
  (`riemannHypothesis_flipPoint_exponent`).
* **The spectrum** (`poleSubtractedExponent_flipPoint`). The pole-subtracted exponent of `x_θ` is
  exactly `θ` for every `θ` between the exponent of `0` and `1`; under RH every value in `(1/2, 1)`
  is attained by a point carrying the pole of `0`
  (`riemannHypothesis_poleSubtractedExponent_spectrum`).
* **The answer** (`pole_does_not_decide_powerLaw`). For `0 < b < 1` and `a < b` some gauge point
  shares the pole of `0` up to `(N+1)^b` and violates the pole-subtracted power law of exponent `a`.
  A proof of the half-power law at `0` must therefore read the prime source at precision `N^{1/2+ε}`
  on sparse prime sets, which is the half-power law itself.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-! ### Power laws of the prime source -/

/-- The pole-subtracted power law of exponent `a` at `y`: `‖ψ_y(N) − N‖ ≤ C (N+1)^a`. -/
def PoleSubtractedPowerLaw (y : GaugeTorus) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖twistedPsi N y - N‖ ≤ C * ((N : ℝ) + 1) ^ a

/-- `y` carries the pole of the trivial point up to precision `(N+1)^b`. -/
def SharesPoleUpTo (y : GaugeTorus) (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖twistedPsi N y - twistedPsi N 0‖ ≤ C * ((N : ℝ) + 1) ^ b

theorem PoleSubtractedPowerLaw.mono {y : GaugeTorus} {a a' : ℝ}
    (h : PoleSubtractedPowerLaw y a) (ha : a ≤ a') : PoleSubtractedPowerLaw y a' := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun N => (hb N).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [N.cast_nonneg (α := ℝ)]) ha

/-! ### The flip blocks -/

/-- The size `⌊4^{θk}⌋` of the `k`-th block. -/
def flipSize (θ : ℝ) (k : ℕ) : ℕ := ⌊(4 : ℝ) ^ (θ * k)⌋₊

/-- **The `k`-th flip block**: the first `⌊4^{θk}⌋` primes of `(4^k, 2·4^k]`. -/
def flipBlock (θ : ℝ) (k : ℕ) : Finset ℕ :=
  (((octavePrimes k).sort (· ≤ ·)).take (flipSize θ k)).toFinset

/-- The flip primes. -/
def flipPrimes (θ : ℝ) : Set ℕ := {p | ∃ k, p ∈ flipBlock θ k}

/-- **The flip point**: the Liouville phase `1/2` on the flip primes, `0` elsewhere. -/
def flipPoint (θ : ℝ) : GaugeTorus := (flipPrimes θ).indicator fun _ => ((1 / 2 : ℝ) : UnitAddCircle)

theorem mem_flipBlock {θ : ℝ} {k p : ℕ} (hp : p ∈ flipBlock θ k) :
    p.Prime ∧ 4 ^ k < p ∧ p ≤ 2 * 4 ^ k := by
  rw [flipBlock, List.mem_toFinset] at hp
  have := (Finset.mem_sort _).mp (List.mem_of_mem_take hp)
  simp only [octavePrimes, mem_filter, mem_Ioc] at this
  exact ⟨this.2, this.1.1, this.1.2⟩

theorem card_flipBlock (θ : ℝ) (k : ℕ) :
    (flipBlock θ k).card = min (flipSize θ k) (octavePrimes k).card := by
  rw [flipBlock, List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).sublist
    (List.take_sublist _ _)), List.length_take, Finset.length_sort]

theorem flipSize_le {θ : ℝ} (k : ℕ) : (flipSize θ k : ℝ) ≤ ((4 : ℝ) ^ θ) ^ k := by
  rw [flipSize, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  exact Nat.floor_le (by positivity)

/-- The flip point takes `−1` on the flip primes. -/
theorem twist_flipPoint_of_mem {θ : ℝ} {p : ℕ} (hp : p.Prime) (h : p ∈ flipPrimes θ) :
    twist (flipPoint θ) p = -1 := by
  rw [twist_prime_apply _ hp, flipPoint, Set.indicator_of_mem h, fourier_coe_apply,
    show 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * (((1 / 2 : ℝ)) : ℂ) / ((1 : ℝ) : ℂ) =
      Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- The flip point takes `1` on the other primes. -/
theorem twist_flipPoint_of_notMem {θ : ℝ} {p : ℕ} (hp : p.Prime) (h : p ∉ flipPrimes θ) :
    twist (flipPoint θ) p = 1 := by
  rw [twist_prime_apply _ hp, flipPoint, Set.indicator_of_notMem h]
  exact fourier_eval_zero _

theorem twist_pow_of_ne_zero (x : GaugeTorus) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    twist x (p ^ k) = twist x p ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, twist_mul x (pow_ne_zero _ hp) hp, ih, pow_succ]

/-- On a prime power the flip point is `±1`, real. -/
theorem twist_flipPoint_primePow {θ : ℝ} {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ∈ flipPrimes θ → twist (flipPoint θ) (p ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ)) ∧
      (p ∉ flipPrimes θ → twist (flipPoint θ) (p ^ k) = 1) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [twist_pow_of_ne_zero _ hp.ne_zero, twist_flipPoint_of_mem hp h]; push_cast; rfl
  · rw [twist_pow_of_ne_zero _ hp.ne_zero, twist_flipPoint_of_notMem hp h, one_pow]

/-! ### The flip charge -/

/-- **The flip charge** `T_θ(N) = Σ_{n ≤ N} Λ(n)(1 − Re χ_{x_θ}(n))`. -/
def flipCharge (θ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, Λ n * (1 - (twist (flipPoint θ) n).re)

theorem flipCharge_term_nonneg (θ : ℝ) (n : ℕ) : 0 ≤ Λ n * (1 - (twist (flipPoint θ) n).re) := by
  refine mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr ?_)
  exact (Complex.re_le_norm _).trans (norm_twist _ _).le

/-- The flip point is real on the support of `Λ`. -/
theorem vonMangoldt_mul_twist_flipPoint (θ : ℝ) (n : ℕ) :
    ((Λ n : ℝ) : ℂ) * twist (flipPoint θ) n = ((Λ n * (twist (flipPoint θ) n).re : ℝ) : ℂ) := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, -, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    by_cases hS : p ∈ flipPrimes θ
    · rw [(twist_flipPoint_primePow hp k).1 hS, Complex.ofReal_re]; push_cast; ring
    · rw [(twist_flipPoint_primePow hp k).2 hS]; simp
  · have h0 : Λ n = 0 := by
      by_contra h
      exact hn (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h)
    simp [h0]

/-- **The charge identity**: `ψ_0(N) − ψ_{x_θ}(N) = T_θ(N)`. -/
theorem twistedPsi_zero_sub_flipPoint (θ : ℝ) (N : ℕ) :
    twistedPsi N 0 - twistedPsi N (flipPoint θ) = (flipCharge θ N : ℂ) := by
  rw [twistedPsi, twistedPsi, ← sum_sub_distrib, flipCharge]
  push_cast
  refine sum_congr rfl fun n _ => ?_
  have h := vonMangoldt_mul_twist_flipPoint θ n
  push_cast at h
  rw [ArithmeticCorrelationGeometry.twist_zero, h]
  ring

/-- The powers of one prime carry `Λ`-mass at most `log N` below `N`. -/
theorem sum_vonMangoldt_base_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ n ∈ (Ioc 0 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), Λ n ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set K := Nat.log p N
  have hsub : (Ioc 0 N).filter (fun n => IsPrimePow n ∧ n.minFac = p) ⊆
      (Icc 1 K).image (p ^ ·) := by
    intro n hn
    obtain ⟨hnI, hpp, hmin⟩ := mem_filter.mp hn
    have hn' := hpp.minFac_pow_factorization_eq
    rw [hmin] at hn'
    refine mem_image.mpr ⟨n.factorization p, mem_Icc.mpr ⟨?_, ?_⟩, hn'⟩
    · by_contra h0
      rw [show n.factorization p = 0 by omega, pow_zero] at hn'
      exact hpp.ne_one hn'.symm
    · exact Nat.le_log_of_pow_le hp.one_lt (hn'.trans_le (mem_Ioc.mp hnI).2)
  calc _ ≤ ∑ n ∈ (Icc 1 K).image (p ^ ·), Λ n :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ k ∈ Icc 1 K, Λ (p ^ k) :=
        sum_image_le_of_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = ∑ _k ∈ Icc 1 K, Real.log p := sum_congr rfl fun k hk => by
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by have := (mem_Icc.mp hk).1; omega),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
    _ = Real.log ((p ^ K : ℕ) : ℝ) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.cast_pow, Real.log_pow]
        simp
    _ ≤ Real.log N := Real.log_le_log (by exact_mod_cast pow_pos hp.pos K)
        (by exact_mod_cast Nat.pow_log_le_self p hN.ne')

/-- The flip primes up to `N`. -/
def flipPrimesUpTo (θ : ℝ) (N : ℕ) : Finset ℕ := by
  classical exact (Icc 1 N).filter (· ∈ flipPrimes θ)

/-- **Upper bound for the charge**: `T_θ(N) ≤ 2 log N · #{flip primes ≤ N}`. -/
theorem flipCharge_le (θ : ℝ) (N : ℕ) :
    flipCharge θ N ≤ 2 * Real.log N * (flipPrimesUpTo θ N).card := by
  classical
  set F := flipPrimesUpTo θ N
  set P : ℕ → Prop := fun n => IsPrimePow n ∧ n.minFac ∈ F
  -- Terms off the flip primes vanish; the others are at most `2Λ(n)`.
  have hterm : ∀ n ∈ Ioc 0 N, Λ n * (1 - (twist (flipPoint θ) n).re) ≤
      if P n then 2 * Λ n else 0 := by
    intro n hn
    by_cases hpp : IsPrimePow n
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
      have hmin : (p ^ k).minFac = p := Nat.Prime.pow_minFac hp hk.ne'
      by_cases hS : p ∈ flipPrimes θ
      · have hF : p ∈ F := by
          simp only [F, flipPrimesUpTo, mem_filter, mem_Icc]
          refine ⟨⟨hp.one_le, ?_⟩, hS⟩
          exact (Nat.le_self_pow hk.ne' p).trans (mem_Ioc.mp hn).2
        rw [if_pos ⟨hpp, by rw [hmin]; exact hF⟩, (twist_flipPoint_primePow hp k).1 hS,
          Complex.ofReal_re]
        have hk1 : -1 ≤ (-1 : ℝ) ^ k := by
          rcases neg_one_pow_eq_or ℝ k with h | h <;> linarith
        nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := p ^ k)]
      · rw [(twist_flipPoint_primePow hp k).2 hS]
        split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
    · have h0 : Λ n = 0 := by
        by_contra h
        exact hpp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h)
      simp [h0]
  have hfib : ∑ n ∈ (Ioc 0 N).filter P, 2 * Λ n =
      ∑ p ∈ F, ∑ n ∈ ((Ioc 0 N).filter P).filter (fun n => n.minFac = p), 2 * Λ n :=
    (sum_fiberwise_of_maps_to (fun n hn => (mem_filter.mp hn).2.2) _).symm
  have hinner : ∀ p ∈ F, ∑ n ∈ ((Ioc 0 N).filter P).filter (fun n => n.minFac = p), 2 * Λ n ≤
      2 * Real.log N := by
    intro p hp
    have hpr : p.Prime := by
      simp only [F, flipPrimesUpTo, mem_filter] at hp
      obtain ⟨k, hk⟩ := hp.2
      exact (mem_flipBlock hk).1
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ =>
      ArithmeticFunction.vonMangoldt_nonneg).trans (sum_vonMangoldt_base_le hpr N)) (by norm_num)
    intro n hn
    simp only [mem_filter] at hn ⊢
    exact ⟨hn.1.1, hn.1.2.1, hn.2⟩
  calc flipCharge θ N ≤ ∑ n ∈ Ioc 0 N, if P n then 2 * Λ n else 0 := sum_le_sum hterm
    _ = ∑ n ∈ (Ioc 0 N).filter P, 2 * Λ n := (sum_filter _ _).symm
    _ ≤ ∑ _p ∈ F, 2 * Real.log N := hfib ▸ sum_le_sum hinner
    _ = 2 * Real.log N * F.card := by rw [sum_const, nsmul_eq_mul]; ring

/-- **Counting the flip primes**: `#{flip primes ≤ N} ≤ 4^θ/(4^θ − 1) · N^θ`. -/
theorem card_flipPrimesUpTo_le {θ : ℝ} (hθ : 0 < θ) (N : ℕ) :
    ((flipPrimesUpTo θ N).card : ℝ) ≤ (4 : ℝ) ^ θ / ((4 : ℝ) ^ θ - 1) * (N : ℝ) ^ θ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [flipPrimesUpTo, Real.zero_rpow hθ.ne']
  set r : ℝ := (4 : ℝ) ^ θ
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hθ
  set K := Nat.log 4 N + 1
  have hsub : flipPrimesUpTo θ N ⊆ (range K).biUnion (flipBlock θ) := by
    intro p hp
    simp only [flipPrimesUpTo, mem_filter, mem_Icc] at hp
    obtain ⟨k, hk⟩ := hp.2
    refine mem_biUnion.mpr ⟨k, mem_range.mpr (Nat.lt_succ_of_le ?_), hk⟩
    exact Nat.le_log_of_pow_le (by norm_num) ((mem_flipBlock hk).2.1.le.trans hp.1.2)
  have hcard : ((flipPrimesUpTo θ N).card : ℝ) ≤ ∑ k ∈ range K, r ^ k := by
    calc ((flipPrimesUpTo θ N).card : ℝ) ≤ (((range K).biUnion (flipBlock θ)).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ ∑ k ∈ range K, ((flipBlock θ k).card : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ k ∈ range K, r ^ k := sum_le_sum fun k _ => by
          rw [card_flipBlock]
          exact (Nat.cast_le.mpr (min_le_left _ _)).trans (flipSize_le k)
  have hgeom : (∑ k ∈ range K, r ^ k) ≤ r ^ K / (r - 1) := by
    rw [le_div_iff₀ (sub_pos.mpr hr), geom_sum_mul]
    linarith [pow_pos (zero_lt_one.trans hr) K]
  have hpow : r ^ K ≤ r * (N : ℝ) ^ θ := by
    have h4 : ((4 ^ Nat.log 4 N : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.pow_log_le_self 4 hN.ne'
    have h4' : r ^ Nat.log 4 N ≤ (N : ℝ) ^ θ := by
      rw [show r ^ Nat.log 4 N = ((4 ^ Nat.log 4 N : ℕ) : ℝ) ^ θ by
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
          Real.rpow_mul (by norm_num), Real.rpow_natCast]; push_cast; rfl]
      exact Real.rpow_le_rpow (by positivity) h4 hθ.le
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left h4' (by positivity)
  calc ((flipPrimesUpTo θ N).card : ℝ) ≤ r ^ K / (r - 1) := hcard.trans hgeom
    _ ≤ r * (N : ℝ) ^ θ / (r - 1) := div_le_div_of_nonneg_right hpow (sub_pos.mpr hr).le
    _ = _ := by ring

/-! ### The same pole -/

theorem flipCharge_nonneg (θ : ℝ) (N : ℕ) : 0 ≤ flipCharge θ N :=
  sum_nonneg fun n _ => flipCharge_term_nonneg θ n

/-- **The flip point carries the pole of `0`** up to every precision `(N+1)^b` with `b > θ`. -/
theorem sharesPoleUpTo_flipPoint {θ b : ℝ} (hθ : 0 < θ) (hb : θ < b) :
    SharesPoleUpTo (flipPoint θ) b := by
  have hr : 1 < (4 : ℝ) ^ θ := Real.one_lt_rpow (by norm_num) hθ
  have hr' : 0 < (4 : ℝ) ^ θ - 1 := sub_pos.mpr hr
  have hε : 0 < b - θ := sub_pos.mpr hb
  refine ⟨2 / (b - θ) * ((4 : ℝ) ^ θ / ((4 : ℝ) ^ θ - 1)), by positivity, fun N => ?_⟩
  rw [← neg_sub, norm_neg, twistedPsi_zero_sub_flipPoint, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (flipCharge_nonneg θ N)]
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hN : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
  -- `log N ≤ (N+1)^{b−θ}/(b−θ)` and `#{flip primes ≤ N} ≤ c (N+1)^θ`.
  have hlog : Real.log N ≤ ((N : ℝ) + 1) ^ (b - θ) / (b - θ) :=
    (Real.log_le_rpow_div (Nat.cast_nonneg N) hε).trans
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg N) hN hε.le) hε.le)
  have hcard : ((flipPrimesUpTo θ N).card : ℝ) ≤
      (4 : ℝ) ^ θ / ((4 : ℝ) ^ θ - 1) * ((N : ℝ) + 1) ^ θ :=
    (card_flipPrimesUpTo_le hθ N).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg N) hN hθ.le) (by positivity))
  have hsplit : ((N : ℝ) + 1) ^ b = ((N : ℝ) + 1) ^ (b - θ) * ((N : ℝ) + 1) ^ θ := by
    rw [← Real.rpow_add hN1, sub_add_cancel]
  calc flipCharge θ N ≤ 2 * Real.log N * (flipPrimesUpTo θ N).card := flipCharge_le θ N
    _ ≤ 2 * (((N : ℝ) + 1) ^ (b - θ) / (b - θ)) *
          ((4 : ℝ) ^ θ / ((4 : ℝ) ^ θ - 1) * ((N : ℝ) + 1) ^ θ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlog (by norm_num)) hcard (Nat.cast_nonneg _)
          (by positivity)
    _ = _ := by rw [hsplit]; ring

/-- The pole is the same: `ψ_{x_θ}(N)/N → 1` for `0 < θ < 1`. -/
theorem tendsto_twistedPsi_flipPoint_div {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    Tendsto (fun N : ℕ => twistedPsi N (flipPoint θ) / (N : ℂ)) atTop (𝓝 1) := by
  set b := (θ + 1) / 2
  obtain ⟨C, hC, hb⟩ := sharesPoleUpTo_flipPoint hθ (show θ < b by simp only [b]; linarith)
  have hb1 : b - 1 < 0 := by simp only [b]; linarith
  -- The difference is `O(N^{b−1}) → 0`.
  have hdiff : Tendsto (fun N : ℕ => (twistedPsi N (flipPoint θ) - twistedPsi N 0) / (N : ℂ))
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => C * 2 ^ b * (N : ℝ) ^ (b - 1)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (by linarith : 0 < -(b - 1))).comp
        tendsto_natCast_atTop_atTop
      simpa [neg_neg] using this.const_mul (C * 2 ^ b)
    refine squeeze_zero_norm' ?_ hpow
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hN0]
    have h2 : ((N : ℝ) + 1) ^ b ≤ 2 ^ b * (N : ℝ) ^ b := by
      rw [← Real.mul_rpow (by norm_num) hN0.le]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by simp only [b]; linarith)
    have hNb : (N : ℝ) ^ (b - 1) * N = (N : ℝ) ^ b := by
      rw [← Real.rpow_add_one hN0.ne', sub_add_cancel]
    calc ‖twistedPsi N (flipPoint θ) - twistedPsi N 0‖ ≤ C * ((N : ℝ) + 1) ^ b := hb N
      _ ≤ C * (2 ^ b * (N : ℝ) ^ b) := mul_le_mul_of_nonneg_left h2 hC
      _ = C * 2 ^ b * (N : ℝ) ^ (b - 1) * N := by rw [mul_assoc (C * 2 ^ b), hNb]; ring
  have hsum := tendsto_twistedPsi_zero_div.add hdiff
  rw [add_zero] at hsum
  refine hsum.congr fun N => ?_
  ring

/-! ### The exponents -/

/-- **Eventually every block is full**: the octave `(4^k, 2·4^k]` holds `⌊4^{θk}⌋` primes for all
large `k` when `θ < 1` (prime number theorem). -/
theorem eventually_card_flipBlock {θ : ℝ} (hθ1 : θ < 1) :
    ∀ᶠ k : ℕ in atTop, (flipBlock θ k).card = flipSize θ k := by
  have hwin := HTGeometry.eventually_primeCount_window_ge (K := 2) (by norm_num)
  have h4 : Tendsto (fun k : ℕ => (4 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hr : 1 < (4 : ℝ) ^ (1 - θ) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hlin := (tendsto_pow_const_div_const_pow_of_one_lt 1 hr).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * Real.log 4) by positivity))
  filter_upwards [h4.eventually hwin, hlin, eventually_ge_atTop 1] with k hk hkl hk0
  rw [card_flipBlock, min_eq_left]
  have hfl1 : ⌊(2 : ℝ) * (4 : ℝ) ^ k⌋₊ = 2 * 4 ^ k := by
    rw [show (2 : ℝ) * (4 : ℝ) ^ k = ((2 * 4 ^ k : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hfl2 : ⌊(4 : ℝ) ^ k⌋₊ = 4 ^ k := by
    rw [show (4 : ℝ) ^ k = ((4 ^ k : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [hfl1, hfl2] at hk
  have hcountR : (Nat.primeCounting (2 * 4 ^ k) : ℝ) ≤
      Nat.primeCounting (4 ^ k) + ((octavePrimes k).card : ℝ) := by
    exact_mod_cast primeCounting_two_mul_le_add (4 ^ k)
  have hlogk : Real.log ((4 : ℝ) ^ k) = k * Real.log 4 := Real.log_pow 4 k
  -- `2 k log 4 ≤ (4^{1−θ})^k`.
  have hpos : 0 < ((4 : ℝ) ^ (1 - θ)) ^ k := by positivity
  have hkey1 : 2 * Real.log 4 * k ≤ ((4 : ℝ) ^ (1 - θ)) ^ k := by
    rw [pow_one, div_lt_iff₀ hpos] at hkl
    have := mul_lt_mul_of_pos_left hkl (by positivity : (0 : ℝ) < 2 * Real.log 4)
    rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
    exact this.le
  have hsplit : (4 : ℝ) ^ k = ((4 : ℝ) ^ θ) ^ k * ((4 : ℝ) ^ (1 - θ)) ^ k := by
    rw [← mul_pow, ← Real.rpow_add (by norm_num), add_sub_cancel, Real.rpow_one]
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hlogpos : 0 < (k : ℝ) * Real.log 4 := by positivity
  -- `⌊4^{θk}⌋ ≤ (4^θ)^k ≤ 4^k/(2 log 4^k) ≤ #octave`.
  have hsize : (flipSize θ k : ℝ) ≤ (2 - 1) / 2 * ((4 : ℝ) ^ k / Real.log ((4 : ℝ) ^ k)) := by
    refine (flipSize_le k).trans ?_
    rw [hlogk, show (2 - 1 : ℝ) / 2 * ((4 : ℝ) ^ k / (k * Real.log 4)) =
      (4 : ℝ) ^ k / (2 * Real.log 4 * k) by ring, le_div_iff₀ (by positivity), hsplit]
    exact mul_le_mul_of_nonneg_left hkey1 (by positivity)
  have : (flipSize θ k : ℝ) ≤ ((octavePrimes k).card : ℝ) := by linarith
  exact_mod_cast this

/-- A full block forces the charge at `2·4^k`: `#F_k ≤ T_θ(2·4^k)`. -/
theorem card_flipBlock_le_flipCharge (θ : ℝ) (k : ℕ) :
    ((flipBlock θ k).card : ℝ) ≤ flipCharge θ (2 * 4 ^ k) := by
  have hsub : flipBlock θ k ⊆ Ioc 0 (2 * 4 ^ k) := fun p hp => by
    obtain ⟨hp, -, hp2⟩ := mem_flipBlock hp
    exact mem_Ioc.mpr ⟨hp.pos, hp2⟩
  have hlog2 := Real.log_two_gt_d9
  calc ((flipBlock θ k).card : ℝ) = ∑ _p ∈ flipBlock θ k, (1 : ℝ) := by simp
    _ ≤ ∑ p ∈ flipBlock θ k, Λ p * (1 - (twist (flipPoint θ) p).re) := sum_le_sum fun p hp => by
        obtain ⟨hpr, -, -⟩ := mem_flipBlock hp
        rw [twist_flipPoint_of_mem hpr ⟨k, hp⟩, ArithmeticFunction.vonMangoldt_apply_prime hpr]
        have : Real.log 2 ≤ Real.log p :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hpr.two_le)
        norm_num
        linarith
    _ ≤ flipCharge θ (2 * 4 ^ k) :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => flipCharge_term_nonneg θ n

/-- **Below `θ` the pole does not transmit the power law**: `0` and `x_θ` cannot both satisfy the
pole-subtracted power law of an exponent `a < θ`. -/
theorem not_poleSubtractedPowerLaw_flipPoint {θ a : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (ha : a < θ)
    (h0 : PoleSubtractedPowerLaw 0 a) : ¬ PoleSubtractedPowerLaw (flipPoint θ) a := by
  intro hx
  set a' := max a 0
  have ha' : a' < θ := max_lt ha hθ
  have ha'0 : 0 ≤ a' := le_max_right a 0
  obtain ⟨C₀, hC₀, h0b⟩ := h0.mono (le_max_left a 0)
  obtain ⟨C₁, hC₁, hxb⟩ := hx.mono (le_max_left a 0)
  -- The charge is a difference of two pole-subtracted sums.
  have hT : ∀ N : ℕ, flipCharge θ N ≤ (C₀ + C₁) * ((N : ℝ) + 1) ^ a' := by
    intro N
    have he : (flipCharge θ N : ℂ) =
        (twistedPsi N 0 - N) - (twistedPsi N (flipPoint θ) - N) := by
      rw [← twistedPsi_zero_sub_flipPoint]; ring
    have hn : ‖(flipCharge θ N : ℂ)‖ ≤ C₀ * ((N : ℝ) + 1) ^ a' + C₁ * ((N : ℝ) + 1) ^ a' := by
      rw [he]; exact (norm_sub_le _ _).trans (add_le_add (h0b N) (hxb N))
    rw [Complex.norm_real, Real.norm_eq_abs] at hn
    linarith [le_abs_self (flipCharge θ N)]
  set D := (C₀ + C₁) * 3 ^ a'
  have hgrow := tendsto_pow_atTop_atTop_of_one_lt
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 4) (sub_pos.mpr ha'))
  obtain ⟨k, hk1, hk2⟩ :=
    ((eventually_card_flipBlock hθ1).and (hgrow.eventually_gt_atTop (1 + D))).exists
  have hlow := card_flipBlock_le_flipCharge θ k
  rw [hk1] at hlow
  have hfloor : (4 : ℝ) ^ (θ * k) < flipSize θ k + 1 := Nat.lt_floor_add_one _
  have hN : ((2 * 4 ^ k : ℕ) : ℝ) + 1 ≤ 3 * (4 : ℝ) ^ k := by
    push_cast
    linarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) (n := k)]
  have h4pow : ((4 : ℝ) ^ k) ^ a' = ((4 : ℝ) ^ a') ^ k := by
    rw [← Real.rpow_natCast (4 : ℝ) k, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast ((4 : ℝ) ^ a') k, ← Real.rpow_mul (by norm_num), mul_comm]
  have hpow : (((2 * 4 ^ k : ℕ) : ℝ) + 1) ^ a' ≤ 3 ^ a' * ((4 : ℝ) ^ a') ^ k := by
    calc _ ≤ (3 * (4 : ℝ) ^ k) ^ a' := Real.rpow_le_rpow (by positivity) hN ha'0
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity), h4pow]
  have hθk : (4 : ℝ) ^ (θ * k) = ((4 : ℝ) ^ (θ - a')) ^ k * ((4 : ℝ) ^ a') ^ k := by
    rw [← mul_pow, ← Real.rpow_add (by norm_num), sub_add_cancel, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  have hv : 1 ≤ ((4 : ℝ) ^ a') ^ k := one_le_pow₀ (Real.one_le_rpow (by norm_num) ha'0)
  have hup : flipCharge θ (2 * 4 ^ k) ≤ D * ((4 : ℝ) ^ a') ^ k := by
    calc _ ≤ (C₀ + C₁) * (((2 * 4 ^ k : ℕ) : ℝ) + 1) ^ a' := hT _
      _ ≤ (C₀ + C₁) * (3 ^ a' * ((4 : ℝ) ^ a') ^ k) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = D * ((4 : ℝ) ^ a') ^ k := by simp only [D]; ring
  have hmul : (1 + D) * ((4 : ℝ) ^ a') ^ k ≤ ((4 : ℝ) ^ (θ - a')) ^ k * ((4 : ℝ) ^ a') ^ k :=
    mul_le_mul_of_nonneg_right hk2.le (by positivity)
  have hD : 0 ≤ D := by positivity
  nlinarith

/-- **Above `θ` the pole transmits the power law**: the law of exponent `b > θ` passes from `0` to
`x_θ`. -/
theorem poleSubtractedPowerLaw_flipPoint {θ b : ℝ} (hθ : 0 < θ) (hb : θ < b)
    (h0 : PoleSubtractedPowerLaw 0 b) : PoleSubtractedPowerLaw (flipPoint θ) b := by
  obtain ⟨C₀, hC₀, h0b⟩ := h0
  obtain ⟨C₁, hC₁, h1b⟩ := sharesPoleUpTo_flipPoint hθ hb
  refine ⟨C₀ + C₁, by positivity, fun N => ?_⟩
  calc ‖twistedPsi N (flipPoint θ) - N‖ =
        ‖(twistedPsi N 0 - N) + (twistedPsi N (flipPoint θ) - twistedPsi N 0)‖ := by ring_nf
    _ ≤ C₀ * ((N : ℝ) + 1) ^ b + C₁ * ((N : ℝ) + 1) ^ b :=
        (norm_add_le _ _).trans (add_le_add (h0b N) (h1b N))
    _ = _ := by ring

/-- Under RH the trivial point satisfies every pole-subtracted power law above `1/2`. -/
theorem poleSubtractedPowerLaw_zero_of_riemannHypothesis (hRH : RiemannHypothesis) {b : ℝ}
    (hb : 1 / 2 < b) : PoleSubtractedPowerLaw 0 b := by
  obtain ⟨C, hC, hbd⟩ := RHTower.Sieve.exists_chebyshev_error_power_bound hRH
    (sub_pos.mpr hb)
  refine ⟨C, hC.le, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa [twistedPsi] using hC.le
  have hI : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  have h := hbd N hN
  rw [show (1 / 2 : ℝ) + (b - 1 / 2) = b by ring, hI] at h
  have he : twistedPsi N 0 - N = (((∑ n ∈ Ioc 0 N, (Λ n : ℝ)) - N : ℝ) : ℂ) := by
    rw [twistedPsi]
    push_cast
    exact congrArg (· - (N : ℂ)) (sum_congr rfl fun n _ => by rw [twist_zero, mul_one])
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) (by linarith)) hC.le)

/-- **Under RH the flip point has pole-subtracted exponent exactly `θ`**: for `1/2 < θ < 1` it
violates every law of exponent below `θ` and satisfies every law above `θ`, while sharing the pole
of `0`. -/
theorem riemannHypothesis_flipPoint_exponent (hRH : RiemannHypothesis) {θ : ℝ}
    (hθ : 1 / 2 < θ) (hθ1 : θ < 1) :
    (∀ a < θ, ¬ PoleSubtractedPowerLaw (flipPoint θ) a) ∧
      (∀ b, θ < b → PoleSubtractedPowerLaw (flipPoint θ) b) := by
  have hθ0 : 0 < θ := by linarith
  refine ⟨fun a ha => ?_, fun b hb =>
    poleSubtractedPowerLaw_flipPoint hθ0 hb
      (poleSubtractedPowerLaw_zero_of_riemannHypothesis hRH (by linarith))⟩
  intro hx
  -- Raise `a` above `1/2`, where the trivial point satisfies the law.
  set a' := max a ((1 / 2 + θ) / 2)
  have ha' : a' < θ := max_lt ha (by linarith)
  exact not_poleSubtractedPowerLaw_flipPoint hθ0 hθ1 ha'
    (poleSubtractedPowerLaw_zero_of_riemannHypothesis hRH
      (lt_of_lt_of_le (by linarith) (le_max_right _ _)))
    (hx.mono (le_max_left _ _))

/-! ### The exponent spectrum -/

/-- **The pole-subtracted exponent** of `y`: the least `a ≥ 0` with `‖ψ_y(N) − N‖ ≪ (N+1)^a`. -/
def poleSubtractedExponent (y : GaugeTorus) : ℝ :=
  sInf {a | 0 ≤ a ∧ PoleSubtractedPowerLaw y a}

/-- Chebyshev's bound: the trivial point satisfies the law of exponent `1`. -/
theorem poleSubtractedPowerLaw_zero_one : PoleSubtractedPowerLaw 0 1 := by
  refine ⟨Real.log 4 + 5, by positivity, fun N => ?_⟩
  rw [twistedPsi_zero, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Real.rpow_one]
  have h1 := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) N)
  have h2 := Chebyshev.psi_nonneg (N : ℝ)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [abs_le]
  constructor <;> nlinarith

/-- Laws above the exponent of `0` hold at `0`. -/
theorem poleSubtractedPowerLaw_zero_of_lt {b : ℝ} (hb : poleSubtractedExponent 0 < b) :
    PoleSubtractedPowerLaw 0 b := by
  obtain ⟨a, ⟨-, hla⟩, hab⟩ :=
    exists_lt_of_csInf_lt (s := {a | 0 ≤ a ∧ PoleSubtractedPowerLaw 0 a})
      ⟨1, zero_le_one, poleSubtractedPowerLaw_zero_one⟩ hb
  exact hla.mono hab.le

/-- **Every value in `(Θ_ψ, 1)` is attained**: for `θ` between the exponent of `0` and `1`, the flip
point `x_θ` has pole-subtracted exponent exactly `θ`. -/
theorem poleSubtractedExponent_flipPoint {θ : ℝ} (hθ : poleSubtractedExponent 0 < θ)
    (hθ1 : θ < 1) : poleSubtractedExponent (flipPoint θ) = θ := by
  have hE0 : 0 ≤ poleSubtractedExponent 0 :=
    le_csInf ⟨1, zero_le_one, poleSubtractedPowerLaw_zero_one⟩ fun a ha => ha.1
  have hθ0 : 0 < θ := hE0.trans_lt hθ
  have hbdd : BddBelow {a | 0 ≤ a ∧ PoleSubtractedPowerLaw (flipPoint θ) a} :=
    ⟨0, fun a ha => ha.1⟩
  apply le_antisymm
  · refine le_of_forall_gt fun b hb => ?_
    obtain ⟨c, hθc, hcb⟩ := exists_between hb
    have hc := poleSubtractedPowerLaw_flipPoint hθ0 hθc
      (poleSubtractedPowerLaw_zero_of_lt (hθ.trans hθc))
    exact (csInf_le hbdd ⟨hθ0.le.trans hθc.le, hc⟩).trans_lt hcb
  · refine le_csInf ⟨1, zero_le_one,
      poleSubtractedPowerLaw_flipPoint hθ0 hθ1 poleSubtractedPowerLaw_zero_one⟩ ?_
    rintro a ⟨-, hla⟩
    by_contra hlt
    push Not at hlt
    -- Raise `a` above the exponent of `0`, keeping it below `θ`.
    set a' := max a ((poleSubtractedExponent 0 + θ) / 2)
    have ha' : a' < θ := max_lt hlt (by linarith)
    exact not_poleSubtractedPowerLaw_flipPoint hθ0 hθ1 ha'
      (poleSubtractedPowerLaw_zero_of_lt (lt_of_lt_of_le (by linarith) (le_max_right _ _)))
      (hla.mono (le_max_left _ _))

/-- **Under RH the spectrum contains `(1/2, 1)`**, each value attained by a point carrying the pole
of `0`. -/
theorem riemannHypothesis_poleSubtractedExponent_spectrum (hRH : RiemannHypothesis) {θ : ℝ}
    (hθ : 1 / 2 < θ) (hθ1 : θ < 1) :
    poleSubtractedExponent (flipPoint θ) = θ ∧ SharesPoleUpTo (flipPoint θ) ((θ + 1) / 2) := by
  have hE : poleSubtractedExponent 0 ≤ 1 / 2 := by
    refine le_of_forall_gt fun b hb => ?_
    obtain ⟨c, hc, hcb⟩ := exists_between hb
    exact (csInf_le (s := {a | 0 ≤ a ∧ PoleSubtractedPowerLaw 0 a}) ⟨0, fun a ha => ha.1⟩
      ⟨by linarith, poleSubtractedPowerLaw_zero_of_riemannHypothesis hRH hc⟩).trans_lt hcb
  exact ⟨poleSubtractedExponent_flipPoint (hE.trans_lt hθ) hθ1,
    sharesPoleUpTo_flipPoint (by linarith) (by linarith)⟩

/-! ### The answer -/

/-- **The pole does not decide the power law.** For `0 < b < 1` and every `a < b` some gauge point
carries the pole of the trivial point up to precision `(N+1)^b` and violates the pole-subtracted
power law of exponent `a`: it is the trivial point itself, or a flip point `x_θ` with
`max(a, 0) < θ < b`. -/
theorem pole_does_not_decide_powerLaw {a b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hab : a < b) :
    ∃ y : GaugeTorus, SharesPoleUpTo y b ∧ ¬ PoleSubtractedPowerLaw y a := by
  by_cases h0 : PoleSubtractedPowerLaw 0 a
  · have hm : max a 0 < b := max_lt hab hb0
    set θ := (max a 0 + b) / 2
    have hθ0 : 0 < θ := by have := le_max_right a 0; simp only [θ]; linarith
    have hθb : θ < b := by simp only [θ]; linarith
    have haθ : a < θ := by have := le_max_left a 0; simp only [θ]; linarith
    exact ⟨flipPoint θ, sharesPoleUpTo_flipPoint hθ0 hθb,
      not_poleSubtractedPowerLaw_flipPoint hθ0 (hθb.trans hb1) haθ h0⟩
  · exact ⟨0, ⟨0, le_rfl, fun N => by simp⟩, h0⟩

/-- **No property of the pole implies the half-power law.** If a property `P` of gauge points holds
at every point carrying the pole of `0` up to `(N+1)^b` (`0 < b < 1`), then `P` does not imply the
pole-subtracted power law of any exponent `a < b`; for `b > 1/2` this includes the half-power law. -/
theorem no_pole_property_implies_powerLaw {a b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hab : a < b)
    (P : GaugeTorus → Prop) (hP : ∀ y, SharesPoleUpTo y b → P y) :
    ¬ ∀ y, P y → PoleSubtractedPowerLaw y a := by
  intro h
  obtain ⟨y, hy, hny⟩ := pole_does_not_decide_powerLaw hb0 hb1 hab
  exact hny (h y (hP y hy))

end GaloisForLFunctions.ArithmeticGaugeTheory
