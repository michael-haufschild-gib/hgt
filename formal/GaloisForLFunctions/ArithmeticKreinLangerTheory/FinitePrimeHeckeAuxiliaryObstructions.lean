import GaloisForLFunctions.ArithmeticKreinLangerTheory.IntegralityProducesLinearCounts
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.WherePrecisionIsLost
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite-prime and parity-blind obstructions for Hecke–factorial auxiliaries

Multivariate polynomials `Q ∈ ℤ[X_p : p prime]` in the commuting prime dilation operators act on
factorial towers via `n ↦ ∏_{k ≥ 1} (⌊n / k⌋!)^{c(k)}`, where `k = ∏ p^{e_p}` corresponds
bijectively to the monomial `∏ X_p^{e_p}` (`stencilToMvPoly_mvPolyToStencil`,
`mvPolyToStencil_stencilToMvPoly`). Writing `stepWeight c m = ∑_k c(k) ⌊m / k⌋` and
`stencilSlope c = -∑_k c(k) (log k) / k`:

* **Exact integrality (`forall_stencilDen_dvd_stencilNum_iff`).** The denominator divides the
  numerator for every `n` if and only if `0 ≤ stepWeight c m` for every `m ≥ 1`.
* **Vanishing-order upper producer (`psi_le_of_stepWeight_producer`).** If `c` is balanced
  (`∑ c(k) / k = 0`), `stepWeight c ≥ 0` everywhere, and `stepWeight c r ≥ m ≥ 1` for
  `1 ≤ r < B` (`B ≥ 2`), then every prime `p ∈ (n/B, n]` divides the integer auxiliary `A_n` to
  order at least `m` (`pow_dvd_stencilInt_of_prime_mem_Ioc`), `sum_mul_log_le_log_of_dvd` bounds
  `θ(n) - θ(⌊n/B⌋)`, and `B`-adic telescoping gives
  `ψ(x) ≤ (stencilSlope c / (m (1 - 1/B))) x + C (log x)²`.
* **Pronic slope series (`hasSum_stepWeight_div_pronic`).** For balanced `c`,
  `stencilSlope c = ∑'_{r ≥ 1} stepWeight c r / (r (r + 1))`.
* **Single-prime Hecke ceiling (`single_prime_hecke_slope_ge_two_log_two`).** Any balanced integer
  auxiliary supported on powers of a single prime `p₀` has normalized vanishing-order slope at
  least `(p₀ log p₀) / (p₀ - 1) ≥ 2 log 2`.
* **Two-prime `{2, 3}` breakthrough (`psi_le_of_twoThreeStencil`).** The `{2, 3}`-supported stencil
  `1 - X_2 - X_3 - X_2² + X_2² X_3` reaches normalized slope `(10/9) log 2 + (1/3) log 3 < 23/20 < 2 log 2`.
* **Universal finite-prime coprime jump obstruction (`finite_prime_alphabet_slope_gt_one`).** For
  any finite set `S` of primes (`P_S = ∏_{p ∈ S} p`), every `S`-supported integer producer has
  `stepWeight c q - stepWeight c (q - 1) = stepWeight c 1` at integers coprime to `P_S`, forcing
  normalized slope strictly above `1 + 1 / ((P_S + 1)(P_S + 2)) > 1`.
* **Parity-blind multinomial obstruction (`non_alternating_stencil_slope_gt`).** Even across
  infinitely many primes and arbitrary `B`, any balanced auxiliary with `c(k) ≤ 0` for all `k ≥ 2`
  (no positive parity-cancellation terms on `k ≥ 2`) has normalized slope strictly above
  `31 / 30 > 1` via the Sylvester `(1, 2, 6)` dual weights (`504^5 > e^{31}`).
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticOfSquareRootPrecision (chebyshevTransform
  chebyshevTransform_vonMangoldt vonMangoldtWeight log_factorial_sub_bounds)

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-! ### Prime-dilation multivariate polynomials and integer stencils -/

/-- Index type of prime Hecke/dilation variables `X_p`. -/
abbrev PrimeVar : Type := {p : ℕ // p.Prime}

/-- Positive integer `∏ p^{e_p}` associated to a monomial in `{X_p : p prime}`. -/
def heckeDivisor (s : PrimeVar →₀ ℕ) : ℕ :=
  s.prod fun p e => p.1 ^ e

theorem heckeDivisor_pos (s : PrimeVar →₀ ℕ) : 0 < heckeDivisor s := by
  rw [heckeDivisor, Finsupp.prod]
  exact prod_pos fun p _ => pow_pos p.2.pos _

theorem factorization_heckeDivisor (s : PrimeVar →₀ ℕ) (p : PrimeVar) :
    (heckeDivisor s).factorization p.1 = s p := by
  classical
  rw [heckeDivisor, Finsupp.prod,
    Nat.factorization_prod fun q _ => (pow_pos q.2.pos _).ne',
    Finsupp.finsetSum_apply]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p ∈ s.support
  · rw [sum_eq_single p]
    · rw [p.2.factorization_self, mul_one]
    · intro q _ hqp
      have hne : q.1 ≠ p.1 := fun h => hqp (Subtype.ext h)
      rw [Nat.factorization_eq_zero_of_not_dvd
        (fun hd => hne ((Nat.prime_dvd_prime_iff_eq p.2 q.2).mp hd).symm), mul_zero]
    · intro h; exact absurd hp h
  · rw [Finsupp.notMem_support_iff.mp hp, sum_eq_zero]
    intro q hq
    have hqp : q ≠ p := fun h => hp (h ▸ hq)
    have hne : q.1 ≠ p.1 := fun h => hqp (Subtype.ext h)
    rw [Nat.factorization_eq_zero_of_not_dvd
      (fun hd => hne ((Nat.prime_dvd_prime_iff_eq p.2 q.2).mp hd).symm), mul_zero]

theorem heckeDivisor_injective : Function.Injective heckeDivisor := by
  intro s₁ s₂ h
  ext p
  rw [← factorization_heckeDivisor s₁ p, ← factorization_heckeDivisor s₂ p, h]

/-- Prime-exponent monomial attached to a positive integer `k`. -/
def divisorMonomial (k : ℕ) : PrimeVar →₀ ℕ :=
  k.primeFactors.attach.sum fun p =>
    Finsupp.single ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ (k.factorization p.1)

theorem divisorMonomial_apply (k : ℕ) (q : PrimeVar) :
    divisorMonomial k q = k.factorization q.1 := by
  classical
  rw [divisorMonomial, Finsupp.finsetSum_apply]
  by_cases hq : q.1 ∈ k.primeFactors
  · rw [sum_eq_single ⟨q.1, hq⟩]
    · simp
    · intro p _ hpq
      have hne : q ≠ ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ := fun h => by
        have hv : p.1 = q.1 := (congrArg Subtype.val h).symm
        exact hpq (Subtype.ext hv)
      exact Finsupp.single_eq_of_ne hne
    · intro h; exact absurd (mem_attach _ _) h
  · rw [sum_eq_zero]
    · have hq' : q.1 ∉ k.factorization.support := by rwa [Nat.support_factorization]
      exact (Finsupp.notMem_support_iff.mp hq').symm
    · intro p _
      have hne : q ≠ ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ := fun h =>
        hq (congrArg Subtype.val h ▸ p.2)
      exact Finsupp.single_eq_of_ne hne

theorem heckeDivisor_divisorMonomial {k : ℕ} (hk : 0 < k) :
    heckeDivisor (divisorMonomial k) = k := by
  apply Nat.eq_of_factorization_eq (heckeDivisor_pos _).ne' hk.ne'
  intro p
  by_cases hp : p.Prime
  · exact (factorization_heckeDivisor (divisorMonomial k) ⟨p, hp⟩).trans
      (divisorMonomial_apply k ⟨p, hp⟩)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem divisorMonomial_heckeDivisor (s : PrimeVar →₀ ℕ) :
    divisorMonomial (heckeDivisor s) = s := by
  ext p
  rw [divisorMonomial_apply, factorization_heckeDivisor]

/-- Stencil `c : ℕ →₀ ℤ` (`c 0 = 0`) associated to `Q ∈ ℤ[X_p : p prime]`. -/
def mvPolyToStencil (Q : MvPolynomial PrimeVar ℤ) : ℕ →₀ ℤ :=
  Q.support.sum fun s => Finsupp.single (heckeDivisor s) (Q.coeff s)

/-- Multivariate prime-Hecke polynomial associated to a stencil `c : ℕ →₀ ℤ`. -/
def stencilToMvPoly (c : ℕ →₀ ℤ) : MvPolynomial PrimeVar ℤ :=
  c.support.sum fun k => if k = 0 then 0 else MvPolynomial.monomial (divisorMonomial k) (c k)

theorem mvPolyToStencil_zero_apply (Q : MvPolynomial PrimeVar ℤ) :
    mvPolyToStencil Q 0 = 0 := by
  rw [mvPolyToStencil, Finsupp.finsetSum_apply, sum_eq_zero]
  intro s _
  exact Finsupp.single_eq_of_ne (heckeDivisor_pos s).ne

theorem mvPolyToStencil_apply_heckeDivisor (Q : MvPolynomial PrimeVar ℤ) (s : PrimeVar →₀ ℕ) :
    mvPolyToStencil Q (heckeDivisor s) = Q.coeff s := by
  classical
  rw [mvPolyToStencil, Finsupp.finsetSum_apply]
  by_cases hs : s ∈ Q.support
  · rw [sum_eq_single s]
    · simp
    · intro t _ hts
      exact Finsupp.single_eq_of_ne (fun h => hts (heckeDivisor_injective h.symm))
    · intro h; exact absurd hs h
  · rw [sum_eq_zero]
    · exact (MvPolynomial.notMem_support_iff.mp hs).symm
    · intro t ht
      have hts : t ≠ s := fun h => hs (h ▸ ht)
      exact Finsupp.single_eq_of_ne (fun h => hts (heckeDivisor_injective h.symm))

theorem stencilToMvPoly_mvPolyToStencil (Q : MvPolynomial PrimeVar ℤ) :
    stencilToMvPoly (mvPolyToStencil Q) = Q := by
  classical
  ext s
  rw [stencilToMvPoly, MvPolynomial.coeff_sum]
  set k := heckeDivisor s
  have hk0 : k ≠ 0 := (heckeDivisor_pos s).ne'
  by_cases hk : k ∈ (mvPolyToStencil Q).support
  · rw [sum_eq_single k]
    · rw [if_neg hk0, MvPolynomial.coeff_monomial, if_pos (divisorMonomial_heckeDivisor s),
        mvPolyToStencil_apply_heckeDivisor]
    · intro m hm hmk
      by_cases hm0 : m = 0
      · simp [hm0]
      · rw [if_neg hm0, MvPolynomial.coeff_monomial, if_neg]
        intro hd
        apply hmk
        rw [← heckeDivisor_divisorMonomial (Nat.pos_of_ne_zero hm0), hd]
    · intro h; exact absurd hk h
  · rw [sum_eq_zero]
    · have hz : mvPolyToStencil Q k = 0 := Finsupp.notMem_support_iff.mp hk
      rw [mvPolyToStencil_apply_heckeDivisor] at hz
      exact hz.symm
    · intro m hm
      by_cases hm0 : m = 0
      · simp [hm0]
      · rw [if_neg hm0, MvPolynomial.coeff_monomial, if_neg]
        intro hd
        apply hk
        have heq : m = k := by
          rw [← heckeDivisor_divisorMonomial (Nat.pos_of_ne_zero hm0), hd]
        exact heq ▸ hm

theorem mvPolyToStencil_stencilToMvPoly {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) :
    mvPolyToStencil (stencilToMvPoly c) = c := by
  classical
  ext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [mvPolyToStencil_zero_apply, hc0]
  · rw [ ← heckeDivisor_divisorMonomial hk, mvPolyToStencil_apply_heckeDivisor,
      heckeDivisor_divisorMonomial hk, stencilToMvPoly, MvPolynomial.coeff_sum]
    by_cases hks : k ∈ c.support
    · rw [sum_eq_single k]
      · rw [if_neg hk.ne', MvPolynomial.coeff_monomial, if_pos rfl]
      · intro m hm hmk
        by_cases hm0 : m = 0
        · simp [hm0]
        · rw [if_neg hm0, MvPolynomial.coeff_monomial, if_neg]
          intro hd
          apply hmk
          have := congrArg heckeDivisor hd
          rwa [heckeDivisor_divisorMonomial (Nat.pos_of_ne_zero hm0),
            heckeDivisor_divisorMonomial hk] at this
      · intro h; exact absurd hks h
    · rw [sum_eq_zero]
      · exact (Finsupp.notMem_support_iff.mp hks).symm
      · intro m hm
        by_cases hm0 : m = 0
        · simp [hm0]
        · rw [if_neg hm0, MvPolynomial.coeff_monomial, if_neg]
          intro hd
          apply hks
          have heq : m = k := by
            have := congrArg heckeDivisor hd
            rwa [heckeDivisor_divisorMonomial (Nat.pos_of_ne_zero hm0),
              heckeDivisor_divisorMonomial hk] at this
          exact heq ▸ hm

/-! ### Step weights, factorial ratios, and exact `p`-adic integrality -/

/-- Stirling cancellation condition `∑_{k} c(k) / k = 0` killing the `n log n - n` superlinear term. -/
def IsBalanced (c : ℕ →₀ ℤ) : Prop :=
  ∑ k ∈ c.support, (c k : ℝ) / k = 0

/-- Integer step weight `g_c(m) = ∑_k c(k) ⌊m / k⌋`. -/
def stepWeight (c : ℕ →₀ ℤ) (m : ℕ) : ℤ :=
  ∑ k ∈ c.support, c k * (m / k : ℕ)

/-- Exponential growth slope `stencilSlope(c) = -∑_k c(k) (log k) / k`. -/
def stencilSlope (c : ℕ →₀ ℤ) : ℝ :=
  ∑ k ∈ c.support, -(c k : ℝ) * Real.log k / k

/-- Positive factorial numerator `∏_{c(k) > 0} (⌊n / k⌋!)^{c(k)}`. -/
def stencilNum (c : ℕ →₀ ℤ) (n : ℕ) : ℕ :=
  ∏ k ∈ c.support, if 0 < c k then ((n / k).factorial) ^ (c k).toNat else 1

/-- Positive factorial denominator `∏_{c(k) < 0} (⌊n / k⌋!)^{-c(k)}`. -/
def stencilDen (c : ℕ →₀ ℤ) (n : ℕ) : ℕ :=
  ∏ k ∈ c.support, if c k < 0 then ((n / k).factorial) ^ (-c k).toNat else 1

/-- Integer quotient `stencilNum c n / stencilDen c n` (exact when `stencilDen c n ∣ stencilNum c n`). -/
def stencilInt (c : ℕ →₀ ℤ) (n : ℕ) : ℕ :=
  stencilNum c n / stencilDen c n

@[simp] theorem stepWeight_zero (c : ℕ →₀ ℤ) : stepWeight c 0 = 0 := by
  simp [stepWeight]

theorem stepWeight_one {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) : stepWeight c 1 = c 1 := by
  classical
  rw [stepWeight]
  by_cases h1 : 1 ∈ c.support
  · rw [sum_eq_single 1]
    · simp
    · intro k hk hk1
      have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
      have hk2 : 1 < k := by omega
      simp [Nat.div_eq_of_lt hk2]
    · intro h; exact absurd h1 h
  · rw [Finsupp.notMem_support_iff.mp h1, sum_eq_zero]
    intro k hk
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hk1 : k ≠ 1 := fun h => h1 (h ▸ hk)
    have hk2 : 1 < k := by omega
    simp [Nat.div_eq_of_lt hk2]

theorem stencilNum_pos (c : ℕ →₀ ℤ) (n : ℕ) : 0 < stencilNum c n := by
  rw [stencilNum]
  refine prod_pos fun k _ => ?_
  split_ifs
  · exact pow_pos (Nat.factorial_pos _) _
  · exact zero_lt_one

theorem stencilDen_pos (c : ℕ →₀ ℤ) (n : ℕ) : 0 < stencilDen c n := by
  rw [stencilDen]
  refine prod_pos fun k _ => ?_
  split_ifs
  · exact pow_pos (Nat.factorial_pos _) _
  · exact zero_lt_one

private lemma nat_log_lt_succ (p m n : ℕ) (hmn : m ≤ n) : Nat.log p m < n + 1 := by
  rcases le_or_gt p 1 with hp | hp
  · rw [Nat.log_of_left_le_one hp]; omega
  · exact ((Nat.log_mono_right hmn).trans (Nat.log_le_self p n)).trans_lt (Nat.lt_succ_self n)

/-- **Legendre valuation identity for Hecke–factorial stencils.** -/
theorem factorization_stencilNum_sub_stencilDen (c : ℕ →₀ ℤ) (n : ℕ) {p : ℕ} (hp : p.Prime) :
    ((stencilNum c n).factorization p : ℤ) - ((stencilDen c n).factorization p : ℤ) =
      ∑ i ∈ Ico 1 (n + 1), stepWeight c (n / p ^ i) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnum_fac : (stencilNum c n).factorization p =
      ∑ k ∈ c.support, (if 0 < c k then (c k).toNat else 0) * padicValNat p ((n / k).factorial) := by
    rw [stencilNum, Nat.factorization_prod fun k _ => by
      split_ifs
      · exact (pow_pos (Nat.factorial_pos _) _).ne'
      · exact one_ne_zero, Finsupp.finsetSum_apply]
    refine sum_congr rfl fun k _ => ?_
    split_ifs with hck
    · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.factorization_def _ hp]
    · simp
  have hden_fac : (stencilDen c n).factorization p =
      ∑ k ∈ c.support, (if c k < 0 then (-c k).toNat else 0) * padicValNat p ((n / k).factorial) := by
    rw [stencilDen, Nat.factorization_prod fun k _ => by
      split_ifs
      · exact (pow_pos (Nat.factorial_pos _) _).ne'
      · exact one_ne_zero, Finsupp.finsetSum_apply]
    refine sum_congr rfl fun k _ => ?_
    split_ifs with hck
    · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.factorization_def _ hp]
    · simp
  rw [hnum_fac, hden_fac, Nat.cast_sum, Nat.cast_sum, ← sum_sub_distrib]
  have hcoef : ∀ k ∈ c.support,
      ((((if 0 < c k then (c k).toNat else 0) * padicValNat p ((n / k).factorial) : ℕ) : ℤ) -
        (((if c k < 0 then (-c k).toNat else 0) * padicValNat p ((n / k).factorial) : ℕ) : ℤ)) =
      ∑ i ∈ Ico 1 (n + 1), c k * (((n / p ^ i) / k : ℕ) : ℤ) := by
    intro k _
    have hlog : Nat.log p (n / k) < n + 1 := nat_log_lt_succ p (n / k) n (Nat.div_le_self n k)
    rw [padicValNat_factorial hlog]
    have hsum_eq : ∑ i ∈ Ico 1 (n + 1), (n / k) / p ^ i = ∑ i ∈ Ico 1 (n + 1), (n / p ^ i) / k :=
      sum_congr rfl fun i _ => by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm k]
    rw [hsum_eq]
    have hck_split : (((if 0 < c k then (c k).toNat else 0 : ℕ) : ℤ) -
        ((if c k < 0 then (-c k).toNat else 0 : ℕ) : ℤ)) = c k := by
      rcases lt_trichotomy 0 (c k) with hpos | hzero | hneg
      · rw [if_pos hpos, if_neg (by omega)]; omega
      · rw [← hzero]; simp
      · rw [if_neg (by omega), if_pos hneg]; omega
    rw [Nat.cast_mul, Nat.cast_mul, ← sub_mul, hck_split, Nat.cast_sum, mul_sum]
  rw [sum_congr rfl hcoef, sum_comm]
  rfl

/-- **Exact integrality characterization.** `stencilDen c n ∣ stencilNum c n` holds for all `n`
if and only if `0 ≤ stepWeight c m` for every `m ≥ 1`. -/
theorem forall_stencilDen_dvd_stencilNum_iff {c : ℕ →₀ ℤ} :
    (∀ n : ℕ, stencilDen c n ∣ stencilNum c n) ↔ ∀ m : ℕ, 1 ≤ m → 0 ≤ stepWeight c m := by
  constructor
  · intro hdvd m hm
    by_contra! hneg
    obtain ⟨p, hpm, hp⟩ := Nat.exists_infinite_primes (m + 1)
    have hle := (Nat.factorization_le_iff_dvd (stencilDen_pos c (p * m)).ne'
      (stencilNum_pos c (p * m)).ne').mpr (hdvd (p * m)) p
    have hval := factorization_stencilNum_sub_stencilDen c (p * m) hp
    have hnonneg : (0 : ℤ) ≤ ((stencilNum c (p * m)).factorization p : ℤ) -
        ((stencilDen c (p * m)).factorization p : ℤ) := by omega
    rw [hval] at hnonneg
    have hp_pos : 0 < p := hp.pos
    have hpm_ge : 1 ≤ p * m := Nat.mul_pos hp_pos hm
    have hsum : ∑ i ∈ Ico 1 (p * m + 1), stepWeight c ((p * m) / p ^ i) = stepWeight c m := by
      rw [sum_eq_single 1]
      · simp [Nat.mul_div_right m hp_pos]
      · intro i hi hi1
        have hi2 : 2 ≤ i := by
          have := (mem_Ico.mp hi).1; omega
        have hgt : p * m < p ^ i := by
          calc p * m < p * p := Nat.mul_lt_mul_of_pos_left (by omega) hp_pos
            _ = p ^ 2 := (sq p).symm
            _ ≤ p ^ i := Nat.pow_le_pow_right hp_pos hi2
        rw [Nat.div_eq_of_lt hgt, stepWeight_zero]
      · intro h; exact absurd (mem_Ico.mpr ⟨le_rfl, by omega⟩) h
    rw [hsum] at hnonneg
    omega
  · intro hstep n
    rw [← Nat.factorization_le_iff_dvd (stencilDen_pos c n).ne' (stencilNum_pos c n).ne']
    intro p
    by_cases hp : p.Prime
    · have hval := factorization_stencilNum_sub_stencilDen c n hp
      have hsum : 0 ≤ ∑ i ∈ Ico 1 (n + 1), stepWeight c (n / p ^ i) := by
        refine sum_nonneg fun i _ => ?_
        rcases Nat.eq_zero_or_pos (n / p ^ i) with hz | hpos
        · rw [hz, stepWeight_zero]
        · exact hstep _ hpos
      omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-! ### Vanishing-order upper producer and Stirling asymptotics -/

theorem stencilDen_dvd_stencilNum_of_nonneg {c : ℕ →₀ ℤ}
    (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r) (n : ℕ) :
    stencilDen c n ∣ stencilNum c n := by
  rw [← Nat.factorization_le_iff_dvd (stencilDen_pos c n).ne' (stencilNum_pos c n).ne']
  intro p
  by_cases hp : p.Prime
  · have hval := factorization_stencilNum_sub_stencilDen c n hp
    have hsum : 0 ≤ ∑ i ∈ Ico 1 (n + 1), stepWeight c (n / p ^ i) :=
      sum_nonneg fun i _ => hstep _
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem stencilInt_pos_of_nonneg {c : ℕ →₀ ℤ} (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r) (n : ℕ) :
    0 < stencilInt c n :=
  Nat.div_pos (Nat.le_of_dvd (stencilNum_pos c n) (stencilDen_dvd_stencilNum_of_nonneg hstep n))
    (stencilDen_pos c n)

/-- **Prime vanishing-order certificate.** Every prime `p ∈ (n / B, n]` divides `stencilInt c n`
to multiplicity at least `m` whenever `stepWeight c ≥ 0` and `stepWeight c ≥ m` on `[1, B)`. -/
theorem pow_dvd_stencilInt_of_prime_mem_Ioc {c : ℕ →₀ ℤ} {m B n p : ℕ}
    (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r)
    (hwin : ∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) (hB : 0 < B)
    (hp : p.Prime) (hpI : p ∈ Ioc (n / B) n) :
    p ^ m ∣ stencilInt c n := by
  have hdvd := stencilDen_dvd_stencilNum_of_nonneg hstep n
  have hne : stencilInt c n ≠ 0 := (stencilInt_pos_of_nonneg hstep n).ne'
  rw [hp.pow_dvd_iff_le_factorization hne, stencilInt, Nat.factorization_div hdvd,
    Finsupp.tsub_apply]
  have hval := factorization_stencilNum_sub_stencilDen c n hp
  obtain ⟨hp1, hp2⟩ := mem_Ioc.mp hpI
  have hnp_ge : 1 ≤ n / p := (Nat.one_le_div_iff hp.pos).mpr hp2
  have hnp_lt : n / p < B := by
    rw [Nat.div_lt_iff_lt_mul hp.pos]
    have hlt := (Nat.div_lt_iff_lt_mul hB).mp hp1
    rwa [mul_comm] at hlt
  have hn_pos : 0 < n := lt_of_lt_of_le hp.pos hp2
  have hn1 : 1 ∈ Ico 1 (n + 1) := mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hsingle : stepWeight c (n / p ^ 1) ≤ ∑ i ∈ Ico 1 (n + 1), stepWeight c (n / p ^ i) :=
    single_le_sum (fun i _ => hstep _) hn1
  rw [pow_one] at hsingle
  have hm_le : (m : ℤ) ≤ stepWeight c (n / p) := hwin (n / p) (mem_Ico.mpr ⟨hnp_ge, hnp_lt⟩)
  have hle_fac := (Nat.factorization_le_iff_dvd (stencilDen_pos c n).ne'
    (stencilNum_pos c n).ne').mpr hdvd p
  omega

/-- **Prime ledger (`sum_mul_log_le_log_of_dvd`).** Vanishing to order `m` on primes in `(n/B, n]`
gives `m (θ(n) - θ(n/B)) ≤ log(stencilInt c n)`. -/
theorem theta_sub_le_log_stencilInt {c : ℕ →₀ ℤ} {m B : ℕ}
    (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r)
    (hwin : ∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) (hB : 0 < B) (n : ℕ) :
    (m : ℝ) * (Chebyshev.theta n - Chebyshev.theta (n / B : ℕ)) ≤
      Real.log (stencilInt c n : ℝ) := by
  have h := sum_mul_log_le_log_of_dvd (stencilInt_pos_of_nonneg hstep n).ne'
    (S := (Ioc (n / B) n).filter Nat.Prime) (fun p hp => (mem_filter.mp hp).2) (fun _ => m)
    fun p hp => pow_dvd_stencilInt_of_prime_mem_Ioc hstep hwin hB
      (mem_filter.mp hp).2 (mem_filter.mp hp).1
  rw [← mul_sum] at h
  have htheta : Chebyshev.theta n - Chebyshev.theta (n / B : ℕ) =
      ∑ p ∈ (Ioc (n / B) n).filter Nat.Prime, Real.log p := by
    rw [Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast, Nat.floor_natCast]
    have hunion : Ioc 0 (n / B) ∪ Ioc (n / B) n = Ioc 0 n :=
      Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (Nat.div_le_self n B)
    have hdisj : Disjoint ((Ioc 0 (n / B)).filter Nat.Prime) ((Ioc (n / B) n).filter Nat.Prime) :=
      Disjoint.mono (filter_subset _ _) (filter_subset _ _) (Ioc_disjoint_Ioc_of_le le_rfl)
    rw [← hunion, filter_union, sum_union hdisj]
    ring
  rwa [htheta]

theorem log_stencilInt_eq_sum {c : ℕ →₀ ℤ} (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r) (n : ℕ) :
    Real.log (stencilInt c n : ℝ) =
      ∑ k ∈ c.support, (c k : ℝ) * Real.log ((n / k).factorial : ℕ) := by
  have hdvd := stencilDen_dvd_stencilNum_of_nonneg hstep n
  have hden_pos : (0 : ℝ) < stencilDen c n := by exact_mod_cast stencilDen_pos c n
  have hnum_pos : (0 : ℝ) < stencilNum c n := by exact_mod_cast stencilNum_pos c n
  have hcast : (stencilInt c n : ℝ) = (stencilNum c n : ℝ) / (stencilDen c n : ℝ) := by
    rw [stencilInt, Nat.cast_div hdvd hden_pos.ne']
  rw [hcast, Real.log_div hnum_pos.ne' hden_pos.ne']
  have hlog_num : Real.log (stencilNum c n : ℝ) =
      ∑ k ∈ c.support, (if 0 < c k then ((c k).toNat : ℝ) else 0) *
        Real.log ((n / k).factorial : ℕ) := by
    rw [stencilNum, Nat.cast_prod, Real.log_prod fun k _ => by
      split_ifs
      · exact_mod_cast (pow_pos (Nat.factorial_pos _) _).ne'
      · norm_num]
    refine sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [Nat.cast_pow, Real.log_pow]
    · simp
  have hlog_den : Real.log (stencilDen c n : ℝ) =
      ∑ k ∈ c.support, (if c k < 0 then ((-c k).toNat : ℝ) else 0) *
        Real.log ((n / k).factorial : ℕ) := by
    rw [stencilDen, Nat.cast_prod, Real.log_prod fun k _ => by
      split_ifs
      · exact_mod_cast (pow_pos (Nat.factorial_pos _) _).ne'
      · norm_num]
    refine sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [Nat.cast_pow, Real.log_pow]
    · simp
  rw [hlog_num, hlog_den, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [← sub_mul]
  congr 1
  rcases lt_trichotomy 0 (c k) with hpos | hzero | hneg
  · rw [if_pos hpos, if_neg (by omega), sub_zero]
    exact_mod_cast Int.toNat_of_nonneg hpos.le
  · rw [← hzero]; simp
  · rw [if_neg (by omega), if_pos hneg, zero_sub]
    have : ((-c k).toNat : ℤ) = -c k := Int.toNat_of_nonneg (by omega)
    have hR : ((-c k).toNat : ℝ) = -(c k : ℝ) := by exact_mod_cast this
    linarith

theorem log_stencilInt_eq_vonMangoldt {c : ℕ →₀ ℤ} (hc0 : c 0 = 0)
    (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r) (n : ℕ) :
    Real.log (stencilInt c n : ℝ) =
      ∑ d ∈ Ioc 0 n, vonMangoldtWeight d * (stepWeight c (n / d) : ℝ) := by
  rw [log_stencilInt_eq_sum hstep n]
  have hterm : ∀ k ∈ c.support, (c k : ℝ) * Real.log ((n / k).factorial : ℕ) =
      ∑ d ∈ Ioc 0 n, vonMangoldtWeight d * ((c k : ℝ) * (((n / d) / k : ℕ) : ℝ)) := by
    intro k hk
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
    rw [← chebyshevTransform_vonMangoldt]
    have hsub : chebyshevTransform vonMangoldtWeight (n / k) =
        ∑ d ∈ Ioc 0 n, vonMangoldtWeight d * (((n / k) / d : ℕ) : ℝ) := by
      refine sum_subset (Ioc_subset_Ioc_right (Nat.div_le_self n k)) fun d hd hdn => ?_
      have hlt : n / k < d := by
        simp only [mem_Ioc, not_and, not_le] at hdn
        exact hdn (mem_Ioc.mp hd).1
      rw [Nat.div_eq_of_lt hlt, Nat.cast_zero, mul_zero]
    rw [hsub, mul_sum]
    refine sum_congr rfl fun d _ => ?_
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm k d]
    ring
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← mul_sum]
  congr 1
  rw [stepWeight, Int.cast_sum]
  exact sum_congr rfl fun k _ => by rw [Int.cast_mul, Int.cast_natCast]

/-- **Prime-power ledger (`ψ`).** Under `stepWeight c ≥ 0` and `stepWeight c ≥ m` on `[1, B)`,
`m (ψ(n) - ψ(n/B)) ≤ log(stencilInt c n)`. -/
theorem psi_sub_le_log_stencilInt {c : ℕ →₀ ℤ} {m B : ℕ} (hc0 : c 0 = 0)
    (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r)
    (hwin : ∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) (hB : 0 < B) (n : ℕ) :
    (m : ℝ) * (Chebyshev.psi n - Chebyshev.psi (n / B : ℕ)) ≤
      Real.log (stencilInt c n : ℝ) := by
  rw [log_stencilInt_eq_vonMangoldt hc0 hstep n, Chebyshev.psi, Chebyshev.psi,
    Nat.floor_natCast, Nat.floor_natCast]
  have hcons := Finset.sum_Ioc_consecutive (f := fun d => ArithmeticFunction.vonMangoldt d)
    (Nat.zero_le (n / B)) (Nat.div_le_self n B)
  have hdiff : (∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d) -
      (∑ d ∈ Ioc 0 (n / B), ArithmeticFunction.vonMangoldt d) =
      ∑ d ∈ Ioc (n / B) n, ArithmeticFunction.vonMangoldt d := by linarith
  rw [hdiff, mul_sum]
  calc ∑ d ∈ Ioc (n / B) n, (m : ℝ) * ArithmeticFunction.vonMangoldt d
      ≤ ∑ d ∈ Ioc (n / B) n, vonMangoldtWeight d * (stepWeight c (n / d) : ℝ) := by
        refine sum_le_sum fun d hd => ?_
        obtain ⟨hd1, hd2⟩ := mem_Ioc.mp hd
        have hd_pos : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd1
        have hnd_ge : 1 ≤ n / d := (Nat.one_le_div_iff hd_pos).mpr hd2
        have hnd_lt : n / d < B := by
          rw [Nat.div_lt_iff_lt_mul hd_pos]
          have hlt := (Nat.div_lt_iff_lt_mul hB).mp hd1
          rwa [mul_comm] at hlt
        have hm_le : (m : ℝ) ≤ (stepWeight c (n / d) : ℝ) := by
          exact_mod_cast hwin (n / d) (mem_Ico.mpr ⟨hnd_ge, hnd_lt⟩)
        have hΛ : 0 ≤ vonMangoldtWeight d := ArithmeticFunction.vonMangoldt_nonneg
        change (m : ℝ) * vonMangoldtWeight d ≤ _
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hm_le hΛ
    _ ≤ ∑ d ∈ Ioc 0 n, vonMangoldtWeight d * (stepWeight c (n / d) : ℝ) := by
        refine sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le _)) fun d _ _ => ?_
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by exact_mod_cast hstep _)

/-- Uniform Stirling approximation error for `log (⌊n / k⌋!)` across both `n < k` and `k ≤ n`. -/
theorem abs_log_div_factorial_sub_le {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    |Real.log ((n / k).factorial : ℕ) - ((n : ℝ) / k) * (Real.log n - Real.log k - 1)| ≤
      3 + Real.log k + 2 * Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  rcases lt_or_ge n k with hlt | hge
  · rw [Nat.div_eq_of_lt hlt, Nat.factorial_zero, Nat.cast_one, Real.log_one, zero_sub, abs_neg,
      abs_mul]
    have hnk1 : |(n : ℝ) / k| ≤ 1 := by
      rw [abs_of_pos (div_pos hn0 hk0), div_le_one hk0]
      exact_mod_cast hlt.le
    have habs : |Real.log n - Real.log k - 1| ≤ Real.log n + Real.log k + 1 := by
      rw [show Real.log n - Real.log k - 1 = Real.log n + (-(Real.log k + 1)) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg hlogn, abs_neg, abs_of_nonneg (by linarith)]
      linarith
    calc |(n : ℝ) / k| * |Real.log n - Real.log k - 1|
        ≤ 1 * (Real.log n + Real.log k + 1) := mul_le_mul hnk1 habs (abs_nonneg _) zero_le_one
      _ ≤ 3 + Real.log k + 2 * Real.log n := by linarith
  · set q := n / k
    have hq1 : 1 ≤ q := (Nat.one_le_div_iff hk).mpr hge
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hq_le_n : (q : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n k
    have hlogq : Real.log q ≤ Real.log n := Real.log_le_log hq0 hq_le_n
    set t := (n : ℝ) / k
    have hqt : (q : ℝ) ≤ t := Nat.cast_div_le
    have htq1 : t < (q : ℝ) + 1 := by
      rw [div_lt_iff₀ hk0]
      have hlt_nat : n < (q + 1) * k := by
        rw [mul_comm]
        exact Nat.lt_mul_div_succ n hk
      exact_mod_cast hlt_nat
    have htn : t ≤ n := div_le_self hn0.le (by exact_mod_cast hk)
    have ht0 : 0 < t := div_pos hn0 hk0
    have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (le_trans (by exact_mod_cast hq1) hqt)
    have hlogt_le : Real.log t ≤ Real.log n := Real.log_le_log ht0 htn
    have hlogt_eq : Real.log t = Real.log n - Real.log k := Real.log_div hn0.ne' hk0.ne'
    obtain ⟨hb1, hb2⟩ := log_factorial_sub_bounds hq1
    have hstirl : |Real.log (q.factorial : ℕ) - (q * Real.log q - q)| ≤ 1 + Real.log n := by
      rw [abs_of_nonneg hb1.le]
      linarith [Real.log_nonneg (by exact_mod_cast hq1 : (1 : ℝ) ≤ q)]
    have hqlog : 0 ≤ (q : ℝ) * (Real.log t - Real.log q) ∧
        (q : ℝ) * (Real.log t - Real.log q) ≤ t - q := by
      have hdiv_ge : 1 ≤ t / q := (one_le_div hq0).mpr hqt
      have hdiv_pos : 0 < t / q := lt_of_lt_of_le zero_lt_one hdiv_ge
      rw [← Real.log_div ht0.ne' hq0.ne']
      refine ⟨mul_nonneg hq0.le (Real.log_nonneg hdiv_ge), ?_⟩
      calc (q : ℝ) * Real.log (t / q)
          ≤ q * (t / q - 1) := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hdiv_pos) hq0.le
        _ = t - q := by field_simp [hq0.ne']
    have hmain_diff : |(t * Real.log t - t) - (q * Real.log q - q)| ≤ 1 + Real.log n := by
      have hid : (t * Real.log t - t) - (q * Real.log q - q) =
          (t - q) * Real.log t + (q * (Real.log t - Real.log q) - (t - q)) := by ring
      rw [hid]
      have h1 : 0 ≤ (t - q) * Real.log t := mul_nonneg (by linarith) hlogt0
      have h2 : (t - q) * Real.log t ≤ Real.log n := by
        calc (t - q) * Real.log t ≤ 1 * Real.log t := mul_le_mul_of_nonneg_right (by linarith) hlogt0
          _ = Real.log t := one_mul _
          _ ≤ Real.log n := hlogt_le
      rw [abs_le]
      constructor <;> linarith [hqlog.1, hqlog.2]
    rw [← hlogt_eq, show t * (Real.log t - 1) = t * Real.log t - t by ring]
    calc |Real.log (q.factorial : ℕ) - (t * Real.log t - t)|
        = |(Real.log (q.factorial : ℕ) - (q * Real.log q - q)) -
            ((t * Real.log t - t) - (q * Real.log q - q))| := by congr 1; ring
      _ ≤ |Real.log (q.factorial : ℕ) - (q * Real.log q - q)| +
            |(t * Real.log t - t) - (q * Real.log q - q)| := abs_sub _ _
      _ ≤ (1 + Real.log n) + (1 + Real.log n) := add_le_add hstirl hmain_diff
      _ ≤ 3 + Real.log k + 2 * Real.log n := by linarith

/-- Explicit Stirling error constant for a stencil `c`. -/
def stencilErrorConst (c : ℕ →₀ ℤ) : ℝ :=
  ∑ k ∈ c.support, |(c k : ℝ)| * (3 + Real.log k + 2)

theorem stencilErrorConst_nonneg (c : ℕ →₀ ℤ) : 0 ≤ stencilErrorConst c := by
  rw [stencilErrorConst]
  refine sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp; positivity
  · have : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
    linarith

/-- **Stirling asymptotic for balanced integer stencils.** For every `n ≥ 1`,
`|log(stencilInt c n) - stencilSlope c · n| ≤ stencilErrorConst c · (1 + log n)`. -/
theorem abs_log_stencilInt_sub_slope_le {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c)
    (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r) {n : ℕ} (hn : 1 ≤ n) :
    |Real.log (stencilInt c n : ℝ) - stencilSlope c * n| ≤
      stencilErrorConst c * (1 + Real.log n) := by
  rw [log_stencilInt_eq_sum hstep n]
  have hlin : stencilSlope c * n =
      ∑ k ∈ c.support, (c k : ℝ) * (((n : ℝ) / k) * (Real.log n - Real.log k - 1)) := by
    have hsplit : ∀ k ∈ c.support,
        (c k : ℝ) * (((n : ℝ) / k) * (Real.log n - Real.log k - 1)) =
        (n * (Real.log n - 1)) * ((c k : ℝ) / k) + (-(c k : ℝ) * Real.log k / k) * n :=
      fun k _ => by ring
    rw [sum_congr rfl hsplit, sum_add_distrib, ← mul_sum, ← sum_mul, hbal, mul_zero, zero_add]
    rfl
  rw [hlin, ← sum_sub_distrib, stencilErrorConst, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  rw [← mul_sub, abs_mul]
  refine (mul_le_mul_of_nonneg_left (abs_log_div_factorial_sub_le hn hk1) (abs_nonneg _)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hprod : 0 ≤ Real.log k * Real.log n := mul_nonneg hlogk hlogn
  linarith

/-- The slope of a balanced nonnegative stencil is nonnegative. -/
theorem stencilSlope_nonneg {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c)
    (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r) : 0 ≤ stencilSlope c := by
  by_contra! hneg
  set E := stencilErrorConst c
  have hE : 0 ≤ E := stencilErrorConst_nonneg c
  obtain ⟨N, hN1, hNlt⟩ : ∃ N : ℕ, 1 ≤ N ∧ stencilSlope c * (N : ℝ) + E * (1 + Real.log N) < 0 := by
    set M := Nat.ceil ((2 * E + 2) / (-stencilSlope c)) + 2
    have hM1 : 1 ≤ M := by omega
    refine ⟨M ^ 2, Nat.one_le_pow 2 M hM1, ?_⟩
    have hM_pos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hM_ge : (2 * E + 2) / (-stencilSlope c) ≤ M :=
      (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_add_right _ 2)
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast Nat.le_add_left 2 _
    have hlogM : Real.log ((M ^ 2 : ℕ) : ℝ) ≤ 2 * M := by
      rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
      have := Real.log_le_sub_one_of_pos hM_pos
      linarith
    have hmul : 2 * E + 2 ≤ (M : ℝ) * (-stencilSlope c) :=
      (div_le_iff₀ (by linarith)).mp hM_ge
    have hmulM : (2 * E + 2) * (M : ℝ) ≤ (M : ℝ) * (-stencilSlope c) * (M : ℝ) :=
      mul_le_mul_of_nonneg_right hmul hM_pos.le
    have hElog : E * (1 + Real.log ((M ^ 2 : ℕ) : ℝ)) ≤ E * (1 + 2 * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hE
    have hcast_sq : stencilSlope c * ((M ^ 2 : ℕ) : ℝ) = -((M : ℝ) * (-stencilSlope c) * (M : ℝ)) := by
      rw [Nat.cast_pow]; ring
    have h2M : E * (1 + 2 * (M : ℝ)) < (2 * E + 2) * (M : ℝ) := by
      have hid : (2 * E + 2) * (M : ℝ) - E * (1 + 2 * (M : ℝ)) =
          E * ((M : ℝ) - 1) + 2 * (M : ℝ) := by ring
      have hEm : 0 ≤ E * ((M : ℝ) - 1) := mul_nonneg hE (by linarith)
      linarith
    linarith
  have hlog_ge : 0 ≤ Real.log (stencilInt c N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast stencilInt_pos_of_nonneg hstep N)
  have habs := (abs_le.mp (abs_log_stencilInt_sub_slope_le hc0 hbal hstep hN1)).2
  linarith

/-- **General vanishing-order upper producer.** If `c` is balanced, `stepWeight c ≥ 0` everywhere,
and `stepWeight c ≥ m ≥ 1` on `[1, B)` (`B ≥ 2`), then
`ψ(x) ≤ (stencilSlope c / (m (1 - 1/B))) x + C (log x)²` for all `x ≥ 2`. -/
theorem psi_le_of_stepWeight_producer {c : ℕ →₀ ℤ} {m B : ℕ} (hc0 : c 0 = 0)
    (hbal : IsBalanced c) (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r) (hm : 1 ≤ m) (hB : 2 ≤ B)
    (hwin : ∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      Chebyshev.psi x ≤
        (stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ)))) * x + C * (Real.log x) ^ 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (1 : ℝ) < B := by exact_mod_cast hB
  have h1B : 0 < 1 - 1 / (B : ℝ) := by
    rw [sub_pos, div_lt_one hB0]; exact hB1
  have hslope0 : 0 ≤ stencilSlope c := stencilSlope_nonneg hc0 hbal hstep
  set E := stencilErrorConst c
  have hE0 : 0 ≤ E := stencilErrorConst_nonneg c
  have hstep_bound : ∀ n : ℕ, Chebyshev.psi n - Chebyshev.psi (n / B : ℕ) ≤
      (stencilSlope c / m) * n + (E / m) * (1 + Real.log (max n 1 : ℕ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.zero_div, Nat.cast_zero, Chebyshev.psi_zero, sub_self, mul_zero, zero_add]
      positivity
    · have hpsi := psi_sub_le_log_stencilInt hc0 hstep hwin (by omega) n
      have hst := (abs_le.mp (abs_log_stencilInt_sub_slope_le hc0 hbal hstep hn)).2
      have hmax : max n 1 = n := max_eq_left hn
      rw [hmax, show (stencilSlope c / m) * (n : ℝ) + (E / m) * (1 + Real.log n) =
        (stencilSlope c * n + E * (1 + Real.log n)) / m by ring, le_div_iff₀ hm0]
      linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogB_pos : 0 < Real.log B := Real.log_pos hB1
  refine ⟨(E / m + 1) * (1 / Real.log B + 2 / Real.log 2) * (1 / Real.log 2 + 1), by positivity,
    fun x hx => ?_⟩
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlogx_ge : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogx_pos : 0 < Real.log x := lt_of_lt_of_le hlog2_pos hlogx_ge
  set K := (Nat.log B N).succ
  have hBK : N < B ^ K := Nat.lt_pow_succ_log_self hB N
  have htel : Chebyshev.psi x =
      ∑ j ∈ range K, (Chebyshev.psi (N / B ^ j : ℕ) - Chebyshev.psi (N / B ^ (j + 1) : ℕ)) := by
    have hpsi_eq : Chebyshev.psi x = Chebyshev.psi (N : ℝ) := by
      rw [Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast]
    have hsum := Finset.sum_range_sub' (fun j => Chebyshev.psi (N / B ^ j : ℕ)) K
    rw [pow_zero, Nat.div_one, Nat.div_eq_of_lt hBK, Nat.cast_zero, Chebyshev.psi_zero,
      sub_zero] at hsum
    rw [hpsi_eq, ← hsum]
  rw [htel]
  have hdiv_succ : ∀ j : ℕ, (N / B ^ j) / B = N / B ^ (j + 1) := fun j => by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  have hterm_le : ∀ j ∈ range K,
      Chebyshev.psi (N / B ^ j : ℕ) - Chebyshev.psi (N / B ^ (j + 1) : ℕ) ≤
        (stencilSlope c / m) * (x * (1 / (B : ℝ)) ^ j) + (E / m) * (1 + Real.log x) := by
    intro j _
    rw [← hdiv_succ j]
    have hb := hstep_bound (N / B ^ j)
    have hnb_le : ((N / B ^ j : ℕ) : ℝ) ≤ x * (1 / (B : ℝ)) ^ j := by
      calc ((N / B ^ j : ℕ) : ℝ)
          ≤ (N : ℝ) / ((B ^ j : ℕ) : ℝ) := Nat.cast_div_le
        _ ≤ x / (B : ℝ) ^ j := by
            push_cast; exact div_le_div_of_nonneg_right hNx (pow_nonneg hB0.le j)
        _ = x * (1 / (B : ℝ)) ^ j := by rw [one_div, inv_pow, div_eq_mul_inv]
    have hlog_le : Real.log (max (N / B ^ j) 1 : ℕ) ≤ Real.log x := by
      have hm_le : ((max (N / B ^ j) 1 : ℕ) : ℝ) ≤ x := by
        rw [Nat.cast_max]
        exact max_le ((Nat.cast_le.mpr (Nat.div_le_self N _)).trans hNx) (by norm_num; linarith)
      exact Real.log_le_log (by positivity) hm_le
    refine hb.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left hnb_le (div_nonneg hslope0 hm0.le)
    · exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hE0 hm0.le)
  have hgeom : ∑ j ∈ range K, (1 / (B : ℝ)) ^ j ≤ 1 / (1 - 1 / (B : ℝ)) := by
    have hne : (1 / (B : ℝ)) ≠ 1 := by linarith
    rw [geom_sum_eq hne]
    have hpow0 : 0 ≤ (1 / (B : ℝ)) ^ K := by positivity
    have hrew : ((1 / (B : ℝ)) ^ K - 1) / (1 / (B : ℝ) - 1) =
        (1 - (1 / (B : ℝ)) ^ K) / (1 - 1 / (B : ℝ)) := by
      rw [div_eq_div_iff (by linarith) h1B.ne']
      ring
    rw [hrew]
    exact div_le_div_of_nonneg_right (by linarith) h1B.le
  have hK_le : (K : ℝ) ≤ (1 / Real.log B + 2 / Real.log 2) * Real.log x := by
    have hpow_le : B ^ Nat.log B N ≤ N := Nat.pow_log_le_self B (by omega : N ≠ 0)
    have hpow_leR : (B : ℝ) ^ Nat.log B N ≤ x := by
      rw [← Nat.cast_pow]
      exact (Nat.cast_le.mpr hpow_le).trans hNx
    have hlog_le : (Nat.log B N : ℝ) * Real.log B ≤ Real.log x := by
      have := Real.log_le_log (pow_pos hB0 _) hpow_leR
      rwa [Real.log_pow] at this
    have h1 : (Nat.log B N : ℝ) ≤ Real.log x / Real.log B := (le_div_iff₀ hlogB_pos).mpr hlog_le
    have h2 : (1 : ℝ) ≤ (2 / Real.log 2) * Real.log x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2_pos]; linarith
    calc (K : ℝ) = (Nat.log B N : ℝ) + 1 := by simp [K]
      _ ≤ Real.log x / Real.log B + (2 / Real.log 2) * Real.log x := add_le_add h1 h2
      _ = (1 / Real.log B + 2 / Real.log 2) * Real.log x := by ring
  have h1log : 1 + Real.log x ≤ (1 / Real.log 2 + 1) * Real.log x := by
    have : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log x := by
      rw [one_div_mul_eq_div, one_le_div hlog2_pos]; exact hlogx_ge
    linarith
  calc ∑ j ∈ range K, (Chebyshev.psi (N / B ^ j : ℕ) - Chebyshev.psi (N / B ^ (j + 1) : ℕ))
      ≤ ∑ j ∈ range K, ((stencilSlope c / m) * (x * (1 / (B : ℝ)) ^ j) +
          (E / m) * (1 + Real.log x)) := sum_le_sum hterm_le
    _ = (stencilSlope c / m) * x * (∑ j ∈ range K, (1 / (B : ℝ)) ^ j) +
          (K : ℝ) * ((E / m) * (1 + Real.log x)) := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
        congr 1
        rw [← mul_sum, ← mul_sum]
        ring
    _ ≤ (stencilSlope c / m) * x * (1 / (1 - 1 / (B : ℝ))) +
          ((1 / Real.log B + 2 / Real.log 2) * Real.log x) *
            ((E / m + 1) * ((1 / Real.log 2 + 1) * Real.log x)) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hgeom (mul_nonneg (div_nonneg hslope0 hm0.le) (by linarith))
        · refine mul_le_mul hK_le ?_ (mul_nonneg (div_nonneg hE0 hm0.le) (by linarith)) (by positivity)
          exact mul_le_mul (by linarith) h1log (by linarith) (by positivity)
    _ = (stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ)))) * x +
          ((E / m + 1) * (1 / Real.log B + 2 / Real.log 2) * (1 / Real.log 2 + 1)) *
            (Real.log x) ^ 2 := by
        congr 1
        · field_simp [hm0.ne', h1B.ne']
        · ring

/-! ### Pronic slope series and palindromic duality -/

private lemma hasSum_pronic_inv :
    HasSum (fun j : ℕ => (1 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => by positivity)]
  have htel : ∀ R : ℕ, ∑ j ∈ range R, (1 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) =
      1 - 1 / ((R : ℝ) + 1) := by
    intro R
    induction R with
    | zero => simp
    | succ R ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : (R : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (R : ℝ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  simp_rw [htel]
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at h
  exact h.congr fun R => by simp [one_div]

private lemma natCast_mod_succ_sub_mod (d j : ℕ) (hd : 0 < d) :
    (((j + 1) % d : ℕ) : ℝ) - ((j % d : ℕ) : ℝ) = 1 - if d ∣ j + 1 then (d : ℝ) else 0 := by
  have hdiv := Nat.div_add_mod j d
  have hlt := Nat.mod_lt j hd
  set q := j / d
  set s := j % d
  have hj1 : j + 1 = (s + 1) + d * q := by omega
  by_cases hs : s + 1 < d
  · have hmod : (j + 1) % d = s + 1 := by
      rw [hj1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
    have hndvd : ¬ d ∣ j + 1 := fun h => by
      have := Nat.mod_eq_zero_of_dvd h; omega
    rw [hmod, if_neg hndvd]
    push_cast; ring
  · have hs' : s + 1 = d := by omega
    have hmod : (j + 1) % d = 0 := by rw [hj1, hs', Nat.add_mul_mod_self_left, Nat.mod_self]
    rw [hmod, if_pos (Nat.dvd_of_mod_eq_zero hmod)]
    have : ((s + 1 : ℕ) : ℝ) = d := by rw [hs']
    push_cast at this ⊢
    linarith

private lemma sum_range_dvd_succ_div (d K : ℕ) (hd : 0 < d) :
    ∑ j ∈ range (d * K), (if d ∣ j + 1 then (d : ℝ) else 0) / ((j : ℝ) + 1) =
      ∑ k ∈ range K, 1 / ((k : ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    rw [sum_eq_single (d - 1)]
    · rw [if_pos (by
        rw [show d * K + (d - 1) + 1 = d * (K + 1) by
          obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
          simp only [Nat.add_sub_cancel]; ring]
        exact dvd_mul_right d (K + 1))]
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have hcast : ((d * K + (d - 1) : ℕ) : ℝ) + 1 = d * ((K : ℝ) + 1) := by
        rw [show d * K + (d - 1) = d * K + d - 1 by omega, Nat.cast_sub (by omega)]
        push_cast; ring
      rw [hcast]
      field_simp
    · intro a ha hne
      rw [if_neg, zero_div]
      intro hdvd
      have ha' := mem_range.mp ha
      have h2 : d ∣ a + 1 := by
        have : d ∣ d * K + (a + 1) := by rwa [← add_assoc]
        exact (Nat.dvd_add_right (dvd_mul_right d K)).mp this
      obtain ⟨c, hc⟩ := h2
      rcases c with _ | _ | c
      · omega
      · omega
      · have hge : d * 2 ≤ d * (c + 1 + 1) := Nat.mul_le_mul_left d (by omega)
        rw [← hc] at hge
        omega
    · intro h; exact absurd (mem_range.mpr (by omega)) h

/-- Exact pronic series for `((r % d) / d) / (r (r + 1))`. -/
theorem hasSum_mod_div_pronic {d : ℕ} (hd : 1 ≤ d) :
    HasSum (fun j : ℕ => (((j + 1) % d : ℕ) : ℝ) / d / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
      (Real.log d / d) := by
  have hd0 : 0 < d := hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Summable fun j : ℕ =>
      (((j + 1) % d : ℕ) : ℝ) / d / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    refine hasSum_pronic_inv.summable.of_nonneg_of_le (fun j => by positivity) fun j => ?_
    have hle : (((j + 1) % d : ℕ) : ℝ) / d ≤ 1 := by
      rw [div_le_one hdR]; exact_mod_cast (Nat.mod_lt _ hd0).le
    rw [div_eq_mul_one_div]
    exact mul_le_of_le_one_left (by positivity) hle
  set A : ℕ → ℝ := fun R => ∑ j ∈ range R,
    ((((j + 1) % d : ℕ) : ℝ) / d - ((j % d : ℕ) : ℝ) / d) / ((j : ℝ) + 1)
  have habel : ∀ R : ℕ,
      ∑ j ∈ range R, (((j + 1) % d : ℕ) : ℝ) / d / (((j : ℝ) + 1) * ((j : ℝ) + 2)) =
        A R - ((R % d : ℕ) : ℝ) / d / ((R : ℝ) + 1) := by
    intro R
    induction R with
    | zero => simp [A]
    | succ R ih =>
      simp only [A] at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have h1 : (R : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (R : ℝ) + 2 ≠ 0 := by positivity
      push_cast; field_simp; ring
  have hF : Tendsto (fun R : ℕ => ((R % d : ℕ) : ℝ) / d / ((R : ℝ) + 1)) atTop (𝓝 0) := by
    refine squeeze_zero (fun R => by positivity) (fun R => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hle : ((R % d : ℕ) : ℝ) / d ≤ 1 := by
      rw [div_le_one hdR]; exact_mod_cast (Nat.mod_lt R hd0).le
    exact div_le_div_of_nonneg_right hle (by positivity)
  have hAlim : Tendsto A atTop
      (𝓝 (∑' j : ℕ, (((j + 1) % d : ℕ) : ℝ) / d / (((j : ℝ) + 1) * ((j : ℝ) + 2)))) := by
    have := hs.hasSum.tendsto_sum_nat.add hF
    rw [add_zero] at this
    exact this.congr fun R => by rw [habel]; ring
  have hdK : Tendsto (fun K : ℕ => d * K) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => ha.trans (Nat.le_mul_of_pos_left a hd)⟩
  have hharm_eq : ∀ n : ℕ, (harmonic n : ℝ) = ∑ j ∈ range n, 1 / ((j : ℝ) + 1) := by
    intro n; rw [harmonic]; push_cast; simp [one_div]
  have hAval : ∀ K : ℕ, A (d * K) = ((harmonic (d * K) : ℝ) - harmonic K) / d := by
    intro K
    simp only [A]
    have hterm : ∀ j : ℕ,
        ((((j + 1) % d : ℕ) : ℝ) / d - ((j % d : ℕ) : ℝ) / d) / ((j : ℝ) + 1) =
          (1 / ((j : ℝ) + 1)) / d - (if d ∣ j + 1 then (d : ℝ) else 0) / ((j : ℝ) + 1) / d := by
      intro j
      rw [← sub_div, natCast_mod_succ_sub_mod d j hd0]
      field_simp
    rw [sum_congr rfl fun j _ => hterm j, sum_sub_distrib, ← sum_div, ← sum_div,
      sum_range_dvd_succ_div d K hd0, hharm_eq, hharm_eq, sub_div]
  have hlim_harm : Tendsto (fun K : ℕ => (harmonic (d * K) : ℝ) - harmonic K) atTop
      (𝓝 (Real.log d)) := by
    have h := Real.tendsto_harmonic_sub_log
    have hlim := ((h.comp hdK).sub h).add_const (Real.log d)
    rw [sub_self, zero_add] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    have hKR : (K : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply]
    push_cast
    rw [Real.log_mul hdR.ne' hKR]
    ring
  have hlim2 : Tendsto (fun K : ℕ => A (d * K)) atTop (𝓝 (Real.log d / d)) := by
    simp_rw [hAval]
    exact hlim_harm.div_const d
  have heq := tendsto_nhds_unique (hAlim.comp hdK) hlim2
  rw [← heq]
  exact hs.hasSum

/-- Residue decomposition `stepWeight c r = ∑_k (-c(k) / k) (r % k)` for balanced stencils. -/
theorem stepWeight_eq_sum_mod {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) (r : ℕ) :
    (stepWeight c r : ℝ) = ∑ k ∈ c.support, (-(c k : ℝ) / k) * ((r % k : ℕ) : ℝ) := by
  have hterm : ∀ k ∈ c.support, (c k : ℝ) * ((r / k : ℕ) : ℝ) =
      (r : ℝ) * ((c k : ℝ) / k) + (-(c k : ℝ) / k) * ((r % k : ℕ) : ℝ) := by
    intro k hk
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
    have hdiv : (k : ℝ) * ((r / k : ℕ) : ℝ) + ((r % k : ℕ) : ℝ) = r := by
      exact_mod_cast Nat.div_add_mod r k
    have hdiv' : ((r / k : ℕ) : ℝ) = ((r : ℝ) - ((r % k : ℕ) : ℝ)) / k := by
      rw [eq_div_iff hkR]; linarith
    rw [hdiv']; ring
  rw [stepWeight, Int.cast_sum]
  have hcast : ∀ k ∈ c.support, ((c k * (r / k : ℕ) : ℤ) : ℝ) = (c k : ℝ) * ((r / k : ℕ) : ℝ) :=
    fun _ _ => by push_cast; rfl
  rw [sum_congr rfl hcast, sum_congr rfl hterm, sum_add_distrib, ← mul_sum, hbal, mul_zero,
    zero_add]

/-- **Pronic slope series.** For every balanced stencil `c` (`c 0 = 0`),
`stencilSlope c = ∑'_{j : ℕ} stepWeight c (j + 1) / ((j + 1)(j + 2))`. -/
theorem hasSum_stepWeight_div_pronic {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) :
    HasSum (fun j : ℕ => (stepWeight c (j + 1) : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
      (stencilSlope c) := by
  have hfun : (fun j : ℕ => (stepWeight c (j + 1) : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) =
      fun j : ℕ => ∑ k ∈ c.support,
        (-(c k : ℝ)) * ((((j + 1) % k : ℕ) : ℝ) / k / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
    ext j
    rw [stepWeight_eq_sum_mod hc0 hbal (j + 1), sum_div]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [hfun, stencilSlope]
  refine hasSum_sum fun k hk => ?_
  have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
  have h := (hasSum_mod_div_pronic (Nat.pos_of_ne_zero hk0)).mul_left (-(c k : ℝ))
  simpa only [mul_div_assoc] using h

/-- Periodicity and palindromic duality of `stepWeight c` on any common multiple `L` of `c.support`. -/
theorem stepWeight_periodic {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) {L : ℕ}
    (hL : ∀ k ∈ c.support, k ∣ L) (q r : ℕ) :
    stepWeight c (q * L + r) = stepWeight c r := by
  have hR : (stepWeight c (q * L + r) : ℝ) = (stepWeight c r : ℝ) := by
    rw [stepWeight_eq_sum_mod hc0 hbal, stepWeight_eq_sum_mod hc0 hbal]
    refine sum_congr rfl fun k hk => ?_
    obtain ⟨m, rfl⟩ := hL k hk
    have hmod : (q * (k * m) + r) % k = r % k := by
      rw [show q * (k * m) + r = r + k * (q * m) by ring, Nat.add_mul_mod_self_left]
    rw [hmod]
  exact_mod_cast hR

theorem stepWeight_reflect_add {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) {L r : ℕ}
    (hL : ∀ k ∈ c.support, k ∣ L) (hr : r < L) :
    stepWeight c (L - 1 - r) + stepWeight c r = -∑ k ∈ c.support, c k := by
  have hterm : ∀ k ∈ c.support, ((L - 1 - r) / k : ℕ) + (r / k : ℕ) = L / k - 1 := by
    intro k hk
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    obtain ⟨m, rfl⟩ := hL k hk
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp at hr
    · have h1 := Nat.div_add_mod r k
      have h2 := Nat.mod_lt r hk_pos
      have hlt_div : r / k < m := (Nat.div_lt_iff_lt_mul hk_pos).mpr (by rwa [mul_comm])
      have hle : r / k ≤ m - 1 := by omega
      have hkm : k * m = k * (m - 1 - r / k) + k * (r / k) + k := by
        zify [hle, hm0]; ring
      have hrew : k * m - 1 - r = (k - 1 - r % k) + k * (m - 1 - r / k) := by omega
      have hlt_rem : k - 1 - r % k < k := by omega
      have hdiv1 : (k * m - 1 - r) / k = m - 1 - r / k := by
        rw [hrew, Nat.add_mul_div_left _ _ hk_pos, Nat.div_eq_of_lt hlt_rem, zero_add]
      have hdivL : k * m / k = m := Nat.mul_div_right m hk_pos
      omega
  have hR : ((stepWeight c (L - 1 - r) + stepWeight c r : ℤ) : ℝ) =
      ((-∑ k ∈ c.support, c k : ℤ) : ℝ) := by
    simp only [stepWeight, ← sum_add_distrib, ← mul_add, Int.cast_sum, Int.cast_neg]
    have hsum : ∑ k ∈ c.support, ((c k * (((L - 1 - r) / k : ℕ) + (r / k : ℕ)) : ℤ) : ℝ) =
        ∑ k ∈ c.support, ((L : ℝ) * ((c k : ℝ) / k) - (c k : ℝ)) := by
      refine sum_congr rfl fun k hk => ?_
      have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
      have ht := hterm k hk
      obtain ⟨m, hm⟩ := hL k hk
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp [hm] at hr
        · exact hpos
      have hLk : ((L / k : ℕ) : ℝ) = (L : ℝ) / k := by
        rw [hm, Nat.mul_div_right m hk_pos]
        push_cast; field_simp [hkR]
      have hge1 : 1 ≤ L / k := by
        rw [hm, Nat.mul_div_right m hk_pos]
        omega
      have htR : (((L - 1 - r) / k : ℕ) : ℝ) + ((r / k : ℕ) : ℝ) = ((L / k : ℕ) : ℝ) - 1 := by
        have := congrArg (Nat.cast (R := ℝ)) ht
        rwa [Nat.cast_add, Nat.cast_sub hge1, Nat.cast_one] at this
      rw [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_natCast, htR, hLk]
      ring
    rw [hsum, sum_sub_distrib, ← mul_sum, hbal, mul_zero, zero_sub]
  exact_mod_cast hR

/-! ### Ceiling 1: Single-prime Hecke auxiliaries (`2 log 2`) -/

/-- Exact prime-power sum identity for balanced stencils supported on `{p₀^j : 0 ≤ j ≤ K}`. -/
theorem sum_stepWeight_prime_pow_div {c : ℕ →₀ ℤ} {p₀ K M : ℕ} (hp₀ : p₀.Prime)
    (hbal : IsBalanced c) (hsupp : ∀ k ∈ c.support, ∃ j ≤ K, k = p₀ ^ j) (hKM : K ≤ M) :
    ∑ r ∈ range (M + 1), (stepWeight c (p₀ ^ r) : ℝ) / (p₀ : ℝ) ^ r =
      stencilSlope c / Real.log p₀ := by
  have hp0_pos : 0 < p₀ := hp₀.pos
  have hp0R : (0 : ℝ) < p₀ := by exact_mod_cast hp0_pos
  have hlogp : Real.log p₀ ≠ 0 := (Real.log_pos (by exact_mod_cast hp₀.one_lt)).ne'
  simp only [stepWeight, Int.cast_sum, sum_div]
  rw [sum_comm]
  have hinner : ∀ k ∈ c.support,
      ∑ r ∈ range (M + 1), ((c k * (p₀ ^ r / k : ℕ) : ℤ) : ℝ) / (p₀ : ℝ) ^ r =
        (M + 1 : ℝ) * ((c k : ℝ) / k) + (-(c k : ℝ) * Real.log k / k) / Real.log p₀ := by
    intro k hk
    obtain ⟨j, hjK, rfl⟩ := hsupp k hk
    have hjM : j ≤ M := hjK.trans hKM
    have hsplit_range : range (M + 1) = range j ∪ Ico j (M + 1) := by
      ext r; simp only [mem_range, mem_union, mem_Ico]; omega
    have hdisj : Disjoint (range j) (Ico j (M + 1)) := by
      rw [Finset.disjoint_left]; intro r hr1 hr2
      have := mem_range.mp hr1; have := (mem_Ico.mp hr2).1; omega
    rw [hsplit_range, sum_union hdisj]
    have hlow : ∑ r ∈ range j, ((c (p₀ ^ j) * (p₀ ^ r / p₀ ^ j : ℕ) : ℤ) : ℝ) / (p₀ : ℝ) ^ r = 0 := by
      refine sum_eq_zero fun r hr => ?_
      have hlt : p₀ ^ r < p₀ ^ j := Nat.pow_lt_pow_right hp₀.one_lt (mem_range.mp hr)
      simp [Nat.div_eq_of_lt hlt]
    have hhigh : ∑ r ∈ Ico j (M + 1),
        ((c (p₀ ^ j) * (p₀ ^ r / p₀ ^ j : ℕ) : ℤ) : ℝ) / (p₀ : ℝ) ^ r =
        (M + 1 - j : ℕ) * ((c (p₀ ^ j) : ℝ) / (p₀ : ℝ) ^ j) := by
      have hcongr : ∀ r ∈ Ico j (M + 1),
          ((c (p₀ ^ j) * (p₀ ^ r / p₀ ^ j : ℕ) : ℤ) : ℝ) / (p₀ : ℝ) ^ r =
            (c (p₀ ^ j) : ℝ) / (p₀ : ℝ) ^ j := by
        intro r hr
        have hjr : j ≤ r := (mem_Ico.mp hr).1
        have hdiv : p₀ ^ r / p₀ ^ j = p₀ ^ (r - j) := by
          rw [← Nat.pow_sub_mul_pow p₀ hjr, Nat.mul_div_cancel _ (pow_pos hp0_pos j)]
        rw [hdiv]
        push_cast
        have hpowR : (p₀ : ℝ) ^ r = (p₀ : ℝ) ^ (r - j) * (p₀ : ℝ) ^ j := by
          rw [← pow_add, Nat.sub_add_cancel hjr]
        rw [hpowR]
        have hne : (p₀ : ℝ) ^ (r - j) ≠ 0 := pow_ne_zero _ hp0R.ne'
        field_simp [hne]
      rw [sum_congr rfl hcongr, sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [hlow, zero_add, hhigh, Nat.cast_sub (by omega : j ≤ M + 1), Nat.cast_pow, Real.log_pow]
    push_cast
    field_simp [hlogp]
    ring
  rw [sum_congr rfl hinner, sum_add_distrib, ← mul_sum, hbal, mul_zero, zero_add, ← sum_div]
  rfl

/-- **Single-prime Hecke ceiling (`(p₀ log p₀) / (p₀ - 1)`).** -/
theorem single_prime_hecke_slope_ge {c : ℕ →₀ ℤ} {p₀ K m R : ℕ} (hp₀ : p₀.Prime)
    (hbal : IsBalanced c) (hsupp : ∀ k ∈ c.support, ∃ j ≤ K, k = p₀ ^ j)
    (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r) (hm : 1 ≤ m) (hR : 1 ≤ R)
    (hwin : ∀ r < R, (m : ℤ) ≤ stepWeight c (p₀ ^ r)) :
    (p₀ : ℝ) * Real.log p₀ / ((p₀ : ℝ) - 1) ≤
      stencilSlope c / ((m : ℝ) * (1 - 1 / (p₀ : ℝ) ^ R)) := by
  have hp1 : (1 : ℝ) < p₀ := by exact_mod_cast hp₀.one_lt
  have hp0 : (0 : ℝ) < p₀ := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlogp : 0 < Real.log p₀ := Real.log_pos hp1
  have hpow_gt1 : (1 : ℝ) < (p₀ : ℝ) ^ R := one_lt_pow₀ hp1 (by omega)
  have h1pR : 0 < 1 - 1 / (p₀ : ℝ) ^ R := by
    rw [sub_pos, div_lt_one (by positivity)]; exact hpow_gt1
  set M := max K R
  have hid := sum_stepWeight_prime_pow_div hp₀ hbal hsupp (le_max_left K R)
  have hsub : range R ⊆ range (M + 1) := range_mono (by omega)
  have hge : (m : ℝ) * ∑ r ∈ range R, (1 / (p₀ : ℝ)) ^ r ≤
      stencilSlope c / Real.log p₀ := by
    rw [← hid, mul_sum]
    calc ∑ r ∈ range R, (m : ℝ) * (1 / (p₀ : ℝ)) ^ r
        ≤ ∑ r ∈ range R, (stepWeight c (p₀ ^ r) : ℝ) / (p₀ : ℝ) ^ r := by
          refine sum_le_sum fun r hr => ?_
          have hw : (m : ℝ) ≤ (stepWeight c (p₀ ^ r) : ℝ) := by
            exact_mod_cast hwin r (mem_range.mp hr)
          rw [one_div, inv_pow, ← div_eq_mul_inv]
          exact div_le_div_of_nonneg_right hw (by positivity)
      _ ≤ ∑ r ∈ range (M + 1), (stepWeight c (p₀ ^ r) : ℝ) / (p₀ : ℝ) ^ r := by
          refine sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => ?_
          exact div_nonneg (by exact_mod_cast hstep _) (by positivity)
  have hgeom : ∑ r ∈ range R, (1 / (p₀ : ℝ)) ^ r =
      (1 - 1 / (p₀ : ℝ) ^ R) * ((p₀ : ℝ) / ((p₀ : ℝ) - 1)) := by
    have hne : (1 / (p₀ : ℝ)) ≠ 1 := by
      rw [ne_eq, div_eq_one_iff_eq hp0.ne']
      linarith
    rw [geom_sum_eq hne, one_div_pow, mul_div_assoc',
      div_eq_div_iff (show (1 : ℝ) / p₀ - 1 ≠ 0 by linarith) (show (p₀ : ℝ) - 1 ≠ 0 by linarith)]
    have hp_inv : (p₀ : ℝ) * (1 / (p₀ : ℝ) - 1) = 1 - (p₀ : ℝ) := by
      rw [mul_sub, mul_one_div_cancel hp0.ne', mul_one]
    rw [mul_assoc, hp_inv]
    ring
  rw [hgeom] at hge
  rw [le_div_iff₀ (mul_pos hm0 h1pR)]
  have hge' := (le_div_iff₀ hlogp).mp hge
  linarith [show (p₀ : ℝ) * Real.log p₀ / ((p₀ : ℝ) - 1) * ((m : ℝ) * (1 - 1 / (p₀ : ℝ) ^ R)) =
    (m : ℝ) * ((1 - 1 / (p₀ : ℝ) ^ R) * ((p₀ : ℝ) / ((p₀ : ℝ) - 1))) * Real.log p₀ by ring]

/-- `(p log p) / (p - 1) ≥ 2 log 2` for every prime `p`. -/
theorem prime_mul_log_div_sub_one_ge {p : ℕ} (hp : p.Prime) :
    2 * Real.log 2 ≤ (p : ℝ) * Real.log p / ((p : ℝ) - 1) := by
  rcases eq_or_lt_of_le hp.two_le with rfl | hp3
  · norm_num
  · have hp3' : 3 ≤ p := hp3
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3'
    have hsub : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [le_div_iff₀ hsub]
    rcases eq_or_lt_of_le hp3' with rfl | hp4
    · -- `p = 3`: show `4 log 2 ≤ 3 log 3`, i.e. `16 ≤ 27`
      push_cast
      have hlt : Real.log ((2 : ℝ) ^ 4) ≤ Real.log ((3 : ℝ) ^ 3) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow, Real.log_pow] at hlt
      norm_num at hlt ⊢
      linarith
    · -- `p ≥ 4`: `log p ≥ log 4 = 2 log 2`, so `p log p ≥ 2 p log 2 > 2 (p - 1) log 2`
      have hlog4 : 2 * Real.log 2 ≤ Real.log p := by
        have h4p : (2 : ℝ) ^ 2 ≤ p := by
          rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
          exact_mod_cast hp4
        have hlt : Real.log ((2 : ℝ) ^ 2) ≤ Real.log p :=
          Real.log_le_log (by norm_num) h4p
        rw [Real.log_pow] at hlt
        norm_num at hlt
        exact hlt
      have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hmul : (p : ℝ) * (2 * Real.log 2) ≤ (p : ℝ) * Real.log p :=
        mul_le_mul_of_nonneg_left hlog4 (by linarith)
      linarith

/-- **Universal single-prime Hecke ceiling (`2 log 2`).** -/
theorem single_prime_hecke_slope_ge_two_log_two {c : ℕ →₀ ℤ} {p₀ K m R : ℕ} (hp₀ : p₀.Prime)
    (hbal : IsBalanced c) (hsupp : ∀ k ∈ c.support, ∃ j ≤ K, k = p₀ ^ j)
    (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r) (hm : 1 ≤ m) (hR : 1 ≤ R)
    (hwin : ∀ r < R, (m : ℤ) ≤ stepWeight c (p₀ ^ r)) :
    2 * Real.log 2 ≤ stencilSlope c / ((m : ℝ) * (1 - 1 / (p₀ : ℝ) ^ R)) :=
  (prime_mul_log_div_sub_one_ge hp₀).trans
    (single_prime_hecke_slope_ge hp₀ hbal hsupp hstep hm hR hwin)

/-! ### Breakthrough at two primes: `{2, 3}` beats `2 log 2` -/

/-- Explicit `{2, 3}`-supported stencil `c_{2,3} = e_1 - e_2 - e_3 - e_4 + e_{12}`. -/
def twoThreeStencil : ℕ →₀ ℤ :=
  Finsupp.single 1 1 - Finsupp.single 2 1 - Finsupp.single 3 1 -
    Finsupp.single 4 1 + Finsupp.single 12 1

private lemma twoThreeStencil_apply (k : ℕ) :
    twoThreeStencil k =
      (if 1 = k then 1 else 0) - (if 2 = k then 1 else 0) -
        (if 3 = k then 1 else 0) - (if 4 = k then 1 else 0) +
        (if 12 = k then 1 else 0) := by
  simp [twoThreeStencil, Finsupp.single_apply]

private lemma twoThreeStencil_support_subset :
    twoThreeStencil.support ⊆ ({1, 2, 3, 4, 12} : Finset ℕ) := by
  intro k hk
  have hk' : twoThreeStencil k ≠ 0 := Finsupp.mem_support_iff.mp hk
  by_contra hnot
  simp only [mem_insert, mem_singleton, not_or] at hnot
  obtain ⟨h1, h2, h3, h4, h12⟩ := hnot
  apply hk'
  rw [twoThreeStencil_apply, if_neg (Ne.symm h1), if_neg (Ne.symm h2),
    if_neg (Ne.symm h3), if_neg (Ne.symm h4), if_neg (Ne.symm h12)]
  norm_num

theorem twoThreeStencil_zero : twoThreeStencil 0 = 0 := by
  norm_num [twoThreeStencil_apply]

theorem isBalanced_twoThreeStencil : IsBalanced twoThreeStencil := by
  rw [IsBalanced, sum_subset twoThreeStencil_support_subset
    (fun k _ hk => by rw [Finsupp.notMem_support_iff.mp hk]; simp)]
  simp only [sum_insert (by simp : (1 : ℕ) ∉ ({2, 3, 4, 12} : Finset ℕ)),
    sum_insert (by simp : (2 : ℕ) ∉ ({3, 4, 12} : Finset ℕ)),
    sum_insert (by simp : (3 : ℕ) ∉ ({4, 12} : Finset ℕ)),
    sum_insert (by simp : (4 : ℕ) ∉ ({12} : Finset ℕ)), sum_singleton]
  norm_num [twoThreeStencil_apply]

theorem stepWeight_twoThreeStencil_eq (r : ℕ) :
    stepWeight twoThreeStencil r =
      (r : ℤ) - (r / 2 : ℕ) - (r / 3 : ℕ) - (r / 4 : ℕ) + (r / 12 : ℕ) := by
  rw [stepWeight, sum_subset twoThreeStencil_support_subset
    (fun k _ hk => by rw [Finsupp.notMem_support_iff.mp hk]; simp)]
  simp only [sum_insert (by simp : (1 : ℕ) ∉ ({2, 3, 4, 12} : Finset ℕ)),
    sum_insert (by simp : (2 : ℕ) ∉ ({3, 4, 12} : Finset ℕ)),
    sum_insert (by simp : (3 : ℕ) ∉ ({4, 12} : Finset ℕ)),
    sum_insert (by simp : (4 : ℕ) ∉ ({12} : Finset ℕ)), sum_singleton]
  have v1 : twoThreeStencil 1 = 1 := by norm_num [twoThreeStencil_apply]
  have v2 : twoThreeStencil 2 = -1 := by norm_num [twoThreeStencil_apply]
  have v3 : twoThreeStencil 3 = -1 := by norm_num [twoThreeStencil_apply]
  have v4 : twoThreeStencil 4 = -1 := by norm_num [twoThreeStencil_apply]
  have v12 : twoThreeStencil 12 = 1 := by norm_num [twoThreeStencil_apply]
  rw [v1, v2, v3, v4, v12, Nat.div_one]
  ring

theorem stepWeight_twoThreeStencil_bounds (r : ℕ) :
    0 ≤ stepWeight twoThreeStencil r ∧ stepWeight twoThreeStencil r ≤ 1 := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 12 ∧ r = 12 * q + s :=
    ⟨r / 12, r % 12, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod r 12).symm⟩
  rw [stepWeight_twoThreeStencil_eq]
  have h2 : (12 * q + s) / 2 = 6 * q + s / 2 := by omega
  have h3 : (12 * q + s) / 3 = 4 * q + s / 3 := by omega
  have h4 : (12 * q + s) / 4 = 3 * q + s / 4 := by omega
  have h12 : (12 * q + s) / 12 = q + s / 12 := by omega
  rw [h2, h3, h4, h12]
  push_cast
  interval_cases s <;> omega

theorem stepWeight_twoThreeStencil_window :
    ∀ r ∈ Ico 1 4, (1 : ℤ) ≤ stepWeight twoThreeStencil r := by
  intro r hr
  obtain ⟨h1, h4⟩ := mem_Ico.mp hr
  rw [stepWeight_twoThreeStencil_eq]
  interval_cases r <;> omega

theorem twoThreeStencil_normalized_slope :
    stencilSlope twoThreeStencil / ((1 : ℝ) * (1 - 1 / (4 : ℝ))) =
      (10 / 9 : ℝ) * Real.log 2 + (1 / 3 : ℝ) * Real.log 3 := by
  rw [stencilSlope, sum_subset twoThreeStencil_support_subset
    (fun k _ hk => by rw [Finsupp.notMem_support_iff.mp hk]; simp)]
  simp only [sum_insert (by simp : (1 : ℕ) ∉ ({2, 3, 4, 12} : Finset ℕ)),
    sum_insert (by simp : (2 : ℕ) ∉ ({3, 4, 12} : Finset ℕ)),
    sum_insert (by simp : (3 : ℕ) ∉ ({4, 12} : Finset ℕ)),
    sum_insert (by simp : (4 : ℕ) ∉ ({12} : Finset ℕ)), sum_singleton]
  have v1 : twoThreeStencil 1 = 1 := by norm_num [twoThreeStencil_apply]
  have v2 : twoThreeStencil 2 = -1 := by norm_num [twoThreeStencil_apply]
  have v3 : twoThreeStencil 3 = -1 := by norm_num [twoThreeStencil_apply]
  have v4 : twoThreeStencil 4 = -1 := by norm_num [twoThreeStencil_apply]
  have v12 : twoThreeStencil 12 = 1 := by norm_num [twoThreeStencil_apply]
  rw [v1, v2, v3, v4, v12]
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 4 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), l4]
  push_cast
  rw [Real.log_one, l4, l12]
  ring

theorem twoThreeStencil_slope_lt :
    stencilSlope twoThreeStencil / ((1 : ℝ) * (1 - 1 / (4 : ℝ))) < 23 / 20 ∧
      (23 / 20 : ℝ) < 2 * Real.log 2 := by
  rw [twoThreeStencil_normalized_slope]
  have h98 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
    show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow, Real.log_pow] at h98
  norm_num at h98
  exact ⟨by linarith [Real.log_two_lt_d9, h98], by linarith [Real.log_two_gt_d9]⟩

/-- **Unconditional `{2, 3}` upper producer beating `2 log 2`.** -/
theorem psi_le_of_twoThreeStencil :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      Chebyshev.psi x ≤ (23 / 20 : ℝ) * x + C * (Real.log x) ^ 2 := by
  obtain ⟨C, hC, hpsi⟩ := psi_le_of_stepWeight_producer twoThreeStencil_zero
    isBalanced_twoThreeStencil (fun r => (stepWeight_twoThreeStencil_bounds r).1)
    le_rfl (by norm_num : 2 ≤ 4) stepWeight_twoThreeStencil_window
  refine ⟨C, hC, fun x hx => (hpsi x hx).trans ?_⟩
  have hlt := twoThreeStencil_slope_lt.1
  have hmul := mul_le_mul_of_nonneg_right hlt.le (by linarith : (0 : ℝ) ≤ x)
  linarith

/-! ### Ceiling 2: Universal finite-prime coprime jump obstruction (`> 1`) -/

/-- Support restriction to a finite set `S` of primes (`ℤ[X_p : p ∈ S]`). -/
def IsPrimeAlphabetSupported (S : Finset ℕ) (c : ℕ →₀ ℤ) : Prop :=
  ∀ k ∈ c.support, ∀ p : ℕ, p.Prime → p ∣ k → p ∈ S

/-- **Coprime jump law.** At every `q ≥ 2` coprime to `∏_{p ∈ S} p`, an `S`-supported stencil jumps
by `stepWeight c 1`: `stepWeight c q - stepWeight c (q - 1) = stepWeight c 1`. -/
theorem stepWeight_coprime_jump {S : Finset ℕ} {c : ℕ →₀ ℤ} (hc0 : c 0 = 0)
    (hS : IsPrimeAlphabetSupported S c) {q : ℕ} (hq : 2 ≤ q)
    (hcop : Nat.Coprime q (∏ p ∈ S, p)) :
    stepWeight c q - stepWeight c (q - 1) = stepWeight c 1 := by
  rw [stepWeight_one hc0]
  classical
  have hdiff : ∀ k ∈ c.support, k ≠ 1 → (q / k : ℕ) = ((q - 1) / k : ℕ) := by
    intro k hk hk1
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hk2 : 2 ≤ k := by omega
    obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
    have hpS : p ∈ S := hS k hk p hp hpk
    have hpP : p ∣ ∏ r ∈ S, r := dvd_prod_of_mem _ hpS
    have hndvd : ¬ k ∣ q := by
      intro hkq
      have hpq : p ∣ q := dvd_trans hpk hkq
      exact hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpq hpP)
    have hmod_ne : q % k ≠ 0 := fun hz => hndvd (Nat.dvd_of_mod_eq_zero hz)
    have hdiv := Nat.div_add_mod q k
    have hlt := Nat.mod_lt q (Nat.pos_of_ne_zero hk0)
    have hrew : q - 1 = (q % k - 1) + k * (q / k) := by omega
    have hlt' : q % k - 1 < k := by omega
    rw [hrew, Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero hk0),
      Nat.div_eq_of_lt (a := q % k - 1) hlt', zero_add]
  rw [stepWeight, stepWeight, ← sum_sub_distrib]
  by_cases h1 : 1 ∈ c.support
  · rw [sum_eq_single 1]
    · rw [Nat.div_one, Nat.div_one, ← mul_sub]
      have hq1 : (q : ℤ) - ((q - 1 : ℕ) : ℤ) = 1 := by omega
      rw [hq1, mul_one]
    · intro k hk hk1
      rw [← mul_sub, hdiff k hk hk1, sub_self, mul_zero]
    · intro h; exact absurd h1 h
  · rw [Finsupp.notMem_support_iff.mp h1, sum_eq_zero]
    intro k hk
    have hk1 : k ≠ 1 := fun h => h1 (h ▸ hk)
    rw [← mul_sub, hdiff k hk hk1, sub_self, mul_zero]

/-- **Universal finite-prime alphabet obstruction.** For any finite set `S` of primes with
`P_S = ∏_{p ∈ S} p`, every balanced `S`-supported integer producer has normalized slope strictly
greater than `1 + 1 / ((P_S + 1)(P_S + 2)) > 1`. -/
theorem finite_prime_alphabet_slope_gt_one {S : Finset ℕ} (hSp : ∀ p ∈ S, p.Prime)
    {c : ℕ →₀ ℤ} {m B : ℕ} (hc0 : c 0 = 0) (hbal : IsBalanced c)
    (hS : IsPrimeAlphabetSupported S c) (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r)
    (hm : 1 ≤ m) (hB : 2 ≤ B) (hwin : ∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) :
    1 + 1 / (((∏ p ∈ S, p : ℕ) : ℝ) + 1) / (((∏ p ∈ S, p : ℕ) : ℝ) + 2) <
      stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) := by
  set P := ∏ p ∈ S, p
  have hP_pos : 0 < P := prod_pos fun p hp => (hSp p hp).pos
  set q₀ := P + 1
  have hq0_ge : 2 ≤ q₀ := by omega
  have hcop : Nat.Coprime q₀ P := by simp [q₀]
  have hjump := stepWeight_coprime_jump hc0 hS hq0_ge hcop
  have hg1 : (m : ℤ) ≤ stepWeight c 1 := hwin 1 (mem_Ico.mpr ⟨le_rfl, hB⟩)
  have hexcess : (m : ℝ) + (if q₀ < B then (m : ℝ) else 0) ≤ (stepWeight c q₀ : ℝ) := by
    split_ifs with hqB
    · have hprev : (m : ℤ) ≤ stepWeight c (q₀ - 1) :=
        hwin (q₀ - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
      have : (2 * m : ℤ) ≤ stepWeight c q₀ := by omega
      have hR : (2 * (m : ℝ)) ≤ (stepWeight c q₀ : ℝ) := by exact_mod_cast this
      linarith
    · have hprev : 0 ≤ stepWeight c (q₀ - 1) := hstep (q₀ - 1)
      have : (m : ℤ) ≤ stepWeight c q₀ := by omega
      have hR : (m : ℝ) ≤ (stepWeight c q₀ : ℝ) := by exact_mod_cast this
      linarith
  have hhas := hasSum_stepWeight_div_pronic hc0 hbal
  set N := max B (q₀ + 1)
  have hpartial_le : ∑ j ∈ range N,
      (stepWeight c (j + 1) : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) ≤ stencilSlope c :=
    hhas.summable.sum_le_tsum (range N) (fun j _ => div_nonneg (by exact_mod_cast hstep _) (by positivity))
      |>.trans_eq hhas.tsum_eq
  have hbase_tel : ∑ j ∈ range (B - 1), (m : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) =
      (m : ℝ) * (1 - 1 / (B : ℝ)) := by
    have htel : ∀ R : ℕ, ∑ j ∈ range R, (1 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) =
        1 - 1 / ((R : ℝ) + 1) := by
      intro R
      induction R with
      | zero => simp
      | succ R ih =>
        rw [Finset.sum_range_succ, ih]
        have h1 : (R : ℝ) + 1 ≠ 0 := by positivity
        have h2 : (R : ℝ) + 2 ≠ 0 := by positivity
        push_cast; field_simp; ring
    have hmul : ∑ j ∈ range (B - 1), (m : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) =
        (m : ℝ) * ∑ j ∈ range (B - 1), (1 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
      rw [mul_sum]; refine sum_congr rfl fun j _ => by ring
    rw [hmul, htel (B - 1), Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_one]
    ring
  set base : ℕ → ℝ := fun j =>
    (if j + 1 < B then (m : ℝ) else 0) + (if j = P then (m : ℝ) else 0)
  have hpt : ∀ j ∈ range N,
      base j / (((j : ℝ) + 1) * ((j : ℝ) + 2)) ≤
        (stepWeight c (j + 1) : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    intro j _
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    by_cases hjP : j = P
    · subst hjP
      simp only [base, if_true]
      have hq : P + 1 = q₀ := rfl
      rw [hq, add_comm]
      exact hexcess
    · simp only [base, if_neg hjP, add_zero]
      split_ifs with hjB
      · exact_mod_cast hwin (j + 1) (mem_Ico.mpr ⟨by omega, hjB⟩)
      · exact_mod_cast hstep (j + 1)
  have hsum_base : ∑ j ∈ range N, base j / (((j : ℝ) + 1) * ((j : ℝ) + 2)) =
      (m : ℝ) * (1 - 1 / (B : ℝ)) + (m : ℝ) / (((P : ℝ) + 1) * ((P : ℝ) + 2)) := by
    simp only [base, add_div, sum_add_distrib]
    have h1 : ∑ j ∈ range N, (if j + 1 < B then (m : ℝ) else 0) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) =
        ∑ j ∈ range (B - 1), (m : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
      rw [← sum_subset (range_mono (show B - 1 ≤ N by omega))]
      · refine sum_congr rfl fun j hj => ?_
        have hj' : j + 1 < B := by have := mem_range.mp hj; omega
        rw [if_pos hj']
      · intro j _ hjnot
        have hj' : ¬ j + 1 < B := by have := mt mem_range.mpr hjnot; omega
        rw [if_neg hj', zero_div]
    have h2 : ∑ j ∈ range N, (if j = P then (m : ℝ) else 0) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) =
        (m : ℝ) / (((P : ℝ) + 1) * ((P : ℝ) + 2)) := by
      rw [sum_eq_single P]
      · simp
      · intro j _ hjP; simp [hjP]
      · intro h; exact absurd (mem_range.mpr (by omega : P < N)) h
    rw [h1, hbase_tel, h2]
  have hslope_ge : (m : ℝ) * (1 - 1 / (B : ℝ)) + (m : ℝ) / (((P : ℝ) + 1) * ((P : ℝ) + 2)) ≤
      stencilSlope c :=
    hsum_base ▸ (sum_le_sum hpt).trans hpartial_le
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (1 : ℝ) < B := by exact_mod_cast hB
  have h1B : 0 < 1 - 1 / (B : ℝ) := by rw [sub_pos, div_lt_one hB0]; exact hB1
  have h1B_lt : 1 - 1 / (B : ℝ) < 1 := by
    have : 0 < 1 / (B : ℝ) := by positivity
    linarith
  rw [lt_div_iff₀ (mul_pos hm0 h1B)]
  have hpos_term : 0 < (m : ℝ) / (((P : ℝ) + 1) * ((P : ℝ) + 2)) := by positivity
  have hstrict : (1 + 1 / ((P : ℝ) + 1) / ((P : ℝ) + 2)) * ((m : ℝ) * (1 - 1 / (B : ℝ))) <
      (m : ℝ) * (1 - 1 / (B : ℝ)) + (m : ℝ) / (((P : ℝ) + 1) * ((P : ℝ) + 2)) := by
    rw [div_div]
    have hrew : (1 + 1 / (((P : ℝ) + 1) * ((P : ℝ) + 2))) * ((m : ℝ) * (1 - 1 / (B : ℝ))) =
        (m : ℝ) * (1 - 1 / (B : ℝ)) +
          ((m : ℝ) / (((P : ℝ) + 1) * ((P : ℝ) + 2))) * (1 - 1 / (B : ℝ)) := by ring
    rw [hrew]
    linarith [mul_lt_of_lt_one_right hpos_term h1B_lt]
  exact hstrict.trans_le hslope_ge

/-- **Strict main-term gap for every individual stencil.** Because `c.support` is finite, every
balanced integer producer `(c, m, B)` is supported on a finite prime alphabet, so its normalized
vanishing-order slope is strictly greater than `1`. -/
theorem one_lt_normalized_slope_of_producer {c : ℕ →₀ ℤ} {m B : ℕ} (hc0 : c 0 = 0)
    (hbal : IsBalanced c) (hstep : ∀ r : ℕ, 0 ≤ stepWeight c r)
    (hm : 1 ≤ m) (hB : 2 ≤ B) (hwin : ∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) :
    1 < stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) := by
  classical
  set S := c.support.biUnion Nat.primeFactors
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => by
    obtain ⟨k, _, hp'⟩ := mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors hp'
  have hS : IsPrimeAlphabetSupported S c := fun k hk p hp hpk => by
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
    exact mem_biUnion.mpr ⟨k, hk, Nat.mem_primeFactors.mpr ⟨hp, hpk, hk0⟩⟩
  have hgt := finite_prime_alphabet_slope_gt_one hSp hc0 hbal hS hstep hm hB hwin
  have hpos : 0 < 1 / (((∏ p ∈ S, p : ℕ) : ℝ) + 1) / (((∏ p ∈ S, p : ℕ) : ℝ) + 2) := by positivity
  linarith

/-! ### Ceiling 3: Parity-blind / non-alternating multinomial obstruction (`> 31 / 30`) -/

private lemma sylvester_two_point_le_log {k : ℕ} (hk : 2 ≤ k) :
    Real.log 2 * ((1 % k : ℕ) : ℝ) +
        ((Real.log 3 - Real.log 2) / 2) * ((2 % k : ℕ) : ℝ) ≤ Real.log k := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.cast_one, mul_one]
  rcases eq_or_lt_of_le hk with rfl | hk3
  · simp
  · have h2 : 2 % k = 2 := Nat.mod_eq_of_lt hk3
    rw [h2, Nat.cast_ofNat]
    have hlog3 : Real.log 3 ≤ Real.log k :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hk3)
    linarith

private lemma sylvester_three_point_le_log {k : ℕ} (hk : 2 ≤ k) :
    Real.log 2 * ((1 % k : ℕ) : ℝ) +
        ((Real.log 3 - Real.log 2) / 2) * ((2 % k : ℕ) : ℝ) +
        ((Real.log 7 - Real.log 3) / 6) * ((6 % k : ℕ) : ℝ) ≤ Real.log k := by
  by_cases hk7 : 7 ≤ k
  · have m1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have m2 : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
    have m6 : 6 % k = 6 := Nat.mod_eq_of_lt (by omega)
    rw [m1, m2, m6]
    push_cast
    have hlog7 : Real.log 7 ≤ Real.log k :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hk7)
    linarith
  · have hk7' : k < 7 := lt_of_not_ge hk7
    interval_cases k
    · norm_num
    · norm_num
    · -- `k = 4`: `log 3 + (log 7 - log 3) / 3 = log(63) / 3 ≤ log(64) / 3 = log 4`
      norm_num
      have h63 : Real.log ((3 : ℝ) ^ 2 * 7) ≤ Real.log ((4 : ℝ) ^ 3) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow] at h63
      norm_num at h63
      linarith
    · -- `k = 5`: `log 3 + (log 7 - log 3) / 6 = log(1701) / 6 ≤ log(15625) / 6 = log 5`
      norm_num
      have h1701 : Real.log ((3 : ℝ) ^ 5 * 7) ≤ Real.log ((5 : ℝ) ^ 6) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow] at h1701
      norm_num at h1701
      linarith
    · -- `k = 6`: `log 3 ≤ log 6`
      norm_num
      have h36 : Real.log 3 ≤ Real.log 6 := Real.log_le_log (by norm_num) (by norm_num)
      linarith

private lemma numerical_sylvester_bounds :
    (31 / 30 : ℝ) < 2 * Real.log 2 ∧
      (31 / 30 : ℝ) < (3 / 5 : ℝ) * (Real.log 2 + Real.log 3) / 1 * (1 / 2) * 2 ∧
      (31 / 30 : ℝ) < (3 / 5 : ℝ) * ((Real.log 2 + Real.log 3) / 2) * 2 ∧
      (31 / 30 : ℝ) < (Real.log 2 / 2 + Real.log 3 / 3 + Real.log 7 / 6) := by
  have hexp31 : Real.exp 31 < (272 / 100 : ℝ) ^ 31 := by
    rw [show (31 : ℝ) = (31 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ (Real.exp_one_lt_d9.trans (by norm_num)) (Real.exp_pos 1).le (by norm_num)
  have h6 : (31 : ℝ) < 18 * (Real.log 2 + Real.log 3) := by
    have hpow : (272 / 100 : ℝ) ^ 31 < (6 : ℝ) ^ 18 := by norm_num
    have hlog := Real.log_lt_log (Real.exp_pos 31) (hexp31.trans hpow)
    rw [Real.log_exp, Real.log_pow, show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)] at hlog
    norm_num at hlog ⊢
    linarith
  have h504 : (31 : ℝ) < 5 * (3 * Real.log 2 + 2 * Real.log 3 + Real.log 7) := by
    have hpow : (272 / 100 : ℝ) ^ 31 < ((2 : ℝ) ^ 3 * 3 ^ 2 * 7) ^ 5 := by norm_num
    have hlog := Real.log_lt_log (Real.exp_pos 31) (hexp31.trans hpow)
    rw [Real.log_exp, Real.log_pow, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow] at hlog
    norm_num at hlog ⊢
    linarith
  exact ⟨by linarith [Real.log_two_gt_d9], by linarith, by linarith, by linarith⟩

/-- **Parity-blind / non-alternating multinomial ceiling (`> 31 / 30`).** Every balanced stencil
with `c(k) ≤ 0` for all `k ≥ 2` (no positive parity-cancellation numerator terms on `k ≥ 2`) has
normalized vanishing-order slope strictly exceeding `31 / 30 > 1`, uniformly in `B` and in the
number of primes. -/
theorem non_alternating_stencil_slope_gt {c : ℕ →₀ ℤ} {m B : ℕ} (hc0 : c 0 = 0)
    (hbal : IsBalanced c) (hnonpos : ∀ k : ℕ, 2 ≤ k → c k ≤ 0)
    (hm : 1 ≤ m) (hB : 2 ≤ B) (hwin : ∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) :
    (31 / 30 : ℝ) < stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (1 : ℝ) < B := by exact_mod_cast hB
  have h1B : 0 < 1 - 1 / (B : ℝ) := by rw [sub_pos, div_lt_one hB0]; exact hB1
  set S2 := c.support.filter fun k => 2 ≤ k
  have hstep_S2 : ∀ r : ℕ, (stepWeight c r : ℝ) =
      ∑ k ∈ S2, (-(c k : ℝ) / k) * ((r % k : ℕ) : ℝ) := by
    intro r
    rw [stepWeight_eq_sum_mod hc0 hbal r, ← sum_subset (filter_subset (fun k => 2 ≤ k) c.support)]
    intro k hk hknot
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hk1 : k = 1 := by
      simp only [mem_filter, hk, true_and, not_le] at hknot
      omega
    subst hk1
    rw [Nat.mod_one, Nat.cast_zero, mul_zero]
  have hslope_S2 : stencilSlope c = ∑ k ∈ S2, (-(c k : ℝ) / k) * Real.log k := by
    rw [stencilSlope, ← sum_subset (filter_subset (fun k => 2 ≤ k) c.support)]
    · refine sum_congr rfl fun k _ => by ring
    · intro k hk hknot
      have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
      have hk1 : k = 1 := by
        simp only [mem_filter, hk, true_and, not_le] at hknot
        omega
      subst hk1
      simp
  have hx_nonneg : ∀ k ∈ S2, 0 ≤ -(c k : ℝ) / k := by
    intro k hk
    have hk2 : 2 ≤ k := (mem_filter.mp hk).2
    have hck : (c k : ℝ) ≤ 0 := by exact_mod_cast hnonpos k hk2
    exact div_nonneg (by linarith) (by positivity)
  obtain ⟨hb_B2, _, hb_B6, hb_B7⟩ := numerical_sylvester_bounds
  rcases eq_or_lt_of_le hB with rfl | hB3
  · -- `B = 2`: `r = 1` gives `stencilSlope c ≥ m * log 2`
    have hw1 : (m : ℝ) ≤ (stepWeight c 1 : ℝ) := by
      exact_mod_cast hwin 1 (mem_Ico.mpr ⟨le_rfl, by norm_num⟩)
    rw [hstep_S2 1] at hw1
    have hle : (m : ℝ) * Real.log 2 ≤ stencilSlope c := by
      calc (m : ℝ) * Real.log 2
          ≤ (∑ k ∈ S2, (-(c k : ℝ) / k) * ((1 % k : ℕ) : ℝ)) * Real.log 2 :=
            mul_le_mul_of_nonneg_right hw1 (Real.log_pos one_lt_two).le
        _ = ∑ k ∈ S2, (-(c k : ℝ) / k) * (((1 % k : ℕ) : ℝ) * Real.log 2) := by
            rw [sum_mul]; refine sum_congr rfl fun _ _ => by ring
        _ ≤ ∑ k ∈ S2, (-(c k : ℝ) / k) * Real.log k := by
            refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (hx_nonneg k hk)
            have hk2 : 2 ≤ k := (mem_filter.mp hk).2
            rw [Nat.mod_eq_of_lt (by omega : 1 < k), Nat.cast_one, one_mul]
            exact Real.log_le_log (by norm_num) (by exact_mod_cast hk2)
        _ = stencilSlope c := hslope_S2.symm
    rw [lt_div_iff₀ (mul_pos hm0 h1B)]
    push_cast at hle ⊢
    have hlt' : (31 / 30 : ℝ) * ((m : ℝ) * (1 / 2)) < (m : ℝ) * Real.log 2 := by
      rw [show (31 / 30 : ℝ) * ((m : ℝ) * (1 / 2)) = (m : ℝ) * ((31 / 30) / 2) by ring]
      exact mul_lt_mul_of_pos_left (by linarith) hm0
    have heq' : (31 / 30 : ℝ) * ((m : ℝ) * (1 - 1 / 2)) = (31 / 30 : ℝ) * ((m : ℝ) * (1 / 2)) := by
      ring
    linarith
  · by_cases hB6 : B ≤ 6
    · -- `3 ≤ B ≤ 6`: `(w_1, w_2)` gives `stencilSlope c ≥ m * (log 2 + log 3) / 2`
      have hw1 : (m : ℝ) ≤ ∑ k ∈ S2, (-(c k : ℝ) / k) * ((1 % k : ℕ) : ℝ) := by
        rw [← hstep_S2 1]; exact_mod_cast hwin 1 (mem_Ico.mpr ⟨le_rfl, by omega⟩)
      have hw2 : (m : ℝ) ≤ ∑ k ∈ S2, (-(c k : ℝ) / k) * ((2 % k : ℕ) : ℝ) := by
        rw [← hstep_S2 2]; exact_mod_cast hwin 2 (mem_Ico.mpr ⟨by norm_num, hB3⟩)
      have hl2 : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
      have hl32 : 0 ≤ (Real.log 3 - Real.log 2) / 2 := by
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
        linarith
      have hle : (m : ℝ) * ((Real.log 2 + Real.log 3) / 2) ≤ stencilSlope c := by
        calc (m : ℝ) * ((Real.log 2 + Real.log 3) / 2)
            = Real.log 2 * m + ((Real.log 3 - Real.log 2) / 2) * m := by ring
          _ ≤ Real.log 2 * (∑ k ∈ S2, (-(c k : ℝ) / k) * ((1 % k : ℕ) : ℝ)) +
                ((Real.log 3 - Real.log 2) / 2) *
                  (∑ k ∈ S2, (-(c k : ℝ) / k) * ((2 % k : ℕ) : ℝ)) :=
              add_le_add (mul_le_mul_of_nonneg_left hw1 hl2) (mul_le_mul_of_nonneg_left hw2 hl32)
          _ = ∑ k ∈ S2, (-(c k : ℝ) / k) *
                (Real.log 2 * ((1 % k : ℕ) : ℝ) +
                  ((Real.log 3 - Real.log 2) / 2) * ((2 % k : ℕ) : ℝ)) := by
              rw [mul_sum, mul_sum, ← sum_add_distrib]
              exact sum_congr rfl fun _ _ => by ring
          _ ≤ ∑ k ∈ S2, (-(c k : ℝ) / k) * Real.log k :=
              sum_le_sum fun k hk =>
                mul_le_mul_of_nonneg_left (sylvester_two_point_le_log (mem_filter.mp hk).2)
                  (hx_nonneg k hk)
          _ = stencilSlope c := hslope_S2.symm
      have h1B_le : 1 - 1 / (B : ℝ) ≤ 5 / 6 := by
        have : (1 : ℝ) / 6 ≤ 1 / B :=
          one_div_le_one_div_of_le hB0 (by exact_mod_cast hB6)
        linarith
      rw [lt_div_iff₀ (mul_pos hm0 h1B)]
      have hstep1 : (31 / 30 : ℝ) * ((m : ℝ) * (1 - 1 / (B : ℝ))) ≤
          (m : ℝ) * ((31 / 30) * (5 / 6)) := by
        rw [show (31 / 30 : ℝ) * ((m : ℝ) * (1 - 1 / (B : ℝ))) =
          (m : ℝ) * ((31 / 30) * (1 - 1 / (B : ℝ))) by ring]
        exact mul_le_mul_of_nonneg_left (by linarith) hm0.le
      have hstep2 : (m : ℝ) * ((31 / 30) * (5 / 6)) <
          (m : ℝ) * ((Real.log 2 + Real.log 3) / 2) :=
        mul_lt_mul_of_pos_left (by linarith) hm0
      linarith
    · -- `B ≥ 7`: `(w_1, w_2, w_6)` gives `stencilSlope c ≥ m * log(504) / 6`
      have hB7 : 7 ≤ B := by omega
      have hw1 : (m : ℝ) ≤ ∑ k ∈ S2, (-(c k : ℝ) / k) * ((1 % k : ℕ) : ℝ) := by
        rw [← hstep_S2 1]; exact_mod_cast hwin 1 (mem_Ico.mpr ⟨le_rfl, by omega⟩)
      have hw2 : (m : ℝ) ≤ ∑ k ∈ S2, (-(c k : ℝ) / k) * ((2 % k : ℕ) : ℝ) := by
        rw [← hstep_S2 2]; exact_mod_cast hwin 2 (mem_Ico.mpr ⟨by norm_num, by omega⟩)
      have hw6 : (m : ℝ) ≤ ∑ k ∈ S2, (-(c k : ℝ) / k) * ((6 % k : ℕ) : ℝ) := by
        rw [← hstep_S2 6]; exact_mod_cast hwin 6 (mem_Ico.mpr ⟨by norm_num, hB7⟩)
      have hl2 : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
      have hl32 : 0 ≤ (Real.log 3 - Real.log 2) / 2 := by
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
        linarith
      have hl73 : 0 ≤ (Real.log 7 - Real.log 3) / 6 := by
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 7)
        linarith
      have hle : (m : ℝ) * (Real.log 2 / 2 + Real.log 3 / 3 + Real.log 7 / 6) ≤ stencilSlope c := by
        calc (m : ℝ) * (Real.log 2 / 2 + Real.log 3 / 3 + Real.log 7 / 6)
            = Real.log 2 * m + ((Real.log 3 - Real.log 2) / 2) * m +
                ((Real.log 7 - Real.log 3) / 6) * m := by ring
          _ ≤ Real.log 2 * (∑ k ∈ S2, (-(c k : ℝ) / k) * ((1 % k : ℕ) : ℝ)) +
                ((Real.log 3 - Real.log 2) / 2) *
                  (∑ k ∈ S2, (-(c k : ℝ) / k) * ((2 % k : ℕ) : ℝ)) +
                ((Real.log 7 - Real.log 3) / 6) *
                  (∑ k ∈ S2, (-(c k : ℝ) / k) * ((6 % k : ℕ) : ℝ)) :=
              add_le_add
                (add_le_add (mul_le_mul_of_nonneg_left hw1 hl2)
                  (mul_le_mul_of_nonneg_left hw2 hl32))
                (mul_le_mul_of_nonneg_left hw6 hl73)
          _ = ∑ k ∈ S2, (-(c k : ℝ) / k) *
                (Real.log 2 * ((1 % k : ℕ) : ℝ) +
                  ((Real.log 3 - Real.log 2) / 2) * ((2 % k : ℕ) : ℝ) +
                  ((Real.log 7 - Real.log 3) / 6) * ((6 % k : ℕ) : ℝ)) := by
              rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
              exact sum_congr rfl fun _ _ => by ring
          _ ≤ ∑ k ∈ S2, (-(c k : ℝ) / k) * Real.log k :=
              sum_le_sum fun k hk =>
                mul_le_mul_of_nonneg_left (sylvester_three_point_le_log (mem_filter.mp hk).2)
                  (hx_nonneg k hk)
          _ = stencilSlope c := hslope_S2.symm
      have h1B_lt : 1 - 1 / (B : ℝ) < 1 := by
        have : 0 < 1 / (B : ℝ) := by positivity
        linarith
      rw [lt_div_iff₀ (mul_pos hm0 h1B)]
      have hstep1 : (31 / 30 : ℝ) * ((m : ℝ) * (1 - 1 / (B : ℝ))) < (m : ℝ) * (31 / 30) := by
        rw [show (31 / 30 : ℝ) * ((m : ℝ) * (1 - 1 / (B : ℝ))) =
          (m : ℝ) * ((31 / 30) * (1 - 1 / (B : ℝ))) by ring]
        exact mul_lt_mul_of_pos_left (by linarith) hm0
      have hstep2 : (m : ℝ) * (31 / 30) <
          (m : ℝ) * (Real.log 2 / 2 + Real.log 3 / 3 + Real.log 7 / 6) :=
        mul_lt_mul_of_pos_left hb_B7 hm0
      linarith

/-- **Sign-alternation necessity.** Any balanced integer stencil reaching normalized slope
`≤ 31 / 30` must have both positive and negative coefficients on `k ≥ 2`. -/
theorem exists_sign_alternation_of_slope_le {c : ℕ →₀ ℤ} {m B : ℕ} (hc0 : c 0 = 0)
    (hbal : IsBalanced c) (hm : 1 ≤ m) (hB : 2 ≤ B)
    (hwin : ∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r)
    (hslope : stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) ≤ 31 / 30) :
    (∃ k₁ : ℕ, 2 ≤ k₁ ∧ 0 < c k₁) ∧ (∃ k₂ : ℕ, 2 ≤ k₂ ∧ c k₂ < 0) := by
  refine ⟨?_, ?_⟩
  · by_contra! hnonpos
    exact absurd hslope (not_le_of_gt (non_alternating_stencil_slope_gt hc0 hbal hnonpos hm hB hwin))
  · by_contra! hnonneg
    have hw1 : (m : ℝ) ≤ (stepWeight c 1 : ℝ) := by
      exact_mod_cast hwin 1 (mem_Ico.mpr ⟨le_rfl, hB⟩)
    rw [stepWeight_eq_sum_mod hc0 hbal 1] at hw1
    have hle0 : ∑ k ∈ c.support, (-(c k : ℝ) / k) * ((1 % k : ℕ) : ℝ) ≤ 0 := by
      refine sum_nonpos fun k hk => ?_
      have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
      have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      rcases eq_or_lt_of_le hk1 with rfl | hk2
      · simp
      · have hck : 0 ≤ (c k : ℝ) := by exact_mod_cast hnonneg k hk2
        have h1 : -(c k : ℝ) / k ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        exact mul_nonpos_of_nonpos_of_nonneg h1 (Nat.cast_nonneg _)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    linarith

#print axioms forall_stencilDen_dvd_stencilNum_iff
#print axioms psi_le_of_stepWeight_producer
#print axioms single_prime_hecke_slope_ge_two_log_two
#print axioms psi_le_of_twoThreeStencil
#print axioms finite_prime_alphabet_slope_gt_one
#print axioms one_lt_normalized_slope_of_producer
#print axioms non_alternating_stencil_slope_gt
#print axioms exists_sign_alternation_of_slope_le

end GaloisForLFunctions.ArithmeticKreinLangerTheory
