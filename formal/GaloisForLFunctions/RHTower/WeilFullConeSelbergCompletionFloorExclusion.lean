import GaloisForLFunctions.RHTower.WeilPositivitySparsePrimeFloor
import GaloisForLFunctions.RHTower.SelbergTruncatedVonMangoldtKreinCompletion

/-!
# Selberg completions with smooth-supported mollifiers are not Weil-positive

For a weight `w : ℕ → ℝ` the Selberg-weighted von Mangoldt function is
`Λ_w(n) = ∑_{d ∣ n} μ(d) w(d) log(n/d)`, with Dirichlet series `-(∑ μ(d) w(d) d^{-s}) ζ'(s)`.
With `w = 1` on `[1, X]` it agrees with `Λ` below `X` and at every prime, so it is a Krein
completion of the level-`a` Weil form for `X = ⌊e^{2a}⌋`.

**Theorem** (`not_weilPositiveFull_selbergWeightedVonMangoldt`).  Suppose `w(1) > 0` and, for some
`Y`, `w(d) = 0` at every `d ≥ 2` whose prime factors all exceed `Y`.  This holds whenever `w` has
finite support, and whenever `w` is supported on `Y`-smooth numbers.  Then `Λ_w` is not full-cone
Weil-positive for the archimedean datum of `ζ`.

**Proof.**
* A divisor `d ≥ 2` of an integer `n` whose prime factors all exceed `Y` has the same property, so
  `w(d) = 0`.  Hence `Λ_w(n) = w(1) log n ≥ w(1) log 2` on every such `n ≥ 2`
  (`selbergWeightedVonMangoldt_eq_of_rough`).
* A positive floor on the squarefree integers built from the primes `> Y` is excluded
  (`not_floor_on_rough_squarefree`).  The resonator is `1_{m ∣ N}` with `N` a product of
  `⌊b²/(3 log b)⌋` primes in `(b², b³]`, so that `log N ≤ b²` while the resonance product is at
  least `b⁶`.

So the finite-mollifier Selberg completions of every level `a` lie outside the full Weil cone,
unconditionally.  By the unconditional criterion for mollified completions, the one-sided bound
`θ'(t) + Re(ζ'(½+it) M(½+it)) ≥ 0` for all `t` fails for every finite mollifier `M` with
`M(1) = 0`, `M'(1) = 1` and positive constant term.
-/

open Finset Filter

namespace RHTower
namespace SelbergCompletionFloor

open PrimorialResonance CramerModel RoughRandomPrimes SparsePrimeFloor

/-- **No producer has a positive floor on the squarefree integers built from the primes `> Y`.** -/
theorem not_floor_on_rough_squarefree {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {c : ℝ}
    (hc : 0 < c) (Y : ℕ)
    (hfloor : ∀ n, 2 ≤ n → Squarefree n → (∀ p, p.Prime → p ∣ n → Y < p) → c ≤ lam n) :
    False := by
  obtain ⟨C₀, hC⟩ := floor_resonance_inequality (weilPositive_of_weilPositiveFull hW)
  obtain ⟨b, hcard, hsix, hbig, hb3, hbY⟩ := (eventually_card_window_ge.and
    (eventually_six_log_le.and ((eventually_ge_atTop ⌈(1 + |C₀| + 2 * c) / c⌉₊).and
      ((eventually_ge_atTop 3).and (eventually_ge_atTop Y))))).exists
  have hceil : (1 + |C₀| + 2 * c) / c ≤ (b : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hbig)
  have hbr : (3 : ℝ) ≤ b := by exact_mod_cast hb3
  have hl : 0 < Real.log b := Real.log_pos (by linarith)
  have hKle : primeCount b ≤ (window b).card := Nat.floor_le_of_le hcard
  obtain ⟨S, hSsub, hScard⟩ := exists_subset_card_eq hKle
  have hS : ∀ p ∈ S, p.Prime := fun p hp => (mem_window (hSsub hp)).1
  set N := ∏ p ∈ S, p with hNdef
  have hN : N ≠ 0 := prod_ne_zero_iff.mpr fun p hp => (hS p hp).ne_zero
  have hsq : Squarefree N := squarefree_prod_primes hS
  -- the floor holds on every divisor `n ≥ 2` of `N`
  have hlow : ∀ n ∈ N.divisors, 2 ≤ n → c ≤ lam n := by
    intro n hn h2
    have hdn := Nat.dvd_of_mem_divisors hn
    refine hfloor n h2 (hsq.squarefree_of_dvd hdn) fun q hq hqn => ?_
    have hqS := mem_of_prime_dvd_prod hS hq (hqn.trans hdn)
    have hq2 : b ^ 2 < q := (mem_window (hSsub hqS)).2.1
    have hbb : b ≤ b ^ 2 := Nat.le_self_pow (by norm_num) b
    omega
  have hineq : 2 * c * (setProduct S - 1) ≤ Real.log N + C₀ := hC S hS c hc.le hlow
  -- `log N ≤ b²`
  have hlogN : Real.log N ≤ (b : ℝ) ^ 2 := by
    rw [hNdef, Nat.cast_prod, Real.log_prod (fun p hp => by
      exact_mod_cast (hS p hp).ne_zero)]
    calc ∑ p ∈ S, Real.log (p : ℝ) ≤ ∑ _p ∈ S, 3 * Real.log b := by
          refine sum_le_sum fun p hp => ?_
          obtain ⟨hpr, -, hp3⟩ := mem_window (hSsub hp)
          calc Real.log (p : ℝ) ≤ Real.log ((b : ℝ) ^ 3) :=
                Real.log_le_log (by exact_mod_cast hpr.pos) (by exact_mod_cast hp3)
            _ = 3 * Real.log b := by rw [Real.log_pow]; norm_num
      _ = (primeCount b : ℝ) * (3 * Real.log b) := by rw [sum_const, hScard, nsmul_eq_mul]
      _ ≤ (b : ℝ) ^ 2 := by
          have := Nat.floor_le (show 0 ≤ (b : ℝ) ^ 2 / (3 * Real.log b) by positivity)
          unfold primeCount
          rw [le_div_iff₀ (by positivity)] at this
          linarith
  -- the resonance product is at least `b⁶`
  have hQ : ((b : ℝ) ^ 2) ^ 3 ≤ setProduct S := by
    have hY : ∀ p ∈ S, (p : ℝ) ≤ (b : ℝ) ^ 3 := fun p hp => by
      exact_mod_cast (mem_window (hSsub hp)).2.2
    refine le_trans ?_ (exp_le_setProduct hS hY)
    rw [hScard]
    calc ((b : ℝ) ^ 2) ^ 3 = Real.exp (6 * Real.log b) := by
          rw [show (6 : ℝ) * Real.log b = Real.log ((b : ℝ) ^ 6) by rw [Real.log_pow]; norm_num,
            Real.exp_log (by positivity)]; ring
      _ ≤ Real.exp ((primeCount b : ℝ) * ((b : ℝ) ^ 3) ^ (-(1 / 2 : ℝ)) / 4) :=
          Real.exp_le_exp.mpr hsix
  -- `2c(b⁶ - 1) > b² + C₀` contradicts the resonance inequality
  have hcb : 1 + |C₀| + 2 * c ≤ c * b := by
    rw [div_le_iff₀ hc] at hceil; linarith
  have hb2 : (1 : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith
  have hb5 : (b : ℝ) ^ 2 ≤ (b : ℝ) ^ 5 := by
    have : (b : ℝ) ^ 5 = (b : ℝ) ^ 2 * (b : ℝ) ^ 3 := by ring
    rw [this]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))
  have hbig6 : (b : ℝ) ^ 2 + |C₀| + 2 * c ≤ c * (b : ℝ) ^ 6 := by
    have h1 : (1 + |C₀| + 2 * c) * (b : ℝ) ^ 5 ≤ c * b * (b : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_right hcb (by positivity)
    have h2 : (b : ℝ) ^ 2 + |C₀| + 2 * c ≤ (1 + |C₀| + 2 * c) * (b : ℝ) ^ 5 := by
      have hb51 : (1 : ℝ) ≤ (b : ℝ) ^ 5 := hb2.trans hb5
      nlinarith [abs_nonneg C₀]
    calc (b : ℝ) ^ 2 + |C₀| + 2 * c ≤ (1 + |C₀| + 2 * c) * (b : ℝ) ^ 5 := h2
      _ ≤ c * b * (b : ℝ) ^ 5 := h1
      _ = c * (b : ℝ) ^ 6 := by ring
  have hQc : 2 * c * (((b : ℝ) ^ 2) ^ 3 - 1) ≤ 2 * c * (setProduct S - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hpow6 : ((b : ℝ) ^ 2) ^ 3 = (b : ℝ) ^ 6 := by ring
  rw [hpow6] at hQc
  have hC₀ : C₀ ≤ |C₀| := le_abs_self C₀
  linarith [abs_nonneg C₀]

/-- A divisor `d ≥ 2` of a positive integer whose prime factors all exceed `Y` has a prime factor
`> Y`, and every prime factor of `d` exceeds `Y`. -/
theorem rough_of_dvd {Y n d : ℕ} (hrough : ∀ p, p.Prime → p ∣ n → Y < p) (hd : d ∣ n) :
    ∀ p, p.Prime → p ∣ d → Y < p := fun p hp hpd => hrough p hp (hpd.trans hd)

/-- **Selberg weights on rough integers.**  If `w` vanishes at every `d ≥ 2` whose prime factors all
exceed `Y`, then `Λ_w(n) = w(1) log n` at every `n ≥ 1` whose prime factors all exceed `Y`. -/
theorem selbergWeightedVonMangoldt_eq_of_rough {w : ℕ → ℝ} {Y n : ℕ}
    (hw : ∀ d, 2 ≤ d → (∀ p, p.Prime → p ∣ d → Y < p) → w d = 0) (hn : 1 ≤ n)
    (hrough : ∀ p, p.Prime → p ∣ n → Y < p) :
    selbergWeightedVonMangoldt w n = w 1 * Real.log n := by
  unfold selbergWeightedVonMangoldt
  have hn0 : n ≠ 0 := by omega
  rw [Finset.sum_eq_single (n, 1)]
  · simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul]
    ring
  · intro x hx hne
    obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hx2 : x.2 ∣ n := Dvd.intro_left _ hmul
    have hx2pos : 0 < x.2 := Nat.pos_of_dvd_of_pos hx2 (by omega)
    by_cases h1 : x.2 = 1
    · exfalso
      apply hne
      have : x.1 = n := by rw [h1, mul_one] at hmul; exact hmul
      exact Prod.ext this h1
    · have h2 : 2 ≤ x.2 := by omega
      rw [hw x.2 h2 (rough_of_dvd hrough hx2), mul_zero, mul_zero]
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one n, hn0⟩) h

/-- **Selberg completions with smooth-supported mollifiers are not Weil-positive.**  If `w(1) > 0`
and `w` vanishes at every `d ≥ 2` whose prime factors all exceed some `Y` (for instance, `w` of
finite support, or supported on `Y`-smooth numbers), then `Λ_w = (μ w) ⋆ log` is not full-cone
Weil-positive.  Unconditional: no hypothesis on the zeros of `ζ` is used. -/
theorem not_weilPositiveFull_selbergWeightedVonMangoldt {w : ℕ → ℝ} (hw1 : 0 < w 1) (Y : ℕ)
    (hw : ∀ d, 2 ≤ d → (∀ p, p.Prime → p ∣ d → Y < p) → w d = 0) :
    ¬ WeilPositiveFull (selbergWeightedVonMangoldt w) := by
  intro hW
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine not_floor_on_rough_squarefree hW (c := w 1 * Real.log 2) (by positivity) Y ?_
  intro n hn _ hrough
  rw [selbergWeightedVonMangoldt_eq_of_rough hw (by omega) hrough]
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by norm_num) (by exact_mod_cast hn)) hw1.le

/-- **Finite mollifiers.**  A Selberg weight with `w(1) > 0` and `w(d) = 0` for `d > Y` gives a
weight system outside the full Weil cone. -/
theorem not_weilPositiveFull_selbergWeightedVonMangoldt_of_finite {w : ℕ → ℝ} (hw1 : 0 < w 1)
    (Y : ℕ) (hw : ∀ d, Y < d → w d = 0) :
    ¬ WeilPositiveFull (selbergWeightedVonMangoldt w) := by
  refine not_weilPositiveFull_selbergWeightedVonMangoldt hw1 Y fun d hd hrough => hw d ?_
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
  exact (hrough p hp hpd).trans_le (Nat.le_of_dvd (by omega) hpd)

/-- **The level-wise Selberg completions are never full-cone producers.**  For every aperture
cutoff `X` and every finite weight `w` with `w = 1` on `[1, X]` (so that `Λ_w = Λ` on `[0, X]` and at
every prime), `Λ_w` is not full-cone Weil-positive. -/
theorem not_weilPositiveFull_selbergCompletion {w : ℕ → ℝ} {X : ℕ}
    (hwX : ∀ d, 1 ≤ d → d ≤ X → w d = 1) (hX : 1 ≤ X) (Y : ℕ) (hw : ∀ d, Y < d → w d = 0) :
    ¬ WeilPositiveFull (selbergWeightedVonMangoldt w) :=
  not_weilPositiveFull_selbergWeightedVonMangoldt_of_finite
    (by rw [hwX 1 le_rfl hX]; norm_num) Y hw

end SelbergCompletionFloor

end RHTower
