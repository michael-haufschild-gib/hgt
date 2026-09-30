import GaloisForLFunctions.RHTower.WeilPositivityPrimorialResonance

/-!
# Random integer prime systems are almost surely not Weil-positive

Let `X_n` (`n ∈ ℕ`) be random variables with values in `[0, 1]`, pairwise independent on the
squarefree integers, and suppose
`E X_n ≥ c / log n` for every squarefree `n ≥ 3`.  The model case is Cramér's: `X_n` is the
indicator of the event `n ∈ M` for a random set `M` with `P(n ∈ M) = 1 / log n`, so that
`lam(n) = X_n log n` is the random von Mangoldt weight.

**Theorem** (`ae_not_weilPositiveFull_of_random`, `ae_not_weilPositiveFull_cramer`).  Almost surely,
no weights that agree with `X_n log n` on the squarefree integers are full-cone Weil-positive for
the archimedean datum of `ζ`.  This covers the Beurling von Mangoldt function of Cramér's random
primes, whose values at proper powers are not independent.  Only pairwise independence on the
squarefree integers is used.

The primorial resonance sum `S_y = ∑_{n ∣ y#, n ≥ 2} lam(n) n^{-1/2} d(y#/n)` obeys
`2 S_y ≤ (log y# + C₀) d(y#)` for every Weil-positive system (`weil_divisor_resonance_bound`).  For
the random system:
* `E S_y ≥ c 2^{π(y)} (P_y - 2)`, where `P_y = ∏_{p ≤ y} (1 + p^{-1/2}/2)`, since the convolution
  `n^{-1/2} ⋆ d` is multiplicative;
* `Var S_y ≤ (log y#)² 4^{π(y)} P_y` by pairwise independence;
* `P_y ≥ y³` for large `y` by Chebyshev's bound for `θ`.

Chebyshev's inequality makes each event `{2 S_y ≤ (log y# + K) d(y#)}` have probability at most
`16 (log 4)² y² / (c² P_y)`, which tends to zero.  A countable union over integer `K` finishes the
proof.
-/

open Finset Filter MeasureTheory ProbabilityTheory

namespace RHTower
namespace CramerModel

open PrimorialResonance

/-! ## Deterministic estimates at a primorial -/

theorem eventually_mul_log_le_primeRpowLower {a : ℝ} (ha1 : a < 1) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, K * Real.log x ≤ primeRpowLower a x := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < 1 - a := by linarith
  set K' := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  filter_upwards [eventually_log_add_one_le (show 0 < Real.log 2 / 4 by positivity),
    eventually_sqrt_mul_log_le (show 0 < Real.log 2 / 8 by positivity),
    eventually_log_sq_le hb (show 0 < Real.log 2 / (8 * K') by positivity),
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
  have hfin : K' * Real.log x ≤ Real.log 2 / 8 * x ^ (1 - a) / Real.log x := by
    rw [le_div_iff₀ hlx]
    have h3' : Real.log x ^ 2 * (8 * K') ≤ Real.log 2 * x ^ (1 - a) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h3
      · nlinarith
    nlinarith
  have hKK : K * Real.log x ≤ K' * Real.log x :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hlx.le
  linarith

theorem card_divisors_div_le {N n : ℕ} (hN : N ≠ 0) (hn : n ∣ N) :
    ((N / n).divisors.card : ℝ) ≤ N.divisors.card := by
  exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hN (Nat.div_dvd_of_dvd hn))

/-- Dropping the divisors `1` and `2` costs at most `2 d(N)`. -/
theorem resonanceMass_le_sum_three_le (a : ℝ) (ha : 0 ≤ a) {N : ℕ} (hN : N ≠ 0) :
    resonanceMass a N - 2 * N.divisors.card ≤
      ∑ n ∈ N.divisors with 3 ≤ n, (n : ℝ) ^ (-a) * ((N / n).divisors.card : ℝ) := by
  rw [resonanceMass_apply, ← sum_filter_add_sum_filter_not N.divisors (fun n => 3 ≤ n)]
  have hsmall : ∑ n ∈ N.divisors with ¬ 3 ≤ n, (n : ℝ) ^ (-a) * ((N / n).divisors.card : ℝ) ≤
      2 * N.divisors.card := by
    have hsub : N.divisors.filter (fun n => ¬ 3 ≤ n) ⊆ {1, 2} := by
      intro m hm
      obtain ⟨hd, h3⟩ := mem_filter.mp hm
      have := Nat.pos_of_mem_divisors hd
      simp only [mem_insert, mem_singleton]
      omega
    calc ∑ n ∈ N.divisors with ¬ 3 ≤ n, (n : ℝ) ^ (-a) * ((N / n).divisors.card : ℝ)
        ≤ ∑ n ∈ N.divisors with ¬ 3 ≤ n, (N.divisors.card : ℝ) := by
          refine sum_le_sum fun n hn => ?_
          obtain ⟨hd, -⟩ := mem_filter.mp hn
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_mem_divisors hd
          have hr : (n : ℝ) ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
          have hr0 : 0 ≤ (n : ℝ) ^ (-a) := Real.rpow_nonneg (by linarith) _
          calc (n : ℝ) ^ (-a) * ((N / n).divisors.card : ℝ)
              ≤ 1 * (N.divisors.card : ℝ) :=
                mul_le_mul hr (card_divisors_div_le hN (Nat.dvd_of_mem_divisors hd))
                  (Nat.cast_nonneg _) zero_le_one
            _ = N.divisors.card := one_mul _
      _ = ((N.divisors.filter (fun n => ¬ 3 ≤ n)).card : ℝ) * N.divisors.card := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 * N.divisors.card := by
          have hc : (N.divisors.filter (fun n => ¬ 3 ≤ n)).card ≤ 2 :=
            (card_le_card hsub).trans (card_le_two)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)
  linarith

/-- `∏_{p ≤ y} (2 + x_p) = 2^{π(y)} ∏_{p ≤ y} (1 + x_p/2)`. -/
theorem prod_two_add_eq (y : ℕ) (x : ℕ → ℝ) :
    ∏ p ∈ y.primesLE, (2 + x p) = 2 ^ y.primesLE.card * ∏ p ∈ y.primesLE, (1 + x p / 2) := by
  rw [← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun _ _ => by ring

/-- The primorial resonance product `P_y = ∏_{p ≤ y} (1 + p^{-1/2}/2)`. -/
noncomputable def resonanceProduct (y : ℕ) : ℝ := ∏ p ∈ y.primesLE, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2)

theorem one_le_resonanceProduct (y : ℕ) : 1 ≤ resonanceProduct y :=
  one_le_prod fun p _ => by
    have := Real.rpow_nonneg (Nat.cast_nonneg p) (-(1 / 2 : ℝ))
    linarith

theorem resonanceMass_half_primorial (y : ℕ) :
    resonanceMass (1 / 2) (primorial y) = 2 ^ y.primesLE.card * resonanceProduct y := by
  rw [resonanceMass_primorial, prod_two_add_eq]; rfl

theorem resonanceMass_one_primorial_le (y : ℕ) :
    resonanceMass 1 (primorial y) ≤ 2 ^ y.primesLE.card * resonanceProduct y := by
  rw [resonanceMass_primorial, prod_two_add_eq, resonanceProduct]
  refine mul_le_mul_of_nonneg_left (prod_le_prod (fun p _ => ?_) fun p hp => ?_) (by positivity)
  · have := Real.rpow_nonneg (Nat.cast_nonneg p) (-1 : ℝ); linarith
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le
    have : (p : ℝ) ^ (-1 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
    linarith

theorem exp_primeRpowLower_le_resonanceProduct {y : ℕ} (hy : 3 ≤ y) :
    Real.exp (primeRpowLower (1 / 2) y) ≤ resonanceProduct y :=
  (Real.exp_le_exp.mpr (primeRpowLower_le_sum (by norm_num) hy)).trans
    (exp_sum_le_prod_one_add (by norm_num) y)

/-! ## The random weight system -/

variable {Ω : Type*}

/-- The coefficient `log n · n^{-1/2} · d(y#/n)` of `X_n` in the primorial resonance sum. -/
noncomputable def resCoef (y n : ℕ) : ℝ :=
  Real.log n / Real.sqrt n * ((primorial y / n).divisors.card : ℝ)

/-- The primorial resonance sum `S_y = ∑_{n ∣ y#, n ≥ 2} log n · n^{-1/2} d(y#/n) X_n`. -/
noncomputable def resSum (X : ℕ → Ω → ℝ) (y : ℕ) (ω : Ω) : ℝ :=
  ∑ n ∈ (primorial y).divisors with 2 ≤ n, resCoef y n * X n ω

theorem resCoef_nonneg (y n : ℕ) : 0 ≤ resCoef y n := by
  unfold resCoef
  have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  positivity

/-- Weil positivity of weights agreeing with `log n · X_n(ω)` on the squarefree integers bounds
every primorial resonance sum. -/
theorem exists_resSum_le_of_weilPositiveFull (X : ℕ → Ω → ℝ) {ω : Ω} {lam : ℕ → ℝ}
    (hlam : ∀ n, Squarefree n → lam n = Real.log n * X n ω) (hW : WeilPositiveFull lam) :
    ∃ C₀ : ℝ, ∀ y : ℕ, 2 * resSum X y ω ≤
      (Real.log (primorial y) + C₀) * (primorial y).divisors.card := by
  obtain ⟨C₀, hC⟩ := weil_divisor_resonance_bound (weilPositive_of_weilPositiveFull hW)
  refine ⟨C₀, fun y => ?_⟩
  have h := hC (primorial y) (primorial_pos y)
  convert h using 3
  unfold resSum
  refine sum_congr rfl fun n hn => ?_
  have hsq : Squarefree n := (squarefree_primorial y).squarefree_of_dvd
    (Nat.dvd_of_mem_divisors (mem_filter.mp hn).1)
  rw [hlam n hsq]
  unfold resCoef
  ring

section Probability

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integrable_of_unit {X : Ω → ℝ} (hm : Measurable X) (hb : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) :
    Integrable X P :=
  Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hb ω])

theorem memLp_two_of_unit {X : Ω → ℝ} (hm : Measurable X) (hb : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1)
    (a : ℝ) : MemLp (fun ω => a * X ω) 2 P :=
  MemLp.of_bound (hm.const_mul a).aestronglyMeasurable (|a|) (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_mul]
    have : |X ω| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hb ω]
    calc |a| * |X ω| ≤ |a| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg a)
      _ = |a| := mul_one _)

theorem variance_le_one_of_unit {X : Ω → ℝ} (hm : Measurable X) (hb : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) :
    Var[X; P] ≤ 1 := by
  refine (variance_le_expectation_sq hm.aestronglyMeasurable).trans ?_
  calc ∫ ω, (X ^ 2) ω ∂P ≤ ∫ _ω, (1 : ℝ) ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => by
          simp only [Pi.pow_apply]; positivity) (integrable_const 1)
          (Eventually.of_forall fun ω => ?_)
        simp only [Pi.pow_apply]
        nlinarith [hb ω]
    _ = 1 := by simp

theorem integral_resSum (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1) (y : ℕ) :
    ∫ ω, resSum X y ω ∂P =
      ∑ n ∈ (primorial y).divisors with 2 ≤ n, resCoef y n * ∫ ω, X n ω ∂P := by
  unfold resSum
  rw [integral_finsetSum _ fun n _ => (integrable_of_unit (hm n) (hb n)).const_mul _]
  exact sum_congr rfl fun n _ => integral_const_mul _ _

/-- **Expectation of the resonance sum.**  If `E X_n ≥ c / log n` on squarefree `n ≥ 3`, then
`E S_y ≥ c (M_{1/2}(y#) - 2 d(y#))`. -/
theorem integral_resSum_ge (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1) {c : ℝ} (hc : 0 ≤ c)
    (hmean : ∀ n : ℕ, 3 ≤ n → Squarefree n → c / Real.log n ≤ ∫ ω, X n ω ∂P) (y : ℕ) :
    c * (resonanceMass (1 / 2) (primorial y) - 2 * (primorial y).divisors.card) ≤
      ∫ ω, resSum X y ω ∂P := by
  rw [integral_resSum X hm hb]
  set N := primorial y
  have hN : N ≠ 0 := (primorial_pos y).ne'
  have hsub : N.divisors.filter (fun n => 3 ≤ n) ⊆ N.divisors.filter (fun n => 2 ≤ n) := by
    intro m hm'; simp only [mem_filter] at hm' ⊢; exact ⟨hm'.1, by omega⟩
  have hE0 : ∀ n, 0 ≤ ∫ ω, X n ω ∂P := fun n => integral_nonneg fun ω => (hb n ω).1
  calc c * (resonanceMass (1 / 2) N - 2 * N.divisors.card)
      ≤ c * ∑ n ∈ N.divisors with 3 ≤ n,
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((N / n).divisors.card : ℝ) :=
        mul_le_mul_of_nonneg_left (resonanceMass_le_sum_three_le _ (by norm_num) hN) hc
    _ = ∑ n ∈ N.divisors with 3 ≤ n, resCoef y n * (c / Real.log n) := by
        rw [mul_sum]
        refine sum_congr rfl fun n hn => ?_
        obtain ⟨-, h3⟩ := mem_filter.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
        have hs : (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt n := by
          rw [Real.rpow_neg hn0.le, Real.sqrt_eq_rpow]; exact (one_div _).symm
        unfold resCoef
        rw [hs]
        field_simp
        rfl
    _ ≤ ∑ n ∈ N.divisors with 3 ≤ n, resCoef y n * ∫ ω, X n ω ∂P := by
        refine sum_le_sum fun n hn => ?_
        obtain ⟨hd, h3⟩ := mem_filter.mp hn
        have hsq : Squarefree n := (squarefree_primorial y).squarefree_of_dvd
          (Nat.dvd_of_mem_divisors hd)
        exact mul_le_mul_of_nonneg_left (hmean n h3 hsq) (resCoef_nonneg y n)
    _ ≤ ∑ n ∈ N.divisors with 2 ≤ n, resCoef y n * ∫ ω, X n ω ∂P :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
          mul_nonneg (resCoef_nonneg y n) (hE0 n)

theorem resCoef_sq_le {y n : ℕ} (hn : n ∈ (primorial y).divisors) :
    resCoef y n ^ 2 ≤ Real.log (primorial y) ^ 2 * (primorial y).divisors.card *
      ((n : ℝ) ^ (-(1 : ℝ)) * ((primorial y / n).divisors.card : ℝ)) := by
  set N := primorial y
  have hN : N ≠ 0 := (primorial_pos y).ne'
  have hd := Nat.dvd_of_mem_divisors hn
  have hn1 : 1 ≤ n := Nat.pos_of_mem_divisors hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hlN : Real.log n ≤ Real.log N :=
    Real.log_le_log hn0 (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hd)
  have hτ := card_divisors_div_le hN hd
  have hτ0 : (0 : ℝ) ≤ ((N / n).divisors.card : ℝ) := Nat.cast_nonneg _
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
  have hinv : (n : ℝ) ^ (-(1 : ℝ)) = 1 / n := by rw [Real.rpow_neg_one, one_div]
  have h1 : Real.log n ^ 2 ≤ Real.log N ^ 2 := pow_le_pow_left₀ hl0 hlN 2
  have h2 : ((N / n).divisors.card : ℝ) ^ 2 ≤
      (N.divisors.card : ℝ) * ((N / n).divisors.card : ℝ) := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hτ hτ0
  have hlhs : resCoef y n ^ 2 = Real.log n ^ 2 * ((N / n).divisors.card : ℝ) ^ 2 / n := by
    unfold resCoef
    rw [mul_pow, div_pow, hs]
    ring
  rw [hlhs, hinv, div_le_iff₀ hn0]
  calc Real.log n ^ 2 * ((N / n).divisors.card : ℝ) ^ 2
      ≤ Real.log N ^ 2 * ((N.divisors.card : ℝ) * ((N / n).divisors.card : ℝ)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = Real.log N ^ 2 * (N.divisors.card : ℝ) * (1 / n * ((N / n).divisors.card : ℝ)) * n := by
        field_simp

/-- **Variance of the resonance sum** for pairwise independent `[0,1]`-valued variables:
`Var S_y ≤ (log y#)² d(y#) M_1(y#)`. -/
theorem variance_resSum_le (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1)
    (hind : ∀ i j, i ≠ j → Squarefree i → Squarefree j → X i ⟂ᵢ[P] X j) (y : ℕ) :
    Var[resSum X y; P] ≤ Real.log (primorial y) ^ 2 * (primorial y).divisors.card *
      resonanceMass 1 (primorial y) := by
  set N := primorial y
  set D := N.divisors.filter (fun n => 2 ≤ n)
  have hfun : resSum X y = ∑ n ∈ D, fun ω => resCoef y n * X n ω := by
    funext ω; unfold resSum; rw [Finset.sum_apply]
  rw [hfun, IndepFun.variance_sum (fun n _ => memLp_two_of_unit (hm n) (hb n) _)
    (fun i hi j hj hij => (hind i j hij
      ((squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors (mem_filter.mp hi).1))
      ((squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors (mem_filter.mp hj).1))
      ).comp (measurable_const_mul _) (measurable_const_mul _))]
  have hterm : ∀ n ∈ D, Var[fun ω => resCoef y n * X n ω; P] ≤ resCoef y n ^ 2 := fun n _ => by
    rw [variance_const_mul]
    calc resCoef y n ^ 2 * Var[X n; P] ≤ resCoef y n ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (variance_le_one_of_unit (hm n) (hb n)) (sq_nonneg _)
      _ = resCoef y n ^ 2 := mul_one _
  refine (sum_le_sum hterm).trans ?_
  have hDsub : D ⊆ N.divisors := filter_subset _ _
  calc ∑ n ∈ D, resCoef y n ^ 2
      ≤ ∑ n ∈ D, Real.log N ^ 2 * N.divisors.card *
          ((n : ℝ) ^ (-(1 : ℝ)) * ((N / n).divisors.card : ℝ)) :=
        sum_le_sum fun n hn => resCoef_sq_le (hDsub hn)
    _ ≤ ∑ n ∈ N.divisors, Real.log N ^ 2 * N.divisors.card *
          ((n : ℝ) ^ (-(1 : ℝ)) * ((N / n).divisors.card : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hDsub fun n _ _ => by
          have := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 : ℝ))
          positivity
    _ = Real.log N ^ 2 * N.divisors.card * resonanceMass 1 N := by
        rw [← mul_sum, resonanceMass_apply]

end Probability

section Main

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Along the primorials the resonance product beats every power of `y` eventually: for all large
`y`, `P_y ≥ y^3`, hence the expectation of `S_y` dominates both the Weil bound and the standard
deviation. -/
theorem eventually_cube_le_resonanceProduct :
    ∀ᶠ y : ℕ in atTop, (y : ℝ) ^ 3 ≤ resonanceProduct y := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_mul_log_le_primeRpowLower (a := 1 / 2) (by norm_num) 3)
  filter_upwards [h, eventually_ge_atTop 3] with y hy hy3
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  calc (y : ℝ) ^ 3 = Real.exp (3 * Real.log y) := by
        rw [← Real.log_rpow hy0, Real.exp_log (by positivity)]; norm_cast
    _ ≤ Real.exp (primeRpowLower (1 / 2) y) := Real.exp_le_exp.mpr hy
    _ ≤ resonanceProduct y := exp_primeRpowLower_le_resonanceProduct hy3

theorem weil_bound_le_mean_aux {c K L y Py logN : ℝ} (hc : 0 < c) (hy1 : 1 ≤ y)
    (hA : (L + |K| + 2 * c) / c ≤ y) (hcube : y ^ 3 ≤ Py) (hlog : logN ≤ y * L) :
    logN + K ≤ c * (Py - 2) := by
  have h1 : L + |K| + 2 * c ≤ c * y := by
    have := (div_le_iff₀ hc).mp hA; linarith
  have hy0 : 0 ≤ y := by linarith
  have hy23 : y ^ 2 ≤ y ^ 3 := by
    have := mul_le_mul_of_nonneg_left hy1 (sq_nonneg y)
    calc y ^ 2 = y ^ 2 * 1 := (mul_one _).symm
      _ ≤ y ^ 2 * y := this
      _ = y ^ 3 := by ring
  have hcy : y * (L + |K| + 2 * c) ≤ c * y ^ 2 := by
    have := mul_le_mul_of_nonneg_left h1 hy0
    calc y * (L + |K| + 2 * c) ≤ y * (c * y) := this
      _ = c * y ^ 2 := by ring
  have hmix : y * L + (|K| + 2 * c) ≤ y * (L + |K| + 2 * c) := by
    have h0 : 0 ≤ |K| + 2 * c := by positivity
    have := mul_le_mul_of_nonneg_right hy1 h0
    linarith
  have hcP : c * y ^ 2 ≤ c * Py := mul_le_mul_of_nonneg_left (hy23.trans hcube) hc.le
  have hKa : K ≤ |K| := le_abs_self K
  linarith

theorem variance_ratio_aux {c ε L y Py logN V E q : ℝ} (hc : 0 < c) (hε : 0 < ε) (hq : 0 < q)
    (hy : 0 < y) (hV : V ≤ logN ^ 2 * q * (q * Py)) (hE : c * q * (Py - 2) ≤ E)
    (hPy4 : 4 ≤ Py) (hcube : y ^ 3 ≤ Py) (hB : 16 * L ^ 2 / (c ^ 2 * ε) ≤ y)
    (hlog0 : 0 ≤ logN) (hlog : logN ≤ y * L) :
    V ≤ ε * (E / 2) ^ 2 := by
  have hkey : 16 * L ^ 2 ≤ c ^ 2 * ε * y := by
    rw [div_le_iff₀ (by positivity)] at hB; linarith
  have hlog2 : logN ^ 2 ≤ y ^ 2 * L ^ 2 := by
    have := pow_le_pow_left₀ hlog0 hlog 2
    calc logN ^ 2 ≤ (y * L) ^ 2 := this
      _ = y ^ 2 * L ^ 2 := by ring
  have hPy0 : 0 < Py := by linarith
  have h16 : 16 * y ^ 2 * L ^ 2 ≤ ε * c ^ 2 * Py := by
    calc 16 * y ^ 2 * L ^ 2 = y ^ 2 * (16 * L ^ 2) := by ring
      _ ≤ y ^ 2 * (c ^ 2 * ε * y) := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = c ^ 2 * ε * y ^ 3 := by ring
      _ ≤ c ^ 2 * ε * Py := mul_le_mul_of_nonneg_left hcube (by positivity)
      _ = ε * c ^ 2 * Py := by ring
  have hE0 : 0 ≤ c * q * (Py - 2) := by
    have : 0 ≤ Py - 2 := by linarith
    positivity
  have hEsq : (c * q * (Py - 2)) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ hE0 hE 2
  have hPy2 : Py ^ 2 / 4 ≤ (Py - 2) ^ 2 := by nlinarith
  have hlow : c ^ 2 * q ^ 2 * Py ^ 2 / 16 ≤ (E / 2) ^ 2 := by
    have h5 : (c * q * (Py - 2)) ^ 2 = c ^ 2 * q ^ 2 * (Py - 2) ^ 2 := by ring
    have h6 : c ^ 2 * q ^ 2 * (Py ^ 2 / 4) ≤ c ^ 2 * q ^ 2 * (Py - 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hPy2 (by positivity)
    have h7 : (E / 2) ^ 2 = E ^ 2 / 4 := by ring
    rw [h7]
    nlinarith
  have hup : V ≤ y ^ 2 * L ^ 2 * (q ^ 2 * Py) := by
    calc V ≤ logN ^ 2 * q * (q * Py) := hV
      _ = logN ^ 2 * (q ^ 2 * Py) := by ring
      _ ≤ y ^ 2 * L ^ 2 * (q ^ 2 * Py) :=
        mul_le_mul_of_nonneg_right hlog2 (by positivity)
  have hmid : y ^ 2 * L ^ 2 * (q ^ 2 * Py) ≤ ε * (c ^ 2 * q ^ 2 * Py ^ 2 / 16) := by
    have := mul_le_mul_of_nonneg_right h16 (show 0 ≤ q ^ 2 * Py / 16 by positivity)
    calc y ^ 2 * L ^ 2 * (q ^ 2 * Py) = 16 * y ^ 2 * L ^ 2 * (q ^ 2 * Py / 16) := by ring
      _ ≤ ε * c ^ 2 * Py * (q ^ 2 * Py / 16) := this
      _ = ε * (c ^ 2 * q ^ 2 * Py ^ 2 / 16) := by ring
  calc V ≤ ε * (c ^ 2 * q ^ 2 * Py ^ 2 / 16) := hup.trans hmid
    _ ≤ ε * (E / 2) ^ 2 := mul_le_mul_of_nonneg_left hlow hε.le

theorem memLp_resSum (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1) (y : ℕ) : MemLp (resSum X y) 2 P := by
  have hfun : resSum X y = ∑ n ∈ (primorial y).divisors.filter (fun n => 2 ≤ n),
      fun ω => resCoef y n * X n ω := by
    funext ω; unfold resSum; rw [Finset.sum_apply]
  rw [hfun]
  exact memLp_finsetSum' _ fun n _ => memLp_two_of_unit (hm n) (hb n) _

/-- The primorial event: at a single large primorial the Weil bound fails except on a set of
probability at most `ε`. -/
theorem measure_resSum_le_le (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1)
    (hind : ∀ i j, i ≠ j → Squarefree i → Squarefree j → X i ⟂ᵢ[P] X j) {c : ℝ}
    (hc : 0 < c) (hmean : ∀ n : ℕ, 3 ≤ n → Squarefree n → c / Real.log n ≤ ∫ ω, X n ω ∂P)
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) {y : ℕ} (hyP : (y : ℝ) ^ 3 ≤ resonanceProduct y)
    (hy0 : 4 ≤ (y : ℝ)) (hyA : (Real.log 4 + |K| + 2 * c) / c ≤ y)
    (hyB : 16 * Real.log 4 ^ 2 / (c ^ 2 * ε) ≤ y) :
    P {ω | 2 * resSum X y ω ≤ (Real.log (primorial y) + K) * (primorial y).divisors.card} ≤
      ENNReal.ofReal ε := by
  have hτ : (((primorial y).divisors.card : ℕ) : ℝ) = 2 ^ y.primesLE.card :=
    card_divisors_primorial y
  have hq : (0 : ℝ) < 2 ^ y.primesLE.card := by positivity
  have hlogN := log_primorial_le y
  have hlogN0 : 0 ≤ Real.log (primorial y) := Real.log_natCast_nonneg _
  have hPy4 : 4 ≤ resonanceProduct y := by
    have : (4 : ℝ) ^ 3 ≤ (y : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hy0 3
    linarith
  have hE := integral_resSum_ge X hm hb hc.le hmean y (P := P)
  rw [resonanceMass_half_primorial, hτ] at hE
  have hE' : c * 2 ^ y.primesLE.card * (resonanceProduct y - 2) ≤ ∫ ω, resSum X y ω ∂P := by
    linarith
  have hKy := weil_bound_le_mean_aux hc (by linarith) hyA hyP hlogN
  have hEpos : 0 < ∫ ω, resSum X y ω ∂P := by
    have : 0 < c * 2 ^ y.primesLE.card * (resonanceProduct y - 2) := by
      have : 0 < resonanceProduct y - 2 := by linarith
      positivity
    linarith
  have hsub : {ω | 2 * resSum X y ω ≤ (Real.log (primorial y) + K) *
      (primorial y).divisors.card} ⊆
      {ω | (∫ ω, resSum X y ω ∂P) / 2 ≤ |resSum X y ω - ∫ ω, resSum X y ω ∂P|} := by
    intro ω h
    simp only [Set.mem_setOf_eq] at h ⊢
    rw [hτ] at h
    have h2 : 2 * resSum X y ω ≤ ∫ ω, resSum X y ω ∂P := by
      calc 2 * resSum X y ω ≤ (Real.log (primorial y) + K) * 2 ^ y.primesLE.card := h
        _ ≤ c * (resonanceProduct y - 2) * 2 ^ y.primesLE.card :=
          mul_le_mul_of_nonneg_right hKy hq.le
        _ ≤ ∫ ω, resSum X y ω ∂P := by linarith
    rw [abs_sub_comm, le_abs]
    left; linarith
  have hV := variance_resSum_le X hm hb hind y (P := P)
  rw [hτ] at hV
  have hV' : Var[resSum X y; P] ≤ Real.log (primorial y) ^ 2 * 2 ^ y.primesLE.card *
      (2 ^ y.primesLE.card * resonanceProduct y) :=
    hV.trans (mul_le_mul_of_nonneg_left (resonanceMass_one_primorial_le y) (by positivity))
  have hratio := variance_ratio_aux hc hε hq (by linarith) hV' hE' hPy4 hyP hyB hlogN0 hlogN
  have hcheb := meas_ge_le_variance_div_sq (memLp_resSum X hm hb y (P := P)) (half_pos hEpos)
  refine (measure_mono hsub).trans (hcheb.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [div_le_iff₀ (by positivity)]
  exact hratio

/-- **For a fixed constant `K`, the Weil resonance bound at every primorial is a null event.** -/
theorem measure_forall_resSum_le_eq_zero (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1)
    (hind : ∀ i j, i ≠ j → Squarefree i → Squarefree j → X i ⟂ᵢ[P] X j) {c : ℝ}
    (hc : 0 < c) (hmean : ∀ n : ℕ, 3 ≤ n → Squarefree n → c / Real.log n ≤ ∫ ω, X n ω ∂P)
    (K : ℝ) :
    P {ω | ∀ y : ℕ, 2 * resSum X y ω ≤
      (Real.log (primorial y) + K) * (primorial y).divisors.card} = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
  have hεr : (0 : ℝ) < ε := hε
  set A : ℝ := (Real.log 4 + |K| + 2 * c) / c
  set B : ℝ := 16 * Real.log 4 ^ 2 / (c ^ 2 * ε)
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨y, hyP, hy1⟩ := (eventually_cube_le_resonanceProduct.and
    (eventually_ge_atTop ⌈A + B + 4⌉₊)).exists
  have hceil : A + B + 4 ≤ (y : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hy1)
  refine (measure_mono fun ω hω => ?_).trans
    (measure_resSum_le_le X hm hb hind hc hmean K hεr hyP (by linarith) (by linarith)
      (by linarith))
  exact hω y

/-- **Random integer prime systems are almost surely not Weil-positive.**  Let `X_n` be random
variables with values in `[0, 1]`, pairwise independent on the squarefree integers, with
`E X_n ≥ c / log n` on the squarefree `n ≥ 3`.  If random weights `lam_ω` agree with `X_n log n` on
the squarefree integers (their values elsewhere are arbitrary), then almost surely `lam_ω` is not
full-cone Weil-positive for the archimedean datum of `ζ`.  The primorial resonance sum has mean of
size `2^{π(y)} ∏_{p ≤ y}(1 + p^{-1/2}/2)`, beyond every power of `y`, and variance smaller than the
square of the mean, while Weil positivity bounds it by `(log y# + C₀) 2^{π(y)}`. -/
theorem ae_not_weilPositiveFull_of_random (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1)
    (hind : ∀ i j, i ≠ j → Squarefree i → Squarefree j → X i ⟂ᵢ[P] X j) {c : ℝ}
    (hc : 0 < c) (hmean : ∀ n : ℕ, 3 ≤ n → Squarefree n → c / Real.log n ≤ ∫ ω, X n ω ∂P)
    (lam : Ω → ℕ → ℝ) (hlam : ∀ ω n, Squarefree n → lam ω n = Real.log n * X n ω) :
    ∀ᵐ ω ∂P, ¬ WeilPositiveFull (lam ω) := by
  rw [ae_iff]
  simp only [not_not]
  have hsub : {ω | WeilPositiveFull (lam ω)} ⊆
      ⋃ K : ℕ, {ω | ∀ y : ℕ, 2 * resSum X y ω ≤
        (Real.log (primorial y) + K) * (primorial y).divisors.card} := by
    intro ω hω
    obtain ⟨C₀, hC⟩ := exists_resSum_le_of_weilPositiveFull X (hlam ω) hω
    obtain ⟨K, hK⟩ := exists_nat_ge C₀
    refine Set.mem_iUnion.mpr ⟨K, fun y => (hC y).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  exact measure_mono_null hsub (measure_iUnion_null fun K =>
    measure_forall_resSum_le_eq_zero X hm hb hind hc hmean K)

/-- **Cramér's model.**  Let `X_n ∈ [0,1]` be pairwise independent with `E X_n = 1 / log n` for
`n ≥ 3` (the indicators of Cramér's random primes `M`).  Then almost surely neither the weights
`X_n log n` nor any weights agreeing with them on the squarefree integers (for instance the Beurling
von Mangoldt function `Λ_M`, with `Λ_M(m^k) = log m` for `m ∈ M`) are full-cone Weil-positive. -/
theorem ae_not_weilPositiveFull_cramer (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1)
    (hind : ∀ i j, i ≠ j → Squarefree i → Squarefree j → X i ⟂ᵢ[P] X j)
    (hmean : ∀ n : ℕ, 3 ≤ n → ∫ ω, X n ω ∂P = 1 / Real.log n)
    (lam : Ω → ℕ → ℝ) (hlam : ∀ ω n, Squarefree n → lam ω n = Real.log n * X n ω) :
    ∀ᵐ ω ∂P, ¬ WeilPositiveFull (lam ω) :=
  ae_not_weilPositiveFull_of_random X hm hb hind one_pos (fun n hn _ => (hmean n hn).ge) lam hlam

end Main

end CramerModel
end RHTower
