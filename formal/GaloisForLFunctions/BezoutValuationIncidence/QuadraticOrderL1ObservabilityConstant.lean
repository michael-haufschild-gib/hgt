import GaloisForLFunctions.BezoutValuationIncidence.FlatSelbergRowAndExactQuadraticSandwichOrder
import GaloisForLFunctions.BezoutValuationIncidence.PolynomialWindowTranslatedMomentTransfer

/-!
# The ℓ¹ observability constant has exact order `N²`

The inverse ℓ¹ inequality `(Σ_{d ≤ N} |c(d)|)² ≤ S_N Q_Sel(c)` holds with
`S_N = Σ_{q ≤ N} σ(q)²/φ(q)`, and it controls the window transfer of translated moments of every
degree. The constant has no logarithm:

* `σ(q) φ(q) ≤ q²` (a prime-power inequality, multiplicative), so `σ(q)²/φ(q) ≤ q (q/φ(q))³`;
* `(q/φ(q))³ = Π_{p ∣ q} (1 + x_p)`, `x_p = (p/(p-1))³ - 1`, expands over the subsets of the prime
  factors; counting the `q ≤ N` divisible by a product of primes gives
  `Σ_{q ≤ N} (q/φ(q))³ ≤ N Π_{p ≤ N} (1 + x_p/p) ≤ e^{19/2} N`, because
  `x_n/n ≤ 6/((n-1)(n-2))` telescopes for `n ≥ 3`;
* hence `S_N ≤ e^{19/2} N²`.

Conversely the row with all Selberg coordinates equal to one has `Σ_d c(d) = s(N!) = Φ(N)` and
`Q_Sel = Φ(N)`, so no constant below `Φ(N) ≥ N²/8 + N - (N/2) H_N` is admissible. The optimal
inverse ℓ¹ constant has exact order `N²`, and the degree-`m` window transfer of translated moments
holds with error `(e^{19/4} N √Q_Sel)^m` at every phase.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. `σ(q) φ(q) ≤ q²` -/

private theorem sigma_mul_totient_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((ArithmeticFunction.sigma 1 (p ^ k) : ℕ) : ℝ) * ((p ^ k).totient : ℝ) ≤ ((p ^ k : ℕ) : ℝ) ^ 2 := by
  rcases k with _ | j
  · simp
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hgeom : ((ArithmeticFunction.sigma 1 (p ^ (j + 1)) : ℕ) : ℝ) * ((p : ℝ) - 1) =
        (p : ℝ) ^ (j + 2) - 1 := by
      rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
      push_cast
      exact geom_sum_mul (p : ℝ) (j + 2)
    rw [Nat.totient_prime_pow_succ hp]
    push_cast [Nat.cast_sub hp.one_lt.le]
    have hpow : (1 : ℝ) ≤ (p : ℝ) ^ j := one_le_pow₀ hp1
    calc ((ArithmeticFunction.sigma 1 (p ^ (j + 1)) : ℕ) : ℝ) * ((p : ℝ) ^ j * ((p : ℝ) - 1))
        = (p : ℝ) ^ j * ((p : ℝ) ^ (j + 2) - 1) := by rw [← hgeom]; ring
      _ ≤ (p : ℝ) ^ j * (p : ℝ) ^ (j + 2) := by nlinarith
      _ = ((p : ℝ) ^ (j + 1)) ^ 2 := by ring

theorem sigma_mul_totient_le_sq (q : ℕ) :
    ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) * (q.totient : ℝ) ≤ (q : ℝ) ^ 2 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p k hp => exact_mod_cast sigma_mul_totient_prime_pow hp k
  | coprime a b _ _ hab ha hb =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hab, Nat.totient_mul hab]
    push_cast
    have h0 : 0 ≤ ((ArithmeticFunction.sigma 1 b : ℕ) : ℝ) * (b.totient : ℝ) := by positivity
    calc ((ArithmeticFunction.sigma 1 a : ℕ) : ℝ) * ((ArithmeticFunction.sigma 1 b : ℕ) : ℝ) *
          ((a.totient : ℝ) * (b.totient : ℝ))
        = (((ArithmeticFunction.sigma 1 a : ℕ) : ℝ) * (a.totient : ℝ)) *
          (((ArithmeticFunction.sigma 1 b : ℕ) : ℝ) * (b.totient : ℝ)) := by
          ring
      _ ≤ (a : ℝ) ^ 2 * (b : ℝ) ^ 2 := mul_le_mul ha hb h0 (sq_nonneg _)
      _ = ((a : ℝ) * b) ^ 2 := by ring

/-! ## §2. The cubed totient ratio -/

/-- `x_p = (p/(p-1))³ - 1`. -/
def totientRatioCubeExcess (p : ℕ) : ℝ := ((p : ℝ) / ((p : ℝ) - 1)) ^ 3 - 1

theorem totientRatioCubeExcess_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ totientRatioCubeExcess p := by
  unfold totientRatioCubeExcess
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  nlinarith [one_le_pow₀ (n := 3) h1]

theorem div_totient_eq_prod {q : ℕ} (hq : q ≠ 0) :
    (q : ℝ) / (q.totient : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors q
  have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
  have hpos : ∀ p ∈ q.primeFactors, ((p : ℝ) - 1) ≠ 0 := fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).one_lt
    have : (1 : ℝ) < p := by exact_mod_cast this
    linarith
  have hcast : (q.totient : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ) =
      (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have h' := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at h'
    rw [h']
    congr 1
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  rw [prod_div_distrib, eq_div_iff (prod_ne_zero_iff.mpr hpos), div_mul_eq_mul_div,
    div_eq_iff hφ, ← hcast]
  ring

theorem div_totient_cube_eq_sum_powerset {q : ℕ} (hq : q ≠ 0) :
    ((q : ℝ) / (q.totient : ℝ)) ^ 3 =
      ∑ t ∈ q.primeFactors.powerset, ∏ p ∈ t, totientRatioCubeExcess p := by
  rw [div_totient_eq_prod hq, ← prod_pow, ← prod_one_add]
  exact prod_congr rfl fun p _ => by unfold totientRatioCubeExcess; ring

/-- `x_n / n ≤ 6 / ((n-1)(n-2))` for `n ≥ 3`. -/
theorem totientRatioCubeExcess_div_le {n : ℕ} (hn : 3 ≤ n) :
    totientRatioCubeExcess n / n ≤ 6 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
  unfold totientRatioCubeExcess
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  rw [div_pow, div_sub_one (by positivity), div_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [mul_pos h1 h2, mul_pos (mul_pos h1 h2) h1]

theorem sum_Icc_six_div_le (M : ℕ) :
    ∑ n ∈ Icc 3 M, 6 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) ≤ 6 := by
  have key : ∀ M : ℕ, 2 ≤ M → ∑ n ∈ Icc 3 M, 6 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) =
      6 - 6 / ((M : ℝ) - 1) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => norm_num
    | succ M hM ih =>
      rw [sum_Icc_succ_top (by omega), ih]
      have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
      have e1 : ((M + 1 : ℕ) : ℝ) - 1 = M := by push_cast; ring
      have e2 : ((M + 1 : ℕ) : ℝ) - 2 = (M : ℝ) - 1 := by push_cast; ring
      rw [e1, e2]
      have h1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
      have h2 : (0 : ℝ) < (M : ℝ) := by linarith
      field_simp
      ring
  rcases Nat.lt_or_ge M 2 with hM | hM
  · have : Icc 3 M = ∅ := by
      ext n
      simp only [mem_Icc, notMem_empty, iff_false]
      omega
    rw [this, sum_empty]
    norm_num
  · rw [key M hM]
    have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have : (0 : ℝ) ≤ 6 / ((M : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
    linarith

theorem sum_Icc_two_totientRatioCubeExcess_div_le (N : ℕ) :
    ∑ n ∈ Icc 2 N, totientRatioCubeExcess n / n ≤ 19 / 2 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have : Icc 2 N = ∅ := by
      ext n
      simp only [mem_Icc, notMem_empty, iff_false]
      omega
    rw [this, sum_empty]
    norm_num
  have hsplit : Icc 2 N = insert 2 (Icc 3 N) := by
    ext n
    simp only [mem_Icc, mem_insert]
    omega
  rw [hsplit, sum_insert (by simp)]
  have h2 : totientRatioCubeExcess 2 / (2 : ℕ) = 7 / 2 := by
    unfold totientRatioCubeExcess
    norm_num
  have h3 := (sum_le_sum fun n hn => totientRatioCubeExcess_div_le (mem_Icc.mp hn).1).trans
    (sum_Icc_six_div_le N)
  linarith

/-- **Average of the cubed totient ratio.** `Σ_{q ≤ N} (q/φ(q))³ ≤ e^{19/2} N`. -/
theorem sum_div_totient_cube_le (N : ℕ) :
    ∑ q ∈ Icc 1 N, ((q : ℝ) / (q.totient : ℝ)) ^ 3 ≤ Real.exp (19 / 2) * N := by
  classical
  set P := (Icc 1 N).filter Nat.Prime with hP
  have hpf : ∀ q ∈ Icc 1 N, q.primeFactors ⊆ P := by
    intro q hq p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp'.1.one_lt.le,
      (Nat.le_of_dvd (mem_Icc.mp hq).1 hp'.2.1).trans (mem_Icc.mp hq).2⟩, hp'.1⟩
  -- expand over subsets of prime factors and exchange the sums
  have hexp : ∑ q ∈ Icc 1 N, ((q : ℝ) / (q.totient : ℝ)) ^ 3 =
      ∑ t ∈ P.powerset, (∏ p ∈ t, totientRatioCubeExcess p) *
        ((Icc 1 N).filter fun q => t ⊆ q.primeFactors).card := by
    rw [sum_congr rfl fun q hq => div_totient_cube_eq_sum_powerset
      (by have := (mem_Icc.mp hq).1; omega)]
    rw [sum_comm' (t' := P.powerset) (s' := fun t => (Icc 1 N).filter fun q => t ⊆ q.primeFactors)]
    · refine sum_congr rfl fun t _ => ?_
      rw [sum_const, nsmul_eq_mul, mul_comm]
    · intro q t
      simp only [mem_powerset, mem_filter]
      constructor
      · rintro ⟨hq, ht⟩
        exact ⟨⟨hq, ht⟩, ht.trans (hpf q hq)⟩
      · rintro ⟨⟨hq, ht⟩, _⟩
        exact ⟨hq, ht⟩
  -- the count of `q ≤ N` divisible by a product of distinct primes
  have hcount : ∀ t ∈ P.powerset, (((Icc 1 N).filter fun q => t ⊆ q.primeFactors).card : ℝ) ≤
      (N : ℝ) / ∏ p ∈ t, (p : ℝ) := by
    intro t ht
    have htP := mem_powerset.mp ht
    have hprime : ∀ p ∈ t, p.Prime := fun p hp => (mem_filter.mp (htP hp)).2
    have hsub : (Icc 1 N).filter (fun q => t ⊆ q.primeFactors) ⊆
        (Ioc 0 N).filter (fun q => (∏ p ∈ t, p) ∣ q) := by
      intro q hq
      obtain ⟨hqI, htq⟩ := mem_filter.mp hq
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Icc.mp hqI).1, (mem_Icc.mp hqI).2⟩, ?_⟩
      exact prod_primes_dvd q (fun p hp => (hprime p hp).prime)
        fun p hp => (Nat.mem_primeFactors.mp (htq hp)).2.1
    have hcard := card_le_card hsub
    rw [Nat.Ioc_filter_dvd_card_eq_div] at hcard
    calc (((Icc 1 N).filter fun q => t ⊆ q.primeFactors).card : ℝ)
        ≤ ((N / ∏ p ∈ t, p : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ (N : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ) := Nat.cast_div_le
      _ = (N : ℝ) / ∏ p ∈ t, (p : ℝ) := by push_cast; rfl
  have hx0 : ∀ p ∈ P, 0 ≤ totientRatioCubeExcess p := fun p hp =>
    totientRatioCubeExcess_nonneg (mem_filter.mp hp).2.two_le
  have hbound : ∑ q ∈ Icc 1 N, ((q : ℝ) / (q.totient : ℝ)) ^ 3 ≤
      (N : ℝ) * ∏ p ∈ P, (1 + totientRatioCubeExcess p / p) := by
    rw [hexp, prod_one_add, mul_sum]
    refine sum_le_sum fun t ht => ?_
    have htP := mem_powerset.mp ht
    have hF0 : 0 ≤ ∏ p ∈ t, totientRatioCubeExcess p := prod_nonneg fun p hp => hx0 p (htP hp)
    calc (∏ p ∈ t, totientRatioCubeExcess p) *
          (((Icc 1 N).filter fun q => t ⊆ q.primeFactors).card : ℝ)
        ≤ (∏ p ∈ t, totientRatioCubeExcess p) * ((N : ℝ) / ∏ p ∈ t, (p : ℝ)) :=
          mul_le_mul_of_nonneg_left (hcount t ht) hF0
      _ = (N : ℝ) * ∏ p ∈ t, totientRatioCubeExcess p / p := by
          rw [prod_div_distrib]
          ring
  have hexpb : ∏ p ∈ P, (1 + totientRatioCubeExcess p / p) ≤ Real.exp (19 / 2) := by
    calc ∏ p ∈ P, (1 + totientRatioCubeExcess p / p)
        ≤ ∏ p ∈ P, Real.exp (totientRatioCubeExcess p / p) :=
          prod_le_prod (fun p hp => by
            have := hx0 p hp
            have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
            positivity) fun p _ => by linarith [Real.add_one_le_exp (totientRatioCubeExcess p / p)]
      _ = Real.exp (∑ p ∈ P, totientRatioCubeExcess p / p) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (19 / 2) := by
          refine Real.exp_le_exp.mpr ((sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
            fun n hn _ => ?_).trans (sum_Icc_two_totientRatioCubeExcess_div_le N))
          · obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
            exact mem_Icc.mpr ⟨hpp.two_le, (mem_Icc.mp hpI).2⟩
          · have := totientRatioCubeExcess_nonneg (mem_Icc.mp hn).1
            positivity
  calc ∑ q ∈ Icc 1 N, ((q : ℝ) / (q.totient : ℝ)) ^ 3
      ≤ (N : ℝ) * ∏ p ∈ P, (1 + totientRatioCubeExcess p / p) := hbound
    _ ≤ (N : ℝ) * Real.exp (19 / 2) := mul_le_mul_of_nonneg_left hexpb (Nat.cast_nonneg N)
    _ = Real.exp (19 / 2) * N := by ring

/-! ## §3. The observability constant -/

/-- **The ℓ¹ observability constant is quadratic.** `S_N ≤ e^{19/2} N²`. -/
theorem sieveWindowObservabilityConstant_le_exp_mul_sq (N : ℕ) :
    sieveWindowObservabilityConstant N ≤ Real.exp (19 / 2) * (N : ℝ) ^ 2 := by
  unfold sieveWindowObservabilityConstant
  have hpt : ∀ q ∈ Icc 1 N, ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) ^ 2 / (q.totient : ℝ) ≤
      (N : ℝ) * ((q : ℝ) / (q.totient : ℝ)) ^ 3 := by
    intro q hq
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    have hqN : (q : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hq).2
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
    have hσ := sigma_mul_totient_le_sq q
    have hσ0 : (0 : ℝ) ≤ ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) := Nat.cast_nonneg _
    have hσle : ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) ≤ (q : ℝ) ^ 2 / q.totient := by
      rw [le_div_iff₀ hφ]
      exact hσ
    have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
    calc ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) ^ 2 / (q.totient : ℝ)
        ≤ ((q : ℝ) ^ 2 / q.totient) ^ 2 / (q.totient : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hσ0 hσle 2) hφ.le
      _ = (q : ℝ) * ((q : ℝ) / (q.totient : ℝ)) ^ 3 := by
          field_simp
      _ ≤ (N : ℝ) * ((q : ℝ) / (q.totient : ℝ)) ^ 3 :=
          mul_le_mul_of_nonneg_right hqN (by positivity)
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum]
  calc (N : ℝ) * ∑ q ∈ Icc 1 N, ((q : ℝ) / (q.totient : ℝ)) ^ 3
      ≤ (N : ℝ) * (Real.exp (19 / 2) * N) :=
        mul_le_mul_of_nonneg_left (sum_div_totient_cube_le N) (Nat.cast_nonneg N)
    _ = Real.exp (19 / 2) * (N : ℝ) ^ 2 := by ring

/-- **Quadratic inverse ℓ¹ inequality.** `(Σ |c(d)|)² ≤ e^{19/2} N² Q_Sel(c)`. -/
theorem sum_abs_sq_le_exp_mul_sq_mul_selberg (N : ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, |c d|) ^ 2 ≤ Real.exp (19 / 2) * (N : ℝ) ^ 2 * selbergTotientDiagonalForm N c :=
  (sum_abs_sq_le_observabilityConstant_mul_selberg N c).trans
    (mul_le_mul_of_nonneg_right (sieveWindowObservabilityConstant_le_exp_mul_sq N)
      (selbergTotientDiagonalForm_nonneg N c))

/-- **Window transfer of translated moments at quadratic order.** -/
theorem abs_window_translatedMoment_sub_le_exp_mul_sq (N : ℕ) (c : ℕ → ℝ) {m : ℕ}
    (h : Fin m → ℕ) (A K : ℕ) :
    |(∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + h i)) -
        (K : ℝ) * SieveMoments.translatedMoment N c h| ≤
      Real.sqrt (Real.exp (19 / 2) * (N : ℝ) ^ 2 * selbergTotientDiagonalForm N c) ^ m :=
  (abs_window_translatedMoment_sub_le N c h A K).trans
    (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _)
      (Real.le_sqrt_of_sq_le (sum_abs_sq_le_exp_mul_sq_mul_selberg N c)) m)

/-! ## §4. Sharpness: the all-ones Selberg row -/

/-- The row whose Selberg coordinates all equal one. -/
def unitSelbergRow (N : ℕ) : ℕ → ℝ := RHTower.pmRamanujanResidueCoeff (fun _ => 1) N

/-- **No constant below `Φ(N)` is admissible.** -/
theorem cyclotomicIncidenceOrder_le_of_l1_constant {N : ℕ} (hN : 1 ≤ N) {S : ℝ}
    (hS : ∀ c : ℕ → ℝ, (∑ d ∈ Icc 1 N, |c d|) ^ 2 ≤ S * selbergTotientDiagonalForm N c) :
    (cyclotomicIncidenceOrder N : ℝ) ≤ S := by
  set c := unitSelbergRow N
  have hY : ∀ q ∈ Icc 1 N, selbergMultiplesCoord N c q = 1 := fun q hq =>
    RHTower.pmRamanujanResidueCoeff_multiples _ (mem_Icc.mp hq).1 (mem_Icc.mp hq).2
  have hQ : selbergTotientDiagonalForm N c = cyclotomicIncidenceOrder N := by
    unfold selbergTotientDiagonalForm cyclotomicIncidenceOrder
    push_cast
    exact sum_congr rfl fun q hq => by rw [hY q hq]; ring
  have hsum : ∑ d ∈ Icc 1 N, c d = cyclotomicIncidenceOrder N := by
    have h := sieveSeq_factorial_eq_sum_totient_mul N c
    unfold sieveSeq at h
    rw [filter_true_of_mem fun d hd => Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2] at h
    have hR : ∑ q ∈ Icc 1 N, (q.totient : ℝ) * selbergMultiplesCoord N c q =
        cyclotomicIncidenceOrder N := by
      rw [sum_congr rfl fun q hq => by rw [hY q hq, mul_one], cyclotomicIncidenceOrder]
      push_cast
      rfl
    exact h.trans hR
  have hle : (cyclotomicIncidenceOrder N : ℝ) ≤ ∑ d ∈ Icc 1 N, |c d| := by
    rw [← hsum]
    exact (le_abs_self _).trans (abs_sum_le_sum_abs _ _)
  have h := hS c
  rw [hQ] at h
  have hΦ : (0 : ℝ) < cyclotomicIncidenceOrder N := by
    have : 1 ≤ cyclotomicIncidenceOrder N := by
      unfold cyclotomicIncidenceOrder
      rw [Icc_eq_cons_Ioc hN, sum_cons]
      simp
    exact_mod_cast this
  have : (cyclotomicIncidenceOrder N : ℝ) ^ 2 ≤ S * cyclotomicIncidenceOrder N :=
    (pow_le_pow_left₀ hΦ.le hle 2).trans h
  nlinarith

/-- **The optimal inverse ℓ¹ constant has exact order `N²`.** -/
theorem l1_observability_constant_exact_quadratic_order {N : ℕ} (hN : 1 ≤ N) :
    (∀ c : ℕ → ℝ, (∑ d ∈ Icc 1 N, |c d|) ^ 2 ≤
        Real.exp (19 / 2) * (N : ℝ) ^ 2 * selbergTotientDiagonalForm N c) ∧
      ∀ S : ℝ, (∀ c : ℕ → ℝ, (∑ d ∈ Icc 1 N, |c d|) ^ 2 ≤ S * selbergTotientDiagonalForm N c) →
        (N : ℝ) ^ 2 / 8 + N - (N : ℝ) / 2 * (harmonic N : ℝ) ≤ S :=
  ⟨sum_abs_sq_le_exp_mul_sq_mul_selberg N, fun _ hS =>
    (cyclotomicIncidenceOrder_ge N).trans (cyclotomicIncidenceOrder_le_of_l1_constant hN hS)⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
