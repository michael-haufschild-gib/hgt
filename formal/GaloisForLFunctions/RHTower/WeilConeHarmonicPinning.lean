import GaloisForLFunctions.RHTower.WeilConeMultiplesOfPrimeLaw

/-!
# Harmonic pinning: the only free scalar of the notch-small Weil cone

Let `lam` be full-cone Weil-positive with notch-small deviation `d = lam − Λ`, and write
`T = Σ_n d(n)/n` and `Γ_N = Σ_n d(n) gcd(n, N)/n`.

**The gcd twist law** (`le_zero_of_tendsto_gcdTwist`). For every integer `N ≥ 2` the twist
`q(τ) = |1 + t N^{iτ}|²` has main weight `n^{−1/2} (1 + t² + t N^{−1/2} (gcd(n, N) + 1))`. So its fibre
sums are `(1 + t²) T + t N^{−1/2} (T + Γ_N)`, and these cannot have a positive limit:
`(1 + t²) T + t N^{−1/2} (T + Γ_N) ≤ 0` for every `t`. In particular `T ≤ 0`
(`nonpos_of_tendsto_harmonicSum`).

**Harmonic pinning gives uniqueness** (`eq_vonMangoldt_of_harmonicPinning`). Suppose the harmonic sums
of `d` over the multiples of every `e ≥ 2` converge absolutely. If `T = 0`, then `lam = Λ`.
For nonnegative `lam` the absolute convergence is the multiples-of-a-prime law, so
(`eq_vonMangoldt_of_nonneg_of_harmonicPinning`) **a nonnegative Weil-positive `lam` with notch-small
deviation equals `Λ` iff `Σ (lam − Λ)(n)/n = 0`**. Every other such `lam` has `Σ (lam − Λ)(n)/n < 0`:
`Λ` is the unique maximizer of the harmonic constant.

**Proof.**
* With `T = 0` the law gives `Γ_N = 0` for all `N`, since `t = ±1` are both allowed.
* `Γ_N = Σ_{e∣N} φ(e) U_e`, with `U_e = Σ_{e∣n} d(n)/n` and `U_1 = T`. By strong induction on `N`,
  every `U_e` vanishes.
* For a finite set `S` of primes, `Z_e(S) = Σ_{k : (k, S) = 1} d(ek)/(ek)` satisfies
  `Z_e(S ∪ {p}) = Z_e(S) − Z_{ep}(S)` and `Z_e(∅) = U_e`, so `Z_e(S) = 0`.
* With `S` the primes up to `y`, `Z_e(S) = d(e)/e + Σ_{k>y, (k,S)=1} d(ek)/(ek)`. The tail tends
  to `0`, so `d(e) = 0`.
-/

noncomputable section

open Filter Topology RHTower

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable
open RHTower.PrimeSmallDeviation

variable {P : Finset ℕ}

/-! ## Twist norms by exponents -/

theorem vecNum_mul_vecDen_eq_prod (a : P → ℤ) :
    vecNum a * vecDen a = ∏ p : P, (p : ℕ) ^ (a p).natAbs := by
  unfold vecNum vecDen
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => by rw [← pow_add, Int.toNat_add_toNat_neg_eq_natAbs]

theorem twistNorm_eq_mul_prod (n : ℕ) (w : P → ℤ) :
    twistNorm P n w =
      ((roughPart P n * ∏ p : P, (p : ℕ) ^ (vecOf P n p - w p).natAbs : ℕ) : ℝ) := by
  unfold twistNorm
  have h := vecNum_mul_vecDen_eq_prod (vecOf P n - w)
  simp only [Pi.sub_apply] at h
  rw [← h]
  push_cast
  ring

theorem prod_coe_primeFactors_pow_factorization {N : ℕ} (hN : N ≠ 0) :
    ∏ p : N.primeFactors, (p : ℕ) ^ N.factorization p = N := by
  rw [Finset.prod_coe_sort N.primeFactors (fun p => p ^ N.factorization p)]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hN]
  exact (Finsupp.prod_of_support_subset _ (Nat.support_factorization N).le _
    (fun p _ => pow_zero p)).symm

theorem gcd_eq_prod_min {n N : ℕ} (hn : n ≠ 0) (hN : N ≠ 0) :
    Nat.gcd n N = ∏ p : N.primeFactors, (p : ℕ) ^ min (n.factorization p) (N.factorization p) := by
  have hg : Nat.gcd n N ≠ 0 := Nat.gcd_ne_zero_right hN
  rw [Finset.prod_coe_sort N.primeFactors
    (fun p => p ^ min (n.factorization p) (N.factorization p))]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hg]
  rw [Finsupp.prod_of_support_subset _ (s := N.primeFactors) ?_ _ (fun p _ => pow_zero p)]
  · refine Finset.prod_congr rfl fun p _ => ?_
    rw [Nat.factorization_gcd hn hN]
    rfl
  · rw [Nat.support_factorization]
    exact Nat.primeFactors_mono (Nat.gcd_dvd_right n N) hN

/-- `twistNorm(n, 0) = n`. -/
theorem twistNorm_zero_eq {n : ℕ} (hn : n ≠ 0) : twistNorm P n 0 = n := by
  rw [twistNorm_eq_mul_prod]
  have e : ∏ p : P, (p : ℕ) ^ (vecOf P n p - (0 : P → ℤ) p).natAbs = smoothPart P n := by
    unfold smoothPart
    exact Finset.prod_congr rfl fun p _ => by simp [vecOf]
  rw [e, mul_comm, smoothPart_mul_roughPart n hn]

/-- `twistNorm(n, −vec N) = n N` over the primes of `N`. -/
theorem twistNorm_neg_vecOf_eq {N n : ℕ} (hN : N ≠ 0) (hn : n ≠ 0) :
    twistNorm N.primeFactors n (-vecOf N.primeFactors N) = n * N := by
  rw [twistNorm_eq_mul_prod]
  have e : ∏ p : N.primeFactors,
      (p : ℕ) ^ (vecOf N.primeFactors n p - (-vecOf N.primeFactors N) p).natAbs =
      (∏ p : N.primeFactors, (p : ℕ) ^ n.factorization p) *
        ∏ p : N.primeFactors, (p : ℕ) ^ N.factorization p := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add]
    congr 1
    simp only [vecOf, Pi.neg_apply]
    omega
  have hs : (∏ p : N.primeFactors, (p : ℕ) ^ n.factorization p) =
      smoothPart N.primeFactors n := rfl
  rw [e, prod_coe_primeFactors_pow_factorization hN, hs, ← mul_assoc, mul_comm (roughPart _ _),
    smoothPart_mul_roughPart n hn]
  push_cast; ring

/-- `twistNorm(n, vec N) gcd(n, N)² = n N` over the primes of `N`. -/
theorem twistNorm_vecOf_mul_gcd_sq {N n : ℕ} (hN : N ≠ 0) (hn : n ≠ 0) :
    twistNorm N.primeFactors n (vecOf N.primeFactors N) * (Nat.gcd n N : ℝ) ^ 2 = n * N := by
  rw [twistNorm_eq_mul_prod, gcd_eq_prod_min hn hN]
  have key : (∏ p : N.primeFactors,
      (p : ℕ) ^ (vecOf N.primeFactors n p - vecOf N.primeFactors N p).natAbs) *
      (∏ p : N.primeFactors, (p : ℕ) ^ min (n.factorization p) (N.factorization p)) ^ 2 =
      smoothPart N.primeFactors n * N := by
    have e : (∏ p : N.primeFactors,
        (p : ℕ) ^ (vecOf N.primeFactors n p - vecOf N.primeFactors N p).natAbs) *
        (∏ p : N.primeFactors, (p : ℕ) ^ min (n.factorization p) (N.factorization p)) ^ 2 =
        (∏ p : N.primeFactors, (p : ℕ) ^ n.factorization p) *
          ∏ p : N.primeFactors, (p : ℕ) ^ N.factorization p := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      simp only [vecOf]
      omega
    rw [e, prod_coe_primeFactors_pow_factorization hN]
    rfl
  have h2 : (roughPart N.primeFactors n * ∏ p : N.primeFactors,
      (p : ℕ) ^ (vecOf N.primeFactors n p - vecOf N.primeFactors N p).natAbs) *
      (∏ p : N.primeFactors, (p : ℕ) ^ min (n.factorization p) (N.factorization p)) ^ 2 =
      n * N := by
    rw [mul_assoc, key, ← mul_assoc, mul_comm (roughPart _ _), smoothPart_mul_roughPart n hn]
  exact_mod_cast h2

/-! ## The gcd twist -/

/-- The coefficients `c_0 = 1`, `c_{vec N} = t` of the twist `|1 + t N^{iτ}|²`. -/
def gcdPairCoeff (N : ℕ) (t : ℝ) : (N.primeFactors → ℤ) → ℝ := fun a => if a = 0 then 1 else t

/-- **The main weight of `|1 + t N^{iτ}|²`**: `(1 + t² + t N^{−1/2}(gcd(n, N) + 1)) n^{−1/2}`. -/
theorem twistMainWeight_gcd_eq {N : ℕ} (hN : 2 ≤ N) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    twistMainWeight N.primeFactors {0, vecOf N.primeFactors N} (gcdPairCoeff N t) n =
      (1 + t ^ 2 + t * (Real.sqrt N)⁻¹ * ((Nat.gcd n N : ℝ) + 1)) * (Real.sqrt n)⁻¹ := by
  have hg0 : (0 : N.primeFactors → ℤ) ≠ vecOf N.primeFactors N :=
    (vecOf_ne_zero ⟨hN, subset_rfl⟩).symm
  have hN0 : N ≠ 0 := by omega
  unfold twistMainWeight
  rw [Finset.sum_pair hg0, Finset.sum_pair hg0, Finset.sum_pair hg0]
  have hc0 : gcdPairCoeff N t 0 = 1 := if_pos rfl
  have hcg : gcdPairCoeff N t (vecOf N.primeFactors N) = t := if_neg hg0.symm
  rw [hc0, hcg]
  simp only [mul_one, one_mul, sub_self, zero_sub, sub_zero]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hG : (0 : ℝ) < Nat.gcd n N := by
    exact_mod_cast Nat.gcd_pos_of_pos_right n (show 0 < N by omega)
  have tg : twistNorm N.primeFactors n (vecOf N.primeFactors N) = n * N / (Nat.gcd n N : ℝ) ^ 2 := by
    rw [eq_div_iff (by positivity)]
    exact twistNorm_vecOf_mul_gcd_sq hN0 hn
  rw [twistNorm_zero_eq hn, twistNorm_neg_vecOf_eq hN0 hn, tg]
  have e1 : (Real.sqrt (n * N))⁻¹ = (Real.sqrt n)⁻¹ * (Real.sqrt N)⁻¹ := by
    rw [Real.sqrt_mul hn0.le, mul_inv]
  have e2 : (Real.sqrt (n * N / (Nat.gcd n N : ℝ) ^ 2))⁻¹ =
      (Nat.gcd n N : ℝ) * ((Real.sqrt n)⁻¹ * (Real.sqrt N)⁻¹) := by
    rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hG.le, Real.sqrt_mul hn0.le, inv_div]
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
    field_simp
  rw [e1, e2]
  ring

/-- The `|1 + t N^{iτ}|²`-fibre partial sums are `(1 + t²) T_k + t N^{−1/2} (T_k + Γ_k)`. -/
theorem sum_gcdTwist_eq {N : ℕ} (hN : 2 ≤ N) {d : ℕ → ℝ} (hd0 : d 0 = 0) (t : ℝ) (k : ℕ) :
    ∑ n ∈ Finset.range (k + 1), d n * (Real.sqrt n)⁻¹ *
        twistMainWeight N.primeFactors {0, vecOf N.primeFactors N} (gcdPairCoeff N t) n =
      (1 + t ^ 2) * ∑ n ∈ Finset.range (k + 1), d n / n +
        t * (Real.sqrt N)⁻¹ * (∑ n ∈ Finset.range (k + 1), d n / n +
          ∑ n ∈ Finset.range (k + 1), d n * Nat.gcd n N / n) := by
  have e : ∀ n ∈ Finset.range (k + 1), d n * (Real.sqrt n)⁻¹ *
      twistMainWeight N.primeFactors {0, vecOf N.primeFactors N} (gcdPairCoeff N t) n =
      (1 + t ^ 2) * (d n / n) + t * (Real.sqrt N)⁻¹ * (d n / n + d n * Nat.gcd n N / n) := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hd0]
    rw [twistMainWeight_gcd_eq hN hn.ne' t]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = (n : ℝ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hn0.le]
    rw [div_eq_mul_inv, div_eq_mul_inv, ← hsq]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib]

/-- **The gcd twist law.** If the combined partial sums `(1 + t²) T_k + t N^{−1/2} (T_k + Γ_k)` of a
notch-small Weil deviation converge, the limit is `≤ 0`. -/
theorem le_zero_of_tendsto_gcdTwist {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    (hd : NotchSmall (WeilOneSided.coneDeviation lam)) {N : ℕ} (hN : 2 ≤ N) (t : ℝ) {X : ℝ}
    (hX : Tendsto (fun k : ℕ =>
      (1 + t ^ 2) * ∑ n ∈ Finset.range (k + 1), WeilOneSided.coneDeviation lam n / n +
        t * (Real.sqrt N)⁻¹ * (∑ n ∈ Finset.range (k + 1), WeilOneSided.coneDeviation lam n / n +
          ∑ n ∈ Finset.range (k + 1),
            WeilOneSided.coneDeviation lam n * Nat.gcd n N / n)) atTop (𝓝 X)) :
    X ≤ 0 := by
  by_contra hX0
  push Not at hX0
  have hd0 : WeilOneSided.coneDeviation lam 0 = 0 := by simp [WeilOneSided.coneDeviation]
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hX.eventually (Ioi_mem_nhds (half_lt_self hX0)))
  have hβ : ∀ a ∈ ({0, vecOf N.primeFactors N} : Finset (N.primeFactors → ℤ)), ∀ p,
      |a p| ≤ (fun p : N.primeFactors => N.factorization p) p := by
    intro a ha p
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simp
    · rw [Finset.mem_singleton.mp ha]; simp [vecOf]
  have h := twistFibreSum_nonpos_of_weilPositiveFull hW hd
    (fun p hp => Nat.prime_of_mem_primeFactors hp) {0, vecOf N.primeFactors N}
    (gcdPairCoeff N t) hβ (Y := X / 2) (T := T) fun k hk => by
      rw [sum_gcdTwist_eq hN hd0 t k]
      exact (hT k hk).le
  linarith

/-- **The harmonic constant of a notch-small Weil deviation is `≤ 0`.** -/
theorem nonpos_of_tendsto_harmonicSum {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    (hd : NotchSmall (WeilOneSided.coneDeviation lam)) {T : ℝ}
    (hT : Tendsto (fun k : ℕ => ∑ n ∈ Finset.range k, WeilOneSided.coneDeviation lam n / n)
      atTop (𝓝 T)) : T ≤ 0 := by
  have hT1 := (tendsto_add_atTop_iff_nat 1).mpr hT
  refine le_zero_of_tendsto_gcdTwist hW hd (le_refl 2) 0 (X := T) ?_
  refine hT1.congr fun k => ?_
  simp

/-! ## Harmonic pinning gives uniqueness -/

/-- `d(n) gcd(n, N)/n = Σ_{e∣N} φ(e) 1_{e∣n} d(n)/n`. -/
theorem mul_gcd_div_eq_sum_totient {N : ℕ} (hN : N ≠ 0) (d : ℕ → ℝ) (n : ℕ) :
    d n * Nat.gcd n N / n =
      ∑ e ∈ N.divisors, (Nat.totient e : ℝ) * (if e ∣ n then d n / n else 0) := by
  classical
  have hfilter : N.divisors.filter (· ∣ n) = (Nat.gcd n N).divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, h1⟩, Nat.gcd_ne_zero_right hN⟩
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h2, hN⟩, h1⟩
  have e1 : ∑ e ∈ N.divisors, (Nat.totient e : ℝ) * (if e ∣ n then d n / n else 0) =
      (∑ e ∈ N.divisors.filter (· ∣ n), (Nat.totient e : ℝ)) * (d n / n) := by
    rw [Finset.sum_mul, Finset.sum_filter]
    exact Finset.sum_congr rfl fun e _ => by split_ifs <;> ring
  rw [e1, hfilter]
  have h2 : ∑ e ∈ (Nat.gcd n N).divisors, (Nat.totient e : ℝ) = Nat.gcd n N := by
    exact_mod_cast Nat.sum_totient (Nat.gcd n N)
  rw [h2]
  ring

/-- **Harmonic pinning gives uniqueness.** Let `lam` be full-cone Weil-positive with notch-small
deviation `d`, whose harmonic sums over the multiples of every `e ≥ 2` converge absolutely. If
`Σ_n d(n)/n = 0`, then `lam = Λ`. -/
theorem eq_vonMangoldt_of_harmonicPinning {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    (hd : NotchSmall (WeilOneSided.coneDeviation lam))
    (hmult : ∀ e, 2 ≤ e → Summable fun n : ℕ =>
      if e ∣ n then |WeilOneSided.coneDeviation lam n| / n else 0)
    (hT : Tendsto (fun k : ℕ => ∑ n ∈ Finset.range k, WeilOneSided.coneDeviation lam n / n)
      atTop (𝓝 0)) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  classical
  set d := WeilOneSided.coneDeviation lam with hddef
  have hd0 : d 0 = 0 := by simp [hddef, WeilOneSided.coneDeviation]
  -- the multiples series
  set u : ℕ → ℕ → ℝ := fun e n => if e ∣ n then d n / n else 0 with hu
  have hus : ∀ e, 2 ≤ e → Summable (u e) := fun e he =>
    (hmult e he).of_norm_bounded fun n => by
      simp only [hu, Real.norm_eq_abs]
      split_ifs
      · rw [abs_div, Nat.abs_cast]
      · simp
  set U : ℕ → ℝ := fun e => if e = 1 then 0 else ∑' n, u e n with hU
  have hUlim : ∀ e, 1 ≤ e →
      Tendsto (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), u e n) atTop (𝓝 (U e)) := by
    intro e he
    rcases Nat.eq_or_lt_of_le he with rfl | he2
    · simp only [hU, if_true]
      refine ((tendsto_add_atTop_iff_nat 1).mpr hT).congr fun k => ?_
      exact Finset.sum_congr rfl fun n _ => by simp [hu]
    · simp only [hU, if_neg (show e ≠ 1 by omega)]
      exact (tendsto_add_atTop_iff_nat 1).mpr (hus e he2).hasSum.tendsto_sum_nat
  -- `Γ_N = Σ_{e∣N} φ(e) U_e = 0`
  have hΓ0 : ∀ N, 2 ≤ N → ∑ e ∈ N.divisors, (Nat.totient e : ℝ) * U e = 0 := by
    intro N hN
    have hN0 : N ≠ 0 := by omega
    have hΓlim : Tendsto (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), d n * Nat.gcd n N / n) atTop
        (𝓝 (∑ e ∈ N.divisors, (Nat.totient e : ℝ) * U e)) := by
      have h : Tendsto (fun k : ℕ => ∑ e ∈ N.divisors, (Nat.totient e : ℝ) *
          ∑ n ∈ Finset.range (k + 1), u e n) atTop
          (𝓝 (∑ e ∈ N.divisors, (Nat.totient e : ℝ) * U e)) :=
        tendsto_finsetSum _ fun e he =>
          (hUlim e (Nat.pos_of_mem_divisors he)).const_mul _
      refine h.congr fun k => ?_
      rw [Finset.sum_congr rfl fun n _ => mul_gcd_div_eq_sum_totient hN0 d n, Finset.sum_comm]
      exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
    have hT1 := (tendsto_add_atTop_iff_nat 1).mpr hT
    have hlaw : ∀ t : ℝ, t * (Real.sqrt N)⁻¹ * (∑ e ∈ N.divisors, (Nat.totient e : ℝ) * U e) ≤ 0 := by
      intro t
      have h := le_zero_of_tendsto_gcdTwist hW hd hN t
        (X := (1 + t ^ 2) * 0 + t * (Real.sqrt N)⁻¹ *
          (0 + ∑ e ∈ N.divisors, (Nat.totient e : ℝ) * U e))
        (((hT1.const_mul _).add ((hT1.add hΓlim).const_mul _)))
      linarith
    have hs : 0 < (Real.sqrt N)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < N)))
    have h1 := hlaw 1
    have h2 := hlaw (-1)
    nlinarith
  -- every `U_e` vanishes
  have hU0 : ∀ N, 1 ≤ N → U N = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro hN
      rcases Nat.eq_or_lt_of_le hN with rfl | hN2
      · simp [hU]
      have hsum := hΓ0 N hN2
      rw [Finset.sum_eq_single N (fun e he hne => by
          rw [ih e (lt_of_le_of_ne (Nat.divisor_le he) hne) (Nat.pos_of_mem_divisors he),
            mul_zero])
          (fun h => absurd (Nat.mem_divisors_self N (by omega)) h)] at hsum
      have hφ : (Nat.totient N : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
      exact (mul_eq_zero.mp hsum).resolve_left hφ
  -- the coprime-filtered multiples sums
  set f : ℕ → ℕ → ℝ := fun m k => d (m * k) / ((m * k : ℕ) : ℝ) with hf
  have hfs : ∀ m, 2 ≤ m → Summable fun k => |f m k| := fun m hm => by
    have h := (hmult m hm).comp_injective (mul_right_injective₀ (show m ≠ 0 by omega))
    refine h.congr fun k => ?_
    simp only [Function.comp_apply, hf]
    rw [if_pos (dvd_mul_right m k), abs_div, Nat.abs_cast]
  set Z : ℕ → Finset ℕ → ℝ := fun m S =>
    ∑' k, if (∀ p ∈ S, ¬ p ∣ k) then f m k else 0 with hZ
  have hZsum : ∀ m, 2 ≤ m → ∀ S : Finset ℕ,
      Summable fun k => if (∀ p ∈ S, ¬ p ∣ k) then f m k else 0 := fun m hm S =>
    (hfs m hm).of_norm_bounded fun k => by
      simp only [Real.norm_eq_abs]
      split_ifs
      · exact le_rfl
      · simp
  have hZ0 : ∀ m, 2 ≤ m → Z m ∅ = 0 := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have e : Z m ∅ = ∑' n, u m n := by
      simp only [hZ, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, if_true]
      rw [← (mul_right_injective₀ hm0).tsum_eq (f := u m) ?_]
      · exact tsum_congr fun k => by simp [hu, hf]
      · intro n hn
        simp only [Function.mem_support, hu] at hn
        split_ifs at hn with h
        · obtain ⟨k, rfl⟩ := h; exact ⟨k, rfl⟩
        · exact absurd rfl hn
    have := hU0 m (by omega)
    simp only [hU, if_neg (show m ≠ 1 by omega)] at this
    rw [e, this]
  have hZstep : ∀ m, 2 ≤ m → ∀ (S : Finset ℕ) (p : ℕ), p.Prime → p ∉ S →
      (∀ q ∈ S, q.Prime) → Z m (insert p S) = Z m S - Z (m * p) S := by
    intro m hm S p hp hpS hS
    set g : ℕ → ℝ := fun k => if (∀ q ∈ S, ¬ q ∣ k) ∧ p ∣ k then f m k else 0 with hg
    have hgs : Summable g := (hfs m hm).of_norm_bounded fun k => by
      simp only [hg, Real.norm_eq_abs]
      split_ifs
      · exact le_rfl
      · simp
    have hsplit : ∀ k, (if (∀ q ∈ insert p S, ¬ q ∣ k) then f m k else 0) =
        (if (∀ q ∈ S, ¬ q ∣ k) then f m k else 0) - g k := by
      intro k
      simp only [hg, Finset.mem_insert, forall_eq_or_imp]
      by_cases h1 : p ∣ k <;> by_cases h2 : ∀ q ∈ S, ¬ q ∣ k <;> simp [h1, h2]
    have hiff : ∀ j, (∀ q ∈ S, ¬ q ∣ p * j) ↔ (∀ q ∈ S, ¬ q ∣ j) := by
      intro j
      refine ⟨fun h q hq hqj => h q hq (dvd_mul_of_dvd_right hqj p), fun h q hq hqpj => ?_⟩
      rcases (Nat.Prime.dvd_mul (hS q hq)).mp hqpj with hqp | hqj
      · have := (Nat.prime_dvd_prime_iff_eq (hS q hq) hp).mp hqp
        exact hpS (this ▸ hq)
      · exact h q hq hqj
    have hreindex : ∑' k, g k = Z (m * p) S := by
      rw [← (mul_right_injective₀ hp.ne_zero).tsum_eq (f := g) ?_]
      · simp only [hZ]
        refine tsum_congr fun j => ?_
        simp only [hg, hf]
        rw [if_congr ((and_iff_left (dvd_mul_right p j)).trans (hiff j)) rfl rfl]
        congr 2 <;> ring_nf
      · intro k hk
        simp only [Function.mem_support, hg] at hk
        split_ifs at hk with h
        · obtain ⟨j, rfl⟩ := h.2; exact ⟨j, rfl⟩
        · exact absurd rfl hk
    simp only [hZ]
    rw [tsum_congr hsplit, (hZsum m hm S).tsum_sub hgs, hreindex]
  have hZall : ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → ∀ m, 2 ≤ m → Z m S = 0 := by
    intro S
    refine Finset.induction_on S (fun _ m hm => hZ0 m hm) ?_
    intro p S hpS ih hS m hm
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [hZstep m hm S p hp hpS hS', ih hS' m hm,
      ih hS' (m * p) (by nlinarith [hp.two_le])]
    ring
  -- isolation of `d(e)`
  intro e he
  have hdz : d e = 0 := by
    set h : ℕ → ℝ := fun k => |f e k| with hh
    have hhs : Summable h := hfs e he
    have hbound : ∀ y : ℕ, 1 ≤ y → |d e / e| ≤ ∑' i, h (i + (y + 1)) := by
      intro y hy
      set φ : ℕ → ℝ := fun k => if (∀ q ∈ primesUpTo y, ¬ q ∣ k) then f e k else 0 with hφ
      have hφs : Summable φ := hZsum e he (primesUpTo y)
      have hZy : ∑' k, φ k = 0 := hZall _ (fun q hq => prime_of_mem_primesUpTo q hq) e he
      have hsplit := hφs.sum_add_tsum_nat_add (y + 1)
      have hfin : ∑ k ∈ Finset.range (y + 1), φ k = d e / e := by
        rw [Finset.sum_eq_single 1]
        · simp only [hφ, hf, mul_one]
          rw [if_pos fun q hq hq1 => (prime_of_mem_primesUpTo q hq).one_lt.ne'
            (Nat.dvd_one.mp hq1)]
        · intro k hk hk1
          rcases Nat.lt_or_ge k 2 with hk2 | hk2
          · interval_cases k
            · simp [hφ, hf, hd0]
            · exact absurd rfl hk1
          · have hky : k ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            simp only [hφ]
            rw [if_neg]
            push Not
            exact ⟨k.minFac, mem_primesUpTo.mpr ⟨(Nat.minFac_le (by omega)).trans hky,
              Nat.minFac_prime (by omega)⟩, Nat.minFac_dvd k⟩
        · intro h1; exact absurd (Finset.mem_range.mpr (by omega)) h1
      have htail : |∑' i, φ (i + (y + 1))| ≤ ∑' i, h (i + (y + 1)) := by
        have hs1 := (summable_nat_add_iff (y + 1)).mpr hφs
        have hs2 := (summable_nat_add_iff (y + 1)).mpr hhs
        refine (abs_tsum_le_tsum_abs (hs1.abs)).trans
          (hs1.abs.tsum_le_tsum (fun i => ?_) hs2)
        simp only [hφ, hh]
        split_ifs
        · exact le_rfl
        · simp
      rw [← hfin]
      have : ∑ k ∈ Finset.range (y + 1), φ k = -∑' i, φ (i + (y + 1)) := by linarith
      rw [this, abs_neg]
      exact htail
    have hlim : Tendsto (fun y : ℕ => ∑' i, h (i + (y + 1))) atTop (𝓝 0) :=
      (tendsto_sum_nat_add h).comp (tendsto_add_atTop_nat 1)
    have hle : |d e / e| ≤ 0 :=
      ge_of_tendsto hlim (eventually_atTop.mpr ⟨1, fun y hy => hbound y hy⟩)
    have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
    have := abs_nonpos_iff.mp hle
    rwa [div_eq_zero_iff, or_iff_left he0] at this
  have : d e = lam e - ArithmeticFunction.vonMangoldt e := by
    simp only [hddef, WeilOneSided.coneDeviation, if_pos he]
  linarith

/-! ## The nonnegative cone -/

/-- For nonnegative Weil-positive `lam`, the deviation has absolutely convergent harmonic sums over the
multiples of every `e ≥ 2`. -/
theorem summable_multiples_abs_coneDeviation_of_nonneg {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n) {e : ℕ} (he : 2 ≤ e) :
    Summable fun n : ℕ => if e ∣ n then |WeilOneSided.coneDeviation lam n| / n else 0 := by
  classical
  set p := e.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpe : p ∣ e := Nat.minFac_dvd e
  have h1 := summable_multiples_of_weilPositiveFull_of_nonneg hW hnn hp
  have h2 : Summable fun n : ℕ =>
      if p ∣ n then (ArithmeticFunction.vonMangoldt n : ℝ) / n else 0 := by
    refine summable_of_sum_range_le (c := Real.log p) (fun n => ?_) fun N => ?_
    · split_ifs
      · have := ArithmeticFunction.vonMangoldt_nonneg (n := n); positivity
      · exact le_rfl
    · rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp; exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
      · have := sum_multiples_vonMangoldt_div_le hp (N - 1)
        rwa [Nat.sub_add_cancel hN] at this
  have h3 : Summable fun n : ℕ =>
      if n = p then |WeilOneSided.coneDeviation lam p| / p else 0 :=
    (hasSum_ite_eq p _).summable
  refine (h1.add (h2.add h3)).of_nonneg_of_le (fun n => ?_) fun n => ?_
  · split_ifs <;> positivity
  · have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hn := Nat.cast_nonneg (α := ℝ) n
    have t1 : 0 ≤ (if p ∣ n ∧ n ≠ p then lam n / n else 0) := by
      split_ifs with h
      · rcases Nat.eq_zero_or_pos n with rfl | hn0
        · simp
        · exact div_nonneg (hnn n (by
            have := Nat.le_of_dvd hn0 h.1; have := hp.two_le; omega)) hn
      · exact le_rfl
    have t2 : 0 ≤ (if p ∣ n then (ArithmeticFunction.vonMangoldt n : ℝ) / n else 0) := by
      split_ifs
      · positivity
      · exact le_rfl
    have t3 : 0 ≤ (if n = p then |WeilOneSided.coneDeviation lam p| / p else 0) := by
      split_ifs <;> positivity
    by_cases hen : e ∣ n
    · rw [if_pos hen]
      have hpn : p ∣ n := hpe.trans hen
      by_cases hnp : n = p
      · have h3e : (if n = p then |WeilOneSided.coneDeviation lam p| / p else 0) =
            |WeilOneSided.coneDeviation lam n| / n := by rw [if_pos hnp, hnp]
        linarith
      · have e1 : (if p ∣ n ∧ n ≠ p then lam n / n else 0) = lam n / n := if_pos ⟨hpn, hnp⟩
        have e2 : (if p ∣ n then (ArithmeticFunction.vonMangoldt n : ℝ) / n else 0) =
            (ArithmeticFunction.vonMangoldt n : ℝ) / n := if_pos hpn
        rcases Nat.lt_or_ge n 2 with h2 | h2
        · interval_cases n
          · rw [Nat.cast_zero, div_zero]; linarith
          · exact absurd (Nat.dvd_one.mp hpn) hp.one_lt.ne'
        · have hdn : WeilOneSided.coneDeviation lam n = lam n - ArithmeticFunction.vonMangoldt n := by
            simp only [WeilOneSided.coneDeviation, if_pos h2]
          rw [hdn]
          have habs : |lam n - ArithmeticFunction.vonMangoldt n| ≤
              lam n + ArithmeticFunction.vonMangoldt n := by
            rw [abs_le]; constructor <;> linarith [hnn n h2]
          have : |lam n - ArithmeticFunction.vonMangoldt n| / n ≤
              lam n / n + (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
            rw [← add_div]; exact div_le_div_of_nonneg_right habs hn
          linarith
    · rw [if_neg hen]; linarith

/-- **Harmonic pinning for the nonnegative cone.** A nonnegative full-cone Weil-positive `lam` with
notch-small deviation and `Σ_n (lam − Λ)(n)/n = 0` equals `Λ`. -/
theorem eq_vonMangoldt_of_nonneg_of_harmonicPinning {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n)
    (hd : NotchSmall (WeilOneSided.coneDeviation lam))
    (hT : Tendsto (fun k : ℕ => ∑ n ∈ Finset.range k, WeilOneSided.coneDeviation lam n / n)
      atTop (𝓝 0)) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  eq_vonMangoldt_of_harmonicPinning hW hd
    (fun _ he => summable_multiples_abs_coneDeviation_of_nonneg hW hnn he) hT

/-- **RH as a harmonic inequality.** RH holds iff some nonnegative full-cone Weil-positive weight
system with notch-small deviation has a convergent harmonic constant `Σ (lam − Λ)(n)/n ≥ 0`. -/
theorem riemannHypothesis_iff_exists_nonneg_harmonicConstant_nonneg :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, RHTower.WeilPositiveFull lam ∧ (∀ n, 2 ≤ n → 0 ≤ lam n) ∧
      NotchSmall (WeilOneSided.coneDeviation lam) ∧ ∃ T : ℝ, 0 ≤ T ∧
        Tendsto (fun k : ℕ => ∑ n ∈ Finset.range k, WeilOneSided.coneDeviation lam n / n) atTop
          (𝓝 T) := by
  constructor
  · intro hRH
    have h0 : WeilOneSided.coneDeviation (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) =
        fun _ => 0 := by
      funext n; simp [WeilOneSided.coneDeviation]
    refine ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH,
      fun n _ => ArithmeticFunction.vonMangoldt_nonneg, ?_, 0, le_rfl, ?_⟩
    · rw [h0]; exact notchSmall_of_tendsto_zero tendsto_const_nhds
    · rw [h0]; simp
  · rintro ⟨lam, hW, hnn, hd, T, hT0, hT⟩
    have hT00 : T = 0 := le_antisymm (nonpos_of_tendsto_harmonicSum hW hd hT) hT0
    subst hT00
    have h := eq_vonMangoldt_of_nonneg_of_harmonicPinning hW hnn hd hT
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc

/-! ## Local mass tending to zero -/

/-- **Harmonic pinning with vanishing local mass.** Let `lam ≥ 0` be full-cone Weil-positive, and
suppose the local harmonic mass of `d = lam − Λ` tends to `0`. Then `Σ_n d(n)/n` converges to some
`T ≤ 0`, and `T = 0` forces `lam = Λ`. -/
theorem exists_harmonicConstant_of_nonneg_of_localMassTendsZero {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n)
    (hloc : LocalMassTendsZero (WeilOneSided.coneDeviation lam)) :
    ∃ T : ℝ, Tendsto (fun k : ℕ => ∑ n ∈ Finset.range k, WeilOneSided.coneDeviation lam n / n)
      atTop (𝓝 T) ∧ T ≤ 0 ∧ (T = 0 → ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) := by
  have hd0 : WeilOneSided.coneDeviation lam 0 = 0 := by simp [WeilOneSided.coneDeviation]
  have hd1 : WeilOneSided.coneDeviation lam 1 = 0 := by simp [WeilOneSided.coneDeviation]
  have hd := notchSmall_of_localMassTendsZero hd0 hd1 hloc
  have hLM : 0 < WeilOneSided.localMassConst := by
    unfold WeilOneSided.localMassConst
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  obtain ⟨T, hT⟩ := WeilOneSided.exists_tendsto_sum_coneDeviation_div_of_localMass hW
    fun η hη => hloc (η * WeilOneSided.localMassConst) (by positivity)
  refine ⟨T, hT, nonpos_of_tendsto_harmonicSum hW hd hT, fun hT0 => ?_⟩
  subst hT0
  exact eq_vonMangoldt_of_nonneg_of_harmonicPinning hW hnn hd hT

/-- **RH as a harmonic inequality, local-mass form.** RH holds iff some nonnegative full-cone
Weil-positive weight system whose deviation from `Λ` has vanishing local harmonic mass has
nonnegative harmonic constant `lim Σ_{n<k} (lam − Λ)(n)/n`. -/
theorem riemannHypothesis_iff_exists_nonneg_localMass_harmonicConstant_nonneg :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, RHTower.WeilPositiveFull lam ∧
      (∀ n, 2 ≤ n → 0 ≤ lam n) ∧ LocalMassTendsZero (WeilOneSided.coneDeviation lam) ∧
      ∀ T : ℝ, Tendsto (fun k : ℕ => ∑ n ∈ Finset.range k, WeilOneSided.coneDeviation lam n / n)
        atTop (𝓝 T) → 0 ≤ T := by
  constructor
  · intro hRH
    have h0 : WeilOneSided.coneDeviation (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) =
        fun _ => 0 := by
      funext n; simp [WeilOneSided.coneDeviation]
    refine ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH,
      fun n _ => ArithmeticFunction.vonMangoldt_nonneg, ?_, fun T hT => ?_⟩
    · rw [h0]; exact fun η hη => ⟨0, fun _ _ _ => by simp; exact hη.le⟩
    · rw [h0] at hT
      simp only [zero_div, Finset.sum_const_zero] at hT
      exact (tendsto_nhds_unique tendsto_const_nhds hT).le
  · rintro ⟨lam, hW, hnn, hloc, hT⟩
    obtain ⟨T, hTlim, hTle, hTeq⟩ :=
      exists_harmonicConstant_of_nonneg_of_localMassTendsZero hW hnn hloc
    have h := hTeq (le_antisymm hTle (hT T hTlim))
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc

end RHTower.WeilAbscissa
