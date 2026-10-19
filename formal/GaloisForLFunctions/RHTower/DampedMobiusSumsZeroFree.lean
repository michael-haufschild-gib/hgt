import GaloisForLFunctions.RHTower.ZetaMultipleLandauZeroFree

/-!
# Multiplicatively damped Möbius sums

Let `f` be real on the primes with `|f(p)| ≤ 1`, and damp the Möbius function by the
multiplicative weight `F(n) = ∏_{p ∣ n} f(p)`: `a = μ·F`.  The divisor sum of `a` is the
multiplicative function `g(n) = ∏_{p ∣ n} (1 - f(p)) ≥ 0`, and `g` has the multiplicative inverse
`h(p^k) = (f(p) - 1) f(p)^{k-1}` with `|h| ≤ g`.  So `L(a)·ζ = L(g)` with `L(g)` a nonnegative
Dirichlet series that cannot vanish where it converges absolutely (`L(g)·L(h) = 1`).

**Theorem.**  If `Σ_{n ≤ x} μ(n)F(n) = O(x^θ)`, `0 ≤ θ < 1`, and `(σ-1)L(g)(σ) → 0` as `σ ↓ 1`
(true when `Σ_p (1 - f(p))/p < ∞`), then `Σ_n g(n) n^{-σ} < ∞` for `σ > θ`, `ζ(s) ≠ 0` for
`Re s > θ` (`riemannZeta_ne_zero_of_isBigO`), and `θ ≥ 1/2` (`half_le_of_isBigO`).

So no multiplicative damping of `μ` bounded by `1` on the primes produces cancellation beyond the
zero abscissa of `ζ`.  Moreover the damping `1 - f(p)` must be thin at the exponent `θ` it
achieves.  Deleting a set of primes is the case `f = 1_{p ∉ E}`.
-/

open Filter Topology Complex Asymptotics Set LSeries ArithmeticFunction

noncomputable section

namespace RHTower

namespace DampedMobius

/-- A function of the form `n ↦ ∏_{p ∣ n} φ(p, v_p(n))` is multiplicative. -/
theorem isMultiplicative_of_prod {R : Type*} [CommMonoidWithZero R]
    (φ : ℕ → ℕ → R) (A : ArithmeticFunction R)
    (hA : ∀ n, n ≠ 0 → A n = ∏ p ∈ n.primeFactors, φ p (n.factorization p)) :
    A.IsMultiplicative := by
  refine ⟨by rw [hA 1 one_ne_zero]; simp, fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn; subst hmn; rw [hA 1 one_ne_zero]; simp
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn; subst hmn; rw [hA 1 one_ne_zero]; simp
  rw [hA _ (mul_ne_zero hm hn), hA m hm, hA n hn, Nat.Coprime.primeFactors_mul hmn,
    Finset.prod_union hmn.disjoint_primeFactors, Nat.factorization_mul_of_coprime hmn]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpn : n.factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd fun h => ?_
      have hg := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) h
      rw [hmn.gcd_eq_one] at hg
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.mp hg)
    simp [hpn]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpm : m.factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd fun h => ?_
      have hg := Nat.dvd_gcd h (Nat.dvd_of_mem_primeFactors hp)
      rw [hmn.gcd_eq_one] at hg
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.mp hg)
    simp [hpm]

/-- On prime powers, a product-form function is its local factor. -/
theorem prod_prime_pow {R : Type*} [CommMonoid R]
    (φ : ℕ → ℕ → R) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ∏ q ∈ (p ^ k).primeFactors, φ q ((p ^ k).factorization q) = φ p k := by
  rw [Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton, hp.factorization_pow,
    Finsupp.single_eq_same]

/-- `(A * B)(p^k) = Σ_{j ≤ k} A(p^j) B(p^{k-j})`. -/
theorem mul_apply_prime_pow (A B : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (A * B) (p ^ k) = ∑ j ∈ Finset.range (k + 1), A (p ^ j) * B (p ^ (k - j)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => A x * B y), Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hj) hp.pos]

variable (f : ℕ → ℝ)

/-- The damped Möbius function `μ(n) ∏_{p ∣ n} f(p)`. -/
def dampedMobius : ArithmeticFunction ℝ :=
  ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ).pmul (prodPrimeFactors f)

/-- The divisor sum of the damped Möbius function: `∏_{p ∣ n} (1 - f(p))`. -/
def divisorSum : ArithmeticFunction ℝ := prodPrimeFactors fun p => 1 - f p

/-- The Dirichlet inverse of `divisorSum`: `∏_{p^k ∥ n} (f(p) - 1) f(p)^{k-1}`. -/
def inverse : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else
    ∏ p ∈ n.primeFactors, (f p - 1) * f p ^ (n.factorization p - 1), by simp⟩

theorem isMultiplicative_dampedMobius : (dampedMobius f).IsMultiplicative :=
  isMultiplicative_moebius.intCast.pmul (IsMultiplicative.prodPrimeFactors f)

theorem isMultiplicative_divisorSum : (divisorSum f).IsMultiplicative :=
  IsMultiplicative.prodPrimeFactors _

theorem isMultiplicative_inverse : (inverse f).IsMultiplicative :=
  isMultiplicative_of_prod (fun p k => (f p - 1) * f p ^ (k - 1)) _ fun n hn => by
    simp [inverse, hn]

theorem dampedMobius_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    dampedMobius f (p ^ k) = if k = 0 then 1 else if k = 1 then -f p else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [(isMultiplicative_dampedMobius f).map_one]
  rw [dampedMobius, pmul_apply, intCoe_apply, moebius_apply_prime_pow hp hk.ne',
    prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow hk.ne' hp,
    Finset.prod_singleton, if_neg hk.ne']
  split_ifs <;> simp

theorem divisorSum_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    divisorSum f (p ^ k) = if k = 0 then 1 else 1 - f p := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [(isMultiplicative_divisorSum f).map_one]
  rw [divisorSum, prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton, if_neg hk.ne']

theorem inverse_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    inverse f (p ^ k) = if k = 0 then 1 else (f p - 1) * f p ^ (k - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [(isMultiplicative_inverse f).map_one]
  simp only [inverse, coe_mk, pow_ne_zero _ hp.ne_zero, if_false, if_neg hk.ne']
  exact prod_prime_pow (fun p k => (f p - 1) * f p ^ (k - 1)) hp hk.ne'

/-- **The divisor sum of the damped Möbius function.** -/
theorem dampedMobius_mul_zeta : dampedMobius f * (zeta : ArithmeticFunction ℝ) = divisorSum f := by
  refine ((isMultiplicative_dampedMobius f).mul isMultiplicative_zeta.natCast
    ).eq_iff_eq_on_prime_powers _ _ (isMultiplicative_divisorSum f) |>.mpr fun p i hp => ?_
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, divisorSum_apply_prime_pow f hp]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [dampedMobius_apply_prime_pow f hp]
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have htail : ∀ j : ℕ, ∑ x ∈ Finset.range (j + 2), dampedMobius f (p ^ x) =
      ∑ x ∈ Finset.range 2, dampedMobius f (p ^ x) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Finset.sum_range_succ, ih, dampedMobius_apply_prime_pow f hp]
      simp
  rw [htail k, if_neg (Nat.succ_ne_zero k)]
  simp [Finset.sum_range_succ, dampedMobius_apply_prime_pow f hp]
  ring

/-- **The inverse of the divisor sum.** -/
theorem inverse_mul_divisorSum : inverse f * divisorSum f = 1 := by
  refine ((isMultiplicative_inverse f).mul (isMultiplicative_divisorSum f)
    ).eq_iff_eq_on_prime_powers _ _ isMultiplicative_one |>.mpr fun p k hp => ?_
  rw [mul_apply_prime_pow _ _ hp]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [(isMultiplicative_inverse f).map_one, (isMultiplicative_divisorSum f).map_one]
  rw [one_apply_ne (by simpa using (Nat.one_lt_pow hk.ne' hp.one_lt).ne')]
  -- split off `j = k`; the remaining terms telescope
  rw [Finset.sum_range_succ, Nat.sub_self]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', Nat.sub_zero]
  have hmid : ∀ j ∈ Finset.range m, inverse f (p ^ (j + 1)) * divisorSum f (p ^ (m + 1 - (j + 1)))
      = (f p - 1) * f p ^ j * (if m - j = 0 then 1 else 1 - f p) := by
    intro j hj
    rw [inverse_apply_prime_pow f hp, divisorSum_apply_prime_pow f hp, if_neg (Nat.succ_ne_zero j),
      Nat.add_sub_cancel, show m + 1 - (j + 1) = m - j by omega]
  rw [Finset.sum_congr rfl hmid]
  have hmid' : ∀ j ∈ Finset.range m, (f p - 1) * f p ^ j * (if m - j = 0 then 1 else 1 - f p)
      = -((1 - f p) ^ 2 * f p ^ j) := by
    intro j hj
    have hjm := Finset.mem_range.mp hj
    rw [if_neg (by omega)]
    ring
  rw [Finset.sum_congr rfl hmid', Finset.sum_neg_distrib, ← Finset.mul_sum,
    inverse_apply_prime_pow f hp, divisorSum_apply_prime_pow f hp, inverse_apply_prime_pow f hp,
    divisorSum_apply_prime_pow f hp]
  simp only [if_true, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]
  linear_combination (1 - f p) * geom_sum_mul (f p) m

/-! ### Bounds for `|f(p)| ≤ 1` -/

variable {f}

section Bounds

variable (hf : ∀ p, p.Prime → |f p| ≤ 1)
include hf

theorem abs_dampedMobius_le (n : ℕ) : |dampedMobius f n| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [dampedMobius, pmul_apply, intCoe_apply, prodPrimeFactors_apply hn, abs_mul,
    Finset.abs_prod]
  have h1 : |((moebius n : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  have h2 : ∏ p ∈ n.primeFactors, |f p| ≤ 1 :=
    Finset.prod_le_one (fun p _ => abs_nonneg _) fun p hp => hf p (Nat.prime_of_mem_primeFactors hp)
  calc |((moebius n : ℤ) : ℝ)| * ∏ p ∈ n.primeFactors, |f p| ≤ 1 * 1 :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun p _ => abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem divisorSum_nonneg (n : ℕ) : 0 ≤ divisorSum f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [divisorSum, prodPrimeFactors_apply hn]
  exact Finset.prod_nonneg fun p hp => by
    have := hf p (Nat.prime_of_mem_primeFactors hp)
    linarith [le_abs_self (f p)]

theorem abs_inverse_le (n : ℕ) : |inverse f n| ≤ divisorSum f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [divisorSum, prodPrimeFactors_apply hn]
  simp only [inverse, coe_mk, hn, if_false, Finset.abs_prod]
  refine Finset.prod_le_prod (fun p _ => abs_nonneg _) fun p hp => ?_
  have hfp := hf p (Nat.prime_of_mem_primeFactors hp)
  rw [abs_mul, abs_pow, abs_sub_comm, abs_of_nonneg (by linarith [le_abs_self (f p)] :
    (0 : ℝ) ≤ 1 - f p)]
  calc (1 - f p) * |f p| ^ (n.factorization p - 1) ≤ (1 - f p) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hfp)
          (by linarith [le_abs_self (f p)])
    _ = 1 - f p := mul_one _

end Bounds

/-! ### The zeta multiple and its nonvanishing -/

/-- The damped Möbius function as a real sequence. -/
def seq (f : ℕ → ℝ) (n : ℕ) : ℝ := dampedMobius f n

theorem convolution_seq_one :
    convolution (IntegerBeurling.countSeq (seq f)) 1 = fun n => ((divisorSum f n : ℝ) : ℂ) := by
  funext n
  rw [convolution_def]
  simp only [Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => IntegerBeurling.countSeq (seq f) a),
    ← dampedMobius_mul_zeta f, coe_mul_zeta_apply]
  simp [IntegerBeurling.countSeq, seq]

theorem LSeries_seq_mul_riemannZeta (hf : ∀ p, p.Prime → |f p| ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (IntegerBeurling.countSeq (seq f)) s * riemannZeta s =
      LSeries (fun n => ((divisorSum f n : ℝ) : ℂ)) s := by
  rw [← LSeries_one_eq_riemannZeta hs, ← LSeries_convolution'
    (IntegerBeurling.summable_countSeq (a := seq f) (abs_dampedMobius_le hf) hs)
    (LSeriesSummable_one_iff.mpr hs), convolution_seq_one]

theorem summable_divisorSum_two (hf : ∀ p, p.Prime → |f p| ≤ 1) :
    LSeriesSummable (fun n => ((divisorSum f n : ℝ) : ℂ)) 2 := by
  rw [← convolution_seq_one]
  exact (IntegerBeurling.summable_countSeq (a := seq f) (abs_dampedMobius_le hf)
    (by norm_num)).convolution
    (LSeriesSummable_one_iff.mpr (by norm_num))

/-- **`L(g)` does not vanish where it converges absolutely:** `L(g)·L(h) = 1`. -/
theorem LSeries_divisorSum_ne_zero (hf : ∀ p, p.Prime → |f p| ≤ 1) {s : ℂ}
    (hsum : LSeriesSummable (fun n => ((divisorSum f n : ℝ) : ℂ)) s) :
    LSeries (fun n => ((divisorSum f n : ℝ) : ℂ)) s ≠ 0 := by
  have hsumh : LSeriesSummable (fun n => ((inverse f n : ℝ) : ℂ)) s := by
    have hn : Summable fun n => ‖term (fun n => ((divisorSum f n : ℝ) : ℂ)) s n‖ :=
      summable_norm_iff.mpr hsum
    refine (summable_norm_iff (E := ℂ)).mp (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => LSeries.norm_term_le s ?_) hn)
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_of_nonneg (divisorSum_nonneg hf n)]
    exact abs_inverse_le hf n
  have hconv : convolution (fun n => ((divisorSum f n : ℝ) : ℂ)) (fun n => ((inverse f n : ℝ) : ℂ))
      = LSeries.delta := by
    funext n
    rw [convolution_def]
    dsimp only
    have h1 := congrArg (fun A : ArithmeticFunction ℝ => ((A n : ℝ) : ℂ))
      ((mul_comm (divisorSum f) (inverse f)).trans (inverse_mul_divisorSum f))
    simp only [mul_apply, Complex.ofReal_sum, Complex.ofReal_mul] at h1
    rw [h1, LSeries.delta]
    by_cases h : n = 1
    · subst h; simp
    · simp [h]
  intro h0
  have := LSeries_convolution' hsum hsumh
  rw [hconv, LSeries_delta, Pi.one_apply, h0, zero_mul] at this
  exact one_ne_zero this

/-! ### Main theorems -/

section Main

variable (hf : ∀ p, p.Prime → |f p| ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
  (hM : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, dampedMobius f n) =O[atTop] fun x => x ^ θ)
  (hD : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * LSeries (fun n => ((divisorSum f n : ℝ) : ℂ)) σ)
    (𝓝[>] 1) (𝓝 0))
include hf hθ hθ1 hM hD

/-- **The damping must be thin at the exponent it achieves:** `Σ g(n) n^{-σ} < ∞`, `σ > θ`. -/
theorem summable_divisorSum_of_isBigO {σ : ℝ} (hσ : θ < σ) :
    LSeriesSummable (fun n => ((divisorSum f n : ℝ) : ℂ)) σ :=
  ZetaMultiple.summable_of_isBigO (a := seq f) (abs_dampedMobius_le hf) (divisorSum_nonneg hf)
    (summable_divisorSum_two hf) (fun _ hs => LSeries_seq_mul_riemannZeta hf hs) hθ hθ1 hM hD hσ

/-- **Damped Möbius cancellation is a zero-free region:** `ζ(s) ≠ 0` for `Re s > θ`. -/
theorem riemannZeta_ne_zero_of_isBigO {z : ℂ} (hz : θ < z.re) : riemannZeta z ≠ 0 :=
  ZetaMultiple.riemannZeta_ne_zero_of_isBigO (a := seq f) (abs_dampedMobius_le hf)
    (divisorSum_nonneg hf) (summable_divisorSum_two hf)
    (fun _ hs => LSeries_seq_mul_riemannZeta hf hs) hθ hθ1 hM hD
    (fun _ hs => LSeries_divisorSum_ne_zero hf hs) hz

end Main

/-- **Damped Möbius cancellation stops at the half power.** -/
theorem half_le_of_isBigO (hf : ∀ p, p.Prime → |f p| ≤ 1)
    (hD : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * LSeries (fun n => ((divisorSum f n : ℝ) : ℂ)) σ)
      (𝓝[>] 1) (𝓝 0))
    {θ : ℝ}
    (hM : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, dampedMobius f n) =O[atTop] fun x => x ^ θ) :
    1 / 2 ≤ θ :=
  ZetaMultiple.half_le_of_isBigO (a := seq f) (abs_dampedMobius_le hf) (divisorSum_nonneg hf)
    (summable_divisorSum_two hf) (fun _ hs => LSeries_seq_mul_riemannZeta hf hs)
    (fun _ hs => LSeries_divisorSum_ne_zero hf hs) hD hM

/-! ### Mild dampings: `Σ_p (1 - f(p))/p < ∞` -/

theorem inv_one_sub_le_two {x : ℝ} (hx : x ≤ 1 / 2) : 1 / (1 - x) ≤ 2 := by
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The local factor `Σ_k g(p^k) p^{-k} = 1 + (1 - f(p))/(p - 1) ≤ exp(2(1 - f(p))/p)`. -/
theorem tsum_divisorSum_prime_pow_le (hf : ∀ p, p.Prime → |f p| ≤ 1) {p : ℕ} (hp : p.Prime) :
    ∑' k : ℕ, divisorSum f (p ^ k) / ((p ^ k : ℕ) : ℝ) ≤ Real.exp (2 * ((1 - f p) / p)) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hq1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hc0 : 0 ≤ 1 - f p := by linarith [le_abs_self (f p), hf p hp]
  have hterm : ∀ k : ℕ, divisorSum f (p ^ (k + 1)) / ((p ^ (k + 1) : ℕ) : ℝ) =
      (1 - f p) * (1 / p) * (1 / p) ^ k := by
    intro k
    rw [divisorSum_apply_prime_pow f hp, if_neg (Nat.succ_ne_zero k)]
    push_cast
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    rw [one_div_pow]
    field_simp
    ring
  have hsum : Summable fun k : ℕ => divisorSum f (p ^ k) / ((p ^ k : ℕ) : ℝ) := by
    rw [← summable_nat_add_iff 1]
    simp_rw [hterm]
    exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
  rw [hsum.tsum_eq_zero_add]
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, pow_zero, Nat.cast_one, div_one,
    (isMultiplicative_divisorSum f).map_one]
  have hx : (1 - f p) * (1 / (p : ℝ)) * (1 - 1 / (p : ℝ))⁻¹ ≤ 2 * ((1 - f p) / p) := by
    rw [← one_div, mul_assoc, show 2 * ((1 - f p) / p) = (1 - f p) * (1 / p * 2) by ring]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (inv_one_sub_le_two (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)) hq0) hc0
  calc 1 + (1 - f p) * (1 / (p : ℝ)) * (1 - 1 / (p : ℝ))⁻¹ ≤ 1 + 2 * ((1 - f p) / p) := by
        linarith
    _ ≤ Real.exp (2 * ((1 - f p) / p)) := by linarith [Real.add_one_le_exp (2 * ((1 - f p) / p))]

/-- **`Σ_p (1 - f(p))/p < ∞` gives `Σ_n g(n)/n < ∞`**, by the Euler product over `[0, N)`. -/
theorem summable_divisorSum_div (hf : ∀ p, p.Prime → |f p| ≤ 1)
    (hsum : Summable ({p : ℕ | p.Prime}.indicator fun p => (1 - f p) / p)) :
    Summable fun n : ℕ => divisorSum f n / n := by
  classical
  set c : ℕ → ℝ := {p : ℕ | p.Prime}.indicator fun p => (1 - f p) / p with hc
  have hc0 : ∀ p, 0 ≤ c p := fun p => Set.indicator_nonneg (fun p hp => div_nonneg
    (by linarith [le_abs_self (f p), hf p hp]) (Nat.cast_nonneg p)) p
  refine summable_of_sum_range_le (c := Real.exp (2 * ∑' p, c p))
    (fun n => div_nonneg (divisorSum_nonneg hf n) n.cast_nonneg) fun N => ?_
  set F : ℕ → ℝ := fun n => divisorSum f n / n with hF
  have hmul : ∀ {m n : ℕ}, m.Coprime n → F (m * n) = F m * F n := by
    intro m n hmn
    simp only [hF, (isMultiplicative_divisorSum f).map_mul_of_coprime hmn, Nat.cast_mul]
    rw [mul_div_mul_comm]
  have hloc : ∀ {p : ℕ}, p.Prime → Summable fun k : ℕ => ‖F (p ^ k)‖ := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / p)
        (by rw [div_lt_one (by linarith)]; linarith)).mul_left 2)
    rw [Real.norm_of_nonneg (div_nonneg (divisorSum_nonneg hf _) (Nat.cast_nonneg _))]
    have hg2 : divisorSum f (p ^ k) ≤ 2 := by
      rw [divisorSum_apply_prime_pow f hp]
      split_ifs
      · norm_num
      · linarith [neg_abs_le (f p), hf p hp]
    push_cast
    rw [one_div_pow, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right hg2 (by positivity)
  have hhas := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := F) (by simp [hF, (isMultiplicative_divisorSum f).map_one]) hmul hloc
    (Finset.range N)).2
  have hsub : ∀ n ∈ (Finset.range N).filter (· ≠ 0), n ∈ Nat.factoredNumbers (Finset.range N) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    refine Nat.mem_factoredNumbers.mpr ⟨hn.2, fun p hp => ?_⟩
    exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_of_mem_primeFactorsList hp) hn.1)
  have hrange : ∑ i ∈ Finset.range N, divisorSum f i / i =
      ∑ i ∈ (Finset.range N).filter (· ≠ 0), F i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · push Not at h; subst h; simp
  have hle1 : ∑ i ∈ (Finset.range N).filter (· ≠ 0), F i ≤
      ∏ p ∈ Finset.range N with p.Prime, ∑' k : ℕ, F (p ^ k) := by
    rw [← Finset.sum_subtype_of_mem F hsub]
    exact sum_le_hasSum _ (fun i _ => div_nonneg (divisorSum_nonneg hf _) (Nat.cast_nonneg _)) hhas
  have hfactor : ∀ p ∈ Finset.filter (fun p => p.Prime) (Finset.range N),
      ∑' k : ℕ, F (p ^ k) ≤ Real.exp (2 * c p) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    rw [hc, Set.indicator_of_mem (show p ∈ {p : ℕ | p.Prime} from hpp)]
    exact tsum_divisorSum_prime_pow_le hf hpp
  have hprod : ∏ p ∈ Finset.range N with p.Prime, ∑' k : ℕ, F (p ^ k) ≤
      Real.exp (2 * ∑ p ∈ Finset.range N with p.Prime, c p) := by
    rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod (fun p _ => tsum_nonneg fun k =>
      div_nonneg (divisorSum_nonneg hf _) (Nat.cast_nonneg _)) hfactor
  have hcsum : ∑ p ∈ Finset.range N with p.Prime, c p ≤ ∑' p, c p :=
    hsum.sum_le_tsum _ (fun p _ => hc0 p)
  rw [hrange]
  calc ∑ i ∈ (Finset.range N).filter (· ≠ 0), F i
      ≤ ∏ p ∈ Finset.range N with p.Prime, ∑' k : ℕ, F (p ^ k) := hle1
    _ ≤ Real.exp (2 * ∑ p ∈ Finset.range N with p.Prime, c p) := hprod
    _ ≤ Real.exp (2 * ∑' p, c p) := Real.exp_le_exp.mpr (by linarith)

/-- **Mild dampings cannot beat the zero abscissa.**  If `|f(p)| ≤ 1`, `Σ_p (1 - f(p))/p < ∞` and
`Σ_{n ≤ x} μ(n) ∏_{p ∣ n} f(p) = O(x^θ)` with `0 ≤ θ < 1`, then `ζ(s) ≠ 0` for `Re s > θ`. -/
theorem riemannZeta_ne_zero_of_isBigO_of_summable (hf : ∀ p, p.Prime → |f p| ≤ 1)
    (hsum : Summable ({p : ℕ | p.Prime}.indicator fun p => (1 - f p) / p))
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hM : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, dampedMobius f n) =O[atTop] fun x => x ^ θ)
    {z : ℂ} (hz : θ < z.re) : riemannZeta z ≠ 0 :=
  riemannZeta_ne_zero_of_isBigO hf hθ hθ1 hM
    (ZetaMultiple.tendsto_sub_one_mul_LSeries_of_summable (divisorSum_nonneg hf)
      (summable_divisorSum_div hf hsum)) hz

/-- **Mild dampings stop at the half power:** `Σ_{n ≤ x} μ(n) ∏_{p ∣ n} f(p)` is never
`O(x^θ)` with `θ < 1/2`. -/
theorem not_isBigO_dampedMobius_of_summable (hf : ∀ p, p.Prime → |f p| ≤ 1)
    (hsum : Summable ({p : ℕ | p.Prime}.indicator fun p => (1 - f p) / p))
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, dampedMobius f n) =O[atTop] fun x => x ^ θ :=
  fun hM => absurd (half_le_of_isBigO hf (ZetaMultiple.tendsto_sub_one_mul_LSeries_of_summable
    (divisorSum_nonneg hf) (summable_divisorSum_div hf hsum)) hM) (not_le.mpr hθ)

end DampedMobius

end RHTower
