import GaloisForLFunctions.ArithmeticProduction.PrefixCancellationAmplifiesTheZeroFloor
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheLineIsAShiftOfTheField
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

/-!
# Truncated Möbius collar dichotomy, `ℓ²`-blindness, and the shifted-inverse countermodel on `ℕ`

Let `c_X(n) = ∑_{d ∣ n, d ≤ X} μ(d)` (`truncatedMoebiusDivisorSum X n`) denote the Dirichlet
coefficients of `ζ(s) M_X(s)`.  On `1 ≤ n ≤ X` exact Möbius inversion gives `c_X(n) = δ_{n,1}`;
above `X`, four unconditional laws govern both its arithmetic collar structure and the obstructions
to pure `ℓ²` or local Euler-product proofs of long mollified second-moment bounds:

1. **Smooth–prime dichotomy on `(X, X²]` and collar Dirichlet factorization.**
   * On the first octave `X < n ≤ 2X`, `c_X(n) = -μ(n)` (`truncatedMoebiusDivisorSum_eq_neg_moebius_of_mem_Ioc`).
   * At every prime `p > X`, `c_X(p) = 1` (`truncatedMoebiusDivisorSum_prime_of_gt`).
   * At every composite `n ∈ (X, X²]` divisible by a prime `p > X`, writing `n = p m` forces
     `2 ≤ m < X < p`, `gcd(p, m) = 1`, and `{d ∣ n : d ≤ X} = {d ∣ m}`, so `c_X(n) = 0`
     (`truncatedMoebiusDivisorSum_eq_zero_of_composite_rough_le_sq`).
   * For every `n ≥ 2`, `c_X(n) = -∑_{m ∣ n, m > X} μ(m)` (`truncatedMoebiusDivisorSum_eq_neg_sum_gt`),
     yielding the exact collar factorization
     `∑_{X < n ≤ XR} c_X(n) n^{-s} = -∑_{r=1}^R r^{-s} ∑_{X < m ≤ ⌊XR/r⌋} μ(m) m^{-s}`
     (`collar_dirichletPoly_eq_neg_sum_pureMoebius`) and its critical-line Cauchy–Schwarz bound
     (`integral_normSq_collar_le_harmonic_mul_sum_pureMoebius`).
2. **Multiplicative gauge-twist equivariance** (`divisorSum_mul_completelyMultiplicative`,
   `norm_divisorSum_mul_completelyMultiplicative_eq`): twisting `b(d)` and `1` by a completely
   multiplicative unimodular character preserves all restricted divisor-sum moduli identically.
3. **`ℓ²`-blindness of prefix-cancelled unit-sign sequences**
   (`exists_prefix_zero_unit_sign_criticalMoment_ge`): for every `X ≥ 2` and `T ≥ 2`, there exists
   `c : ℕ → ℤ` with `c(1) = 1`, `c(n) = 0` on `[2, X]`, `|c(n)| ≤ 1` everywhere (so
   `∑_{n ≤ M} c(n)² ≤ M`), yet `∫_1^T ‖∑_{X < n ≤ 2X} c(n) n^{-1/2-it}‖² dt ≥ X / (100 log(2X))`.
4. **Shifted-inverse multiplicative countermodel on `ℕ`**
   (`exists_shiftedInverse_countermodel_blowup`): for every `δ ∈ (0, ½)` and
   `s_δ = (½ - δ) - 2i`, the multiplicative pair `a_δ(n) = μ(n) n^{-s_δ}`, `b_δ(d) = d^{-s_δ}`
   satisfies `a_δ * b_δ = 1`, `‖a_δ‖ ≤ 1`, `‖b_δ‖ ≤ 1`, `∑_{d ≥ 1} ‖b_δ(d)‖² / d < ∞`, and
   `L(a_δ, s) = ζ(s + s_δ)⁻¹` on `Re s > ½ + δ`, while `F_δ(½ + it) = ζ(½ + it + s_δ)⁻¹` is
   analytic and zero-free across `[1, 3]` and its critical-line `L²` mass blows up at rate at least
   `κ_δ X^{2δ} / log(2X)` across every `[1, T]` (`T ≥ 3`).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open BiScaleUncertainty.ChebyshevGauge

/-! ## §1. Smooth–prime dichotomy on `(X, X²]` and collar Dirichlet factorization -/

/-- Truncated Möbius divisor sum `c_X(n) = ∑_{d ∣ n, d ≤ X} μ(d)`, the `n`-th Dirichlet coefficient
of `ζ(s) M_X(s)`. -/
def truncatedMoebiusDivisorSum (X n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (· ≤ X), ArithmeticFunction.moebius d

private theorem sum_divisors_moebius_eq_ite (n : ℕ) :
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d = if n = 1 then 1 else 0 := by
  apply Int.cast_injective (α := ℝ)
  have h := sum_divisors_sharpCoeff n
  unfold sharpCoeff at h
  rw [Int.cast_sum, h]
  split_ifs <;> simp

/-- Real cast of `truncatedMoebiusDivisorSum` matches `divisorSum (Icc 1 X) sharpCoeff` for `n ≥ 1`. -/
theorem truncatedMoebiusDivisorSum_cast_eq_divisorSum {X n : ℕ} (hn : 1 ≤ n) :
    ((truncatedMoebiusDivisorSum X n : ℤ) : ℝ) = divisorSum (Finset.Icc 1 X) sharpCoeff n := by
  unfold truncatedMoebiusDivisorSum divisorSum sharpCoeff
  rw [Int.cast_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd, _⟩, hdX⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, hdX⟩, hd⟩
  · rintro ⟨⟨_, hdX⟩, hd⟩
    exact ⟨⟨hd, by omega⟩, hdX⟩

/-- Exact Möbius inversion on the prefix `1 ≤ n ≤ X`: `c_X(n) = δ_{n,1}`. -/
theorem truncatedMoebiusDivisorSum_of_mem_Icc {X n : ℕ} (hn : n ∈ Finset.Icc 1 X) :
    truncatedMoebiusDivisorSum X n = if n = 1 then 1 else 0 := by
  obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
  unfold truncatedMoebiusDivisorSum
  have hfil : n.divisors.filter (· ≤ X) = n.divisors := by
    refine Finset.filter_true_of_mem fun d hd => ?_
    exact (Nat.le_of_dvd hn1 (Nat.mem_divisors.mp hd).1).trans hnX
  rw [hfil, sum_divisors_moebius_eq_ite]

/-- **Complementary divisor flip.** For every `n ≥ 2`,
`c_X(n) = -∑_{m ∣ n, m > X} μ(m)`. -/
theorem truncatedMoebiusDivisorSum_eq_neg_sum_gt {X n : ℕ} (hn : 2 ≤ n) :
    truncatedMoebiusDivisorSum X n = -∑ m ∈ n.divisors.filter (X < ·), ArithmeticFunction.moebius m := by
  unfold truncatedMoebiusDivisorSum
  have hpart := Finset.sum_filter_add_sum_filter_not n.divisors (· ≤ X)
    (fun d => ArithmeticFunction.moebius d)
  have hnot : n.divisors.filter (fun d => ¬ d ≤ X) = n.divisors.filter (X < ·) := by
    ext d
    simp only [Finset.mem_filter, not_le]
  rw [hnot, sum_divisors_moebius_eq_ite, if_neg (by omega : n ≠ 1)] at hpart
  omega

/-- **First-octave identity.** For `X ≥ 1` and `X < n ≤ 2X`, `c_X(n) = -μ(n)`. -/
theorem truncatedMoebiusDivisorSum_eq_neg_moebius_of_mem_Ioc {X n : ℕ} (hX : 1 ≤ X)
    (hn : n ∈ Finset.Ioc X (2 * X)) :
    truncatedMoebiusDivisorSum X n = -ArithmeticFunction.moebius n := by
  obtain ⟨hnX, hn2X⟩ := Finset.mem_Ioc.mp hn
  rw [truncatedMoebiusDivisorSum_eq_neg_sum_gt (by omega)]
  have hfil : n.divisors.filter (X < ·) = {n} := by
    ext m
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨k, hk⟩, hn0⟩, hmX⟩
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
      have hk1 : k = 1 := by nlinarith
      subst hk1
      omega
    · rintro rfl
      exact ⟨⟨dvd_rfl, by omega⟩, hnX⟩
  rw [hfil, Finset.sum_singleton]

/-- **Prime persistence above `X`.** For every prime `p > X` (`X ≥ 1`), `c_X(p) = 1`. -/
theorem truncatedMoebiusDivisorSum_prime_of_gt {X p : ℕ} (hX : 1 ≤ X) (hp : p.Prime)
    (hXp : X < p) :
    truncatedMoebiusDivisorSum X p = 1 := by
  unfold truncatedMoebiusDivisorSum
  have hfil : p.divisors.filter (· ≤ X) = (1 : ℕ).divisors := by
    rw [hp.divisors]
    ext d
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Nat.divisors_one]
    constructor
    · rintro ⟨rfl | rfl, hdX⟩
      · rfl
      · omega
    · rintro rfl
      exact ⟨Or.inl rfl, hX⟩
  rw [hfil, sum_divisors_moebius_eq_ite, if_pos rfl]

/-- **Composite rough vanishing on `(X, X²]`.** If `X < n ≤ X²`, `n` is composite, and `n` has a
prime factor `p > X`, then `c_X(n) = 0`. -/
theorem truncatedMoebiusDivisorSum_eq_zero_of_composite_rough_le_sq {X n p : ℕ} (hX : 1 ≤ X)
    (hnX : X < n) (hn2 : n ≤ X ^ 2) (hnp : ¬ n.Prime) (hp : p.Prime) (hXp : X < p)
    (hpn : p ∣ n) :
    truncatedMoebiusDivisorSum X n = 0 := by
  obtain ⟨m, rfl⟩ := hpn
  have hm0 : m ≠ 0 := by rintro rfl; simp at hnX; omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hnp (by simpa using hp)
  have hm2 : 2 ≤ m := by omega
  have hmX : m < X := by nlinarith
  unfold truncatedMoebiusDivisorSum
  have hfil : (p * m).divisors.filter (· ≤ X) = m.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd_pm, hpm0⟩, hdX⟩
      refine ⟨?_, hm0⟩
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_pm (Nat.pos_of_ne_zero hpm0)
      have hnot_pd : ¬ p ∣ d := fun hpd => by
        have := Nat.le_of_dvd hd_pos hpd
        omega
      exact ((hp.coprime_iff_not_dvd.mpr hnot_pd).symm.dvd_mul_left).mp hd_pm
    · rintro ⟨hd_m, _⟩
      exact ⟨⟨dvd_mul_of_dvd_right hd_m p, mul_ne_zero hp.ne_zero hm0⟩,
        (Nat.le_of_dvd (by omega) hd_m).trans hmX.le⟩
  rw [hfil, sum_divisors_moebius_eq_ite, if_neg (by omega)]

/-- **Collar Dirichlet factorization.** For `X ≥ 1` and any `R : ℕ`,
`∑_{X < n ≤ XR} c_X(n) n^{-s} = -∑_{r=1}^R r^{-s} ∑_{X < m ≤ ⌊XR/r⌋} μ(m) m^{-s}`. -/
theorem collar_dirichletPoly_eq_neg_sum_pureMoebius {X R : ℕ} (hX : 1 ≤ X) (s : ℂ) :
    (∑ n ∈ Finset.Ioc X (X * R),
      (truncatedMoebiusDivisorSum X n : ℂ) * (n : ℂ) ^ (-s)) =
    -∑ r ∈ Finset.Icc 1 R, (r : ℂ) ^ (-s) *
      ∑ m ∈ Finset.Ioc X ((X * R) / r),
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s) := by
  have hlhs : (∑ n ∈ Finset.Ioc X (X * R),
        (truncatedMoebiusDivisorSum X n : ℂ) * (n : ℂ) ^ (-s)) =
      -∑ n ∈ Finset.Ioc X (X * R),
        ∑ m ∈ n.divisors.filter (X < ·),
          (ArithmeticFunction.moebius m : ℂ) * (n : ℂ) ^ (-s) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hnX, _⟩ := Finset.mem_Ioc.mp hn
    rw [truncatedMoebiusDivisorSum_eq_neg_sum_gt (by omega), Int.cast_neg, Int.cast_sum,
      neg_mul, Finset.sum_mul]
  rw [hlhs]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sigma', ← Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => ⟨p.1 / p.2, p.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_filter, Nat.mem_divisors,
      Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨hnX, hnXR⟩, ⟨hm_dvd, _⟩, hmX⟩ := hp
    have hm_pos : 0 < m := by omega
    have hmul : (n / m) * m = n := Nat.div_mul_cancel hm_dvd
    have hq_pos : 0 < n / m := by
      by_contra h0
      rw [Nat.eq_zero_of_not_pos h0, zero_mul] at hmul
      omega
    have hqR : n / m ≤ R := by nlinarith
    exact ⟨⟨hq_pos, hqR⟩, hmX, (Nat.le_div_iff_mul_le hq_pos).mpr (by linarith)⟩
  · rintro ⟨n₁, m₁⟩ hp₁ ⟨n₂, m₂⟩ hp₂ heq
    simp only [Sigma.mk.inj_iff] at heq
    obtain ⟨hq_eq, hm_eq⟩ := heq
    have hm₁_dvd : m₁ ∣ n₁ :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hp₁).2).1).1
    have hm₂_dvd : m₂ ∣ n₂ :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hp₂).2).1).1
    subst hm_eq
    have hn_eq : n₁ = n₂ := by
      rw [← Nat.div_mul_cancel hm₁_dvd, ← Nat.div_mul_cancel hm₂_dvd, hq_eq]
    subst hn_eq
    rfl
  · rintro ⟨r, m⟩ hrm
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_filter,
      Nat.mem_divisors] at hrm ⊢
    obtain ⟨⟨hr1, hrR⟩, hmX, hm_div⟩ := hrm
    have hm_pos : 0 < m := by omega
    have hmul_le : m * r ≤ X * R := (Nat.le_div_iff_mul_le hr1).mp hm_div
    refine ⟨⟨r * m, m⟩, ⟨⟨by nlinarith, by linarith⟩,
      ⟨⟨dvd_mul_left m r, by positivity⟩, hmX⟩⟩, ?_⟩
    simp [Nat.mul_div_cancel _ hm_pos]
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hp
    have hm_dvd : m ∣ n := hp.2.1.1
    have hmul : (n / m) * m = n := Nat.div_mul_cancel hm_dvd
    have hcpow : (n : ℂ) ^ (-s) = ((n / m : ℕ) : ℂ) ^ (-s) * (m : ℂ) ^ (-s) := by
      conv_lhs => rw [← hmul]
      simpa using Complex.mul_cpow_ofReal_nonneg (a := ((n / m : ℕ) : ℝ)) (b := (m : ℝ))
        (by positivity) (by positivity) (-s)
    rw [hcpow]
    ring

private theorem sum_Icc_inv_le_one_add_log_collar {R : ℕ} (hR : 1 ≤ R) :
    ∑ r ∈ Finset.Icc 1 R, (r : ℝ)⁻¹ ≤ 1 + Real.log R := by
  induction R with
  | zero => omega
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hk1_pos : (0 : ℝ) < k + 1 := by positivity
      have hstep : ((k + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
        have hexp := Real.add_one_le_exp (-(1 / ((k : ℝ) + 1)))
        have hfrac : -(1 / ((k : ℝ) + 1)) + 1 = (k : ℝ) / ((k : ℝ) + 1) := by
          field_simp
          ring
        rw [hfrac] at hexp
        have hlog := Real.log_le_log (div_pos hk_pos hk1_pos) hexp
        rw [Real.log_div hk_pos.ne' hk1_pos.ne', Real.log_exp] at hlog
        push_cast
        linarith [show ((k : ℝ) + 1)⁻¹ = 1 / ((k : ℝ) + 1) from one_div _ |>.symm]
      have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext r
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : (k + 1) ∉ Finset.Icc 1 k := by simp
      rw [hsplit, Finset.sum_insert hnot]
      linarith [ih hk1]

/-- **Critical-line Cauchy–Schwarz collar bound.** For `X ≥ 1`, `R ≥ 1`, and `T ≥ 1`,
`∫_1^T ‖∑_{X < n ≤ XR} c_X(n) n^{-1/2-it}‖² dt` is at most `1 + log R` times the sum over
`1 ≤ r ≤ R` of the pure-Möbius collar moments `∫_1^T ‖∑_{X < m ≤ ⌊XR/r⌋} μ(m) m^{-1/2-it}‖² dt`. -/
theorem integral_normSq_collar_le_harmonic_mul_sum_pureMoebius {X R : ℕ} (hX : 1 ≤ X)
    (hR : 1 ≤ R) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T,
      ‖∑ n ∈ Finset.Ioc X (X * R),
        (truncatedMoebiusDivisorSum X n : ℂ) *
          (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2) ≤
    (1 + Real.log R) * ∑ r ∈ Finset.Icc 1 R,
      ∫ t in (1 : ℝ)..T,
        ‖∑ m ∈ Finset.Ioc X ((X * R) / r),
          (ArithmeticFunction.moebius m : ℂ) *
            (m : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
  have hcont_poly : ∀ (S : Finset ℕ) (f : ℕ → ℂ), (∀ k ∈ S, 1 ≤ k) →
      Continuous fun t : ℝ =>
        ‖∑ k ∈ S, f k * (k : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
    intro S f hS
    refine (continuous_finsetSum S fun k hk => ?_).norm.pow 2
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by have := hS k hk; omega)).ne'
    exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hk0))
  have hcontL := hcont_poly (Finset.Ioc X (X * R))
    (fun n => (truncatedMoebiusDivisorSum X n : ℂ))
    (fun n hn => by have := (Finset.mem_Ioc.mp hn).1; omega)
  have hcontR : ∀ r ∈ Finset.Icc 1 R, Continuous fun t : ℝ =>
      ‖∑ m ∈ Finset.Ioc X ((X * R) / r),
        (ArithmeticFunction.moebius m : ℂ) *
          (m : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 :=
    fun r _ => hcont_poly _ _ (fun m hm => by have := (Finset.mem_Ioc.mp hm).1; omega)
  have hpt : ∀ t : ℝ,
      ‖∑ n ∈ Finset.Ioc X (X * R),
        (truncatedMoebiusDivisorSum X n : ℂ) *
          (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
      (1 + Real.log R) * ∑ r ∈ Finset.Icc 1 R,
        ‖∑ m ∈ Finset.Ioc X ((X * R) / r),
          (ArithmeticFunction.moebius m : ℂ) *
            (m : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
    intro t
    rw [collar_dirichletPoly_eq_neg_sum_pureMoebius hX, norm_neg]
    set s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
    set A : ℕ → ℂ := fun r =>
      ∑ m ∈ Finset.Ioc X ((X * R) / r), (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
    have htri : ‖∑ r ∈ Finset.Icc 1 R, (r : ℂ) ^ (-s) * A r‖ ≤
        ∑ r ∈ Finset.Icc 1 R, ‖(r : ℂ) ^ (-s)‖ * ‖A r‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => le_of_eq (norm_mul _ _))
    have hcs : (∑ r ∈ Finset.Icc 1 R, ‖(r : ℂ) ^ (-s)‖ * ‖A r‖) ^ 2 ≤
        (∑ r ∈ Finset.Icc 1 R, ‖(r : ℂ) ^ (-s)‖ ^ 2) * ∑ r ∈ Finset.Icc 1 R, ‖A r‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 R) (fun r => ‖(r : ℂ) ^ (-s)‖) (fun r => ‖A r‖)
    have hr_norm : ∑ r ∈ Finset.Icc 1 R, ‖(r : ℂ) ^ (-s)‖ ^ 2 = ∑ r ∈ Finset.Icc 1 R, (r : ℝ)⁻¹ := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr0 : 0 < r := (Finset.mem_Icc.mp hr).1
      have hre : (-s).re = -(1 / 2 : ℝ) := by dsimp [s]; simp
      rw [Complex.norm_natCast_cpow_of_pos hr0, hre, ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (Nat.cast_nonneg r)]
      have hexp : -(1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 := by norm_num
      rw [hexp, Real.rpow_neg_one]
    calc ‖∑ r ∈ Finset.Icc 1 R, (r : ℂ) ^ (-s) * A r‖ ^ 2
        ≤ (∑ r ∈ Finset.Icc 1 R, ‖(r : ℂ) ^ (-s)‖ * ‖A r‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (∑ r ∈ Finset.Icc 1 R, ‖(r : ℂ) ^ (-s)‖ ^ 2) * ∑ r ∈ Finset.Icc 1 R, ‖A r‖ ^ 2 := hcs
      _ = (∑ r ∈ Finset.Icc 1 R, (r : ℝ)⁻¹) * ∑ r ∈ Finset.Icc 1 R, ‖A r‖ ^ 2 := by rw [hr_norm]
      _ ≤ (1 + Real.log R) * ∑ r ∈ Finset.Icc 1 R, ‖A r‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (sum_Icc_inv_le_one_add_log_collar hR)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hint_sum : Continuous fun t : ℝ =>
      ∑ r ∈ Finset.Icc 1 R,
        ‖∑ m ∈ Finset.Ioc X ((X * R) / r),
          (ArithmeticFunction.moebius m : ℂ) *
            (m : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 :=
    continuous_finsetSum _ hcontR
  calc (∫ t in (1 : ℝ)..T,
        ‖∑ n ∈ Finset.Ioc X (X * R),
          (truncatedMoebiusDivisorSum X n : ℂ) *
            (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2)
      ≤ ∫ t in (1 : ℝ)..T, (1 + Real.log R) *
          ∑ r ∈ Finset.Icc 1 R,
            ‖∑ m ∈ Finset.Ioc X ((X * R) / r),
              (ArithmeticFunction.moebius m : ℂ) *
                (m : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 :=
        intervalIntegral.integral_mono_on hT (hcontL.intervalIntegrable volume 1 T)
          ((hint_sum.const_mul _).intervalIntegrable volume 1 T) (fun t _ => hpt t)
    _ = (1 + Real.log R) * ∑ r ∈ Finset.Icc 1 R,
          ∫ t in (1 : ℝ)..T,
            ‖∑ m ∈ Finset.Ioc X ((X * R) / r),
              (ArithmeticFunction.moebius m : ℂ) *
                (m : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_finset_sum fun r hr =>
            (hcontR r hr).intervalIntegrable volume 1 T]

/-! ## §2. Multiplicative gauge-twist equivariance -/

/-- **Multiplicative gauge-twist equivariance.** For any finite support `S ⊂ ℕ₊`, weight
`b : ℕ → ℂ`, and completely multiplicative `χ : ℕ → ℂ` on `ℕ₊`, twisting `b(d) ↦ b(d) χ(d)` and
`1(q) ↦ χ(q)` multiplies every restricted divisor sum at `n ≥ 1` by `χ(n)`. -/
theorem divisorSum_mul_completelyMultiplicative {S : Finset ℕ} (hS : ∀ d ∈ S, 1 ≤ d)
    (b χ : ℕ → ℂ) (hχ : ∀ d q : ℕ, 1 ≤ d → 1 ≤ q → χ (d * q) = χ d * χ q)
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ d ∈ S.filter (· ∣ n), (b d * χ d) * χ (n / d)) =
      χ n * ∑ d ∈ S.filter (· ∣ n), b d := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdS, hd_dvd⟩ := Finset.mem_filter.mp hd
  have hd1 : 1 ≤ d := hS d hdS
  have hmul : d * (n / d) = n := Nat.mul_div_cancel' hd_dvd
  have hq1 : 1 ≤ n / d := by
    by_contra h0
    rw [Nat.eq_zero_of_not_pos h0, mul_zero] at hmul
    omega
  calc (b d * χ d) * χ (n / d) = b d * (χ d * χ (n / d)) := by ring
    _ = b d * χ (d * (n / d)) := by rw [← hχ d (n / d) hd1 hq1]
    _ = χ n * b d := by rw [hmul]; ring

/-- Unimodular completely multiplicative twists leave every restricted divisor-sum modulus
unchanged. -/
theorem norm_divisorSum_mul_completelyMultiplicative_eq {S : Finset ℕ} (hS : ∀ d ∈ S, 1 ≤ d)
    (b χ : ℕ → ℂ) (hχ : ∀ d q : ℕ, 1 ≤ d → 1 ≤ q → χ (d * q) = χ d * χ q)
    (hunit : ∀ m : ℕ, 1 ≤ m → ‖χ m‖ = 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖∑ d ∈ S.filter (· ∣ n), (b d * χ d) * χ (n / d)‖ = ‖∑ d ∈ S.filter (· ∣ n), b d‖ := by
  rw [divisorSum_mul_completelyMultiplicative hS b χ hχ hn, norm_mul, hunit n hn, one_mul]

/-! ## §3. `ℓ²`-blindness of prefix-cancelled unit-sign sequences -/

private theorem norm_exp_ofReal_mul_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * I) - 1‖ ≤ |θ| := by
  have hre : (Complex.exp ((θ : ℂ) * I) - 1).re = Real.cos θ - 1 := by
    rw [Complex.exp_ofReal_mul_I]
    simp
  have him : (Complex.exp ((θ : ℂ) * I) - 1).im = Real.sin θ := by
    rw [Complex.exp_ofReal_mul_I]
    simp
  have hsq : ‖Complex.exp ((θ : ℂ) * I) - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h1 := Real.cos_two_mul (θ / 2)
      have h2 := Real.sin_sq_add_cos_sq (θ / 2)
      have h2m : 2 * (θ / 2) = θ := by ring
      rw [h2m] at h1
      linarith
    have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      have h1 := Real.sin_two_mul (θ / 2)
      have h2m : 2 * (θ / 2) = θ := by ring
      rwa [h2m] at h1
    have hpyth := Real.sin_sq_add_cos_sq (θ / 2)
    rw [hcos, hsin]
    nlinarith
  have hsin_le : |Real.sin (θ / 2)| ≤ |θ| / 2 := by
    calc |Real.sin (θ / 2)| ≤ |θ / 2| := Real.abs_sin_le_abs
      _ = |θ| / 2 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsq_le : ‖Complex.exp ((θ : ℂ) * I) - 1‖ ^ 2 ≤ |θ| ^ 2 := by
    rw [hsq]
    have h4 : 4 * Real.sin (θ / 2) ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
      rw [mul_pow, sq_abs]; ring
    rw [h4]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  nlinarith [norm_nonneg (Complex.exp ((θ : ℂ) * I) - 1), abs_nonneg θ]

private theorem norm_natCast_cpow_shift_sub_le {n : ℕ} (hn : 1 ≤ n) (s₀ : ℂ) (t t₀ : ℝ) :
    ‖(n : ℂ) ^ (-(s₀ + (t : ℂ) * I)) - (n : ℂ) ^ (-(s₀ + (t₀ : ℂ) * I))‖ ≤
      ‖(n : ℂ) ^ (-(s₀ + (t₀ : ℂ) * I))‖ * (|t - t₀| * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  have hmul : (n : ℂ) ^ (-(s₀ + (t : ℂ) * I)) =
      (n : ℂ) ^ (-(s₀ + (t₀ : ℂ) * I)) *
        Complex.exp (((-(t - t₀) * Real.log n : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, hlog, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hdiff : (n : ℂ) ^ (-(s₀ + (t : ℂ) * I)) - (n : ℂ) ^ (-(s₀ + (t₀ : ℂ) * I)) =
      (n : ℂ) ^ (-(s₀ + (t₀ : ℂ) * I)) *
        (Complex.exp (((-(t - t₀) * Real.log n : ℝ) : ℂ) * I) - 1) := by
    rw [hmul]
    ring
  rw [hdiff, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_exp_ofReal_mul_I_sub_one_le _).trans_eq ?_
  rw [abs_mul, abs_neg, abs_of_nonneg (Real.log_natCast_nonneg n)]

private def realSignInt (u : ℝ) : ℤ := if 0 ≤ u then 1 else -1

private theorem abs_realSignInt_le_one (u : ℝ) : |realSignInt u| ≤ 1 := by
  unfold realSignInt
  split_ifs <;> norm_num

private theorem cast_realSignInt_mul (u : ℝ) : (realSignInt u : ℝ) * u = |u| := by
  unfold realSignInt
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (not_le.mp h)]

private theorem norm_le_abs_re_add_abs_im_aux (w : ℂ) : ‖w‖ ≤ |w.re| + |w.im| := by
  have hsq : ‖w‖ ^ 2 ≤ (|w.re| + |w.im|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [abs_nonneg w.re, abs_nonneg w.im, sq_abs w.re, sq_abs w.im]
  nlinarith [norm_nonneg w, abs_nonneg w.re, abs_nonneg w.im]

/-- **`ℓ²`-blindness of prefix-cancelled unit-sign sequences.**
For every `X ≥ 2` and `T ≥ 2`, there exists `c : ℕ → ℤ` satisfying `c(1) = 1`, `c(n) = 0` on
`2 ≤ n ≤ X`, `|c(n)| ≤ 1` for all `n` (hence `∑_{1 ≤ n ≤ M} c(n)² ≤ M` for all `M`), and
`∫_1^T ‖∑_{X < n ≤ 2X} c(n) n^{-1/2 - it}‖² dt ≥ X / (100 log(2X))`. -/
theorem exists_prefix_zero_unit_sign_criticalMoment_ge {X : ℕ} (hX : 2 ≤ X)
    {T : ℝ} (hT : 2 ≤ T) :
    ∃ c : ℕ → ℤ,
      c 1 = 1 ∧
      (∀ n ∈ Finset.Icc 2 X, c n = 0) ∧
      (∀ n : ℕ, |c n| ≤ 1) ∧
      (∀ M : ℕ, ∑ n ∈ Finset.Icc 1 M, (c n : ℝ) ^ 2 ≤ M) ∧
      (X : ℝ) / (100 * Real.log (2 * X)) ≤
        ∫ t in (1 : ℝ)..T,
          ‖∑ n ∈ Finset.Ioc X (2 * X),
            (c n : ℂ) * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
  have hX_pos : (0 : ℝ) < X := by positivity
  have h2X_ge4 : (4 : ℝ) ≤ 2 * (X : ℝ) := by
    have : (2 : ℝ) ≤ X := by exact_mod_cast hX
    linarith
  have hlog_gt1 : 1 < Real.log (2 * (X : ℝ)) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith [Real.exp_one_lt_d9]
  have hlog_pos : 0 < Real.log (2 * (X : ℝ)) := lt_trans zero_lt_one hlog_gt1
  let t₀ : ℝ := 3 / 2
  let z : ℕ → ℂ := fun n => (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t₀ : ℂ) * I))
  have hz_norm : ∀ n : ℕ, 1 ≤ n → ‖z n‖ = (Real.sqrt n)⁻¹ := by
    intro n hn1
    dsimp [z]
    rw [Complex.norm_natCast_cpow_of_pos hn1]
    have hre : (-(((1 / 2 : ℝ) : ℂ) + (t₀ : ℂ) * I)).re = -(1 / 2 : ℝ) := by simp
    rw [hre, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
  have hcard : ((Finset.Ioc X (2 * X)).card : ℝ) = X := by
    rw [Nat.card_Ioc]
    have : 2 * X - X = X := by omega
    rw [this]
  have hsum_norm : Real.sqrt X / Real.sqrt 2 ≤
      (∑ n ∈ Finset.Ioc X (2 * X), |(z n).re|) + ∑ n ∈ Finset.Ioc X (2 * X), |(z n).im| := by
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ n ∈ Finset.Ioc X (2 * X),
        (Real.sqrt 2 * Real.sqrt X)⁻¹ ≤ |(z n).re| + |(z n).im| := by
      intro n hn
      obtain ⟨hnX, hn2X⟩ := Finset.mem_Ioc.mp hn
      have hn1 : 1 ≤ n := by omega
      have hn_le : (n : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast hn2X
      have hsq_le : Real.sqrt n ≤ Real.sqrt 2 * Real.sqrt X := by
        rw [← Real.sqrt_mul zero_le_two]
        exact Real.sqrt_le_sqrt hn_le
      have hinv : (Real.sqrt 2 * Real.sqrt X)⁻¹ ≤ (Real.sqrt n)⁻¹ :=
        inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) hsq_le
      exact (hinv.trans_eq (hz_norm n hn1).symm).trans (norm_le_abs_re_add_abs_im_aux (z n))
    have h1 := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at h1
    have hval : (X : ℝ) * (Real.sqrt 2 * Real.sqrt X)⁻¹ = Real.sqrt X / Real.sqrt 2 := by
      have hsqX : (X : ℝ) = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX_pos.le).symm
      have hsX0 : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX_pos).ne'
      have hs20 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr two_pos).ne'
      conv_lhs => rw [hsqX]
      field_simp [hsX0, hs20]
    rwa [hval] at h1
  let buildC : (ℕ → ℝ) → ℕ → ℤ := fun f n =>
    if n = 1 then 1 else if n ∈ Finset.Ioc X (2 * X) then realSignInt (f n) else 0
  obtain ⟨c, hc1, hc_pref, hc_abs, hc_peak⟩ :
      ∃ c : ℕ → ℤ, c 1 = 1 ∧ (∀ n ∈ Finset.Icc 2 X, c n = 0) ∧ (∀ n : ℕ, |c n| ≤ 1) ∧
        Real.sqrt X / (2 * Real.sqrt 2) ≤ ‖∑ n ∈ Finset.Ioc X (2 * X), (c n : ℂ) * z n‖ := by
    have hprops : ∀ f : ℕ → ℝ, buildC f 1 = 1 ∧
        (∀ n ∈ Finset.Icc 2 X, buildC f n = 0) ∧ (∀ n : ℕ, |buildC f n| ≤ 1) := by
      intro f
      refine ⟨by simp [buildC], fun n hn => ?_, fun n => ?_⟩
      · obtain ⟨hn2, hnX⟩ := Finset.mem_Icc.mp hn
        have hn_ne1 : n ≠ 1 := by omega
        have hn_not : n ∉ Finset.Ioc X (2 * X) := by
          simp only [Finset.mem_Ioc]
          omega
        simp [buildC, hn_ne1, hn_not]
      · dsimp [buildC]
        split_ifs
        · norm_num
        · exact abs_realSignInt_le_one _
        · norm_num
    rcases le_or_gt (Real.sqrt X / (2 * Real.sqrt 2))
        (∑ n ∈ Finset.Ioc X (2 * X), |(z n).re|) with hre_big | him_big
    · obtain ⟨hp1, hp2, hp3⟩ := hprops (fun n => (z n).re)
      refine ⟨buildC (fun n => (z n).re), hp1, hp2, hp3, hre_big.trans ?_⟩
      have hre_sum : (∑ n ∈ Finset.Ioc X (2 * X),
          (buildC (fun k => (z k).re) n : ℂ) * z n).re =
          ∑ n ∈ Finset.Ioc X (2 * X), |(z n).re| := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn_ne1 : n ≠ 1 := by have := (Finset.mem_Ioc.mp hn).1; omega
        simp only [buildC, if_neg hn_ne1, if_pos hn]
        have hcast : ((realSignInt (z n).re : ℂ) * z n).re =
            (realSignInt (z n).re : ℝ) * (z n).re := by simp [Complex.mul_re]
        rw [hcast, cast_realSignInt_mul]
      rw [← hre_sum]
      exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
    · have him_ge : Real.sqrt X / (2 * Real.sqrt 2) ≤
          ∑ n ∈ Finset.Ioc X (2 * X), |(z n).im| := by linarith
      obtain ⟨hp1, hp2, hp3⟩ := hprops (fun n => (z n).im)
      refine ⟨buildC (fun n => (z n).im), hp1, hp2, hp3, him_ge.trans ?_⟩
      have him_sum : (∑ n ∈ Finset.Ioc X (2 * X),
          (buildC (fun k => (z k).im) n : ℂ) * z n).im =
          ∑ n ∈ Finset.Ioc X (2 * X), |(z n).im| := by
        rw [Complex.im_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn_ne1 : n ≠ 1 := by have := (Finset.mem_Ioc.mp hn).1; omega
        simp only [buildC, if_neg hn_ne1, if_pos hn]
        have hcast : ((realSignInt (z n).im : ℂ) * z n).im =
            (realSignInt (z n).im : ℝ) * (z n).im := by simp [Complex.mul_im]
        rw [hcast, cast_realSignInt_mul]
      rw [← him_sum]
      exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
  refine ⟨c, hc1, hc_pref, hc_abs, fun M => ?_, ?_⟩
  · calc ∑ n ∈ Finset.Icc 1 M, (c n : ℝ) ^ 2
        ≤ ∑ _n ∈ Finset.Icc 1 M, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n _ => ?_
          have h1 : |(c n : ℝ)| ≤ 1 := by exact_mod_cast hc_abs n
          nlinarith [sq_abs (c n : ℝ), abs_nonneg (c n : ℝ)]
      _ = M := by simp
  · obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = 1 / (8 * Real.log (2 * (X : ℝ))) := ⟨_, rfl⟩
    have hη_pos : 0 < η := by rw [hη_def]; positivity
    have hη_lt : η < 1 / 8 := by
      rw [hη_def, div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h1_low : 1 ≤ t₀ - η := by dsimp [t₀]; linarith
    have hlow_high : t₀ - η ≤ t₀ + η := by linarith
    have hhigh_T : t₀ + η ≤ T := by dsimp [t₀]; linarith
    have hcont : Continuous fun t : ℝ =>
        ‖∑ n ∈ Finset.Ioc X (2 * X),
          (c n : ℂ) * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
      refine (continuous_finsetSum _ fun n hn => ?_).norm.pow 2
      have hn0 : (n : ℂ) ≠ 0 := by
        have := (Finset.mem_Ioc.mp hn).1
        exact_mod_cast (show 0 < n by omega).ne'
      exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))
    have hpt_band : ∀ t ∈ Set.Icc (t₀ - η) (t₀ + η),
        (X : ℝ) / 25 ≤
          ‖∑ n ∈ Finset.Ioc X (2 * X),
            (c n : ℂ) * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
      intro t ht
      have habs_t : |t - t₀| ≤ η := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hdiff_le : ‖(∑ n ∈ Finset.Ioc X (2 * X),
            (c n : ℂ) * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))) -
          ∑ n ∈ Finset.Ioc X (2 * X), (c n : ℂ) * z n‖ ≤ Real.sqrt X / 8 := by
        rw [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans ?_
        have hterm : ∀ n ∈ Finset.Ioc X (2 * X),
            ‖(c n : ℂ) * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) - (c n : ℂ) * z n‖ ≤
              (Real.sqrt X)⁻¹ * (1 / 8) := by
          intro n hn
          obtain ⟨hnX, hn2X⟩ := Finset.mem_Ioc.mp hn
          have hn1 : 1 ≤ n := by omega
          rw [← mul_sub, norm_mul]
          have hcn : ‖(c n : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]
            exact_mod_cast hc_abs n
          have hsh := norm_natCast_cpow_shift_sub_le hn1 ((1 / 2 : ℝ) : ℂ) t t₀
          have hzn_le : ‖z n‖ ≤ (Real.sqrt X)⁻¹ := by
            rw [hz_norm n hn1]
            exact inv_anti₀ (Real.sqrt_pos.mpr hX_pos)
              (Real.sqrt_le_sqrt (by exact_mod_cast hnX.le))
          have hlog_le : |t - t₀| * Real.log n ≤ 1 / 8 := by
            have hln : Real.log n ≤ Real.log (2 * (X : ℝ)) :=
              Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hn2X)
            calc |t - t₀| * Real.log n
                ≤ η * Real.log (2 * (X : ℝ)) :=
                  mul_le_mul habs_t hln (Real.log_natCast_nonneg n) hη_pos.le
              _ = 1 / 8 := by
                  rw [hη_def]
                  field_simp [hlog_pos.ne']
          calc ‖(c n : ℂ)‖ *
                ‖(n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) - z n‖
              ≤ 1 * (‖z n‖ * (|t - t₀| * Real.log n)) :=
                mul_le_mul hcn hsh (norm_nonneg _) zero_le_one
            _ ≤ (Real.sqrt X)⁻¹ * (1 / 8) := by
                rw [one_mul]
                exact mul_le_mul hzn_le hlog_le (by positivity) (by positivity)
        refine (Finset.sum_le_sum hterm).trans_eq ?_
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        have hsqX : (X : ℝ) = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX_pos.le).symm
        have hsX0 : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX_pos).ne'
        conv_lhs => rw [hsqX]
        field_simp [hsX0]
      have hnum_const : 1 / 5 ≤ 1 / (2 * Real.sqrt 2) - 1 / 8 := by
        have hs2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
        have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
        have h26 : 13 * Real.sqrt 2 ≤ 20 := by nlinarith [hs2_pos, hsq2]
        rw [show (1 / 5 : ℝ) ≤ 1 / (2 * Real.sqrt 2) - 1 / 8 ↔ 13 / 40 ≤ 1 / (2 * Real.sqrt 2) by
          constructor <;> intro h <;> linarith]
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      have hnorm_ge : Real.sqrt X / 5 ≤
          ‖∑ n ∈ Finset.Ioc X (2 * X),
            (c n : ℂ) * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ := by
        set S_t : ℂ := ∑ n ∈ Finset.Ioc X (2 * X),
          (c n : ℂ) * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
        set S_0 : ℂ := ∑ n ∈ Finset.Ioc X (2 * X), (c n : ℂ) * z n
        have htri : ‖S_0‖ ≤ ‖S_t‖ + ‖S_t - S_0‖ := by
          have h1 : S_0 = S_t - (S_t - S_0) := by ring
          have h2 := norm_sub_le S_t (S_t - S_0)
          rwa [← h1] at h2
        have hmul_const := mul_le_mul_of_nonneg_right hnum_const (Real.sqrt_nonneg X)
        linarith
      calc (X : ℝ) / 25 = (Real.sqrt X / 5) ^ 2 := by
            rw [div_pow, Real.sq_sqrt hX_pos.le]
            norm_num
        _ ≤ ‖∑ n ∈ Finset.Ioc X (2 * X),
              (c n : ℂ) * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 :=
            pow_le_pow_left₀ (by positivity) hnorm_ge 2
    have hband_int : (X : ℝ) / (100 * Real.log (2 * X)) ≤
        ∫ t in (t₀ - η)..(t₀ + η),
          ‖∑ n ∈ Finset.Ioc X (2 * X),
            (c n : ℂ) * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
      have hmono := intervalIntegral.integral_mono_on hlow_high intervalIntegrable_const
        (hcont.intervalIntegrable volume (t₀ - η) (t₀ + η)) hpt_band
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      refine le_trans (le_of_eq ?_) hmono
      have hlen : (t₀ + η) - (t₀ - η) = 2 * η := by ring
      rw [hlen, hη_def]
      field_simp [hlog_pos.ne']
      ring
    refine hband_int.trans ?_
    have hadj1 := intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable volume 1 (t₀ - η))
      (hcont.intervalIntegrable volume (t₀ - η) (t₀ + η))
    have hadj2 := intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable volume 1 (t₀ + η))
      (hcont.intervalIntegrable volume (t₀ + η) T)
    have hnn1 : 0 ≤ ∫ t in (1 : ℝ)..(t₀ - η),
        ‖∑ n ∈ Finset.Ioc X (2 * X),
          (c n : ℂ) * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 :=
      intervalIntegral.integral_nonneg h1_low fun _ _ => sq_nonneg _
    have hnn2 : 0 ≤ ∫ t in (t₀ + η)..T,
        ‖∑ n ∈ Finset.Ioc X (2 * X),
          (c n : ℂ) * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 :=
      intervalIntegral.integral_nonneg hhigh_T fun _ _ => sq_nonneg _
    linarith

/-! ## §4. Shifted-inverse multiplicative countermodel on `ℕ` -/

/-- Spectral shift `s_δ = (½ - δ) - 2i` placing the real evaluation point `1 - δ ∈ (½, 1)` at
critical-line height `t = 2`. -/
def shiftedInverseOffset (δ : ℝ) : ℂ := ((1 / 2 - δ : ℝ) : ℂ) - 2 * I

/-- Shifted Möbius arithmetic function `a_δ(n) = μ(n) n^{-s_δ}` (`0` at `n = 0`). -/
def shiftedInverseCoeff (δ : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-shiftedInverseOffset δ),
    by simp⟩

/-- Shifted zeta arithmetic function `b_δ(d) = d^{-s_δ}` (`0` at `d = 0`), the exact Dirichlet
convolution inverse of `shiftedInverseCoeff δ`. -/
def shiftedZetaCoeff (δ : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun d => if d = 0 then 0 else (d : ℂ) ^ (-shiftedInverseOffset δ), by simp⟩

/-- Meromorphic target `F_δ(s) = ζ(s + s_δ)⁻¹` extending `L(a_δ, s)`. -/
def shiftedInverseFn (δ : ℝ) (s : ℂ) : ℂ :=
  (riemannZeta (s + shiftedInverseOffset δ))⁻¹

theorem isMultiplicative_shiftedZetaCoeff (δ : ℝ) :
    (shiftedZetaCoeff δ).IsMultiplicative := by
  refine ⟨by simp [shiftedZetaCoeff], fun {m n} _ => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [shiftedZetaCoeff]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [shiftedZetaCoeff]
  simp only [shiftedZetaCoeff, ArithmeticFunction.coe_mk, mul_eq_zero, hm, hn, or_self, ↓reduceIte]
  simpa using Complex.mul_cpow_ofReal_nonneg (a := (m : ℝ)) (b := (n : ℝ))
    (by positivity) (by positivity) (-shiftedInverseOffset δ)

theorem isMultiplicative_shiftedInverseCoeff (δ : ℝ) :
    (shiftedInverseCoeff δ).IsMultiplicative := by
  have heq : shiftedInverseCoeff δ =
      ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ).pmul
        (shiftedZetaCoeff δ) := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [shiftedInverseCoeff]
    · simp [shiftedInverseCoeff, shiftedZetaCoeff, hn]
  rw [heq]
  exact ArithmeticFunction.isMultiplicative_moebius.intCast.pmul
    (isMultiplicative_shiftedZetaCoeff δ)

/-- Exact Dirichlet convolution identity `a_δ * b_δ = 1` in `ArithmeticFunction ℂ`. -/
theorem shiftedInverseCoeff_mul_shiftedZetaCoeff (δ : ℝ) :
    shiftedInverseCoeff δ * shiftedZetaCoeff δ = 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply]
  have hsum : (∑ x ∈ Nat.divisorsAntidiagonal n,
        shiftedInverseCoeff δ x.1 * shiftedZetaCoeff δ x.2) =
      (∑ x ∈ Nat.divisorsAntidiagonal n, (ArithmeticFunction.moebius x.1 : ℂ)) *
        (n : ℂ) ^ (-shiftedInverseOffset δ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hx1 : x.1 ≠ 0 := fun h0 => hn0 (by rw [← hmul, h0, zero_mul])
    have hx2 : x.2 ≠ 0 := fun h0 => hn0 (by rw [← hmul, h0, mul_zero])
    simp only [shiftedInverseCoeff, shiftedZetaCoeff, ArithmeticFunction.coe_mk, hx1, hx2,
      ↓reduceIte]
    have hcpow : (x.1 : ℂ) ^ (-shiftedInverseOffset δ) * (x.2 : ℂ) ^ (-shiftedInverseOffset δ) =
        (n : ℂ) ^ (-shiftedInverseOffset δ) := by
      conv_rhs => rw [← hmul]
      symm
      simpa using Complex.mul_cpow_ofReal_nonneg (a := (x.1 : ℝ)) (b := (x.2 : ℝ))
        (by positivity) (by positivity) (-shiftedInverseOffset δ)
    rw [mul_assoc, hcpow]
  rw [hsum, Nat.sum_divisorsAntidiagonal (fun d _ => (ArithmeticFunction.moebius d : ℂ)),
    ← Int.cast_sum, sum_divisors_moebius_eq_ite]
  split_ifs with hn1
  · subst hn1
    simp
  · simp

theorem norm_shiftedZetaCoeff_le_one {δ : ℝ} (hδ1 : δ ≤ 1 / 2) (d : ℕ) :
    ‖shiftedZetaCoeff δ d‖ ≤ 1 := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [shiftedZetaCoeff]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  simp only [shiftedZetaCoeff, ArithmeticFunction.coe_mk, hd, ↓reduceIte]
  rw [Complex.norm_natCast_cpow_of_pos hd_pos]
  have hre : (-shiftedInverseOffset δ).re = -(1 / 2 - δ) := by
    unfold shiftedInverseOffset
    simp
  rw [hre]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd_pos) (by linarith)

theorem norm_shiftedInverseCoeff_le_one {δ : ℝ} (hδ1 : δ ≤ 1 / 2) (n : ℕ) :
    ‖shiftedInverseCoeff δ n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [shiftedInverseCoeff]
  have heq : shiftedInverseCoeff δ n =
      (ArithmeticFunction.moebius n : ℂ) * shiftedZetaCoeff δ n := by
    simp [shiftedInverseCoeff, shiftedZetaCoeff, hn]
  rw [heq, norm_mul]
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  exact mul_le_one₀ hμ (norm_nonneg _) (norm_shiftedZetaCoeff_le_one hδ1 n)

theorem summable_normSq_shiftedZetaCoeff_div {δ : ℝ} (hδ1 : δ < 1 / 2) :
    Summable fun d : ℕ => ‖shiftedZetaCoeff δ d‖ ^ 2 / (d : ℝ) := by
  have hpow : Summable fun d : ℕ => ((d : ℝ) ^ (2 - 2 * δ))⁻¹ := by
    have hexp : 1 < 2 - 2 * δ := by linarith
    exact (Real.summable_nat_rpow_inv.mpr hexp)
  refine hpow.congr fun d => ?_
  rcases eq_or_ne d 0 with rfl | hd
  · have h20 : (2 - 2 * δ : ℝ) ≠ 0 := by linarith
    simp [shiftedZetaCoeff, Real.zero_rpow h20]
  · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    have hdR_pos : (0 : ℝ) < d := by exact_mod_cast hd_pos
    simp only [shiftedZetaCoeff, ArithmeticFunction.coe_mk, hd, ↓reduceIte]
    rw [Complex.norm_natCast_cpow_of_pos hd_pos]
    have hre : (-shiftedInverseOffset δ).re = -(1 / 2 - δ) := by
      unfold shiftedInverseOffset
      simp
    rw [hre, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hdR_pos.le, div_eq_mul_inv,
      ← Real.rpow_neg_one (d : ℝ), ← Real.rpow_add hdR_pos, ← Real.rpow_neg hdR_pos.le]
    congr 1
    push_cast
    ring

theorem lSeries_shiftedInverseCoeff (δ : ℝ) {s : ℂ} (hs : 1 / 2 + δ < s.re) :
    LSeries (fun n => shiftedInverseCoeff δ n) s = shiftedInverseFn δ s := by
  have hre : 1 < (s + shiftedInverseOffset δ).re := by
    unfold shiftedInverseOffset
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.re_ofNat, Complex.I_re, mul_zero, Complex.im_ofNat, Complex.I_im, mul_one, sub_self]
    linarith
  have hterm : ∀ n : ℕ, LSeries.term (fun k => shiftedInverseCoeff δ k) s n =
      LSeries.term (fun k => (ArithmeticFunction.moebius k : ℂ)) (s + shiftedInverseOffset δ) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      simp only [shiftedInverseCoeff, ArithmeticFunction.coe_mk, hn, ↓reduceIte]
      rw [Complex.cpow_neg, Complex.cpow_add _ _ hn0]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  rw [show LSeries (fun k => shiftedInverseCoeff δ k) s =
      LSeries (fun k => (ArithmeticFunction.moebius k : ℂ)) (s + shiftedInverseOffset δ) from
    tsum_congr hterm]
  unfold shiftedInverseFn
  apply eq_inv_of_mul_eq_one_left
  have h := LSeries_one_mul_Lseries_moebius hre
  rwa [LSeries_one_eq_riemannZeta hre, mul_comm] at h

/-- On the band `[1, 3]`, `½ + it + s_δ = (1 - δ) + i(t - 2)` has `|Im| ≤ 1 ≤ 9/2`, so `ξ` and `ζ`
are unconditionally zero-free and `shiftedInverseFn δ (½ + it)` is continuous and nonvanishing. -/
theorem continuousOn_shiftedInverseFn_Icc_one_three {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ContinuousOn (fun t : ℝ => shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
      (Set.Icc 1 3) := by
  intro t ht
  have hw_eq : ∀ u : ℝ, ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I + shiftedInverseOffset δ =
      ((1 - δ : ℝ) : ℂ) + ((u - 2 : ℝ) : ℂ) * I := by
    intro u
    unfold shiftedInverseOffset
    push_cast
    ring
  have hw_ne1 : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I + shiftedInverseOffset δ ≠ 1 := by
    rw [hw_eq t]
    intro h1
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hw_zeta_ne0 : riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I + shiftedInverseOffset δ) ≠ 0 := by
    rw [hw_eq t]
    have hre : 0 < (((1 - δ : ℝ) : ℂ) + ((t - 2 : ℝ) : ℂ) * I).re := by simp; linarith
    have hne1 : (((1 - δ : ℝ) : ℂ) + ((t - 2 : ℝ) : ℂ) * I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have him : |(((1 - δ : ℝ) : ℂ) + ((t - 2 : ℝ) : ℂ) * I).im| ≤ 9 / 2 := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
      rw [abs_le]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact MultiscaleMollifiedZetaField.riemannZeta_ne_zero_of_xi_ne_zero hre hne1
      (_root_.RHTower.xi_ne_zero_of_abs_im_le_nine_halves him)
  have hcζ : ContinuousAt
      (fun u : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I + shiftedInverseOffset δ)) t :=
    ContinuousAt.comp (g := riemannZeta)
      (f := fun u : ℝ => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I + shiftedInverseOffset δ)
      (differentiableAt_riemannZeta hw_ne1).continuousAt (by fun_prop)
  exact (hcζ.inv₀ hw_zeta_ne0).continuousWithinAt

/-- **Shifted-inverse multiplicative countermodel on `ℕ`.**
For every `δ ∈ (0, ½)`, the multiplicative pair `(shiftedInverseCoeff δ, shiftedZetaCoeff δ)`
satisfies exact Dirichlet inversion, unit norm bounds, weighted `ℓ²` summability
`∑ ‖b_δ(d)‖² / d < ∞`, and `L(a_δ, s) = ζ(s + s_δ)⁻¹` on `Re s > ½ + δ`, while there exists
`κ > 0` such that for every `X ≥ 2`:
1. on `[1, 3]` (where `F_δ(½ + it)` is unconditionally continuous and pole-free),
   `∫_1^3 ‖F_δ(½ + it) ∑_{d=1}^X b_δ(d) d^{-1/2-it}‖² dt ≥ κ X^{2δ} / log(2X)`;
2. for every `T ≥ 3`, the Lebesgue `L²` integral on `[1, T]` satisfies
   `ENNReal.ofReal (κ X^{2δ} / log(2X)) ≤ ∫⁻_{t ∈ (1, T]} ‖F_δ(½ + it) B_{δ,X}(½ + it)‖² dt`
   (and the same lower bound holds for the Bochner integral whenever `F_δ B_{δ,X}` is square
   integrable on `[1, T]`). -/
theorem exists_shiftedInverse_countermodel_blowup {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    (shiftedInverseCoeff δ).IsMultiplicative ∧
    (shiftedZetaCoeff δ).IsMultiplicative ∧
    shiftedInverseCoeff δ * shiftedZetaCoeff δ = 1 ∧
    (∀ n : ℕ, ‖shiftedInverseCoeff δ n‖ ≤ 1) ∧
    (∀ d : ℕ, ‖shiftedZetaCoeff δ d‖ ≤ 1) ∧
    Summable (fun d : ℕ => ‖shiftedZetaCoeff δ d‖ ^ 2 / (d : ℝ)) ∧
    (∀ s : ℂ, 1 / 2 + δ < s.re →
      LSeries (fun n => shiftedInverseCoeff δ n) s = shiftedInverseFn δ s) ∧
    ∃ κ : ℝ, 0 < κ ∧ ∀ {X : ℕ}, 2 ≤ X →
      (κ * (X : ℝ) ^ (2 * δ) / Real.log (2 * X) ≤
        ∫ t in (1 : ℝ)..3,
          ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            ∑ d ∈ Finset.Icc 1 X,
              shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2) ∧
      (∀ {T : ℝ}, 3 ≤ T →
        ENNReal.ofReal (κ * (X : ℝ) ^ (2 * δ) / Real.log (2 * X)) ≤
          ∫⁻ t in Set.Ioc (1 : ℝ) T,
            ENNReal.ofReal (‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
              ∑ d ∈ Finset.Icc 1 X,
                shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2)) := by
  refine ⟨isMultiplicative_shiftedInverseCoeff δ, isMultiplicative_shiftedZetaCoeff δ,
    shiftedInverseCoeff_mul_shiftedZetaCoeff δ, norm_shiftedInverseCoeff_le_one hδ1.le,
    norm_shiftedZetaCoeff_le_one hδ1.le, summable_normSq_shiftedZetaCoeff_div hδ1,
    fun s hs => lSeries_shiftedInverseCoeff δ hs, ?_⟩
  have hcontF_on := continuousOn_shiftedInverseFn_Icc_one_three hδ0 hδ1
  have hw2 : ((1 / 2 : ℝ) : ℂ) + (2 : ℂ) * I + shiftedInverseOffset δ = ((1 - δ : ℝ) : ℂ) := by
    unfold shiftedInverseOffset
    push_cast
    ring
  have hζ2_ne0 : riemannZeta ((1 - δ : ℝ) : ℂ) ≠ 0 := by
    refine MultiscaleMollifiedZetaField.riemannZeta_ne_zero_of_xi_ne_zero
      (by simp; linarith) (by intro h; have := congrArg Complex.re h; simp at this; linarith) ?_
    exact _root_.RHTower.xi_ne_zero_of_abs_im_le_nine_halves (by simp)
  have hF2_pos : 0 < ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (2 : ℂ) * I)‖ := by
    unfold shiftedInverseFn
    rw [hw2, norm_inv, inv_pos]
    exact norm_pos_iff.mpr hζ2_ne0
  set c₁ : ℝ := ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (2 : ℂ) * I)‖ / 2
  have hc₁_pos : 0 < c₁ := half_pos hF2_pos
  have hcF_at2 : ContinuousAt
      (fun t : ℝ => ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) 2 := by
    have hmem : Set.Icc (1 : ℝ) 3 ∈ 𝓝 (2 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
    exact (hcontF_on.norm.continuousWithinAt (by norm_num : (2 : ℝ) ∈ Set.Icc 1 3)).continuousAt hmem
  have hev_c₁ : ∀ᶠ t : ℝ in 𝓝 (2 : ℝ),
      c₁ ≤ ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    hcF_at2.eventually (ge_mem_nhds (by dsimp [c₁]; linarith))
  obtain ⟨r₀, hr₀_pos, hr₀_ball⟩ := Metric.eventually_nhds_iff.mp hev_c₁
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = min (r₀ / 2) (1 / 2) := ⟨_, rfl⟩
  have hr_pos : 0 < r := by rw [hr_def]; exact lt_min (half_pos hr₀_pos) (by norm_num)
  have hr_le_half : r ≤ 1 / 2 := by rw [hr_def]; exact min_le_right _ _
  have hr_lt_r₀ : r < r₀ := by
    have : r ≤ r₀ / 2 := by rw [hr_def]; exact min_le_left _ _
    linarith
  have hc₁_band : ∀ t : ℝ, |t - 2| ≤ r →
      c₁ ≤ ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    intro t ht
    exact hr₀_ball (by rw [Real.dist_eq]; exact lt_of_le_of_lt ht hr_lt_r₀)
  refine ⟨c₁ ^ 2 * r / 2, by positivity, fun {X} hX => ?_⟩
  have hX_pos : (0 : ℝ) < X := by positivity
  have hlog_gt1 : 1 < Real.log (2 * (X : ℝ)) := by
    rw [Real.lt_log_iff_exp_lt (by have : (2 : ℝ) ≤ X := by exact_mod_cast hX; linarith)]
    linarith [Real.exp_one_lt_d9]
  have hlog_pos : 0 < Real.log (2 * (X : ℝ)) := lt_trans zero_lt_one hlog_gt1
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = r / Real.log (2 * (X : ℝ)) := ⟨_, rfl⟩
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  have hη_lt_r : η < r := by
    rw [hη_def, div_lt_iff₀ hlog_pos]
    nlinarith
  have hη_le_half : η ≤ 1 / 2 := hη_lt_r.le.trans hr_le_half
  have hterm_eq : ∀ (d : ℕ), 1 ≤ d → ∀ (t : ℝ),
      shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        (d : ℂ) ^ (-(((1 - δ : ℝ) : ℂ) + ((t - 2 : ℝ) : ℂ) * I)) := by
    intro d hd1 t
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show 0 < d from hd1).ne'
    simp only [shiftedZetaCoeff, ArithmeticFunction.coe_mk, (show d ≠ 0 by omega), ↓reduceIte]
    rw [← Complex.cpow_add _ _ hd0]
    congr 1
    unfold shiftedInverseOffset
    push_cast
    ring
  set S₂ : ℝ := ∑ d ∈ Finset.Icc 1 X, (d : ℝ) ^ (-(1 - δ))
  have hS₂_ge : (X : ℝ) ^ δ ≤ S₂ := by
    have hmin : ∀ d ∈ Finset.Icc 1 X, (X : ℝ) ^ (-(1 - δ)) ≤ (d : ℝ) ^ (-(1 - δ)) := by
      intro d hd
      obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.mp hd
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hd1) (by exact_mod_cast hdX)
        (by linarith)
    have hsum_ge := Finset.sum_le_sum hmin
    rw [Finset.sum_const, Nat.card_Icc, show X + 1 - 1 = X by omega, nsmul_eq_mul] at hsum_ge
    refine le_trans (le_of_eq ?_) hsum_ge
    conv_rhs => rw [← Real.rpow_one (X : ℝ)]
    rw [← Real.rpow_add hX_pos]
    congr 1
    ring
  have hB_at2 : (∑ d ∈ Finset.Icc 1 X,
        shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (2 : ℂ) * I))) = (S₂ : ℂ) := by
    dsimp [S₂]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    rw [hterm_eq d hd1 2]
    have hsub : (((1 - δ : ℝ) : ℂ) + ((2 - 2 : ℝ) : ℂ) * I) = ((1 - δ : ℝ) : ℂ) := by simp
    rw [hsub, ← Complex.ofReal_natCast, ← Complex.ofReal_neg,
      Complex.ofReal_cpow (Nat.cast_nonneg d)]
  have hpt_band : ∀ t ∈ Set.Icc (2 - η) (2 + η),
      c₁ ^ 2 * (X : ℝ) ^ (2 * δ) / 4 ≤
        ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          ∑ d ∈ Finset.Icc 1 X,
            shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
    intro t ht
    have habs_t : |t - 2| ≤ η := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hc₁_t : c₁ ≤ ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
      hc₁_band t (habs_t.trans hη_lt_r.le)
    have hdiff_B : ‖(∑ d ∈ Finset.Icc 1 X,
          shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))) - (S₂ : ℂ)‖ ≤
        S₂ / 2 := by
      rw [← hB_at2, ← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have hterm_diff : ∀ d ∈ Finset.Icc 1 X,
          ‖shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) -
            shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (2 : ℂ) * I))‖ ≤
            (d : ℝ) ^ (-(1 - δ)) * (1 / 2) := by
        intro d hd
        obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.mp hd
        rw [hterm_eq d hd1 t, hterm_eq d hd1 2]
        have hsh := norm_natCast_cpow_shift_sub_le hd1 ((1 - δ : ℝ) : ℂ) (t - 2) 0
        simp only [Complex.ofReal_zero, zero_mul, add_zero, sub_zero] at hsh
        have hnorm0 : ‖(d : ℂ) ^ (-((1 - δ : ℝ) : ℂ))‖ = (d : ℝ) ^ (-(1 - δ)) := by
          rw [Complex.norm_natCast_cpow_of_pos hd1]
          simp
        rw [hnorm0] at hsh
        have hlog_le : |t - 2| * Real.log d ≤ 1 / 2 := by
          have hd_le2X : (d : ℝ) ≤ 2 * (X : ℝ) := by
            have : (d : ℝ) ≤ X := by exact_mod_cast hdX
            linarith
          have hld : Real.log d ≤ Real.log (2 * (X : ℝ)) :=
            Real.log_le_log (by exact_mod_cast hd1) hd_le2X
          calc |t - 2| * Real.log d
              ≤ η * Real.log (2 * (X : ℝ)) :=
                mul_le_mul habs_t hld (Real.log_natCast_nonneg d) hη_pos.le
            _ = r := by rw [hη_def, div_mul_cancel₀ _ hlog_pos.ne']
            _ ≤ 1 / 2 := hr_le_half
        exact hsh.trans (mul_le_mul_of_nonneg_left hlog_le (Real.rpow_nonneg (Nat.cast_nonneg d) _))
      refine (Finset.sum_le_sum hterm_diff).trans_eq ?_
      rw [← Finset.sum_mul]
      dsimp [S₂]
      ring
    have hB_ge : (X : ℝ) ^ δ / 2 ≤
        ‖∑ d ∈ Finset.Icc 1 X,
          shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ := by
      set B_t : ℂ := ∑ d ∈ Finset.Icc 1 X,
        shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
      have hS₂_nn : 0 ≤ S₂ := (Real.rpow_nonneg hX_pos.le δ).trans hS₂_ge
      have htri : S₂ ≤ ‖B_t‖ + ‖B_t - (S₂ : ℂ)‖ := by
        have h1 : (S₂ : ℂ) = B_t - (B_t - (S₂ : ℂ)) := by ring
        have h2 := norm_sub_le B_t (B_t - (S₂ : ℂ))
        rw [← h1, Complex.norm_real, Real.norm_of_nonneg hS₂_nn] at h2
        exact h2
      linarith
    rw [norm_mul]
    have hprod_ge : c₁ * ((X : ℝ) ^ δ / 2) ≤
        ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
          ‖∑ d ∈ Finset.Icc 1 X,
            shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ :=
      mul_le_mul hc₁_t hB_ge (by positivity) hc₁_pos.le
    calc c₁ ^ 2 * (X : ℝ) ^ (2 * δ) / 4
        = (c₁ * ((X : ℝ) ^ δ / 2)) ^ 2 := by
          have hrpow2 : ((X : ℝ) ^ δ) ^ 2 = (X : ℝ) ^ (2 * δ) := by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hX_pos.le]
            congr 1; push_cast; ring
          rw [mul_pow, div_pow, hrpow2]
          ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hprod_ge 2
  have hcontB : Continuous fun t : ℝ =>
      ∑ d ∈ Finset.Icc 1 X,
        shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    refine continuous_finsetSum _ fun d hd => ?_
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Finset.mem_Icc.mp hd).1.ne'
    exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hd0))
  have hcont_prod : ContinuousOn
      (fun t : ℝ => ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        ∑ d ∈ Finset.Icc 1 X,
          shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2)
      (Set.Icc 1 3) :=
    ((hcontF_on.mul hcontB.continuousOn).norm.pow 2)
  have h1_low : (1 : ℝ) ≤ 2 - η := by linarith
  have hlow_high : 2 - η ≤ 2 + η := by linarith
  have hhigh_3 : 2 + η ≤ (3 : ℝ) := by linarith
  have hint_1_low : IntervalIntegrable
      (fun t : ℝ => ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        ∑ d ∈ Finset.Icc 1 X,
          shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2)
      volume 1 (2 - η) :=
    (hcont_prod.mono (Set.Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc h1_low
  have hint_band : IntervalIntegrable
      (fun t : ℝ => ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        ∑ d ∈ Finset.Icc 1 X,
          shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2)
      volume (2 - η) (2 + η) :=
    (hcont_prod.mono (Set.Icc_subset_Icc h1_low hhigh_3)).intervalIntegrable_of_Icc hlow_high
  have hint_high_3 : IntervalIntegrable
      (fun t : ℝ => ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        ∑ d ∈ Finset.Icc 1 X,
          shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2)
      volume (2 + η) 3 :=
    (hcont_prod.mono (Set.Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc hhigh_3
  have hint_1_high : IntervalIntegrable
      (fun t : ℝ => ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        ∑ d ∈ Finset.Icc 1 X,
          shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2)
      volume 1 (2 + η) :=
    hint_1_low.trans hint_band
  have hboch_band : (c₁ ^ 2 * r / 2) * (X : ℝ) ^ (2 * δ) / Real.log (2 * X) ≤
      ∫ t in (2 - η)..(2 + η),
        ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          ∑ d ∈ Finset.Icc 1 X,
            shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
    have hmono := intervalIntegral.integral_mono_on hlow_high intervalIntegrable_const hint_band
      hpt_band
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    refine le_trans (le_of_eq ?_) hmono
    have hlen : (2 + η) - (2 - η) = 2 * η := by ring
    rw [hlen, hη_def]
    field_simp [hlog_pos.ne']
    ring
  have hboch_13 : (c₁ ^ 2 * r / 2) * (X : ℝ) ^ (2 * δ) / Real.log (2 * X) ≤
      ∫ t in (1 : ℝ)..3,
        ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          ∑ d ∈ Finset.Icc 1 X,
            shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
    have hadj1 := intervalIntegral.integral_add_adjacent_intervals hint_1_low hint_band
    have hadj2 := intervalIntegral.integral_add_adjacent_intervals hint_1_high hint_high_3
    have hnn1 : 0 ≤ ∫ t in (1 : ℝ)..(2 - η),
        ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          ∑ d ∈ Finset.Icc 1 X,
            shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 :=
      intervalIntegral.integral_nonneg h1_low fun _ _ => sq_nonneg _
    have hnn2 : 0 ≤ ∫ t in (2 + η)..(3 : ℝ),
        ‖shiftedInverseFn δ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          ∑ d ∈ Finset.Icc 1 X,
            shiftedZetaCoeff δ d * (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2 :=
      intervalIntegral.integral_nonneg hhigh_3 fun _ _ => sq_nonneg _
    linarith
  refine ⟨hboch_13, fun {T} hT => ?_⟩
  have hint_13 := hint_1_high.trans hint_high_3
  have hofReal := ENNReal.ofReal_le_ofReal hboch_13
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3),
    ofReal_integral_eq_lintegral_ofReal hint_13.1
      (Eventually.of_forall fun _ => sq_nonneg _)] at hofReal
  exact hofReal.trans (lintegral_mono_set (Set.Ioc_subset_Ioc_right hT))

end GaloisForLFunctions.ArithmeticProduction
