import GaloisForLFunctions.RHTower.DigammaLeLog
import GaloisForLFunctions.RHTower.XiHorizontalSlopeNearOne

/-!
# The `3-4-1` inequality for Dirichlet logarithmic derivatives

On `Re s > 1`, `−L'/L(s, ψ) = Σ ψ(n) Λ(n) n^{−s}` (`neg_logDeriv_LFunction_eq_LSeries`). For `n` prime to
the modulus put `z = χ(n) n^{−it}`, a unit; then `3 + 4 Re z + Re z² = 2(1 + Re z)² ≥ 0`, and for the
other `n` all three characters vanish. Hence:

* **`3-4-1`** (`three_four_one_logDeriv`). For `σ > 1`,
  `3 Re(−L₀'/L₀)(σ) + 4 Re(−L'/L)(σ + it, χ) + Re(−L'/L)(σ + 2it, χ²) ≥ 0`, with `L₀` the principal
  `L`-function of the modulus.
* **The principal character at real points** (`neg_re_logDeriv_trivChar_real_le`).
  `Re(−L₀'/L₀)(σ) ≤ 1/(σ − 1) − 1/5` for `1 < σ ≤ 2`: its coefficients are at most those of `−ζ'/ζ`.
* **The principal character off the real axis** (`neg_re_logDeriv_trivChar_le`).
  `Re(−L₀'/L₀)(s) ≤ Re(−ζ'/ζ)(s) + log q` for `Re s > 1`: the two series differ on the prime powers
  `p^k`, `p ∣ q`, whose total is at most `Σ_{p ∣ q} log p/(p^σ − 1) ≤ log q`
  (`tsum_vonMangoldt_not_coprime_le`).
-/

noncomputable section

open Complex ArithmeticFunction

namespace RHTower

variable {q : ℕ} [NeZero q]

/-- `−L'/L(s, ψ)` is the twisted von Mangoldt series on `Re s > 1`. -/
theorem neg_logDeriv_LFunction_eq_LSeries (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv ψ.LFunction s = LSeries (fun n => ψ n * ((Λ n : ℝ) : ℂ)) s := by
  rw [logDeriv_apply, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries ψ hs,
    DirichletCharacter.LFunction_eq_LSeries ψ hs, ← neg_div]
  exact (DirichletCharacter.LSeries_twist_vonMangoldt_eq ψ hs).symm

/-- `3a + 4 Re(az) + Re(az²) ≥ 0` for `a ≥ 0` and a unit `z`. -/
theorem three_four_one_unit {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * a + 4 * ((a : ℂ) * z).re + ((a : ℂ) * z ^ 2).re := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at h
    nlinarith
  simp only [re_ofReal_mul, sq, mul_re]
  nlinarith [mul_nonneg ha (sq_nonneg (z.re + 1))]

/-- The `n`-th term of the `3-4-1` combination is nonnegative. -/
theorem three_four_one_term (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (fun n => (1 : DirichletCharacter ℂ q) n * ((Λ n : ℝ) : ℂ)) σ n).re +
      4 * (LSeries.term (fun n => χ n * ((Λ n : ℝ) : ℂ)) (σ + t * I) n).re +
      (LSeries.term (fun n => (χ ^ 2) n * ((Λ n : ℝ) : ℂ)) (σ + 2 * t * I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne',
    LSeries.term_of_ne_zero hn.ne']
  by_cases hu : IsUnit (n : ZMod q)
  · -- `n` prime to the modulus: the unit `z = χ(n) n^{−it}`.
    set u : ℂ := (n : ℂ) ^ ((t : ℂ) * I) with hudef
    have hunorm : ‖u‖ = 1 := by
      rw [hudef, Complex.norm_natCast_cpow_of_pos hn]
      simp
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hunorm
      exact zero_ne_one hunorm
    have hχn : ‖χ n‖ = 1 := by
      have h := χ.unit_norm_eq_one hu.unit
      rwa [IsUnit.unit_spec] at h
    set z : ℂ := χ n / u with hzdef
    have hz : ‖z‖ = 1 := by rw [hzdef, norm_div, hχn, hunorm, div_one]
    set a : ℝ := Λ n / (n : ℝ) ^ σ with hadef
    have hpos : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by exact_mod_cast hn) σ
    have ha : 0 ≤ a := div_nonneg vonMangoldt_nonneg hpos.le
    have hnσ : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      rfl
    have hσne : (((n : ℝ) ^ σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have e1 : (1 : DirichletCharacter ℂ q) n * ((Λ n : ℝ) : ℂ) / (n : ℂ) ^ (σ : ℂ) = (a : ℂ) := by
      rw [MulChar.one_apply hu, one_mul, hnσ, hadef, Complex.ofReal_div]
    have e2 : χ n * ((Λ n : ℝ) : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * I) = (a : ℂ) * z := by
      rw [Complex.cpow_add _ _ hn0, hnσ, ← hudef, hzdef, hadef, Complex.ofReal_div]
      field_simp
    have e3 : (χ ^ 2) n * ((Λ n : ℝ) : ℂ) / (n : ℂ) ^ ((σ : ℂ) + 2 * t * I) =
        (a : ℂ) * z ^ 2 := by
      rw [MulChar.pow_apply' _ two_ne_zero,
        show (σ : ℂ) + 2 * t * I = σ + ((2 : ℕ) : ℂ) * (t * I) by push_cast; ring,
        Complex.cpow_add _ _ hn0, Complex.cpow_nat_mul, hnσ, ← hudef, hzdef, hadef,
        Complex.ofReal_div]
      field_simp
    rw [e1, e2, e3, Complex.ofReal_re]
    exact three_four_one_unit ha hz
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    simp

/-- **The `3-4-1` inequality for logarithmic derivatives.** -/
theorem three_four_one_logDeriv (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-logDeriv (1 : DirichletCharacter ℂ q).LFunction σ).re +
      4 * (-logDeriv χ.LFunction (σ + t * I)).re +
      (-logDeriv (χ ^ 2).LFunction (σ + 2 * t * I)).re := by
  have h0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have h1 : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h2 : 1 < ((σ : ℂ) + 2 * t * I).re := by simpa using hσ
  rw [neg_logDeriv_LFunction_eq_LSeries _ h0, neg_logDeriv_LFunction_eq_LSeries _ h1,
    neg_logDeriv_LFunction_eq_LSeries _ h2]
  have hs0 := hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ q) h0).LSeriesHasSum
  have hs1 := hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h1).LSeriesHasSum
  have hs2 := hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2) h2).LSeriesHasSum
  exact (((hs0.mul_left 3).add (hs1.mul_left 4)).add hs2).nonneg fun n =>
    three_four_one_term χ σ t n

/-! ### The principal character -/

/-- A term of the principal series is at most the corresponding term of `−ζ'/ζ`, and equal to it on
integers prime to the modulus. -/
theorem re_term_trivChar_sub_le (s : ℂ) (n : ℕ) :
    (LSeries.term (fun n => (1 : DirichletCharacter ℂ q) n * ((Λ n : ℝ) : ℂ)) s n).re ≤
      (LSeries.term (fun n => ((Λ n : ℝ) : ℂ)) s n).re +
        (if IsUnit (n : ZMod q) then 0 else Λ n / (n : ℝ) ^ s.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu, one_mul, if_pos hu, add_zero]
  · rw [MulChar.map_nonunit _ hu, zero_mul, zero_div, Complex.zero_re, if_neg hu]
    have hre : (((Λ n : ℝ) : ℂ) / (n : ℂ) ^ s).re ≥ -(Λ n / (n : ℝ) ^ s.re) := by
      have h := Complex.abs_re_le_norm (((Λ n : ℝ) : ℂ) / (n : ℂ) ^ s)
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
        Complex.norm_natCast_cpow_of_pos hn] at h
      linarith [neg_abs_le (((Λ n : ℝ) : ℂ) / (n : ℂ) ^ s).re]
    linarith

/-- The prime powers `p^k`, `k ≥ 1`, of one prime `p ∣ q`, weighted by `log p · n^{−σ}`. -/
def primePowerWeight (σ : ℝ) (p : ℕ) (n : ℕ) : ℝ :=
  Set.indicator (Set.range fun k : ℕ => p ^ (k + 1)) (fun n => Real.log p / (n : ℝ) ^ σ) n

theorem primePowerWeight_nonneg {σ : ℝ} {p : ℕ} (hp : p.Prime) (n : ℕ) :
    0 ≤ primePowerWeight σ p n := by
  unfold primePowerWeight
  refine Set.indicator_nonneg (fun n _ => ?_) n
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) (Real.rpow_nonneg (by positivity) _)

/-- The weights of one prime sum to `log p · p^{−σ}/(1 − p^{−σ}) ≤ log p`. -/
theorem hasSum_primePowerWeight {σ : ℝ} (hσ : 1 ≤ σ) {p : ℕ} (hp : p.Prime) :
    Summable (primePowerWeight σ p) ∧ ∑' n, primePowerWeight σ p n ≤ Real.log p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hinj : Function.Injective fun k : ℕ => p ^ (k + 1) := fun a b h =>
    by simpa using Nat.pow_right_injective hp.two_le h
  have hsupp : ∀ n ∉ Set.range (fun k : ℕ => p ^ (k + 1)), primePowerWeight σ p n = 0 :=
    fun n hn => Set.indicator_of_notMem hn _
  set r : ℝ := ((p : ℝ) ^ σ)⁻¹ with hr
  have hpσ : (2 : ℝ) ≤ (p : ℝ) ^ σ :=
    hp2.trans (by simpa using Real.rpow_le_rpow_of_exponent_le (by linarith) hσ)
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 / 2 := by rw [hr]; exact (inv_le_inv₀ (by linarith) (by norm_num)).mpr hpσ |>.trans (by norm_num)
  -- On the prime powers the weight is a geometric sequence.
  have hcomp : (primePowerWeight σ p ∘ fun k : ℕ => p ^ (k + 1)) =
      fun k => Real.log p * r * r ^ k := by
    funext k
    simp only [Function.comp_apply, primePowerWeight]
    rw [Set.indicator_of_mem (Set.mem_range_self k)]
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm, Real.rpow_mul (by positivity),
      Real.rpow_natCast, hr, ← inv_pow, pow_succ]
    ring
  have hgeo : Summable fun k : ℕ => Real.log p * r * r ^ k :=
    (summable_geometric_of_lt_one hr0 (by linarith)).mul_left _
  have hsum : Summable (primePowerWeight σ p) := by
    rw [← hinj.summable_iff hsupp, hcomp]
    exact hgeo
  refine ⟨hsum, ?_⟩
  rw [← hinj.tsum_eq (fun n hn => by
    by_contra h
    exact hn (Function.mem_support.mpr h |> fun _ => by
      by_contra hn'
      exact (Function.mem_support.mp hn) (hsupp n hn'))), hcomp, tsum_mul_left,
    tsum_geometric_of_lt_one hr0 (by linarith)]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have h2 : r * (1 - r)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ (by linarith)]
    linarith
  calc Real.log p * r * (1 - r)⁻¹ = Real.log p * (r * (1 - r)⁻¹) := by ring
    _ ≤ Real.log p * 1 := mul_le_mul_of_nonneg_left h2 hlog
    _ = Real.log p := mul_one _

/-- **The prime powers dividing the modulus.** `Σ_{(n, q) > 1} Λ(n) n^{−σ} ≤ log q` for `σ ≥ 1`. -/
theorem tsum_vonMangoldt_not_coprime_le {σ : ℝ} (hσ : 1 ≤ σ) :
    Summable (fun n : ℕ => if IsUnit (n : ZMod q) then 0 else Λ n / (n : ℝ) ^ σ) ∧
      ∑' n : ℕ, (if IsUnit (n : ZMod q) then 0 else Λ n / (n : ℝ) ^ σ) ≤ Real.log q := by
  have hprime : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hsums := fun p (hp : p ∈ q.primeFactors) => hasSum_primePowerWeight hσ (hprime p hp)
  -- Pointwise domination by the prime-power weights of the primes of `q`.
  have hdom : ∀ n : ℕ, (if IsUnit (n : ZMod q) then 0 else Λ n / (n : ℝ) ^ σ) ≤
      ∑ p ∈ q.primeFactors, primePowerWeight σ p n := by
    intro n
    have hnonneg : 0 ≤ ∑ p ∈ q.primeFactors, primePowerWeight σ p n :=
      Finset.sum_nonneg fun p hp => primePowerWeight_nonneg (hprime p hp) n
    split_ifs with hu
    · exact hnonneg
    by_cases hΛ : Λ n = 0
    · rw [hΛ, zero_div]; exact hnonneg
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hpq : p ∈ q.primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp, ?_, NeZero.ne q⟩
      by_contra hnd
      have hcop : Nat.Coprime (p ^ k) q := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).pow_left k
      exact hu ((ZMod.isUnit_iff_coprime _ q).mpr hcop)
    have hval : Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) ^ σ = primePowerWeight σ p (p ^ k) := by
      unfold primePowerWeight
      rw [Set.indicator_of_mem ⟨k - 1, by rw [Nat.sub_add_cancel hk]⟩,
        vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
    rw [hval]
    exact Finset.single_le_sum (fun p' hp' => primePowerWeight_nonneg (hprime p' hp') (p ^ k)) hpq
  have hsumdom : Summable fun n : ℕ => ∑ p ∈ q.primeFactors, primePowerWeight σ p n :=
    summable_sum fun p hp => (hsums p hp).1
  have hsummable : Summable (fun n : ℕ => if IsUnit (n : ZMod q) then 0 else Λ n / (n : ℝ) ^ σ) :=
    Summable.of_nonneg_of_le (fun n => by
      split_ifs
      · exact le_rfl
      · exact div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hdom hsumdom
  refine ⟨hsummable, ?_⟩
  calc ∑' n : ℕ, (if IsUnit (n : ZMod q) then 0 else Λ n / (n : ℝ) ^ σ)
      ≤ ∑' n : ℕ, ∑ p ∈ q.primeFactors, primePowerWeight σ p n :=
        hsummable.tsum_le_tsum hdom hsumdom
    _ = ∑ p ∈ q.primeFactors, ∑' n : ℕ, primePowerWeight σ p n :=
        Summable.tsum_finsetSum fun p hp => (hsums p hp).1
    _ ≤ ∑ p ∈ q.primeFactors, Real.log p := Finset.sum_le_sum fun p hp => (hsums p hp).2
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [Real.log_prod fun p hp => by exact_mod_cast (hprime p hp).ne_zero]
    _ ≤ Real.log q := by
        refine Real.log_le_log (Finset.prod_pos fun p hp => by exact_mod_cast (hprime p hp).pos) ?_
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.prod_primeFactors_dvd q)

/-- **The principal character off the real axis.** `Re(−L₀'/L₀)(s) ≤ Re(−ζ'/ζ)(s) + log q`. -/
theorem neg_re_logDeriv_trivChar_le {s : ℂ} (hs : 1 < s.re) :
    (-logDeriv (1 : DirichletCharacter ℂ q).LFunction s).re ≤
      (-deriv riemannZeta s / riemannZeta s).re + Real.log q := by
  rw [neg_logDeriv_LFunction_eq_LSeries _ hs,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  have h0 := hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ q) hs).LSeriesHasSum
  have hΛ := hasSum_re (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  obtain ⟨hsumq, hq⟩ := tsum_vonMangoldt_not_coprime_le (q := q) hs.le
  have hle := hasSum_le (fun n => re_term_trivChar_sub_le s n) h0 (hΛ.add hsumq.hasSum)
  linarith

/-- **The principal character at real points.** `Re(−L₀'/L₀)(σ) ≤ 1/(σ − 1) − 1/5` for `1 < σ ≤ 2`. -/
theorem neg_re_logDeriv_trivChar_real_le {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) :
    (-logDeriv (1 : DirichletCharacter ℂ q).LFunction σ).re ≤ 1 / (σ - 1) - 1 / 5 := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ1
  rw [neg_logDeriv_LFunction_eq_LSeries _ hs]
  have h0 := hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ q) hs).LSeriesHasSum
  have hΛ := hasSum_re (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  -- Termwise the principal coefficients are at most `Λ`.
  have hterm : ∀ n : ℕ,
      (LSeries.term (fun n => (1 : DirichletCharacter ℂ q) n * ((Λ n : ℝ) : ℂ)) σ n).re ≤
        (LSeries.term (fun n => ((Λ n : ℝ) : ℂ)) σ n).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
    have hnσ : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      rfl
    by_cases hu : IsUnit (n : ZMod q)
    · rw [MulChar.one_apply hu, one_mul]
    · rw [MulChar.map_nonunit _ hu, zero_mul, zero_div, hnσ, ← Complex.ofReal_div,
        Complex.ofReal_re, Complex.zero_re]
      exact div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hle := hasSum_le hterm h0 hΛ
  have hz := neg_re_logDeriv_riemannZeta_real_le_neg hσ1 hσ2
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hz
  linarith

end RHTower
