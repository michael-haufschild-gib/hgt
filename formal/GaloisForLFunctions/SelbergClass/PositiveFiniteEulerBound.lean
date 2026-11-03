import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerCoefficients
import GaloisForLFunctions.HTGeometry.CanonicalEulerLog
import GaloisForLFunctions.RHTower.SelbergClass.Full
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The strict Euler bound excludes reciprocal finite factors

The logarithmic coefficient at `pᵏ` is `(1-αᵏ-βᵏ)/k`, where
`αβ=p` and `α+β=-A`. The doubled power-sum identity forces exponential
rate at least `p^(1/2)`, excluding every full Selberg Euler exponent.
-/

noncomputable section
open Complex Filter Topology Set
namespace GaloisForLFunctions.SelbergClass.PositiveFiniteEuler

/-- The logarithm of a local factor `1-αp⁻ˢ`, supported on powers of `p`. -/
def powerLogCoeff (p : ℕ) (α : ℂ) : ℕ → ℂ :=
  Function.extend (fun k : ℕ => p ^ k) (fun k => -(α ^ k) / (k : ℂ)) 0

private theorem pow_injective {p : ℕ} (hp : 1 < p) :
    Function.Injective (fun k : ℕ => p ^ k) :=
  (pow_right_strictMono₀ hp).injective

theorem powerLogCoeff_pow {p : ℕ} (hp : 1 < p) (α : ℂ) (k : ℕ) :
    powerLogCoeff p α (p ^ k) = -(α ^ k) / (k : ℂ) :=
  (pow_injective hp).extend_apply _ _ k

@[simp] theorem powerLogCoeff_zero {p : ℕ} (hp : p ≠ 0) (α : ℂ) :
    powerLogCoeff p α 0 = 0 := by
  apply Function.extend_apply'
  rintro ⟨k, hk⟩
  exact pow_ne_zero k hp hk

@[simp] theorem powerLogCoeff_one {p : ℕ} (hp : 1 < p) (α : ℂ) :
    powerLogCoeff p α 1 = 0 := by
  simpa only [pow_zero, Nat.cast_zero, div_zero] using powerLogCoeff_pow hp α 0

private theorem powerLogCoeff_term {p : ℕ} (hp : 1 < p) (α s : ℂ) :
    LSeries.term (powerLogCoeff p α) s =
      Function.extend (fun k : ℕ => p ^ k)
        (fun k => -((α * (p : ℂ) ^ (-s)) ^ k) / (k : ℂ)) 0 := by
  have hp0 : p ≠ 0 := by omega
  funext n
  by_cases hn : ∃ k : ℕ, p ^ k = n
  · obtain ⟨k, rfl⟩ := hn
    rw [LSeries.term_of_ne_zero (pow_ne_zero k hp0), powerLogCoeff_pow hp,
      (pow_injective hp).extend_apply]
    have hpow : ((p ^ k : ℕ) : ℂ) ^ s = ((p : ℂ) ^ s) ^ k := by
      induction k with
      | zero => simp only [pow_zero, Nat.cast_one, one_cpow]
      | succ k ih =>
        calc ((p ^ (k + 1) : ℕ) : ℂ) ^ s =
            ((p ^ k : ℕ) : ℂ) ^ s * (p : ℂ) ^ s := by
              rw [pow_succ, Nat.cast_mul]
              exact Complex.natCast_mul_natCast_cpow _ _ _
          _ = ((p : ℂ) ^ s) ^ (k + 1) := by rw [ih, pow_succ]
    rw [hpow, mul_pow, Complex.cpow_neg, inv_pow]
    ring
  · rw [Function.extend_apply' _ _ n hn]
    by_cases hn0 : n = 0
    · subst n
      exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero hn0]
      change Function.extend _ _ _ n / _ = 0
      rw [Function.extend_apply' _ _ n hn]
      simp only [Pi.zero_apply, zero_div]

/-- The sparse natural-number series is the Taylor logarithm of its local factor. -/
theorem hasSum_powerLogCoeff {p : ℕ} (hp : 1 < p) (α : ℂ) {s : ℂ}
    (hs : ‖α * (p : ℂ) ^ (-s)‖ < 1) :
    LSeriesHasSum (powerLogCoeff p α) s (Complex.log (1 - α * (p : ℂ) ^ (-s))) := by
  rw [LSeriesHasSum, powerLogCoeff_term hp]
  apply (hasSum_extend_zero (pow_injective hp)).mpr
  have h := (Complex.hasSum_taylorSeries_neg_log hs).neg
  simpa only [neg_neg, neg_div] using h

/-- The canonical zeta logarithm plus the two local quadratic logarithms. -/
def eulerLogCoeff (p : ℕ) (α β : ℂ) : ℕ → ℂ :=
  RHTower.eulerLogDirichletCoeff + powerLogCoeff p α + powerLogCoeff p β

theorem eulerLogCoeff_prime_pow {p : ℕ} (hp : p.Prime) (α β : ℂ) {k : ℕ} (hk : k ≠ 0) :
    eulerLogCoeff p α β (p ^ k) = (1 - α ^ k - β ^ k) / (k : ℂ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp only [eulerLogCoeff, Pi.add_apply, powerLogCoeff_pow hp.one_lt,
    RHTower.eulerLogDirichletCoeff_prime_pow_succ _ _ hp, Nat.cast_succ]
  ring

theorem hasSum_eulerLogCoeff {p : ℕ} (hp : p.Prime) (α β : ℂ) {s : ℂ}
    (hs : 1 < s.re) (hα : ‖α * (p : ℂ) ^ (-s)‖ < 1)
    (hβ : ‖β * (p : ℂ) ^ (-s)‖ < 1) :
    LSeriesHasSum (eulerLogCoeff p α β) s
      (RHTower.canonicalEulerLogZeta s + Complex.log (1 - α * (p : ℂ) ^ (-s)) +
        Complex.log (1 - β * (p : ℂ) ^ (-s))) :=
  LSeriesHasSum.add
    (LSeriesHasSum.add (RHTower.canonicalEulerLogZeta_summable hs).LSeriesHasSum
      (hasSum_powerLogCoeff hp.one_lt α hα))
    (hasSum_powerLogCoeff hp.one_lt β hβ)

/-- The local root decomposition gives the actual Euler logarithm on its half-plane. -/
theorem exp_lSeries_eulerLogCoeff {p : ℕ} (hp : p.Prime) {A : ℝ} {α β : ℂ}
    (hadd : α + β = -(A : ℂ)) (hmul : α * β = p) {s : ℂ}
    (hs : 1 < s.re) (hα : ‖α * (p : ℂ) ^ (-s)‖ < 1)
    (hβ : ‖β * (p : ℂ) ^ (-s)‖ < 1) :
    Complex.exp (LSeries (eulerLogCoeff p α β) s) = localFactor p A s * riemannZeta s := by
  have hα0 : 1 - α * (p : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have h1 := sub_eq_zero.mp h
    rw [← h1, norm_one] at hα
    exact lt_irrefl _ hα
  have hβ0 : 1 - β * (p : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have h1 := sub_eq_zero.mp h
    rw [← h1, norm_one] at hβ
    exact lt_irrefl _ hβ
  rw [(hasSum_eulerLogCoeff hp α β hs hα hβ).LSeries_eq,
    Complex.exp_add, Complex.exp_add, Complex.exp_log hα0, Complex.exp_log hβ0,
    RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta hs]
  have hfactor : (1 - α * (p : ℂ) ^ (-s)) * (1 - β * (p : ℂ) ^ (-s)) =
      localFactor p A s := by
    calc _ = 1 - (α + β) * (p : ℂ) ^ (-s) +
        (α * β) * ((p : ℂ) ^ (-s)) ^ 2 := by ring
      _ = localFactor p A s := by rw [hadd, hmul, localFactor]; ring
  rw [mul_assoc, hfactor, mul_comm]

private theorem exists_log_halfplane {p : ℕ} (hp : 1 < p) (α β : ℂ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℂ, B < s.re →
      ‖α * (p : ℂ) ^ (-s)‖ < 1 ∧ ‖β * (p : ℂ) ^ (-s)‖ < 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hl : 0 < Real.log p := Real.log_pos hpR
  have hbase : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have ht : Tendsto (fun x : ℝ => max ‖α‖ ‖β‖ * Real.exp (-(Real.log p * x)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply, id_eq] using
      (hbase.comp (Filter.Tendsto.const_mul_atTop hl tendsto_id)).const_mul (max ‖α‖ ‖β‖)
  obtain ⟨B, hB⟩ := eventually_atTop.mp (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  refine ⟨max B 1, le_max_right _ _, fun s hs => ?_⟩
  have hsmall := hB s.re ((le_max_left B 1).trans hs.le)
  have heq (z : ℂ) : ‖z * (p : ℂ) ^ (-s)‖ = ‖z‖ * Real.exp (-(Real.log p * s.re)) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re,
      Real.rpow_def_of_pos (by positivity)]
    congr 2
    ring
  rw [heq, heq]
  exact ⟨(mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le).trans_lt hsmall,
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le).trans_lt hsmall⟩

/-- Equality after exponentiation determines all nonconstant Dirichlet coefficients.
Differentiation removes the additive logarithm branch. -/
private theorem coeff_eq_of_exp_lSeries_eq {f g : ℕ → ℂ} {B : ℝ}
    (hf : ∀ s : ℂ, B < s.re → LSeriesSummable f s)
    (hg : ∀ s : ℂ, B < s.re → LSeriesSummable g s)
    (he : ∀ s : ℂ, B < s.re → Complex.exp (LSeries f s) = Complex.exp (LSeries g s))
    {n : ℕ} (hn : 1 < n) : f n = g n := by
  have hfa : LSeries.abscissaOfAbsConv f ≤ (B + 1 : ℝ) := by
    simpa only [Complex.ofReal_re] using
      (hf ((B + 1 : ℝ) : ℂ) (by simp only [Complex.ofReal_re]; linarith)).abscissaOfAbsConv_le
  have hga : LSeries.abscissaOfAbsConv g ≤ (B + 1 : ℝ) := by
    simpa only [Complex.ofReal_re] using
      (hg ((B + 1 : ℝ) : ℂ) (by simp only [Complex.ofReal_re]; linarith)).abscissaOfAbsConv_le
  have hfbs {s : ℂ} (hs : B + 1 < s.re) : LSeries.abscissaOfAbsConv f < s.re :=
    hfa.trans_lt (by exact_mod_cast hs)
  have hgbs {s : ℂ} (hs : B + 1 < s.re) : LSeries.abscissaOfAbsConv g < s.re :=
    hga.trans_lt (by exact_mod_cast hs)
  have hderiv {s : ℂ} (hs : B + 1 < s.re) :
      LSeries (LSeries.logMul f) s = LSeries (LSeries.logMul g) s := by
    have hdf := (LSeries_hasDerivAt (hfbs hs)).cexp
    have hdg := (LSeries_hasDerivAt (hgbs hs)).cexp
    have hloc : (fun z : ℂ => Complex.exp (LSeries f z)) =ᶠ[𝓝 s]
        (fun z : ℂ => Complex.exp (LSeries g z)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (by linarith : B < s.re)] with z hz
      exact he z hz
    have h := (hdf.congr_of_eventuallyEq hloc.symm).deriv.symm.trans hdg.deriv
    rw [he s (by linarith)] at h
    have hcancel := mul_left_cancel₀ (Complex.exp_ne_zero (LSeries g s)) h
    exact neg_injective hcancel
  have hlogf := LSeriesSummable_logMul_of_lt_re (hfbs (s := (B + 2 : ℝ)) (by simp))
  have hlogg := LSeriesSummable_logMul_of_lt_re (hgbs (s := (B + 2 : ℝ)) (by simp))
  have hc : LSeries.logMul f n = LSeries.logMul g n := by
    apply LSeries.eq_of_LSeries_eventually_eq
      (hlogf.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _))
      (hlogg.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _))
    · filter_upwards [eventually_gt_atTop (B + 1)] with x hx
      exact hderiv (s := (x : ℂ)) hx
    · omega
  change Complex.log (n : ℂ) * f n = Complex.log (n : ℂ) * g n at hc
  apply mul_left_cancel₀ _ hc
  rw [← Complex.natCast_log]
  exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hn)).ne'

/-- Any purported full Selberg carrier is forced to have the explicit quadratic Euler logarithm. -/
theorem fullClass_eulerLogCoeff_prime_pow {p : ℕ} (hp : p.Prime) {A : ℝ} {α β : ℂ}
    (hadd : α + β = -(A : ℂ)) (hmul : α * β = p)
    (F : RHTower.SelbergClass) (hcoeff : F.coeff = arithmeticCoeffs p A)
    {k : ℕ} (hk : k ≠ 0) :
    F.eulerLogCoeff (p ^ k) = (1 - α ^ k - β ^ k) / (k : ℂ) := by
  obtain ⟨B, hB, hhalf⟩ := exists_log_halfplane hp.one_lt α β
  have hsame : F.eulerLogCoeff (p ^ k) = eulerLogCoeff p α β (p ^ k) := by
    apply coeff_eq_of_exp_lSeries_eq (B := B)
    · exact fun s hs => F.eulerLogSummable s (hB.trans_lt hs)
    · exact fun s hs => (hasSum_eulerLogCoeff hp α β (hB.trans_lt hs)
        (hhalf s hs).1 (hhalf s hs).2).LSeriesSummable
    · intro s hs
      rw [F.eulerProduct s (hB.trans_lt hs), ← F.lSeries_eq_value s (hB.trans_lt hs), hcoeff,
        (lSeriesHasSum hp A (hB.trans_lt hs)).LSeries_eq,
        exp_lSeries_eulerLogCoeff hp hadd hmul (hB.trans_lt hs) (hhalf s hs).1 (hhalf s hs).2]
    · exact one_lt_pow₀ hp.one_lt hk
  rw [hsame, eulerLogCoeff_prime_pow hp α β hk]

private theorem quadratic_roots (p : ℕ) (A : ℝ) :
    ∃ α β : ℂ, α + β = -(A : ℂ) ∧ α * β = p := by
  let d : ℂ := ((A : ℂ) ^ 2 - 4 * p) ^ (2⁻¹ : ℂ)
  have hd : d ^ 2 = (A : ℂ) ^ 2 - 4 * p := Complex.cpow_nat_inv_pow _ (by norm_num)
  refine ⟨(-(A : ℂ) + d) / 2, (-(A : ℂ) - d) / 2, by ring, ?_⟩
  calc (-(A : ℂ) + d) / 2 * ((-(A : ℂ) - d) / 2) = ((A : ℂ) ^ 2 - d ^ 2) / 4 := by ring
    _ = p := by rw [hd]; ring

/-- Reciprocal roots cannot have logarithmic coefficients growing with exponent below one half. -/
theorem not_strictEulerBound {p : ℕ} (hp : 1 < p) {α β : ℂ} (hmul : α * β = p)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k ≠ 0 →
      ‖(1 - α ^ k - β ^ k) / (k : ℂ)‖ ≤ C * ((p ^ k : ℕ) : ℝ) ^ θ := by
  rintro ⟨C, hC, hb⟩
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  let R : ℝ := Real.sqrt p
  have hR0 : 0 < R := Real.sqrt_pos.mpr hp0
  have hRsq : R ^ 2 = (p : ℝ) := Real.sq_sqrt hp0.le
  have hR1 : 1 < R := by nlinarith only [hRsq, hR0, hpR]
  let q : ℝ := (p : ℝ) ^ θ / R
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    apply (div_lt_one hR0).mpr
    change (p : ℝ) ^ θ < Real.sqrt p
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_lt_rpow_of_exponent_lt hpR hθ
  have hpow (k : ℕ) : ((p ^ k : ℕ) : ℝ) ^ θ = ((p : ℝ) ^ θ) ^ k := by
    rw [Nat.cast_pow, Real.rpow_def_of_pos (pow_pos hp0 k), Real.log_pow,
      Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul]
    congr 1
    ring
  let a : ℂ := α / (R : ℂ)
  let b : ℂ := β / (R : ℂ)
  let u : ℕ → ℂ := fun k => a ^ k + b ^ k
  have hab : a * b = 1 := by
    have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR0.ne'
    have hsC : (R : ℂ) ^ 2 = (p : ℂ) := by exact_mod_cast hRsq
    dsimp only [a, b]
    rw [div_mul_div_comm, ← pow_two, hmul, ← hsC, div_self (pow_ne_zero 2 hRC)]
  have hmajor : ∀ᶠ k : ℕ in atTop,
      ‖u k‖ ≤ R⁻¹ ^ k + C * ((k : ℝ) * q ^ k) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : k ≠ 0 := by omega
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
    have hid : α ^ k + β ^ k = 1 - (k : ℂ) * ((1 - α ^ k - β ^ k) / (k : ℂ)) := by
      field_simp [hkC]
      ring
    have hn : ‖α ^ k + β ^ k‖ ≤ 1 + (k : ℝ) * (C * ((p : ℝ) ^ θ) ^ k) := by
      rw [hid]
      calc ‖1 - (k : ℂ) * ((1 - α ^ k - β ^ k) / (k : ℂ))‖ ≤
          ‖(1 : ℂ)‖ + ‖(k : ℂ) * ((1 - α ^ k - β ^ k) / (k : ℂ))‖ := norm_sub_le _ _
        _ = 1 + (k : ℝ) * ‖(1 - α ^ k - β ^ k) / (k : ℂ)‖ := by
          rw [norm_one, norm_mul, Complex.norm_natCast]
        _ ≤ 1 + (k : ℝ) * (C * ((p : ℝ) ^ θ) ^ k) := by
          gcongr
          exact (hb k hk0).trans_eq (by rw [hpow])
    have hnorm : ‖u k‖ = ‖α ^ k + β ^ k‖ / R ^ k := by
      dsimp only [u, a, b]
      rw [div_pow, div_pow, ← add_div, norm_div, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0.le]
    rw [hnorm]
    calc ‖α ^ k + β ^ k‖ / R ^ k ≤
        (1 + (k : ℝ) * (C * ((p : ℝ) ^ θ) ^ k)) / R ^ k :=
          div_le_div_of_nonneg_right hn (pow_nonneg hR0.le k)
      _ = R⁻¹ ^ k + C * ((k : ℝ) * q ^ k) := by
        rw [inv_pow, show q ^ k = ((p : ℝ) ^ θ) ^ k / R ^ k by exact div_pow _ _ _]
        ring
  have hgeom : Tendsto (fun k : ℕ => R⁻¹ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hR0.le) ((inv_lt_one₀ hR0).mpr hR1)
  have hlin : Tendsto (fun k : ℕ => (k : ℝ) * q ^ k) atTop (𝓝 0) := by
    have hsum := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
    simpa only [pow_one] using hsum.tendsto_atTop_zero
  have hupper : Tendsto (fun k : ℕ => R⁻¹ ^ k + C * ((k : ℝ) * q ^ k)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hgeom.add (hlin.const_mul C)
  have hu : Tendsto u atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Filter.Eventually.of_forall fun k => norm_nonneg (u k)) hmajor hupper
  have hdouble (k : ℕ) : u (2 * k) = u k ^ 2 - 2 := by
    have hprod : a ^ k * b ^ k = 1 := by rw [← mul_pow, hab, one_pow]
    dsimp only [u]
    rw [show 2 * k = k * 2 by omega, pow_mul, pow_mul]
    calc (a ^ k) ^ 2 + (b ^ k) ^ 2 =
        (a ^ k + b ^ k) ^ 2 - 2 * (a ^ k * b ^ k) := by ring
      _ = (a ^ k + b ^ k) ^ 2 - 2 := by rw [hprod]; ring
  have htwo : Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    exact eventually_atTop.mpr ⟨n, fun k hk => by omega⟩
  have hzero : Tendsto (fun k : ℕ => u (2 * k)) atTop (𝓝 0) := hu.comp htwo
  have hneg : Tendsto (fun k : ℕ => u (2 * k)) atTop (𝓝 (-2 : ℂ)) := by
    have h := (hu.pow 2).sub_const 2
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub, ← hdouble] using h
  have hbad := tendsto_nhds_unique hzero hneg
  norm_num at hbad

/-- No reciprocal quadratic finite-factor modification belongs to the full Selberg class. -/
theorem not_fullClass {p : ℕ} (hp : p.Prime) (A : ℝ) :
    ¬ ∃ F : RHTower.SelbergClass, F.coeff = arithmeticCoeffs p A := by
  rintro ⟨F, hF⟩
  obtain ⟨α, β, hadd, hmul⟩ := quadratic_roots p A
  obtain ⟨C, hC, hb⟩ := F.eulerLogBound
  apply not_strictEulerBound hp.one_lt hmul F.eulerTheta_lt_half
  refine ⟨C, hC, fun k hk => ?_⟩
  rw [← fullClass_eulerLogCoeff_prime_pow hp hadd hmul F hF hk]
  exact hb (p ^ k) (pow_ne_zero k hp.ne_zero)

end GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
