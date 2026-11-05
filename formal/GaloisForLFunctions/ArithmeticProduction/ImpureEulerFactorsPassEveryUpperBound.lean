import GaloisForLFunctions.ArithmeticProduction.TypeIInformationIsParityBlind
import GaloisForLFunctions.RHTower.ChebyshevSchmidtOmega
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Impure Euler factors pass every upper bound

Replace `ζ` by `F(s) = ζ(s)(1 − c p^{−s})` with `c > √p`.  The new factor has modulus between `c p^{−σ} − 1` and `1 + c p^{−σ}` on `Re s = σ`, so it changes no
mean-value upper bound by more than a constant.  The mimic has the following properties, all proved below.

* **Integer count at bounded precision** (`abs_sum_impureCoeff_sub_le`): its coefficients `1 − c 1_{p∣n}` sum to `(1 − c/p)N + O(c)`.
* **Failed prime count** (`not_count_impureWeight`): its logarithmic-derivative coefficients `Λ(n) − c^k log p 1_{n = p^k}` violate the count, because a one-signed drift of size
  `x^{log c/log p}` with exponent above `½` is excluded by the oscillation of `ψ(x) − x`.
* **All upper bounds survive** (`norm_impureFactor_le`, `integral_norm_sq_mimic_le`).
* **A lattice of zeros at fixed depth** (`impureFactor_eq_zero`, `exists_lattice_zero_near`): every interval of length `2π/log p` contains the ordinate of a zero of depth
  `log c/log p − ½`, so window occupancy fails.
* **Positive log-mean** (`tendsto_logMean_impureFactor`): the mean of `log|1 − c p^{−½−it}|` tends to `log(c/√p) > 0`.

Consequently (`not_of_stable_under_impureWeight`) a statement stable under this deformation cannot imply the count.  So no statement that sees only upper bounds for `ζ` on lines
`Re s ≥ ½` can decide RH, however sharp its constants: a deciding input must be **locally pure**, that is, it must see the size of the Euler factor at every single prime.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.ArithmeticProduction

open ArithmeticOfSquareRootPrecision

/-- The impure Euler factor `1 − c p^{−s}`. -/
def impureFactor (p : ℕ) (c : ℝ) (s : ℂ) : ℂ := 1 - (c : ℂ) * (p : ℂ) ^ (-s)

/-- The coefficients of `ζ(s)(1 − c p^{−s})`. -/
def impureCoeff (p : ℕ) (c : ℝ) (n : ℕ) : ℝ := 1 - if p ∣ n then c else 0

/-- The change in the prime weight: `c^k log p` at `p^k`, `k ≥ 1`. -/
def impureDelta (p : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  if IsTowerPower p n then Real.log p * c ^ Nat.log p n else 0

/-- The prime weight of `ζ(s)(1 − c p^{−s})`. -/
def impureWeight (p : ℕ) (c : ℝ) : ℕ → ℝ := vonMangoldtWeight - impureDelta p c

/-- **The integers of the mimic are counted at bounded precision.** -/
theorem abs_sum_impureCoeff_sub_le {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    |∑ n ∈ Finset.Icc 1 N, impureCoeff p c n - (1 - c / p) * N| ≤ c := by
  have hsum : ∑ n ∈ Finset.Icc 1 N, impureCoeff p c n = N - c * ((N / p : ℕ) : ℝ) := by
    unfold impureCoeff
    rw [Finset.sum_sub_distrib]
    have h1 := sum_Icc_ite_dvd hp N (fun _ => c)
    have h2 : ∑ k ∈ Finset.Icc 1 (N / p), c = ((N / p : ℕ) : ℝ) * c := by simp
    rw [h1, h2]
    simp
    ring
  rw [hsum]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hfl : (N : ℝ) / p - 1 < ((N / p : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one ((N : ℝ) / p)
    rw [Nat.floor_div_eq_div] at this
    linarith
  have hfl2 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
  have hval : (N : ℝ) - c * ((N / p : ℕ) : ℝ) - (1 - c / p) * N =
      c * ((N : ℝ) / p - ((N / p : ℕ) : ℝ)) := by
    field_simp
    ring
  rw [hval, abs_mul, abs_of_nonneg hc]
  refine mul_le_of_le_one_right hc ?_
  rw [abs_le]
  constructor <;> linarith

theorem impureDelta_nonneg {p : ℕ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) : 0 ≤ impureDelta p c n := by
  unfold impureDelta
  split_ifs
  · exact mul_nonneg (Real.log_natCast_nonneg p) (pow_nonneg hc _)
  · exact le_rfl

/-- The tower sum dominates its top term: `Σ_{n ≤ x} δ(n) ≥ c^K log p`, with `K = ⌊log_p x⌋`. -/
theorem le_partialSum_impureDelta {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 ≤ c) {x : ℝ} (hx : (p : ℝ) ≤ x) :
    Real.log p * c ^ Nat.log p ⌊x⌋₊ ≤ partialSum (impureDelta p c) x := by
  have hp1 := hp.one_lt
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg p) hx
  set N := ⌊x⌋₊ with hN
  have hpN : p ≤ N := Nat.le_floor hx
  have hN0 : N ≠ 0 := by
    have := hp.pos
    omega
  set K := Nat.log p N with hK
  have hK1 : 1 ≤ K := Nat.log_pos hp1 hpN
  have hpow : p ^ K ≤ N := Nat.pow_log_le_self p hN0
  have hmem : p ^ K ∈ Finset.Ioc 0 N :=
    Finset.mem_Ioc.mpr ⟨Nat.pow_pos hp.pos, hpow⟩
  unfold partialSum
  rw [← hN]
  have hsingle := Finset.single_le_sum (f := impureDelta p c) (s := Finset.Ioc 0 N)
    (fun n _ => impureDelta_nonneg hc n) hmem
  refine le_trans (le_of_eq ?_) hsingle
  unfold impureDelta
  have htower : IsTowerPower p (p ^ K) :=
    ⟨K, Finset.mem_Icc.mpr ⟨hK1, (Nat.lt_pow_self hp1).le⟩, rfl⟩
  rw [if_pos htower, Nat.log_pow hp1]

/-- **The prime count fails for an impure factor.** -/
theorem not_count_impureWeight {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : √(p : ℝ) < c) :
    ¬ Count (impureWeight p c) := by
  intro hcount
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hc0 : 0 < c := lt_of_le_of_lt (Real.sqrt_nonneg _) hc
  -- the exponent of the drift
  set η : ℝ := Real.log c / Real.log p with hη
  have hη12 : 1 / 2 < η := by
    rw [hη, lt_div_iff₀ hlogp]
    have h1 := Real.log_lt_log (Real.sqrt_pos.mpr hp0) hc
    rw [Real.log_sqrt hp0.le] at h1
    linarith
  have hcpow : Real.exp (η * Real.log p) = c := by
    rw [hη, div_mul_cancel₀ _ hlogp.ne', Real.exp_log hc0]
  -- lower bound of the drift
  have hdrift : ∀ x : ℝ, (p : ℝ) ≤ x →
      Real.log p * ((x / (2 * p)) ^ η) ≤ partialSum (impureDelta p c) x := by
    intro x hx
    refine le_trans ?_ (le_partialSum_impureDelta hp hc0.le hx)
    refine mul_le_mul_of_nonneg_left ?_ hlogp.le
    set N := ⌊x⌋₊ with hN
    have hx0 : 0 < x := by linarith
    have hNge : x / 2 ≤ (N : ℝ) := by
      have h1 : (1 : ℝ) ≤ N := by
        have : 1 ≤ N := Nat.one_le_floor_iff x |>.mpr (by linarith)
        exact_mod_cast this
      have h2 := Nat.lt_floor_add_one x
      linarith
    have hN0 : N ≠ 0 := by
      have : 1 ≤ N := Nat.one_le_floor_iff x |>.mpr (by linarith)
      omega
    set K := Nat.log p N with hK
    have hlt : N < p ^ (K + 1) := Nat.lt_pow_succ_log_self hp.one_lt N
    have hlt' : (N : ℝ) < (p : ℝ) ^ (K + 1) := by exact_mod_cast hlt
    have hbase : x / (2 * p) ≤ (p : ℝ) ^ K := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : (p : ℝ) ^ (K + 1) = (p : ℝ) ^ K * p := pow_succ _ _
      nlinarith
    have hc1 : c ^ K = ((p : ℝ) ^ K) ^ η := by
      rw [← hcpow, ← Real.exp_nat_mul, Real.rpow_def_of_pos (pow_pos hp0 K), Real.log_pow]
      congr 1
      ring
    rw [hc1]
    exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
  -- comparison with the oscillation of `ψ`
  obtain ⟨c₀, hc₀, hneg, -⟩ := _root_.RHTower.chebyshevPsi_sub_omega_pm
  obtain ⟨C, hC0, hC⟩ := (hcount : _ =O[atTop] sqrtScale).exists_pos
  have hexpo : (1 : ℝ) - (1 - η) = η := by ring
  have hlittle : sqrtScale =o[atTop] fun x : ℝ => x ^ η := by
    have h := sqrtScale_isLittleO_rpow (η := 1 - η) (by linarith)
    rwa [hexpo] at h
  have hlit := hlittle.def (c := Real.log p * (1 / (2 * p)) ^ η / (2 * C)) (by positivity)
  have hev : ∀ᶠ x : ℝ in atTop, 0 ≤ Chebyshev.psi x - x := by
    filter_upwards [hC.bound, hlit, eventually_ge_atTop (p : ℝ), eventually_gt_atTop (1 : ℝ)]
      with x h1 h2 h3 h4
    have hx0 : 0 < x := by linarith
    have hsplit : partialSum (impureWeight p c) x =
        Chebyshev.psi x - partialSum (impureDelta p c) x := by
      unfold partialSum impureWeight
      simp only [Pi.sub_apply]
      rw [Finset.sum_sub_distrib]
      rfl
    have hdr := hdrift x h3
    have hpowsplit : (x / (2 * p)) ^ η = (1 / (2 * p)) ^ η * x ^ η := by
      rw [div_eq_mul_inv x, mul_comm x, Real.mul_rpow (by positivity) hx0.le, one_div]
    rw [hpowsplit] at hdr
    rw [Real.norm_eq_abs, hsplit] at h1
    have h5 := (abs_le.mp h1).1
    have hscale : ‖sqrtScale x‖ ≤ Real.log p * (1 / (2 * p)) ^ η / (2 * C) * ‖x ^ η‖ := h2
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hscale
    have hC' : C * ‖sqrtScale x‖ ≤ Real.log p * (1 / (2 * p)) ^ η * x ^ η / 2 := by
      have h6 := mul_le_mul_of_nonneg_left hscale hC0.le
      refine h6.trans (le_of_eq ?_)
      field_simp
    have hpos : 0 ≤ Real.log p * (1 / (2 * p)) ^ η * x ^ η := by positivity
    have h7 : Real.log p * ((1 / (2 * p)) ^ η * x ^ η) = Real.log p * (1 / (2 * p)) ^ η * x ^ η := by
      ring
    rw [h7] at hdr
    linarith
  obtain ⟨x, hx1, hx2⟩ := (hneg.and_eventually (hev.and (eventually_gt_atTop (0 : ℝ)))).exists
  have h8 : 0 < c₀ * √x := mul_pos hc₀ (Real.sqrt_pos.mpr hx2.2)
  linarith [hx2.1]

/-- A statement stable under one impure factor and implying the count fails at `Λ`. -/
theorem not_of_stable_under_impureWeight {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : √(p : ℝ) < c)
    (S : (ℕ → ℝ) → Prop) (hS : ∀ a, S a → Count a) (hstab : S vonMangoldtWeight → S (impureWeight p c)) :
    ¬ S vonMangoldtWeight := fun h => not_count_impureWeight hp hc (hS _ (hstab h))

/-! ### The size of the factor -/

theorem norm_impureFactor_le {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) {s : ℂ} :
    ‖impureFactor p c s‖ ≤ 1 + c * (p : ℝ) ^ (-s.re) := by
  unfold impureFactor
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc,
    Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]

/-- **Upper bounds survive.**  The mean square of the mimic on the critical line is at most `(1 + c/√p)²` times that of `ζ`, on every window. -/
theorem integral_norm_sq_mimic_le {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hint : IntervalIntegrable (fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) volume T₁ T₂)
    (hint2 : IntervalIntegrable (fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) volume T₁ T₂) :
    ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (1 + c * (p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 *
        ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hT hint2 (hint.const_mul _) fun t _ => ?_
  rw [norm_mul, mul_pow, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have h := norm_impureFactor_le hp hc (s := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hre : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).re = 1 / 2 := by simp
  rwa [hre] at h

/-! ### The lattice of zeros -/

private theorem exp_lattice_aux (lp lc : ℝ) (k : ℤ) (hlp : lp ≠ 0) :
    ((lp : ℝ) : ℂ) * -(((lc / lp : ℝ) : ℂ) + ((2 * Real.pi * k / lp : ℝ) : ℂ) * I) =
      ((-lc : ℝ) : ℂ) + ((-k : ℤ) : ℂ) * (2 * Real.pi * I) := by
  have h : (lp : ℂ) ≠ 0 := by exact_mod_cast hlp
  push_cast
  field_simp
  ring

/-- The zeros of the factor: `s_k = η + 2πik/log p`, `η = log c/log p`. -/
theorem impureFactor_eq_zero {p : ℕ} (hp : 1 < p) {c : ℝ} (hc : 0 < c) (k : ℤ) :
    impureFactor p c (((Real.log c / Real.log p : ℝ) : ℂ) +
      ((2 * Real.pi * k / Real.log p : ℝ) : ℂ) * I) = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hlogC : (Real.log p : ℂ) ≠ 0 := by exact_mod_cast hlogp.ne'
  unfold impureFactor
  have hcpow : (p : ℂ) ^ (-(((Real.log c / Real.log p : ℝ) : ℂ) +
      ((2 * Real.pi * k / Real.log p : ℝ) : ℂ) * I)) = ((c⁻¹ : ℝ) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp0.ne'), ← Complex.ofReal_natCast p,
      ← Complex.ofReal_log hp0.le]
    have hexp := exp_lattice_aux (Real.log p) (Real.log c) k hlogp.ne'
    rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, ← Complex.ofReal_exp,
      Real.exp_neg, Real.exp_log hc]
  rw [hcpow, ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne']
  simp

/-- **Window occupancy fails.**  Every interval of length `2π/log p` contains the ordinate of a zero of the factor, at the fixed real part
`log c/log p`. -/
theorem exists_lattice_zero_near {p : ℕ} (hp : 1 < p) (t : ℝ) :
    ∃ k : ℤ, |2 * Real.pi * k / Real.log p - t| ≤ Real.pi / Real.log p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hπ := Real.pi_pos
  set y : ℝ := t * Real.log p / (2 * Real.pi) with hy
  refine ⟨round y, ?_⟩
  have hround := abs_sub_round y
  have hval : 2 * Real.pi * (round y : ℝ) / Real.log p - t =
      2 * Real.pi / Real.log p * ((round y : ℝ) - y) := by
    rw [hy]
    field_simp
  rw [hval, abs_mul, abs_of_pos (by positivity), abs_sub_comm]
  calc 2 * Real.pi / Real.log p * |y - (round y : ℝ)| ≤ 2 * Real.pi / Real.log p * (1 / 2) :=
        mul_le_mul_of_nonneg_left hround (by positivity)
    _ = _ := by ring

/-! ### The log-mean -/

/-- The integrated logarithm of a pure factor is bounded uniformly in the interval. -/
theorem abs_integral_log_norm_one_sub_le {q lam : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hlam : 0 < lam)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    |∫ t in T₁..T₂, Real.log ‖1 - (q : ℂ) * Complex.exp (((lam * t : ℝ) : ℂ) * I)‖| ≤
      2 / lam * (1 - q)⁻¹ := by
  set z : ℝ → ℂ := fun t => (q : ℂ) * Complex.exp (((lam * t : ℝ) : ℂ) * I) with hz
  have hznorm : ∀ t, ‖z t‖ = q := by
    intro t
    simp only [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0]
    rw [Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsum : ∀ t, HasSum (fun n : ℕ => ((z t) ^ n / n).re)
      (-Real.log ‖1 - z t‖) := by
    intro t
    have h := Complex.hasSum_taylorSeries_neg_log (z := z t) (by rw [hznorm]; exact hq1)
    have h2 := (Complex.hasSum_re h)
    rwa [Complex.neg_re, Complex.log_re] at h2
  have hF : ∀ n : ℕ, Continuous fun t => ((z t) ^ n / n).re := by
    intro n
    simp only [hz]
    fun_prop
  have hbound : ∀ (n : ℕ) (t : ℝ), ‖((z t) ^ n / n).re‖ ≤ q ^ n := by
    intro n t
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, norm_pow, hznorm]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [Complex.norm_natCast]
      exact div_le_self (pow_nonneg hq0 n) hn1
  have hgeo := hasSum_geometric_of_lt_one hq0 hq1
  have hmain := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (F := fun (n : ℕ) t => ((z t) ^ n / n).re) (f := fun t => -Real.log ‖1 - z t‖) (a := T₁) (b := T₂)
    (fun n _ => q ^ n)
    (fun n => (hF n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t _ => hbound n t)
    (Filter.Eventually.of_forall fun _ _ => hgeo.summable)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ => hsum t)
  -- each term
  have hterm : ∀ n : ℕ, ‖∫ t in T₁..T₂, ((z t) ^ n / n).re‖ ≤ 2 / lam * q ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
      positivity
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set μ : ℂ := (n : ℂ) * (lam : ℂ) * I with hμ
    have hμ0 : μ ≠ 0 := by
      rw [hμ]
      have h1 : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
      have h2 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
      exact mul_ne_zero (mul_ne_zero h1 h2) I_ne_zero
    have hzpow : ∀ t : ℝ, (z t) ^ n / n =
        ((q ^ n / n : ℝ) : ℂ) * Complex.exp (μ * t) := by
      intro t
      simp only [hz, hμ]
      rw [mul_pow, ← Complex.exp_nat_mul]
      push_cast
      have h3 : (n : ℂ) * ((lam : ℂ) * (t : ℂ) * I) = (n : ℂ) * (lam : ℂ) * I * (t : ℂ) := by ring
      rw [h3]
      ring
    have hre : ∫ t in T₁..T₂, ((z t) ^ n / n).re =
        ((q ^ n / n : ℝ) : ℂ).re * (∫ t in T₁..T₂, Complex.exp (μ * t)).re := by
      have hcont : Continuous fun t : ℝ => Complex.exp (μ * t) := by fun_prop
      have h4 := intervalIntegral.intervalIntegral_eq_integral_uIoc
        (fun t : ℝ => Complex.exp (μ * t)) T₁ T₂ volume
      have hrecomp : (∫ t in T₁..T₂, Complex.exp (μ * t)).re =
          ∫ t in T₁..T₂, (Complex.exp (μ * t)).re := by
        rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
        exact (Complex.reCLM.integral_comp_comm
          (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).symm
      rw [hrecomp, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      show ((z t) ^ n / n).re = _
      rw [hzpow t, Complex.re_ofReal_mul, Complex.ofReal_re]
    rw [hre, Complex.ofReal_re, integral_exp_mul_complex hμ0, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity)]
    have hnormμ : ‖μ‖ = n * lam := by
      rw [hμ, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real,
        Real.norm_of_nonneg hlam.le, Complex.norm_I, mul_one]
    have hbdexp : ∀ t : ℝ, ‖Complex.exp (μ * t)‖ = 1 := by
      intro t
      have h5 : μ * (t : ℂ) = (((n : ℝ) * lam * t : ℝ) : ℂ) * I := by
        rw [hμ]
        push_cast
        ring
      rw [h5, Complex.norm_exp_ofReal_mul_I]
    have hint : |((Complex.exp (μ * T₂) - Complex.exp (μ * T₁)) / μ).re| ≤ 2 / (n * lam) := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_div, hnormμ]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      refine (norm_sub_le _ _).trans ?_
      rw [hbdexp, hbdexp]
      norm_num
    calc q ^ n / n * |((Complex.exp (μ * T₂) - Complex.exp (μ * T₁)) / μ).re|
        ≤ q ^ n / n * (2 / (n * lam)) := mul_le_mul_of_nonneg_left hint (by positivity)
      _ = 2 / lam * q ^ n * (1 / (n * n)) := by
        field_simp
      _ ≤ 2 / lam * q ^ n * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_one (by positivity)]
        nlinarith
      _ = _ := mul_one _
  have hbd := tsum_of_norm_bounded (hgeo.mul_left (2 / lam)) hterm
  rw [hmain.tsum_eq, intervalIntegral.integral_neg, norm_neg, Real.norm_eq_abs] at hbd
  exact hbd

/-- **The mean of `log|1 − c p^{−½−it}|` is `log(c/√p)`.** -/
theorem tendsto_logMean_impureFactor {p : ℕ} (hp : 1 < p) {c : ℝ} (hc : √(p : ℝ) < c) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T),
        Real.log ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) atTop
      (𝓝 (Real.log (c / √(p : ℝ)))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hlam : 0 < Real.log p := Real.log_pos hp1
  have hs0 : 0 < √(p : ℝ) := Real.sqrt_pos.mpr hp0
  have hc0 : 0 < c := by linarith
  set r : ℝ := c / √(p : ℝ) with hr
  have hr1 : 1 < r := by rw [hr, one_lt_div hs0]; exact hc
  have hr0 : 0 < r := by linarith
  set q : ℝ := r⁻¹ with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by rw [hq]; exact inv_lt_one_of_one_lt₀ hr1
  -- the factor in terms of the pure factor
  have hsqrtexp : Real.exp (Real.log p / 2) = √(p : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0]
    congr 1
    ring
  have hpt : ∀ t : ℝ, Real.log ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ =
      Real.log r + Real.log ‖1 - (q : ℂ) * Complex.exp (((Real.log p * t : ℝ) : ℂ) * I)‖ := by
    intro t
    have hcpow : (p : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        (((√(p : ℝ))⁻¹ : ℝ) : ℂ) * Complex.exp (-(((Real.log p * t : ℝ) : ℂ) * I)) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp0.ne'), ← Complex.ofReal_natCast p,
        ← Complex.ofReal_log hp0.le, ← hsqrtexp, ← Real.exp_neg, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    set e := Complex.exp (((Real.log p * t : ℝ) : ℂ) * I) with he
    have hene : e ≠ 0 := Complex.exp_ne_zero _
    have heinv : Complex.exp (-(((Real.log p * t : ℝ) : ℂ) * I)) = e⁻¹ := by
      rw [Complex.exp_neg]
    have hrq : (r : ℂ) * (q : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hq, mul_inv_cancel₀ hr0.ne', Complex.ofReal_one]
    have hee : e⁻¹ * e = 1 := inv_mul_cancel₀ hene
    have hrc : (c : ℂ) * (((√(p : ℝ))⁻¹ : ℝ) : ℂ) = (r : ℂ) := by
      rw [← Complex.ofReal_mul, hr, div_eq_mul_inv]
    have heq : impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
        -((r : ℂ) * e⁻¹) * (1 - (q : ℂ) * e) := by
      unfold impureFactor
      rw [hcpow, heinv]
      linear_combination (-e⁻¹) * hrc - (e⁻¹ * e) * hrq - hee
    have hnorme : ‖e‖ = 1 := by rw [he, Complex.norm_exp_ofReal_mul_I]
    have hne : (1 - (q : ℂ) * e) ≠ 0 := by
      intro h
      have h2 : (q : ℂ) * e = 1 := by
        rw [sub_eq_zero] at h
        exact h.symm
      have h3 := congrArg norm h2
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0.le, hnorme, mul_one, norm_one] at h3
      linarith
    rw [heq, norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_inv,
      hnorme, inv_one, mul_one, Real.log_mul hr0.ne' (norm_ne_zero_iff.mpr hne)]
  -- the pure factor is continuous, so its logarithm integrates
  have hcont : Continuous fun t : ℝ =>
      Real.log ‖1 - (q : ℂ) * Complex.exp (((Real.log p * t : ℝ) : ℂ) * I)‖ := by
    have hG : Continuous fun t : ℝ => ‖1 - (q : ℂ) * Complex.exp (((Real.log p * t : ℝ) : ℂ) * I)‖ := by
      fun_prop
    refine hG.log fun t h => ?_
    have h1 := norm_eq_zero.mp h
    have h2 : (q : ℂ) * Complex.exp (((Real.log p * t : ℝ) : ℂ) * I) = 1 := by
      rw [sub_eq_zero] at h1
      exact h1.symm
    have h3 := congrArg norm h2
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0.le, Complex.norm_exp_ofReal_mul_I,
      mul_one, norm_one] at h3
    linarith
  have hbound : ∀ T : ℝ, 0 < T → |T⁻¹ * ∫ t in T..(2 * T),
      Real.log ‖1 - (q : ℂ) * Complex.exp (((Real.log p * t : ℝ) : ℂ) * I)‖| ≤
        T⁻¹ * (2 / Real.log p * (1 - q)⁻¹) := by
    intro T hT
    rw [abs_mul, abs_of_pos (inv_pos.mpr hT)]
    exact mul_le_mul_of_nonneg_left
      (abs_integral_log_norm_one_sub_le hq0.le hq1 hlam (by linarith)) (inv_pos.mpr hT).le
  have hsplit : ∀ᶠ T : ℝ in atTop, T⁻¹ * ∫ t in T..(2 * T),
      Real.log ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ =
        Real.log r + T⁻¹ * ∫ t in T..(2 * T),
          Real.log ‖1 - (q : ℂ) * Complex.exp (((Real.log p * t : ℝ) : ℂ) * I)‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simp_rw [hpt]
    rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _), intervalIntegral.integral_const, smul_eq_mul, mul_add]
    congr 1
    field_simp
    ring
  have hzero : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T),
      Real.log ‖1 - (q : ℂ) * Complex.exp (((Real.log p * t : ℝ) : ℂ) * I)‖) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_inv_atTop_zero.mul_const
      (2 / Real.log p * (1 - q)⁻¹)).trans (by simp))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Real.norm_eq_abs]
    exact hbound T hT
  have hlim := (tendsto_const_nhds (x := Real.log r)).add hzero
  rw [add_zero] at hlim
  exact hlim.congr' (hsplit.mono fun T hT => hT.symm)

end GaloisForLFunctions.ArithmeticProduction
