import GaloisForLFunctions.RHTower.CCMPolarPrimePolynomialFrequencyCancellation
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistHalfDensityWindow
import GaloisForLFunctions.RHTower.CCMRestrictedWeilCanonicalHeadCompletedErrorControl

/-!
# Prime-polar cancellation on exponential frequency windows

The literal finite-aperture multiplier is uniformly `o(exp a)` for every
band `|ξ| ≤ exp (K*a)`, with fixed positive `K`. The polynomial-frequency
source theorem handles the lower band. Above it, complete half-density
Mangoldt prefixes apply at the exact cutoffs `floor (exp a)` and
`floor (exp (2*a))`. The small prime head and continuous polar term are
retained. No zero-location or cancellation premise is assumed.
-/

open Filter Topology
noncomputable section
namespace RHTower

/-- The exact polar multiplier decays with frequency, uniformly in aperture. -/
theorem abs_polarMultiplier_le_exp_div_frequency {a ξ : ℝ}
    (ha : 0 ≤ a) (hξ : 1 ≤ |ξ|) :
    |polarMultiplier a ξ| ≤ 6 * Real.exp a / |ξ| := by
  have hneg : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
  have hs : |Real.sinh a| ≤ Real.exp a := by
    rw [Real.sinh_eq, abs_le]
    constructor <;> linarith [Real.exp_pos a, Real.exp_pos (-a)]
  have hc : |Real.cosh a| ≤ Real.exp a := by
    rw [Real.cosh_eq, abs_of_pos (by positivity : 0 < (Real.exp a + Real.exp (-a)) / 2)]
    linarith
  have hx0 : 0 < |ξ| := lt_of_lt_of_le zero_lt_one hξ
  have hd : 0 < ξ ^ 2 + (1 / 4 : ℝ) := by positivity
  have hfirst : |2 * Real.sinh a * Real.cos (2 * a * ξ)| ≤ 2 * Real.exp a := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num))
      (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hsecond : |4 * ξ * Real.cosh a * Real.sin (2 * a * ξ)| ≤
      4 * |ξ| * Real.exp a := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity))
      (Real.abs_sin_le_one _) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hn : |2 * Real.sinh a * Real.cos (2 * a * ξ) +
      4 * ξ * Real.cosh a * Real.sin (2 * a * ξ)| ≤ 6 * |ξ| * Real.exp a := by
    refine ((abs_add_le _ _).trans (add_le_add hfirst hsecond)).trans ?_
    nlinarith [Real.exp_pos a]
  rw [polarMultiplier, abs_div, abs_of_pos hd]
  refine (div_le_div_of_nonneg_right hn hd.le).trans ?_
  rw [div_le_div_iff₀ hd hx0]
  calc
    (6 * |ξ| * Real.exp a) * |ξ| = 6 * Real.exp a * ξ ^ 2 := by rw [← sq_abs ξ]; ring
    _ ≤ 6 * Real.exp a * (ξ ^ 2 + 1 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private theorem halfDensityTwist_re {n : ℕ} (hn : 2 ≤ n) (ξ : ℝ) :
    ((1 / Real.sqrt (n : ℝ)) • Sieve.vonMangoldtTwist (-ξ) n).re =
      criticalMellinAtomWeight n * Real.cos (ξ * Real.log (n : ℝ)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  have hphase : (n : ℂ) ^ (-(((-ξ : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((ξ * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hn0, hlog]
    congr 1
    push_cast
    ring
  rw [Complex.smul_re, smul_eq_mul, Sieve.vonMangoldtTwist, hphase,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one,
    Real.exp_zero, one_mul]
  rw [criticalMellinAtomWeight_eq_div_sqrt]
  ring

/-- Exact source weld, including the vanishing zero and one terms. -/
theorem criticalMellinPrimeCosineModule_eq_halfDensityTwist_re (a ξ : ℝ) :
    criticalMellinPrimeCosineModule a ξ =
      2 * (∑ n ∈ Finset.range (⌊Real.exp (2 * a)⌋₊ + 1),
        (1 / Real.sqrt (n : ℝ)) • Sieve.vonMangoldtTwist (-ξ) n).re := by
  let N := ⌊Real.exp (2 * a)⌋₊
  have hs : Finset.Icc 2 N ⊆ Finset.range (N + 1) := by
    intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  have hsum := Finset.sum_subset (f := fun n : ℕ =>
    (1 / Real.sqrt (n : ℝ)) • Sieve.vonMangoldtTwist (-ξ) n) hs
    (fun n hn hout => by
      have hcase : n = 0 ∨ n = 1 := by
        simp only [Finset.mem_range, Finset.mem_Icc] at hn hout
        omega
      rcases hcase with rfl | rfl <;> simp [Sieve.vonMangoldtTwist])
  rw [← hsum, criticalMellinPrimeCosineModule]
  rw [Complex.re_sum]
  congr 1
  exact Finset.sum_congr rfl fun n hn => (halfDensityTwist_re (Finset.mem_Icc.mp hn).1 ξ).symm

/-- The literal prime cosine module is controlled by the complete twisted prefix. -/
theorem abs_criticalMellinPrimeCosineModule_le_halfDensityTwist (a ξ : ℝ) :
    |criticalMellinPrimeCosineModule a ξ| ≤
      2 * ‖∑ n ∈ Finset.range (⌊Real.exp (2 * a)⌋₊ + 1),
        (1 / Real.sqrt (n : ℝ)) • Sieve.vonMangoldtTwist (-ξ) n‖ := by
  rw [criticalMellinPrimeCosineModule_eq_halfDensityTwist_re, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)

private theorem eventually_exponential_cutoffs (L : ℝ) (hL : 1 ≤ L) :
    ∀ᶠ a : ℝ in atTop,
      Sieve.twoRangeXmin ((19 : ℝ) / 20) (Real.exp (L * a)) ≤
          (⌊Real.exp a⌋₊ : ℝ) ∧
      Real.log (⌊Real.exp (2 * a)⌋₊ : ℝ) ≤
          Sieve.twoRangeLx 2 (Real.exp (L * a)) ∧
      Sieve.twoRangeT₀ 2 100 (Real.exp (L * a)) ≤ (2 * a) ^ (312 : ℕ) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hr : Tendsto (fun a : ℝ => (L * a) ^ ((19 : ℝ) / 20) / a)
      atTop (𝓝 0) := by
    have hz := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 20) (by norm_num)).const_mul
      (L ^ ((19 : ℝ) / 20))
    simp only [mul_zero] at hz
    refine hz.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [Real.mul_rpow hL0.le ha.le]
    calc
      L ^ ((19 : ℝ) / 20) * a ^ (-((1 : ℝ) / 20)) =
          L ^ ((19 : ℝ) / 20) * (a ^ ((19 : ℝ) / 20) / a ^ (1 : ℝ)) := by
        rw [← Real.rpow_sub ha]
        norm_num
      _ = _ := by rw [Real.rpow_one]; ring
  filter_upwards [hr.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (L ^ (311 : ℕ))]
    with a hr ha hpow
  have ha0 : 0 < a := by linarith
  have hsmall : (L * a) ^ ((19 : ℝ) / 20) ≤ a / 2 := by
    have h := (div_le_iff₀ ha0).mp hr
    linarith
  have hehalf : 2 ≤ Real.exp (a / 2) := by
    linarith [Real.add_one_le_exp (a / 2)]
  have hesq : Real.exp a = Real.exp (a / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hfloor : Real.exp (a / 2) ≤ (⌊Real.exp a⌋₊ : ℝ) := by
    have hf := Nat.lt_floor_add_one (Real.exp a)
    nlinarith
  have hNpos : (0 : ℝ) < (⌊Real.exp (2 * a)⌋₊ : ℝ) := by
    have hNat : 1 ≤ ⌊Real.exp (2 * a)⌋₊ :=
      Nat.le_floor (by simpa only [Nat.cast_one] using Real.one_le_exp (show 0 ≤ 2 * a by positivity))
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNat)
  have hNlog : Real.log (⌊Real.exp (2 * a)⌋₊ : ℝ) ≤ 2 * a := by
    have h := Real.log_le_log hNpos (Nat.floor_le (Real.exp_pos (2 * a)).le)
    simpa only [Real.log_exp] using h
  refine ⟨?_, ?_, ?_⟩
  · change Real.exp ((Real.log (Real.exp (L * a))) ^ ((19 : ℝ) / 20)) ≤ _
    rw [Real.log_exp]
    exact (Real.exp_le_exp.mpr hsmall).trans hfloor
  · rw [Sieve.twoRangeLx, Real.log_exp, Real.rpow_two]
    have hLa : a ≤ L * a := by nlinarith
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact hNlog.trans (by nlinarith)
  · have hT : Sieve.twoRangeT₀ 2 100 (Real.exp (L * a)) = (L * a) ^ (311 : ℕ) := by
      rw [Sieve.twoRangeT₀, Real.log_exp]
      norm_num only
      exact Real.rpow_natCast _ _
    rw [hT, mul_pow]
    calc
      L ^ (311 : ℕ) * a ^ (311 : ℕ) ≤ a * a ^ (311 : ℕ) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = a ^ (312 : ℕ) := by rw [show (312 : ℕ) = 311 + 1 from rfl, pow_succ]; ring
      _ ≤ (2 * a) ^ (312 : ℕ) := pow_le_pow_left₀ ha0.le (by linarith) _

private theorem exponential_cutoff_sqrt_upper {a : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (⌊Real.exp a⌋₊ : ℝ) ≤ Real.exp (a / 2) ∧
      Real.sqrt ((⌊Real.exp (2 * a)⌋₊ : ℝ) + 1) ≤ 2 * Real.exp a := by
  constructor
  · exact (Real.sqrt_le_sqrt (Nat.floor_le (Real.exp_pos a).le)).trans_eq
      (sqrt_exp_eq_exp_half a)
  · have hroot := Real.sqrt_le_sqrt
      (add_le_add (Nat.floor_le (Real.exp_pos (2 * a)).le) (le_refl (1 : ℝ)))
    refine hroot.trans ?_
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [show 2 * a = a + a by ring, Real.exp_add]
      nlinarith [Real.one_le_exp ha]

/-- The complete actual prime module cancels on the high-frequency portion
of every exponential aperture window. -/
theorem eventually_abs_criticalMellinPrimeCosineModule_le_exponentialHighFrequency
    (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ξ : ℝ,
      (2 * a) ^ (312 : ℕ) ≤ |ξ| → |ξ| ≤ Real.exp (K * a) →
      |criticalMellinPrimeCosineModule a ξ| ≤ ε * Real.exp a := by
  let L := K + 1
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hscale : Tendsto (fun a : ℝ => Real.exp (L * a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hL0)
  have hhead : Tendsto (fun a : ℝ => 42 * Real.exp (-(a / 2))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply, id_eq] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).const_mul 42
  filter_upwards [hscale.eventually (Sieve.eventually_norm_vonMangoldtTwist_halfDensity_prefix_le
      (ε / 32) (by positivity)),
    eventually_exponential_cutoffs L hL,
    hhead.eventually_le_const (by positivity : (0 : ℝ) < ε / 2),
    eventually_ge_atTop (0 : ℝ)] with a harith hcut hsmall ha
  intro ξ hlo hhi
  have hMN : ⌊Real.exp a⌋₊ ≤ ⌊Real.exp (2 * a)⌋₊ :=
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hupper : |-ξ| ≤ 2 * Real.pi * Real.exp (L * a) := by
    rw [abs_neg]
    calc
      |ξ| ≤ Real.exp (K * a) := hhi
      _ ≤ Real.exp (L * a) := Real.exp_le_exp.mpr (by dsimp [L]; nlinarith)
      _ ≤ 2 * Real.pi * Real.exp (L * a) := by
        have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        nlinarith [Real.exp_pos (L * a)]
  have hb := harith ⌊Real.exp a⌋₊ ⌊Real.exp (2 * a)⌋₊ (-ξ) hMN hcut.1 hcut.2.1
    (by simpa only [abs_neg] using hcut.2.2.trans hlo) hupper
  obtain ⟨hrM, hrN⟩ := exponential_cutoff_sqrt_upper ha
  have hprime := (abs_criticalMellinPrimeCosineModule_le_halfDensityTwist a ξ).trans
    (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2))
  have hhead' : 42 * Real.exp (a / 2) ≤ ε / 2 * Real.exp a := by
    have hm := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos a).le
    rw [mul_assoc 42, ← Real.exp_add, show -(a / 2) + a = a / 2 by ring] at hm
    exact hm
  nlinarith [Real.exp_pos a]

/-- Uniform cancellation for the literal prime-polar multiplier on every
fixed exponential frequency window. All cutoff endpoints and prime powers
are included; no cancellation premise is assumed. -/
theorem eventually_abs_polarPrimeStieltjesSymbol_le_exponentialFrequency
    (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ξ : ℝ, |ξ| ≤ Real.exp (K * a) →
      |polarPrimeStieltjesSymbol a ξ| ≤ ε * Real.exp a := by
  have hpow : Tendsto (fun a : ℝ => (2 * a) ^ (312 : ℕ)) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def, id_eq] using
      (tendsto_rpow_atTop (show (0 : ℝ) < (312 : ℕ) by norm_num)).comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  filter_upwards [eventually_abs_polarPrimeStieltjesSymbol_le_polynomialFrequency 312 ε hε,
    eventually_abs_criticalMellinPrimeCosineModule_le_exponentialHighFrequency
      K (ε / 2) hK (by positivity),
    hpow.eventually (eventually_ge_atTop (max 1 (12 / ε))),
    eventually_ge_atTop (0 : ℝ)] with a hlow hhigh hthreshold ha
  intro ξ hξ
  by_cases hl : |ξ| ≤ (2 * a) ^ (312 : ℕ)
  · exact hlow ξ hl
  have hband : (2 * a) ^ (312 : ℕ) ≤ |ξ| := (lt_of_not_ge hl).le
  have hx1 : 1 ≤ |ξ| := (le_max_left _ _).trans (hthreshold.trans hband)
  have hx0 : 0 < |ξ| := lt_of_lt_of_le zero_lt_one hx1
  have hxeps : 12 ≤ ε * |ξ| := by
    have h := (le_max_right (1 : ℝ) (12 / ε)).trans (hthreshold.trans hband)
    have hh := (div_le_iff₀ hε).mp h
    linarith
  have hp : |polarMultiplier a ξ| ≤ ε / 2 * Real.exp a := by
    refine (abs_polarMultiplier_le_exp_div_frequency ha hx1).trans ?_
    rw [div_le_iff₀ hx0]
    calc
      6 * Real.exp a ≤ (ε / 2 * |ξ|) * Real.exp a :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos a).le
      _ = _ := by ring
  have hc := hhigh ξ hband hξ
  change |polarMultiplier a ξ - criticalMellinPrimeCosineModule a ξ| ≤ _
  have ht : |polarMultiplier a ξ - criticalMellinPrimeCosineModule a ξ| ≤
      |polarMultiplier a ξ| + |criticalMellinPrimeCosineModule a ξ| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (polarMultiplier a ξ) 0 (criticalMellinPrimeCosineModule a ξ)
  exact ht.trans ((add_le_add hp hc).trans_eq (by ring))

end RHTower
end
