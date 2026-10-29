import GaloisForLFunctions.RHTower.PoissonSummationPiecewise
import GaloisForLFunctions.HTGeometry.MonotonePhaseFirstDerivativeTest

/-!
# Truncated Poisson summation for an exponential sum

For a real phase `f` on `[A, B]` (`A ≤ B` integers) with `f″ ≥ 0` and `|f′| ≤ K′`, and an integer
`K ≥ max(1, 2K′)`,

  `Σ_{A<m≤B} e(f(m)) = ∫_A^B e(f) + Σ_{n=1}^{K} (∫_A^B e(f(t) + nt) dt + ∫_A^B e(f(t) − nt) dt) + E`,
  `‖E‖ ≤ 5`  (`norm_sum_sub_truncatedPoisson_le`, `e(x) = exp(2πix)`).

**Proof.**  Second-order Euler–Maclaurin at integer endpoints gives
`Σ φ(m) = ∫ φ + (φ(B) − φ(A))/2 + ∫ P φ″`, `φ = e(f)`, with `P` the periodic primitive of the
sawtooth (`sum_Ioc_eq_integral_add_sawPrimitive`).  The cosine series of `P` converges absolutely,
so `∫ P φ″` is the sum of `(∫ cos(2πnt) φ″)/(2π²n²)` corrected by `φ′(B) − φ′(A)` against
`Σ 1/n² = π²/6` (`hasSum_integral_cos_mul_div_sq`).  Two integrations by parts at integer endpoints
turn the `n`-th term into `2∫ cos(2πnt) φ` (`integral_cos_mul_second_deriv`), which is the pair of
dual integrals.  For `n > K` the term is instead bounded directly: `φ″ = (2πif″ − 4π²f′²)φ`, the
`f″` part has total mass `≤ 4πK′`, and the `f′²` part is a first-derivative-test integral with phase
derivative `≥ 2π(n − K′)` (`norm_integral_cos_mul_second_deriv_le`).  The tail is then `O(1)` by
`Σ_{n>K} n^{−2} ≤ 2/(K + 1)`.
-/

open Complex MeasureTheory Set intervalIntegral Filter Topology
open scoped Interval

namespace RHTower

noncomputable section

/-! ## Euler–Maclaurin at integer endpoints -/

/-- Second-order Euler–Maclaurin at integer endpoints, real form. -/
theorem sum_Ioc_eq_integral_add_sawPrimitive_real {A B : ℤ} (hAB : A ≤ B) {h h' h'' : ℝ → ℝ}
    (hd1 : ∀ x ∈ Icc (A : ℝ) B, HasDerivAt h (h' x) x)
    (hd2 : ∀ x ∈ Icc (A : ℝ) B, HasDerivAt h' (h'' x) x)
    (hc2 : ContinuousOn h'' (Icc (A : ℝ) B)) :
    ∑ m ∈ Finset.Ioc A B, h m
      = (∫ x in (A : ℝ)..B, h x) + (h B - h A) / 2
        + ∫ x in (A : ℝ)..B, GaloisForLFunctions.RHTower.sawPrimitive x * h'' x := by
  have hab : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have := GaloisForLFunctions.RHTower.em_dilated hab one_pos hd1 hd2 hc2
  simp only [div_one, Int.floor_intCast, mul_one, one_mul,
    GaloisForLFunctions.RHTower.sawPrimitive_intCast, zero_mul, mul_zero, sub_zero, add_zero,
    GaloisForLFunctions.RHTower.sawUnit, Int.fract_intCast] at this
  rw [this]
  ring

/-- **Second-order Euler–Maclaurin at integer endpoints.**  At integers the sawtooth equals `1/2`
and its periodic primitive vanishes, so only the trapezoid correction and the `P φ″` remainder
survive. -/
theorem sum_Ioc_eq_integral_add_sawPrimitive {A B : ℤ} (hAB : A ≤ B) {φ φ' φ'' : ℝ → ℂ}
    (hd1 : ∀ x ∈ Icc (A : ℝ) B, HasDerivAt φ (φ' x) x)
    (hd2 : ∀ x ∈ Icc (A : ℝ) B, HasDerivAt φ' (φ'' x) x)
    (hc2 : ContinuousOn φ'' (Icc (A : ℝ) B)) :
    ∑ m ∈ Finset.Ioc A B, φ m
      = (∫ x in (A : ℝ)..B, φ x) + (φ B - φ A) / 2
        + ∫ x in (A : ℝ)..B, (GaloisForLFunctions.RHTower.sawPrimitive x : ℂ) * φ'' x := by
  have hab : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hφc : ContinuousOn φ (Icc (A : ℝ) B) := fun x hx =>
    (hd1 x hx).continuousAt.continuousWithinAt
  have hφi : IntervalIntegrable φ volume (A : ℝ) B :=
    (hφc.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hφ''i : IntervalIntegrable φ'' volume (A : ℝ) B :=
    (hc2.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hPi : IntervalIntegrable
      (fun x => (GaloisForLFunctions.RHTower.sawPrimitive x : ℂ) * φ'' x) volume (A : ℝ) B := by
    refine ⟨hφ''i.1.bdd_mul (c := 1 / 8) ?_ ?_, hφ''i.2.bdd_mul (c := 1 / 8) ?_ ?_⟩
    · exact (Complex.measurable_ofReal.comp
        GaloisForLFunctions.RHTower.measurable_sawPrimitive).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact GaloisForLFunctions.RHTower.abs_sawPrimitive_le x
    · exact (Complex.measurable_ofReal.comp
        GaloisForLFunctions.RHTower.measurable_sawPrimitive).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact GaloisForLFunctions.RHTower.abs_sawPrimitive_le x
  have hre := sum_Ioc_eq_integral_add_sawPrimitive_real hAB (h := fun x => (φ x).re)
    (h' := fun x => (φ' x).re) (h'' := fun x => (φ'' x).re)
    (fun x hx => Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd1 x hx))
    (fun x hx => Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd2 x hx))
    (Complex.continuous_re.comp_continuousOn hc2)
  have him := sum_Ioc_eq_integral_add_sawPrimitive_real hAB (h := fun x => (φ x).im)
    (h' := fun x => (φ' x).im) (h'' := fun x => (φ'' x).im)
    (fun x hx => Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hd1 x hx))
    (fun x hx => Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hd2 x hx))
    (Complex.continuous_im.comp_continuousOn hc2)
  have hre1 : (∫ x in (A : ℝ)..B, φ x).re = ∫ x in (A : ℝ)..B, (φ x).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hφi
    simpa using this.symm
  have him1 : (∫ x in (A : ℝ)..B, φ x).im = ∫ x in (A : ℝ)..B, (φ x).im := by
    have := Complex.imCLM.intervalIntegral_comp_comm hφi
    simpa using this.symm
  have hre2 : (∫ x in (A : ℝ)..B, (GaloisForLFunctions.RHTower.sawPrimitive x : ℂ) * φ'' x).re
      = ∫ x in (A : ℝ)..B, GaloisForLFunctions.RHTower.sawPrimitive x * (φ'' x).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hPi
    simpa using this.symm
  have him2 : (∫ x in (A : ℝ)..B, (GaloisForLFunctions.RHTower.sawPrimitive x : ℂ) * φ'' x).im
      = ∫ x in (A : ℝ)..B, GaloisForLFunctions.RHTower.sawPrimitive x * (φ'' x).im := by
    have := Complex.imCLM.intervalIntegral_comp_comm hPi
    simpa using this.symm
  apply Complex.ext
  · rw [Complex.re_sum, Complex.add_re, Complex.add_re, hre1, hre2, hre]
    simp
  · rw [Complex.im_sum, Complex.add_im, Complex.add_im, him1, him2, him]
    simp

/-! ## The cosine series of the remainder -/

/-- **The remainder interchange, complex form.**  The `1/n²` cosine samples of a continuous weight
sum to its integral against `2π²(1/12 − P)`. -/
theorem hasSum_integral_cos_mul_div_sq {a b : ℝ} (hab : a ≤ b) {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc a b)) :
    HasSum (fun n : ℕ => (∫ t in a..b, (Real.cos (2 * Real.pi * n * t) : ℂ) * w t)
        / (((n : ℝ) ^ (2 : ℕ) : ℝ) : ℂ))
      (∫ t in a..b, (((2 * Real.pi ^ (2 : ℕ) *
          (1 / 12 - GaloisForLFunctions.RHTower.sawPrimitive t)) : ℝ) : ℂ) * w t) := by
  set μ : Measure ℝ := volume.restrict (Ioc a b) with hμ
  set F : ℕ → ℝ → ℂ := fun n t =>
    (Real.cos (2 * Real.pi * n * t) : ℂ) * w t / (((n : ℝ) ^ (2 : ℕ) : ℝ) : ℂ) with hF
  have hwμ : Integrable w μ := by
    have : IntervalIntegrable w volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]; exact hw
    exact this.1
  have hFint : ∀ n : ℕ, Integrable (F n) μ := by
    intro n
    have hb : Integrable (fun t : ℝ => (Real.cos (2 * Real.pi * n * t) : ℂ) * w t) μ :=
      hwμ.bdd_mul (Measurable.aestronglyMeasurable (by fun_prop))
        (Filter.Eventually.of_forall fun t => by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    exact hb.div_const _
  have hnormle : ∀ n : ℕ, (∫ t, ‖F n t‖ ∂μ) ≤ (∫ t, ‖w t‖ ∂μ) / (n : ℝ) ^ (2 : ℕ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF]
    have hnpos : (0 : ℝ) < (n : ℝ) ^ (2 : ℕ) := by positivity
    have hptw : ∀ t, ‖F n t‖ ≤ ‖w t‖ / (n : ℝ) ^ (2 : ℕ) := by
      intro t
      have habs : |Real.cos (2 * Real.pi * n * t)| ≤ 1 := Real.abs_cos_le_one _
      simp only [hF, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
      gcongr
      nlinarith [norm_nonneg (w t)]
    calc (∫ t, ‖F n t‖ ∂μ) ≤ ∫ t, ‖w t‖ / (n : ℝ) ^ (2 : ℕ) ∂μ :=
          integral_mono (hFint n).norm (hwμ.norm.div_const _) hptw
      _ = (∫ t, ‖w t‖ ∂μ) / (n : ℝ) ^ (2 : ℕ) := MeasureTheory.integral_div _ _
  have hsummable : Summable fun n : ℕ => ∫ t, ‖F n t‖ ∂μ := by
    have hdom : Summable fun n : ℕ => (∫ t, ‖w t‖ ∂μ) / (n : ℝ) ^ (2 : ℕ) := by
      have hml := (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (∫ t, ‖w t‖ ∂μ)
      exact hml.congr fun n => by ring
    exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hnormle hdom
  have hmain := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hsummable
  have htsum : ∀ t, (∑' n : ℕ, F n t)
      = (((2 * Real.pi ^ (2 : ℕ) *
          (1 / 12 - GaloisForLFunctions.RHTower.sawPrimitive t)) : ℝ) : ℂ) * w t := by
    intro t
    have h := (Complex.hasSum_ofReal.mpr
      (GaloisForLFunctions.RHTower.hasSum_cos_div_sq t)).mul_right (w t)
    refine (h.congr_fun fun n => ?_).tsum_eq
    simp only [hF]
    push_cast
    ring
  simp only [htsum] at hmain
  rw [intervalIntegral.integral_of_le hab]
  refine hmain.congr_fun fun n => ?_
  simp only [hF]
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_div]

/-! ## Two integrations by parts at integer endpoints -/

/-- At integer endpoints, `∫ cos(2πnt) φ″ = φ′(B) − φ′(A) − 4π²n² ∫ cos(2πnt) φ`. -/
theorem integral_cos_mul_second_deriv {A B : ℤ} (hAB : A ≤ B) {φ φ' φ'' : ℝ → ℂ} (n : ℕ)
    (hd1 : ∀ x ∈ Icc (A : ℝ) B, HasDerivAt φ (φ' x) x)
    (hd2 : ∀ x ∈ Icc (A : ℝ) B, HasDerivAt φ' (φ'' x) x)
    (hc2 : ContinuousOn φ'' (Icc (A : ℝ) B)) :
    (∫ t in (A : ℝ)..B, (Real.cos (2 * Real.pi * n * t) : ℂ) * φ'' t)
      = (φ' B - φ' A) - ((4 * Real.pi ^ 2 * (n : ℝ) ^ 2 : ℝ) : ℂ)
          * ∫ t in (A : ℝ)..B, (Real.cos (2 * Real.pi * n * t) : ℂ) * φ t := by
  have hab : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have huI : uIcc (A : ℝ) B = Icc (A : ℝ) B := uIcc_of_le hab
  set ω : ℝ := 2 * Real.pi * n with hω
  have hc : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (Real.cos (ω * t) : ℂ))
      ((-(Real.sin (ω * x) * ω) : ℝ) : ℂ) x := fun x =>
    (((hasDerivAt_id' x).const_mul ω).cos).ofReal_comp.congr_deriv (by push_cast; ring)
  have hs : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (((-(Real.sin (ω * t) * ω)) : ℝ) : ℂ))
      (((-(Real.cos (ω * x) * ω * ω)) : ℝ) : ℂ) x := fun x =>
    ((((hasDerivAt_id' x).const_mul ω).sin).mul_const ω).neg.ofReal_comp.congr_deriv
      (by push_cast; ring)
  have hφc : ContinuousOn φ (Icc (A : ℝ) B) := fun x hx =>
    (hd1 x hx).continuousAt.continuousWithinAt
  have hφ'c : ContinuousOn φ' (Icc (A : ℝ) B) := fun x hx =>
    (hd2 x hx).continuousAt.continuousWithinAt
  have hcos1 : ∀ m : ℤ, Real.cos (ω * m) = 1 := fun m => by
    rw [hω, show 2 * Real.pi * n * (m : ℝ) = ((n * m : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_int_mul_two_pi _
  have hsin0 : ∀ m : ℤ, Real.sin (ω * m) = 0 := fun m => by
    rw [hω, show 2 * Real.pi * n * (m : ℝ) = ((2 * n * m : ℤ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_int_mul_pi _
  -- first integration by parts
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => (Real.cos (ω * t) : ℂ)) (v := φ')
    (u' := fun x => ((-(Real.sin (ω * x) * ω) : ℝ) : ℂ)) (v' := φ'')
    (fun x _ => hc x) (fun x hx => hd2 x (by rwa [huI] at hx))
    ((Continuous.continuousOn (by fun_prop)).intervalIntegrable)
    ((hc2.mono (by rw [huI])).intervalIntegrable)
  -- second integration by parts
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => (((-(Real.sin (ω * t) * ω)) : ℝ) : ℂ)) (v := φ)
    (u' := fun x => (((-(Real.cos (ω * x) * ω * ω)) : ℝ) : ℂ)) (v' := φ')
    (fun x _ => hs x) (fun x hx => hd1 x (by rwa [huI] at hx))
    ((Continuous.continuousOn (by fun_prop)).intervalIntegrable)
    ((hφ'c.mono (by rw [huI])).intervalIntegrable)
  rw [h1, h2]
  simp only [hcos1, hsin0, Complex.ofReal_one, one_mul, zero_mul, neg_zero, Complex.ofReal_zero,
    sub_zero, zero_sub]
  have hφi : IntervalIntegrable (fun t => (Real.cos (ω * t) : ℂ) * φ t) volume (A : ℝ) B :=
    ((Continuous.continuousOn (by fun_prop)).mul (hφc.mono (by rw [huI]))).intervalIntegrable
  have e : (fun x => (((-(Real.cos (ω * x) * ω * ω)) : ℝ) : ℂ) * φ x)
      = fun x => (-(ω * ω : ℝ) : ℂ) * ((Real.cos (ω * x) : ℂ) * φ x) := by
    funext x; push_cast; ring
  rw [e, intervalIntegral.integral_const_mul]
  rw [hω]
  push_cast
  ring

/-! ## The tail of the cosine series -/

theorem ofReal_cos_mul_cexp (θ ψ : ℝ) :
    (Real.cos θ : ℂ) * Complex.exp ((ψ : ℂ) * I)
      = (Complex.exp (((ψ + θ : ℝ) : ℂ) * I) + Complex.exp (((ψ - θ : ℝ) : ℂ) * I)) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  rw [add_div, add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, ← Complex.exp_add,
    ← Complex.exp_add]
  push_cast
  ring_nf

/-- The `f′²`-weighted dual integral off resonance: phase derivative `2π(f′ ± n)` with `|f′| ≤ K′ < n`
gives `7K′²/(2π(n − K′))`. -/
theorem norm_integral_sq_deriv_mul_cexp_le {f f' f'' : ℝ → ℝ} {a b K' n σ : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 ≤ f'' x)
    (hK' : ∀ x ∈ Icc a b, |f' x| ≤ K') (hn : K' < n) (hσ : σ = 1 ∨ σ = -1) :
    ‖∫ t in a..b, ((f' t ^ 2 : ℝ) : ℂ)
        * Complex.exp (((2 * Real.pi * (f t + σ * n * t) : ℝ) : ℂ) * I)‖
      ≤ 7 * K' ^ 2 / (2 * Real.pi * (n - K')) := by
  have hK'0 : 0 ≤ K' := (abs_nonneg _).trans (hK' a ⟨le_rfl, hab⟩)
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hf'c : ContinuousOn f' (Icc a b) := fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hlam : 0 < 2 * Real.pi * (n - K') := by
    have := Real.pi_pos; nlinarith
  have hsq : ∀ x ∈ Icc a b, f' x ^ 2 ≤ K' ^ 2 := fun x hx => by
    have := hK' x hx
    nlinarith [abs_nonneg (f' x), sq_abs (f' x)]
  have h := GaloisForLFunctions.HTGeometry.norm_integral_mul_exp_le_of_monotone_phase
    (g := fun t => ((f' t ^ 2 : ℝ) : ℂ)) (g' := fun t => ((2 * f' t * f'' t : ℝ) : ℂ))
    (Θ := fun t => 2 * Real.pi * (f t + σ * n * t)) (Θ' := fun t => 2 * Real.pi * (f' t + σ * n))
    (Θ'' := fun t => 2 * Real.pi * f'' t) (G := K' ^ 2) (V := 4 * K' ^ 2) hab hlam
    (fun x hx => ((hf' x hx).pow 2).ofReal_comp.congr_deriv (by push_cast; ring))
    ((Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_const.mul hf'c).mul hf''c)))
    (fun x hx => (((hf x hx).add ((hasDerivAt_id' x).const_mul (σ * n))).const_mul
      (2 * Real.pi)).congr_deriv (by ring))
    (fun x hx => (((hf' x hx).add_const (σ * n)).const_mul (2 * Real.pi)))
    (continuousOn_const.mul hf''c)
    (fun x hx => mul_nonneg (by positivity) (hpos x hx))
    (fun x hx => by
      have hx' := abs_le.mp (hK' x hx)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rcases hσ with rfl | rfl
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith)
    (fun x hx => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsq x hx)
    (by
      have hint1 : IntervalIntegrable (fun x => ‖((2 * f' x * f'' x : ℝ) : ℂ)‖) volume a b := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hab]
        exact (Complex.continuous_ofReal.comp_continuousOn
          ((continuousOn_const.mul hf'c).mul hf''c)).norm
      have hint2 : IntervalIntegrable (fun x => 2 * K' * f'' x) volume a b := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hab]
        exact continuousOn_const.mul hf''c
      have hmono := intervalIntegral.integral_mono_on hab hint1 hint2 (fun x hx => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (hpos x hx), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := hK' x hx
        nlinarith [hpos x hx, abs_nonneg (f' x)])
      have hftc : ∫ x in a..b, 2 * K' * f'' x = 2 * K' * (f' b - f' a) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun x hx => hf' x (by rwa [uIcc_of_le hab] at hx))
            ((hf''c.mono (by rw [uIcc_of_le hab])).intervalIntegrable)]
      have hb' := abs_le.mp (hK' b hbI)
      have ha' := abs_le.mp (hK' a haI)
      rw [hftc] at hmono
      nlinarith)
  have hga : ‖((f' a ^ 2 : ℝ) : ℂ)‖ ≤ K' ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsq a haI
  have hgb : ‖((f' b ^ 2 : ℝ) : ℂ)‖ ≤ K' ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsq b hbI
  refine h.trans ?_
  rw [div_le_div_iff_of_pos_right hlam]
  linarith

/-- **The tail term.**  For `φ = e(f)` with `f″ ≥ 0`, `|f′| ≤ K′ < n`,
`‖∫ cos(2πnt) φ″‖ ≤ 4πK′ + 14πK′²/(n − K′)`. -/
theorem norm_integral_cos_mul_second_deriv_le {f f' f'' : ℝ → ℝ} {a b K' n : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 ≤ f'' x)
    (hK' : ∀ x ∈ Icc a b, |f' x| ≤ K') (hn : K' < n) :
    ‖∫ t in a..b, (Real.cos (2 * Real.pi * n * t) : ℂ)
        * ((((2 * Real.pi * f'' t : ℝ) : ℂ) * I - ((4 * Real.pi ^ 2 * f' t ^ 2 : ℝ) : ℂ))
          * Complex.exp (((2 * Real.pi * f t : ℝ) : ℂ) * I))‖
      ≤ 4 * Real.pi * K' + 14 * Real.pi * K' ^ 2 / (n - K') := by
  have hK'0 : 0 ≤ K' := (abs_nonneg _).trans (hK' a ⟨le_rfl, hab⟩)
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have huI : uIcc a b = Icc a b := uIcc_of_le hab
  have hfc : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hf'c : ContinuousOn f' (Icc a b) := fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hφc : ContinuousOn (fun t => Complex.exp (((2 * Real.pi * f t : ℝ) : ℂ) * I)) (Icc a b) :=
    ((Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hfc)).mul
      continuousOn_const).cexp
  have hcos : Continuous (fun t : ℝ => (Real.cos (2 * Real.pi * n * t) : ℂ)) := by fun_prop
  -- split the integrand
  set φ := fun t => Complex.exp (((2 * Real.pi * f t : ℝ) : ℂ) * I) with hφ
  have hsplit : (fun t => (Real.cos (2 * Real.pi * n * t) : ℂ)
        * ((((2 * Real.pi * f'' t : ℝ) : ℂ) * I - ((4 * Real.pi ^ 2 * f' t ^ 2 : ℝ) : ℂ)) * φ t))
      = fun t => (Real.cos (2 * Real.pi * n * t) : ℂ) * (((2 * Real.pi * f'' t : ℝ) : ℂ) * I * φ t)
          - ((2 * Real.pi ^ 2 : ℝ) : ℂ) * ((((f' t ^ 2 : ℝ) : ℂ)
              * Complex.exp (((2 * Real.pi * (f t + 1 * n * t)) : ℝ) * I))
            + (((f' t ^ 2 : ℝ) : ℂ)
              * Complex.exp (((2 * Real.pi * (f t + (-1) * n * t)) : ℝ) * I))) := by
    funext t
    have e := ofReal_cos_mul_cexp (2 * Real.pi * n * t) (2 * Real.pi * f t)
    have e1 : (((2 * Real.pi * (f t + 1 * n * t)) : ℝ) : ℂ)
        = (((2 * Real.pi * f t + 2 * Real.pi * n * t) : ℝ) : ℂ) := by push_cast; ring
    have e2 : (((2 * Real.pi * (f t + (-1) * n * t)) : ℝ) : ℂ)
        = (((2 * Real.pi * f t - 2 * Real.pi * n * t) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2]
    have : (Real.cos (2 * Real.pi * n * t) : ℂ) * φ t
        = (Complex.exp (((2 * Real.pi * f t + 2 * Real.pi * n * t : ℝ) : ℂ) * I)
          + Complex.exp (((2 * Real.pi * f t - 2 * Real.pi * n * t : ℝ) : ℂ) * I)) / 2 := e
    calc (Real.cos (2 * Real.pi * n * t) : ℂ)
          * ((((2 * Real.pi * f'' t : ℝ) : ℂ) * I - ((4 * Real.pi ^ 2 * f' t ^ 2 : ℝ) : ℂ)) * φ t)
        = (Real.cos (2 * Real.pi * n * t) : ℂ) * (((2 * Real.pi * f'' t : ℝ) : ℂ) * I * φ t)
          - ((4 * Real.pi ^ 2 * f' t ^ 2 : ℝ) : ℂ) * ((Real.cos (2 * Real.pi * n * t) : ℂ) * φ t) := by
          ring
      _ = _ := by rw [this]; push_cast; ring
  rw [hsplit]
  have hi1 : IntervalIntegrable (fun t => (Real.cos (2 * Real.pi * n * t) : ℂ)
      * (((2 * Real.pi * f'' t : ℝ) : ℂ) * I * φ t)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huI]
    exact hcos.continuousOn.mul (((Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.mul hf''c)).mul continuousOn_const).mul hφc)
  have hcontE : ∀ σ : ℝ, ContinuousOn (fun t => ((f' t ^ 2 : ℝ) : ℂ)
      * Complex.exp (((2 * Real.pi * (f t + σ * n * t)) : ℝ) * I)) (Icc a b) := fun σ =>
    (Complex.continuous_ofReal.comp_continuousOn (hf'c.pow 2)).mul
      ((Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
        (hfc.add (continuousOn_const.mul continuousOn_id)))).mul continuousOn_const).cexp
  have hiE : ∀ σ : ℝ, IntervalIntegrable (fun t => ((f' t ^ 2 : ℝ) : ℂ)
      * Complex.exp (((2 * Real.pi * (f t + σ * n * t)) : ℝ) * I)) volume a b := fun σ =>
    (by rw [huI]; exact hcontE σ : ContinuousOn _ (uIcc a b)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => ((2 * Real.pi ^ 2 : ℝ) : ℂ) * ((((f' t ^ 2 : ℝ) : ℂ)
      * Complex.exp (((2 * Real.pi * (f t + 1 * n * t)) : ℝ) * I))
      + (((f' t ^ 2 : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * (f t + (-1) * n * t)) : ℝ) * I))))
      volume a b := ((hiE 1).add (hiE (-1))).const_mul _
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hiE 1) (hiE (-1))]
  -- the `f″` part has total mass `2π(f′(b) − f′(a)) ≤ 4πK′`
  have hX : ‖∫ t in a..b, (Real.cos (2 * Real.pi * n * t) : ℂ)
      * (((2 * Real.pi * f'' t : ℝ) : ℂ) * I * φ t)‖ ≤ 4 * Real.pi * K' := by
    have hgi : IntervalIntegrable (fun t => 2 * Real.pi * f'' t) volume a b :=
      (by rw [huI]; exact continuousOn_const.mul hf''c : ContinuousOn _ (uIcc a b)).intervalIntegrable
    have hle := intervalIntegral.norm_integral_le_of_norm_le hab
      (f := fun t => (Real.cos (2 * Real.pi * n * t) : ℂ)
        * (((2 * Real.pi * f'' t : ℝ) : ℂ) * I * φ t))
      (g := fun t => 2 * Real.pi * f'' t)
      (Filter.Eventually.of_forall fun t ht => by
        have htI : t ∈ Icc a b := Ioc_subset_Icc_self ht
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
          hφ, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one,
          abs_of_nonneg (mul_nonneg (by positivity) (hpos t htI))]
        have := Real.abs_cos_le_one (2 * Real.pi * n * t)
        have h0 : 0 ≤ 2 * Real.pi * f'' t := mul_nonneg (by positivity) (hpos t htI)
        nlinarith) hgi
    have hftc : ∫ t in a..b, 2 * Real.pi * f'' t = 2 * Real.pi * (f' b - f' a) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => hf' x (by rwa [huI] at hx))
          ((hf''c.mono (by rw [huI])).intervalIntegrable)]
    rw [hftc] at hle
    have hb' := abs_le.mp (hK' b hbI)
    have ha' := abs_le.mp (hK' a haI)
    refine hle.trans ?_
    have := Real.pi_pos
    nlinarith
  have hP := norm_integral_sq_deriv_mul_cexp_le hab hf hf' hf''c hpos hK' hn (σ := 1) (Or.inl rfl)
  have hM := norm_integral_sq_deriv_mul_cexp_le hab hf hf' hf''c hpos hK' hn (σ := -1)
    (Or.inr rfl)
  have hc : ‖((2 * Real.pi ^ 2 : ℝ) : ℂ)‖ = 2 * Real.pi ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hnK : 0 < n - K' := by linarith
  have hfin : 2 * Real.pi ^ 2 * (7 * K' ^ 2 / (2 * Real.pi * (n - K'))
      + 7 * K' ^ 2 / (2 * Real.pi * (n - K'))) = 14 * Real.pi * K' ^ 2 / (n - K') := by
    field_simp
    ring
  calc _ ≤ ‖∫ t in a..b, (Real.cos (2 * Real.pi * n * t) : ℂ)
          * (((2 * Real.pi * f'' t : ℝ) : ℂ) * I * φ t)‖
        + ‖((2 * Real.pi ^ 2 : ℝ) : ℂ)‖ * (‖∫ t in a..b, ((f' t ^ 2 : ℝ) : ℂ)
            * Complex.exp (((2 * Real.pi * (f t + 1 * n * t)) : ℝ) * I)‖
          + ‖∫ t in a..b, ((f' t ^ 2 : ℝ) : ℂ)
            * Complex.exp (((2 * Real.pi * (f t + (-1) * n * t)) : ℝ) * I)‖) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
        gcongr
        exact norm_add_le _ _
    _ ≤ 4 * Real.pi * K' + 2 * Real.pi ^ 2 * (7 * K' ^ 2 / (2 * Real.pi * (n - K'))
          + 7 * K' ^ 2 / (2 * Real.pi * (n - K'))) := by
        rw [hc]
        gcongr
    _ = 4 * Real.pi * K' + 14 * Real.pi * K' ^ 2 / (n - K') := by rw [hfin]

/-! ## Truncated Poisson summation -/

theorem intervalIntegrable_sawPrimitive_mul_complex {a b : ℝ} {w : ℝ → ℂ}
    (hw : IntervalIntegrable w volume a b) :
    IntervalIntegrable (fun x => (GaloisForLFunctions.RHTower.sawPrimitive x : ℂ) * w x)
      volume a b := by
  have hm : AEStronglyMeasurable (fun x => (GaloisForLFunctions.RHTower.sawPrimitive x : ℂ))
      volume := (Complex.measurable_ofReal.comp
        GaloisForLFunctions.RHTower.measurable_sawPrimitive).aestronglyMeasurable
  have hb : ∀ᵐ x ∂volume, ‖(GaloisForLFunctions.RHTower.sawPrimitive x : ℂ)‖ ≤ 1 / 8 :=
    Filter.Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact GaloisForLFunctions.RHTower.abs_sawPrimitive_le x
  exact ⟨hw.1.bdd_mul (c := 1 / 8) hm.restrict (ae_restrict_of_ae hb),
    hw.2.bdd_mul (c := 1 / 8) hm.restrict (ae_restrict_of_ae hb)⟩

/-- `2∫ cos(2πνt) e(f) = ∫ e(f + νt) + ∫ e(f − νt)`. -/
theorem two_mul_integral_cos_mul_cexp {f : ℝ → ℝ} {a b ν : ℝ} (hf : ContinuousOn f (uIcc a b)) :
    2 * ∫ t in a..b, (Real.cos (2 * Real.pi * ν * t) : ℂ)
        * Complex.exp (((2 * Real.pi * f t : ℝ) : ℂ) * I)
      = (∫ t in a..b, Complex.exp (((2 * Real.pi * (f t + ν * t) : ℝ) : ℂ) * I))
        + ∫ t in a..b, Complex.exp (((2 * Real.pi * (f t - ν * t) : ℝ) : ℂ) * I) := by
  have hc : ∀ σ : ℝ, IntervalIntegrable
      (fun t => Complex.exp (((2 * Real.pi * (f t + σ * ν * t) : ℝ) : ℂ) * I)) volume a b :=
    fun σ => (((Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
      (hf.add (continuousOn_const.mul continuousOn_id)))).mul
        continuousOn_const).cexp).intervalIntegrable
  have e : (fun t => (Real.cos (2 * Real.pi * ν * t) : ℂ)
        * Complex.exp (((2 * Real.pi * f t : ℝ) : ℂ) * I))
      = fun t => (Complex.exp (((2 * Real.pi * (f t + 1 * ν * t) : ℝ) : ℂ) * I)
          + Complex.exp (((2 * Real.pi * (f t + (-1) * ν * t) : ℝ) : ℂ) * I)) / 2 := by
    funext t
    rw [ofReal_cos_mul_cexp]
    have h1 : 2 * Real.pi * f t + 2 * Real.pi * ν * t = 2 * Real.pi * (f t + 1 * ν * t) := by
      ring
    have h2 : 2 * Real.pi * f t - 2 * Real.pi * ν * t = 2 * Real.pi * (f t + (-1) * ν * t) := by
      ring
    rw [h1, h2]
  have e1 : (fun t => Complex.exp (((2 * Real.pi * (f t + ν * t) : ℝ) : ℂ) * I))
      = fun t => Complex.exp (((2 * Real.pi * (f t + 1 * ν * t) : ℝ) : ℂ) * I) := by
    funext t; rw [one_mul]
  have e2 : (fun t => Complex.exp (((2 * Real.pi * (f t - ν * t) : ℝ) : ℂ) * I))
      = fun t => Complex.exp (((2 * Real.pi * (f t + (-1) * ν * t) : ℝ) : ℂ) * I) := by
    funext t; congr 3; ring
  rw [e, e1, e2, intervalIntegral.integral_div, intervalIntegral.integral_add (hc 1) (hc (-1))]
  ring

/-- **Truncated Poisson summation.**  For `f″ ≥ 0`, `|f′| ≤ K′` on `[A, B]` and an integer
`K ≥ max(1, 2K′)`, the exponential sum `Σ_{A<m≤B} e(f(m))` is the sum of the `2K + 1` dual integrals
`∫_A^B e(f(t) − νt) dt`, `|ν| ≤ K`, up to an error of norm at most `5`. -/
theorem norm_sum_sub_truncatedPoisson_le {f f' f'' : ℝ → ℝ} {A B : ℤ} (hAB : A ≤ B) {K' : ℝ}
    {K : ℕ}
    (hf : ∀ x ∈ Icc (A : ℝ) B, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (A : ℝ) B, HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Icc (A : ℝ) B)) (hpos : ∀ x ∈ Icc (A : ℝ) B, 0 ≤ f'' x)
    (hK' : ∀ x ∈ Icc (A : ℝ) B, |f' x| ≤ K') (hK : 2 * K' ≤ K) (hK1 : 1 ≤ K) :
    ‖(∑ m ∈ Finset.Ioc A B, Complex.exp (((2 * Real.pi * f m : ℝ) : ℂ) * I))
        - ((∫ t in (A : ℝ)..B, Complex.exp (((2 * Real.pi * f t : ℝ) : ℂ) * I))
          + ∑ n ∈ Finset.range K,
              ((∫ t in (A : ℝ)..B,
                  Complex.exp (((2 * Real.pi * (f t + ((n : ℝ) + 1) * t) : ℝ) : ℂ) * I))
                + ∫ t in (A : ℝ)..B,
                  Complex.exp (((2 * Real.pi * (f t - ((n : ℝ) + 1) * t) : ℝ) : ℂ) * I)))‖
      ≤ 5 := by
  have hab : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have huI : uIcc (A : ℝ) B = Icc (A : ℝ) B := uIcc_of_le hab
  have haI : (A : ℝ) ∈ Icc (A : ℝ) B := ⟨le_rfl, hab⟩
  have hbI : (B : ℝ) ∈ Icc (A : ℝ) B := ⟨hab, le_rfl⟩
  have hK'0 : 0 ≤ K' := (abs_nonneg _).trans (hK' A haI)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  have hpi := Real.pi_pos
  have hfc : ContinuousOn f (Icc (A : ℝ) B) := fun x hx =>
    (hf x hx).continuousAt.continuousWithinAt
  have hf'c : ContinuousOn f' (Icc (A : ℝ) B) := fun x hx =>
    (hf' x hx).continuousAt.continuousWithinAt
  set φ : ℝ → ℂ := fun t => Complex.exp (((2 * Real.pi * f t : ℝ) : ℂ) * I) with hφ
  set φ' : ℝ → ℂ := fun t => ((2 * Real.pi * f' t : ℝ) : ℂ) * I * φ t with hφ'
  set φ'' : ℝ → ℂ := fun t => (((2 * Real.pi * f'' t : ℝ) : ℂ) * I
      - ((4 * Real.pi ^ 2 * f' t ^ 2 : ℝ) : ℂ)) * φ t with hφ''
  have hφc : ContinuousOn φ (Icc (A : ℝ) B) :=
    ((Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hfc)).mul
      continuousOn_const).cexp
  have hd1 : ∀ x ∈ Icc (A : ℝ) B, HasDerivAt φ (φ' x) x := fun x hx => by
    have h := ((((hf x hx).const_mul (2 * Real.pi)).ofReal_comp).mul_const I).cexp
    refine h.congr_deriv ?_
    simp only [hφ, hφ']
    push_cast
    ring
  have hd2 : ∀ x ∈ Icc (A : ℝ) B, HasDerivAt φ' (φ'' x) x := fun x hx => by
    have h := ((((hf' x hx).const_mul (2 * Real.pi)).ofReal_comp).mul_const I).mul (hd1 x hx)
    refine h.congr_deriv ?_
    simp only [hφ, hφ', hφ'']
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * (f' x : ℂ)) ^ 2
      * Complex.exp (2 * (Real.pi : ℂ) * (f x : ℂ) * I) * Complex.I_mul_I
  have hc2 : ContinuousOn φ'' (Icc (A : ℝ) B) :=
    (((Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hf''c)).mul
      continuousOn_const).sub (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.mul (hf'c.pow 2)))).mul hφc
  have hφ''i : IntervalIntegrable φ'' volume (A : ℝ) B :=
    (hc2.mono (by rw [huI])).intervalIntegrable
  have hEM := sum_Ioc_eq_integral_add_sawPrimitive hAB hd1 hd2 hc2
  -- the Fourier side
  have hFTC : (∫ t in (A : ℝ)..B, φ'' t) = φ' B - φ' A :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd2 x (by rwa [huI] at hx)) hφ''i
  set Δ := φ' B - φ' A with hΔ
  set Q := ∫ t in (A : ℝ)..B, (GaloisForLFunctions.RHTower.sawPrimitive t : ℂ) * φ'' t with hQ
  set c : ℕ → ℂ := fun n => (∫ t in (A : ℝ)..B, (Real.cos (2 * Real.pi * n * t) : ℂ) * φ'' t)
    / (((n : ℝ) ^ (2 : ℕ) : ℝ) : ℂ) with hc
  have hS : HasSum c (∫ t in (A : ℝ)..B, (((2 * Real.pi ^ (2 : ℕ) *
      (1 / 12 - GaloisForLFunctions.RHTower.sawPrimitive t)) : ℝ) : ℂ) * φ'' t) :=
    hasSum_integral_cos_mul_div_sq hab hc2
  have hZ : HasSum (fun n : ℕ => Δ / (((n : ℝ) ^ (2 : ℕ) : ℝ) : ℂ))
      (Δ * (((Real.pi ^ 2 / 6) : ℝ) : ℂ)) := by
    have := (Complex.hasSum_ofReal.mpr hasSum_zeta_two).mul_left Δ
    refine this.congr_fun fun n => ?_
    push_cast
    ring
  have hval : (∫ t in (A : ℝ)..B, (((2 * Real.pi ^ (2 : ℕ) *
      (1 / 12 - GaloisForLFunctions.RHTower.sawPrimitive t)) : ℝ) : ℂ) * φ'' t)
        - Δ * (((Real.pi ^ 2 / 6) : ℝ) : ℂ) = -(((2 * Real.pi ^ 2 : ℝ) : ℂ)) * Q := by
    have e : (fun t => (((2 * Real.pi ^ (2 : ℕ) *
        (1 / 12 - GaloisForLFunctions.RHTower.sawPrimitive t)) : ℝ) : ℂ) * φ'' t)
        = fun t => (((Real.pi ^ 2 / 6) : ℝ) : ℂ) * φ'' t
          - ((2 * Real.pi ^ 2 : ℝ) : ℂ)
            * ((GaloisForLFunctions.RHTower.sawPrimitive t : ℂ) * φ'' t) := by
      funext t; push_cast; ring
    rw [e, intervalIntegral.integral_sub (hφ''i.const_mul _)
      ((intervalIntegrable_sawPrimitive_mul_complex hφ''i).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hFTC]
    ring
  set d : ℕ → ℂ := fun n => c n - Δ / (((n : ℝ) ^ (2 : ℕ) : ℝ) : ℂ) with hd
  have hD : HasSum d (-(((2 * Real.pi ^ 2 : ℝ) : ℂ)) * Q) := by
    rw [← hval]; exact hS.sub hZ
  set J : ℕ → ℂ := fun n => ∫ t in (A : ℝ)..B, (Real.cos (2 * Real.pi * n * t) : ℂ) * φ t with hJ
  have hdsucc : ∀ m : ℕ, d (m + 1) = -(((4 * Real.pi ^ 2 : ℝ) : ℂ)) * J (m + 1) := by
    intro m
    have h3 := integral_cos_mul_second_deriv hAB (m + 1) hd1 hd2 hc2
    simp only [hd, hc, hJ]
    rw [h3]
    have hne : (((((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by positivity
      exact_mod_cast this.ne'
    field_simp
    push_cast
    ring
  have hd0 : d 0 = 0 := by simp [hd, hc]
  -- the tail of the series
  set D₀ : ℝ := 8 * Real.pi * K' + 28 * Real.pi * K' ^ 2 / K with hD₀
  have hφ'n : ∀ x ∈ Icc (A : ℝ) B, ‖φ' x‖ ≤ 2 * Real.pi * K' := fun x hx => by
    simp only [hφ', hφ]
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, mul_one, mul_one, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left (hK' x hx) (by positivity)
  have hΔn : ‖Δ‖ ≤ 4 * Real.pi * K' := by
    have := norm_sub_le (φ' B) (φ' A)
    linarith [hφ'n B hbI, hφ'n A haI]
  have htail : ∀ n : ℕ, K + 1 ≤ n → ‖d n‖ ≤ D₀ * (((n : ℝ) ^ 2)⁻¹) := by
    intro n hn
    have hnR : (K : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hnK : K' < n := by linarith
    have hT := norm_integral_cos_mul_second_deriv_le hab hf hf' hf''c hpos hK' hnK
    have hgap : 14 * Real.pi * K' ^ 2 / ((n : ℝ) - K') ≤ 28 * Real.pi * K' ^ 2 / K := by
      rw [div_le_div_iff₀ (by linarith) hKpos]
      have : (0 : ℝ) ≤ Real.pi * K' ^ 2 := by positivity
      nlinarith
    have hcn : ‖c n‖ ≤ (4 * Real.pi * K' + 28 * Real.pi * K' ^ 2 / K) * (((n : ℝ) ^ 2)⁻¹) := by
      simp only [hc]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hT.trans (by linarith)) (by positivity)
    have hΔ' : ‖Δ / (((n : ℝ) ^ (2 : ℕ) : ℝ) : ℂ)‖ ≤ 4 * Real.pi * K' * (((n : ℝ) ^ 2)⁻¹) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hΔn (by positivity)
    calc ‖d n‖ ≤ ‖c n‖ + ‖Δ / (((n : ℝ) ^ (2 : ℕ) : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hcn hΔ'
      _ = D₀ * (((n : ℝ) ^ 2)⁻¹) := by rw [hD₀]; ring
  have hD₀nn : 0 ≤ D₀ := by positivity
  have hseg : ∀ M : ℕ, K + 1 ≤ M →
      ‖(∑ n ∈ Finset.range M, d n) - ∑ n ∈ Finset.range (K + 1), d n‖ ≤ D₀ * (2 / (K + 1)) := by
    intro M hM
    rw [← Finset.sum_Ico_eq_sub d hM]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun n hn => htail n (Finset.mem_Ico.mp hn).1).trans ?_
    rw [← Finset.mul_sum, Finset.Ico_add_one_left_eq_Ioo]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast sum_Ioo_inv_sq_le K M) hD₀nn
  have hlim : ‖-(((2 * Real.pi ^ 2 : ℝ) : ℂ)) * Q - ∑ n ∈ Finset.range (K + 1), d n‖
      ≤ D₀ * (2 / (K + 1)) :=
    le_of_tendsto ((hD.tendsto_sum_nat.sub_const _).norm)
      (Filter.eventually_atTop.mpr ⟨K + 1, hseg⟩)
  -- the head of the series is the dual integrals
  have hhead : ∑ n ∈ Finset.range (K + 1), d n
      = -(((2 * Real.pi ^ 2 : ℝ) : ℂ)) * ∑ n ∈ Finset.range K,
          ((∫ t in (A : ℝ)..B,
              Complex.exp (((2 * Real.pi * (f t + ((n : ℝ) + 1) * t) : ℝ) : ℂ) * I))
            + ∫ t in (A : ℝ)..B,
              Complex.exp (((2 * Real.pi * (f t - ((n : ℝ) + 1) * t) : ℝ) : ℂ) * I)) := by
    rw [Finset.sum_range_succ', hd0, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hdsucc n, ← two_mul_integral_cos_mul_cexp (hfc.mono (by rw [huI]))]
    simp only [hJ, hφ]
    push_cast
    ring
  set W := ∑ n ∈ Finset.range K,
          ((∫ t in (A : ℝ)..B,
              Complex.exp (((2 * Real.pi * (f t + ((n : ℝ) + 1) * t) : ℝ) : ℂ) * I))
            + ∫ t in (A : ℝ)..B,
              Complex.exp (((2 * Real.pi * (f t - ((n : ℝ) + 1) * t) : ℝ) : ℂ) * I)) with hW
  rw [hhead] at hlim
  have hc2pi : ‖((2 * Real.pi ^ 2 : ℝ) : ℂ)‖ = 2 * Real.pi ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hQW : ‖Q - W‖ ≤ D₀ * (2 / (K + 1)) / (2 * Real.pi ^ 2) := by
    have e : -(((2 * Real.pi ^ 2 : ℝ) : ℂ)) * Q - -(((2 * Real.pi ^ 2 : ℝ) : ℂ)) * W
        = -(((2 * Real.pi ^ 2 : ℝ) : ℂ)) * (Q - W) := by ring
    rw [e, norm_mul, norm_neg, hc2pi] at hlim
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hbd : ‖(φ B - φ A) / 2‖ ≤ 1 := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have := norm_sub_le (φ B) (φ A)
    have h1 : ‖φ B‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have h2 : ‖φ A‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    linarith
  have hnum : D₀ * (2 / (K + 1)) / (2 * Real.pi ^ 2) ≤ 4 := by
    have hD₀le : D₀ ≤ 11 * Real.pi * K := by
      rw [hD₀]
      have h1 : 8 * Real.pi * K' ≤ 4 * Real.pi * K := by nlinarith
      have h2 : 28 * Real.pi * K' ^ 2 / K ≤ 7 * Real.pi * K := by
        rw [div_le_iff₀ hKpos]
        have : K' ^ 2 ≤ (K : ℝ) ^ 2 / 4 := by nlinarith
        nlinarith
      linarith
    rw [div_le_iff₀ (by positivity)]
    have hK1' : (K : ℝ) / (K + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h3 : D₀ * (2 / (K + 1)) ≤ 22 * Real.pi * (K / (K + 1)) := by
      have : D₀ * (2 / (K + 1)) ≤ 11 * Real.pi * K * (2 / (K + 1)) :=
        mul_le_mul_of_nonneg_right hD₀le (by positivity)
      calc _ ≤ 11 * Real.pi * K * (2 / (K + 1)) := this
        _ = 22 * Real.pi * (K / (K + 1)) := by ring
    have h4 : 22 * Real.pi * (K / (K + 1)) ≤ 22 * Real.pi := by
      have := mul_le_mul_of_nonneg_left hK1' (by positivity : (0 : ℝ) ≤ 22 * Real.pi)
      linarith
    have h5 : 22 * Real.pi ≤ 4 * (2 * Real.pi ^ 2) := by nlinarith [Real.pi_gt_three]
    linarith
  have hsum : (∑ m ∈ Finset.Ioc A B, Complex.exp (((2 * Real.pi * f m : ℝ) : ℂ) * I))
      = ∑ m ∈ Finset.Ioc A B, φ m := rfl
  rw [hsum, hEM]
  have e : (∫ x in (A : ℝ)..B, φ x) + (φ B - φ A) / 2 + Q
      - ((∫ t in (A : ℝ)..B, φ t) + W) = (φ B - φ A) / 2 + (Q - W) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith

end

end RHTower
