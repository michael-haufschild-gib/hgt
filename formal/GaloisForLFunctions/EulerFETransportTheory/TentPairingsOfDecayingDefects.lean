import GaloisForLFunctions.ExactEventTheory.TentRecurrenceOfIntegrableDefects

/-!
# Tent pairings of polynomially bounded defects

Let `ν = ν_B` satisfy the defective theta law with a measurable polynomially bounded defect `g`,
and let `T_ε(h, y) = ∫_{-1}^{1} h (1 - |s|) Re J_g(h ε + i(y + h s)) ds` be the defect paired with
the tent of width `h` centred at `y`.

* `tendsto_tentDefect` — for `0 < h ≤ 1 < y/h`, `T_ε(h, y) → tentAtomMass − tentRecurrentPart` as
  `ε → 0⁺`: the tent identity holds with the error defined as the limit, with no size assumption on
  `g`.
* `integral_tent_mul_defectLaplace` — **double integration by parts.**  With
  `G(t) = g(t) / ((1/2 + 2it)(3/2 + 2it))` and `τ_σ = h(ε + i(n + σ))`,
  `∫_{-1}^{1} (1 - |s|) J_g(τ_s) ds = -h⁻² (τ₁² J_G(τ₁) - 2 τ₀² J_G(τ₀) + τ₋₁² J_G(τ₋₁))`.
  Each kernel is `c(t) τ^{-1/2 + 2it}`, the second derivative of `τ^{3/2 + 2it}` up to the factor
  `(ih)² (1/2 + 2it)(3/2 + 2it)`, and the tent turns a second derivative into a second difference.
-/

open Complex MeasureTheory Filter Topology Set Function
open RHTower.HamburgerStability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ExactEventTheory
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-! ## The tent identity for polynomially bounded defects -/

/-- The tent-defect kernel of a measurable, polynomially bounded defect is continuous. -/
theorem continuous_tentDefectKernel_of_poly {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n : ℝ) :
    Continuous (tentDefectKernel g h n ε) := by
  have hc := (differentiableOn_defectLaplace hgm.aestronglyMeasurable hgb).continuousOn
  have hcu : ContinuousOn (fun s : ℝ => defectLaplace g
      ((h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I))) univ := by
    apply hc.comp (by fun_prop)
    intro s _
    simpa using mul_pos hh hε
  change Continuous fun s : ℝ => h * (1 - |s|) *
    (defectLaplace g ((h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I))).re
  exact (by fun_prop : Continuous fun s : ℝ => h * (1 - |s|)).mul
    (Complex.continuous_re.comp (continuousOn_univ.mp hcu))

/-- The scaled Laplace identity paired with a tent, for any polynomially bounded defect. -/
theorem tent_pairing_identity_of_poly {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -(β : ℂ) +
        (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h n ε : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hn : 1 ≤ n) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ u, (∫ s in (-1 : ℝ)..1, tentSeriesKernel h n ε s u) ∂ν =
      (∫ u, (∫ s in (-1 : ℝ)..1, tentDualKernel h n ε s u) ∂ν) +
        (∫ s in (-1 : ℝ)..1, tentPolarKernel h β n ε s) +
          ∫ s in (-1 : ℝ)..1, tentDefectKernel g h n ε s := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  have hS := integrable_tentSeriesKernel hsupp hmom hh hh1 hn hε hε1
  have hD := integrable_tentDualKernel hsupp hmom hh hε n
  have hDi : IntervalIntegrable (fun s : ℝ => ∫ u, tentDualKernel h n ε s u ∂ν) volume (-1) 1 :=
    intervalIntegrable_iff.mpr hD.integral_prod_left
  have hPi : IntervalIntegrable (tentPolarKernel h β n ε) volume (-1) 1 :=
    (continuous_tentPolarKernel h β n hε).intervalIntegrable (-1) 1
  have hJi : IntervalIntegrable (tentDefectKernel g h n ε) volume (-1) 1 :=
    (continuous_tentDefectKernel_of_poly hgm hgb hh hε n).intervalIntegrable (-1) 1
  have he : (∫ s in (-1 : ℝ)..1, ∫ u, tentSeriesKernel h n ε s u ∂ν) =
      (∫ s in (-1 : ℝ)..1, ∫ u, tentDualKernel h n ε s u ∂ν) +
        (∫ s in (-1 : ℝ)..1, tentPolarKernel h β n ε s) +
          ∫ s in (-1 : ℝ)..1, tentDefectKernel g h n ε s := by
    rw [intervalIntegral.integral_congr (fun s _ =>
      integral_tentSeriesKernel_eq_of_theta_defect hsupp hmom hgm hgb hθ hh hε n s),
      intervalIntegral.integral_add (hDi.add hPi) hJi,
      intervalIntegral.integral_add hDi hPi]
  rwa [intervalIntegral_integral_swap hS, intervalIntegral_integral_swap hD] at he

/-- The defect paired with the tent of width `h` centred at `y`. -/
def tentDefect (g : ℝ → ℂ) (h y ε : ℝ) : ℝ :=
  ∫ s in (-1 : ℝ)..1, tentDefectKernel g h (y / h) ε s

/-- **The tent identity.**  For a polynomially bounded defect the tent pairings converge to the
atomic mass minus the recurrent part. -/
theorem tendsto_tentDefect (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h y : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hy : h < y) :
    Tendsto (fun ε : ℝ => tentDefect g h y ε) (𝓝[>] 0)
      (𝓝 (tentAtomMass B.intNorm h y - tentRecurrentPart B.intNorm β h y)) := by
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp
    (integrable_rpow_beurlingSystemIntegerMeasure B hBsum)
  have hn : 1 < y / h := (lt_div_iff₀ hh).mpr (by simpa only [one_mul] using hy)
  have hlim := ((tendsto_integral_tentSeriesKernel hsupp hmom hh hh1 hn.le).sub
    (tendsto_integral_tentDualKernel hsupp hmom hh (y / h))).sub
      (tendsto_integral_tentPolarKernel h β hn.le)
  have hval : (1 / 2) * (∫ u, unitTent (y / h) (u / h) ∂beurlingSystemIntegerMeasure B) -
      h * (∫ u, Real.cos (2 * Real.pi * (h * u) * (y / h)) * tentFourierWeight h u
        ∂beurlingSystemIntegerMeasure B) - h * β =
      tentAtomMass B.intNorm h y - tentRecurrentPart B.intNorm β h y := by
    have he (u : ℝ) : 2 * Real.pi * (h * u) * (y / h) = 2 * Real.pi * u * y := by
      field_simp
    simp only [integral_beurlingSystemIntegerMeasure_eq_tsum, he]
    rw [tentRecurrentPart_eq B.intNorm_pos (summable_beurling_inv_sq B hBsum) hh]
    dsimp only [tentAtomMass]
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  have hid := tent_pairing_identity_of_poly hsupp hmom hgm hgb hθ hh hh1 hn.le hε.1 hε.2.le
  dsimp only [tentDefect]
  linarith

/-! ## Double integration by parts -/

/-- **A tent turns a second derivative into a second difference**:
`∫_{-1}^{1} (1 - |s|) φ''(s) ds = φ(1) - 2φ(0) + φ(-1)`. -/
theorem integral_tent_mul_deriv2 {φ φ₁ φ₂ : ℝ → ℂ} (h1 : ∀ s, HasDerivAt φ (φ₁ s) s)
    (h2 : ∀ s, HasDerivAt φ₁ (φ₂ s) s) (hc : Continuous φ₂) :
    ∫ s in (-1 : ℝ)..1, ((1 - |s| : ℝ) : ℂ) * φ₂ s = φ 1 - 2 * φ 0 + φ (-1) := by
  have hc1 : Continuous φ₁ := continuous_iff_continuousAt.mpr fun s => (h2 s).continuousAt
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => ((1 - |s| : ℝ) : ℂ) * φ₂ s) volume a b :=
    fun a b => (by fun_prop : Continuous fun s : ℝ => ((1 - |s| : ℝ) : ℂ)).mul hc
      |>.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-1) 0) (hint 0 1)]
  -- right half: `∫₀¹ (1 - s) φ₂ = -φ₁(0) + φ(1) - φ(0)`
  have hR : ∫ s in (0 : ℝ)..1, ((1 - |s| : ℝ) : ℂ) * φ₂ s = -φ₁ 0 + (φ 1 - φ 0) := by
    have hcongr : ∫ s in (0 : ℝ)..1, ((1 - |s| : ℝ) : ℂ) * φ₂ s =
        ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) * φ₂ s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le zero_le_one] at hs
      simp only [abs_of_nonneg hs.1]
      push_cast; ring
    rw [hcongr, intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun s : ℝ => 1 - (s : ℂ)) (u' := fun _ => -1)
      (fun s _ => by simpa using ((hasDerivAt_id (s : ℝ)).ofReal_comp).const_sub 1)
      (fun s _ => h2 s) (by simp) (hc.intervalIntegrable 0 1)]
    have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => h1 s)
      (hc1.intervalIntegrable 0 1)
    simp only [neg_one_mul, intervalIntegral.integral_neg, hF]
    push_cast
    ring
  -- left half: `∫_{-1}^0 (1 + s) φ₂ = φ₁(0) - (φ(0) - φ(-1))`
  have hL : ∫ s in (-1 : ℝ)..0, ((1 - |s| : ℝ) : ℂ) * φ₂ s = φ₁ 0 - (φ 0 - φ (-1)) := by
    have hcongr : ∫ s in (-1 : ℝ)..0, ((1 - |s| : ℝ) : ℂ) * φ₂ s =
        ∫ s in (-1 : ℝ)..0, (1 + (s : ℂ)) * φ₂ s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hs
      simp only [abs_of_nonpos hs.2]
      push_cast; ring
    rw [hcongr, intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun s : ℝ => 1 + (s : ℂ)) (u' := fun _ => 1)
      (fun s _ => by simpa using ((hasDerivAt_id (s : ℝ)).ofReal_comp).const_add 1)
      (fun s _ => h2 s) (by simp) (hc.intervalIntegrable (-1) 0)]
    have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => h1 s)
      (hc1.intervalIntegrable (-1) 0)
    simp only [one_mul, hF]
    push_cast
    ring
  rw [hL, hR]
  ring

/-- The point `h(ε + i(n + s))` above the tent. -/
def tentPt (h n ε s : ℝ) : ℂ := (h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)

@[simp] theorem tentPt_re (h n ε s : ℝ) : (tentPt h n ε s).re = h * ε := by simp [tentPt]

@[simp] theorem tentPt_im (h n ε s : ℝ) : (tentPt h n ε s).im = h * (n + s) := by simp [tentPt]

theorem continuous_tentPt (h n ε : ℝ) : Continuous (tentPt h n ε) := by
  unfold tentPt; fun_prop

theorem hasDerivAt_tentPt (h n ε s : ℝ) : HasDerivAt (tentPt h n ε) ((h : ℂ) * I) s := by
  have h1 : HasDerivAt (fun s : ℝ => ((n + s : ℝ) : ℂ)) 1 s := by
    simpa using ((hasDerivAt_id s).const_add n).ofReal_comp
  exact (((h1.mul_const I).const_add (ε : ℂ)).const_mul (h : ℂ)).congr_deriv (by ring)

theorem tentPt_mem_slitPlane {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n s : ℝ) :
    tentPt h n ε s ∈ slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [tentPt_re]; positivity))

theorem tentPt_ne_zero {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n s : ℝ) : tentPt h n ε s ≠ 0 :=
  slitPlane_ne_zero (tentPt_mem_slitPlane hh hε n s)

/-- **Second difference of a power along the tent**: for `(a + 2)(a + 1) ≠ 0`,
`∫_{-1}^{1} (1 - |s|) τ_s^a ds = (τ₁^{a+2} - 2τ₀^{a+2} + τ₋₁^{a+2}) / ((a + 2)(a + 1)(ih)²)`. -/
theorem integral_tent_mul_cpow {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n : ℝ) {a : ℂ}
    (ha : (a + 2) * (a + 1) ≠ 0) :
    ∫ s in (-1 : ℝ)..1, ((1 - |s| : ℝ) : ℂ) * tentPt h n ε s ^ a =
      (tentPt h n ε 1 ^ (a + 2) - 2 * tentPt h n ε 0 ^ (a + 2) +
        tentPt h n ε (-1) ^ (a + 2)) / ((a + 2) * (a + 1) * ((h : ℂ) * I) ^ 2) := by
  have hd : ∀ (c : ℂ) (s : ℝ), HasDerivAt (fun s => tentPt h n ε s ^ c)
      (c * tentPt h n ε s ^ (c - 1) * ((h : ℂ) * I)) s := fun c s =>
    (Complex.hasStrictDerivAt_cpow_const (tentPt_mem_slitPlane hh hε n s)).hasDerivAt.comp s
      (hasDerivAt_tentPt h n ε s)
  have h1 : ∀ s, HasDerivAt (fun s => tentPt h n ε s ^ (a + 2))
      ((a + 2) * tentPt h n ε s ^ (a + 1) * ((h : ℂ) * I)) s := by
    intro s
    have := hd (a + 2) s
    rwa [show a + 2 - 1 = a + 1 by ring] at this
  have h2 : ∀ s, HasDerivAt (fun s => (a + 2) * tentPt h n ε s ^ (a + 1) * ((h : ℂ) * I))
      ((a + 2) * (a + 1) * ((h : ℂ) * I) ^ 2 * tentPt h n ε s ^ a) s := by
    intro s
    have := ((hd (a + 1) s).const_mul (a + 2)).mul_const ((h : ℂ) * I)
    rw [show a + 1 - 1 = a by ring] at this
    exact this.congr_deriv (by ring)
  have hc : Continuous fun s => (a + 2) * (a + 1) * ((h : ℂ) * I) ^ 2 * tentPt h n ε s ^ a :=
    continuous_const.mul ((continuous_tentPt h n ε).cpow continuous_const
      fun s => tentPt_mem_slitPlane hh hε n s)
  have key := integral_tent_mul_deriv2 h1 h2 hc
  have hK : (a + 2) * (a + 1) * ((h : ℂ) * I) ^ 2 ≠ 0 :=
    mul_ne_zero ha (pow_ne_zero 2 (mul_ne_zero (by exact_mod_cast hh.ne') I_ne_zero))
  rw [eq_div_iff hK, ← key, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- The coefficient `c(t)` of the kernel `k(2t, τ) = c(t) τ^{-1/2 + 2it}`. -/
def kerCoeff (t : ℝ) : ℂ := gammaPair (2 * t) * (Real.pi : ℂ) ^ (-(1 - linePt (2 * t) / 2))

/-- The exponent `-1/2 + 2it` of the kernel `k(2t, τ)`. -/
def kerExp (t : ℝ) : ℂ := 1 + 2 * (-(1 - linePt (2 * t) / 2))

theorem kerExp_eq (t : ℝ) : kerExp t = -1 / 2 + 2 * t * I := by
  simp only [kerExp, linePt]; push_cast; ring

theorem pairKernel_eq_cpow (t : ℝ) {τ : ℂ} (hτ : 0 < τ.re) :
    pairKernel (2 * t) τ = kerCoeff t * τ ^ kerExp t := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  rw [← boundaryPairKernel_eq hτ, boundaryPairKernel, kerCoeff, kerExp,
    Complex.cpow_add _ _ hτ0, Complex.cpow_one]
  ring

theorem continuous_kerCoeff : Continuous kerCoeff := by
  unfold kerCoeff
  exact (continuous_gammaPair.comp (continuous_const.mul continuous_id)).mul
    (Continuous.const_cpow (by unfold linePt; fun_prop)
      (Or.inl (by exact_mod_cast Real.pi_ne_zero)))

theorem continuous_kerExp : Continuous kerExp := by
  unfold kerExp linePt; fun_prop

/-- `(1/2 + 2it)(3/2 + 2it)`, the factor gained by integrating `τ^{-1/2+2it}` twice. -/
def tentFactor (t : ℝ) : ℂ := (3 / 2 + 2 * t * I) * (1 / 2 + 2 * t * I)

theorem kerExp_factor (t : ℝ) : (kerExp t + 2) * (kerExp t + 1) = tentFactor t := by
  rw [kerExp_eq, tentFactor]; ring

theorem three_quarters_le_norm_tentFactor (t : ℝ) : 3 / 4 ≤ ‖tentFactor t‖ := by
  rw [tentFactor, norm_mul]
  have h1 : 3 / 2 ≤ ‖(3 / 2 : ℂ) + 2 * t * I‖ := by
    have := Complex.abs_re_le_norm ((3 / 2 : ℂ) + 2 * t * I)
    simp at this; norm_num at this ⊢; linarith
  have h2 : 1 / 2 ≤ ‖(1 / 2 : ℂ) + 2 * t * I‖ := by
    have := Complex.abs_re_le_norm ((1 / 2 : ℂ) + 2 * t * I)
    simp at this; norm_num at this ⊢; linarith
  nlinarith [norm_nonneg ((1 / 2 : ℂ) + 2 * t * I)]

theorem tentFactor_ne_zero (t : ℝ) : tentFactor t ≠ 0 := by
  intro h
  have := three_quarters_le_norm_tentFactor t
  rw [h, norm_zero] at this
  norm_num at this

theorem continuous_tentFactor : Continuous tentFactor := by
  unfold tentFactor; fun_prop

/-- The twice-integrated defect `G(t) = g(t) / ((3/2 + 2it)(1/2 + 2it))`. -/
def tentPrimitive (g : ℝ → ℂ) (t : ℝ) : ℂ := g t / tentFactor t

theorem measurable_tentPrimitive {g : ℝ → ℂ} (hgm : Measurable g) :
    Measurable (tentPrimitive g) :=
  hgm.div continuous_tentFactor.measurable

theorem norm_tentPrimitive_le (g : ℝ → ℂ) (t : ℝ) :
    ‖tentPrimitive g t‖ ≤ 4 / 3 * ‖g t‖ := by
  rw [tentPrimitive, norm_div, div_le_iff₀ (norm_pos_iff.mpr (tentFactor_ne_zero t))]
  have := three_quarters_le_norm_tentFactor t
  nlinarith [norm_nonneg (g t)]

/-- `τ² k(2t, τ) = c(t) τ^{3/2 + 2it}`. -/
theorem sq_mul_pairKernel (t : ℝ) {τ : ℂ} (hτ : 0 < τ.re) :
    τ ^ 2 * pairKernel (2 * t) τ = kerCoeff t * τ ^ (kerExp t + 2) := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  rw [pairKernel_eq_cpow t hτ, Complex.cpow_add _ _ hτ0,
    show (τ ^ (2 : ℂ)) = τ ^ (2 : ℕ) by exact_mod_cast Complex.cpow_natCast τ 2]
  ring

/-- Above the tent the kernel decays uniformly: for `|s| ≤ 1`,
`‖k(2t, τ_s)‖ ≤ 3 (hε)^{-1/2} e^{-2(hε/M)|t|}` with `M = hε + h(|n| + 1)`. -/
theorem norm_pairKernel_tentPt_le {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n t : ℝ) {s : ℝ}
    (hs : |s| ≤ 1) :
    ‖pairKernel (2 * t) (tentPt h n ε s)‖ ≤
      3 * (h * ε) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(2 * (h * ε / (h * ε + h * (|n| + 1))) * |t|)) := by
  set τ := tentPt h n ε s with hτ
  have hre : τ.re = h * ε := tentPt_re h n ε s
  have hre0 : 0 < τ.re := by rw [hre]; positivity
  have hb := norm_pairKernel_two_mul_le t hre0
  have hge : h * ε ≤ ‖τ‖ := hre ▸ Complex.re_le_norm τ
  have hle : ‖τ‖ ≤ h * ε + h * (|n| + 1) := by
    calc ‖τ‖ ≤ |τ.re| + |τ.im| := Complex.norm_le_abs_re_add_abs_im τ
      _ = h * ε + h * |n + s| := by
          rw [hre, hτ, tentPt_im, abs_of_pos (by positivity), abs_mul, abs_of_pos hh]
      _ ≤ h * ε + h * (|n| + 1) := by
          gcongr
          exact (abs_add_le n s).trans (by linarith)
  have hM : 0 < h * ε + h * (|n| + 1) := by positivity
  have hfrac : h * ε / (h * ε + h * (|n| + 1)) ≤ τ.re / ‖τ‖ := by
    rw [hre]
    exact div_le_div_of_nonneg_left (by positivity) (lt_of_lt_of_le (by positivity) hge) hle
  refine hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by positivity) hge (by norm_num)) (by norm_num))
    (Real.exp_le_exp.mpr ?_) (by positivity) (by positivity))
  nlinarith [abs_nonneg t]

/-- **Double integration by parts for the defect transform.**  With `G = tentPrimitive g`,
`∫_{-1}^{1} (1 - |s|) J_g(τ_s) ds = (τ₁² J_G(τ₁) - 2 τ₀² J_G(τ₀) + τ₋₁² J_G(τ₋₁)) / (ih)²`. -/
theorem integral_tent_mul_defectLaplace {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n : ℝ) :
    ∫ s in (-1 : ℝ)..1, ((1 - |s| : ℝ) : ℂ) * defectLaplace g (tentPt h n ε s) =
      (tentPt h n ε 1 ^ 2 * defectLaplace (tentPrimitive g) (tentPt h n ε 1) -
        2 * (tentPt h n ε 0 ^ 2 * defectLaplace (tentPrimitive g) (tentPt h n ε 0)) +
          tentPt h n ε (-1) ^ 2 * defectLaplace (tentPrimitive g) (tentPt h n ε (-1))) /
        ((h : ℂ) * I) ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((1 / (2 * Real.pi) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hre : ∀ s, 0 < (tentPt h n ε s).re := fun s => by rw [tentPt_re]; positivity
  have hCg : 0 ≤ Cg := le_trans (norm_nonneg _) ((hgb 0).trans (by simp))
  -- the integrand on `[-1, 1] × ℝ`
  set F : ℝ → ℝ → ℂ := fun s t => ((1 - |s| : ℝ) : ℂ) *
    (c * (g t * (kerCoeff t * tentPt h n ε s ^ kerExp t))) with hF
  have hrow : ∀ s, ((1 - |s| : ℝ) : ℂ) * defectLaplace g (tentPt h n ε s) = ∫ t, F s t := by
    intro s
    rw [defectLaplace, ← hc, ← integral_const_mul c, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hF, pairKernel_eq_cpow t (hre s)]
  have hFint : Integrable (uncurry F) ((volume.restrict (uIoc (-1 : ℝ) 1)).prod volume) := by
    set δ : ℝ := 2 * (h * ε / (h * ε + h * (|n| + 1))) with hδ
    have hδ0 : 0 < δ := by positivity
    set B : ℝ → ℝ := fun t => ‖c‖ * Cg * (3 * (h * ε) ^ (-(1 / 2 : ℝ))) *
      ((1 + |t|) ^ N * Real.exp (-(δ * |t|))) with hB
    have hBi : Integrable B := (integrable_one_add_abs_pow_mul_exp hδ0 N).const_mul _
    haveI : IsFiniteMeasure (volume.restrict (uIoc (-1 : ℝ) 1)) := by
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
    have hmaj : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * B z.2)
        ((volume.restrict (uIoc (-1 : ℝ) 1)).prod volume) :=
      Integrable.mul_prod (integrable_const (1 : ℝ)) hBi
    refine hmaj.mono' ?_ ?_
    · have hcont : Continuous fun z : ℝ × ℝ => ((1 - |z.1| : ℝ) : ℂ) *
          (c * (kerCoeff z.2 * tentPt h n ε z.1 ^ kerExp z.2)) := by
        refine (by fun_prop : Continuous fun z : ℝ × ℝ => ((1 - |z.1| : ℝ) : ℂ)).mul
          (continuous_const.mul ((continuous_kerCoeff.comp continuous_snd).mul ?_))
        exact ((continuous_tentPt h n ε).comp continuous_fst).cpow
          (continuous_kerExp.comp continuous_snd) fun z => tentPt_mem_slitPlane hh hε n z.1
      have he : uncurry F = fun z : ℝ × ℝ => g z.2 * (((1 - |z.1| : ℝ) : ℂ) *
          (c * (kerCoeff z.2 * tentPt h n ε z.1 ^ kerExp z.2))) := by
        funext z
        simp only [hF, uncurry]
        ring
      rw [he]
      exact ((hgm.comp measurable_snd).mul hcont.measurable).aestronglyMeasurable
    · have hprod : (volume.restrict (uIoc (-1 : ℝ) 1)).prod (volume : Measure ℝ) =
          ((volume : Measure ℝ).prod volume).restrict (uIoc (-1 : ℝ) 1 ×ˢ univ) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [hprod]
      filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod MeasurableSet.univ)] with z hz
      obtain ⟨s, t⟩ := z
      have hs : |s| ≤ 1 := by
        have := hz.1
        rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at this
        exact abs_le.mpr ⟨this.1.le, this.2⟩
      have hk := norm_pairKernel_tentPt_le hh hε n t hs
      rw [pairKernel_eq_cpow t (hre s), norm_mul] at hk
      simp only [uncurry, hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, hB, one_mul]
      have h1s : abs (1 - |s|) ≤ 1 :=
        abs_le.mpr ⟨by linarith [abs_nonneg s], by linarith [abs_nonneg s]⟩
      calc abs (1 - |s|) * (‖c‖ * (‖g t‖ * (‖kerCoeff t‖ * ‖tentPt h n ε s ^ kerExp t‖)))
          ≤ 1 * (‖c‖ * ((Cg * (1 + |t|) ^ N) * (3 * (h * ε) ^ (-(1 / 2 : ℝ)) *
              Real.exp (-(δ * |t|))))) := by
            gcongr
            all_goals exact hgb t
        _ = _ := by ring
  rw [intervalIntegral.integral_congr (fun s _ => hrow s), intervalIntegral_integral_swap hFint]
  -- each column is a second difference
  have hint : ∀ σ : ℝ, Integrable fun t => tentPrimitive g t * pairKernel (2 * t) (tentPt h n ε σ) :=
    fun σ => integrable_defectLaplace_integrand (measurable_tentPrimitive hgm).aestronglyMeasurable
      (Cg := 4 / 3 * Cg) (N := N) (fun t => (norm_tentPrimitive_le g t).trans (by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hgb t) (by norm_num))) (hre σ)
  have hcol : ∀ t, ∫ s in (-1 : ℝ)..1, F s t =
      ((tentPt h n ε 1 ^ 2 * c) * (tentPrimitive g t * pairKernel (2 * t) (tentPt h n ε 1)) -
        (2 * tentPt h n ε 0 ^ 2 * c) * (tentPrimitive g t * pairKernel (2 * t) (tentPt h n ε 0)) +
          (tentPt h n ε (-1) ^ 2 * c) *
            (tentPrimitive g t * pairKernel (2 * t) (tentPt h n ε (-1)))) / ((h : ℂ) * I) ^ 2 := by
    intro t
    have hfa : (kerExp t + 2) * (kerExp t + 1) ≠ 0 := by
      rw [kerExp_factor]; exact tentFactor_ne_zero t
    have hcalc : ∫ s in (-1 : ℝ)..1, F s t = (c * g t * kerCoeff t) *
        ∫ s in (-1 : ℝ)..1, ((1 - |s| : ℝ) : ℂ) * tentPt h n ε s ^ kerExp t := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [hF]
      ring
    rw [hcalc, integral_tent_mul_cpow hh hε n hfa]
    have e : ∀ σ : ℝ, tentPt h n ε σ ^ 2 * pairKernel (2 * t) (tentPt h n ε σ) =
        kerCoeff t * tentPt h n ε σ ^ (kerExp t + 2) := fun σ => sq_mul_pairKernel t (hre σ)
    have hG : tentPrimitive g t = g t / ((kerExp t + 2) * (kerExp t + 1)) := by
      rw [kerExp_factor]; rfl
    have hhI : ((h : ℂ) * I) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero (by exact_mod_cast hh.ne') I_ne_zero)
    have e1 : ∀ σ : ℝ, tentPt h n ε σ ^ 2 * c *
        (tentPrimitive g t * pairKernel (2 * t) (tentPt h n ε σ)) =
        c * tentPrimitive g t * (kerCoeff t * tentPt h n ε σ ^ (kerExp t + 2)) := by
      intro σ; rw [← e σ]; ring
    rw [e1 1, show 2 * tentPt h n ε 0 ^ 2 * c * (tentPrimitive g t *
      pairKernel (2 * t) (tentPt h n ε 0)) = 2 * (tentPt h n ε 0 ^ 2 * c *
        (tentPrimitive g t * pairKernel (2 * t) (tentPt h n ε 0))) by ring, e1 0, e1 (-1), hG]
    field_simp
  rw [integral_congr_ae (Eventually.of_forall hcol), integral_div]
  have hA : Integrable (fun t => (tentPt h n ε 1 ^ 2 * c) *
      (tentPrimitive g t * pairKernel (2 * t) (tentPt h n ε 1)) -
        (2 * tentPt h n ε 0 ^ 2 * c) * (tentPrimitive g t * pairKernel (2 * t) (tentPt h n ε 0))) :=
    ((hint 1).const_mul _).sub ((hint 0).const_mul _)
  rw [integral_add hA ((hint (-1)).const_mul _),
    integral_sub ((hint 1).const_mul _) ((hint 0).const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul]
  simp only [defectLaplace, ← hc]
  ring

end GaloisForLFunctions.EulerFETransportTheory
