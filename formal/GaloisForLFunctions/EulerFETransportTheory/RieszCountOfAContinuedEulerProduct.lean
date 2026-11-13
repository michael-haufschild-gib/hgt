import GaloisForLFunctions.EulerFETransportTheory.TheMellinTransformOfAContinuousEulerProduct
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift
import GaloisForLFunctions.EulerFETransportTheory.DecayingTentErrorsAreSmall

/-!
# The count of a measure whose Mellin transform continues past `Re s = 1/2`

Let `ν` live on `[1, ∞)` with `∫ u^{-2} dν < ∞` and `Z(s) = ∫ u^{-s} dν`.  If `G(s) = (s - 1) Z(s)`
continues holomorphically across the strip `2/5 ≤ Re s ≤ 2` with `‖G(s)‖ ≤ C (1 + |Im s|)^{3/2}`
there, then `ν([1, x]) = A x + O(x^{4/5})`, `A = Re G(1)` (`exists_abs_count_sub_le`).

* The Riesz kernel `φ(u) = (1 - u)₊²/2` has `𝓜φ(s) = 1/(s(s+1)(s+2))` (`mellin_rieszKernel`), so
  Mellin inversion gives the second Riesz mean
  `N₂(x) = ∫ (x - u)₊²/2 dν = (1/2π) ∫ Z(2 + iτ) x^{4+iτ} / ((2+iτ)(3+iτ)(4+iτ)) dτ`.
* The same identity for `A · du` on `[1, ∞)` (transform `A/(s - 1)`) gives `A (x - 1)³/6`; the
  difference has the transform `H = (G - A)/(s - 1)`, holomorphic on the strip, and the contour
  moves to `Re s = 2/5`: `N₂(x) = A(x - 1)³/6 + O(x^{12/5})`.
* Second differences of step `h = x^{4/5}` bracket `h² ν([1, x])` (the kernel of the second
  difference is a quadratic B-spline between `0` and `h²`).
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-! ## The Riesz kernel and its Mellin transform -/

/-- The Riesz kernel `φ(u) = (1 - u)²/2` for `u ≤ 1`, `0` beyond. -/
def rieszKernel (u : ℝ) : ℝ := if u ≤ 1 then (1 - u) ^ 2 / 2 else 0

theorem continuous_rieszKernel : Continuous rieszKernel := by
  unfold rieszKernel
  exact Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
    fun u hu => by rw [hu]; norm_num

theorem rieszKernel_nonneg (u : ℝ) : 0 ≤ rieszKernel u := by
  unfold rieszKernel; split_ifs <;> positivity

theorem rieszKernel_le_half {u : ℝ} (hu : 0 ≤ u) : rieszKernel u ≤ 1 / 2 := by
  unfold rieszKernel
  split_ifs with h
  · nlinarith
  · norm_num

/-- `𝓜φ(s) = 1/(s(s+1)(s+2))` for `Re s > 0`. -/
theorem mellin_rieszKernel {s : ℂ} (hs : 0 < s.re) :
    mellin (fun u => (rieszKernel u : ℂ)) s = 1 / (s * (s + 1) * (s + 2)) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hs2 : s + 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  -- the integrand vanishes beyond `1`
  have hsplit : mellin (fun u => (rieszKernel u : ℂ)) s =
      ∫ u in Ioc (0 : ℝ) 1, (u : ℂ) ^ (s - 1) * (((1 - u) ^ 2 / 2 : ℝ) : ℂ) := by
    rw [mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi]
    · have hzero : ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (s - 1) • (rieszKernel u : ℂ) = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
        rw [rieszKernel, if_neg (not_le.mpr hu)]; simp
      rw [hzero, add_zero]
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      rw [rieszKernel, if_pos hu.2, smul_eq_mul]
    · refine IntegrableOn.congr_fun
        (f := fun u : ℝ => (u : ℂ) ^ (s - 1) * (((1 - u) ^ 2 / 2 : ℝ) : ℂ))
        ?_ (fun u hu => by rw [rieszKernel, if_pos hu.2, smul_eq_mul]) measurableSet_Ioc
      have hi : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (s - 1)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
      exact (hi.mul_continuousOn (g := fun u : ℝ => (((1 - u) ^ 2 / 2 : ℝ) : ℂ))
        (by fun_prop)).1
    · refine (integrableOn_zero).congr_fun (fun u hu => ?_) measurableSet_Ioi
      rw [rieszKernel, if_neg (not_le.mpr hu)]; simp
  -- expand `(1 - u)²/2 u^{s-1}` and integrate termwise
  have hexp : ∀ u ∈ Ioc (0 : ℝ) 1, (u : ℂ) ^ (s - 1) * (((1 - u) ^ 2 / 2 : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ((u : ℂ) ^ (s - 1) - 2 * (u : ℂ) ^ s + (u : ℂ) ^ (s + 1)) := by
    intro u hu
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.1.ne'
    have e1 : (u : ℂ) ^ s = (u : ℂ) ^ (s - 1) * u := by
      have := Complex.cpow_add (s - 1) 1 hu0
      rw [Complex.cpow_one, sub_add_cancel] at this
      exact this
    have e2 : (u : ℂ) ^ (s + 1) = (u : ℂ) ^ (s - 1) * u ^ 2 := by
      have := Complex.cpow_add (s - 1) 2 hu0
      rw [show s - 1 + 2 = s + 1 by ring,
        show (u : ℂ) ^ (2 : ℂ) = (u : ℂ) ^ (2 : ℕ) by exact_mod_cast Complex.cpow_natCast (u : ℂ) 2]
        at this
      exact this
    rw [e1, e2]
    push_cast
    ring
  have hre : ∀ r : ℂ, -1 < r.re → ∫ u in Ioc (0 : ℝ) 1, (u : ℂ) ^ r = 1 / (r + 1) := by
    intro r hr
    have hr1 : r + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hr),
      Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero, Complex.zero_cpow hr1, sub_zero]
  have hint : ∀ r : ℂ, -1 < r.re → IntegrableOn (fun u : ℝ => (u : ℂ) ^ r) (Ioc (0 : ℝ) 1) := by
    intro r hr
    exact (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) hr).1
  have h1 : -1 < (s - 1).re := by simp; linarith
  have h2 : -1 < s.re := by linarith
  have h3 : -1 < (s + 1).re := by simp; linarith
  have i12 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) - 2 * (u : ℂ) ^ s) (Ioc (0 : ℝ) 1) :=
    (hint _ h1).sub ((hint _ h2).const_mul 2)
  have i2 : IntegrableOn (fun u : ℝ => 2 * (u : ℂ) ^ s) (Ioc (0 : ℝ) 1) := (hint _ h2).const_mul 2
  rw [hsplit, setIntegral_congr_fun measurableSet_Ioc hexp, integral_const_mul,
    integral_add i12 (hint _ h3), integral_sub (hint _ h1) i2, integral_const_mul,
    hre _ h1, hre _ h2, hre _ h3, show s - 1 + 1 = s by ring, show s + 1 + 1 = s + 2 by ring]
  field_simp
  ring

/-- The cubic kernel `M(s) = 1/(s(s+1)(s+2))`. -/
def rieszMellin (s : ℂ) : ℂ := 1 / (s * (s + 1) * (s + 2))

theorem rieszMellin_denom_ne_zero {s : ℂ} (hs : 0 < s.re) : s * (s + 1) * (s + 2) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> intro h <;>
    · have := congrArg Complex.re h
      simp at this
      linarith

theorem differentiableAt_rieszMellin {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ rieszMellin s := by
  unfold rieszMellin
  exact (differentiableAt_const _).div (by fun_prop) (rieszMellin_denom_ne_zero hs)

theorem continuous_rieszMellin_line {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun τ : ℝ => rieszMellin ((σ : ℂ) + (τ : ℂ) * I) :=
  continuous_iff_continuousAt.mpr fun _ =>
    (differentiableAt_rieszMellin (by simpa using hσ)).continuousAt.comp (by fun_prop)

/-- On `Re s ≥ 2/5` the cubic kernel decays: `‖M(σ + iτ)‖ ≤ 20 (1 + |τ|)^{-3}`. -/
theorem norm_rieszMellin_le {σ : ℝ} (hσ : 2 / 5 ≤ σ) (τ : ℝ) :
    ‖rieszMellin ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ 20 * (1 + |τ|) ^ (-(3 : ℝ)) := by
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have him : s.im = τ := by simp [hs]
  have hlow : ∀ c : ℝ, 0 ≤ c → (1 + |τ|) / 5 ≤ ‖s + c‖ := by
    intro c hc
    have h1 := Complex.abs_re_le_norm (s + c)
    have h2 := Complex.abs_im_le_norm (s + c)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero,
      hre, him] at h1 h2
    rw [abs_of_pos (by linarith)] at h1
    linarith [abs_nonneg τ]
  have hlow1 : (1 + |τ|) / 2 ≤ ‖s + 1‖ := by
    have h1 := Complex.abs_re_le_norm (s + 1)
    have h2 := Complex.abs_im_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero,
      hre, him] at h1 h2
    rw [abs_of_pos (by linarith)] at h1
    linarith [abs_nonneg τ]
  have hlow2 : (1 + |τ|) / 2 ≤ ‖s + 2‖ := by
    have h1 := Complex.abs_re_le_norm (s + 2)
    have h2 := Complex.abs_im_le_norm (s + 2)
    have e2 : (s + 2).re = σ + 2 := by simp [hre]
    have e2' : (s + 2).im = τ := by simp [him]
    rw [e2] at h1; rw [e2'] at h2
    rw [abs_of_pos (by linarith)] at h1
    linarith [abs_nonneg τ]
  have hs0 := hlow 0 le_rfl
  simp only [Complex.ofReal_zero, add_zero] at hs0
  have hpos : 0 < 1 + |τ| := by positivity
  have hP : (1 + |τ|) ^ 3 / 20 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by
    have := mul_le_mul (mul_le_mul hs0 hlow1 (by positivity) (norm_nonneg _)) hlow2
      (by positivity) (by positivity)
    nlinarith [this]
  have hPpos : 0 < (1 + |τ|) ^ 3 / 20 := by positivity
  rw [rieszMellin, norm_div, norm_one, norm_mul, norm_mul, Real.rpow_neg hpos.le,
    show ((1 + |τ|) ^ (3 : ℝ)) = (1 + |τ|) ^ (3 : ℕ) by norm_cast]
  calc 1 / (‖s‖ * ‖s + 1‖ * ‖s + 2‖) ≤ 1 / ((1 + |τ|) ^ 3 / 20) :=
        one_div_le_one_div_of_le hPpos hP
    _ = 20 * ((1 + |τ|) ^ 3)⁻¹ := by field_simp

/-- **Mellin inversion of the Riesz kernel**: for `y > 0`,
`φ(y) = (1/2π) ∫ y^{-(2+iτ)} M(2 + iτ) dτ`. -/
theorem rieszKernel_eq_mellinInv {y : ℝ} (hy : 0 < y) :
    ((rieszKernel y : ℝ) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ τ : ℝ, (y : ℂ) ^ (-((2 : ℂ) + (τ : ℂ) * I)) * rieszMellin ((2 : ℂ) + (τ : ℂ) * I) := by
  have hconv : MellinConvergent (fun u => (rieszKernel u : ℂ)) ((2 : ℝ) : ℂ) := by
    unfold MellinConvergent
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    refine IntegrableOn.union ?_ ?_
    · refine (Continuous.integrableOn_Icc (μ := volume) (a := 0) (b := 1) ?_).mono_set
        Ioc_subset_Icc_self
      have : Continuous fun t : ℝ => (t : ℂ) ^ (((2 : ℝ) : ℂ) - 1) := by
        rw [show ((2 : ℝ) : ℂ) - 1 = ((1 : ℕ) : ℂ) by push_cast; ring]
        simp only [Complex.cpow_natCast, pow_one]
        fun_prop
      exact this.smul (Complex.continuous_ofReal.comp continuous_rieszKernel)
    · refine integrableOn_zero.congr_fun (fun u hu => ?_) measurableSet_Ioi
      simp only [rieszKernel, if_neg (not_le.mpr (show (1 : ℝ) < u from hu))]
      simp
  have hvert : VerticalIntegrable (mellin fun u => (rieszKernel u : ℂ)) 2 := by
    unfold VerticalIntegrable
    have heq : (fun τ : ℝ => mellin (fun u => (rieszKernel u : ℂ)) (((2 : ℝ) : ℂ) + (τ : ℂ) * I)) =
        fun τ : ℝ => rieszMellin (((2 : ℝ) : ℂ) + (τ : ℂ) * I) := by
      funext τ
      rw [mellin_rieszKernel (by simp)]
      rfl
    rw [heq]
    have hc : Continuous fun τ : ℝ => rieszMellin (((2 : ℝ) : ℂ) + (τ : ℂ) * I) :=
      continuous_rieszMellin_line (by norm_num)
    refine ((integrable_one_add_abs_rpow_neg (r := 3) (by norm_num)).const_mul 20).mono'
      hc.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    exact norm_rieszMellin_le (σ := 2) (by norm_num) τ
  have h := mellinInv_mellin_eq 2 (fun u => (rieszKernel u : ℂ)) hy hconv hvert
    (Complex.continuous_ofReal.comp continuous_rieszKernel).continuousAt
  rw [← h, mellinInv, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only [smul_eq_mul, Complex.ofReal_ofNat]
  rw [mellin_rieszKernel (by simp)]
  rfl

theorem ofReal_div_cpow {u x : ℝ} (hu : 0 < u) (hx : 0 < x) (s : ℂ) :
    ((u / x : ℝ) : ℂ) ^ (-s) = (u : ℂ) ^ (-s) * (x : ℂ) ^ s := by
  have h := Complex.mul_cpow_ofReal_nonneg (div_pos hu hx).le hx.le (-s)
  have e : ((u / x : ℝ) : ℂ) * (x : ℂ) = (u : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hx.ne']
  rw [e] at h
  have hx0 : (x : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left; exact_mod_cast hx.ne'
  rw [h, Complex.cpow_neg (x : ℂ), mul_assoc, inv_mul_cancel₀ hx0, mul_one]

/-- **Riesz means by Mellin inversion**: for `x > 0`,
`∫ φ(u/x) dν = (1/2π) ∫ x^{2+iτ} M(2+iτ) Z(2+iτ) dτ`, `Z = ∫ u^{-s} dν`. -/
theorem integral_rieszKernel_eq {ν : Measure ℝ} [SFinite ν] (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) {x : ℝ} (hx : 0 < x) :
    ((∫ u, rieszKernel (u / x) ∂ν : ℝ) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ τ : ℝ, (x : ℂ) ^ ((2 : ℂ) + (τ : ℂ) * I) * rieszMellin ((2 : ℂ) + (τ : ℂ) * I) *
        measureDirichlet ν ((2 : ℂ) + (τ : ℂ) * I) := by
  set F : ℝ → ℝ → ℂ := fun u τ => ((u / x : ℝ) : ℂ) ^ (-((2 : ℂ) + (τ : ℂ) * I)) *
    rieszMellin ((2 : ℂ) + (τ : ℂ) * I) with hF
  have hae := ae_one_le_of_measure_Iio_one_eq_zero hsupp
  -- pointwise inversion
  have hpt : ∀ᵐ u ∂ν, ((rieszKernel (u / x) : ℝ) : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, F u τ := by
    filter_upwards [hae] with u hu
    exact rieszKernel_eq_mellinInv (div_pos (by linarith) hx)
  -- absolute integrability on the product
  have hcM : Continuous fun τ : ℝ => rieszMellin ((2 : ℂ) + (τ : ℂ) * I) := by
    simpa using continuous_rieszMellin_line (σ := 2) (by norm_num)
  have hint : Integrable (Function.uncurry F) (ν.prod volume) := by
    have hmaj : Integrable (fun z : ℝ × ℝ => (x ^ 2 * (1 / z.1 ^ 2)) *
        (20 * (1 + |z.2|) ^ (-(3 : ℝ)))) (ν.prod volume) :=
      Integrable.mul_prod (hmom.const_mul (x ^ 2))
        ((integrable_one_add_abs_rpow_neg (r := 3) (by norm_num)).const_mul 20)
    refine hmaj.mono' ?_ ?_
    · have hm1 : Measurable fun z : ℝ × ℝ => ((z.1 / x : ℝ) : ℂ) ^
          (-((2 : ℂ) + (z.2 : ℂ) * I)) :=
        (Complex.measurable_ofReal.comp (measurable_fst.div_const x)).pow
          ((measurable_const.add ((Complex.measurable_ofReal.comp measurable_snd).mul_const I)).neg)
      exact (hm1.mul (hcM.measurable.comp measurable_snd)).aestronglyMeasurable
    · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hae] with z hz
      have hu : 0 < z.1 := by linarith
      simp only [Function.uncurry, hF, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hu hx)]
      have hre : (-((2 : ℂ) + (z.2 : ℂ) * I)).re = -2 := by simp
      rw [hre]
      have hM := norm_rieszMellin_le (σ := 2) (by norm_num) z.2
      simp only [Complex.ofReal_ofNat] at hM
      have he : (z.1 / x) ^ (-(2 : ℝ)) = x ^ 2 * (1 / z.1 ^ 2) := by
        rw [Real.rpow_neg (div_pos hu hx).le, Real.div_rpow hu.le hx.le]
        norm_cast
        field_simp
      rw [he]
      gcongr
  -- Fubini and the Dirichlet transform
  rw [← integral_complex_ofReal, integral_congr_ae hpt, integral_const_mul,
    integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only [hF]
  rw [measureDirichlet, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with u hu
  rw [ofReal_div_cpow (by linarith) hx]
  ring

/-! ## The comparison measure `du` on `(1, ∞)` -/

theorem measureDirichlet_volume_Ioi_one {s : ℂ} (hs : 1 < s.re) :
    measureDirichlet (volume.restrict (Ioi (1 : ℝ))) s = 1 / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hs1' : -s + 1 ≠ 0 := fun h => hs1 (by linear_combination -h)
  rw [measureDirichlet, integral_Ioi_cpow_of_lt (by simp; linarith) one_pos, Complex.ofReal_one,
    Complex.one_cpow]
  field_simp
  ring

theorem integrable_inv_sq_volume_Ioi_one :
    Integrable (fun u : ℝ => 1 / u ^ 2) (volume.restrict (Ioi (1 : ℝ))) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) one_pos).congr_fun
    (fun u hu => ?_) measurableSet_Ioi
  have hu : (0 : ℝ) < u := lt_trans one_pos hu
  show u ^ (-2 : ℝ) = 1 / u ^ 2
  rw [Real.rpow_neg hu.le, one_div]
  norm_cast

/-- `∫_1^∞ φ(u/x) du = (x - 1)³/(6x²)` for `x ≥ 1`. -/
theorem integral_rieszKernel_volume {x : ℝ} (hx : 1 ≤ x) :
    ∫ u in Ioi (1 : ℝ), rieszKernel (u / x) = (x - 1) ^ 3 / (6 * x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hzero : ∫ u in Ioi x, rieszKernel (u / x) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu => by
      rw [rieszKernel, if_neg (by rw [not_le, one_lt_div hx0]; exact hu)]
  have hsplit : ∫ u in Ioi (1 : ℝ), rieszKernel (u / x) =
      (∫ u in Ioc (1 : ℝ) x, rieszKernel (u / x)) + ∫ u in Ioi x, rieszKernel (u / x) := by
    rw [← Ioc_union_Ioi_eq_Ioi hx, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi]
    · exact ((continuous_rieszKernel.comp (continuous_id.div_const x)).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    · exact integrableOn_zero.congr_fun (fun u hu => by
        show (0 : ℝ) = rieszKernel (u / x)
        rw [rieszKernel, if_neg (by rw [not_le, one_lt_div hx0]; exact hu)]) measurableSet_Ioi
  rw [hsplit, hzero, add_zero, ← intervalIntegral.integral_of_le hx]
  have hderiv : ∀ u ∈ uIcc 1 x, HasDerivAt (fun u : ℝ => -(x / 6) * (1 - u / x) ^ 3)
      (rieszKernel (u / x)) u := by
    intro u hu
    rw [uIcc_of_le hx] at hu
    have h := ((((hasDerivAt_id u).div_const x).const_sub 1).pow 3).const_mul (-(x / 6))
    rw [rieszKernel, if_pos (by rw [div_le_one hx0]; exact hu.2)]
    refine h.congr_deriv ?_
    have hx' : x ≠ 0 := hx0.ne'
    simp only [id]
    norm_num
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_rieszKernel.comp (continuous_id.div_const x)).intervalIntegrable _ _),
    div_self hx0.ne', sub_self]
  field_simp
  ring

/-! ## The difference quotient -/

/-- On the strip `2/5 ≤ Re s ≤ 2` the difference quotient `H = (G - G(1))/(s - 1)` grows at most
like `(1 + |Im s|)^{1/2}`. -/
theorem exists_norm_dslope_le {G : ℂ → ℂ} {σ₁ : ℝ} (hσ₁ : σ₁ < 2 / 5)
    (hG : DifferentiableOn ℂ G {s : ℂ | σ₁ < s.re}) {C : ℝ}
    (hGb : ∀ s : ℂ, 2 / 5 ≤ s.re → s.re ≤ 2 → ‖G s‖ ≤ C * (1 + |s.im|) ^ (3 / 2 : ℝ)) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∀ s : ℂ, 2 / 5 ≤ s.re → s.re ≤ 2 →
      ‖dslope G 1 s‖ ≤ CH * (1 + |s.im|) ^ (1 / 2 : ℝ) := by
  have hopen : IsOpen {s : ℂ | σ₁ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hH : DifferentiableOn ℂ (dslope G 1) {s : ℂ | σ₁ < s.re} :=
    (differentiableOn_dslope (hopen.mem_nhds (by show σ₁ < (1 : ℂ).re; simp; linarith))).mpr hG
  have hK : IsCompact (Icc (2 / 5 : ℝ) 2 ×ℂ Icc (-1 : ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hH.continuousOn.mono fun s hs => by
    rw [Complex.mem_reProdIm] at hs
    show σ₁ < s.re
    linarith [hs.1.1])
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hGb 1 (by simp; norm_num) (by simp))
    simpa using this
  refine ⟨max (max B 0) (2 * C + 2 * ‖G 1‖), by positivity, fun s hs1 hs2 => ?_⟩
  have hpow : 1 ≤ (1 + |s.im|) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg s.im]) (by norm_num)
  rcases le_or_gt |s.im| 1 with him | him
  · have hsK : s ∈ Icc (2 / 5 : ℝ) 2 ×ℂ Icc (-1 : ℝ) 1 := by
      rw [Complex.mem_reProdIm]; exact ⟨⟨hs1, hs2⟩, abs_le.mp him⟩
    calc ‖dslope G 1 s‖ ≤ B := hB s hsK
      _ ≤ max (max B 0) (2 * C + 2 * ‖G 1‖) := (le_max_left _ _).trans (le_max_left _ _)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hpow
  · have hs1' : s ≠ 1 := fun h => by rw [h] at him; norm_num at him
    have hnorm : |s.im| ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1); simpa using this
    have hpos : 0 < ‖s - 1‖ := by linarith
    have hhalf : (1 + |s.im|) / 2 ≤ ‖s - 1‖ := by linarith
    rw [dslope_of_ne _ hs1', slope_def_field, norm_div]
    rw [div_le_iff₀ hpos]
    have hG1 := hGb s hs1 hs2
    have hsq : (1 + |s.im|) ^ (3 / 2 : ℝ) = (1 + |s.im|) ^ (1 / 2 : ℝ) * (1 + |s.im|) := by
      rw [← Real.rpow_add_one (by positivity)]; norm_num
    calc ‖G s - G 1‖ ≤ ‖G s‖ + ‖G 1‖ := norm_sub_le _ _
      _ ≤ C * ((1 + |s.im|) ^ (1 / 2 : ℝ) * (1 + |s.im|)) + ‖G 1‖ * ((1 + |s.im|) ^ (1 / 2 : ℝ) *
            (1 + |s.im|)) := by
          rw [← hsq]
          gcongr
          have : 1 ≤ (1 + |s.im|) ^ (1 / 2 : ℝ) * (1 + |s.im|) := by nlinarith
          nlinarith [norm_nonneg (G 1)]
      _ = (2 * C + 2 * ‖G 1‖) * (1 + |s.im|) ^ (1 / 2 : ℝ) * ((1 + |s.im|) / 2) := by ring
      _ ≤ max (max B 0) (2 * C + 2 * ‖G 1‖) * (1 + |s.im|) ^ (1 / 2 : ℝ) * ‖s - 1‖ := by
          gcongr
          exact le_max_right _ _

/-! ## The contour shift -/

/-- The integrand `Φ(s) = x^s M(s) H(s)` on the strip:
`‖Φ(σ + iτ)‖ ≤ 20 C_H x^σ (1 + |τ|)^{-5/2}`. -/
theorem norm_cpow_mul_rieszMellin_le {H : ℂ → ℂ} {CH : ℝ}
    (hH : ∀ s : ℂ, 2 / 5 ≤ s.re → s.re ≤ 2 → ‖H s‖ ≤ CH * (1 + |s.im|) ^ (1 / 2 : ℝ))
    {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ1 : 2 / 5 ≤ σ) (hσ2 : σ ≤ 2) (τ : ℝ) :
    ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * I) * rieszMellin ((σ : ℂ) + (τ : ℂ) * I) *
        H ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ 20 * CH * x ^ σ * (1 + |τ|) ^ (-(5 / 2 : ℝ)) := by
  have hpos : 0 < 1 + |τ| := by positivity
  have h1 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * I)‖ = x ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  have h2 := norm_rieszMellin_le hσ1 τ
  have h3 := hH ((σ : ℂ) + (τ : ℂ) * I) (by simp; exact hσ1) (by simp; exact hσ2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_zero, mul_one, zero_add, add_zero] at h3
  rw [norm_mul, norm_mul, h1]
  have he : (1 + |τ|) ^ (-(3 : ℝ)) * (1 + |τ|) ^ (1 / 2 : ℝ) = (1 + |τ|) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_add hpos]; norm_num
  calc x ^ σ * ‖rieszMellin ((σ : ℂ) + (τ : ℂ) * I)‖ * ‖H ((σ : ℂ) + (τ : ℂ) * I)‖
      ≤ x ^ σ * (20 * (1 + |τ|) ^ (-(3 : ℝ))) * (CH * (1 + |τ|) ^ (1 / 2 : ℝ)) := by gcongr
    _ = 20 * CH * x ^ σ * ((1 + |τ|) ^ (-(3 : ℝ)) * (1 + |τ|) ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by rw [he]

/-- **The second Riesz mean.**  `x² ∫ φ(u/x) dν = G(1)(x - 1)³/6 + O(x^{12/5})` for `x ≥ 1`. -/
theorem exists_norm_rieszMean_sub_le {ν : Measure ℝ} [SFinite ν] (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) {G : ℂ → ℂ} {σ₁ : ℝ} (hσ₁ : σ₁ < 2 / 5)
    (hG : DifferentiableOn ℂ G {s : ℂ | σ₁ < s.re})
    (hGZ : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * measureDirichlet ν s) {C : ℝ}
    (hGb : ∀ s : ℂ, 2 / 5 ≤ s.re → s.re ≤ 2 → ‖G s‖ ≤ C * (1 + |s.im|) ^ (3 / 2 : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      ‖((x ^ 2 * ∫ u, rieszKernel (u / x) ∂ν : ℝ) : ℂ) - G 1 * (((x - 1) ^ 3 / 6 : ℝ) : ℂ)‖ ≤
        K * x ^ (12 / 5 : ℝ) := by
  obtain ⟨CH, hCH, hH⟩ := exists_norm_dslope_le hσ₁ hG hGb
  have hopen : IsOpen {s : ℂ | σ₁ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hHd : DifferentiableOn ℂ (dslope G 1) {s : ℂ | σ₁ < s.re} :=
    (differentiableOn_dslope (hopen.mem_nhds (by show σ₁ < (1 : ℂ).re; simp; linarith))).mpr hG
  have hI := integrable_one_add_abs_rpow_neg (r := 5 / 2) (by norm_num)
  set I₅ := ∫ τ : ℝ, (1 + |τ|) ^ (-(5 / 2 : ℝ)) with hI₅
  have hI₅0 : 0 ≤ I₅ := integral_nonneg fun τ => by positivity
  refine ⟨1 / (2 * Real.pi) * (20 * CH * I₅), by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set A := G 1 with hA
  set Φ : ℂ → ℂ := fun s => (x : ℂ) ^ s * rieszMellin s * dslope G 1 s with hΦ
  have hstrip : ∀ s ∈ HTGeometry.verticalStrip (2 / 5) 2, σ₁ < s.re := fun s hs => by
    have := (HTGeometry.mem_verticalStrip.mp hs).1; linarith
  have hΦd : DifferentiableOn ℂ Φ (HTGeometry.verticalStrip (2 / 5) 2) := by
    intro s hs
    have hsre : 0 < s.re := by have := (HTGeometry.mem_verticalStrip.mp hs).1; linarith
    refine (((differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hx0.ne'))).mul
      (differentiableAt_rieszMellin hsre)).mul ?_).differentiableWithinAt
    exact hHd.differentiableAt (hopen.mem_nhds (hstrip s hs))
  have hline : ∀ σ : ℝ, 2 / 5 ≤ σ → σ ≤ 2 →
      Integrable fun τ : ℝ => Φ ((σ : ℂ) + (τ : ℝ) * I) := by
    intro σ h1 h2
    refine ((hI.const_mul (20 * CH * x ^ σ))).mono' ?_ (Eventually.of_forall fun τ =>
      norm_cpow_mul_rieszMellin_le hH hx0 h1 h2 τ)
    refine (ContinuousOn.comp_continuous (s := HTGeometry.verticalStrip (2 / 5) 2) hΦd.continuousOn
      (by fun_prop) fun τ => ?_).aestronglyMeasurable
    exact HTGeometry.mem_verticalStrip.mpr ⟨by simp; exact h1, by simp; exact h2⟩
  -- the contour shift from `Re s = 2` to `Re s = 2/5`
  have hshift : (∫ τ : ℝ, Φ (((2 : ℝ) : ℂ) + (τ : ℝ) * I)) =
      ∫ τ : ℝ, Φ (((2 / 5 : ℝ) : ℂ) + (τ : ℝ) * I) := by
    have hedge : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 → Tendsto (fun T : ℝ =>
        ∫ u in (2 / 5 : ℝ)..2, Φ ((u : ℂ) + ((sgn * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
      intro sgn hsgn
      refine HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
        (M := fun T => 20 * CH * x ^ (2 : ℝ) * (1 + |sgn * T|) ^ (-(5 / 2 : ℝ))) ?_ ?_
      · refine Eventually.of_forall fun T u hu => ?_
        rw [uIoc_of_le (by norm_num)] at hu
        refine (norm_cpow_mul_rieszMellin_le hH hx0 hu.1.le hu.2 _).trans ?_
        gcongr
        exact hu.2
      · have habs : Tendsto (fun T : ℝ => 1 + |sgn * T|) atTop atTop := by
          refine tendsto_atTop_add_const_left _ 1 ?_
          rcases hsgn with h | h <;> subst h <;> simpa using tendsto_abs_atTop_atTop
        have := ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 5 / 2 by norm_num)).comp habs).const_mul
          (20 * CH * x ^ (2 : ℝ))
        simpa using this
    have hbot := hedge (-1) (Or.inr rfl)
    have htop := hedge 1 (Or.inl rfl)
    simp only [neg_one_mul, one_mul] at hbot htop
    exact HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto (by norm_num) hΦd
      (hline (2 / 5) le_rfl (by norm_num)) (hline 2 (by norm_num) le_rfl) hbot htop
  -- the line `Re s = 2`: `Z = A/(s - 1) + H`
  have hZ : ∀ τ : ℝ, (x : ℂ) ^ ((2 : ℂ) + (τ : ℂ) * I) * rieszMellin ((2 : ℂ) + (τ : ℂ) * I) *
      measureDirichlet ν ((2 : ℂ) + (τ : ℂ) * I) =
      A * ((x : ℂ) ^ ((2 : ℂ) + (τ : ℂ) * I) * rieszMellin ((2 : ℂ) + (τ : ℂ) * I) *
        measureDirichlet (volume.restrict (Ioi (1 : ℝ))) ((2 : ℂ) + (τ : ℂ) * I)) +
      Φ (((2 : ℝ) : ℂ) + (τ : ℝ) * I) := by
    intro τ
    have hre : 1 < ((2 : ℂ) + (τ : ℂ) * I).re := by simp
    have hne : (2 : ℂ) + (τ : ℂ) * I ≠ 1 := fun h => by rw [h] at hre; simp at hre
    have hne' : (2 : ℂ) + (τ : ℂ) * I - 1 ≠ 0 := sub_ne_zero.mpr hne
    rw [measureDirichlet_volume_Ioi_one hre, hΦ]
    simp only [Complex.ofReal_ofNat]
    rw [dslope_of_ne _ hne, slope_def_field, hGZ _ hre, ← hA]
    field_simp
    ring
  have hint1 : Integrable fun τ : ℝ => A * ((x : ℂ) ^ ((2 : ℂ) + (τ : ℂ) * I) *
      rieszMellin ((2 : ℂ) + (τ : ℂ) * I) *
        measureDirichlet (volume.restrict (Ioi (1 : ℝ))) ((2 : ℂ) + (τ : ℂ) * I)) := by
    refine Integrable.const_mul ?_ A
    refine ((hI.const_mul (20 * x ^ (2 : ℝ)))).mono' ?_ (Eventually.of_forall fun τ => ?_)
    · have hc : Continuous fun τ : ℝ => (x : ℂ) ^ ((2 : ℂ) + (τ : ℂ) * I) *
          rieszMellin ((2 : ℂ) + (τ : ℂ) * I) * (1 / ((2 : ℂ) + (τ : ℂ) * I - 1)) := by
        refine ((Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx0.ne'))).mul
          ?_).mul ?_
        · exact continuous_iff_continuousAt.mpr fun τ =>
            (differentiableAt_rieszMellin (by simp)).continuousAt.comp (by fun_prop)
        · refine continuous_const.div (by fun_prop) fun τ h => ?_
          have := congrArg Complex.re h
          norm_num at this
      refine hc.aestronglyMeasurable.congr (Eventually.of_forall fun τ => ?_)
      dsimp only
      rw [measureDirichlet_volume_Ioi_one (s := (2 : ℂ) + (τ : ℂ) * I) (by simp)]
    · rw [measureDirichlet_volume_Ioi_one (s := (2 : ℂ) + (τ : ℂ) * I) (by simp), norm_mul,
        norm_mul]
      have h1 : ‖(x : ℂ) ^ ((2 : ℂ) + (τ : ℂ) * I)‖ = x ^ (2 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp
      have h2 := norm_rieszMellin_le (σ := 2) (by norm_num) τ
      simp only [Complex.ofReal_ofNat] at h2
      have h3 : ‖1 / ((2 : ℂ) + (τ : ℂ) * I - 1)‖ ≤ 1 := by
        rw [norm_div, norm_one]
        refine div_le_one_of_le₀ ?_ (norm_nonneg _)
        have hre1 : ((2 : ℂ) + (τ : ℂ) * I - 1).re = 1 := by simp; norm_num
        have := Complex.abs_re_le_norm ((2 : ℂ) + (τ : ℂ) * I - 1)
        rwa [hre1, abs_one] at this
      rw [h1]
      have hpos : 0 ≤ (1 + |τ|) ^ (-(3 : ℝ)) := by positivity
      have h3' : (1 + |τ|) ^ (-(3 : ℝ)) ≤ (1 + |τ|) ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) (by norm_num)
      calc x ^ (2 : ℝ) * ‖rieszMellin ((2 : ℂ) + (τ : ℂ) * I)‖ * ‖1 / ((2 : ℂ) + (τ : ℂ) * I - 1)‖
          ≤ x ^ (2 : ℝ) * (20 * (1 + |τ|) ^ (-(3 : ℝ))) * 1 := by gcongr
        _ = 20 * x ^ (2 : ℝ) * (1 + |τ|) ^ (-(3 : ℝ)) := by ring
        _ ≤ 20 * x ^ (2 : ℝ) * (1 + |τ|) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h3' (by positivity)
  have hint2 : Integrable fun τ : ℝ => Φ (((2 : ℝ) : ℂ) + (τ : ℝ) * I) :=
    hline 2 (by norm_num) le_rfl
  -- assemble
  have hν := integral_rieszKernel_eq hsupp hmom hx0
  have hν₁ := integral_rieszKernel_eq (ν := volume.restrict (Ioi (1 : ℝ)))
    (by rw [Measure.restrict_apply measurableSet_Iio, Iio_inter_Ioi, Ioo_self, measure_empty])
    integrable_inv_sq_volume_Ioi_one hx0
  rw [integral_rieszKernel_volume hx] at hν₁
  have hdiff : ((∫ u, rieszKernel (u / x) ∂ν : ℝ) : ℂ) -
      A * (((x - 1) ^ 3 / (6 * x ^ 2) : ℝ) : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, Φ (((2 / 5 : ℝ) : ℂ) + (τ : ℝ) * I) := by
    rw [hν, hν₁, ← hshift, integral_congr_ae (Eventually.of_forall hZ),
      integral_add hint1 hint2, integral_const_mul]
    ring
  have hbound :
      ‖∫ τ : ℝ, Φ (((2 / 5 : ℝ) : ℂ) + (τ : ℝ) * I)‖ ≤ 20 * CH * x ^ (2 / 5 : ℝ) * I₅ := by
    calc ‖∫ τ : ℝ, Φ (((2 / 5 : ℝ) : ℂ) + (τ : ℝ) * I)‖
        ≤ ∫ τ : ℝ, 20 * CH * x ^ (2 / 5 : ℝ) * (1 + |τ|) ^ (-(5 / 2 : ℝ)) :=
          norm_integral_le_of_norm_le (hI.const_mul _) (Eventually.of_forall fun τ =>
            norm_cpow_mul_rieszMellin_le hH hx0 le_rfl (by norm_num) τ)
      _ = 20 * CH * x ^ (2 / 5 : ℝ) * I₅ := integral_const_mul _ _
  have hx2 : ((x ^ 2 * ∫ u, rieszKernel (u / x) ∂ν : ℝ) : ℂ) - A * (((x - 1) ^ 3 / 6 : ℝ) : ℂ) =
      ((x ^ 2 : ℝ) : ℂ) * (((∫ u, rieszKernel (u / x) ∂ν : ℝ) : ℂ) -
        A * (((x - 1) ^ 3 / (6 * x ^ 2) : ℝ) : ℂ)) := by
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    push_cast
    field_simp
  rw [hx2, hdiff, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hpow : x ^ 2 * x ^ (2 / 5 : ℝ) = x ^ (12 / 5 : ℝ) := by
    rw [show (x ^ 2 : ℝ) = x ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hx0]; norm_num
  calc x ^ 2 * (1 / (2 * Real.pi) * ‖∫ τ : ℝ, Φ (((2 / 5 : ℝ) : ℂ) + (τ : ℝ) * I)‖)
      ≤ x ^ 2 * (1 / (2 * Real.pi) * (20 * CH * x ^ (2 / 5 : ℝ) * I₅)) := by gcongr
    _ = 1 / (2 * Real.pi) * (20 * CH * I₅) * (x ^ 2 * x ^ (2 / 5 : ℝ)) := by ring
    _ = _ := by rw [hpow]

/-! ## From the second Riesz mean to the count -/

/-- The truncated square `(y - u)₊²/2`. -/
def rieszSq (y u : ℝ) : ℝ := max (y - u) 0 ^ 2 / 2

theorem sq_mul_rieszKernel {x : ℝ} (hx : 0 < x) (u : ℝ) :
    x ^ 2 * rieszKernel (u / x) = rieszSq x u := by
  rw [rieszKernel, rieszSq]
  split_ifs with h
  · rw [div_le_one hx] at h
    rw [max_eq_left (by linarith)]
    field_simp
  · rw [div_le_one hx, not_le] at h
    rw [max_eq_right (by linarith)]
    simp

theorem continuous_rieszSq (y : ℝ) : Continuous (rieszSq y) := by
  unfold rieszSq; fun_prop

/-- Domination by the moment: `(y - u)₊²/2 ≤ (y⁴/2) u⁻²` for `u ≥ 1`. -/
theorem rieszSq_le {y u : ℝ} (hu : 1 ≤ u) : rieszSq y u ≤ y ^ 4 / 2 * (1 / u ^ 2) := by
  have hu0 : 0 < u := by linarith
  rw [rieszSq]
  rcases le_or_gt u y with h | h
  · rw [max_eq_left (by linarith), show y ^ 4 / 2 * (1 / u ^ 2) = y ^ 4 / (2 * u ^ 2) by ring,
      div_le_div_iff₀ (by norm_num) (by positivity)]
    have h1 : (y - u) * u ≤ y * y := by nlinarith
    have h2 : 0 ≤ (y - u) * u := by nlinarith
    nlinarith [mul_le_mul h1 h1 h2 (by nlinarith)]
  · rw [max_eq_right (by linarith)]
    have : 0 ≤ y ^ 4 / 2 * (1 / u ^ 2) := by positivity
    simpa using this

theorem integrable_rieszSq {ν : Measure ℝ} (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) (y : ℝ) : Integrable (rieszSq y) ν := by
  refine (hmom.const_mul (y ^ 4 / 2)).mono' (continuous_rieszSq y).aestronglyMeasurable ?_
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold rieszSq; positivity)]
  exact rieszSq_le hu

theorem measure_Icc_one_lt_top {ν : Measure ℝ} (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {y : ℝ} (hy : 0 < y) : ν (Icc 1 y) < ⊤ := by
  refine (measure_mono fun u hu => ?_).trans_lt
    (hmom.measure_norm_ge_lt_top (ε := 1 / y ^ 2) (by positivity))
  have hu0 : 0 < u := by linarith [hu.1]
  show 1 / y ^ 2 ≤ ‖1 / u ^ 2‖
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hu0.le hu.2 2)

theorem measure_Iic_eq {ν : Measure ℝ} (hsupp : ν (Iio 1) = 0) (y : ℝ) :
    ν (Iic y) = ν (Icc 1 y) := by
  refine le_antisymm ?_ (measure_mono Icc_subset_Iic_self)
  calc ν (Iic y) ≤ ν (Iio 1 ∪ Icc 1 y) := measure_mono fun u hu => by
        rcases lt_or_ge u 1 with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hu⟩
    _ ≤ ν (Iio 1) + ν (Icc 1 y) := measure_union_le _ _
    _ = ν (Icc 1 y) := by rw [hsupp, zero_add]

/-- `1_{(-∞, y]}` is `ν`-integrable: `ν[1, y] < ∞` from the moment, and `ν` lives on `[1, ∞)`. -/
theorem integrable_indicator_Iic {ν : Measure ℝ} (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) (y c : ℝ) :
    Integrable ((Iic y).indicator fun _ => c) ν := by
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Iic
  rcases le_or_gt y 0 with hy | hy
  · have h0 : ν (Iic y) = 0 := by
      rw [measure_Iic_eq hsupp, Icc_eq_empty (by linarith), measure_empty]
    exact integrableOn_const (by rw [h0]; exact ENNReal.zero_ne_top)
  · exact integrableOn_const
      (by rw [measure_Iic_eq hsupp]; exact (measure_Icc_one_lt_top hmom hy).ne)

/-- **The quadratic B-spline.**  The second difference of `(· - u)₊²/2` with step `h` lies between
`h² 1[u ≤ y - h]` and `h² 1[u ≤ y + h]`. -/
theorem indicator_le_rieszSq_secondDiff {y h : ℝ} (hh : 0 < h) (u : ℝ) :
    (Iic (y - h)).indicator (fun _ => h ^ 2) u ≤
        rieszSq (y + h) u - 2 * rieszSq y u + rieszSq (y - h) u ∧
      rieszSq (y + h) u - 2 * rieszSq y u + rieszSq (y - h) u ≤
        (Iic (y + h)).indicator (fun _ => h ^ 2) u := by
  simp only [rieszSq]
  rcases le_or_gt h (y - u) with h1 | h1
  · rw [indicator_of_mem (show u ∈ Iic (y - h) from by simp only [mem_Iic]; linarith),
      indicator_of_mem (show u ∈ Iic (y + h) from by simp only [mem_Iic]; linarith),
      max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
    constructor <;> nlinarith
  rcases le_or_gt 0 (y - u) with h2 | h2
  · rw [indicator_of_notMem (show u ∉ Iic (y - h) from by simp only [mem_Iic]; linarith),
      indicator_of_mem (show u ∈ Iic (y + h) from by simp only [mem_Iic]; linarith),
      max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
    constructor <;> nlinarith
  rcases le_or_gt (-h) (y - u) with h3 | h3
  · rw [indicator_of_notMem (show u ∉ Iic (y - h) from by simp only [mem_Iic]; linarith),
      indicator_of_mem (show u ∈ Iic (y + h) from by simp only [mem_Iic]; linarith),
      max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
    constructor <;> nlinarith
  · rw [indicator_of_notMem (show u ∉ Iic (y - h) from by simp only [mem_Iic]; linarith),
      indicator_of_notMem (show u ∉ Iic (y + h) from by simp only [mem_Iic]; linarith),
      max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
    norm_num

/-- Integrated B-spline bounds: `h² N(y - h) ≤ Δ²_h S(y) ≤ h² N(y + h)`,
`S(y) = ∫ (y - u)₊²/2 dν`. -/
theorem secondDiff_bounds {ν : Measure ℝ} (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) {y h : ℝ} (hh : 0 < h) :
    h ^ 2 * ν.real (Iic (y - h)) ≤
        (∫ u, rieszSq (y + h) u ∂ν) - 2 * (∫ u, rieszSq y u ∂ν) + ∫ u, rieszSq (y - h) u ∂ν ∧
      (∫ u, rieszSq (y + h) u ∂ν) - 2 * (∫ u, rieszSq y u ∂ν) + ∫ u, rieszSq (y - h) u ∂ν ≤
        h ^ 2 * ν.real (Iic (y + h)) := by
  have i1 := integrable_rieszSq hsupp hmom (y + h)
  have i2 := integrable_rieszSq hsupp hmom y
  have i3 := integrable_rieszSq hsupp hmom (y - h)
  have i12 : Integrable (fun u => rieszSq (y + h) u - 2 * rieszSq y u) ν := i1.sub (i2.const_mul 2)
  have hΔ : (∫ u, rieszSq (y + h) u ∂ν) - 2 * (∫ u, rieszSq y u ∂ν) + ∫ u, rieszSq (y - h) u ∂ν =
      ∫ u, (rieszSq (y + h) u - 2 * rieszSq y u + rieszSq (y - h) u) ∂ν := by
    rw [integral_add i12 i3, integral_sub i1 (i2.const_mul 2), integral_const_mul]
  have hi : Integrable (fun u => rieszSq (y + h) u - 2 * rieszSq y u + rieszSq (y - h) u) ν :=
    i12.add i3
  rw [hΔ]
  constructor
  · calc h ^ 2 * ν.real (Iic (y - h)) = ∫ u, (Iic (y - h)).indicator (fun _ => h ^ 2) u ∂ν := by
          rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_comm]
      _ ≤ _ := integral_mono (integrable_indicator_Iic hsupp hmom _ _) hi fun u =>
          (indicator_le_rieszSq_secondDiff hh u).1
  · calc _ ≤ ∫ u, (Iic (y + h)).indicator (fun _ => h ^ 2) u ∂ν :=
          integral_mono hi (integrable_indicator_Iic hsupp hmom _ _) fun u =>
            (indicator_le_rieszSq_secondDiff hh u).2
      _ = h ^ 2 * ν.real (Iic (y + h)) := by
          rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_comm]

/-- Three cubic approximations with error `B` give the second difference within `4B`. -/
theorem abs_secondDiff_sub_le {S : ℝ → ℝ} {α y h B : ℝ}
    (h1 : |S (y + h) - α * (y + h - 1) ^ 3 / 6| ≤ B) (h2 : |S y - α * (y - 1) ^ 3 / 6| ≤ B)
    (h3 : |S (y - h) - α * (y - h - 1) ^ 3 / 6| ≤ B) :
    |S (y + h) - 2 * S y + S (y - h) - α * h ^ 2 * (y - 1)| ≤ 4 * B := by
  have key : S (y + h) - 2 * S y + S (y - h) - α * h ^ 2 * (y - 1) =
      (S (y + h) - α * (y + h - 1) ^ 3 / 6) - 2 * (S y - α * (y - 1) ^ 3 / 6) +
        (S (y - h) - α * (y - h - 1) ^ 3 / 6) := by ring
  rw [key]
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **The Riesz count.**  Let `ν` be supported on `[1, ∞)` with `∫ u⁻² dν < ∞` and Dirichlet
transform `Z`.  If `G = (s - 1) Z` on `Re s > 1` extends holomorphically to `Re s > σ₁`
(`σ₁ < 2/5`) with `‖G(s)‖ ≤ C (1 + |Im s|)^{3/2}` on `2/5 ≤ Re s ≤ 2`, then
`ν([1, x]) = Re G(1) · x + O(x^{4/5})`. -/
theorem exists_abs_count_sub_le {ν : Measure ℝ} [SFinite ν] (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) {G : ℂ → ℂ} {σ₁ : ℝ} (hσ₁ : σ₁ < 2 / 5)
    (hG : DifferentiableOn ℂ G {s : ℂ | σ₁ < s.re})
    (hGZ : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * measureDirichlet ν s) {C : ℝ}
    (hGb : ∀ s : ℂ, 2 / 5 ≤ s.re → s.re ≤ 2 → ‖G s‖ ≤ C * (1 + |s.im|) ^ (3 / 2 : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      ν (Icc 1 x) < ⊤ ∧ |ν.real (Icc 1 x) - (G 1).re * x| ≤ K * x ^ (4 / 5 : ℝ) := by
  obtain ⟨K, hK, hR⟩ := exists_norm_rieszMean_sub_le hsupp hmom hσ₁ hG hGZ hGb
  set α := (G 1).re with hα
  set S : ℝ → ℝ := fun y => ∫ u, rieszSq y u ∂ν with hS
  have hN : ∀ y : ℝ, ν.real (Iic y) = ν.real (Icc 1 y) := fun y => by
    rw [measureReal_def, measureReal_def, measure_Iic_eq hsupp]
  -- the cubic approximation of `S`
  have hSa : ∀ y : ℝ, 1 ≤ y → |S y - α * (y - 1) ^ 3 / 6| ≤ K * y ^ (12 / 5 : ℝ) := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have hSy : y ^ 2 * ∫ u, rieszKernel (u / y) ∂ν = S y := by
      rw [hS, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun u => sq_mul_rieszKernel hy0 u)
    have h := (Complex.abs_re_le_norm _).trans (hR y hy)
    rw [hSy] at h
    have hre : (((S y : ℝ) : ℂ) - G 1 * (((y - 1) ^ 3 / 6 : ℝ) : ℂ)).re =
        S y - α * (y - 1) ^ 3 / 6 := by
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero,
        sub_zero, hα]
      ring
    rwa [hre] at h
  -- small and large `x`
  set x₀ : ℝ := 243 with hx₀
  refine ⟨max (2 * |α| + 32 * K) (ν.real (Icc 1 x₀) + x₀ * |α|), by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hfin : ν (Icc 1 x) < ⊤ := measure_Icc_one_lt_top hmom hx0
  refine ⟨hfin, ?_⟩
  have hNn : 0 ≤ ν.real (Icc 1 x) := measureReal_nonneg
  have hpow1 : 1 ≤ x ^ (4 / 5 : ℝ) := Real.one_le_rpow hx (by norm_num)
  rcases lt_or_ge x x₀ with hsmall | hlarge
  · have hmono : ν.real (Icc 1 x) ≤ ν.real (Icc 1 x₀) :=
      measureReal_mono (Icc_subset_Icc le_rfl hsmall.le)
        (measure_Icc_one_lt_top hmom (by norm_num)).ne
    have hαx : |α * x| ≤ x₀ * |α| := by
      rw [abs_mul, abs_of_pos hx0, mul_comm]
      exact mul_le_mul_of_nonneg_right hsmall.le (abs_nonneg _)
    calc |ν.real (Icc 1 x) - α * x| ≤ |ν.real (Icc 1 x)| + |α * x| := abs_sub _ _
      _ ≤ (ν.real (Icc 1 x₀) + x₀ * |α|) * 1 := by
          rw [abs_of_nonneg hNn, mul_one]; linarith
      _ ≤ max (2 * |α| + 32 * K) (ν.real (Icc 1 x₀) + x₀ * |α|) * x ^ (4 / 5 : ℝ) :=
          mul_le_mul (le_max_right _ _) hpow1 zero_le_one (by positivity)
  · -- `x = t⁵`, step `h = t⁴`
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x ^ (5⁻¹ : ℝ) := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have hxt : x = t ^ 5 := by
      rw [ht]; exact (Real.rpow_inv_natCast_pow (n := 5) hx0.le (by norm_num)).symm
    have ht3 : 3 ≤ t := by
      by_contra hlt
      have hlt := lt_of_not_ge hlt
      have := pow_lt_pow_left₀ hlt ht0 (n := 5) (by norm_num)
      norm_num at this
      linarith
    have hrp : ∀ r : ℝ, x ^ r = t ^ (5 * r) := fun r => by
      rw [hxt, ← Real.rpow_natCast t 5, ← Real.rpow_mul ht0]; norm_num
    have h45 : x ^ (4 / 5 : ℝ) = t ^ 4 := by
      rw [hrp, show (5 : ℝ) * (4 / 5) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    set h : ℝ := t ^ 4 with hh
    have hh1 : 1 ≤ h := one_le_pow₀ (by linarith)
    have hh0 : 0 < h := by linarith
    have h2h : 3 * h ≤ x := by
      rw [hxt, hh, show t ^ 5 = t * t ^ 4 by ring]
      exact mul_le_mul_of_nonneg_right ht3 (pow_nonneg ht0 4)
    -- `y^{12/5} ≤ 8 t^{12}` on `[0, 2x]`
    have hbig : ∀ y : ℝ, 0 ≤ y → y ≤ 2 * x → K * y ^ (12 / 5 : ℝ) ≤ K * (8 * t ^ 12) := by
      intro y hy0 hy2
      refine mul_le_mul_of_nonneg_left ?_ hK
      calc y ^ (12 / 5 : ℝ) ≤ (2 * x) ^ (12 / 5 : ℝ) := Real.rpow_le_rpow hy0 hy2 (by norm_num)
        _ = 2 ^ (12 / 5 : ℝ) * t ^ 12 := by
            rw [Real.mul_rpow (by norm_num) hx0.le, hrp,
              show (5 : ℝ) * (12 / 5) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        _ ≤ 2 ^ (3 : ℝ) * t ^ 12 := by
            gcongr
            · norm_num
            · norm_num
        _ = 8 * t ^ 12 := by norm_num
    have hE : 4 * (K * (8 * t ^ 12)) = h ^ 2 * (32 * K * t ^ 4) := by rw [hh]; ring
    -- upper bound at the centre `x + h`
    have hup := (secondDiff_bounds hsupp hmom (y := x + h) hh0).1
    rw [add_sub_cancel_right] at hup
    have hΔup := abs_secondDiff_sub_le (S := S) (α := α) (y := x + h) (h := h)
      ((hSa _ (by linarith)).trans (hbig _ (by linarith) (by linarith)))
      ((hSa _ (by linarith)).trans (hbig _ (by linarith) (by linarith)))
      ((hSa _ (by linarith)).trans (hbig _ (by linarith) (by linarith)))
    -- lower bound at the centre `x - h`
    have hlo := (secondDiff_bounds hsupp hmom (y := x - h) hh0).2
    rw [sub_add_cancel] at hlo
    have hΔlo := abs_secondDiff_sub_le (S := S) (α := α) (y := x - h) (h := h)
      ((hSa _ (by linarith)).trans (hbig _ (by linarith) (by linarith)))
      ((hSa _ (by linarith)).trans (hbig _ (by linarith) (by linarith)))
      ((hSa _ (by linarith)).trans (hbig _ (by linarith) (by linarith)))
    rw [hE, add_sub_cancel_right] at hΔup
    rw [hE, sub_add_cancel] at hΔlo
    rw [hN] at hup hlo
    simp only [hS] at hup hlo hΔup hΔlo
    rw [abs_le] at hΔup hΔlo
    have hh2 : 0 < h ^ 2 := by positivity
    -- divide the sandwich by `h²`
    have hU : ν.real (Icc 1 x) - α * x ≤ α * (h - 1) + 32 * K * t ^ 4 := by
      have : h ^ 2 * ν.real (Icc 1 x) ≤ h ^ 2 * (α * (x + h - 1) + 32 * K * t ^ 4) := by
        linarith [hΔup.2]
      have := le_of_mul_le_mul_left this hh2
      linarith
    have hL : -(α * (h + 1)) - 32 * K * t ^ 4 ≤ ν.real (Icc 1 x) - α * x := by
      have : h ^ 2 * (α * (x - h - 1) - 32 * K * t ^ 4) ≤ h ^ 2 * ν.real (Icc 1 x) := by
        linarith [hΔlo.1]
      have := le_of_mul_le_mul_left this hh2
      linarith
    have hαh : |α| * (h + 1) ≤ 2 * |α| * h := by nlinarith [abs_nonneg α]
    rw [h45]
    rw [abs_le]
    constructor
    · have : -(|α| * (h + 1)) ≤ -(α * (h + 1)) :=
        neg_le_neg (mul_le_mul_of_nonneg_right (le_abs_self α) (by linarith))
      have hm : (2 * |α| + 32 * K) * h ≤
          max (2 * |α| + 32 * K) (ν.real (Icc 1 x₀) + x₀ * |α|) * h :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hh0.le
      nlinarith
    · have : α * (h - 1) ≤ |α| * (h + 1) := by
        have := mul_le_mul_of_nonneg_right (le_abs_self α) (show 0 ≤ h - 1 by linarith)
        nlinarith [abs_nonneg α]
      have hm : (2 * |α| + 32 * K) * h ≤
          max (2 * |α| + 32 * K) (ν.real (Icc 1 x₀) + x₀ * |α|) * h :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hh0.le
      nlinarith

end GaloisForLFunctions.EulerFETransportTheory
