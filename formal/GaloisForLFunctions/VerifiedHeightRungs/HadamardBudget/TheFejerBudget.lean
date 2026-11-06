import GaloisForLFunctions.RHTower.ZetaFejerWeight
import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCount
import GaloisForLFunctions.RHTower.XiEndpointOffLineQuartetHeightGap
import GaloisForLFunctions.RHTower.DigammaBinetFourthOrder
import GaloisForLFunctions.RHTower.PolePurchaseLogDerivIdentity
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.RHTower.XiLogDerivFactorization

/-!
# The Fejér budget of an off-line zero

For `a > ½`, `σ = ½ + a`, every zero contributes a nonnegative Poisson term to the Hadamard sum
`Re ξ'/ξ(σ + iy)`. An off-line zero and its reflection have the same ordinate, so they contribute
twice, where a simple on-line zero contributes once.

Averaging over `y` against the Fejér density `K_L` keeps positivity and turns the Dirichlet series of
`ζ'/ζ` into a finite polynomial, since `∫ K_L(τ) cos(θτ) dτ = (1 − |θ|/L)₊`. So an off-line zero at
height `γ ≥ 1`, `γ² ≥ (2 + σ)²`, forces (`two_mul_fejerLaplace_le_of_offLine`)

`2 ∫₀^L (1 − u/L) e^{−au} du ≤ archBudget a L γ − Σ_{log n < L} Λ(n) n^{−σ} (1 − log n/L) cos(γ log n)`,

where `archBudget a L γ = ½ log(γ/2π) + O(1/γ)`. The left side is `≈ 2/a`.

The averaging is done symmetrically in `τ`: the odd part of the logarithm cancels, which is why the
error of the archimedean side is `O(1/γ)` and not `O(1/√γ)`.
-/

open Complex MeasureTheory Set Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget

open _root_.RHTower _root_.RHTower.FejerWeight GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The Fejér density -/

/-- The Fejér probability density of band `L`. -/
def fejerK (L τ : ℝ) : ℝ := fejerBandProfile L τ / (2 * Real.pi)

variable {L : ℝ}

theorem fejerK_nonneg (hL : 0 < L) (τ : ℝ) : 0 ≤ fejerK L τ :=
  div_nonneg (fejerBandProfile_nonneg hL τ) (by positivity)

theorem fejerK_neg (L τ : ℝ) : fejerK L (-τ) = fejerK L τ := by
  unfold fejerK fejerBandProfile
  by_cases h : τ = 0
  · simp [h]
  · simp [h, Real.cos_neg]

theorem continuous_fejerK (hL : 0 < L) : Continuous (fejerK L) :=
  (continuous_fejerBandProfile hL).div_const _

theorem integrable_fejerK (hL : 0 < L) : Integrable (fejerK L) :=
  (integrable_fejerBandProfile hL).div_const _

theorem fejerK_le_inv (hL : 0 < L) {τ : ℝ} (hτ : τ ≠ 0) :
    fejerK L τ ≤ 2 / (Real.pi * L * τ ^ 2) := by
  have h := fejerBandProfile_le_inv hL hτ
  unfold fejerK
  have hπ := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hpos : 0 < τ ^ 2 * L := by positivity
  rw [le_div_iff₀ hpos] at h
  nlinarith

private theorem integrable_profile_mul_cexp (hL : 0 < L) (y : ℝ) :
    Integrable fun v : ℝ => ((fejerBandProfile L v : ℝ) : ℂ) * cexp (-(I * y * v)) := by
  refine (integrable_fejerBandProfile hL).ofReal.mul_bdd
    (c := 1) ?_ (ae_of_all _ fun v => ?_)
  · exact (by fun_prop : Continuous fun v : ℝ => cexp (-(I * y * v))).aestronglyMeasurable
  · have : -(I * (y : ℂ) * v) = ((-(y * v) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]

private theorem cexp_neg_mul (y v : ℝ) :
    cexp (-(I * y * v)) = ((Real.cos (y * v) : ℝ) : ℂ) - ((Real.sin (y * v) : ℝ) : ℂ) * I := by
  have : -(I * (y : ℂ) * v) = ((-(y * v) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

private theorem re_ofReal_mul_sub (F c s : ℝ) :
    ((F : ℂ) * ((c : ℂ) - (s : ℂ) * I)).re = F * c := by
  simp [Complex.mul_re]

private theorem im_ofReal_mul_sub (F c s : ℝ) :
    ((F : ℂ) * ((c : ℂ) - (s : ℂ) * I)).im = -(F * s) := by
  simp [Complex.mul_im]

private theorem two_pi_triangle_eq (T : ℝ) :
    2 * (Real.pi : ℂ) * (T : ℂ) = ((2 * Real.pi * T : ℝ) : ℂ) := by
  push_cast
  ring

/-- `∫ K_L(τ) cos(yτ) dτ = (1 − |y|/L)₊`. -/
theorem integral_fejerK_mul_cos (hL : 0 < L) (y : ℝ) :
    ∫ τ, fejerK L τ * Real.cos (y * τ) = triangleFn L y := by
  have h := integral_fejerBandProfile_mul_cexp hL y
  rw [two_pi_triangle_eq] at h
  have hre := congrArg Complex.re h
  have hint := integrable_profile_mul_cexp hL y
  rw [Complex.ofReal_re, ← Complex.reCLM_apply, ← reCLM.integral_comp_comm hint] at hre
  have e : ∀ v : ℝ, Complex.reCLM (((fejerBandProfile L v : ℝ) : ℂ) * cexp (-(I * y * v))) =
      fejerBandProfile L v * Real.cos (y * v) := fun v => by
    rw [Complex.reCLM_apply, cexp_neg_mul, re_ofReal_mul_sub]
  simp_rw [e] at hre
  unfold fejerK
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, hre]
  have := Real.pi_pos
  field_simp

/-- `∫ K_L(τ) sin(yτ) dτ = 0`. -/
theorem integral_fejerK_mul_sin (hL : 0 < L) (y : ℝ) :
    ∫ τ, fejerK L τ * Real.sin (y * τ) = 0 := by
  have h := integral_fejerBandProfile_mul_cexp hL y
  rw [two_pi_triangle_eq] at h
  have him := congrArg Complex.im h
  have hint := integrable_profile_mul_cexp hL y
  rw [Complex.ofReal_im, ← Complex.imCLM_apply, ← imCLM.integral_comp_comm hint] at him
  have e : ∀ v : ℝ, Complex.imCLM (((fejerBandProfile L v : ℝ) : ℂ) * cexp (-(I * y * v))) =
      -(fejerBandProfile L v * Real.sin (y * v)) := fun v => by
    rw [Complex.imCLM_apply, cexp_neg_mul, im_ofReal_mul_sub]
  simp_rw [e] at him
  rw [integral_neg, neg_eq_zero] at him
  unfold fejerK
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, him, zero_div]

theorem integrable_fejerK_mul_bdd (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ τ, |f τ| ≤ C) : Integrable fun τ => fejerK L τ * f τ :=
  (integrable_fejerK hL).mul_bdd (c := C) hf.aestronglyMeasurable
    (ae_of_all _ fun τ => by simpa [Real.norm_eq_abs] using hC τ)

/-- The total mass of the density. -/
theorem integral_fejerK (hL : 0 < L) : ∫ τ, fejerK L τ = 1 := by
  have h := integral_fejerK_mul_cos hL 0
  simpa [triangleFn] using h

/-- Averaging a cosine at a shifted height multiplies it by the Fejér weight. -/
theorem integral_fejerK_mul_cos_add (hL : 0 < L) (γ θ : ℝ) :
    ∫ τ, fejerK L τ * Real.cos ((γ + τ) * θ) = triangleFn L θ * Real.cos (γ * θ) := by
  have e : ∀ τ, fejerK L τ * Real.cos ((γ + τ) * θ) =
      Real.cos (γ * θ) * (fejerK L τ * Real.cos (θ * τ)) -
        Real.sin (γ * θ) * (fejerK L τ * Real.sin (θ * τ)) := by
    intro τ
    rw [show (γ + τ) * θ = γ * θ + θ * τ by ring, Real.cos_add]
    ring
  simp_rw [e]
  have hc := integrable_fejerK_mul_bdd hL (f := fun τ => Real.cos (θ * τ)) (by fun_prop)
    (C := 1) (fun τ => Real.abs_cos_le_one _)
  have hs := integrable_fejerK_mul_bdd hL (f := fun τ => Real.sin (θ * τ)) (by fun_prop)
    (C := 1) (fun τ => Real.abs_sin_le_one _)
  rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul,
    integral_fejerK_mul_cos hL, integral_fejerK_mul_sin hL]
  ring

/-! ## The Laplace transform of the Fejér weight -/

/-- `∫₀^∞ (1 − u/L)₊ e^{−xu} du`. -/
def fejerLaplace (L x : ℝ) : ℝ := ∫ u in Ioi 0, triangleFn L u * Real.exp (-x * u)

private theorem integrableOn_triangle_mul_exp (hL : 0 < L) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u => triangleFn L u * Real.exp (-x * u)) (Ioi 0) := by
  have h := integrableOn_exp_mul_Ioi (a := -x) (by linarith) 0
  refine Integrable.bdd_mul h (c := 1) (continuous_triangleFn L).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (triangleFn_nonneg L u)]
  exact triangleFn_le_one hL u

/-- The Lorentz kernel is the Laplace transform of `e^{−xu} cos(τu)`. -/
theorem lorentz_eq_integral {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    x / (x ^ 2 + τ ^ 2) = ∫ u in Ioi 0, Real.exp (-x * u) * Real.cos (τ * u) := by
  have hre : ((-(x : ℂ) + ((-τ : ℝ) : ℂ) * I)).re < 0 := by simp [hx]
  have h := integral_exp_mul_complex_Ioi hre 0
  have hint : IntegrableOn (fun u : ℝ =>
      cexp ((-(x : ℂ) + ((-τ : ℝ) : ℂ) * I) * (u : ℂ))) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hre 0
  have hval := congrArg Complex.re h
  rw [← Complex.reCLM_apply, ← reCLM.integral_comp_comm hint] at hval
  have e : ∀ u : ℝ, Complex.reCLM (cexp ((-(x : ℂ) + ((-τ : ℝ) : ℂ) * I) * (u : ℂ))) =
      Real.exp (-x * u) * Real.cos (τ * u) := by
    intro u
    have hz : (-(x : ℂ) + ((-τ : ℝ) : ℂ) * I) * (u : ℂ) =
        ((-x * u : ℝ) : ℂ) + ((-(τ * u) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [Complex.reCLM_apply, hz, Complex.exp_re]
    have h1 : (((-x * u : ℝ) : ℂ) + ((-(τ * u) : ℝ) : ℂ) * I).re = -x * u := by simp
    have h2 : (((-x * u : ℝ) : ℂ) + ((-(τ * u) : ℝ) : ℂ) * I).im = -(τ * u) := by simp
    rw [h1, h2, Real.cos_neg]
  simp_rw [e] at hval
  rw [hval]
  have hc : -cexp ((-(x : ℂ) + ((-τ : ℝ) : ℂ) * I) * ((0 : ℝ) : ℂ)) /
      (-(x : ℂ) + ((-τ : ℝ) : ℂ) * I) = ((x : ℂ) + (τ : ℂ) * I)⁻¹ := by
    have e2 : -(x : ℂ) + ((-τ : ℝ) : ℂ) * I = -((x : ℂ) + (τ : ℂ) * I) := by
      push_cast
      ring
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, e2, neg_div_neg_eq, one_div]
  rw [hc, Complex.inv_re, Complex.normSq_apply]
  have h1 : ((x : ℂ) + (τ : ℂ) * I).re = x := by simp
  have h2 : ((x : ℂ) + (τ : ℂ) * I).im = τ := by simp
  rw [h1, h2]
  ring_nf

/-- **Laplace identity.** `∫ K_L(τ) x/(x² + τ²) dτ = ∫₀^∞ (1 − u/L)₊ e^{−xu} du`. -/
theorem integral_fejerK_mul_lorentz (hL : 0 < L) {x : ℝ} (hx : 0 < x) :
    ∫ τ, fejerK L τ * (x / (x ^ 2 + τ ^ 2)) = fejerLaplace L x := by
  have hexp : Integrable (fun u => Real.exp (-x * u)) (volume.restrict (Ioi 0)) :=
    integrableOn_exp_mul_Ioi (a := -x) (by linarith) 0
  have hswap : Integrable (Function.uncurry fun (τ u : ℝ) =>
      fejerK L τ * (Real.exp (-x * u) * Real.cos (τ * u)))
      (volume.prod (volume.restrict (Ioi 0))) := by
    refine ((integrable_fejerK hL).mul_prod hexp).mono' ?_ (ae_of_all _ fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have := continuous_fejerK hL
      simp only [Function.uncurry_def]
      fun_prop
    · simp only [Function.uncurry_def, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (fejerK_nonneg hL _), abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left ?_ (fejerK_nonneg hL _)
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  calc ∫ τ, fejerK L τ * (x / (x ^ 2 + τ ^ 2))
      = ∫ τ, ∫ u in Ioi 0, fejerK L τ * (Real.exp (-x * u) * Real.cos (τ * u)) := by
        refine integral_congr_ae (ae_of_all _ fun τ => ?_)
        simp only
        rw [lorentz_eq_integral hx τ, integral_const_mul]
    _ = ∫ u in Ioi 0, ∫ τ, fejerK L τ * (Real.exp (-x * u) * Real.cos (τ * u)) :=
        integral_integral_swap hswap
    _ = fejerLaplace L x := by
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only
        have e : ∀ τ, fejerK L τ * (Real.exp (-x * u) * Real.cos (τ * u)) =
            Real.exp (-x * u) * (fejerK L τ * Real.cos (u * τ)) := by
          intro τ
          rw [mul_comm τ u]
          ring
        simp_rw [e]
        rw [integral_const_mul, integral_fejerK_mul_cos hL, mul_comm]

/-- Convexity of the Laplace transform in `x`. -/
theorem two_mul_fejerLaplace_le (hL : 0 < L) {a δ : ℝ} (h1 : 0 < a - δ) (h2 : 0 < a + δ) :
    2 * fejerLaplace L a ≤ fejerLaplace L (a - δ) + fejerLaplace L (a + δ) := by
  have ha : 0 < a := by linarith
  unfold fejerLaplace
  rw [← integral_add (integrableOn_triangle_mul_exp hL h1) (integrableOn_triangle_mul_exp hL h2),
    ← integral_const_mul]
  refine integral_mono ((integrableOn_triangle_mul_exp hL ha).const_mul 2)
    ((integrableOn_triangle_mul_exp hL h1).add (integrableOn_triangle_mul_exp hL h2)) fun u => ?_
  have hcosh := Real.one_le_cosh (δ * u)
  rw [Real.cosh_eq] at hcosh
  have e1 : Real.exp (-(a - δ) * u) = Real.exp (-a * u) * Real.exp (δ * u) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(a + δ) * u) = Real.exp (-a * u) * Real.exp (-(δ * u)) := by
    rw [← Real.exp_add]; ring_nf
  have hT := triangleFn_nonneg L u
  have hE := (Real.exp_pos (-a * u)).le
  have h3 := mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) ≤ Real.exp (δ * u) +
      Real.exp (-(δ * u))) (mul_nonneg hT hE)
  simp only [e1, e2]
  linarith only [h3]

/-- Closed form of the Laplace transform. -/
theorem fejerLaplace_eq (hL : 0 < L) {x : ℝ} (hx : 0 < x) :
    fejerLaplace L x = 1 / x - (1 - Real.exp (-x * L)) / (x ^ 2 * L) := by
  have hsplit : (fun u => triangleFn L u * Real.exp (-x * u)) =ᵐ[volume.restrict (Ioi 0)]
      Set.indicator (Ioc 0 L) fun u => (1 - u / L) * Real.exp (-x * u) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)
    by_cases huL : u ≤ L
    · rw [Set.indicator_of_mem (show u ∈ Ioc 0 L from ⟨hu, huL⟩)]
      show triangleFn L u * Real.exp (-x * u) = _
      congr 1
      unfold triangleFn
      rw [abs_of_pos hu, max_eq_left]
      rw [sub_nonneg, div_le_one hL]
      exact huL
    · rw [Set.indicator_of_notMem (show u ∉ Ioc 0 L from fun h => huL h.2)]
      show triangleFn L u * Real.exp (-x * u) = 0
      rw [triangleFn_eq_zero hL (by rw [abs_of_pos hu]; linarith), zero_mul]
  unfold fejerLaplace
  rw [integral_congr_ae hsplit, setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc 0 L = Ioc 0 L from by
      ext u; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; tauto,
    ← intervalIntegral.integral_of_le hL.le]
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) L, HasDerivAt
      (fun u => -(Real.exp (-x * u) * (1 - u / L)) / x + Real.exp (-x * u) / (x ^ 2 * L))
      ((1 - u / L) * Real.exp (-x * u)) u := by
    intro u _
    have he : HasDerivAt (fun u => Real.exp (-x * u)) (Real.exp (-x * u) * (-x)) u := by
      have := ((hasDerivAt_id u).const_mul (-x)).exp
      simpa using this
    have hl : HasDerivAt (fun u => 1 - u / L) (-(1 / L)) u := by
      have := (hasDerivAt_id u).div_const L
      simpa using this.const_sub 1
    refine (((he.mul hl).neg.div_const x).add (he.div_const (x ^ 2 * L))).congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun u => (1 - u / L) * Real.exp (-x * u)) volume 0 L :=
    (by fun_prop : Continuous fun u => (1 - u / L) * Real.exp (-x * u)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [div_self hL.ne', mul_zero, Real.exp_zero, zero_div, sub_zero, sub_self, mul_one,
    neg_zero]
  field_simp
  ring

/-! ## The Hadamard pair -/

/-- **An off-line zero counts twice.** At every point `σ + iy` right of the critical strip, the
pair of an off-line zero and its reflection is at most `Re ξ'/ξ`. -/
theorem xiLinePairRe_le_re_logDeriv_xi {a : ℝ} (ha : 1 / 2 < a) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) (y : ℝ) :
    xiLinePairRe a ((q.1 : ℂ).re - 1 / 2) (y - (q.1 : ℂ).im) ≤
      (logDeriv xi (((1 / 2 + a : ℝ) : ℂ) + (y : ℂ) * I)).re := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = ((1 / 2 + a : ℝ) : ℂ) + (y : ℂ) * I := ⟨_, rfl⟩
  have hsre : s.re = 1 / 2 + a := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  rw [← hs]
  have hsa : s.re - 1 / 2 = a := by rw [hsre]; ring
  have hxi : xi s ≠ 0 := xi_ne_zero_of_one_le_re (by rw [hsre]; linarith)
  have hnn (r : XiZeroCopy) :
      0 ≤ xiLinePairRe (s.re - 1 / 2) ((r.1 : ℂ).re - 1 / 2) (s.im - (r.1 : ℂ).im) := by
    have h0 := xiZeroCopy_re_pos r
    have h1 := xiZeroCopy_re_lt_one r
    rw [hsa]
    unfold xiLinePairRe
    apply add_nonneg
    · exact div_nonneg (by linarith) (by positivity)
    · exact div_nonneg (by linarith) (by positivity)
  have hsum := sum_pair_le_two_mul_re_logDeriv_xi hxi hnn
    ({q, xiZeroCopyLineConjEquiv q} : Finset XiZeroCopy)
  rw [Finset.sum_pair (xiZeroCopy_ne_lineConj_of_re_ne_half q hoff)] at hsum
  have hJ : xiLinePairRe (s.re - 1 / 2) (((xiZeroCopyLineConjEquiv q).1 : ℂ).re - 1 / 2)
      (s.im - ((xiZeroCopyLineConjEquiv q).1 : ℂ).im) =
        xiLinePairRe (s.re - 1 / 2) ((q.1 : ℂ).re - 1 / 2) (s.im - (q.1 : ℂ).im) := by
    rw [xiZero_lineConj_eq]
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re,
      Complex.sub_im, Complex.one_im, Complex.conj_im]
    have e : 1 - (q.1 : ℂ).re - 1 / 2 = -((q.1 : ℂ).re - 1 / 2) := by ring
    rw [e]
    unfold xiLinePairRe
    rw [sub_neg_eq_add, show s.re - 1 / 2 + -((q.1 : ℂ).re - 1 / 2) =
      s.re - 1 / 2 - ((q.1 : ℂ).re - 1 / 2) by ring]
    ring
  rw [hJ, hsa, hsim] at hsum
  linarith only [hsum]

/-! ## The archimedean side -/

/-- Retaining the sign of the Stirling corrections: `Re ψ(w) ≤ log |w| + 1/(120 x⁴)` for
`Re w = x ≥ 1`. -/
theorem re_digamma_le_log_norm {w : ℂ} (hw : 1 ≤ w.re) :
    (Complex.digamma w).re ≤ Real.log ‖w‖ + 1 / (120 * w.re ^ 4) := by
  have hpos : 0 < w.re := by linarith
  have hS := DigammaBinet.norm_digamma_sub_stirling_le hpos
  have hre := (Complex.re_le_norm _).trans hS
  have hne : w ≠ 0 := fun h => by simp [h] at hpos
  simp only [Complex.add_re, Complex.sub_re] at hre
  rw [Complex.log_re] at hre
  have hN : Complex.normSq w = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have hN0 : 0 < Complex.normSq w := Complex.normSq_pos.mpr hne
  have h1 : (1 / (2 * w)).re = w.re / (2 * Complex.normSq w) := by
    have e : 1 / (2 * w) = ((1 / 2 : ℝ) : ℂ) * w⁻¹ := by
      push_cast
      field_simp
    rw [e, Complex.re_ofReal_mul, Complex.inv_re]
    field_simp
  have h2 : (1 / (12 * w ^ 2)).re =
      (w.re ^ 2 - w.im ^ 2) / (12 * Complex.normSq w ^ 2) := by
    have e : 1 / (12 * w ^ 2) = ((1 / 12 : ℝ) : ℂ) * (w ^ 2)⁻¹ := by
      push_cast
      field_simp
    have hsq : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
      rw [pow_two, Complex.mul_re]; ring
    have hnq : Complex.normSq (w ^ 2) = Complex.normSq w ^ 2 := map_pow _ _ _
    rw [e, Complex.re_ofReal_mul, Complex.inv_re, hsq, hnq]
    field_simp
  rw [h1, h2] at hre
  have hcorr : 0 ≤ w.re / (2 * Complex.normSq w) +
      (w.re ^ 2 - w.im ^ 2) / (12 * Complex.normSq w ^ 2) := by
    have e : w.re / (2 * Complex.normSq w) +
        (w.re ^ 2 - w.im ^ 2) / (12 * Complex.normSq w ^ 2) =
          (6 * w.re * Complex.normSq w + (w.re ^ 2 - w.im ^ 2)) /
            (12 * Complex.normSq w ^ 2) := by
      field_simp
      ring
    rw [e]
    apply div_nonneg _ (by positivity)
    have h3 : 0 ≤ (w.re - 1) * Complex.normSq w := mul_nonneg (by linarith) hN0.le
    have him := sq_nonneg w.im
    have hr := sq_nonneg w.re
    nlinarith only [h3, hN, him, hr]
  linarith only [hre, hcorr]

/-- The archimedean envelope of `Re ξ'/ξ`, with the pole at `0` absorbed by the digamma shift. -/
theorem re_logDeriv_xi_le {σ y : ℝ} (hσ : 1 < σ) :
    (logDeriv xi ((σ : ℂ) + (y : ℂ) * I)).re ≤
      (σ - 1) / ((σ - 1) ^ 2 + y ^ 2) - Real.log Real.pi / 2 +
        1 / 4 * Real.log ((1 + σ / 2) ^ 2 + y ^ 2 / 4) + 1 / (240 * (1 + σ / 2) ^ 4) +
        (logDeriv riemannZeta ((σ : ℂ) + (y : ℂ) * I)).re := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (σ : ℂ) + (y : ℂ) * I := ⟨_, rfl⟩
  rw [← hs]
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hs1 : 1 < s.re := by rw [hsre]; exact hσ
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs1; linarith
  have hnotPole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.div_ofNat_re, hsre, Complex.neg_re, Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hrec := Complex.digamma_apply_add_one (s / 2) hnotPole
  have hinv : (s / 2)⁻¹ = 2 / s := by field_simp
  rw [hinv] at hrec
  have hdig : Complex.digamma (s / 2) / 2 = Complex.digamma (s / 2 + 1) / 2 - 1 / s := by
    rw [hrec]
    field_simp
    ring
  rw [logDeriv_xi_fourFactor hs1, hdig]
  have h1 : (1 / s + (1 / (s - 1)) - (Real.log Real.pi : ℂ) / 2 +
      (Complex.digamma (s / 2 + 1) / 2 - 1 / s) + logDeriv riemannZeta s).re =
      (1 / (s - 1)).re - Real.log Real.pi / 2 + (Complex.digamma (s / 2 + 1)).re / 2 +
        (logDeriv riemannZeta s).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re]
    ring
  have hval : (1 / (s - 1)).re = (σ - 1) / ((σ - 1) ^ 2 + y ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hsre, hsim, sub_zero]
    ring_nf
  have hwre : (s / 2 + 1).re = 1 + σ / 2 := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, hsre]
    ring
  have hwim : (s / 2 + 1).im = y / 2 := by
    simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, hsim]
    ring
  have hd := re_digamma_le_log_norm (w := s / 2 + 1) (by rw [hwre]; linarith)
  have hnorm : Real.log ‖s / 2 + 1‖ = 1 / 2 * Real.log ((1 + σ / 2) ^ 2 + y ^ 2 / 4) := by
    have hsq : ‖s / 2 + 1‖ ^ 2 = (1 + σ / 2) ^ 2 + y ^ 2 / 4 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hwre, hwim]
      ring
    rw [← hsq, Real.log_pow]
    push_cast
    ring
  rw [hwre, hnorm] at hd
  have e120 : 1 / (240 * (1 + σ / 2) ^ 4) = 1 / (120 * (1 + σ / 2) ^ 4) / 2 := by
    field_simp
    norm_num
  rw [h1, hval, e120]
  linarith only [hd]

/-! ## The prime side -/

/-- The Dirichlet coefficient at `σ`. -/
def primeCoeff (σ : ℝ) (n : ℕ) : ℝ := vonMangoldt n * (n : ℝ) ^ (-σ)

theorem primeCoeff_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ primeCoeff σ n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem summable_primeCoeff {σ : ℝ} (hσ : 1 < σ) : Summable (primeCoeff σ) := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
  have hre := h.norm
  refine hre.congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [primeCoeff]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, primeCoeff, Real.rpow_neg hnpos.le,
      div_eq_mul_inv]

/-- The cosine series of `−Re ζ'/ζ`. -/
def primeSeries (σ y : ℝ) : ℝ := ∑' n : ℕ, primeCoeff σ n * Real.cos (y * Real.log n)

/-- `Re ζ'/ζ(σ + iy)` as a cosine series. -/
theorem re_logDeriv_riemannZeta_eq {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    (logDeriv riemannZeta ((σ : ℂ) + (y : ℂ) * I)).re = -primeSeries σ y := by
  have hs : 1 < ((σ : ℂ) + (y : ℂ) * I).re := by simpa using hσ
  rw [logDeriv_riemannZeta_eq_neg_LSeries hs, Complex.neg_re]
  unfold LSeries
  rw [Complex.re_tsum (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)]
  simp_rw [re_vonMangoldt_line_term]
  rfl

/-- The smoothed prime polynomial of a height. -/
def primeSum (σ L γ : ℝ) : ℝ :=
  ∑' n : ℕ, primeCoeff σ n * triangleFn L (Real.log n) * Real.cos (γ * Real.log n)

theorem continuous_primeSeries {σ : ℝ} (hσ : 1 < σ) : Continuous (primeSeries σ) := by
  refine continuous_tsum (fun n => by fun_prop) (summable_primeCoeff hσ) fun n y => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (primeCoeff_nonneg σ n)]
  exact mul_le_of_le_one_right (primeCoeff_nonneg σ n) (Real.abs_cos_le_one _)

theorem abs_primeSeries_le {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    |primeSeries σ y| ≤ ∑' n, primeCoeff σ n := by
  have hs := summable_primeCoeff hσ
  have hb : ∀ n : ℕ, ‖primeCoeff σ n * Real.cos (y * Real.log n)‖ ≤ primeCoeff σ n := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (primeCoeff_nonneg σ n)]
    exact mul_le_of_le_one_right (primeCoeff_nonneg σ n) (Real.abs_cos_le_one _)
  have hsum : Summable fun n : ℕ => ‖primeCoeff σ n * Real.cos (y * Real.log n)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hb hs)

/-- Averaging the Dirichlet series termwise: only `log n < L` survive. -/
theorem integral_fejerK_mul_primeSeries (hL : 0 < L) {σ : ℝ} (hσ : 1 < σ) (γ : ℝ) :
    ∫ τ, fejerK L τ * primeSeries σ (γ + τ) = primeSum σ L γ := by
  have hs := summable_primeCoeff hσ
  have hint (n : ℕ) : Integrable fun τ => fejerK L τ *
      (primeCoeff σ n * Real.cos ((γ + τ) * Real.log n)) := by
    refine integrable_fejerK_mul_bdd hL (by fun_prop) (C := primeCoeff σ n) fun τ => ?_
    rw [abs_mul, abs_of_nonneg (primeCoeff_nonneg σ n)]
    exact mul_le_of_le_one_right (primeCoeff_nonneg σ n) (Real.abs_cos_le_one _)
  have hnorm (n : ℕ) : ∫ τ, ‖fejerK L τ * (primeCoeff σ n *
      Real.cos ((γ + τ) * Real.log n))‖ ≤ primeCoeff σ n := by
    calc _ ≤ ∫ τ, fejerK L τ * primeCoeff σ n := by
          refine integral_mono (hint n).norm ((integrable_fejerK hL).mul_const _) fun τ => ?_
          simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (fejerK_nonneg hL τ),
            abs_of_nonneg (primeCoeff_nonneg σ n)]
          refine mul_le_mul_of_nonneg_left ?_ (fejerK_nonneg hL τ)
          exact mul_le_of_le_one_right (primeCoeff_nonneg σ n) (Real.abs_cos_le_one _)
      _ = _ := by rw [integral_mul_const, integral_fejerK hL, one_mul]
  have hsum : Summable fun n : ℕ => ∫ τ, ‖fejerK L τ * (primeCoeff σ n *
      Real.cos ((γ + τ) * Real.log n))‖ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hnorm hs
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hmul : ∀ τ, fejerK L τ * primeSeries σ (γ + τ) =
      ∑' n : ℕ, fejerK L τ * (primeCoeff σ n * Real.cos ((γ + τ) * Real.log n)) :=
    fun τ => tsum_mul_left.symm
  simp_rw [hmul]
  rw [← hswap]
  unfold primeSum
  refine tsum_congr fun n => ?_
  have e : ∀ τ, fejerK L τ * (primeCoeff σ n * Real.cos ((γ + τ) * Real.log n)) =
      primeCoeff σ n * (fejerK L τ * Real.cos ((γ + τ) * Real.log n)) := fun τ => by ring
  simp_rw [e]
  rw [integral_const_mul, integral_fejerK_mul_cos_add hL]
  ring

/-- The reflected average gives the same polynomial. -/
theorem integral_fejerK_mul_primeSeries_sub (hL : 0 < L) {σ : ℝ} (hσ : 1 < σ) (γ : ℝ) :
    ∫ τ, fejerK L τ * primeSeries σ (γ - τ) = primeSum σ L γ := by
  rw [← integral_fejerK_mul_primeSeries hL hσ γ,
    ← integral_neg_eq_self (fun τ => fejerK L τ * primeSeries σ (γ + τ)) volume]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only [fejerK_neg, sub_eq_add_neg]

/-! ## The tail of the logarithm -/

/-- The tail `|τ|^{−3/2}` outside `[−R, R]`. -/
def tailFn (R τ : ℝ) : ℝ := if R < |τ| then |τ| ^ (-(3 / 2) : ℝ) else 0

theorem tailFn_nonneg (R τ : ℝ) : 0 ≤ tailFn R τ := by
  unfold tailFn
  split_ifs
  · positivity
  · exact le_rfl

theorem integrable_tailFn {R : ℝ} (hR : 1 ≤ R) : Integrable (tailFn R) := by
  have hmeas : Measurable (tailFn R) := by
    unfold tailFn
    refine Measurable.ite ?_ (by fun_prop) measurable_const
    exact measurableSet_lt measurable_const (by fun_prop)
  have hmaj := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2)
    (by norm_num)).const_mul (3 : ℝ)
  refine hmaj.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tailFn_nonneg R τ)]
  unfold tailFn
  split_ifs with h
  · have hτ0 : 0 < |τ| := by linarith
    have h1 : 1 + ‖τ‖ ≤ 2 * |τ| := by rw [Real.norm_eq_abs]; linarith
    have h2 : (2 * |τ|) ^ (-(3 / 2) : ℝ) ≤ (1 + ‖τ‖) ^ (-(3 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    rw [Real.mul_rpow (by norm_num) hτ0.le] at h2
    have h3 : (1 / 3 : ℝ) ≤ (2 : ℝ) ^ (-(3 / 2) : ℝ) := by
      rw [Real.rpow_neg (by norm_num), show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
      have hsq : Real.sqrt 2 ≤ 3 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      rw [one_div]
      apply inv_anti₀ (by positivity)
      linarith only [hsq]
    have h4 := Real.rpow_nonneg hτ0.le (-(3 / 2) : ℝ)
    nlinarith only [h2, h3, h4]
  · have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖τ‖) (-(3 / 2) : ℝ)
    positivity

theorem integral_tailFn {R : ℝ} (hR : 0 < R) : ∫ τ, tailFn R τ = 4 / Real.sqrt R := by
  have h := integral_comp_abs (f := fun r : ℝ => if R < r then r ^ (-(3 / 2) : ℝ) else 0)
  have e : (∫ r in Ioi (0 : ℝ), (if R < r then r ^ (-(3 / 2) : ℝ) else 0)) =
      ∫ r in Ioi R, r ^ (-(3 / 2) : ℝ) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    by_cases hr : R < r
    · have h0 : (0 : ℝ) < r := by linarith
      simp [indicator, hr, h0]
    · simp [indicator, hr]
  have hval := integral_Ioi_rpow_of_lt (a := -(3 / 2)) (by norm_num) hR
  rw [show (-(3 / 2) + 1 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hR.le,
    ← Real.sqrt_eq_rpow] at hval
  unfold tailFn
  rw [h, e, hval]
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  field_simp
  norm_num

/-- `log(1 + r) ≤ √r`. -/
theorem log_one_add_le_sqrt {r : ℝ} (hr : 0 ≤ r) : Real.log (1 + r) ≤ Real.sqrt r := by
  obtain ⟨x, hx0, rfl⟩ : ∃ x, 0 ≤ x ∧ r = x ^ 2 := ⟨Real.sqrt r, Real.sqrt_nonneg r,
    (Real.sq_sqrt hr).symm⟩
  rw [Real.sqrt_sq hx0]
  have h3 : ∑ i ∈ Finset.range 4, x ^ i / (i.factorial : ℝ) ≤ Real.exp x :=
    Real.sum_le_exp_of_nonneg hx0 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h3
  norm_num at h3
  have hle : 1 + x ^ 2 ≤ Real.exp x := by
    have hq : 0 ≤ x * (x ^ 2 / 6 - x / 2 + 1) :=
      mul_nonneg hx0 (by nlinarith only [sq_nonneg (x - 3 / 2)])
    nlinarith only [h3, hq]
  calc Real.log (1 + x ^ 2) ≤ Real.log (Real.exp x) :=
        Real.log_le_log (by positivity) hle
    _ = x := Real.log_exp x

/-! ## The pointwise majorants -/

/-- The Poisson term of the pole at `1` is small after averaging. -/
theorem fejerK_mul_lorentz_le (hL : 0 < L) {x γ τ y : ℝ} (hx : 0 < x) (hγ : 0 < γ)
    (hy : γ - |τ| ≤ |y|) :
    fejerK L τ * (x / (x ^ 2 + y ^ 2)) ≤ fejerK L τ * (4 * x / γ ^ 2) +
      8 / (Real.pi * L * γ ^ 2) * (x / (x ^ 2 + y ^ 2)) := by
  have hπ := Real.pi_pos
  have hK := fejerK_nonneg hL τ
  have hP0 : 0 ≤ x / (x ^ 2 + y ^ 2) := by positivity
  by_cases hτγ : |τ| ≤ γ / 2
  · have hy2 : γ / 2 ≤ |y| := by linarith only [hy, hτγ]
    have hy3 : γ ^ 2 / 4 ≤ y ^ 2 := by
      rw [← sq_abs y]
      nlinarith only [pow_le_pow_left₀ (by positivity : 0 ≤ γ / 2) hy2 2]
    have hle : x / (x ^ 2 + y ^ 2) ≤ 4 * x / γ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_pos hx (sq_pos_of_pos hx), mul_le_mul_of_nonneg_left hy3 hx.le]
    have h3 : 0 ≤ 8 / (Real.pi * L * γ ^ 2) * (x / (x ^ 2 + y ^ 2)) := by positivity
    linarith only [mul_le_mul_of_nonneg_left hle hK, h3]
  · have hτ : γ / 2 < |τ| := not_le.1 hτγ
    have hτ0 : τ ≠ 0 := by
      rintro rfl
      rw [abs_zero] at hτ
      linarith only [hτ, hγ]
    have hτ2 : γ ^ 2 / 4 ≤ τ ^ 2 := by
      rw [← sq_abs τ]
      nlinarith only [pow_le_pow_left₀ (by positivity : 0 ≤ γ / 2) hτ.le 2]
    have hK2 : fejerK L τ ≤ 8 / (Real.pi * L * γ ^ 2) := by
      refine (fejerK_le_inv hL hτ0).trans ?_
      have hp : 0 < Real.pi * L := by positivity
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_left hτ2 hp.le]
    have h2 : 0 ≤ fejerK L τ * (4 * x / γ ^ 2) := by positivity
    linarith only [mul_le_mul_of_nonneg_right hK2 hP0, h2]

/-- The odd part of the logarithm cancels between `γ ± τ`. -/
theorem log_pair_le {C2 γ τ : ℝ} (hC : 0 < C2) (hγ : 0 < γ) (h4 : 4 * C2 ≤ γ ^ 2) :
    1 / 4 * Real.log (C2 + (γ + τ) ^ 2 / 4) + 1 / 4 * Real.log (C2 + (γ - τ) ^ 2 / 4) ≤
      1 / 2 * Real.log (C2 + γ ^ 2 / 4) + 1 / 4 * Real.log (1 + τ ^ 4 / γ ^ 4) := by
  obtain ⟨D, hD⟩ : ∃ D, D = C2 + γ ^ 2 / 4 := ⟨_, rfl⟩
  have hDpos : 0 < D := by rw [hD]; positivity
  have hAp : 0 < C2 + (γ + τ) ^ 2 / 4 := by positivity
  have hAm : 0 < C2 + (γ - τ) ^ 2 / 4 := by positivity
  have hprod : (C2 + (γ + τ) ^ 2 / 4) * (C2 + (γ - τ) ^ 2 / 4) ≤
      D ^ 2 * (1 + τ ^ 4 / γ ^ 4) := by
    have hexp : (C2 + (γ + τ) ^ 2 / 4) * (C2 + (γ - τ) ^ 2 / 4) =
        D ^ 2 + τ ^ 2 * (C2 / 2 - γ ^ 2 / 8) + τ ^ 4 / 16 := by
      rw [hD]
      ring
    have hmid : τ ^ 2 * (C2 / 2 - γ ^ 2 / 8) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith only [h4])
    have hD2 : γ ^ 4 / 16 ≤ D ^ 2 := by
      have h1 : γ ^ 2 / 4 ≤ D := by rw [hD]; linarith only [hC]
      have := pow_le_pow_left₀ (by positivity : 0 ≤ γ ^ 2 / 4) h1 2
      nlinarith only [this]
    have hγ4 : 0 < γ ^ 4 := by positivity
    have hr : τ ^ 4 / 16 ≤ D ^ 2 * (τ ^ 4 / γ ^ 4) := by
      have h0 : 0 ≤ τ ^ 4 / γ ^ 4 := by positivity
      have := mul_le_mul_of_nonneg_right hD2 h0
      have e : γ ^ 4 / 16 * (τ ^ 4 / γ ^ 4) = τ ^ 4 / 16 := by
        field_simp
      linarith only [this, e]
    rw [hexp]
    linarith only [hmid, hr, mul_add (D ^ 2) 1 (τ ^ 4 / γ ^ 4), mul_one (D ^ 2)]
  have hr0 : 0 < 1 + τ ^ 4 / γ ^ 4 := by positivity
  have hlog := Real.log_le_log (mul_pos hAp hAm) hprod
  rw [Real.log_mul hAp.ne' hAm.ne', Real.log_mul (by positivity) hr0.ne', Real.log_pow] at hlog
  rw [← hD]
  push_cast at hlog
  linarith only [hlog]

/-- `log(1 + r⁴)` against the density: quadratic near the centre, `√r` in the tail. -/
theorem fejerK_mul_log_le (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ) (τ : ℝ) :
    fejerK L τ * (1 / 8 * Real.log (1 + τ ^ 4 / γ ^ 4)) ≤
      1 / (4 * Real.pi * L * γ ^ 2) * Set.indicator (Icc (-γ) γ) (fun _ => (1 : ℝ)) τ +
        1 / (Real.pi * L * Real.sqrt γ) * tailFn γ τ := by
  have hπ := Real.pi_pos
  have hK := fejerK_nonneg hL τ
  have hsq : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  by_cases hτ : |τ| ≤ γ
  · have hmem : τ ∈ Icc (-γ) γ := abs_le.1 hτ
    have ht : tailFn γ τ = 0 := by simp [tailFn, not_lt.2 hτ]
    rw [Set.indicator_of_mem hmem, ht, mul_zero, add_zero, mul_one]
    by_cases hτ0 : τ = 0
    · subst hτ0
      have : (1 : ℝ) + 0 ^ 4 / γ ^ 4 = 1 := by norm_num
      rw [this, Real.log_one, mul_zero, mul_zero]
      positivity
    · have hτpos : 0 < τ ^ 2 := by positivity
      have hτ2 : τ ^ 2 ≤ γ ^ 2 := by
        rw [← sq_abs τ]
        exact pow_le_pow_left₀ (abs_nonneg τ) hτ 2
      have hγ2 : 0 < γ ^ 2 := by positivity
      have hlog : Real.log (1 + τ ^ 4 / γ ^ 4) ≤ τ ^ 2 / γ ^ 2 := by
        have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + τ ^ 4 / γ ^ 4 by positivity)
        have h2 : τ ^ 4 / γ ^ 4 ≤ τ ^ 2 / γ ^ 2 := by
          rw [show τ ^ 4 / γ ^ 4 = (τ ^ 2 / γ ^ 2) * (τ ^ 2 / γ ^ 2) by field_simp]
          have h3 : τ ^ 2 / γ ^ 2 ≤ 1 := (div_le_one hγ2).2 hτ2
          exact mul_le_of_le_one_right (by positivity) h3
        linarith only [h1, h2]
      have hlog0 : 0 ≤ Real.log (1 + τ ^ 4 / γ ^ 4) := Real.log_nonneg (by
        have : 0 ≤ τ ^ 4 / γ ^ 4 := by positivity
        linarith only [this])
      calc fejerK L τ * (1 / 8 * Real.log (1 + τ ^ 4 / γ ^ 4))
          ≤ 2 / (Real.pi * L * τ ^ 2) * (1 / 8 * (τ ^ 2 / γ ^ 2)) :=
            mul_le_mul (fejerK_le_inv hL hτ0) (by linarith only [hlog]) (by positivity)
              (by positivity)
        _ = _ := by field_simp; norm_num
  · have hτ' : γ < |τ| := not_le.1 hτ
    have hτabs : 0 < |τ| := hγ.trans hτ'
    have hτ0 : τ ≠ 0 := abs_pos.1 hτabs
    have hmem : τ ∉ Icc (-γ) γ := fun h => hτ (abs_le.2 h)
    have ht : tailFn γ τ = |τ| ^ (-(3 / 2) : ℝ) := by simp [tailFn, hτ']
    rw [Set.indicator_of_notMem hmem, mul_zero, zero_add, ht]
    obtain ⟨r, hr⟩ : ∃ r, r = |τ| / γ := ⟨_, rfl⟩
    have hr0 : 0 ≤ r := by rw [hr]; positivity
    have hr4 : τ ^ 4 / γ ^ 4 = r ^ 4 := by
      rw [hr, div_pow]
      congr 1
      rw [← Even.pow_abs (by decide : Even 4) τ]
    have hlog : Real.log (1 + τ ^ 4 / γ ^ 4) ≤ 4 * Real.sqrt r := by
      rw [hr4]
      have h1 : 1 + r ^ 4 ≤ (1 + r) ^ 4 := by
        nlinarith only [pow_nonneg hr0 2, pow_nonneg hr0 3, hr0]
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith only [h2, log_one_add_le_sqrt hr0]
    have hlog0 : 0 ≤ Real.log (1 + τ ^ 4 / γ ^ 4) := Real.log_nonneg (by
      have : 0 ≤ τ ^ 4 / γ ^ 4 := by positivity
      linarith only [this])
    have hsr : Real.sqrt r = Real.sqrt |τ| / Real.sqrt γ := by
      rw [hr]
      exact Real.sqrt_div hτabs.le _
    have hpow : Real.sqrt |τ| / τ ^ 2 = |τ| ^ (-(3 / 2) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← sq_abs τ, ← Real.rpow_natCast |τ| 2, ← Real.rpow_sub hτabs]
      norm_num
    calc fejerK L τ * (1 / 8 * Real.log (1 + τ ^ 4 / γ ^ 4))
        ≤ 2 / (Real.pi * L * τ ^ 2) * (1 / 8 * (4 * Real.sqrt r)) :=
          mul_le_mul (fejerK_le_inv hL hτ0) (by linarith only [hlog]) (by positivity)
            (by positivity)
      _ = 1 / (Real.pi * L * Real.sqrt γ) * (Real.sqrt |τ| / τ ^ 2) := by
          rw [hsr]
          field_simp
          norm_num
      _ = _ := by rw [hpow]

/-! ## The budget -/

/-- The archimedean budget of the height `γ`. -/
def archBudget (a L γ : ℝ) : ℝ :=
  1 / 4 * Real.log ((1 + (1 / 2 + a) / 2) ^ 2 + γ ^ 2 / 4) - Real.log Real.pi / 2 +
    1 / (240 * (1 + (1 / 2 + a) / 2) ^ 4) + (4 * (a - 1 / 2) + 8 / L) / γ ^ 2 +
    9 / (2 * Real.pi * L) / γ

/-- The pair of an off-line zero, written with Lorentz kernels. -/
private theorem pair_eq_lorentz (a δ τ : ℝ) :
    xiLinePairRe a δ τ = (a - δ) / ((a - δ) ^ 2 + τ ^ 2) + (a + δ) / ((a + δ) ^ 2 + τ ^ 2) := rfl

private theorem pair_neg (a δ τ : ℝ) : xiLinePairRe a δ (-τ) = xiLinePairRe a δ τ := by
  simp only [pair_eq_lorentz, neg_sq]

private theorem integrable_fejerK_mul_lorentz (hL : 0 < L) {x : ℝ} (hx : 0 < x) :
    Integrable fun τ => fejerK L τ * (x / (x ^ 2 + τ ^ 2)) := by
  refine integrable_fejerK_mul_bdd hL (C := 1 / x) ?_ fun τ => ?_
  · refine Continuous.div (by fun_prop) (by fun_prop) fun τ => ?_
    positivity
  · rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hx]
    nlinarith only [sq_nonneg τ, sq_nonneg x]

/-- The shifted Lorentz kernel has mass `π`. -/
private theorem shifted_lorentz {x : ℝ} (hx : 0 < x) (c : ℝ) :
    Integrable (fun τ : ℝ => x / (x ^ 2 + (c + τ) ^ 2)) ∧
      ∫ τ : ℝ, x / (x ^ 2 + (c + τ) ^ 2) = Real.pi := by
  have e : ∀ τ : ℝ, x / (x ^ 2 + (c + τ) ^ 2) = x⁻¹ * ((1 + ((c + τ) / x) ^ 2)⁻¹) := by
    intro τ
    have hp : 0 < x ^ 2 + (c + τ) ^ 2 := by positivity
    field_simp
  simp_rw [e]
  constructor
  · exact ((integrable_inv_one_add_sq.comp_div (R := x) hx.ne').comp_add_left c).const_mul _
  · rw [integral_const_mul, integral_add_left_eq_self (fun τ => (1 + (τ / x) ^ 2)⁻¹) c,
      Measure.integral_comp_div (fun v => (1 + v ^ 2)⁻¹) x, integral_univ_inv_one_add_sq,
      abs_of_pos hx, smul_eq_mul]
    field_simp

/-- The Hadamard pair below the archimedean envelope and the prime series. -/
private theorem pair_le_envelope {a : ℝ} (ha : 1 / 2 < a) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) {σ x δ γ : ℝ} (hσ : σ = 1 / 2 + a) (hx : x = σ - 1)
    (hδ : δ = (q.1 : ℂ).re - 1 / 2) (hγ : (q.1 : ℂ).im = γ) (τ y : ℝ) (hy : y - γ = τ) :
    xiLinePairRe a δ τ ≤ x / (x ^ 2 + y ^ 2) - Real.log Real.pi / 2 +
      1 / 4 * Real.log ((1 + σ / 2) ^ 2 + y ^ 2 / 4) + 1 / (240 * (1 + σ / 2) ^ 4) -
        primeSeries σ y := by
  have hσ1 : 1 < σ := by rw [hσ]; linarith only [ha]
  have hH := xiLinePairRe_le_re_logDeriv_xi ha q hoff y
  rw [hγ, hy, ← hδ, ← hσ] at hH
  have hU := re_logDeriv_xi_le (σ := σ) (y := y) hσ1
  rw [re_logDeriv_riemannZeta_eq hσ1, ← hx] at hU
  linarith only [hH, hU]

/-- **The Fejér budget of an off-line zero.** -/
theorem two_mul_fejerLaplace_le_of_offLine {a : ℝ} (ha : 1 / 2 < a) (hL : 0 < L) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) {γ : ℝ} (hγq : (q.1 : ℂ).im = γ) (hγ1 : 1 ≤ γ)
    (hγ2 : 4 * (1 + (1 / 2 + a) / 2) ^ 2 ≤ γ ^ 2) :
    2 * fejerLaplace L a ≤ archBudget a L γ - primeSum (1 / 2 + a) L γ := by
  have hπ := Real.pi_pos
  have hγ : 0 < γ := by linarith only [hγ1]
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = 1 / 2 + a := ⟨_, rfl⟩
  have hσ : 1 < σ := by rw [hσdef]; linarith only [ha]
  obtain ⟨x, hxdef⟩ : ∃ x, x = σ - 1 := ⟨_, rfl⟩
  have hx : 0 < x := by rw [hxdef]; linarith only [hσ]
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = (q.1 : ℂ).re - 1 / 2 := ⟨_, rfl⟩
  have hq0 := xiZeroCopy_re_pos q
  have hq1 := xiZeroCopy_re_lt_one q
  have hd1 : 0 < a - δ := by rw [hδdef]; linarith only [ha, hq1]
  have hd2 : 0 < a + δ := by rw [hδdef]; linarith only [ha, hq0]
  obtain ⟨C2, hC2⟩ : ∃ C2, C2 = (1 + σ / 2) ^ 2 := ⟨_, rfl⟩
  have hC20 : 0 < C2 := by rw [hC2]; positivity
  have hC4 : 4 * C2 ≤ γ ^ 2 := by rw [hC2, hσdef]; exact hγ2
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀, ε₀ = 1 / (240 * (1 + σ / 2) ^ 4) := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = 1 / 4 * Real.log (C2 + γ ^ 2 / 4) - Real.log Real.pi / 2 + ε₀ +
      4 * x / γ ^ 2 := ⟨_, rfl⟩
  -- The left side.
  have hleft : 2 * fejerLaplace L a ≤ ∫ τ, fejerK L τ * xiLinePairRe a δ τ := by
    simp_rw [pair_eq_lorentz, mul_add]
    rw [integral_add (integrable_fejerK_mul_lorentz hL hd1) (integrable_fejerK_mul_lorentz hL hd2),
      integral_fejerK_mul_lorentz hL hd1, integral_fejerK_mul_lorentz hL hd2]
    exact two_mul_fejerLaplace_le hL hd1 hd2
  have hLHSint : Integrable fun τ => fejerK L τ * xiLinePairRe a δ τ := by
    simp_rw [pair_eq_lorentz, mul_add]
    exact (integrable_fejerK_mul_lorentz hL hd1).add (integrable_fejerK_mul_lorentz hL hd2)
  -- The pieces of the majorant.
  have hS1 : Integrable fun τ => fejerK L τ * primeSeries σ (γ + τ) :=
    integrable_fejerK_mul_bdd hL ((continuous_primeSeries hσ).comp (by fun_prop))
      (C := ∑' n, primeCoeff σ n) fun τ => abs_primeSeries_le hσ _
  have hS2 : Integrable fun τ => fejerK L τ * primeSeries σ (γ - τ) :=
    integrable_fejerK_mul_bdd hL ((continuous_primeSeries hσ).comp (by fun_prop))
      (C := ∑' n, primeCoeff σ n) fun τ => abs_primeSeries_le hσ _
  have hK0 : Integrable fun τ => fejerK L τ * B₀ := (integrable_fejerK hL).mul_const _
  have hind : Integrable (Set.indicator (Icc (-γ) γ) fun _ => (1 : ℝ)) :=
    (integrable_const (1 : ℝ)).integrableOn.integrable_indicator measurableSet_Icc
  have hindI : ∫ τ, Set.indicator (Icc (-γ) γ) (fun _ => (1 : ℝ)) τ = 2 * γ := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
      Real.volume_real_Icc_of_le (by linarith only [hγ])]
    ring
  have htail := integrable_tailFn hγ1
  have hL1 := (shifted_lorentz hx γ).1
  have hL2 := (shifted_lorentz hx γ).2
  have hL3 : Integrable fun τ : ℝ => x / (x ^ 2 + (γ - τ) ^ 2) := by
    have := hL1.comp_neg
    refine this.congr (ae_of_all _ fun τ => ?_)
    simp only [sub_eq_add_neg]
  have hL4 : ∫ τ : ℝ, x / (x ^ 2 + (γ - τ) ^ 2) = Real.pi := by
    rw [← hL2, ← integral_neg_eq_self (fun τ : ℝ => x / (x ^ 2 + (γ + τ) ^ 2)) volume]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only [sub_eq_add_neg]
  let Maj : ℝ → ℝ := fun τ =>
    (fejerK L τ * B₀ - 1 / 2 * (fejerK L τ * primeSeries σ (γ + τ)) -
      1 / 2 * (fejerK L τ * primeSeries σ (γ - τ))) +
    1 / (4 * Real.pi * L * γ ^ 2) * Set.indicator (Icc (-γ) γ) (fun _ => (1 : ℝ)) τ +
    1 / (Real.pi * L * Real.sqrt γ) * tailFn γ τ +
    (4 / (Real.pi * L * γ ^ 2) * (x / (x ^ 2 + (γ + τ) ^ 2)) +
      4 / (Real.pi * L * γ ^ 2) * (x / (x ^ 2 + (γ - τ) ^ 2)))
  have hMajInt : Integrable Maj := by
    exact (((hK0.sub (hS1.const_mul _)).sub (hS2.const_mul _)).add (hind.const_mul _)).add
      (htail.const_mul _) |>.add ((hL1.const_mul _).add (hL3.const_mul _))
  -- The pointwise inequality.
  have hpoint : ∀ τ, fejerK L τ * xiLinePairRe a δ τ ≤ Maj τ := by
    intro τ
    have hK := fejerK_nonneg hL τ
    have hp := pair_le_envelope ha q hoff hσdef hxdef hδdef hγq τ (γ + τ) (by ring)
    have hm := pair_le_envelope ha q hoff hσdef hxdef hδdef hγq (-τ) (γ - τ) (by ring)
    rw [pair_neg] at hm
    rw [← hC2, ← hε₀] at hp hm
    have hlogp := log_pair_le (τ := τ) hC20 hγ hC4
    have hlogK := fejerK_mul_log_le hL hγ τ
    have hl1 := fejerK_mul_lorentz_le hL (τ := τ) (y := γ + τ) hx hγ (by
      have h1 := abs_sub_abs_le_abs_sub γ (-τ)
      rw [abs_neg, sub_neg_eq_add, abs_of_pos hγ] at h1
      exact h1)
    have hl2 := fejerK_mul_lorentz_le hL (τ := τ) (y := γ - τ) hx hγ (by
      have h1 := abs_sub_abs_le_abs_sub γ τ
      rw [abs_of_pos hγ] at h1
      exact h1)
    have hmean : xiLinePairRe a δ τ ≤ 1 / 2 * (x / (x ^ 2 + (γ + τ) ^ 2)) +
        1 / 2 * (x / (x ^ 2 + (γ - τ) ^ 2)) - Real.log Real.pi / 2 + ε₀ -
        1 / 2 * primeSeries σ (γ + τ) - 1 / 2 * primeSeries σ (γ - τ) +
        1 / 4 * Real.log (C2 + γ ^ 2 / 4) + 1 / 8 * Real.log (1 + τ ^ 4 / γ ^ 4) := by
      linarith only [hp, hm, hlogp]
    have hstep := mul_le_mul_of_nonneg_left hmean hK
    have e8 : 4 / (Real.pi * L * γ ^ 2) = 1 / 2 * (8 / (Real.pi * L * γ ^ 2)) := by ring
    have e4 : 4 * x / γ ^ 2 = 1 / 2 * (4 * x / γ ^ 2) + 1 / 2 * (4 * x / γ ^ 2) := by ring
    simp only [Maj]
    rw [hB₀, e8]
    generalize fejerK L τ = A at *
    generalize x / (x ^ 2 + (γ + τ) ^ 2) = P₁ at *
    generalize x / (x ^ 2 + (γ - τ) ^ 2) = P₂ at *
    generalize 4 * x / γ ^ 2 = D at *
    generalize 8 / (Real.pi * L * γ ^ 2) = F at *
    linarith only [hstep, hlogK, hl1, hl2]
  -- The value of the majorant.
  have hright : ∫ τ, Maj τ = B₀ - primeSum σ L γ + 1 / (2 * Real.pi * L * γ) +
      4 / (Real.pi * L * γ) + 8 / (L * γ ^ 2) := by
    have hsq : Real.sqrt γ * Real.sqrt γ = γ := Real.mul_self_sqrt hγ.le
    have hsq0 : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
    simp only [Maj]
    rw [integral_add ((((hK0.sub (hS1.const_mul _)).sub (hS2.const_mul _)).add
        (hind.const_mul _)).add (htail.const_mul _)) ((hL1.const_mul _).add (hL3.const_mul _)),
      integral_add (((hK0.sub (hS1.const_mul _)).sub (hS2.const_mul _)).add (hind.const_mul _))
        (htail.const_mul _),
      integral_add ((hK0.sub (hS1.const_mul _)).sub (hS2.const_mul _)) (hind.const_mul _),
      integral_sub (hK0.sub (hS1.const_mul _)) (hS2.const_mul _),
      integral_sub hK0 (hS1.const_mul _),
      integral_add (hL1.const_mul _) (hL3.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul,
      integral_mul_const, integral_fejerK hL, integral_fejerK_mul_primeSeries hL hσ,
      integral_fejerK_mul_primeSeries_sub hL hσ, hindI, integral_tailFn hγ, hL2, hL4]
    have e1 : 1 / (Real.pi * L * Real.sqrt γ) * (4 / Real.sqrt γ) = 4 / (Real.pi * L * γ) := by
      rw [← hsq]
      field_simp
    rw [e1]
    field_simp
    ring
  have hfinal := hleft.trans (integral_mono hLHSint hMajInt hpoint)
  rw [hright, hB₀] at hfinal
  unfold archBudget
  rw [← hσdef, ← hC2, ← hε₀]
  have e : (4 * (a - 1 / 2) + 8 / L) / γ ^ 2 = 4 * x / γ ^ 2 + 8 / (L * γ ^ 2) := by
    rw [hxdef, hσdef]
    field_simp
    ring
  have e2 : 9 / (2 * Real.pi * L) / γ = 1 / (2 * Real.pi * L * γ) + 4 / (Real.pi * L * γ) := by
    field_simp
    norm_num
  rw [e, e2]
  linarith only [hfinal]

end

end GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget
