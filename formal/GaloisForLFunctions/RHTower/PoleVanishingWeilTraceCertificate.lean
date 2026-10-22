import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundEnergy
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilActualHeadCompletedErrorProducer
import GaloisForLFunctions.RHTower.DigammaVerticalMinimum
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCCMScalingBridge

/-!
# A trace certificate for the pole-vanishing restricted Weil form

**Fourier values are plane-wave residual pairings.**  Let `f ∈ L²(ℝ)` vanish outside the
logarithmic aperture `[-a, a]` and be orthogonal there to the two pole profiles `e^{± x/2}`.
For every frequency `ξ` and all real `p, q`,

`𝓕 f (ξ) = ⟨e_ξ - ((p + q i)/2) e^{x/2} - ((p - q i)/2) e^{-x/2}, f⟩`,

where `e_ξ(x) = exp(2π i ξ x)` on the aperture; on the aperture the subtracted combination is
`p cosh(x/2) + i q sinh(x/2)`.  By Cauchy–Schwarz,

`‖𝓕 f (ξ)‖² ≤ ‖f‖² · ∫_{-a}^{a} (cos ωx - p cosh(x/2))² + (sin ωx - q sinh(x/2))² dx`,
`ω = 2πξ`,

and the integral equals `2a - 2p C(a,ω) + p² (a + sinh a) - 2q S(a,ω) + q² (sinh a - a)`, with
`C(a,ω) = ∫ cos(ωx) cosh(x/2)` and `S(a,ω) = ∫ sin(ωx) sinh(x/2)` in closed form.  Plane waves are
Lipschitz in the frequency: `‖e_ξ - e_m‖² ≤ 4π² (ξ - m)² · 2a³/3`.

**The certificate.**  At the aperture `a = ½ log 2`, on the pole-vanishing subspace, the exact
restricted Weil form reduces to the archimedean form `∫ W(ξ) |𝓕 f(ξ)|² dξ` with
`W(ξ) = Re ψ(1/4 + iπξ) - log π`: the polar term vanishes by the constraints and the only prime
term (`n = 2`) is a translation by the aperture diameter, with null overlap.  Since `W` is even and
nondecreasing in `|ξ|`, and `W ≥ α - (α - W)₊`,

`Q(f) ≥ (α - Σ_k 2h G_k R_k) ‖f‖²`

whenever `W(kh) ≥ α - G_k` on a grid, `W(Kh) ≥ α`, and the constrained Fourier mass density on
the shell `kh ≤ |ξ| < (k+1)h` is at most `R_k ‖f‖²`.  This is the trace of the compressed
negative part of `W - α` on the pole-vanishing subspace.
-/

open MeasureTheory Complex Set
open scoped FourierTransform InnerProduct

noncomputable section

namespace RHTower

/-! ## The plane wave on the aperture -/

/-- The plane wave `x ↦ exp(2π i ξ x)`. -/
def planeWaveProfile (ξ x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * ξ * x : ℝ) : ℂ) * I)

theorem norm_planeWaveProfile (ξ x : ℝ) : ‖planeWaveProfile ξ x‖ = 1 := by
  unfold planeWaveProfile
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_planeWaveProfile (ξ : ℝ) : Continuous (planeWaveProfile ξ) := by
  unfold planeWaveProfile
  fun_prop

theorem planeWaveProfile_memLp_aperture (a : SuzukiPositiveAperture) (ξ : ℝ) :
    MemLp ((centralInterval a.1).indicator (planeWaveProfile ξ)) 2 volume := by
  apply (memLp_indicator_iff_restrict (measurableSet_centralInterval a.1)).2
  have hfinite : IsFiniteMeasure (volume.restrict (centralInterval a.1)) := by
    constructor
    simp [centralInterval]
  letI := hfinite
  refine MemLp.of_bound (p := (2 : ENNReal)) ?_ 1 ?_
  · exact (continuous_planeWaveProfile ξ).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_planeWaveProfile]

/-- The plane wave restricted to the aperture, as an `L²` vector. -/
def planeWaveL2 (a : SuzukiPositiveAperture) (ξ : ℝ) : SoninL2 :=
  (planeWaveProfile_memLp_aperture a ξ).toLp
    ((centralInterval a.1).indicator (planeWaveProfile ξ))

theorem planeWaveL2_coeFn (a : SuzukiPositiveAperture) (ξ : ℝ) :
    (planeWaveL2 a ξ : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (planeWaveProfile ξ) :=
  (planeWaveProfile_memLp_aperture a ξ).coeFn_toLp

/-- **Fourier values are plane-wave pairings.**  For an aperture vector, the Fourier transform
at `ξ` is the `L²` pairing with the aperture plane wave of frequency `ξ`. -/
theorem fourier_eq_inner_planeWaveL2 (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (ξ : ℝ) :
    𝓕 (f.1 : ℝ → ℂ) ξ = inner ℂ (planeWaveL2 a ξ) f.1 := by
  rw [MeasureTheory.L2.inner_def, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [planeWaveL2_coeFn a ξ, suzukiApertureHilbert_ae_zero_outside a f] with
    x hw hf
  rw [hw]
  by_cases hx : x ∈ centralInterval a.1
  · have hconj : (starRingEnd ℂ) (planeWaveProfile ξ x) =
        Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * I) := by
      unfold planeWaveProfile
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [indicator_of_mem hx, RCLike.inner_apply, smul_eq_mul, hconj]
    ring
  · have hxa : a.1 < |x| := by
      by_contra hle
      exact hx (abs_le.mp (not_lt.mp hle))
    rw [indicator_of_notMem hx, hf hxa]
    simp

/-! ## The pole residual -/

/-- The plane wave minus the combination `p cosh(x/2) + i q sinh(x/2)` of the two pole
profiles, as an `L²` vector on the aperture. -/
def poleResidualL2 (a : SuzukiPositiveAperture) (ξ p q : ℝ) : SoninL2 :=
  planeWaveL2 a ξ - (((p : ℂ) + (q : ℂ) * I) / 2) • ccmPolarL2Vector a (1 / 2) -
    (((p : ℂ) - (q : ℂ) * I) / 2) • ccmPolarL2Vector a (-1 / 2)

/-- The residual profile, written through its real and imaginary parts. -/
def poleResidualProfile (ξ p q x : ℝ) : ℂ :=
  ((Real.cos (2 * Real.pi * ξ * x) - p * Real.cosh (x / 2) : ℝ) : ℂ) +
    ((Real.sin (2 * Real.pi * ξ * x) - q * Real.sinh (x / 2) : ℝ) : ℂ) * I

theorem poleResidualProfile_eq (ξ p q x : ℝ) :
    poleResidualProfile ξ p q x =
      planeWaveProfile ξ x - (((p : ℂ) + (q : ℂ) * I) / 2) * ccmPolarProfile (1 / 2) x -
        (((p : ℂ) - (q : ℂ) * I) / 2) * ccmPolarProfile (-1 / 2) x := by
  unfold poleResidualProfile planeWaveProfile ccmPolarProfile
  rw [Real.cosh_eq, Real.sinh_eq, Complex.exp_mul_I]
  push_cast
  ring_nf

theorem poleResidualL2_coeFn (a : SuzukiPositiveAperture) (ξ p q : ℝ) :
    (poleResidualL2 a ξ p q : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (poleResidualProfile ξ p q) := by
  unfold poleResidualL2
  filter_upwards [Lp.coeFn_sub (planeWaveL2 a ξ - (((p : ℂ) + (q : ℂ) * I) / 2) •
      ccmPolarL2Vector a (1 / 2)) ((((p : ℂ) - (q : ℂ) * I) / 2) • ccmPolarL2Vector a (-1 / 2)),
    Lp.coeFn_sub (planeWaveL2 a ξ) ((((p : ℂ) + (q : ℂ) * I) / 2) • ccmPolarL2Vector a (1 / 2)),
    Lp.coeFn_smul (((p : ℂ) + (q : ℂ) * I) / 2) (ccmPolarL2Vector a (1 / 2)),
    Lp.coeFn_smul (((p : ℂ) - (q : ℂ) * I) / 2) (ccmPolarL2Vector a (-1 / 2)),
    planeWaveL2_coeFn a ξ, ccmPolarL2Vector_coeFn a (1 / 2),
    ccmPolarL2Vector_coeFn a (-1 / 2)] with x h1 h2 h3 h4 h5 h6 h7
  rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h5, h6, h7]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hx, smul_eq_mul]
    exact (poleResidualProfile_eq ξ p q x).symm
  · simp [indicator_of_notMem hx]

/-- Under the two pole constraints, the residual pairing is the Fourier value. -/
theorem inner_poleResidualL2_of_polar (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a)
    (hplus : inner ℂ (ccmPolarL2Vector a (1 / 2)) f.1 = 0)
    (hminus : inner ℂ (ccmPolarL2Vector a (-1 / 2)) f.1 = 0) (ξ p q : ℝ) :
    inner ℂ (poleResidualL2 a ξ p q) f.1 = 𝓕 (f.1 : ℝ → ℂ) ξ := by
  rw [poleResidualL2, inner_sub_left, inner_sub_left, inner_smul_left, inner_smul_left,
    hplus, hminus, mul_zero, mul_zero, sub_zero, sub_zero,
    fourier_eq_inner_planeWaveL2]

/-- **Cauchy–Schwarz for pole-vanishing aperture vectors.** -/
theorem norm_fourier_le_poleResidual (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a)
    (hplus : inner ℂ (ccmPolarL2Vector a (1 / 2)) f.1 = 0)
    (hminus : inner ℂ (ccmPolarL2Vector a (-1 / 2)) f.1 = 0) (ξ p q : ℝ) :
    ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ≤ ‖poleResidualL2 a ξ p q‖ * ‖f‖ := by
  rw [← inner_poleResidualL2_of_polar a f hplus hminus ξ p q]
  exact norm_inner_le_norm _ _

/-! ## The residual norm as an integral -/

private theorem norm_sq_eq_integral_norm_sq (g : SoninL2) :
    ‖g‖ ^ 2 = ∫ x : ℝ, ‖(g : ℝ → ℂ) x‖ ^ 2 := by
  have h2 := MeasureTheory.L2.inner_def (𝕜 := ℂ) g g
  rw [inner_self_eq_norm_sq_to_K] at h2
  have hpoint : ∀ x : ℝ, inner ℂ ((g : ℝ → ℂ) x) ((g : ℝ → ℂ) x) =
      ((‖(g : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [hpoint] at h2
  rw [integral_complex_ofReal] at h2
  have h4 : ((‖g‖ ^ 2 : ℝ) : ℂ) = ((∫ x : ℝ, ‖(g : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact h2
  exact_mod_cast h4

theorem norm_sq_poleResidualProfile (ξ p q x : ℝ) :
    ‖poleResidualProfile ξ p q x‖ ^ 2 =
      (Real.cos (2 * Real.pi * ξ * x) - p * Real.cosh (x / 2)) ^ 2 +
        (Real.sin (2 * Real.pi * ξ * x) - q * Real.sinh (x / 2)) ^ 2 := by
  unfold poleResidualProfile
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

/-- The squared residual norm is the aperture integral of the squared real and imaginary
residuals. -/
theorem norm_sq_poleResidualL2 (a : SuzukiPositiveAperture) (ξ p q : ℝ) :
    ‖poleResidualL2 a ξ p q‖ ^ 2 =
      ∫ x in (-a.1)..a.1,
        ((Real.cos (2 * Real.pi * ξ * x) - p * Real.cosh (x / 2)) ^ 2 +
          (Real.sin (2 * Real.pi * ξ * x) - q * Real.sinh (x / 2)) ^ 2) := by
  rw [norm_sq_eq_integral_norm_sq]
  have hae : (fun x : ℝ => ‖(poleResidualL2 a ξ p q : ℝ → ℂ) x‖ ^ 2) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x : ℝ =>
        (Real.cos (2 * Real.pi * ξ * x) - p * Real.cosh (x / 2)) ^ 2 +
          (Real.sin (2 * Real.pi * ξ * x) - q * Real.sinh (x / 2)) ^ 2) := by
    filter_upwards [poleResidualL2_coeFn a ξ p q] with x hx
    rw [hx]
    by_cases hmem : x ∈ centralInterval a.1
    · rw [indicator_of_mem hmem, indicator_of_mem hmem, norm_sq_poleResidualProfile]
    · rw [indicator_of_notMem hmem, indicator_of_notMem hmem]
      simp
  rw [integral_congr_ae hae, integral_indicator (measurableSet_centralInterval a.1),
    intervalIntegral.integral_of_le (by linarith [a.property]), centralInterval,
    integral_Icc_eq_integral_Ioc]

/-! ## The closed form of the residual integral -/

/-- `∫_{-a}^{a} cos(ωx) cosh(x/2) dx`. -/
def poleCosCoshIntegral (a ω : ℝ) : ℝ :=
  4 * (Real.cos (ω * a) * Real.sinh (a / 2) + 2 * ω * Real.sin (ω * a) * Real.cosh (a / 2)) /
    (1 + 4 * ω ^ 2)

/-- `∫_{-a}^{a} sin(ωx) sinh(x/2) dx`. -/
def poleSinSinhIntegral (a ω : ℝ) : ℝ :=
  4 * (Real.sin (ω * a) * Real.cosh (a / 2) - 2 * ω * Real.cos (ω * a) * Real.sinh (a / 2)) /
    (1 + 4 * ω ^ 2)

/-- The closed form of the squared residual norm. -/
def poleResidualClosedForm (a ω p q : ℝ) : ℝ :=
  2 * a - 2 * p * poleCosCoshIntegral a ω + p ^ 2 * (a + Real.sinh a) -
    2 * q * poleSinSinhIntegral a ω + q ^ 2 * (Real.sinh a - a)

private theorem hasDerivAt_cos_mul (ω x : ℝ) :
    HasDerivAt (fun x => Real.cos (ω * x)) (-(Real.sin (ω * x)) * ω) x := by
  have h := (Real.hasDerivAt_cos (ω * x)).comp x ((hasDerivAt_id x).const_mul ω)
  simpa [Function.comp_def] using h

private theorem hasDerivAt_sin_mul (ω x : ℝ) :
    HasDerivAt (fun x => Real.sin (ω * x)) (Real.cos (ω * x) * ω) x := by
  have h := (Real.hasDerivAt_sin (ω * x)).comp x ((hasDerivAt_id x).const_mul ω)
  simpa [Function.comp_def] using h

private theorem hasDerivAt_cosh_half (x : ℝ) :
    HasDerivAt (fun x => Real.cosh (x / 2)) (Real.sinh (x / 2) * (1 / 2)) x := by
  have h := (Real.hasDerivAt_cosh (x / 2)).comp x ((hasDerivAt_id x).div_const 2)
  simpa [Function.comp_def] using h

private theorem hasDerivAt_sinh_half (x : ℝ) :
    HasDerivAt (fun x => Real.sinh (x / 2)) (Real.cosh (x / 2) * (1 / 2)) x := by
  have h := (Real.hasDerivAt_sinh (x / 2)).comp x ((hasDerivAt_id x).div_const 2)
  simpa [Function.comp_def] using h

/-- The antiderivative of the residual integrand. -/
private def poleResidualPrimitive (ω p q x : ℝ) : ℝ :=
  x - 2 * p * ((2 * Real.cos (ω * x) * Real.sinh (x / 2) +
      4 * ω * Real.sin (ω * x) * Real.cosh (x / 2)) / (1 + 4 * ω ^ 2)) +
    p ^ 2 * (x / 2 + Real.sinh (x / 2) * Real.cosh (x / 2)) -
    2 * q * ((2 * Real.sin (ω * x) * Real.cosh (x / 2) -
      4 * ω * Real.cos (ω * x) * Real.sinh (x / 2)) / (1 + 4 * ω ^ 2)) +
    q ^ 2 * (-(x / 2) + Real.sinh (x / 2) * Real.cosh (x / 2))

private theorem hasDerivAt_poleResidualPrimitive (ω p q x : ℝ) :
    HasDerivAt (poleResidualPrimitive ω p q)
      ((Real.cos (ω * x) - p * Real.cosh (x / 2)) ^ 2 +
        (Real.sin (ω * x) - q * Real.sinh (x / 2)) ^ 2) x := by
  have hden : (1 + 4 * ω ^ 2) ≠ 0 := by positivity
  have hc := hasDerivAt_cos_mul ω x
  have hs := hasDerivAt_sin_mul ω x
  have hch := hasDerivAt_cosh_half x
  have hsh := hasDerivAt_sinh_half x
  have hF := ((((hc.mul hsh).const_mul 2).add ((hs.mul hch).const_mul (4 * ω))).div_const
    (1 + 4 * ω ^ 2))
  have hG := ((((hs.mul hch).const_mul 2).sub ((hc.mul hsh).const_mul (4 * ω))).div_const
    (1 + 4 * ω ^ 2))
  have hH := ((hasDerivAt_id x).div_const 2).add (hsh.mul hch)
  have hK := ((hasDerivAt_id x).div_const 2).neg.add (hsh.mul hch)
  have hall := ((((hasDerivAt_id x).sub (hF.const_mul (2 * p))).add (hH.const_mul (p ^ 2))).sub
    (hG.const_mul (2 * q))).add (hK.const_mul (q ^ 2))
  have e1 : (2 * (-Real.sin (ω * x) * ω * Real.sinh (x / 2) +
      Real.cos (ω * x) * (Real.cosh (x / 2) * (1 / 2))) +
      4 * ω * (Real.cos (ω * x) * ω * Real.cosh (x / 2) +
        Real.sin (ω * x) * (Real.sinh (x / 2) * (1 / 2)))) / (1 + 4 * ω ^ 2) =
      Real.cos (ω * x) * Real.cosh (x / 2) := by
    rw [div_eq_iff hden]
    ring
  have e2 : (2 * (Real.cos (ω * x) * ω * Real.cosh (x / 2) +
      Real.sin (ω * x) * (Real.sinh (x / 2) * (1 / 2))) -
      4 * ω * (-Real.sin (ω * x) * ω * Real.sinh (x / 2) +
        Real.cos (ω * x) * (Real.cosh (x / 2) * (1 / 2)))) / (1 + 4 * ω ^ 2) =
      Real.sin (ω * x) * Real.sinh (x / 2) := by
    rw [div_eq_iff hden]
    ring
  have hsc := Real.sin_sq_add_cos_sq (ω * x)
  have hch2 := Real.cosh_sq (x / 2)
  refine (hall.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · rw [e1, e2]
    linear_combination (-1 : ℝ) * hsc + (q ^ 2 / 2 - p ^ 2 / 2) * hch2
  · simp only [poleResidualPrimitive, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id]
    ring

/-- **Closed form of the residual integral.** -/
theorem integral_poleResidual_eq_closedForm (a ω p q : ℝ) :
    ∫ x in (-a)..a, ((Real.cos (ω * x) - p * Real.cosh (x / 2)) ^ 2 +
        (Real.sin (ω * x) - q * Real.sinh (x / 2)) ^ 2) =
      poleResidualClosedForm a ω p q := by
  have hcont : Continuous (fun x : ℝ => (Real.cos (ω * x) - p * Real.cosh (x / 2)) ^ 2 +
      (Real.sin (ω * x) - q * Real.sinh (x / 2)) ^ 2) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_poleResidualPrimitive ω p q x) (hcont.intervalIntegrable _ _)]
  have hsa : Real.sinh a = 2 * Real.sinh (a / 2) * Real.cosh (a / 2) := by
    rw [← Real.sinh_two_mul]
    ring_nf
  unfold poleResidualPrimitive poleResidualClosedForm poleCosCoshIntegral poleSinSinhIntegral
  rw [hsa]
  simp only [mul_neg, neg_div, Real.cos_neg, Real.sin_neg, Real.sinh_neg, Real.cosh_neg]
  ring

theorem norm_sq_poleResidualL2_eq_closedForm (a : SuzukiPositiveAperture) (ξ p q : ℝ) :
    ‖poleResidualL2 a ξ p q‖ ^ 2 = poleResidualClosedForm a.1 (2 * Real.pi * ξ) p q := by
  rw [norm_sq_poleResidualL2, ← integral_poleResidual_eq_closedForm]

/-! ## Lipschitz dependence on the frequency -/

theorem norm_planeWaveProfile_sub_le (ξ m x : ℝ) :
    ‖planeWaveProfile ξ x - planeWaveProfile m x‖ ≤ 2 * Real.pi * |ξ - m| * |x| := by
  unfold planeWaveProfile
  have hsplit : Complex.exp (((2 * Real.pi * ξ * x : ℝ) : ℂ) * I) -
      Complex.exp (((2 * Real.pi * m * x : ℝ) : ℂ) * I) =
      Complex.exp (((2 * Real.pi * m * x : ℝ) : ℂ) * I) *
        (Complex.exp (I * ((2 * Real.pi * (ξ - m) * x : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hsplit, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  norm_num

theorem norm_sq_planeWaveL2_sub_le (a : SuzukiPositiveAperture) (ξ m : ℝ) :
    ‖planeWaveL2 a ξ - planeWaveL2 a m‖ ^ 2 ≤
      4 * Real.pi ^ 2 * (ξ - m) ^ 2 * (2 * a.1 ^ 3 / 3) := by
  rw [norm_sq_eq_integral_norm_sq]
  have hae : (fun x : ℝ => ‖((planeWaveL2 a ξ - planeWaveL2 a m : SoninL2) : ℝ → ℂ) x‖ ^ 2)
      =ᵐ[volume] (centralInterval a.1).indicator
        (fun x : ℝ => ‖planeWaveProfile ξ x - planeWaveProfile m x‖ ^ 2) := by
    filter_upwards [Lp.coeFn_sub (planeWaveL2 a ξ) (planeWaveL2 a m), planeWaveL2_coeFn a ξ,
      planeWaveL2_coeFn a m] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    by_cases hmem : x ∈ centralInterval a.1
    · rw [indicator_of_mem hmem, indicator_of_mem hmem, indicator_of_mem hmem]
    · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, indicator_of_notMem hmem]
      simp
  rw [integral_congr_ae hae, integral_indicator (measurableSet_centralInterval a.1)]
  have hcont1 : Continuous (fun x : ℝ => ‖planeWaveProfile ξ x - planeWaveProfile m x‖ ^ 2) :=
    ((continuous_planeWaveProfile ξ).sub (continuous_planeWaveProfile m)).norm.pow 2
  have hcont2 : Continuous (fun x : ℝ => 4 * Real.pi ^ 2 * (ξ - m) ^ 2 * x ^ 2) := by fun_prop
  have hle : ∫ x in centralInterval a.1, ‖planeWaveProfile ξ x - planeWaveProfile m x‖ ^ 2 ≤
      ∫ x in centralInterval a.1, 4 * Real.pi ^ 2 * (ξ - m) ^ 2 * x ^ 2 := by
    apply setIntegral_mono_on (hcont1.integrableOn_Icc) (hcont2.integrableOn_Icc)
      (measurableSet_centralInterval a.1)
    intro x _
    have h := norm_planeWaveProfile_sub_le ξ m x
    have hn : 0 ≤ ‖planeWaveProfile ξ x - planeWaveProfile m x‖ := norm_nonneg _
    calc ‖planeWaveProfile ξ x - planeWaveProfile m x‖ ^ 2 ≤
          (2 * Real.pi * |ξ - m| * |x|) ^ 2 := pow_le_pow_left₀ hn h 2
      _ = 4 * Real.pi ^ 2 * (ξ - m) ^ 2 * x ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, sq_abs, sq_abs]
          ring
  refine hle.trans (le_of_eq ?_)
  rw [centralInterval, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [a.property]),
    intervalIntegral.integral_const_mul, integral_pow]
  ring

/-- **The constrained Fourier bound at a frequency near a reference frequency.**  For a
pole-vanishing aperture vector, every `η > 0`, and every choice of the reference frequency `m`
and the real residual parameters `p, q`, the Fourier value at `ξ` is controlled by the closed
residual at `m` and the frequency offset. -/
theorem norm_fourier_sq_le_of_polar (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a)
    (hplus : inner ℂ (ccmPolarL2Vector a (1 / 2)) f.1 = 0)
    (hminus : inner ℂ (ccmPolarL2Vector a (-1 / 2)) f.1 = 0) (ξ m p q η : ℝ) (hη : 0 < η) :
    ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤
      ((1 + η) * poleResidualClosedForm a.1 (2 * Real.pi * m) p q +
        (1 + 1 / η) * (4 * Real.pi ^ 2 * (ξ - m) ^ 2 * (2 * a.1 ^ 3 / 3))) * ‖f‖ ^ 2 := by
  have hbase := norm_fourier_le_poleResidual a f hplus hminus ξ p q
  have hdiff : poleResidualL2 a ξ p q - poleResidualL2 a m p q =
      planeWaveL2 a ξ - planeWaveL2 a m := by
    unfold poleResidualL2
    abel
  have htri : ‖poleResidualL2 a ξ p q‖ ≤
      ‖poleResidualL2 a m p q‖ + ‖planeWaveL2 a ξ - planeWaveL2 a m‖ := by
    rw [← hdiff]
    calc ‖poleResidualL2 a ξ p q‖ =
          ‖poleResidualL2 a m p q + (poleResidualL2 a ξ p q - poleResidualL2 a m p q)‖ := by
            congr 1
            abel
      _ ≤ _ := norm_add_le _ _
  set u := ‖poleResidualL2 a m p q‖
  set v := ‖planeWaveL2 a ξ - planeWaveL2 a m‖
  have hu2 : u ^ 2 = poleResidualClosedForm a.1 (2 * Real.pi * m) p q :=
    norm_sq_poleResidualL2_eq_closedForm a m p q
  have hv2 : v ^ 2 ≤ 4 * Real.pi ^ 2 * (ξ - m) ^ 2 * (2 * a.1 ^ 3 / 3) :=
    norm_sq_planeWaveL2_sub_le a ξ m
  have hu0 : 0 ≤ u := norm_nonneg _
  have hv0 : 0 ≤ v := norm_nonneg _
  have hF0 : 0 ≤ ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ := norm_nonneg _
  have hf0 : 0 ≤ ‖f‖ := norm_nonneg _
  have hstep : ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ≤ (u + v) * ‖f‖ :=
    hbase.trans (mul_le_mul_of_nonneg_right htri hf0)
  have hsq : ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤ (u + v) ^ 2 * ‖f‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hF0 hstep 2
  have hyoung : (u + v) ^ 2 ≤ (1 + η) * u ^ 2 + (1 + 1 / η) * v ^ 2 := by
    have h2 : 2 * u * v ≤ η * u ^ 2 + v ^ 2 / η := by
      have hsq' : 0 ≤ (η * u - v) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
      have hexp : (η * u - v) ^ 2 / η = η * u ^ 2 - 2 * u * v + v ^ 2 / η := by
        field_simp
        ring
      linarith
    have : (1 + 1 / η) * v ^ 2 = v ^ 2 + v ^ 2 / η := by ring
    nlinarith
  calc ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤ (u + v) ^ 2 * ‖f‖ ^ 2 := hsq
    _ ≤ ((1 + η) * u ^ 2 + (1 + 1 / η) * v ^ 2) * ‖f‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hyoung (sq_nonneg _)
    _ ≤ _ := by
        rw [hu2]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have h1η : 0 ≤ 1 + 1 / η := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hv2 h1η]


/-! ## The certificate at the aperture `½ log 2` -/

/-- The aperture `a = ½ log 2`, i.e. multiplicative support `[2^{-1/2}, 2^{1/2}]`. -/
def halfLogTwoAperture : SuzukiPositiveAperture :=
  ⟨Real.log 2 / 2, by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity⟩

/-- The archimedean Weil symbol `W(ξ) = Re ψ(1/4 + iπξ) - log π`. -/
def archimedeanWeilSymbol (ξ : ℝ) : ℝ :=
  2 * gammaHardyPhaseRate (2 * Real.pi * ξ)

theorem archimedeanWeilSymbol_eq (ξ : ℝ) :
    archimedeanWeilSymbol ξ =
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I)).re -
        Real.log Real.pi := by
  unfold archimedeanWeilSymbol gammaHardyPhaseRate linePt
  have harg : (((1 / 2 : ℝ) : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) / 2 =
      ((1 / 4 : ℝ) : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [harg]
  ring

/-- `W` is even and nondecreasing in `|ξ|`. -/
theorem archimedeanWeilSymbol_mono {ξ ζ : ℝ} (h : |ξ| ≤ |ζ|) :
    archimedeanWeilSymbol ξ ≤ archimedeanWeilSymbol ζ := by
  rw [archimedeanWeilSymbol_eq, archimedeanWeilSymbol_eq]
  have hpi : |Real.pi * ξ| ≤ |Real.pi * ζ| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have := re_digamma_mono_of_abs_le (a := 1 / 4) (by norm_num) hpi
  linarith

/-- An `L²` vector vanishing outside the aperture is integrable. -/
theorem integrable_suzukiApertureHilbert (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : Integrable (f.1 : ℝ → ℂ) := by
  have hI : IntegrableOn (f.1 : ℝ → ℂ) (centralInterval a.1) := by
    haveI : IsFiniteMeasure (volume.restrict (centralInterval a.1)) :=
      ⟨by simp [centralInterval]⟩
    exact ((Lp.memLp f.1).restrict (centralInterval a.1)).integrable (by norm_num)
  have hind : (f.1 : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (f.1 : ℝ → ℂ) := by
    filter_upwards [suzukiApertureHilbert_ae_zero_outside a f] with x hx
    by_cases hmem : x ∈ centralInterval a.1
    · rw [indicator_of_mem hmem]
    · rw [indicator_of_notMem hmem]
      apply hx
      by_contra hle
      exact hmem (abs_le.mp (not_lt.mp hle))
  exact ((integrable_indicator_iff (measurableSet_centralInterval a.1)).2 hI).congr hind.symm

theorem fourierUnitary_ae_eq_fourier_of_integrable (u : SoninL2)
    (hu : Integrable (u : ℝ → ℂ) volume) :
    (fourierUnitary u : ℝ → ℂ) =ᵐ[volume] 𝓕 (u : ℝ → ℂ) := by
  have he := GaloisForLFunctions.HTGeometry.coeFn_fourierTransform_ae_eq_fourierIntegral u hu
  filter_upwards [he] with r hr
  change (fourierUnitary u : ℝ → ℂ) r = _ at hr
  rw [hr, Real.Lp.fourierTransform_apply, Real.fourier_eq, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [(memLp_one_iff_integrable.mpr hu).coeFn_toLp] with s hs
  rw [hs]

/-- The Fourier-side representative of a form-domain vector is the Fourier transform of its
aperture realization, almost everywhere. -/
theorem ccmFormDomain_ae_eq_fourier (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (u.1 : ℝ → ℂ) =ᵐ[volume]
      𝓕 (((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) : ℝ → ℂ) := by
  have hint := integrable_suzukiApertureHilbert a (ccmArchimedeanFormToAperture a u)
  have h1 := fourierUnitary_ae_eq_fourier_of_integrable _ hint
  have h2 : fourierUnitary (((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) :
      SoninL2)) = ccmArchimedeanWeightedToL2 u.1 :=
    fourierUnitary_ccmArchimedeanFourierToTime u.1
  rw [h2] at h1
  exact (ccmArchimedeanWeightedToL2_coeFn u.1).symm.trans h1

theorem memLp_two_ccmFormDomain (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    MemLp (u.1 : ℝ → ℂ) 2 volume :=
  (memLp_congr_ae (ccmArchimedeanWeightedToL2_coeFn u.1)).mp
    (Lp.memLp (ccmArchimedeanWeightedToL2 u.1))

theorem integrable_norm_sq_ccmFormDomain (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    Integrable (fun ξ : ℝ => ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) volume := by
  have := (memLp_two_ccmFormDomain a u).integrable_norm_rpow (by norm_num) (by norm_num)
  simpa using this

/-- Plancherel for the form domain. -/
theorem integral_norm_sq_ccmFormDomain (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    ∫ ξ : ℝ, ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 = ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  rw [norm_ccmArchimedeanFormToAperture, norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn u.1] with ξ h
  rw [h]

/-- At the aperture `½ log 2`, on the pole-vanishing subspace, the restricted Weil form is the
archimedean form: the polar term vanishes by the constraints, and the only prime term (`n = 2`)
is a translation by the full aperture diameter, which has null overlap. -/
theorem ccmRestrictedWeilSourceQuadratic_halfLogTwo_eq (u : CCMArchimedeanFormDomain
    halfLogTwoAperture) (hu : IsPolarConstrained halfLogTwoAperture u) :
    ccmRestrictedWeilSourceQuadratic halfLogTwoAperture u =
      ∫ ξ : ℝ, archimedeanWeilSymbol ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 := by
  have hfloor : Nat.floor (Real.exp (2 * halfLogTwoAperture.1)) = 2 := by
    have : Real.exp (2 * halfLogTwoAperture.1) = 2 := by
      change Real.exp (2 * (Real.log 2 / 2)) = 2
      rw [show 2 * (Real.log 2 / 2) = Real.log 2 by ring, Real.exp_log (by norm_num)]
    rw [this]
    norm_num
  have hlog : Real.log ((2 : ℕ) : ℝ) = 2 * halfLogTwoAperture.1 := by
    change Real.log ((2 : ℕ) : ℝ) = 2 * (Real.log 2 / 2)
    push_cast
    ring
  have hpos : inner ℂ (logTranslationCLM (Real.log ((2 : ℕ) : ℝ))
      (ccmArchimedeanFormToAperture halfLogTwoAperture u).1)
      (ccmArchimedeanFormToAperture halfLogTwoAperture u).1 = 0 := by
    rw [hlog]
    exact inner_logTranslationCLM_two_aperture_eq_zero halfLogTwoAperture _
  have hneg : inner ℂ (logTranslationCLM (-Real.log ((2 : ℕ) : ℝ))
      (ccmArchimedeanFormToAperture halfLogTwoAperture u).1)
      (ccmArchimedeanFormToAperture halfLogTwoAperture u).1 = 0 := by
    rw [inner_logTranslationCLM, neg_neg, ← inner_conj_symm, hpos, map_zero]
  unfold ccmRestrictedWeilSourceQuadratic
  simp only
  rw [hfloor, hu.1, hu.2]
  simp only [mul_zero, add_zero, Complex.zero_re, Finset.Icc_self,
    Finset.sum_singleton]
  rw [hpos, hneg]
  simp only [add_zero, Complex.zero_re, mul_zero, sub_zero]
  apply integral_congr_ae
  filter_upwards with ξ
  unfold archimedeanWeilSymbol
  ring

/-! ## The grid certificate -/

/-- The step weight of the certificate: `G k` on both frequency shells `k h ≤ |ξ| < (k+1) h`. -/
def gridStepWeight (h : ℝ) (K : ℕ) (G : ℕ → ℝ) (ξ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, G k *
    ((Ico (k * h) ((k + 1) * h)).indicator (fun _ => (1 : ℝ)) ξ +
      (Ioc (-((k + 1) * h)) (-(k * h))).indicator (fun _ => (1 : ℝ)) ξ)

theorem gridStepWeight_nonneg {h : ℝ} {K : ℕ} {G : ℕ → ℝ} (hG : ∀ k, 0 ≤ G k) (ξ : ℝ) :
    0 ≤ gridStepWeight h K G ξ := by
  unfold gridStepWeight
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (hG k)
  apply add_nonneg <;> exact Set.indicator_nonneg (fun _ _ => by norm_num) _

theorem gridStepWeight_le {h : ℝ} {K : ℕ} {G : ℕ → ℝ} (ξ : ℝ) :
    gridStepWeight h K G ξ ≤ ∑ k ∈ Finset.range K, 2 * |G k| := by
  unfold gridStepWeight
  apply Finset.sum_le_sum
  intro k _
  have h1 : (Ico (k * h) ((k + 1) * h)).indicator (fun _ => (1 : ℝ)) ξ ≤ 1 := by
    unfold Set.indicator
    split_ifs <;> norm_num
  have h2 : (Ioc (-((k + 1) * h)) (-(k * h))).indicator (fun _ => (1 : ℝ)) ξ ≤ 1 := by
    unfold Set.indicator
    split_ifs <;> norm_num
  have h1' : 0 ≤ (Ico (k * h) ((k + 1) * h)).indicator (fun _ => (1 : ℝ)) ξ :=
    Set.indicator_nonneg (fun _ _ => by norm_num) _
  have h2' : 0 ≤ (Ioc (-((k + 1) * h)) (-(k * h))).indicator (fun _ => (1 : ℝ)) ξ :=
    Set.indicator_nonneg (fun _ _ => by norm_num) _
  calc G k * (_ + _) ≤ |G k| * (_ + _) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (add_nonneg h1' h2')
    _ ≤ |G k| * 2 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = 2 * |G k| := by ring

theorem measurable_gridStepWeight (h : ℝ) (K : ℕ) (G : ℕ → ℝ) :
    Measurable (gridStepWeight h K G) := by
  unfold gridStepWeight
  apply Finset.measurable_sum
  intro k _
  apply Measurable.const_mul
  exact (measurable_const.indicator measurableSet_Ico).add
    (measurable_const.indicator measurableSet_Ioc)

/-- The symbol lies above `α` minus the step weight, given the grid values. -/
theorem sub_gridStepWeight_le_archimedeanWeilSymbol {α h : ℝ} (hh : 0 < h) {K : ℕ}
    {G : ℕ → ℝ} (hG : ∀ k, 0 ≤ G k)
    (hWk : ∀ k < K, α - G k ≤ archimedeanWeilSymbol (k * h))
    (hWK : α ≤ archimedeanWeilSymbol (K * h)) (ξ : ℝ) :
    α - gridStepWeight h K G ξ ≤ archimedeanWeilSymbol ξ := by
  by_cases hbig : (K : ℝ) * h ≤ |ξ|
  · have hmono := archimedeanWeilSymbol_mono (ξ := K * h) (ζ := ξ)
      (by rw [abs_of_nonneg (by positivity)]; exact hbig)
    have := gridStepWeight_nonneg (h := h) (K := K) hG ξ
    linarith
  · push Not at hbig
    set j := Nat.floor (|ξ| / h) with hj
    have hjle : (j : ℝ) * h ≤ |ξ| := by
      have := Nat.floor_le (div_nonneg (abs_nonneg ξ) hh.le)
      rw [← hj] at this
      calc (j : ℝ) * h ≤ |ξ| / h * h := mul_le_mul_of_nonneg_right this hh.le
        _ = |ξ| := div_mul_cancel₀ _ hh.ne'
    have hjlt : |ξ| < ((j : ℝ) + 1) * h := by
      have := Nat.lt_floor_add_one (|ξ| / h)
      rw [← hj] at this
      calc |ξ| = |ξ| / h * h := (div_mul_cancel₀ _ hh.ne').symm
        _ < ((j : ℝ) + 1) * h := mul_lt_mul_of_pos_right this hh
    have hjK : j < K := by
      by_contra hcon
      push Not at hcon
      have : (K : ℝ) * h ≤ (j : ℝ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcon) hh.le
      linarith
    have hterm : G j ≤ gridStepWeight h K G ξ := by
      unfold gridStepWeight
      have hmem : G j ≤ G j *
          ((Ico (j * h) ((j + 1) * h)).indicator (fun _ => (1 : ℝ)) ξ +
            (Ioc (-((j + 1) * h)) (-(j * h))).indicator (fun _ => (1 : ℝ)) ξ) := by
        rcases le_or_gt 0 ξ with hξ | hξ
        · rw [abs_of_nonneg hξ] at hjle hjlt
          rw [Set.indicator_of_mem (show ξ ∈ Ico ((j : ℝ) * h) (((j : ℝ) + 1) * h) from
            ⟨hjle, hjlt⟩)]
          have : 0 ≤ (Ioc (-(((j : ℝ) + 1) * h)) (-((j : ℝ) * h))).indicator
            (fun _ => (1 : ℝ)) ξ := Set.indicator_nonneg (fun _ _ => by norm_num) _
          nlinarith [hG j]
        · rw [abs_of_neg hξ] at hjle hjlt
          rw [Set.indicator_of_mem (show ξ ∈ Ioc (-(((j : ℝ) + 1) * h)) (-((j : ℝ) * h)) from
            ⟨by linarith, by linarith⟩)]
          have : 0 ≤ (Ico ((j : ℝ) * h) (((j : ℝ) + 1) * h)).indicator
            (fun _ => (1 : ℝ)) ξ := Set.indicator_nonneg (fun _ _ => by norm_num) _
          nlinarith [hG j]
      refine hmem.trans ?_
      apply Finset.single_le_sum (f := fun k => G k *
        ((Ico (k * h) ((k + 1) * h)).indicator (fun _ => (1 : ℝ)) ξ +
          (Ioc (-((k + 1) * h)) (-(k * h))).indicator (fun _ => (1 : ℝ)) ξ))
      · intro k _
        apply mul_nonneg (hG k)
        apply add_nonneg <;> exact Set.indicator_nonneg (fun _ _ => by norm_num) _
      · exact Finset.mem_range.mpr hjK
    have hmono := archimedeanWeilSymbol_mono (ξ := j * h) (ζ := ξ)
      (by rw [abs_of_nonneg (by positivity)]; exact hjle)
    have := hWk j hjK
    linarith

/-- **The trace certificate for the pole-vanishing ground energy at `½ log 2`.**  If the
archimedean symbol is at least `α - G k` at the grid points `k h`, at least `α` at `K h`, and the
Fourier mass of every pole-vanishing aperture vector is at most `R k ‖f‖²` on the shell
`k h ≤ |ξ| < (k+1) h`, then the pole-vanishing ground energy is at least
`α - Σ_k 2 h G k R k`. -/
theorem le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo_of_grid {α h : ℝ} (hh : 0 < h)
    {K : ℕ} {G R : ℕ → ℝ} (hG : ∀ k, 0 ≤ G k)
    (hWk : ∀ k < K, α - G k ≤ archimedeanWeilSymbol (k * h))
    (hWK : α ≤ archimedeanWeilSymbol (K * h))
    (hR : ∀ k < K, ∀ f : suzukiApertureHilbert halfLogTwoAperture,
      inner ℂ (ccmPolarL2Vector halfLogTwoAperture (1 / 2)) f.1 = 0 →
      inner ℂ (ccmPolarL2Vector halfLogTwoAperture (-1 / 2)) f.1 = 0 →
      ∀ ξ : ℝ, (k : ℝ) * h ≤ |ξ| → |ξ| < ((k : ℝ) + 1) * h →
        ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤ R k * ‖f‖ ^ 2) :
    α - ∑ k ∈ Finset.range K, 2 * h * G k * R k ≤
      ccmRestrictedWeilPolarGroundEnergy halfLogTwoAperture := by
  apply le_ccmRestrictedWeilPolarGroundEnergy_of_floor
  intro u hu
  set f := ccmArchimedeanFormToAperture halfLogTwoAperture u with hfdef
  have hplus : inner ℂ (ccmPolarL2Vector halfLogTwoAperture (1 / 2)) f.1 = 0 := hu.1
  have hminus : inner ℂ (ccmPolarL2Vector halfLogTwoAperture (-1 / 2)) f.1 = 0 := hu.2
  rw [ccmRestrictedWeilSourceQuadratic_halfLogTwo_eq u hu]
  set φ : ℝ → ℝ := fun ξ => ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 with hφ
  have hφint : Integrable φ := integrable_norm_sq_ccmFormDomain _ u
  have hφnn : ∀ ξ, 0 ≤ φ ξ := fun ξ => by positivity
  have hφF : φ =ᵐ[volume] fun ξ => ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 := by
    filter_upwards [ccmFormDomain_ae_eq_fourier halfLogTwoAperture u] with ξ hξ
    simp only [hφ, hξ, hfdef]
  set g := gridStepWeight h K G
  have hgmeas : Measurable g := measurable_gridStepWeight h K G
  have hgbdd : ∀ ξ, ‖g ξ‖ ≤ ∑ k ∈ Finset.range K, 2 * |G k| := by
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (gridStepWeight_nonneg hG ξ)]
    exact gridStepWeight_le ξ
  have hgφint : Integrable (fun ξ => g ξ * φ ξ) :=
    hφint.bdd_mul hgmeas.aestronglyMeasurable (Filter.Eventually.of_forall hgbdd)
  have hWint : Integrable (fun ξ => archimedeanWeilSymbol ξ * φ ξ) := by
    have := integrable_two_gammaHardyPhaseRate_mul_norm_sq u.1
    simpa [archimedeanWeilSymbol, hφ] using this
  -- step 1: the symbol dominates `α - g`
  have hstep1 : ∫ ξ, (α - g ξ) * φ ξ ≤ ∫ ξ, archimedeanWeilSymbol ξ * φ ξ := by
    apply integral_mono ((hφint.const_mul α).sub hgφint |>.congr
      (Filter.Eventually.of_forall fun ξ => by simp only [Pi.sub_apply]; ring)) hWint
    intro ξ
    exact mul_le_mul_of_nonneg_right
      (sub_gridStepWeight_le_archimedeanWeilSymbol hh hG hWk hWK ξ) (hφnn ξ)
  have hsplit : ∫ ξ, (α - g ξ) * φ ξ = (α * ∫ ξ, φ ξ) - ∫ ξ, g ξ * φ ξ := by
    have hfun : (fun ξ => (α - g ξ) * φ ξ) = fun ξ => α * φ ξ - g ξ * φ ξ := by
      funext ξ
      ring
    rw [hfun, integral_sub (hφint.const_mul α) hgφint, integral_const_mul]
  -- step 2: the step integral
  have hshell : ∀ k < K, ∀ S : Set ℝ, MeasurableSet S →
      (∀ ξ ∈ S, (k : ℝ) * h ≤ |ξ| ∧ |ξ| < ((k : ℝ) + 1) * h) → volume S ≤ ENNReal.ofReal h →
      ∫ ξ in S, φ ξ ≤ h * (R k * ‖f‖ ^ 2) := by
    intro k hk S hS hSmem hvol
    have hR0 : 0 ≤ R k * ‖f‖ ^ 2 := by
      have hpt := hR k hk f hplus hminus (k * h) (by
        rw [abs_of_nonneg (by positivity)]) (by
        rw [abs_of_nonneg (by positivity)]; nlinarith)
      exact (sq_nonneg _).trans hpt
    have hle : ∫ ξ in S, φ ξ ≤ ∫ ξ in S, R k * ‖f‖ ^ 2 := by
      have hfin : volume S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
      apply setIntegral_mono_ae_restrict hφint.integrableOn (integrableOn_const hfin)
      rw [Filter.EventuallyLE, ae_restrict_iff' hS]
      filter_upwards [hφF] with ξ hξ hmem
      rw [hξ]
      exact hR k hk f hplus hminus ξ (hSmem ξ hmem).1 (hSmem ξ hmem).2
    refine hle.trans ?_
    rw [setIntegral_const, smul_eq_mul]
    have hvolr : volume.real S ≤ h := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hh.le hvol
    exact mul_le_mul_of_nonneg_right hvolr hR0
  have hstep2 : ∫ ξ, g ξ * φ ξ ≤
      ∑ k ∈ Finset.range K, 2 * h * G k * R k * ‖f‖ ^ 2 := by
    have hexp : (fun ξ => g ξ * φ ξ) = fun ξ => ∑ k ∈ Finset.range K,
        (G k * ((Ico (k * h) ((k + 1) * h)).indicator φ ξ +
          (Ioc (-((k + 1) * h)) (-(k * h))).indicator φ ξ)) := by
      funext ξ
      simp only [g, gridStepWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Set.indicator_apply]
      split_ifs <;> ring
    rw [hexp, integral_finsetSum]
    · apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [integral_const_mul, integral_add (hφint.indicator measurableSet_Ico)
        (hφint.indicator measurableSet_Ioc), integral_indicator measurableSet_Ico,
        integral_indicator measurableSet_Ioc]
      have hpos := hshell k hk' (Ico (k * h) ((k + 1) * h)) measurableSet_Ico
        (fun ξ hξ => by
          have h0 : 0 ≤ (k : ℝ) * h := by positivity
          rw [abs_of_nonneg (h0.trans hξ.1)]
          exact ⟨hξ.1, hξ.2⟩)
        (by rw [Real.volume_Ico]; apply le_of_eq; congr 1; ring)
      have hneg := hshell k hk' (Ioc (-((k + 1) * h)) (-(k * h))) measurableSet_Ioc
        (fun ξ hξ => by
          have h0 : 0 ≤ (k : ℝ) * h := by positivity
          by_cases hz : ξ = 0
          · subst hz
            have hk0 : (k : ℝ) * h = 0 := by
              have := hξ.2
              linarith
            simp only [abs_zero]
            exact ⟨hk0.le, by nlinarith⟩
          · have hξneg : ξ ≤ 0 := hξ.2.trans (by linarith)
            rw [abs_of_nonpos hξneg]
            exact ⟨by linarith [hξ.2], by linarith [hξ.1]⟩)
        (by rw [Real.volume_Ioc]; apply le_of_eq; congr 1; ring)
      have hGk := hG k
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hpos hneg) hGk]
    · intro k _
      exact ((hφint.indicator measurableSet_Ico).add
        (hφint.indicator measurableSet_Ioc)).const_mul _
  have hnorm : ∫ ξ, φ ξ = ‖f‖ ^ 2 := integral_norm_sq_ccmFormDomain _ u
  rw [hsplit, hnorm] at hstep1
  have hsum : ∑ k ∈ Finset.range K, 2 * h * G k * R k * ‖f‖ ^ 2 =
      (∑ k ∈ Finset.range K, 2 * h * G k * R k) * ‖f‖ ^ 2 := by
    rw [Finset.sum_mul]
  have hfin : (α - ∑ k ∈ Finset.range K, 2 * h * G k * R k) * ‖f‖ ^ 2 =
      α * ‖f‖ ^ 2 - (∑ k ∈ Finset.range K, 2 * h * G k * R k) * ‖f‖ ^ 2 := by ring
  rw [hfin]
  linarith [hstep1, hstep2, hsum]

end RHTower
