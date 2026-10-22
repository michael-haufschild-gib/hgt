import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedOrientationRankUniversalityLaw
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain
import GaloisForLFunctions.HTGeometry.VerticalModulusDerivative

/-!
# Zero-safe divisor tomography of the theta-cusp center-mixed current

The completed center-mixed current is more than a global RH-equivalent sign coordinate. At every
centered Xi zero of analytic multiplicity `m`, it has an exact planar normal form whose leading
homogeneous cone has degree `2m - 1`. On the transverse line through the zero, a strictly positive
residual forces a negative current immediately on the critical-line side and a positive current
immediately on the exterior side.

This is unconditional divisor tomography, not RH. It proves that infinite shell cancellation
cannot hide a hypothetical off-critical zero: the completed current itself retains its side,
location, and multiplicity without division by `XiC`.
-/

open Complex Set Filter Topology
open scoped Topology

namespace HTGeometry

/-- **The opposite vertical orientation, valid at zeros.** Along the transverse path
`b - a i`, the squared modulus has derivative `2 Im (f' * conj f)`. -/
theorem hasDerivAt_normSq_transverse_general (f : ℂ → ℂ) (b a : ℝ)
    (hf : DifferentiableAt ℂ f ((b : ℂ) - (a : ℂ) * I)) :
    HasDerivAt
      (fun t : ℝ => Complex.normSq (f ((b : ℂ) - (t : ℂ) * I)))
      (2 * (deriv f ((b : ℂ) - (a : ℂ) * I) *
        (starRingEnd ℂ) (f ((b : ℂ) - (a : ℂ) * I))).im) a := by
  have hvertical := hasDerivAt_normSq_vertical_general f b (-a) (by
    convert hf using 1
    push_cast
    ring)
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) a := by
    simpa only [Pi.neg_apply, id_eq] using! (hasDerivAt_id a).neg
  have hcomp := hvertical.comp a hneg
  have harg : (b : ℂ) + ((-a : ℝ) : ℂ) * I = (b : ℂ) - (a : ℂ) * I := by
    push_cast
    ring
  have hderiv :
      -2 * (deriv f ((b : ℂ) + ((-a : ℝ) : ℂ) * I) *
          (starRingEnd ℂ) (f ((b : ℂ) + ((-a : ℝ) : ℂ) * I))).im * -1 =
        2 * (deriv f ((b : ℂ) - (a : ℂ) * I) *
          (starRingEnd ℂ) (f ((b : ℂ) - (a : ℂ) * I))).im := by
    rw [harg]
    ring
  apply (hcomp.congr_deriv hderiv).congr_of_eventuallyEq
  filter_upwards with t
  simp only [Function.comp_apply, Complex.ofReal_neg, neg_mul]
  rw [sub_eq_add_neg]

end HTGeometry

namespace RHTower

noncomputable section

/-- Zero-safe transverse derivative of completed-Xi energy. Unlike a logarithmic derivative, this
is defined at Xi zeros. -/
def xiTransverseEnergyCurrent (a b : ℝ) : ℝ :=
  2 * (deriv XiC ((b : ℂ) - (a : ℂ) * I) *
    (starRingEnd ℂ) (XiC ((b : ℂ) - (a : ℂ) * I))).im

/-- The zero-safe current is the derivative of the squared Xi modulus on every transverse line. -/
theorem hasDerivAt_normSq_XiC_transverse (a b : ℝ) :
    HasDerivAt
      (fun t : ℝ => Complex.normSq (XiC ((b : ℂ) - (t : ℂ) * I)))
      (xiTransverseEnergyCurrent a b) a := by
  exact HTGeometry.hasDerivAt_normSq_transverse_general XiC b a
    (XiC_analytic _ (Set.mem_univ _)).differentiableAt

/-- On the full Fourier--Laplace strip, the algebraic zero-safe current is exactly the actual
theta-cusp center-mixed Fourier current. -/
theorem thetaCuspCenterMixedFourierCurrent_eq_xiTransverseEnergyCurrent
    {a b : ℝ} (ha : |a| < 1) :
    thetaCuspCenterMixedFourierCurrent a ha b = xiTransverseEnergyCurrent a b := by
  rw [thetaCuspCenterMixedFourierCurrent,
    fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm ha b]
  rw [thetaXiHankelOrbit_kreinForm_eq]
  simp only [Complex.ofReal_re, thetaXiHankelOrbitValuePlus,
    thetaXiHankelOrbitTangentPlus, xiTransverseEnergyCurrent]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.neg_re, Complex.neg_im, I_re, I_im]
  ring

/-- Signed transverse displacement from a centered Xi divisor point. Its zero is the physical
aperture of that point. -/
def xiSupportTransverseDisplacement (rho : XiDivisorSupport) (a : ℝ) : ℝ :=
  a + (xiSpectralPointSupport rho).im

/-- Transverse line through the real coordinate of one centered Xi divisor point. -/
def xiSupportTransversePoint (rho : XiDivisorSupport) (a : ℝ) : ℂ :=
  ((xiSpectralPointSupport rho).re : ℂ) - (a : ℂ) * I

/-- Canonical entire cofactor after removing the full analytic multiplicity at `rho`. -/
def xiSupportCofactor (rho : XiDivisorSupport) : ℂ → ℂ :=
  xiThetaDividedChain (xiSpectralPointSupport rho) (xiSupportMultiplicity rho)

/-- Residual after removing the exact odd transverse divisor power from the current. -/
def xiSupportTransverseResidual (rho : XiDivisorSupport) (a : ℝ) : ℝ :=
  2 * (xiSupportMultiplicity rho : ℝ) *
      Complex.normSq (xiSupportCofactor rho (xiSupportTransversePoint rho a)) +
    2 * xiSupportTransverseDisplacement rho a *
      (deriv (xiSupportCofactor rho) (xiSupportTransversePoint rho a) *
        (starRingEnd ℂ)
          (xiSupportCofactor rho (xiSupportTransversePoint rho a))).im

lemma xiSupportTransversePoint_sub (rho : XiDivisorSupport) (a : ℝ) :
    xiSupportTransversePoint rho a - xiSpectralPointSupport rho =
      -(xiSupportTransverseDisplacement rho a : ℂ) * I := by
  apply Complex.ext <;>
    simp [xiSupportTransversePoint, xiSupportTransverseDisplacement]
  ring

@[simp] lemma xiSupportTransversePoint_center (rho : XiDivisorSupport) :
    xiSupportTransversePoint rho (-(xiSpectralPointSupport rho).im) =
      xiSpectralPointSupport rho := by
  apply Complex.ext <;> simp [xiSupportTransversePoint]

@[simp] lemma xiSupportTransverseDisplacement_center (rho : XiDivisorSupport) :
    xiSupportTransverseDisplacement rho (-(xiSpectralPointSupport rho).im) = 0 := by
  simp [xiSupportTransverseDisplacement]

/-- Exact squared-energy factorization on the transverse through a divisor point. -/
theorem normSq_XiC_support_transverse (rho : XiDivisorSupport) (a : ℝ) :
    Complex.normSq (XiC (xiSupportTransversePoint rho a)) =
      xiSupportTransverseDisplacement rho a ^ (2 * xiSupportMultiplicity rho) *
        Complex.normSq (xiSupportCofactor rho (xiSupportTransversePoint rho a)) := by
  rw [xiThetaDividedChain_factorization]
  rw [Complex.normSq_mul, map_pow, xiSupportTransversePoint_sub]
  simp only [map_mul, Complex.normSq_I, mul_one, Complex.normSq_neg,
    Complex.normSq_ofReal]
  rw [show xiSupportTransverseDisplacement rho a *
      xiSupportTransverseDisplacement rho a =
        xiSupportTransverseDisplacement rho a ^ 2 by ring, pow_mul]
  rfl

/-- **Exact odd divisor factorization.** At multiplicity `m`, the transverse current contains the
power `(a + Im alpha)^(2m-1)` and no larger power: its residual is positive at the divisor. -/
theorem xiTransverseEnergyCurrent_support_factorization
    (rho : XiDivisorSupport) (a : ℝ) :
    xiTransverseEnergyCurrent a (xiSpectralPointSupport rho).re =
      xiSupportTransverseDisplacement rho a ^ (2 * xiSupportMultiplicity rho - 1) *
        xiSupportTransverseResidual rho a := by
  let m := xiSupportMultiplicity rho
  let x := xiSupportTransverseDisplacement rho
  let z := xiSupportTransversePoint rho
  let Q := xiSupportCofactor rho
  have hm : 0 < m := xiSupportMultiplicity_pos rho
  have hx : HasDerivAt x 1 a := by
    simpa only [x, xiSupportTransverseDisplacement, one_mul] using!
      (hasDerivAt_id a).add_const (xiSpectralPointSupport rho).im
  have hpow := hx.pow (2 * m)
  have hQ : DifferentiableAt ℂ Q (z a) :=
    (xiThetaDividedChain_analyticAt _ _ _).differentiableAt
  have hQenergy :
      HasDerivAt (fun t : ℝ => Complex.normSq (Q (z t)))
        (2 * (deriv Q (z a) * (starRingEnd ℂ) (Q (z a))).im) a := by
    simpa only [Q, z, xiSupportTransversePoint] using
      HTGeometry.hasDerivAt_normSq_transverse_general Q
        (xiSpectralPointSupport rho).re a hQ
  have hproduct := hpow.mul hQenergy
  have hfactorDeriv :
      HasDerivAt
        (fun t : ℝ => x t ^ (2 * m) * Complex.normSq (Q (z t)))
        (x a ^ (2 * m - 1) * xiSupportTransverseResidual rho a) a := by
    apply hproduct.congr_deriv
    simp only [Pi.pow_apply]
    have hexp : 2 * m = (2 * m - 1) + 1 := by omega
    rw [show x a ^ (2 * m) = x a ^ (2 * m - 1) * x a by
      conv_lhs => rw [hexp, pow_succ]]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    dsimp only [xiSupportTransverseResidual, x, z, Q, m]
    ring
  have hfactorDeriv' :
      HasDerivAt
        (fun t : ℝ => Complex.normSq (XiC (z t)))
        (x a ^ (2 * m - 1) * xiSupportTransverseResidual rho a) a := by
    apply hfactorDeriv.congr_of_eventuallyEq
    filter_upwards with t
    simpa only [x, z, Q, m] using normSq_XiC_support_transverse rho t
  have hcurrent := hasDerivAt_normSq_XiC_transverse a
    (xiSpectralPointSupport rho).re
  exact hcurrent.unique
    (by simpa only [x, z, m, xiSupportTransversePoint] using hfactorDeriv')

/-- The transverse residual is globally continuous. -/
theorem continuous_xiSupportTransverseResidual (rho : XiDivisorSupport) :
    Continuous (xiSupportTransverseResidual rho) := by
  have hQ : Continuous (xiSupportCofactor rho) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (xiThetaDividedChain_analyticAt _ _ z).continuousAt)
  have hQ' : Continuous (deriv (xiSupportCofactor rho)) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (xiThetaDividedChain_analyticAt _ _ z).deriv.continuousAt)
  unfold xiSupportTransverseResidual xiSupportTransversePoint
    xiSupportTransverseDisplacement
  fun_prop

/-- At the divisor, the residual is the strictly positive multiplicity-weighted cofactor norm. -/
theorem xiSupportTransverseResidual_center (rho : XiDivisorSupport) :
    xiSupportTransverseResidual rho (-(xiSpectralPointSupport rho).im) =
      2 * (xiSupportMultiplicity rho : ℝ) *
        Complex.normSq (xiSupportCofactor rho (xiSpectralPointSupport rho)) := by
  rw [xiSupportTransverseResidual, xiSupportTransverseDisplacement_center,
    xiSupportTransversePoint_center]
  ring

theorem xiSupportTransverseResidual_center_pos (rho : XiDivisorSupport) :
    0 < xiSupportTransverseResidual rho (-(xiSpectralPointSupport rho).im) := by
  rw [xiSupportTransverseResidual_center]
  exact mul_pos
    (mul_pos (by norm_num) (Nat.cast_pos.mpr (xiSupportMultiplicity_pos rho)))
    (Complex.normSq_pos.mpr (xiThetaDividedChain_nonzero_at_multiplicity rho))

/-- The zero-safe current vanishes at the divisor itself. -/
theorem xiTransverseEnergyCurrent_at_support (rho : XiDivisorSupport) :
    xiTransverseEnergyCurrent (-(xiSpectralPointSupport rho).im)
      (xiSpectralPointSupport rho).re = 0 := by
  rw [xiTransverseEnergyCurrent_support_factorization,
    xiSupportTransverseDisplacement_center]
  have hm := xiSupportMultiplicity_pos rho
  have hpow : 2 * xiSupportMultiplicity rho - 1 ≠ 0 := by
    omega
  rw [zero_pow hpow, zero_mul]

/-- Punctured normalization of the current converges to a positive constant. This certifies the
exact transverse vanishing order `2m-1` without dividing by Xi. -/
theorem tendsto_xiTransverseEnergyCurrent_normalized_at_support
    (rho : XiDivisorSupport) :
    Tendsto
      (fun a => xiTransverseEnergyCurrent a (xiSpectralPointSupport rho).re /
        xiSupportTransverseDisplacement rho a ^ (2 * xiSupportMultiplicity rho - 1))
      (𝓝[≠] (-(xiSpectralPointSupport rho).im))
      (𝓝 (2 * (xiSupportMultiplicity rho : ℝ) *
        Complex.normSq (xiSupportCofactor rho (xiSpectralPointSupport rho)))) := by
  have hres : Tendsto (xiSupportTransverseResidual rho)
      (𝓝[≠] (-(xiSpectralPointSupport rho).im))
      (𝓝 (xiSupportTransverseResidual rho (-(xiSpectralPointSupport rho).im))) :=
    (continuous_xiSupportTransverseResidual rho).continuousAt.mono_left inf_le_left
  rw [← xiSupportTransverseResidual_center]
  apply hres.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have hdisp : xiSupportTransverseDisplacement rho a ≠ 0 := by
    intro hzero
    apply ha
    simp only [mem_singleton_iff]
    dsimp [xiSupportTransverseDisplacement] at hzero
    linarith
  rw [xiTransverseEnergyCurrent_support_factorization]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero _ hdisp)).symm

/-- A divisor point forces opposite strict signs on the two sides of its transverse aperture. -/
theorem exists_xiTransverseEnergyCurrent_local_sign (rho : XiDivisorSupport) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ a : ℝ, |a + (xiSpectralPointSupport rho).im| < ε →
        (a < -(xiSpectralPointSupport rho).im →
          xiTransverseEnergyCurrent a (xiSpectralPointSupport rho).re < 0) ∧
        (-(xiSpectralPointSupport rho).im < a →
          0 < xiTransverseEnergyCurrent a (xiSpectralPointSupport rho).re) := by
  let d := -(xiSpectralPointSupport rho).im
  have hposNhd : {a : ℝ | 0 < xiSupportTransverseResidual rho a} ∈ 𝓝 d :=
    (continuous_xiSupportTransverseResidual rho).continuousAt.eventually
      (Ioi_mem_nhds (by simpa only [d] using xiSupportTransverseResidual_center_pos rho))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hposNhd
  refine ⟨ε, hε, ?_⟩
  intro a haClose
  have hres : 0 < xiSupportTransverseResidual rho a := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp only [d]
    simpa only [sub_neg_eq_add] using haClose
  constructor
  · intro ha
    rw [xiTransverseEnergyCurrent_support_factorization]
    have hdisp : xiSupportTransverseDisplacement rho a < 0 := by
      dsimp [xiSupportTransverseDisplacement, d] at ha ⊢
      linarith
    have hodd : Odd (2 * xiSupportMultiplicity rho - 1) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
        (ne_of_gt (xiSupportMultiplicity_pos rho))
      rw [hk]
      use k
      omega
    exact mul_neg_of_neg_of_pos (hodd.pow_neg hdisp) hres
  · intro ha
    rw [xiTransverseEnergyCurrent_support_factorization]
    have hdisp : 0 < xiSupportTransverseDisplacement rho a := by
      dsimp [xiSupportTransverseDisplacement, d] at ha ⊢
      linarith
    exact mul_pos (pow_pos hdisp _) hres

/-- Point in the full two-dimensional transverse/tangential plane around a support point. -/
def xiSupportPlanePoint (_rho : XiDivisorSupport) (a b : ℝ) : ℂ :=
  (b : ℂ) - (a : ℂ) * I

def xiSupportTangentialDisplacement (rho : XiDivisorSupport) (b : ℝ) : ℝ :=
  b - (xiSpectralPointSupport rho).re

def xiSupportRadiusSq (rho : XiDivisorSupport) (a b : ℝ) : ℝ :=
  xiSupportTransverseDisplacement rho a ^ 2 +
    xiSupportTangentialDisplacement rho b ^ 2

/-- Residual after removing the radial power `(x²+y²)^(m-1)` from the planar current. -/
def xiSupportPlanarResidual (rho : XiDivisorSupport) (a b : ℝ) : ℝ :=
  2 * (xiSupportMultiplicity rho : ℝ) * xiSupportTransverseDisplacement rho a *
      Complex.normSq (xiSupportCofactor rho (xiSupportPlanePoint rho a b)) +
    xiSupportRadiusSq rho a b *
      (2 * (deriv (xiSupportCofactor rho) (xiSupportPlanePoint rho a b) *
        (starRingEnd ℂ) (xiSupportCofactor rho (xiSupportPlanePoint rho a b))).im)

lemma xiSupportPlanePoint_sub (rho : XiDivisorSupport) (a b : ℝ) :
    xiSupportPlanePoint rho a b - xiSpectralPointSupport rho =
      (xiSupportTangentialDisplacement rho b : ℂ) -
        (xiSupportTransverseDisplacement rho a : ℂ) * I := by
  apply Complex.ext <;>
    simp [xiSupportPlanePoint, xiSupportTangentialDisplacement,
      xiSupportTransverseDisplacement]
  ring

/-- Exact planar squared-energy factorization by the radial divisor power. -/
theorem normSq_XiC_support_plane (rho : XiDivisorSupport) (a b : ℝ) :
    Complex.normSq (XiC (xiSupportPlanePoint rho a b)) =
      xiSupportRadiusSq rho a b ^ xiSupportMultiplicity rho *
        Complex.normSq (xiSupportCofactor rho (xiSupportPlanePoint rho a b)) := by
  rw [xiThetaDividedChain_factorization]
  rw [Complex.normSq_mul, map_pow, xiSupportPlanePoint_sub]
  congr 1
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
    I_re, I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero,
    Complex.sub_im, mul_one, zero_sub]
  dsimp only [xiSupportRadiusSq]
  ring

/-- **Exact planar divisor cone.** At multiplicity `m`, the full current contains the radial
factor `(x²+y²)^(m-1)`. Its leading homogeneous germ is therefore
`2m |Q(alpha)|² x (x²+y²)^(m-1)`, of total degree `2m-1`. -/
theorem xiTransverseEnergyCurrent_support_planar_factorization
    (rho : XiDivisorSupport) (a b : ℝ) :
    xiTransverseEnergyCurrent a b =
      xiSupportRadiusSq rho a b ^ (xiSupportMultiplicity rho - 1) *
        xiSupportPlanarResidual rho a b := by
  let m := xiSupportMultiplicity rho
  let x := xiSupportTransverseDisplacement rho
  let r := fun t : ℝ => xiSupportRadiusSq rho t b
  let z := fun t : ℝ => xiSupportPlanePoint rho t b
  let Q := xiSupportCofactor rho
  have hm : 0 < m := xiSupportMultiplicity_pos rho
  have hx : HasDerivAt x 1 a := by
    simpa only [x, xiSupportTransverseDisplacement, one_mul] using!
      (hasDerivAt_id a).add_const (xiSpectralPointSupport rho).im
  have hr : HasDerivAt r (2 * x a) a := by
    have hraw := (hx.pow 2).add_const (xiSupportTangentialDisplacement rho b ^ 2)
    simpa only [r, xiSupportRadiusSq, Pi.pow_apply, Nat.cast_ofNat, one_mul] using!
      hraw.congr_deriv (by ring)
  have hrpow := hr.pow m
  have hQ : DifferentiableAt ℂ Q (z a) :=
    (xiThetaDividedChain_analyticAt _ _ _).differentiableAt
  have hQenergy :
      HasDerivAt (fun t : ℝ => Complex.normSq (Q (z t)))
        (2 * (deriv Q (z a) * (starRingEnd ℂ) (Q (z a))).im) a := by
    simpa only [Q, z, xiSupportPlanePoint] using
      HTGeometry.hasDerivAt_normSq_transverse_general Q b a hQ
  have hproduct := hrpow.mul hQenergy
  have hfactorDeriv :
      HasDerivAt
        (fun t : ℝ => r t ^ m * Complex.normSq (Q (z t)))
        (r a ^ (m - 1) * xiSupportPlanarResidual rho a b) a := by
    apply hproduct.congr_deriv
    simp only [Pi.pow_apply]
    have hexp : m = (m - 1) + 1 := by omega
    rw [show r a ^ m = r a ^ (m - 1) * r a by
      conv_lhs => rw [hexp, pow_succ]]
    dsimp only [xiSupportPlanarResidual, x, r, z, Q, m]
    ring
  have hfactorDeriv' :
      HasDerivAt
        (fun t : ℝ => Complex.normSq (XiC (z t)))
        (r a ^ (m - 1) * xiSupportPlanarResidual rho a b) a := by
    apply hfactorDeriv.congr_of_eventuallyEq
    filter_upwards with t
    simpa only [r, z, Q, m] using normSq_XiC_support_plane rho t b
  have hcurrent := hasDerivAt_normSq_XiC_transverse a b
  exact hcurrent.unique
    (by simpa only [r, z, m, xiSupportPlanePoint] using hfactorDeriv')

/-- Leading homogeneous divisor cone of the planar current. Its degree is `2m-1`: one signed
transverse factor times `m-1` radial quadratic factors. -/
def xiSupportPlanarLeadingCone (rho : XiDivisorSupport) (a b : ℝ) : ℝ :=
  2 * (xiSupportMultiplicity rho : ℝ) *
    Complex.normSq (xiSupportCofactor rho (xiSpectralPointSupport rho)) *
    xiSupportTransverseDisplacement rho a *
    xiSupportRadiusSq rho a b ^ (xiSupportMultiplicity rho - 1)

/-- Coefficient left after subtracting the leading homogeneous cone and the common radial divisor
power. Its two summands visibly have one extra vanishing factor. -/
def xiSupportPlanarHigherResidual (rho : XiDivisorSupport) (a b : ℝ) : ℝ :=
  2 * (xiSupportMultiplicity rho : ℝ) * xiSupportTransverseDisplacement rho a *
      (Complex.normSq (xiSupportCofactor rho (xiSupportPlanePoint rho a b)) -
        Complex.normSq (xiSupportCofactor rho (xiSpectralPointSupport rho))) +
    xiSupportRadiusSq rho a b *
      (2 * (deriv (xiSupportCofactor rho) (xiSupportPlanePoint rho a b) *
        (starRingEnd ℂ) (xiSupportCofactor rho (xiSupportPlanePoint rho a b))).im)

/-- Exact leading-cone decomposition. This is the algebraic form of the full planar germ, with no
asymptotic or nonvanishing hypothesis. -/
theorem xiTransverseEnergyCurrent_eq_planarLeadingCone_add_higher
    (rho : XiDivisorSupport) (a b : ℝ) :
    xiTransverseEnergyCurrent a b =
      xiSupportPlanarLeadingCone rho a b +
        xiSupportRadiusSq rho a b ^ (xiSupportMultiplicity rho - 1) *
          xiSupportPlanarHigherResidual rho a b := by
  rw [xiTransverseEnergyCurrent_support_planar_factorization]
  unfold xiSupportPlanarLeadingCone xiSupportPlanarHigherResidual
    xiSupportPlanarResidual
  ring

/-- The higher coefficient is continuous in the full transverse/tangential plane. -/
theorem continuous_xiSupportPlanarHigherResidual (rho : XiDivisorSupport) :
    Continuous (Function.uncurry (xiSupportPlanarHigherResidual rho)) := by
  have hQ : Continuous (xiSupportCofactor rho) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (xiThetaDividedChain_analyticAt _ _ z).continuousAt)
  have hQ' : Continuous (deriv (xiSupportCofactor rho)) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (xiThetaDividedChain_analyticAt _ _ z).deriv.continuousAt)
  unfold xiSupportPlanarHigherResidual xiSupportPlanePoint
    xiSupportRadiusSq xiSupportTangentialDisplacement
    xiSupportTransverseDisplacement Function.uncurry
  fun_prop

@[simp] lemma xiSupportTangentialDisplacement_center (rho : XiDivisorSupport) :
    xiSupportTangentialDisplacement rho (xiSpectralPointSupport rho).re = 0 := by
  simp [xiSupportTangentialDisplacement]

@[simp] lemma xiSupportPlanePoint_center (rho : XiDivisorSupport) :
    xiSupportPlanePoint rho (-(xiSpectralPointSupport rho).im)
      (xiSpectralPointSupport rho).re = xiSpectralPointSupport rho := by
  apply Complex.ext <;> simp [xiSupportPlanePoint]

@[simp] lemma xiSupportRadiusSq_center (rho : XiDivisorSupport) :
    xiSupportRadiusSq rho (-(xiSpectralPointSupport rho).im)
      (xiSpectralPointSupport rho).re = 0 := by
  simp [xiSupportRadiusSq]

/-- The higher coefficient vanishes at the divisor. Together with the exact decomposition, this
certifies that the displayed cone is the first planar germ rather than only a formal summand. -/
@[simp] theorem xiSupportPlanarHigherResidual_center (rho : XiDivisorSupport) :
    xiSupportPlanarHigherResidual rho (-(xiSpectralPointSupport rho).im)
      (xiSpectralPointSupport rho).re = 0 := by
  simp [xiSupportPlanarHigherResidual]

/-- Centered Xi support coordinate in physical aperture form. -/
theorem neg_xiSpectralPointSupport_im_eq_re_sub_half (rho : XiDivisorSupport) :
    -(xiSpectralPointSupport rho).im = (rho : ℂ).re - 1 / 2 := by
  simp [xiSpectralPointSupport, Complex.mul_im]

theorem xiSpectralPointSupport_re_eq_im (rho : XiDivisorSupport) :
    (xiSpectralPointSupport rho).re = (rho : ℂ).im := by
  simp [xiSpectralPointSupport, Complex.mul_re]

/-- **Physical negative-current chamber.** Every hypothetical right-of-critical-line Xi divisor
point forces an open negative chamber immediately below its aperture and an open positive chamber
immediately above it, both inside `0 < a < 1/2`. -/
theorem exists_physical_thetaCuspCenterMixedFourierCurrent_sign_chamber
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ a : ℝ, |a - ((rho : ℂ).re - 1 / 2)| < ε →
        (0 < a ∧ a < 1 / 2) ∧
        ∀ ha : |a| < 1,
          (a < (rho : ℂ).re - 1 / 2 →
            thetaCuspCenterMixedFourierCurrent a ha (rho : ℂ).im < 0) ∧
          ((rho : ℂ).re - 1 / 2 < a →
            0 < thetaCuspCenterMixedFourierCurrent a ha (rho : ℂ).im) := by
  obtain ⟨ε0, hε0, hsign⟩ := exists_xiTransverseEnergyCurrent_local_sign rho
  let d : ℝ := (rho : ℂ).re - 1 / 2
  have hd : 0 < d := by dsimp only [d]; linarith
  have hrhoOne : (rho : ℂ).re < 1 := (xi_divisor_support_re_mem_open_unit rho).2
  have hdHalf : d < 1 / 2 := by dsimp only [d]; linarith
  let ε : ℝ := min ε0 (min d (1 / 2 - d))
  have hε : 0 < ε := lt_min hε0 (lt_min hd (sub_pos.mpr hdHalf))
  refine ⟨ε, hε, ?_⟩
  intro a haClose
  have haClose0 : |a + (xiSpectralPointSupport rho).im| < ε0 := by
    have him : (xiSpectralPointSupport rho).im = -d := by
      dsimp only [d]
      linarith [neg_xiSpectralPointSupport_im_eq_re_sub_half rho]
    rw [him]
    dsimp only [d] at haClose ⊢
    rw [show a + -((rho : ℂ).re - 1 / 2) =
        a - ((rho : ℂ).re - 1 / 2) by ring]
    exact haClose.trans_le (min_le_left _ _)
  have haCloseD : |a - d| < d :=
    haClose.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have haCloseHalf : |a - d| < 1 / 2 - d :=
    haClose.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have haPhys : 0 < a ∧ a < 1 / 2 := by
    rw [abs_lt] at haCloseD haCloseHalf
    constructor <;> linarith
  refine ⟨haPhys, ?_⟩
  intro ha
  have hs := hsign a haClose0
  rw [xiSpectralPointSupport_re_eq_im,
    neg_xiSpectralPointSupport_im_eq_re_sub_half] at hs
  rw [thetaCuspCenterMixedFourierCurrent_eq_xiTransverseEnergyCurrent ha]
  simpa only [d] using hs

end

end RHTower
