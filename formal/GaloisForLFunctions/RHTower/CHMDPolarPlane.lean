import GaloisForLFunctions.RHTower.CHMDFullSpectralPairing

/-!
# An explicit nondegenerate polar plane in the original graph

The ground vector and an antisymmetric difference of admitted theta translates
have polar coordinates (1/2,0) and (0,1/2). Their signed Gram matrix is
diag(-1/2,1/2), and both vanish at every Xi zero.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
noncomputable section
namespace RHTower.CHMDDoobGraph

theorem thetaTranslate_fourier (t : ℝ) (ht : 1 < 2 * Real.exp (-2 * |t|)) (z : ℂ) :
    graphFourierReadout (CHMDThetaTranslate.lift t ht) z = exp (I*z*t) * XiC z := by
  have hs : (CHMDThetaTranslate.lift t ht).val.fst =ᵐ[massMeasure]
      phiDoobInv (CHMDTranslation.translate riemannKernelReal t) := CHMDThetaTranslate.lift_source_ae t ht
  rw [graphFourierReadout_of_source hs, paperFT_translate_real,
    ← graphFourierReadout_of_source ground_source_eq_inverse_theta, graphFourierReadout_ground]

theorem thetaTranslate_fourier_plus_pole (t : ℝ) (ht : 1 < 2 * Real.exp (-2 * |t|)) :
    graphFourierReadout (CHMDThetaTranslate.lift t ht) (I/2) =
      ((Real.exp (-t/2)/2 : ℝ) : ℂ) := by
  have hXi : XiC (I/2) = 1/2 := by rw [← graphFourierReadout_ground, ground_fourier_pole]
  have he : I*(I/2)*(t : ℂ) = ((-t/2 : ℝ) : ℂ) := by
    calc
      _ = (I*I)*(t : ℂ)/2 := by ring
      _ = _ := by rw [I_mul_I]; push_cast; ring
  rw [thetaTranslate_fourier, hXi, he, ← Complex.ofReal_exp]
  push_cast
  ring

theorem thetaTranslate_fourier_minus_pole (t : ℝ) (ht : 1 < 2 * Real.exp (-2 * |t|)) :
    graphFourierReadout (CHMDThetaTranslate.lift t ht) (-I/2) =
      ((Real.exp (t/2)/2 : ℝ) : ℂ) := by
  have hXi : XiC (-I/2) = 1/2 := by
    rw [neg_div, XiC_even, ← graphFourierReadout_ground, ground_fourier_pole]
  have he : I*(-I/2)*(t : ℂ) = ((t/2 : ℝ) : ℂ) := by
    calc
      _ = -(I*I)*(t : ℂ)/2 := by ring
      _ = _ := by rw [I_mul_I]; push_cast; ring
  rw [thetaTranslate_fourier, hXi, he, ← Complex.ofReal_exp]
  push_cast
  ring

def oddPolarVector : SourceGraph :=
  (2 * Real.sinh (CHMDThetaTranslate.radius/2))⁻¹ •
    (CHMDThetaTranslate.lift CHMDThetaTranslate.radius
      (CHMDThetaTranslate.small_shift (by rw [abs_of_pos CHMDThetaTranslate.radius_pos])) -
     CHMDThetaTranslate.lift (-CHMDThetaTranslate.radius)
      (CHMDThetaTranslate.small_shift (by rw [abs_neg, abs_of_pos CHMDThetaTranslate.radius_pos])))

theorem polar_sinh_pos : 0 < Real.sinh (CHMDThetaTranslate.radius/2) :=
  Real.sinh_pos_iff.mpr (half_pos CHMDThetaTranslate.radius_pos)

theorem oddPolarVector_mem_fullSpectralNullspace : oddPolarVector ∈ fullSpectralNullspace := by
  intro z hz
  have hstrip := (abs_im_lt_half_of_XiC_eq_zero hz).le
  rw [oddPolarVector, graphFourierReadout_smul _ _ hstrip,
    graphFourierReadout_sub _ _ hstrip, thetaTranslate_fourier, thetaTranslate_fourier, hz]
  simp

theorem oddPolarVector_fourier_plus_pole : graphFourierReadout oddPolarVector (I/2) = -1/2 := by
  rw [oddPolarVector, graphFourierReadout_smul _ _ (by norm_num),
    graphFourierReadout_sub _ _ (by norm_num),
    thetaTranslate_fourier_plus_pole, thetaTranslate_fourier_plus_pole]
  have hs : Real.exp (-CHMDThetaTranslate.radius/2)/2 - Real.exp (CHMDThetaTranslate.radius/2)/2 =
      -Real.sinh (CHMDThetaTranslate.radius/2) := by
    rw [Real.sinh_eq, neg_div]
    ring
  simp only [neg_neg, ← Complex.ofReal_sub, hs, ← Complex.ofReal_mul]
  have he : (2*Real.sinh (CHMDThetaTranslate.radius/2))⁻¹ *
      (-Real.sinh (CHMDThetaTranslate.radius/2)) = -1/2 := by
    field_simp [polar_sinh_pos.ne']
  rw [he]
  norm_num

theorem oddPolarVector_fourier_minus_pole : graphFourierReadout oddPolarVector (-I/2) = 1/2 := by
  rw [oddPolarVector, graphFourierReadout_smul _ _ (by norm_num),
    graphFourierReadout_sub _ _ (by norm_num),
    thetaTranslate_fourier_minus_pole, thetaTranslate_fourier_minus_pole]
  have hs : Real.exp (CHMDThetaTranslate.radius/2)/2 - Real.exp (-CHMDThetaTranslate.radius/2)/2 =
      Real.sinh (CHMDThetaTranslate.radius/2) := by
    rw [Real.sinh_eq, neg_div]
    ring
  simp only [← Complex.ofReal_sub, hs, ← Complex.ofReal_mul]
  have he : (2*Real.sinh (CHMDThetaTranslate.radius/2))⁻¹ *
      Real.sinh (CHMDThetaTranslate.radius/2) = 1/2 := by
    field_simp [polar_sinh_pos.ne']
  rw [he]
  norm_num

theorem polarCosine_oddPolarVector : polarCosine oddPolarVector = 0 := by
  rw [polarCosine_eq_half_fourier, oddPolarVector_fourier_plus_pole, oddPolarVector_fourier_minus_pole]
  norm_num

theorem polarSine_oddPolarVector : polarSine oddPolarVector = 1/2 := by
  rw [polarSine, oddPolarVector_fourier_plus_pole, oddPolarVector_fourier_minus_pole]
  norm_num

theorem sourcePair_ground_eq_polarCosine (p : SourceGraph) :
    sourcePair (constantLift 1) p = -polarCosine p := sourcePair_ground_eq_graphCosine p

theorem sourcePair_oddPolarVector (p : SourceGraph) : sourcePair oddPolarVector p = polarSine p := by
  rw [full_nullspace_pair oddPolarVector_mem_fullSpectralNullspace,
    polarCosine_oddPolarVector, polarSine_oddPolarVector]
  ring

/-- Both signs occur in an actual two-dimensional polar space, with zero cross pairing. -/
theorem polarPlane_gram :
    sourcePair (constantLift 1) (constantLift 1) = -1/2 ∧
    sourcePair (constantLift 1) oddPolarVector = 0 ∧
    sourcePair oddPolarVector oddPolarVector = 1/2 := by
  rw [sourcePair_ground_eq_polarCosine, polarCosine_ground,
    sourcePair_ground_eq_polarCosine, polarCosine_oddPolarVector,
    sourcePair_oddPolarVector, polarSine_oddPolarVector]
  norm_num

end RHTower.CHMDDoobGraph
