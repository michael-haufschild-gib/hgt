import GaloisForLFunctions.RHTower.CHMDMassPolarCompletion

/-!
# Literal weighted Fourier representers in the mass space

Real and imaginary parts of weighted Fourier samples have explicit real L2
representers. These give finite divisor images and translated cardinal images
without an abstract choice of Riesz representer.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

def negMassSamplePoint (a : MassSamplePoint) : MassSamplePoint :=
  ⟨-a.val, by
    rcases a.property with hz | hp | hm
    · exact Or.inl (by rw [XiC_even, hz])
    · exact Or.inr (Or.inr (by rw [hp]; ring))
    · exact Or.inr (Or.inl (by rw [hm]; ring))⟩

def zeroMassSamplePoint (ρ : zetaZeroConfig.carrier) : MassSamplePoint :=
  ⟨gammaOf ρ, Or.inl (CHMDStage16.XiC_gammaOf_eq_zero ρ)⟩

theorem massSample_im_eq_inner (w : MassSpace) (a : MassSamplePoint) :
    (massFourierReadout w a).im = ⟪massSampleImagKernel a, w⟫_ℝ := by
  rw [massSample_eq_inner]
  simp

def massWeightedRealKernel (c : ℂ) (a : MassSamplePoint) : MassSpace :=
  c.re • massSampleRealKernel a - c.im • massSampleImagKernel a

def massWeightedImagKernel (c : ℂ) (a : MassSamplePoint) : MassSpace :=
  c.im • massSampleRealKernel a + c.re • massSampleImagKernel a

theorem massWeightedRealKernel_pair (c : ℂ) (a : MassSamplePoint) (w : MassSpace) :
    ⟪massWeightedRealKernel c a, w⟫_ℝ = (c * massFourierReadout w a).re := by
  rw [massWeightedRealKernel, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    ← massSample_re_eq_inner, ← massSample_im_eq_inner, Complex.mul_re]

theorem massWeightedImagKernel_pair (c : ℂ) (a : MassSamplePoint) (w : MassSpace) :
    ⟪massWeightedImagKernel c a, w⟫_ℝ = (c * massFourierReadout w a).im := by
  rw [massWeightedImagKernel, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    ← massSample_re_eq_inner, ← massSample_im_eq_inner, Complex.mul_im]
  ring

theorem massPolarImage_pair_mass (w v : MassSpace) :
    ⟪massPolarImage w, v⟫_ℝ =
      -((massFourierReadout w (I/2)).re * (massFourierReadout v (-I/2)).re +
        (massFourierReadout w (-I/2)).re * (massFourierReadout v (I/2)).re) := by
  rw [massPolarImage, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    ← massSample_re_eq_inner, ← massSample_re_eq_inner]
  ring

def massShiftedCosineRealKernel (a : MassSamplePoint) (t : ℝ) : MassSpace :=
  massWeightedRealKernel (exp (-(I*a.val)*(t : ℂ))/2) a +
    massWeightedRealKernel (exp ((I*a.val)*(t : ℂ))/2) (negMassSamplePoint a)

def massShiftedCosineImagKernel (a : MassSamplePoint) (t : ℝ) : MassSpace :=
  massWeightedImagKernel (exp (-(I*a.val)*(t : ℂ))/2) a +
    massWeightedImagKernel (exp ((I*a.val)*(t : ℂ))/2) (negMassSamplePoint a)

theorem massShiftedCosineRealKernel_pair (a : MassSamplePoint) (t : ℝ) (q : SourceGraph) :
    ⟪massShiftedCosineRealKernel a t, sourceMap q⟫_ℝ =
      (shiftedCosineReadout q a t).re := by
  rw [massShiftedCosineRealKernel, inner_add_left, massWeightedRealKernel_pair,
    massWeightedRealKernel_pair, massFourierReadout_source _ (massSamplePoint_strip a),
    massFourierReadout_source _ (massSamplePoint_strip (negMassSamplePoint a))]
  change _ = ((exp (-(I*a.val)*(t : ℂ)) * graphFourierReadout q a.val +
    exp ((I*a.val)*(t : ℂ)) * graphFourierReadout q (-a.val))/2).re
  rw [← Complex.add_re]
  congr 1
  change _ + exp ((I*a.val)*(t : ℂ))/2 * graphFourierReadout q (-a.val) = _
  ring

theorem massShiftedCosineImagKernel_pair (a : MassSamplePoint) (t : ℝ) (q : SourceGraph) :
    ⟪massShiftedCosineImagKernel a t, sourceMap q⟫_ℝ =
      (shiftedCosineReadout q a t).im := by
  rw [massShiftedCosineImagKernel, inner_add_left, massWeightedImagKernel_pair,
    massWeightedImagKernel_pair, massFourierReadout_source _ (massSamplePoint_strip a),
    massFourierReadout_source _ (massSamplePoint_strip (negMassSamplePoint a))]
  change _ = ((exp (-(I*a.val)*(t : ℂ)) * graphFourierReadout q a.val +
    exp ((I*a.val)*(t : ℂ)) * graphFourierReadout q (-a.val))/2).im
  rw [← Complex.add_im]
  congr 1
  change _ + exp ((I*a.val)*(t : ℂ))/2 * graphFourierReadout q (-a.val) = _
  ring

end RHTower.CHMDDoobGraph
