import GaloisForLFunctions.RHTower.SelbergMaassTraceDirection

/-!
# Regularized actual Maass trace curvature

A positive constant square regularizes the actual finite congruence trace through
common zeros. Its C² amplitude remains modular invariant. Exact square completion
retains the constant-coordinate correction and gives the actual scalar curvature
equation and quarter-density decomposition. No sign for the full quarter form is
assumed or established; this is not a proof of Selberg's conjecture.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassTraceRegularized
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassTraceBoundary
  SelbergMaassTraceRadial SelbergMaassMean SelbergMaassTraceDirection
noncomputable section

/-- The actual trace amplitude after adding one strictly positive constant square. -/
def radius (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (e : Ioi (0 : ℝ)) (z : ℂ) : ℝ := Real.sqrt (density N f (ofComplex z) + (e : ℝ) ^ 2)

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (e : Ioi (0 : ℝ))

/-- The regularized squared radius is strictly positive, including original trace zeros. -/
theorem denominator_pos (z : ℂ) : 0 < density N f (ofComplex z) + (e : ℝ) ^ 2 :=
  add_pos_of_nonneg_of_pos (density_nonneg N f _) (sq_pos_of_pos e.2)

/-- Exact regularized square, without restricting to the original positive-density locus. -/
theorem radius_sq (z : ℂ) : radius N f e z ^ 2 = density N f (ofComplex z) + (e : ℝ) ^ 2 :=
  Real.sq_sqrt (denominator_pos N f e z).le

/-- The regularized amplitude never vanishes. -/
theorem radius_pos (z : ℂ) : 0 < radius N f e z := Real.sqrt_pos.mpr (denominator_pos N f e z)

/-- The regularization retains C² regularity through common zeros on the actual upper half-plane. -/
theorem radius_contDiffOn : ContDiffOn ℝ 2 (radius N f e) {z : ℂ | 0 < z.im} := by
  apply ((density_contDiffOn N f).add contDiffOn_const).sqrt
  intro z _
  exact (denominator_pos N f e z).ne'

/-- Full modular invariance survives the constant-square regularization. -/
theorem radius_invariant (A : SL2Z) (z : ℍ) :
    radius N f e (A • z : ℍ) = radius N f e (z : ℂ) := by
  simp only [radius, ofComplex_apply, density_invariant]

/-- The literal first derivative is the original trace current divided by twice the regularized radius. -/
theorem radius_dir (v : ℂ) (z : ℍ) :
    dir v (radius N f e) (z : ℂ) = current N f v z / (2 * radius N f e (z : ℂ)) := by
  have hd := ((density_contDiffOn N f).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have h := (hd.hasFDerivAt.add_const ((e : ℝ) ^ 2)).sqrt (denominator_pos N f e (z : ℂ)).ne'
  have hv := congrArg (fun L => L v) h.fderiv
  change dir v (radius N f e) (z : ℂ) = _ at hv
  simp only [smul_apply, smul_eq_mul, Function.comp_apply, ofComplex_apply] at hv
  rw [hv]
  unfold current radius
  simp only [ofComplex_apply]
  ring

/-- Common regularized real radial slope. -/
def slope (v : ℂ) (z : ℍ) : ℝ := current N f v z / (2 * (density N f z + (e : ℝ) ^ 2))

/-- Actual common-slope residual plus the exact constant-coordinate correction. -/
def directionalRemainder (v : ℂ) (z : ℍ) : ℝ :=
  radialResidual N f v (slope N f e v z) z + (e : ℝ) ^ 2 * slope N f e v z ^ 2

/-- The correction is a sum of squares, including at original common zeros. -/
theorem directionalRemainder_nonneg (v : ℂ) (z : ℍ) : 0 ≤ directionalRemainder N f e v z :=
  add_nonneg (radialResidual_nonneg N f v _ z) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Exact regularized square completion retains the constant-coordinate term. -/
theorem directionalRemainder_eq (v : ℂ) (z : ℍ) :
    directionalRemainder N f e v z = directionalEnergy N f v z -
      current N f v z ^ 2 / (4 * (density N f z + (e : ℝ) ^ 2)) := by
  rw [directionalRemainder, radialResidual_expansion]
  unfold slope
  have hp : density N f z + (e : ℝ) ^ 2 ≠ 0 := by
    simpa only [ofComplex_apply] using (denominator_pos N f e (z : ℂ)).ne'
  field_simp
  ring

/-- Full directional energy splits into the actual regularized radius derivative and its retained remainder. -/
theorem directionalEnergy_eq (v : ℂ) (z : ℍ) :
    directionalEnergy N f v z = dir v (radius N f e) (z : ℂ) ^ 2 + directionalRemainder N f e v z := by
  rw [radius_dir, directionalRemainder_eq, div_pow, mul_pow, radius_sq, ofComplex_apply]
  ring

/-- Sum of both regularized source remainders. -/
def remainder (z : ℍ) : ℝ := directionalRemainder N f e 1 z + directionalRemainder N f e Complex.I z

/-- The actual regularized remainder is nonnegative. -/
theorem remainder_nonneg (z : ℍ) : 0 ≤ remainder N f e z :=
  add_nonneg (directionalRemainder_nonneg N f e 1 z) (directionalRemainder_nonneg N f e Complex.I z)

/-- Exact source gradient decomposition valid through common zeros. -/
theorem gradientDensity_eq (z : ℍ) :
    gradientDensity N f (z : ℂ) = dir 1 (radius N f e) (z : ℂ) ^ 2 +
      dir Complex.I (radius N f e) (z : ℂ) ^ 2 + remainder N f e z := by
  have hg : gradientDensity N f (z : ℂ) = directionalEnergy N f 1 z + directionalEnergy N f Complex.I z :=
    Finset.sum_add_distrib
  rw [hg, directionalEnergy_eq N f e 1 z, directionalEnergy_eq N f e Complex.I z]
  unfold remainder
  ring

/-- Regularized scalar curvature retains both the nonnegative remainder and the original spectral mass. -/
theorem radius_laplacian_identity (z : ℍ) :
    radius N f e (z : ℂ) * realLaplacian (radius N f e) (z : ℂ) =
      remainder N f e z - lam * density N f z / z.im ^ 2 := by
  have hf := (radius_contDiffOn N f e).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have he : (fun w => radius N f e w ^ 2) = (fun w => density N f (ofComplex w) + (e : ℝ) ^ 2) :=
    funext (radius_sq N f e)
  have hd (v : ℂ) : dir v (fun w => radius N f e w ^ 2) = dir v (density N f ∘ ofComplex) := by
    rw [he]
    funext w
    exact congrArg (fun L => L v) (fderiv_add_const (𝕜 := ℝ) (f := density N f ∘ ofComplex) (x := w) ((e : ℝ) ^ 2))
  have hx := sq_second_dir hf (1 : ℂ)
  have hy := sq_second_dir hf Complex.I
  rw [hd] at hx hy
  have ht := trace_laplacian N f z
  have hg := gradientDensity_eq N f e z
  unfold realLaplacian at ht ⊢
  linear_combination (ht - hx - hy) / 2 + hg

/-- The original quarter density retains the explicit positive regularization mass correction. -/
theorem quarterDensity_eq (z : ℍ) : quarterDensity N f z =
    (dir 1 (radius N f e) (z : ℂ) ^ 2 + dir Complex.I (radius N f e) (z : ℂ) ^ 2 -
      radius N f e (z : ℂ) ^ 2 / (4 * z.im ^ 2)) + remainder N f e z +
        (e : ℝ) ^ 2 / (4 * z.im ^ 2) := by
  rw [SelbergMaassTraceEnergy.quarterDensity, gradientDensity_eq, radius_sq, ofComplex_apply]
  ring

end
end GaloisForLFunctions.RHTower.SelbergMaassTraceRegularized
