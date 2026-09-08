import GaloisForLFunctions.RHTower.SelbergMaassTraceBoundary
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Actual radial and angular trace energy

Subtract the common real logarithmic radial slope from every literal translated
Maass derivative. The squared residual sum is nonnegative and obeys exact square
completion, unique minimization, and a zero-residual classification. Where the trace
density is positive, actual scalar-amplitude gradient energy plus this residual is
exactly the full vector gradient energy and quarter density.

Multiplication by density gives an identity valid also at its zeros, without asserting
smoothness of the scalar norm there. The actual Maass trace Laplacian then gives a
quotient-free Fisher identity retaining the spectral term. This is not a lower bound
for the full core-plus-cusp boundary form and does not prove Selberg's conjecture.
-/

open Complex Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassTraceRadial
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassTraceBoundary
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Actual squared derivative energy of the finite Maass family in one direction. -/
def directionalEnergy (v : ℂ) (z : ℍ) : ℝ :=
  ∑ q : Deck N, normSq (dir v ((quotientForm N f q).1.1 ∘ ofComplex) (z : ℂ))

/-- Actual real value-derivative pairing of the finite Maass family. -/
def realPairing (v : ℂ) (z : ℍ) : ℝ :=
  ∑ q : Deck N, (dir v ((quotientForm N f q).1.1 ∘ ofComplex) (z : ℂ) *
    (starRingEnd ℂ) ((quotientForm N f q).1.1 z)).re

/-- Actual derivative energy after subtraction of one common real radial slope. -/
def radialResidual (v : ℂ) (c : ℝ) (z : ℍ) : ℝ :=
  ∑ q : Deck N, normSq (dir v ((quotientForm N f q).1.1 ∘ ofComplex) (z : ℂ) -
    (c : ℂ) * (quotientForm N f q).1.1 z)

/-- The canonical real radial slope determined by the actual trace current and mass. -/
def radialSlope (v : ℂ) (z : ℍ) : ℝ := current N f v z / (2 * density N f z)

/-- The actual trace current is twice the finite real value-derivative pairing. -/
theorem current_eq_realPairing (v : ℂ) (z : ℍ) : current N f v z = 2 * realPairing N f v z := by
  have hq (q : Deck N) : ContDiffAt ℝ 2 ((quotientForm N f q).1.1 ∘ ofComplex) (z : ℂ) :=
    (quotientForm N f q).2.2.1.1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hs (q : Deck N) : DifferentiableAt ℝ
      (fun w => normSq ((quotientForm N f q).1.1 (ofComplex w))) (z : ℂ) := by
    simpa only [Complex.normSq_eq_norm_sq, Function.comp_def] using
      ((hq q).norm_sq ℝ).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  change dir v (fun w => ∑ q : Deck N, normSq ((quotientForm N f q).1.1 (ofComplex w))) (z : ℂ) = _
  rw [dir_sum Finset.univ (fun q _ => hs q)]
  unfold realPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have h := normSq_dir ((hq q).differentiableAt (by norm_num)) v
  simpa only [Function.comp_apply, ofComplex_apply] using h

private theorem normSq_shift (a b : ℂ) (c : ℝ) :
    normSq (b - (c : ℂ) * a) = normSq b - 2 * c * (b * (starRingEnd ℂ) a).re + c ^ 2 * normSq a := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im,
    zero_mul, sub_zero, conj_re, conj_im]
  ring

/-- Exact square expansion for the actual derivative residual. -/
theorem radialResidual_expansion (v : ℂ) (c : ℝ) (z : ℍ) :
    radialResidual N f v c z = directionalEnergy N f v z - c * current N f v z + c ^ 2 * density N f z := by
  unfold radialResidual
  simp_rw [normSq_shift]
  rw [current_eq_realPairing]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    directionalEnergy, realPairing, density]
  ring

/-- Every actual common-slope residual is nonnegative. -/
theorem radialResidual_nonneg (v : ℂ) (c : ℝ) (z : ℍ) : 0 ≤ radialResidual N f v c z :=
  Finset.sum_nonneg (fun _ _ => normSq_nonneg _)

/-- Canonical radial subtraction gives the exact minimum and retains its full quadratic excess. -/
theorem radialResidual_minimization (v : ℂ) (z : ℍ) (hz : 0 < density N f z) (c : ℝ) :
    radialResidual N f v c z = radialResidual N f v (radialSlope N f v z) z +
      density N f z * (c - radialSlope N f v z) ^ 2 := by
  rw [radialResidual_expansion, radialResidual_expansion]
  unfold radialSlope
  field_simp [hz.ne']
  ring

/-- Actual directional energy splits into radial current energy and its nonnegative residual. -/
theorem directionalEnergy_decomposition (v : ℂ) (z : ℍ) (hz : 0 < density N f z) :
    directionalEnergy N f v z = current N f v z ^ 2 / (4 * density N f z) +
      radialResidual N f v (radialSlope N f v z) z := by
  rw [radialResidual_expansion]
  unfold radialSlope
  field_simp [hz.ne']
  ring

/-- The literal scalar norm of the finite congruence Maass family. -/
def amplitude (z : ℂ) : ℝ := Real.sqrt (density N f (ofComplex z))

/-- At positive trace density the actual scalar-amplitude derivative is the normalized trace current. -/
theorem amplitude_dir (v : ℂ) (z : ℍ) (hz : 0 < density N f z) :
    dir v (amplitude N f) (z : ℂ) = current N f v z / (2 * Real.sqrt (density N f z)) := by
  have hf := ((density_contDiffOn N f).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have h := hf.hasFDerivAt.sqrt (by simpa only [Function.comp_apply, ofComplex_apply] using hz.ne')
  have hv := congrArg (fun L => L v) h.fderiv
  change dir v (amplitude N f) (z : ℂ) = _ at hv
  simp only [smul_apply, smul_eq_mul, Function.comp_apply, ofComplex_apply] at hv
  rw [hv]
  unfold current
  ring

/-- At positive density the full directional source energy retains scalar-amplitude energy and the residual. -/
theorem directionalEnergy_eq_amplitude_add_residual (v : ℂ) (z : ℍ) (hz : 0 < density N f z) :
    directionalEnergy N f v z = dir v (amplitude N f) (z : ℂ) ^ 2 +
      radialResidual N f v (radialSlope N f v z) z := by
  rw [directionalEnergy_decomposition N f v z hz, amplitude_dir N f v z hz]
  congr 1
  rw [div_pow, mul_pow, Real.sq_sqrt hz.le]
  ring

/-- Sum of the actual horizontal and vertical residual energies after canonical radial subtraction. -/
def angularEnergy (z : ℍ) : ℝ :=
  radialResidual N f 1 (radialSlope N f 1 z) z +
    radialResidual N f Complex.I (radialSlope N f Complex.I z) z

/-- The actual angular residual energy is nonnegative. -/
theorem angularEnergy_nonneg (z : ℍ) : 0 ≤ angularEnergy N f z :=
  add_nonneg (radialResidual_nonneg N f 1 _ z) (radialResidual_nonneg N f Complex.I _ z)

/-- Exact actual radial-plus-angular gradient decomposition at positive density. -/
theorem gradientDensity_eq_radial_add_angular (z : ℍ) (hz : 0 < density N f z) :
    gradientDensity N f (z : ℂ) = dir 1 (amplitude N f) (z : ℂ) ^ 2 +
      dir Complex.I (amplitude N f) (z : ℂ) ^ 2 + angularEnergy N f z := by
  have hg : gradientDensity N f (z : ℂ) = directionalEnergy N f 1 z + directionalEnergy N f Complex.I z := by
    exact Finset.sum_add_distrib
  rw [hg, directionalEnergy_eq_amplitude_add_residual N f 1 z hz,
    directionalEnergy_eq_amplitude_add_residual N f Complex.I z hz]
  unfold angularEnergy
  ring

/-- Actual quarter density retains the full radial quarter density and angular residual. -/
theorem quarterDensity_eq_radial_add_angular (z : ℍ) (hz : 0 < density N f z) :
    quarterDensity N f z = (dir 1 (amplitude N f) (z : ℂ) ^ 2 +
      dir Complex.I (amplitude N f) (z : ℂ) ^ 2 - density N f z / (4 * z.im ^ 2)) + angularEnergy N f z := by
  rw [quarterDensity, gradientDensity_eq_radial_add_angular N f z hz]
  ring

/-- At a trace-density zero, actual current vanishes by the nonnegative local minimum. -/
theorem current_zero_of_density_zero (v : ℂ) (z : ℍ) (hz : density N f z = 0) :
    current N f v z = 0 := by
  have hm : IsLocalMin (density N f ∘ ofComplex) (z : ℂ) := by
    apply Eventually.of_forall
    intro w
    simp only [Function.comp_apply, ofComplex_apply, hz]
    exact density_nonneg N f _
  change fderiv ℝ (density N f ∘ ofComplex) (z : ℂ) v = 0
  rw [hm.fderiv_eq_zero]
  rfl

/-- The multiplied directional decomposition holds at every point, including trace zeros. -/
theorem density_mul_directionalEnergy (v : ℂ) (z : ℍ) :
    density N f z * directionalEnergy N f v z = current N f v z ^ 2 / 4 +
      density N f z * radialResidual N f v (radialSlope N f v z) z := by
  by_cases hz : 0 < density N f z
  · rw [directionalEnergy_decomposition N f v z hz]
    field_simp [hz.ne']
  · have he : density N f z = 0 := le_antisymm (le_of_not_gt hz) (density_nonneg N f z)
    rw [he, current_zero_of_density_zero N f v z he]
    ring

/-- The multiplied radial-plus-angular decomposition holds everywhere without a norm-smoothness assumption. -/
theorem density_mul_gradientDensity (z : ℍ) :
    density N f z * gradientDensity N f (z : ℂ) =
      (current N f 1 z ^ 2 + current N f Complex.I z ^ 2) / 4 + density N f z * angularEnergy N f z := by
  have hg : gradientDensity N f (z : ℂ) = directionalEnergy N f 1 z + directionalEnergy N f Complex.I z :=
    Finset.sum_add_distrib
  rw [hg, mul_add, density_mul_directionalEnergy, density_mul_directionalEnergy]
  unfold angularEnergy
  ring

/-- Zero residual means every actual component derivative has the same real radial slope. -/
theorem radialResidual_eq_zero_iff (v : ℂ) (c : ℝ) (z : ℍ) :
    radialResidual N f v c z = 0 ↔
      ∀ q : Deck N, dir v ((quotientForm N f q).1.1 ∘ ofComplex) (z : ℂ) =
        (c : ℂ) * (quotientForm N f q).1.1 z := by
  unfold radialResidual
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun q _ => normSq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, normSq_eq_zero, sub_eq_zero]

/-- At positive density the canonical common real slope is the unique minimizer. -/
theorem radialResidual_minimum_unique (v : ℂ) (z : ℍ) (hz : 0 < density N f z) (c : ℝ) :
    radialResidual N f v c z = radialResidual N f v (radialSlope N f v z) z ↔ c = radialSlope N f v z := by
  rw [radialResidual_minimization N f v z hz c, add_eq_left,
    mul_eq_zero, or_iff_right hz.ne', sq_eq_zero_iff, sub_eq_zero]

/-- The angular residual vanishes exactly when all actual component derivatives are radial in both directions. -/
theorem angularEnergy_eq_zero_iff (z : ℍ) : angularEnergy N f z = 0 ↔
    (∀ q : Deck N, dir 1 ((quotientForm N f q).1.1 ∘ ofComplex) (z : ℂ) =
      (radialSlope N f 1 z : ℂ) * (quotientForm N f q).1.1 z) ∧
    (∀ q : Deck N, dir Complex.I ((quotientForm N f q).1.1 ∘ ofComplex) (z : ℂ) =
      (radialSlope N f Complex.I z : ℂ) * (quotientForm N f q).1.1 z) := by
  have h1 := radialResidual_nonneg N f 1 (radialSlope N f 1 z) z
  have hI := radialResidual_nonneg N f Complex.I (radialSlope N f Complex.I z) z
  rw [← radialResidual_eq_zero_iff, ← radialResidual_eq_zero_iff]
  unfold angularEnergy
  constructor
  · intro h
    constructor <;> linarith
  · rintro ⟨h, h'⟩
    rw [h, h', add_zero]

/-- The actual trace Fisher identity retains the eigenvalue and the complete angular residual, including at zeros. -/
theorem trace_fisher_identity (z : ℍ) :
    density N f z * realLaplacian (density N f ∘ ofComplex) (z : ℂ) =
      (current N f 1 z ^ 2 + current N f Complex.I z ^ 2) / 2 +
        2 * density N f z * angularEnergy N f z - 2 * lam * density N f z ^ 2 / z.im ^ 2 := by
  calc
    _ = 2 * (density N f z * gradientDensity N f (z : ℂ)) -
        2 * lam * density N f z ^ 2 / z.im ^ 2 := by
      rw [trace_laplacian]
      ring
    _ = _ := by
      rw [density_mul_gradientDensity]
      ring

end
end GaloisForLFunctions.RHTower.SelbergMaassTraceRadial
