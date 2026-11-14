import GaloisForLFunctions.FamilyContinuationTheory.Quartic.GaussianPrimary
import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.PositiveAngularCancellation

/-!
# Primary Gaussian angular lattice sums

The primary condition parametrizes exactly the affine lattice
`1 + (1+i)^3 ℤ[i]`. Its covolume is eight. Affine Poisson summation therefore
separates the exact density-one-eighth mean from a uniformly bounded remainder.
For every positive angular weight the mean vanishes, leaving a bound independent
of the complex sampling scale.
-/

noncomputable section
open Complex RHTower.GaussianTwoSquares
open scoped Classical SchwartzMap FourierTransform

namespace GaloisForLFunctions.FamilyContinuationTheory.Quartic
open MetaplecticMobiusDescent.QuarticPoisson

/-- Gaussian integers congruent to one modulo the ramified cube. -/
abbrev PrimaryGaussian := {z : GaussianInt // IsPrimary z}

/-- Multiplication by the ramified cube, followed by translation by one. -/
def primaryLatticeParam (w : GaussianInt) : PrimaryGaussian :=
  ⟨onePlusI ^ 3 * w + 1, by
    change onePlusI ^ 3 ∣ (onePlusI ^ 3 * w + 1) - 1
    rw [add_sub_cancel_right]
    exact ⟨w, rfl⟩⟩

private theorem primary_step_complex : ((onePlusI ^ 3 : GaussianInt) : ℂ) = -2 + 2 * I := by
  norm_num [onePlusI, pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul, GaussianInt.toComplex_def]

private theorem primary_step_complex_ne_zero : ((onePlusI ^ 3 : GaussianInt) : ℂ) ≠ 0 := by
  rw [primary_step_complex]
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

private theorem primary_step_ne_zero : (onePlusI ^ 3 : GaussianInt) ≠ 0 := by
  intro h
  apply primary_step_complex_ne_zero
  rw [h]
  exact GaussianInt.toComplex_zero

private theorem primaryLatticeParam_bijective : Function.Bijective primaryLatticeParam := by
  constructor
  · intro w v h
    have hv := congrArg Subtype.val h
    change onePlusI ^ 3 * w + 1 = onePlusI ^ 3 * v + 1 at hv
    exact mul_left_cancel₀ primary_step_ne_zero (add_right_cancel hv)
  · rintro ⟨z, hz⟩
    change onePlusI ^ 3 ∣ z - 1 at hz
    obtain ⟨w, hw⟩ := hz
    refine ⟨w, Subtype.ext ?_⟩
    change onePlusI ^ 3 * w + 1 = z
    rw [← hw, sub_add_cancel]

/-- Every primary Gaussian integer has one unique affine lattice coordinate. -/
def primaryLatticeEquiv : GaussianInt ≃ PrimaryGaussian :=
  Equiv.ofBijective primaryLatticeParam primaryLatticeParam_bijective

/-- The primary parametrization is the explicit ramified-cube affine map. -/
theorem primaryLatticeEquiv_apply (w : GaussianInt) :
    primaryLatticeEquiv w = primaryLatticeParam w := rfl

/-- The primary lattice step, viewed as a nonzero complex dilation. -/
def primaryStepUnit : ℂˣ :=
  Units.mk0 ((onePlusI ^ 3 : GaussianInt) : ℂ) primary_step_complex_ne_zero

/-- The complex embedding preserves the primary affine parametrization. -/
theorem primaryLatticeParam_complex (w : GaussianInt) :
    ((primaryLatticeParam w).val : ℂ) = (primaryStepUnit : ℂ) * (w : ℂ) + 1 := by
  change ((onePlusI ^ 3 * w + 1 : GaussianInt) : ℂ) = _
  rw [GaussianInt.toComplex_add, GaussianInt.toComplex_mul, GaussianInt.toComplex_one]
  rfl

/-- The primary affine lattice has covolume eight. -/
theorem primaryStepUnit_norm_sq : ‖(primaryStepUnit : ℂ)‖ ^ 2 = 8 := by
  change ‖((onePlusI ^ 3 : GaussianInt) : ℂ)‖ ^ 2 = 8
  rw [Complex.sq_norm, primary_step_complex]
  norm_num [Complex.normSq_apply]

/-- The exact inverse covolume after an arbitrary complex dilation. -/
theorem primary_covolume_factor (u : ℂˣ) :
    ‖((u * primaryStepUnit : ℂˣ) : ℂ)‖⁻¹ ^ 2 = 1 / (8 * ‖(u : ℂ)‖ ^ 2) := by
  rw [Units.val_mul, inv_pow, norm_mul, mul_pow, primaryStepUnit_norm_sq]
  simp only [one_div, mul_comm]

/-- Schwartz sampling over the primary congruence class. -/
def primaryLatticeSum (f : 𝓢(ℂ, ℂ)) (u : ℂˣ) : ℂ :=
  ∑' z : PrimaryGaussian, f ((u : ℂ) * (z.val : ℂ))

/-- The primary series is exactly an affine Gaussian lattice series. -/
theorem primaryLatticeSum_eq_affine (f : 𝓢(ℂ, ℂ)) (u : ℂˣ) :
    primaryLatticeSum f u = gaussianAffineSum f (u * primaryStepUnit) (u : ℂ) := by
  have h := primaryLatticeEquiv.tsum_eq
    (fun z : PrimaryGaussian => f ((u : ℂ) * (z.val : ℂ)))
  unfold primaryLatticeSum gaussianAffineSum
  simpa only [primaryLatticeEquiv_apply, primaryLatticeParam_complex,
    mul_add, mul_one, mul_assoc, Units.val_mul] using h.symm

/-- Primary Schwartz series converge at every nonzero complex scale. -/
theorem summable_primaryLattice (f : 𝓢(ℂ, ℂ)) (u : ℂˣ) :
    Summable (fun z : PrimaryGaussian => f ((u : ℂ) * (z.val : ℂ))) := by
  have h : Summable (fun w : GaussianInt => f ((u : ℂ) * ((primaryLatticeEquiv w).val : ℂ))) := by
    simpa only [primaryLatticeEquiv_apply, primaryLatticeParam_complex,
      mul_add, mul_one, mul_assoc, Units.val_mul] using
      summable_gaussianAffine f (u * primaryStepUnit) (u : ℂ)
  exact (primaryLatticeEquiv.summable_iff
    (f := fun z : PrimaryGaussian => f ((u : ℂ) * (z.val : ℂ)))).mp h

/-- The density-one-eighth mean is exact, and the remaining primary mass is uniformly bounded. -/
theorem primaryLatticeSum_sub_mean_le (f : 𝓢(ℂ, ℂ)) (u : ℂˣ) :
    ‖primaryLatticeSum f u - (1 / (8 * ‖(u : ℂ)‖ ^ 2) : ℝ) • (𝓕 f) 0‖ ≤
      1632 * derivativeMass 4 f := by
  have h := gaussian_affine_sum_sub_mean_le f (u * primaryStepUnit) (u : ℂ)
  rw [← primaryLatticeSum_eq_affine, primary_covolume_factor] at h
  exact h

/-- Primary angular sums in each nontrivial quarter-turn sector remain uniformly
bounded at all complex scales, even though full unit-orbit cancellation is unavailable. -/
theorem primary_annular_sum_le (n : ℕ) (j : Fin 3) (W : 𝓢(ℝ, ℂ)) (u : ℂˣ) :
    ‖primaryLatticeSum (annularAngularCLM (4 * n + (j.val + 1)) W) u‖ ≤
      1632 * derivativeMass 4 (annularAngularCLM (4 * n + (j.val + 1)) W) := by
  have hz := annularFourier_zero n j W
  change (𝓕 (annularAngularCLM (4 * n + (j.val + 1)) W)) 0 = 0 at hz
  have h := primaryLatticeSum_sub_mean_le (annularAngularCLM (4 * n + (j.val + 1)) W) u
  simpa only [hz, smul_zero, sub_zero] using h

/-- Continuous rotation removes the mean for every positive angular weight,
including multiples of four, which need not cancel under Gaussian unit averaging. -/
theorem primary_positive_annular_sum_le (n : ℕ) (W : 𝓢(ℝ, ℂ)) (u : ℂˣ) :
    ‖primaryLatticeSum (annularAngularCLM (n + 1) W) u‖ ≤
      1632 * derivativeMass 4 (annularAngularCLM (n + 1) W) := by
  have hz := annularFourier_positive_zero n W
  change (𝓕 (annularAngularCLM (n + 1) W)) 0 = 0 at hz
  have h := primaryLatticeSum_sub_mean_le (annularAngularCLM (n + 1) W) u
  simpa only [hz, smul_zero, sub_zero] using h

end GaloisForLFunctions.FamilyContinuationTheory.Quartic
