/-
# Cyclicity of a fixed seed is generic in the coefficients

The Krylov matrix of a linear Hermitian family against a fixed seed has entries that are polynomial
in the coefficients, so its determinant is real-analytic and its modulus squared is a nonzero
real-analytic function as soon as one member of the family makes the seed cyclic.  Its zero set is
then Lebesgue-null, and it is a cone because scaling the coefficients scales the `j`-th Krylov
column by the `j`-th power of the scale.  Polar disintegration carries the nullity to the
coefficient sphere.

Main results:
* `ensembleKrylov`, `analyticAt_ensembleKrylov_det` — the Krylov determinant is real-analytic.
* `volume_ensembleKrylov_det_eq_zero` — **the non-cyclic parameters are Lebesgue-null**.
* `ensembleKrylov_const_mul` — the homogeneity of the Krylov matrix.
* `toSphere_krylovDegenerateSphere_eq_zero` — **the non-cyclic directions are shell-null**.
-/
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial
import GaloisForLFunctions.HTGeometry.MultivariateAnalyticZeroNull
import GaloisForLFunctions.HTGeometry.SphereHomogeneousNullSet
import GaloisForLFunctions.HTGeometry.ShellCoeffScaling
import GaloisForLFunctions.HTGeometry.AngularPhaseLaw

open Matrix Finset MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- The Krylov matrix of a linear Hermitian family against a fixed seed. -/
def ensembleKrylov (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (χ : Fin D → ℂ) (θ : Fin N → ℝ) :
    Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun x j => ((spectralEnsembleMatrix P θ) ^ (j : ℕ) *ᵥ χ) x

theorem analyticAt_spectralEnsembleMatrix_entry (P : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (x y : Fin D) (θ₀ : Fin N → ℝ) :
    AnalyticAt ℝ (fun θ : Fin N → ℝ => spectralEnsembleMatrix P θ x y) θ₀ := by
  have hfun : (fun θ : Fin N → ℝ => spectralEnsembleMatrix P θ x y)
      = ∑ a : Fin N, fun θ : Fin N → ℝ => ((θ a : ℝ) : ℂ) * P a x y := by
    funext θ
    rw [Finset.sum_apply]
    simp [spectralEnsembleMatrix, Matrix.sum_apply, Matrix.smul_apply]
  rw [hfun]
  refine analyticAt_sum _ fun a _ => ?_
  exact ((Complex.ofRealCLM.comp (ContinuousLinearMap.proj a)).analyticAt θ₀).mul
    analyticAt_const

theorem analyticAt_spectralEnsembleMatrix_pow_entry (P : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (m : ℕ) (x y : Fin D) (θ₀ : Fin N → ℝ) :
    AnalyticAt ℝ (fun θ : Fin N → ℝ => ((spectralEnsembleMatrix P θ) ^ m) x y) θ₀ := by
  induction m generalizing x y with
  | zero =>
      have hfun : (fun θ : Fin N → ℝ => ((spectralEnsembleMatrix P θ) ^ 0) x y)
          = fun _ => (if x = y then (1 : ℂ) else 0) := by
        funext θ
        rw [pow_zero, Matrix.one_apply]
      rw [hfun]
      exact analyticAt_const
  | succ m ih =>
      have hfun : (fun θ : Fin N → ℝ => ((spectralEnsembleMatrix P θ) ^ (m + 1)) x y)
          = ∑ z : Fin D, fun θ : Fin N → ℝ =>
              ((spectralEnsembleMatrix P θ) ^ m) x z * spectralEnsembleMatrix P θ z y := by
        funext θ
        rw [Finset.sum_apply, pow_succ, Matrix.mul_apply]
      rw [hfun]
      refine analyticAt_sum _ fun z _ => ?_
      exact (ih x z).mul (analyticAt_spectralEnsembleMatrix_entry P z y θ₀)

theorem analyticAt_ensembleKrylov_entry (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (χ : Fin D → ℂ)
    (x j : Fin D) (θ₀ : Fin N → ℝ) :
    AnalyticAt ℝ (fun θ : Fin N → ℝ => ensembleKrylov P χ θ x j) θ₀ := by
  have hfun : (fun θ : Fin N → ℝ => ensembleKrylov P χ θ x j)
      = ∑ y : Fin D, fun θ : Fin N → ℝ =>
          ((spectralEnsembleMatrix P θ) ^ (j : ℕ)) x y * χ y := by
    funext θ
    rw [Finset.sum_apply, ensembleKrylov]
    rfl
  rw [hfun]
  refine analyticAt_sum _ fun y _ => ?_
  exact (analyticAt_spectralEnsembleMatrix_pow_entry P _ x y θ₀).mul analyticAt_const

theorem analyticAt_ensembleKrylov_det (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (χ : Fin D → ℂ)
    (θ₀ : Fin N → ℝ) :
    AnalyticAt ℝ (fun θ : Fin N → ℝ => (ensembleKrylov P χ θ).det) θ₀ := by
  have hfun : (fun θ : Fin N → ℝ => (ensembleKrylov P χ θ).det)
      = ∑ σ : Equiv.Perm (Fin D), fun θ : Fin N → ℝ =>
          ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, ensembleKrylov P χ θ (σ i) i := by
    funext θ
    rw [Finset.sum_apply, Matrix.det_apply']
  rw [hfun]
  refine analyticAt_sum _ fun σ _ => ?_
  refine analyticAt_const.mul ?_
  have hprod : (fun θ : Fin N → ℝ => ∏ i, ensembleKrylov P χ θ (σ i) i)
      = ∏ i : Fin D, fun θ : Fin N → ℝ => ensembleKrylov P χ θ (σ i) i := by
    funext θ
    rw [Finset.prod_apply]
  rw [hprod]
  exact analyticAt_prod _ fun i _ => analyticAt_ensembleKrylov_entry P χ (σ i) i θ₀

/-- **The non-cyclic parameters are Lebesgue-null.**  The Krylov determinant is a real-analytic
function of the coefficients, so if one member of the family makes the seed cyclic then almost
every member does. -/
theorem volume_ensembleKrylov_det_eq_zero (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (χ : Fin D → ℂ)
    (hwit : ∃ θ₀ : Fin N → ℝ, (ensembleKrylov P χ θ₀).det ≠ 0) :
    volume {θ : Fin N → ℝ | (ensembleKrylov P χ θ).det = 0} = 0 := by
  obtain ⟨θ₀, hθ₀⟩ := hwit
  have hana : AnalyticOnNhd ℝ (fun θ : Fin N → ℝ => Complex.normSq (ensembleKrylov P χ θ).det)
      Set.univ := by
    intro θ _
    have hre : AnalyticAt ℝ (fun θ : Fin N → ℝ => ((ensembleKrylov P χ θ).det).re) θ :=
      (Complex.reCLM.analyticAt _).comp (analyticAt_ensembleKrylov_det P χ θ)
    have him : AnalyticAt ℝ (fun θ : Fin N → ℝ => ((ensembleKrylov P χ θ).det).im) θ :=
      (Complex.imCLM.analyticAt _).comp (analyticAt_ensembleKrylov_det P χ θ)
    have hfun : (fun θ : Fin N → ℝ => Complex.normSq (ensembleKrylov P χ θ).det)
        = (fun θ : Fin N → ℝ => ((ensembleKrylov P χ θ).det).re
            * ((ensembleKrylov P χ θ).det).re)
          + fun θ : Fin N → ℝ => ((ensembleKrylov P χ θ).det).im
            * ((ensembleKrylov P χ θ).det).im := by
      funext θ
      rw [Pi.add_apply, Complex.normSq_apply]
    rw [hfun]
    exact (hre.mul hre).add (him.mul him)
  have hne : ∃ θ : Fin N → ℝ, Complex.normSq (ensembleKrylov P χ θ).det ≠ 0 :=
    ⟨θ₀, by simpa [Complex.normSq_eq_zero] using hθ₀⟩
  have hset : {θ : Fin N → ℝ | (ensembleKrylov P χ θ).det = 0}
      = {θ : Fin N → ℝ | Complex.normSq (ensembleKrylov P χ θ).det = 0} := by
    ext θ
    simp
  rw [hset]
  exact analytic_zero_set_volume_fin N _ hana hne

/-! ## Homogeneity -/

theorem ensembleKrylov_const_mul (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (χ : Fin D → ℂ)
    (c : ℝ) (θ : Fin N → ℝ) :
    ensembleKrylov P χ (fun a => c * θ a)
      = ensembleKrylov P χ θ * Matrix.diagonal (fun j : Fin D => ((c : ℂ)) ^ (j : ℕ)) := by
  ext x j
  rw [Matrix.mul_diagonal, ensembleKrylov, ensembleKrylov]
  show ((spectralEnsembleMatrix P (fun a => c * θ a)) ^ (j : ℕ) *ᵥ χ) x
      = ((spectralEnsembleMatrix P θ) ^ (j : ℕ) *ᵥ χ) x * ((c : ℂ)) ^ (j : ℕ)
  rw [spectralEnsembleMatrix_smul P c θ, smul_pow]
  show ((((c : ℂ)) ^ (j : ℕ) • (spectralEnsembleMatrix P θ) ^ (j : ℕ)) *ᵥ χ) x = _
  rw [Matrix.smul_mulVec]
  show ((c : ℂ)) ^ (j : ℕ) * (((spectralEnsembleMatrix P θ) ^ (j : ℕ) *ᵥ χ) x) = _
  ring

theorem ensembleKrylov_det_eq_zero_of_const_mul (P : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (χ : Fin D → ℂ) (c : ℝ) {θ : Fin N → ℝ} (hθ : (ensembleKrylov P χ θ).det = 0) :
    (ensembleKrylov P χ (fun a => c * θ a)).det = 0 := by
  rw [ensembleKrylov_const_mul, Matrix.det_mul, hθ, zero_mul]

theorem continuous_ensembleKrylov_det (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (χ : Fin D → ℂ) :
    Continuous fun θ : Fin N → ℝ => (ensembleKrylov P χ θ).det := by
  refine continuous_iff_continuousAt.mpr fun θ => ?_
  exact (analyticAt_ensembleKrylov_det P χ θ).continuousAt

/-! ## The degenerate directions of the shell -/

/-- The coefficient directions at which the seed fails to be cyclic. -/
def krylovDegenerateSphere (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (χ : Fin D → ℂ) :
    Set (coeffSphere N) :=
  {x | (ensembleKrylov P χ (sphereCoeff x)).det = 0}

theorem measurableSet_krylovDegenerateSphere (P : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (χ : Fin D → ℂ) : MeasurableSet (krylovDegenerateSphere P χ) :=
  (isClosed_singleton (x := (0 : ℂ))).preimage
    ((continuous_ensembleKrylov_det P χ).comp continuous_sphereCoeff) |>.measurableSet

/-- **The non-cyclic directions are shell-null.** -/
theorem toSphere_krylovDegenerateSphere_eq_zero (P : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (χ : Fin D → ℂ) (hwit : ∃ θ₀ : Fin N → ℝ, (ensembleKrylov P χ θ₀).det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere (krylovDegenerateSphere P χ) = 0 := by
  classical
  have hmp := PiLp.volume_preserving_ofLp (Fin N)
  have hbase := volume_ensembleKrylov_det_eq_zero P χ hwit
  have hnull : (volume : Measure (EuclideanSpace ℝ (Fin N)))
      {x : EuclideanSpace ℝ (Fin N) | (ensembleKrylov P χ (WithLp.ofLp x)).det = 0} = 0 := by
    have hpre : {x : EuclideanSpace ℝ (Fin N) | (ensembleKrylov P χ (WithLp.ofLp x)).det = 0}
        = WithLp.ofLp ⁻¹' {θ : Fin N → ℝ | (ensembleKrylov P χ θ).det = 0} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  refine toSphere_eq_zero_of_scaleInvariant hnull ?_
    (measurableSet_krylovDegenerateSphere P χ) (fun θ hθ => hθ)
  intro r hr x hx
  have hofLp : WithLp.ofLp (r • x) = fun a => r * WithLp.ofLp x a := by
    funext a
    rw [PiLp.smul_apply]
    rfl
  show (ensembleKrylov P χ (WithLp.ofLp (r • x))).det = 0
  rw [hofLp]
  exact ensembleKrylov_det_eq_zero_of_const_mul P χ r hx

end

end GaloisForLFunctions.HTGeometry
