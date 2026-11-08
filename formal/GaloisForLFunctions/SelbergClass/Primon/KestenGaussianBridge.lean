import GaloisForLFunctions.SelbergClass.Primon.KestenGaussianResidual
import GaloisForLFunctions.SelbergClass.Primon.KestenDirichletSchur
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The Dirichlet Green matrix is an actual Gaussian bridge covariance

Removing the prediction from site `n+1` leaves a finite Gaussian vector
independent of that terminal site. Its law is the centered multivariate
Gaussian with covariance equal to the inverse compressed source pencil.
-/

open _root_.RHTower MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The finite field after removing its next terminal predictor. -/
def kestenGaussianBridge (p : Nat.Primes) (n : ℕ) (ω : ℕ → ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => kestenGaussianResidual p (n + 1) i ω)

/-- The finite residual vector has an actual joint Gaussian law. -/
theorem hasGaussianLaw_kestenGaussianBridge (p : Nat.Primes) (n : ℕ) :
    HasGaussianLaw (kestenGaussianBridge p n) (kestenGaussianNoiseMeasure p) := by
  let L : ((Finset.univ : Finset (Fin (n + 1))) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    { toFun x i := x ⟨i, Finset.mem_univ i⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have h := ((isGaussianProcess_kestenGaussianResidual p (n + 1)).comp_right
    (fun i : Fin (n + 1) => i.val)).hasGaussianLaw Finset.univ
  exact (h.map L).map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm.toContinuousLinearMap

theorem integral_kestenGaussianBridge_coord (p : Nat.Primes) (n : ℕ) (i : Fin (n + 1)) :
    (∫ ω, kestenGaussianBridge p n ω i ∂kestenGaussianNoiseMeasure p) = 0 :=
  integral_kestenGaussianResidual p (n + 1) i

/-- Dirichlet inversion is the covariance of terminal regression, entry by entry. -/
theorem covariance_kestenGaussianBridge (p : Nat.Primes) (n : ℕ) (i j : Fin (n + 1)) :
    cov[fun ω => kestenGaussianBridge p n ω i, fun ω => kestenGaussianBridge p n ω j;
      kestenGaussianNoiseMeasure p] = kestenDirichletGreen p n i j := by
  change cov[kestenGaussianResidual p (n + 1) i, kestenGaussianResidual p (n + 1) j;
    kestenGaussianNoiseMeasure p] = _
  rw [covariance_kestenGaussianResidual, kestenDirichletGreen_eq_terminal_schur]

/-- The whole finite Dirichlet field is independent of the removed terminal coordinate. -/
theorem indepFun_kestenGaussianBridge_terminal (p : Nat.Primes) (n : ℕ) :
    IndepFun (kestenGaussianBridge p n) (kestenGaussianProcess p (n + 1))
      (kestenGaussianNoiseMeasure p) := by
  exact (indepFun_kestenGaussianResidual_terminal p (n + 1)).comp
    (show Measurable (fun x : ℕ → ℝ => WithLp.toLp 2 (fun i : Fin (n + 1) => x i)) by fun_prop)
    measurable_id

/-- The bridge has precisely the multivariate Gaussian law with Dirichlet covariance. -/
theorem hasLaw_kestenGaussianBridge (p : Nat.Primes) (n : ℕ) :
    HasLaw (kestenGaussianBridge p n) (multivariateGaussian 0 (kestenDirichletGreen p n))
      (kestenGaussianNoiseMeasure p) where
  aemeasurable := (hasGaussianLaw_kestenGaussianBridge p n).aemeasurable
  map_eq := by
    letI := (hasGaussianLaw_kestenGaussianBridge p n).isGaussian_map
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [integral_map (hasGaussianLaw_kestenGaussianBridge p n).aemeasurable
        (by fun_prop)]
      ext i
      change EuclideanSpace.proj i
        (∫ ω, kestenGaussianBridge p n ω ∂kestenGaussianNoiseMeasure p) = 0
      rw [← (EuclideanSpace.proj i).integral_comp_comm
        (hasGaussianLaw_kestenGaussianBridge p n).integrable]
      exact integral_kestenGaussianBridge_coord p n i
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covariance_map (by fun_prop) (by fun_prop)
        (hasGaussianLaw_kestenGaussianBridge p n).aemeasurable]
    have hproj (i : Fin (n + 1)) :
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          inner ℝ ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis i) x) = fun x => x i := by
      ext x
      simp [PiLp.inner_apply]
    simp_rw [hproj]
    exact (covariance_kestenGaussianBridge p n i j).trans
      (covariance_eval_multivariateGaussian (posDef_kestenDirichletGreen p n).posSemidef i j).symm

end
end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.hasGaussianLaw_kestenGaussianBridge
#print axioms GaloisForLFunctions.SelbergClass.Primon.integral_kestenGaussianBridge_coord
#print axioms GaloisForLFunctions.SelbergClass.Primon.covariance_kestenGaussianBridge
#print axioms GaloisForLFunctions.SelbergClass.Primon.indepFun_kestenGaussianBridge_terminal
#print axioms GaloisForLFunctions.SelbergClass.Primon.hasLaw_kestenGaussianBridge
