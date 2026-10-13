import GaloisForLFunctions.RHTower.WeilLogShiftPowerCovarianceProduct
import GaloisForLFunctions.HTGeometry.FiniteLawProductEntropy

/-! # Exact information deficit of finite Weil power covariance -/

namespace RHTower

open MeasureTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped BigOperators

noncomputable section

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual positive quadratic-tilt weights as a finite probability law. -/
def finiteWeilCanonicalJointQuadraticTiltIndexLaw (r k : ℕ) (a b d : ℝ) :
    Law (Fin (r + 1)) :=
  ⟨finiteWeilCanonicalJointQuadraticTiltWeight r k a b d,
    ⟨fun i => (finiteWeilCanonicalJointQuadraticTiltWeight_pos r k a b d i).le,
      finiteWeilCanonicalJointQuadraticTiltWeight_sum r k a b d⟩⟩

/-- Uniform-weight determinant benchmark on the canonical finite support. -/
def finiteWeilPowerCovarianceUniformBenchmark (r : ℕ) : ℝ :=
  (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
    ((((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ^ 2) / ((r + 1 : ℕ) : ℝ)) *
    (((r + 1 : ℕ) : ℝ)⁻¹) ^ (r + 1)

theorem finiteWeilPowerCovarianceUniformBenchmark_pos (r : ℕ) :
    0 < finiteWeilPowerCovarianceUniformBenchmark r := by
  unfold finiteWeilPowerCovarianceUniformBenchmark
  apply mul_pos
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hij
    have hijFin : i < j := Finset.mem_Ioi.mp hij
    have hij' : (i : ℕ) < (j : ℕ) := hijFin
    have hgap : (0 : ℝ) < ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) :=
      sub_pos.mpr (by exact_mod_cast hij')
    exact div_pos (sq_pos_of_ne_zero hgap.ne') (by positivity)
  · positivity

/-- Exact determinant equals the uniform benchmark times its finite KL deficit factor. -/
theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_entropy
    (r k : ℕ) (a b d : ℝ) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z : E => z 0) r).det =
    finiteWeilPowerCovarianceUniformBenchmark r *
      Real.exp (-(((r + 1 : ℕ) : ℝ) *
        (Law.uniform (Fin (r + 1))).kl
          (finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d))) := by
  have hprod : (∏ i, finiteWeilCanonicalJointQuadraticTiltWeight r k a b d i) =
      (((r + 1 : ℕ) : ℝ)⁻¹) ^ (r + 1) *
        Real.exp (-(((r + 1 : ℕ) : ℝ) *
          (Law.uniform (Fin (r + 1))).kl
            (finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d))) := by
    have heval (i : Fin (r + 1)) :
        finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d i =
          finiteWeilCanonicalJointQuadraticTiltWeight r k a b d i := rfl
    simpa only [Fintype.card_fin, heval] using
      Law.prod_eq_uniform_factor_mul_exp_kl
        (finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d)
        (fun i => finiteWeilCanonicalJointQuadraticTiltWeight_pos r k a b d i)
  rw [finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_product,
    hprod, finiteWeilPowerCovarianceUniformBenchmark]
  ring

end

end RHTower
