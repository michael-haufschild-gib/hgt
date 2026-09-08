import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-!
# Auxiliary Laplace separation of coupled energies

Equations (29)--(30) of arXiv:2608.29825 separate a negative real power of
an additive energy into one Gamma-weighted integral of independent
exponentials. Logarithmic parameters cover every positive exponent and
positive baseline without exporting positivity premises. Squared channel
coordinates permit zero channel energies.
-/

open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- A positive baseline together with finitely many nonnegative channel energies. -/
def coupledCollisionEnergy {n : ℕ} (e : ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.exp e + ∑ i, x i ^ 2

theorem coupledCollisionEnergy_pos {n : ℕ} (e : ℝ) (x : Fin n → ℝ) :
    0 < coupledCollisionEnergy e x := by
  unfold coupledCollisionEnergy
  positivity

/-- At fixed auxiliary time, the coupled exponential separates into every energy channel. -/
theorem coupledCollisionEnergy_exp_factorization {n : ℕ}
    (e t : ℝ) (x : Fin n → ℝ) :
    Real.exp (-coupledCollisionEnergy e x * t) =
      Real.exp (-Real.exp e * t) * ∏ i, Real.exp (-(x i ^ 2) * t) := by
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  simp [coupledCollisionEnergy, add_mul, Finset.sum_mul, Finset.sum_neg_distrib, add_comm]

/-- The auxiliary integral is convergent for every logarithmic shape parameter. -/
theorem coupledCollisionEnergy_laplace_integrable {n : ℕ}
    (a e : ℝ) (x : Fin n → ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (Real.exp a - 1) *
      Real.exp (-coupledCollisionEnergy e x * t)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (by linarith [Real.exp_pos a] : -1 < Real.exp a - 1)
      (le_refl (1 : ℝ)) (coupledCollisionEnergy_pos e x))

/-- Exact negative-power representation, with all convergence conditions proved internally. -/
theorem coupledCollisionEnergy_laplace {n : ℕ} (a e : ℝ) (x : Fin n → ℝ) :
    (coupledCollisionEnergy e x) ^ (-Real.exp a) =
      (Real.Gamma (Real.exp a))⁻¹ *
        ∫ t : ℝ in Ioi 0, t ^ (Real.exp a - 1) *
          Real.exp (-coupledCollisionEnergy e x * t) := by
  have hG : Real.Gamma (Real.exp a) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (Real.exp_pos a))
  rw [show (fun t : ℝ => t ^ (Real.exp a - 1) *
      Real.exp (-coupledCollisionEnergy e x * t)) =
      (fun t : ℝ => t ^ (Real.exp a - 1) *
      Real.exp (-(coupledCollisionEnergy e x * t))) by
        funext t; congr 2; ring]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (Real.exp_pos a)
    (coupledCollisionEnergy_pos e x), one_div, Real.rpow_neg_eq_inv_rpow]
  field_simp

/-- The literal integrand now factors over an arbitrary number of energy channels. -/
theorem coupledCollisionEnergy_separated_laplace {n : ℕ}
    (a e : ℝ) (x : Fin n → ℝ) :
    (coupledCollisionEnergy e x) ^ (-Real.exp a) =
      (Real.Gamma (Real.exp a))⁻¹ *
        ∫ t : ℝ in Ioi 0, t ^ (Real.exp a - 1) *
          Real.exp (-Real.exp e * t) * ∏ i, Real.exp (-(x i ^ 2) * t) := by
  rw [coupledCollisionEnergy_laplace]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [coupledCollisionEnergy_exp_factorization]
    ring

/-- Pairwise energy coupling underlying a fractional Cauchy/Gram kernel. -/
def collisionFractionalKernel (a e x y : ℝ) : ℝ :=
  (Real.exp e + x ^ 2 + y ^ 2) ^ (-Real.exp a)

/-- Gamma representation of each pairwise kernel entry. -/
theorem collisionFractionalKernel_laplace (a e x y : ℝ) :
    collisionFractionalKernel a e x y =
      (Real.Gamma (Real.exp a))⁻¹ *
        ∫ t : ℝ in Ioi 0, t ^ (Real.exp a - 1) *
          Real.exp (-(Real.exp e + x ^ 2 + y ^ 2) * t) := by
  have he : coupledCollisionEnergy e ![x,y] = Real.exp e + x ^ 2 + y ^ 2 := by
    simp [coupledCollisionEnergy, Fin.sum_univ_two, add_assoc]
  simpa only [he, collisionFractionalKernel, neg_mul] using
    coupledCollisionEnergy_laplace a e ![x,y]

/-- Every entry integral is absolutely convergent. -/
theorem collisionFractionalKernel_integrable (a e x y : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (Real.exp a - 1) *
      Real.exp (-(Real.exp e + x ^ 2 + y ^ 2) * t)) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (by linarith [Real.exp_pos a] : -1 < Real.exp a - 1)
      (le_refl (1 : ℝ)) (by positivity : 0 < Real.exp e + x ^ 2 + y ^ 2))

/-- Entrywise coupling is the product of two independent Laplace features. -/
theorem collisionFractionalKernel_feature (e t x y : ℝ) :
    Real.exp (-(Real.exp e + x ^ 2 + y ^ 2) * t) =
      Real.exp (-Real.exp e * t) * Real.exp (-x ^ 2 * t) * Real.exp (-y ^ 2 * t) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The whole finite quadratic form is one integral of a square. -/
theorem collisionFractionalKernel_gram {n : ℕ} (a e : ℝ) (x c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * collisionFractionalKernel a e (x i) (x j) =
      (Real.Gamma (Real.exp a))⁻¹ *
        ∫ t : ℝ in Ioi 0, t ^ (Real.exp a - 1) * Real.exp (-Real.exp e * t) *
          (∑ i, c i * Real.exp (-(x i ^ 2) * t)) ^ 2 := by
  simp_rw [collisionFractionalKernel_laplace]
  have h (i j : Fin n) : IntegrableOn (fun t : ℝ => c i * c j *
      (t ^ (Real.exp a - 1) * Real.exp (-(Real.exp e + x i ^ 2 + x j ^ 2) * t)))
      (Ioi 0) := (collisionFractionalKernel_integrable a e (x i) (x j)).const_mul _
  calc
    _ = (Real.Gamma (Real.exp a))⁻¹ *
        ∑ i, ∑ j, ∫ t : ℝ in Ioi 0, c i * c j *
          (t ^ (Real.exp a - 1) * Real.exp (-(Real.exp e + x i ^ 2 + x j ^ 2) * t)) := by
      simp only [integral_const_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      congr 1
      have hi (i : Fin n) := integral_finsetSum Finset.univ (fun j _ => h i j)
      simp_rw [← hi]
      rw [← integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum _ (fun j _ => h i j))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        simp_rw [collisionFractionalKernel_feature]
        rw [sq, Finset.sum_mul_sum]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- Every finite fractional-energy kernel is positive semidefinite, with no node conditions. -/
theorem collisionFractionalKernel_nonneg {n : ℕ} (a e : ℝ) (x c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * collisionFractionalKernel a e (x i) (x j) := by
  rw [collisionFractionalKernel_gram]
  apply mul_nonneg (by positivity)
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  positivity

end GaloisForLFunctions.HTGeometry
