import GaloisForLFunctions.HTGeometry.VandermondeSamplingEnergy
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Heat-weighted interpolation without a common node or cofactor cap

The exact adjugate columns control the coefficient energy. Exponential
weights are paired before Cauchy--Schwarz, preserving all polynomial sample
cross terms and every individual node rate.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators

def polynomialSamplingHeatCapacity {n : ℕ} (z : Fin n → ℂ)
    (rate : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ j, ∑ i, ‖(Matrix.vandermonde z).adjugate j i‖ ^ 2 * Real.exp (t * rate i)

theorem polynomialSamplingHeatCapacity_nonneg {n : ℕ} (z : Fin n → ℂ)
    (rate : Fin n → ℝ) (t : ℝ) : 0 ≤ polynomialSamplingHeatCapacity z rate t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

/-- Full coefficient energy is controlled by the exactly weighted sample energy. -/
theorem polynomialSample_heat_weighted_energy_bound {n : ℕ} (z a : Fin n → ℂ)
    (rate : Fin n → ℝ) (t : ℝ) :
    ‖(Matrix.vandermonde z).det‖ ^ 2 * (∑ j, ‖a j‖ ^ 2) ≤
      polynomialSamplingHeatCapacity z rate t *
        ∑ i, ‖polynomialSample a (z i)‖ ^ 2 * Real.exp (-(t * rate i)) := by
  classical
  let V := Matrix.vandermonde z
  let y := V.mulVec a
  have hy (i : Fin n) : y i = polynomialSample a (z i) := by
    simp only [y, V, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
      polynomialSample, mul_comm]
  have hc : V.adjugate.mulVec y = V.det • a := by
    change V.adjugate.mulVec (V.mulVec a) = _
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcoord (j : Fin n) :
      ‖V.det‖ ^ 2 * ‖a j‖ ^ 2 ≤
        (∑ i, ‖V.adjugate j i‖ ^ 2 * Real.exp (t * rate i)) *
          ∑ i, ‖y i‖ ^ 2 * Real.exp (-(t * rate i)) := by
    have hj := congrArg (fun v : Fin n → ℂ => v j) hc
    have htri : ‖V.det‖ * ‖a j‖ ≤ ∑ i, ‖V.adjugate j i‖ * ‖y i‖ := by
      rw [← norm_mul]
      rw [show V.det * a j = V.adjugate.mulVec y j by
        simpa only [Pi.smul_apply, smul_eq_mul] using hj.symm]
      change ‖∑ i, V.adjugate j i * y i‖ ≤ _
      simpa only [norm_mul] using
        (norm_sum_le Finset.univ (fun i => V.adjugate j i * y i))
    have hsq := (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htri
    rw [mul_pow] at hsq
    have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (Finset.univ : Finset (Fin n))
      (r := fun i => ‖V.adjugate j i‖ * ‖y i‖)
      (f := fun i => ‖V.adjugate j i‖ ^ 2 * Real.exp (t * rate i))
      (g := fun i => ‖y i‖ ^ 2 * Real.exp (-(t * rate i)))
      (fun _ _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (fun _ _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (fun i _ => by
        have he : Real.exp (t * rate i) * Real.exp (-(t * rate i)) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        calc
          _ = (‖V.adjugate j i‖ ^ 2 * ‖y i‖ ^ 2) * 1 := by ring
          _ ≤ _ := le_of_eq (by rw [← he]; ring))
    exact hsq.trans hCS
  calc
    _ = ∑ j, ‖V.det‖ ^ 2 * ‖a j‖ ^ 2 := Finset.mul_sum ..
    _ ≤ ∑ j, (∑ i, ‖V.adjugate j i‖ ^ 2 * Real.exp (t * rate i)) *
        ∑ i, ‖y i‖ ^ 2 * Real.exp (-(t * rate i)) :=
      Finset.sum_le_sum fun j _ => hcoord j
    _ = _ := by rw [← Finset.sum_mul]; simp only [polynomialSamplingHeatCapacity, V, hy]

/-- Distinct nodes make the coefficient-independent heat capacity strictly positive. -/
theorem polynomialSamplingHeatCapacity_pos (n : ℕ)
    (z : {z : Fin (n + 1) → ℂ // Function.Injective z})
    (rate : Fin (n + 1) → ℝ) (t : ℝ) :
    0 < polynomialSamplingHeatCapacity z.1 rate t := by
  classical
  let j₀ : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  let a : Fin (n + 1) → ℂ := fun j => if j = j₀ then 1 else 0
  have ha : (∑ j, ‖a j‖ ^ 2) = 1 := by simp [a, apply_ite]
  have hD : 0 < ‖(Matrix.vandermonde z.1).det‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr z.property)) _
  have h := polynomialSample_heat_weighted_energy_bound z.1 a rate t
  rw [ha, mul_one] at h
  have hn : polynomialSamplingHeatCapacity z.1 rate t ≠ 0 := by
    intro he
    rw [he, zero_mul] at h
    exact not_le_of_gt hD h
  exact lt_of_le_of_ne (polynomialSamplingHeatCapacity_nonneg z.1 rate t) hn.symm

/-- Exact cofactor weights are no larger than the old common cofactor cap. -/
theorem polynomialSamplingHeatCapacity_le_common_cap {n : ℕ} (z : Fin n → ℂ)
    (rate : Fin n → ℝ) (t : ℝ) :
    polynomialSamplingHeatCapacity z rate t ≤
      (n : ℝ) * polynomialSamplingCap z ^ 2 * ∑ i, Real.exp (t * rate i) := by
  have hB := one_le_phaseFrequencyScale z
  have hentry := norm_vandermonde_apply_le_pow hB (norm_le_phaseFrequencyScale z)
  have hcap : 0 ≤ polynomialSamplingCap z := by
    unfold polynomialSamplingCap
    positivity
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hcap).mpr
          (norm_adjugate_apply_le_factorial_mul_pow (Matrix.vandermonde z)
            (one_le_pow₀ hB) hentry j i)) (Real.exp_pos (t * rate i)).le))
  change polynomialSamplingHeatCapacity z rate t ≤
    ∑ _j : Fin n, ∑ i, polynomialSamplingCap z ^ 2 * Real.exp (t * rate i) at h
  simpa only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_assoc, mul_left_comm] using h

end
end GaloisForLFunctions.HTGeometry
