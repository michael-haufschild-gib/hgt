import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Inverse response to a rank-one perturbation

For a positive definite matrix, the inverse correction factors through
the response to the perturbing vector. The same factorization gives the
entrywise derivative throughout the regular part of the pencil.
-/

open Matrix Filter
open scoped Matrix NNReal Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {A : Matrix V V ℝ}

/-- The change in inverse is the outer product of the unperturbed
response, scaled by the scalar denominator. -/
theorem inv_add_smul_vecMulVec (hA : A.PosDef) (d : V → ℝ) (t : ℝ)
    (ht : 1 + t * (d ⬝ᵥ (A⁻¹ *ᵥ d)) ≠ 0) :
    (A + t • vecMulVec d d)⁻¹ =
      A⁻¹ - (t / (1 + t * (d ⬝ᵥ (A⁻¹ *ᵥ d)))) •
        vecMulVec (A⁻¹ *ᵥ d) (A⁻¹ *ᵥ d) := by
  let v := A⁻¹ *ᵥ d
  let q := d ⬝ᵥ v
  let B := A + t • vecMulVec d d
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hAv : A *ᵥ v = d := by
    change A *ᵥ (A⁻¹ *ᵥ d) = d
    rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hsymm : (A⁻¹)ᵀ = A⁻¹ := by
    ext i j
    simpa only [Matrix.transpose_apply, star_trivial] using hA.isHermitian.inv.apply i j
  have hv : d ᵥ* A⁻¹ = v := by
    rw [← Matrix.mulVec_transpose, hsymm]
  have hleft : B * A⁻¹ = 1 + t • vecMulVec d v := by
    simp only [B, Matrix.add_mul, Matrix.smul_mul, hAA, Matrix.vecMulVec_mul, hv]
  have hright : B * vecMulVec v v = (1 + t * q) • vecMulVec d v := by
    change (A + t • vecMulVec d d) * vecMulVec v v = _
    rw [Matrix.add_mul, Matrix.mul_vecMulVec A, hAv, Matrix.smul_mul,
      Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, add_smul, one_smul]
  change B⁻¹ = A⁻¹ - (t / (1 + t * q)) • vecMulVec v v
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_sub, Matrix.mul_smul, hleft, hright, smul_smul,
    div_mul_cancel₀ _ ht, add_sub_cancel_right]

/-- A nonnegative perturbation has a strictly positive denominator. -/
theorem rankOneUpdate_denominator_pos (hA : A.PosDef) (d : V → ℝ) (t : ℝ≥0) :
    0 < 1 + (t : ℝ) * (d ⬝ᵥ (A⁻¹ *ᵥ d)) := by
  have hq : 0 ≤ d ⬝ᵥ (A⁻¹ *ᵥ d) := by
    simpa only [star_trivial] using hA.inv.posSemidef.dotProduct_mulVec_nonneg d
  exact add_pos_of_pos_of_nonneg one_pos (mul_nonneg t.coe_nonneg hq)

/-- The squared overlap with the perturbing response is exactly the loss
in the inverse quadratic form. -/
theorem dotProduct_inv_add_smul_vecMulVec (hA : A.PosDef) (d x : V → ℝ) (t : ℝ≥0) :
    x ⬝ᵥ ((A + (t : ℝ) • vecMulVec d d)⁻¹ *ᵥ x) =
      x ⬝ᵥ (A⁻¹ *ᵥ x) -
        ((t : ℝ) / (1 + (t : ℝ) * (d ⬝ᵥ (A⁻¹ *ᵥ d)))) * (x ⬝ᵥ (A⁻¹ *ᵥ d)) ^ 2 := by
  rw [inv_add_smul_vecMulVec hA d _ (rankOneUpdate_denominator_pos hA d t).ne',
    Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    dotProduct_smul, dotProduct_smul]
  change _ - (_ / _) * ((x ⬝ᵥ (A⁻¹ *ᵥ d)) * ((A⁻¹ *ᵥ d) ⬝ᵥ x)) = _
  rw [dotProduct_comm (A⁻¹ *ᵥ d) x, pow_two]

/-- The inverse entry derivative factors as the product of the two
unperturbed responses, divided by the squared scalar denominator. -/
theorem hasDerivAt_inv_add_smul_vecMulVec_apply (hA : A.PosDef) (d : V → ℝ) (t : ℝ)
    (ht : 1 + t * (d ⬝ᵥ (A⁻¹ *ᵥ d)) ≠ 0) (i j : V) :
    HasDerivAt (fun s => (A + s • vecMulVec d d)⁻¹ i j)
      (-((A⁻¹ *ᵥ d) i * (A⁻¹ *ᵥ d) j) / (1 + t * (d ⬝ᵥ (A⁻¹ *ᵥ d))) ^ 2) t := by
  let v := A⁻¹ *ᵥ d
  let q := d ⬝ᵥ v
  let D (s : ℝ) := 1 + s * q
  have hD : HasDerivAt D q t := by
    have h := (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).mul_const q)
    change HasDerivAt (fun s => 1 + s * q) (0 + 1 * q) t at h
    simpa only [D, one_mul, zero_add] using h
  have hquot : HasDerivAt (fun s => s / D s) (1 / (D t) ^ 2) t := by
    have htop : 1 * D t - t * q = 1 := by dsimp only [D]; ring
    have h := (hasDerivAt_id t).div hD ht
    change HasDerivAt (fun s => s / D s) ((1 * D t - t * q) / (D t) ^ 2) t at h
    rwa [htop] at h
  have hmodel := ((hquot.mul_const (v i * v j)).const_sub (A⁻¹ i j))
  have hderiv : HasDerivAt (fun s => A⁻¹ i j - s / D s * (v i * v j))
      (-(v i * v j) / (D t) ^ 2) t := by
    have hcoef : -(1 / (D t) ^ 2 * (v i * v j)) = -(v i * v j) / (D t) ^ 2 := by ring
    rw [← hcoef]
    exact hmodel
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [hD.continuousAt.eventually_ne ht] with s hs
  rw [inv_add_smul_vecMulVec hA d s hs, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]

#print axioms inv_add_smul_vecMulVec
#print axioms dotProduct_inv_add_smul_vecMulVec
#print axioms hasDerivAt_inv_add_smul_vecMulVec_apply

end

end GaloisForLFunctions.HTGeometry
