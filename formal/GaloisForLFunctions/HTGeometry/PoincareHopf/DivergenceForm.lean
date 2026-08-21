import GaloisForLFunctions.HTGeometry.PoincareHopf.PiolaIdentity
import GaloisForLFunctions.HTGeometry.PoincareHopf.CompactSupportDivergence

/-!
# The divergence form of the Jacobian determinant

For `u` of class `C²` and `W` of class `C¹` on `ℝⁿ`, set

  `V x j = ∑ i, cof (Du x)_{i j} · W (u x) i`.

Then `div V x = (div W) (u x) · det (Du x)`.

Two inputs make this work: the Piola identity, which kills the terms where the derivative hits the
cofactor, and the row contraction `∑ j, cof M _{i j} · M _{l j} = δ (l = i) · det M`, which turns
the remaining terms into the determinant times the divergence of `W` at `u x`.

Combined with the vanishing of the integral of a compactly supported divergence, this is exactly the
statement that makes the mollified determinant integral of degree theory independent of the choice
of mollifier.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {u W : (Fin n → ℝ) → (Fin n → ℝ)}

/-- A continuous linear map on `Fin n → ℝ` is the basis expansion of its values. -/
theorem clm_apply_eq_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (Fin n → ℝ) →L[ℝ] F) (v : Fin n → ℝ) :
    L v = ∑ l, v l • L (Pi.single l 1) := by
  have hv : v = ∑ l, v l • (Pi.single l (1 : ℝ) : Fin n → ℝ) := by
    funext m
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp

/-- The Piola field `V j = ∑ i, cof (Du)_{i j} · (W ∘ u) i`. -/
noncomputable def piolaField (u W : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∑ i, cofSum (jac u x) i j * W (u x) i

/-- The differential of the `j`-th component of the Piola field. -/
noncomputable def piolaFieldD (u W : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (j : Fin n) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, (cofSum (jac u x) i j •
        ((ContinuousLinearMap.proj i).comp ((fderiv ℝ W (u x)).comp (fderiv ℝ u x)))
      + W (u x) i • cofD u x i j)

theorem hasFDerivAt_piolaField (hu : ContDiff ℝ 2 u) (hW : ContDiff ℝ 1 W) (x : Fin n → ℝ) :
    HasFDerivAt (piolaField u W) (ContinuousLinearMap.pi (piolaFieldD u W x)) x := by
  classical
  have hu1 : HasFDerivAt u (fderiv ℝ u x) x := (hu.differentiable (by simp) x).hasFDerivAt
  have hW1 : HasFDerivAt W (fderiv ℝ W (u x)) (u x) :=
    (hW.differentiable (by simp) (u x)).hasFDerivAt
  have hcomp : HasFDerivAt (fun y => W (u y)) ((fderiv ℝ W (u x)).comp (fderiv ℝ u x)) x :=
    hW1.comp x hu1
  have hcompi : ∀ i : Fin n, HasFDerivAt (fun y => W (u y) i)
      ((ContinuousLinearMap.proj i).comp ((fderiv ℝ W (u x)).comp (fderiv ℝ u x))) x :=
    fun i => hasFDerivAt_pi'.mp hcomp i
  refine hasFDerivAt_pi'.mpr fun j => ?_
  rw [ContinuousLinearMap.proj_pi]
  have hfun : (fun y => piolaField u W y j)
      = ∑ i, (fun y => cofSum (jac u y) i j * W (u y) i) := by
    funext y
    rw [Finset.sum_apply]
    rfl
  rw [hfun, piolaFieldD]
  exact HasFDerivAt.sum fun i _ => (hasFDerivAt_cofSum hu x i j).mul (hcompi i)

/-- **Divergence form of the Jacobian determinant.** -/
theorem fieldDivergence_piolaField (hu : ContDiff ℝ 2 u) (hW : ContDiff ℝ 1 W) (x : Fin n → ℝ) :
    fieldDivergence (piolaField u W) x = fieldDivergence W (u x) * (jac u x).det := by
  classical
  have hV := hasFDerivAt_piolaField hu hW x
  have hfd : fderiv ℝ (piolaField u W) x = ContinuousLinearMap.pi (piolaFieldD u W x) := hV.fderiv
  have hstep0 : fieldDivergence (piolaField u W) x
      = ∑ j, piolaFieldD u W x j (Pi.single j 1) := by
    simp [fieldDivergence, hfd]
  -- expand each component
  have hcolumn : ∀ j : Fin n, (fderiv ℝ u x) (Pi.single j (1 : ℝ)) = fun l => jac u x l j := fun _ => rfl
  have hterm : ∀ j : Fin n, piolaFieldD u W x j (Pi.single j 1)
      = ∑ i, (cofSum (jac u x) i j * (∑ l, jac u x l j * jac W (u x) i l)
              + W (u x) i * cofD u x i j (Pi.single j 1)) := by
    intro j
    rw [piolaFieldD]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul]
    congr 1
    congr 1
    rw [clm_apply_eq_sum (fderiv ℝ W (u x)) ((fderiv ℝ u x) (Pi.single j 1))]
    rw [hcolumn j]
    simp [jac]
  have hsplit : ∑ j, piolaFieldD u W x j (Pi.single j 1)
      = (∑ j, ∑ i, cofSum (jac u x) i j * (∑ l, jac u x l j * jac W (u x) i l))
        + ∑ j, ∑ i, W (u x) i * cofD u x i j (Pi.single j 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hterm j, ← Finset.sum_add_distrib]
  have hpiola : (∑ j, ∑ i, W (u x) i * cofD u x i j (Pi.single j 1)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, piola hu x i, mul_zero]
  have hmain : (∑ j, ∑ i, cofSum (jac u x) i j * (∑ l, jac u x l j * jac W (u x) i l))
      = fieldDivergence W (u x) * (jac u x).det := by
    have hrw : ∀ j i : Fin n,
        cofSum (jac u x) i j * (∑ l, jac u x l j * jac W (u x) i l)
          = ∑ l, jac W (u x) i l * (cofSum (jac u x) i j * jac u x l j) := by
      intro j i
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    calc (∑ j, ∑ i, cofSum (jac u x) i j * (∑ l, jac u x l j * jac W (u x) i l))
        = ∑ j, ∑ i, ∑ l, jac W (u x) i l * (cofSum (jac u x) i j * jac u x l j) := by
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hrw j i
      _ = ∑ i, ∑ l, jac W (u x) i l * ∑ j, cofSum (jac u x) i j * jac u x l j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, ∑ l, jac W (u x) i l * (if l = i then (jac u x).det else 0) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
          rw [sum_cofSum_mul]
      _ = ∑ i, jac W (u x) i i * (jac u x).det := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp
      _ = fieldDivergence W (u x) * (jac u x).det := by
          rw [fieldDivergence, Finset.sum_mul]
          rfl
  rw [hstep0, hsplit, hpiola, hmain, add_zero]

end GaloisForLFunctions.HTGeometry.PoincareHopf
