import GaloisForLFunctions.RHTower.DeningerAlternatizationOperator
import GaloisForLFunctions.RHTower.DeningerStageDeRham
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# The higher logarithmic differentials of a character stage

The exterior products of the logarithmic differentials of the coordinates are the classes that
generate the cohomology of a character stage.  In degree `k` and for a choice of `k` coordinates
they are the form whose coefficient is the product of the inverse coordinates and whose alternating
part is the determinant in those coordinates.  These forms are holomorphic on the stage and closed:
the coefficient depends only on the chosen coordinates, so its derivative pairs each of them against
a determinant in which that coordinate already occurs, and such a determinant vanishes.

* `deningerDetForm` : the determinant in a chosen tuple of coordinates, as a continuous alternating
  form.
* `deningerDetForm_expansion` : the cofactor expansion that makes a repeated column vanish.
* `deningerDlogWedge` : the exterior product `d log z_{σ 1} ∧ ⋯ ∧ d log z_{σ k}`.
* `deningerDlogWedge_holomorphic`, `deningerDlogWedge_closed` : it is holomorphic and closed.
-/

namespace RHTower

section DetForm

variable {r k : ℕ}

/-- **The determinant in a chosen tuple of coordinates**, as a continuous alternating form. -/
noncomputable def deningerDetForm (σ : Fin k → Fin r) : (Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ :=
  AlternatingMap.mkContinuous
    ((Matrix.detRowAlternating (R := ℂ) (n := Fin k)).compLinearMap
      (LinearMap.funLeft ℂ ℂ σ))
    (Nat.factorial k) (fun v => by
      show ‖Matrix.det (Matrix.of fun a b => v a (σ b))‖ ≤ _
      rw [Matrix.det_apply]
      calc ‖∑ π : Equiv.Perm (Fin k), (Equiv.Perm.sign π : ℤˣ) • ∏ i, v (π i) (σ i)‖
          ≤ ∑ π : Equiv.Perm (Fin k), ‖(Equiv.Perm.sign π : ℤˣ) • ∏ i, v (π i) (σ i)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _π : Equiv.Perm (Fin k), ∏ i, ‖v i‖ := by
            refine Finset.sum_le_sum fun π _ => ?_
            rw [deningerNorm_sign_smul, norm_prod]
            calc ∏ i, ‖v (π i) (σ i)‖ ≤ ∏ i, ‖v (π i)‖ :=
                  Finset.prod_le_prod (fun i _ => norm_nonneg _)
                    (fun i _ => norm_le_pi_norm _ _)
              _ = ∏ i, ‖v i‖ := Equiv.prod_comp π fun i => ‖v i‖
        _ = (Nat.factorial k : ℝ) * ∏ i, ‖v i‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
              nsmul_eq_mul])

theorem deningerDetForm_apply (σ : Fin k → Fin r) (v : Fin k → (Fin r → ℂ)) :
    deningerDetForm σ v = Matrix.det (Matrix.of fun a b => v a (σ b)) := rfl

/-- **The cofactor expansion of a determinant with a repeated column vanishes.**  This is the
identity that makes the higher logarithmic differentials closed. -/
theorem deningerDetForm_expansion (σ : Fin k → Fin r) (j : Fin k)
    (v : Fin (k + 1) → (Fin r → ℂ)) :
    ∑ i : Fin (k + 1), (-1 : ℂ) ^ (i : ℕ) * v i (σ j) *
      deningerDetForm σ (Fin.removeNth i v) = 0 := by
  set N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
    Matrix.of fun a b => v a ((Fin.cons (σ j) σ : Fin (k + 1) → Fin r) b) with hN
  have hcol : ∀ a : Fin (k + 1), N a 0 = N a j.succ := by
    intro a
    simp [hN, Fin.cons_zero, Fin.cons_succ]
  have hdet : N.det = 0 :=
    Matrix.det_zero_of_column_eq (Ne.symm (Fin.succ_ne_zero j)) hcol
  have hexp := Matrix.det_succ_column_zero N
  rw [hdet] at hexp
  have hterm : ∀ i : Fin (k + 1),
      (-1 : ℂ) ^ (i : ℕ) * N i 0 * (N.submatrix i.succAbove Fin.succ).det =
        (-1 : ℂ) ^ (i : ℕ) * v i (σ j) * deningerDetForm σ (Fin.removeNth i v) := by
    intro i
    have h0 : N i 0 = v i (σ j) := by simp [hN, Fin.cons_zero]
    have hsub : (N.submatrix i.succAbove Fin.succ) =
        Matrix.of fun a b => (Fin.removeNth i v) a (σ b) := by
      ext a b
      simp [hN, Fin.cons_succ, Fin.removeNth]
    rw [h0, hsub, deningerDetForm_apply]
  rw [Finset.sum_congr rfl fun i _ => hterm i] at hexp
  exact hexp.symm

end DetForm

section DlogWedge

variable {r k : ℕ}

/-- **The exterior product of the logarithmic differentials** of a chosen tuple of coordinates:
`d log z_{σ 1} ∧ ⋯ ∧ d log z_{σ k}`. -/
noncomputable def deningerDlogWedge (σ : Fin k → Fin r) : DeningerStageForm r k :=
  fun z => (∏ j, (z (σ j))⁻¹) • deningerDetForm σ

theorem deningerDlogWedge_apply (σ : Fin k → Fin r) (z : Fin r → ℂ)
    (v : Fin k → (Fin r → ℂ)) :
    deningerDlogWedge σ z v = (∏ j, (z (σ j))⁻¹) * deningerDetForm σ v := rfl

/-- The coefficient of the exterior product depends only on the chosen coordinates. -/
noncomputable def deningerWedgeCoeff (k : ℕ) : (Fin k → ℂ) → ℂ := fun w => ∏ j, (w j)⁻¹

/-- The coordinate projection onto a chosen tuple of coordinates. -/
noncomputable def deningerCoordProj (σ : Fin k → Fin r) : (Fin r → ℂ) →L[ℂ] (Fin k → ℂ) :=
  ContinuousLinearMap.pi fun b => ContinuousLinearMap.proj (σ b)

@[simp]
theorem deningerCoordProj_apply (σ : Fin k → Fin r) (z : Fin r → ℂ) (b : Fin k) :
    deningerCoordProj σ z b = z (σ b) := rfl

theorem deningerWedgeCoeff_comp (σ : Fin k → Fin r) :
    (fun z : Fin r → ℂ => ∏ j, (z (σ j))⁻¹) =
      deningerWedgeCoeff k ∘ deningerCoordProj σ := rfl

theorem deningerWedgeCoeff_analyticAt {w : Fin k → ℂ} (hw : ∀ j, w j ≠ 0) :
    AnalyticAt ℂ (deningerWedgeCoeff k) w := by
  have h : AnalyticAt ℂ (∏ j : Fin k, fun x : Fin k → ℂ => (x j)⁻¹) w := by
    refine Finset.analyticAt_prod _ fun j _ => ?_
    have hproj : AnalyticAt ℂ (fun x : Fin k → ℂ => x j) w :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) j).analyticAt w
    exact hproj.inv (hw j)
  have hfun : (∏ j : Fin k, fun x : Fin k → ℂ => (x j)⁻¹) = deningerWedgeCoeff k := by
    funext x
    simp [deningerWedgeCoeff, Finset.prod_apply]
  rwa [hfun] at h

/-- **The higher logarithmic differentials are holomorphic on the stage.** -/
theorem deningerDlogWedge_holomorphic (σ : Fin k → Fin r) :
    DeningerIsHolomorphicForm (deningerDlogWedge σ) := by
  intro z hz
  have hcoeff : AnalyticAt ℂ (fun y : Fin r → ℂ => ∏ j, (y (σ j))⁻¹) z := by
    rw [deningerWedgeCoeff_comp]
    exact (deningerWedgeCoeff_analyticAt (fun j => hz (σ j))).comp
      ((deningerCoordProj σ).analyticAt z)
  exact hcoeff.smul analyticAt_const

/-- The derivative of the coefficient factors through the chosen coordinates. -/
theorem deningerWedgeCoeff_hasFDerivAt (σ : Fin k → Fin r) {z : Fin r → ℂ}
    (hz : z ∈ deningerStageTorus r) :
    HasFDerivAt (fun y : Fin r → ℂ => ∏ j, (y (σ j))⁻¹)
      ((fderiv ℂ (deningerWedgeCoeff k) (deningerCoordProj σ z)).comp (deningerCoordProj σ)) z := by
  have hg : HasFDerivAt (deningerWedgeCoeff k)
      (fderiv ℂ (deningerWedgeCoeff k) (deningerCoordProj σ z)) (deningerCoordProj σ z) :=
    (deningerWedgeCoeff_analyticAt (w := deningerCoordProj σ z)
      (fun j => hz (σ j))).differentiableAt.hasFDerivAt
  exact hg.comp z (deningerCoordProj σ).hasFDerivAt

/-- **The higher logarithmic differentials are closed.** -/
theorem deningerDlogWedge_closed (σ : Fin k → Fin r) {z : Fin r → ℂ}
    (hz : z ∈ deningerStageTorus r) : extDeriv (deningerDlogWedge σ) z = 0 := by
  classical
  have hdiff : DifferentiableAt ℂ (deningerDlogWedge σ) z :=
    (deningerDlogWedge_holomorphic σ z hz).differentiableAt
  set M := fderiv ℂ (deningerWedgeCoeff k) (deningerCoordProj σ z) with hM
  have hcoeff := deningerWedgeCoeff_hasFDerivAt σ hz
  ext v
  rw [extDeriv_apply hdiff v]
  have hterm : ∀ i : Fin (k + 1),
      fderiv ℂ (fun y => deningerDlogWedge σ y (Fin.removeNth i v)) z (v i) =
        deningerDetForm σ (Fin.removeNth i v) * M (deningerCoordProj σ (v i)) := by
    intro i
    have h := hcoeff.mul_const (deningerDetForm σ (Fin.removeNth i v))
    have hfun : (fun y : Fin r → ℂ => deningerDlogWedge σ y (Fin.removeNth i v))
        = fun y => (∏ j, (y (σ j))⁻¹) * deningerDetForm σ (Fin.removeNth i v) := rfl
    rw [hfun, h.fderiv]
    rfl
  rw [show (0 : (Fin r → ℂ) [⋀^Fin (k + 1)]→L[ℂ] ℂ) v = 0 from rfl]
  simp only [hterm]
  have hdecomp : ∀ i : Fin (k + 1),
      M (deningerCoordProj σ (v i)) =
        ∑ j : Fin k, v i (σ j) * M (fun l => if j = l then 1 else 0) := by
    intro i
    conv_lhs => rw [show deningerCoordProj σ (v i) =
      ∑ j : Fin k, (deningerCoordProj σ (v i) j) • (fun l => if j = l then (1 : ℂ) else 0) from
        pi_eq_sum_univ _]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]; rfl
  simp only [hdecomp, Finset.mul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hexp := deningerDetForm_expansion σ j v
  have hstep : ∀ i : Fin (k + 1),
      ((-1 : ℤ) ^ (i : ℕ)) • (deningerDetForm σ (Fin.removeNth i v) *
          (v i (σ j) * M (fun l => if j = l then 1 else 0)))
        = M (fun l => if j = l then 1 else 0) *
          ((-1 : ℂ) ^ (i : ℕ) * v i (σ j) * deningerDetForm σ (Fin.removeNth i v)) := by
    intro i
    push_cast [zsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.mul_sum, hexp, mul_zero]

/-- **The determinant form is one on the coordinate basis it selects.** -/
theorem deningerDetForm_stdBasis {σ : Fin k → Fin r} (hσ : Function.Injective σ) :
    deningerDetForm σ (fun a => (Pi.single (σ a) (1 : ℂ) : Fin r → ℂ)) = 1 := by
  rw [deningerDetForm_apply]
  have hmat : (Matrix.of fun a b => (Pi.single (σ a) (1 : ℂ) : Fin r → ℂ) (σ b)) =
      (1 : Matrix (Fin k) (Fin k) ℂ) := by
    ext a b
    simp [Pi.single_apply, Matrix.one_apply, hσ.eq_iff, eq_comm]
  rw [hmat, Matrix.det_one]

/-- **The higher logarithmic differentials are nowhere zero on the stage**, so the closed classes
they define are not the zero form. -/
theorem deningerDlogWedge_ne_zero {σ : Fin k → Fin r} (hσ : Function.Injective σ)
    {z : Fin r → ℂ} (hz : z ∈ deningerStageTorus r) : deningerDlogWedge σ z ≠ 0 := by
  intro h
  have hval : deningerDlogWedge σ z (fun a => (Pi.single (σ a) (1 : ℂ) : Fin r → ℂ)) = 0 := by
    rw [h]
    rfl
  rw [deningerDlogWedge_apply, deningerDetForm_stdBasis hσ, mul_one] at hval
  exact (Finset.prod_ne_zero_iff.2 fun j _ => inv_ne_zero (hz (σ j))) hval

end DlogWedge

end RHTower
