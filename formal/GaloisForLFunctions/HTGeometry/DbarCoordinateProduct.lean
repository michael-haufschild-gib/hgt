import GaloisForLFunctions.HTGeometry.DbarAltForms

/-!
# Multiplying a form by a coordinate

The antiholomorphic derivative obeys the Leibniz rule, and the coordinate functions are
holomorphic, so multiplying a set-indexed form by a coordinate commutes with the Dolbeault
operator.  In particular a holomorphic function stays holomorphic after multiplication by a
coordinate — the statement that the ideal of a coordinate hyperplane is stable under the structure
sheaf.

* `HTGeometry.dzbarAt_mul` : the Leibniz rule for `∂̄_j`.
* `HTGeometry.dzbarAt_coord` : a coordinate is holomorphic.
* `HTGeometry.coordSetForm` : multiplication of a form by a coordinate.
* `HTGeometry.setDbar_coordSetForm` : it commutes with the Dolbeault operator.
-/

namespace HTGeometry

open Complex

section Leibniz

variable {n : ℕ}

/-- The antiholomorphic functional is complex homogeneous. -/
theorem dzbarFunctional_smul (j : Fin n) (c : ℂ) (A : (Fin n → ℂ) →L[ℝ] ℂ) :
    dzbarFunctional j (c • A) = c * dzbarFunctional j A := by
  rw [dzbarFunctional_apply, dzbarFunctional_apply, ContinuousLinearMap.smul_comp,
    wirtingerAntihol_smul]

/-- **`∂̄_j` obeys the Leibniz rule.** -/
theorem dzbarAt_mul {F G : (Fin n → ℂ) → ℂ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (j : Fin n) (z : Fin n → ℂ) :
    dzbarAt (fun x => F x * G x) j z = F z * dzbarAt G j z + G z * dzbarAt F j z := by
  have hFG : Differentiable ℝ fun x => F x * G x := fun x => (hF x).mul (hG x)
  have hmul : fderiv ℝ (fun x => F x * G x) z = F z • fderiv ℝ G z + G z • fderiv ℝ F z :=
    ((hF z).hasFDerivAt.mul (hG z).hasFDerivAt).fderiv
  rw [dzbarAt_eq_functional hFG j z, dzbarAt_eq_functional hF j z, dzbarAt_eq_functional hG j z,
    hmul, map_add, dzbarFunctional_smul, dzbarFunctional_smul]

/-- A coordinate function is smooth. -/
theorem contDiff_coord (i : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Fin n → ℂ => z i) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).contDiff

theorem differentiable_coord (i : Fin n) :
    Differentiable ℝ (fun z : Fin n → ℂ => z i) :=
  (contDiff_coord i).differentiable (by simp)

/-- **A coordinate is holomorphic**, so its antiholomorphic derivatives vanish. -/
theorem dzbarAt_coord (i j : Fin n) (z : Fin n → ℂ) :
    dzbarAt (fun x : Fin n → ℂ => x i) j z = 0 := by
  show dzbar (dbarSlice (fun x : Fin n → ℂ => x i) j z) (z j) = 0
  refine (dzbar_eq_zero_of_differentiableAt ?_).1
  by_cases hij : i = j
  · subst hij
    have hid : dbarSlice (fun x : Fin n → ℂ => x i) i z = fun t => t := by
      funext t
      show (Function.update z i t) i = t
      rw [Function.update_self]
    rw [hid]
    exact differentiableAt_id
  · have hconst : dbarSlice (fun x : Fin n → ℂ => x i) j z = fun _ => z i := by
      funext t
      show (Function.update z j t) i = z i
      rw [Function.update_of_ne hij]
    rw [hconst]
    exact differentiableAt_const _

end Leibniz

section CoordinateProduct

variable {n : ℕ}

/-- **Multiplication of a set-indexed form by a coordinate.** -/
def coordSetForm (i : Fin n) (f : SetForm n) : SetForm n := fun S z => z i * f S z

@[simp] theorem coordSetForm_apply (i : Fin n) (f : SetForm n) (S : Finset (Fin n))
    (z : Fin n → ℂ) : coordSetForm i f S z = z i * f S z := rfl

theorem SmoothSetForm.coord {f : SetForm n} (hf : SmoothSetForm f) (i : Fin n) :
    SmoothSetForm (coordSetForm i f) := fun S => (contDiff_coord i).mul (hf S)

theorem SetFormDeg.coord {q : ℕ} {f : SetForm n} (hf : SetFormDeg q f) (i : Fin n) :
    SetFormDeg q (coordSetForm i f) := fun S hS z => by
  rw [coordSetForm_apply, hf S hS z, mul_zero]

/-- **Multiplying by a coordinate commutes with the Dolbeault operator**, because the coordinate is
holomorphic. -/
theorem setDbar_coordSetForm {f : SetForm n} (hf : SmoothSetForm f) (i : Fin n)
    (S : Finset (Fin n)) (z : Fin n → ℂ) :
    setDbar (coordSetForm i f) S z = coordSetForm i (setDbar f) S z := by
  show (∑ k ∈ S, insertSign k (S.erase k) * dzbarAt (coordSetForm i f (S.erase k)) k z)
    = z i * ∑ k ∈ S, insertSign k (S.erase k) * dzbarAt (f (S.erase k)) k z
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show coordSetForm i f (S.erase k)
      = fun x => (fun y : Fin n → ℂ => y i) x * f (S.erase k) x from rfl,
    dzbarAt_mul (differentiable_coord i) (hf.differentiable _) k z, dzbarAt_coord, mul_zero,
    add_zero]
  ring

end CoordinateProduct

end HTGeometry
