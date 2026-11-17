import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Determinant reduction for reflection walks

Sylvester interchange reduces a reflection walk to a quadratic pencil on
its compressed signal space. Projection determinants supply the exact
endpoint factors. The argument holds over arbitrary coefficient fields.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorDeterminant
open Polynomial
variable {K V W : Type*} [Field K] [AddCommGroup V] [AddCommGroup W]
  [Module K V] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

/-- Rectangular determinant interchange for finite-dimensional linear maps. -/
theorem det_one_sub_comp (A : V →ₗ[K] W) (B : W →ₗ[K] V) :
    LinearMap.det (1 - A.comp B) = LinearMap.det (1 - B.comp A) := by
  classical
  let bV := Module.finBasis K V
  let bW := Module.finBasis K W
  rw [← LinearMap.det_toMatrix bW, ← LinearMap.det_toMatrix bV]
  simp only [map_sub, LinearMap.toMatrix_one]
  rw [LinearMap.toMatrix_comp bW bV bW A B, LinearMap.toMatrix_comp bV bW bV B A]
  exact Matrix.det_one_sub_mul_comm _ _

/-- A projection pencil has one scalar factor for its range and one for its kernel. -/
theorem det_projection_pencil (P : Module.End K V) (hP : IsIdempotentElem P) (a b : K) :
    LinearMap.det (a • 1 + b • P) =
      (a + b) ^ Module.finrank K (LinearMap.range P) *
        a ^ Module.finrank K (LinearMap.ker P) := by
  classical
  let hp := LinearMap.IsIdempotentElem.isProj_range P hP
  let e := Submodule.prodEquivOfIsCompl (LinearMap.range P) (LinearMap.ker P) hp.isCompl
  have hfix (u : LinearMap.range P) : P u = (u : V) := by
    obtain ⟨v, hv⟩ := u.property
    rw [← hv]
    exact LinearMap.congr_fun hP.eq v
  have hconj : a • (1 : Module.End K V) + b • P =
      e.conj (LinearMap.prodMap
        ((a + b) • (1 : Module.End K (LinearMap.range P)))
        (a • (1 : Module.End K (LinearMap.ker P)))) := by
    apply LinearMap.ext
    intro x
    obtain ⟨⟨u, v⟩, rfl⟩ := e.surjective x
    change a • e (u, v) + b • P (e (u, v)) =
      e ((LinearMap.prodMap ((a + b) • (1 : Module.End K (LinearMap.range P)))
        (a • (1 : Module.End K (LinearMap.ker P)))) (e.symm (e (u, v))))
    rw [e.symm_apply_apply]
    change a • ((u : V) + v) + b • P ((u : V) + v) =
      (a + b) • (u : V) + a • (v : V)
    rw [map_add, hfix, show P (v : V) = 0 from v.property, add_zero]
    module
  rw [hconj, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj, LinearMap.det_prodMap,
    LinearMap.det_smul, map_one, mul_one,
    LinearMap.det_smul, map_one, mul_one]

/-- A product of a reflection and a projection reflection reduces to the compressed signal determinant. -/
theorem det_reflection_walk (R : Module.End K V) (hR : R * R = 1)
    (i : W →ₗ[K] V) (q : V →ₗ[K] W) (hi : q.comp i = 1)
    (t : K) (ht : t ^ 2 ≠ 1) :
    LinearMap.det (t • 1 - R * ((2 : K) • i.comp q - 1)) *
        (t ^ 2 - 1) ^ Module.finrank K W =
      LinearMap.det (t • 1 + R) *
        LinearMap.det ((t ^ 2 + 1) • 1 - (2 * t) • (q.comp R).comp i) := by
  let B : Module.End K V := t • 1 + R
  let U : Module.End K V := (t ^ 2 - 1)⁻¹ • (t • R - 1)
  have hd : t ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr ht
  have hBR : B * (t • R - 1) = (t ^ 2 - 1) • R := by
    dsimp [B]
    simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, hR]
    module
  have hBU : B * U = R := by
    change B * ((t ^ 2 - 1)⁻¹ • (t • R - 1)) = R
    rw [mul_smul_comm, hBR, smul_smul, inv_mul_cancel₀ hd, one_smul]
  have hfactor : t • 1 - R * ((2 : K) • i.comp q - 1) =
      B * (1 - ((2 : K) • (U.comp i)).comp q) := by
    apply LinearMap.ext
    intro x
    have hb := LinearMap.congr_fun hBU (i (q x))
    change B (U (i (q x))) = R (i (q x)) at hb
    change t • x - R ((2 : K) • i (q x) - x) = B (x - (2 : K) • U (i (q x)))
    rw [map_sub, map_smul, map_sub, map_smul, hb]
    change t • x - ((2 : K) • R (i (q x)) - R x) =
      (t • x + R x) - (2 : K) • R (i (q x))
    module
  have hsmall : 1 - q.comp ((2 : K) • U.comp i) =
      (t ^ 2 - 1)⁻¹ • ((t ^ 2 + 1) • 1 - (2 * t) • (q.comp R).comp i) := by
    apply LinearMap.ext
    intro w
    have hw := LinearMap.congr_fun hi w
    change q (i w) = w at hw
    change w - q ((2 : K) • ((t ^ 2 - 1)⁻¹ • (t • R (i w) - i w))) =
      (t ^ 2 - 1)⁻¹ • ((t ^ 2 + 1) • w - (2 * t) • q (R (i w)))
    rw [map_smul, map_smul, map_sub, map_smul, hw]
    have hs : (t ^ 2 - 1)⁻¹ * (t ^ 2 - 1) = 1 := inv_mul_cancel₀ hd
    calc
      _ = ((t ^ 2 - 1)⁻¹ * (t ^ 2 - 1)) • w -
        (2 : K) • ((t ^ 2 - 1)⁻¹ • (t • q (R (i w)) - w)) := by rw [hs, one_smul]
      _ = _ := by module
  rw [hfactor, map_mul, det_one_sub_comp, hsmall, LinearMap.det_smul]
  have hs : ((t ^ 2 - 1)⁻¹) ^ Module.finrank K W *
      (t ^ 2 - 1) ^ Module.finrank K W = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hd, one_pow]
  calc
    _ = LinearMap.det B *
      LinearMap.det ((t ^ 2 + 1) • 1 - (2 * t) • (q.comp R).comp i) *
        (((t ^ 2 - 1)⁻¹) ^ Module.finrank K W *
          (t ^ 2 - 1) ^ Module.finrank K W) := by ring
    _ = _ := by rw [hs, mul_one]

/-- Polynomial determinant of the compressed quadratic signal pencil. -/
def quadraticPencil (T : Module.End K V) : K[X] :=
  let b := Module.finBasis K V
  Matrix.det (((Polynomial.X ^ 2 + 1) : K[X]) •
    (1 : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K[X]) -
    (Polynomial.C (2 : K) * Polynomial.X) • (LinearMap.toMatrix b b T).map Polynomial.C)

/-- Evaluating the polynomial pencil gives the intrinsic operator determinant. -/
theorem quadraticPencil_eval (T : Module.End K V) (t : K) :
    (quadraticPencil T).eval t = LinearMap.det ((t ^ 2 + 1) • 1 - (2 * t) • T) := by
  classical
  let b := Module.finBasis K V
  unfold quadraticPencil
  rw [show Polynomial.eval t = Polynomial.evalRingHom t from rfl,
    RingHom.map_det, ← LinearMap.det_toMatrix b]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij, b, RingHom.mapMatrix, Matrix.map_apply, Matrix.smul_apply,
    LinearMap.toMatrix_one, smul_eq_mul]

#print axioms quadraticPencil_eval
#print axioms det_reflection_walk
#print axioms det_one_sub_comp
#print axioms det_projection_pencil
end GaloisForLFunctions.RepresentationLifting.OperatorDeterminant
