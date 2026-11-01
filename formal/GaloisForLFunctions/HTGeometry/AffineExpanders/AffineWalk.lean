import GaloisForLFunctions.HTGeometry.BistochasticMixingMajorization
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Margulis–Gabber–Galil affine transition kernel

Four affine shears and their inverses act on the residue torus. Averaging their
permutation matrices gives a symmetric bistochastic kernel, including loops
and repeated edges. Its quadratic form pairs each map with its inverse.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- Horizontal affine shear of the residue torus. -/
def mggShearX (n : ℕ) (b : ZMod n) : Equiv.Perm (ZMod n × ZMod n) where
  toFun p := (p.1 + 2 * p.2 + b, p.2)
  invFun p := (p.1 - 2 * p.2 - b, p.2)
  left_inv p := Prod.ext (by dsimp; ring) rfl
  right_inv p := Prod.ext (by dsimp; ring) rfl

/-- Vertical affine shear of the residue torus. -/
def mggShearY (n : ℕ) (b : ZMod n) : Equiv.Perm (ZMod n × ZMod n) where
  toFun p := (p.1, p.2 + 2 * p.1 + b)
  invFun p := (p.1, p.2 - 2 * p.1 - b)
  left_inv p := Prod.ext rfl (by dsimp; ring)
  right_inv p := Prod.ext rfl (by dsimp; ring)

/-- The four forward affine maps in the Margulis–Gabber–Galil walk. -/
def mggGenerator (n : ℕ) : Fin 4 → Equiv.Perm (ZMod n × ZMod n) :=
  ![mggShearX n 0, mggShearY n 0, mggShearX n 1, mggShearY n 1]

variable (n : ℕ) [NeZero n]

/-- Each forward map and its inverse contributes one eighth of the transition weight.
Loops and repeated edges retain their multiplicities. -/
def mggAffineMatrix : Matrix (ZMod n × ZMod n) (ZMod n × ZMod n) ℝ :=
  fun u v => (∑ a : Fin 4,
    ((if mggGenerator n a u = v then 1 else 0) +
      (if (mggGenerator n a).symm u = v then 1 else 0))) / 8

omit [NeZero n] in
theorem mggAffineMatrix_symm (u v : ZMod n × ZMod n) :
    mggAffineMatrix n u v = mggAffineMatrix n v u := by
  unfold mggAffineMatrix
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  have h₁ : mggGenerator n a u = v ↔ (mggGenerator n a).symm v = u :=
    (mggGenerator n a).apply_eq_iff_eq_symm_apply.trans eq_comm
  have h₂ : (mggGenerator n a).symm u = v ↔ mggGenerator n a v = u :=
    (mggGenerator n a).symm.apply_eq_iff_eq_symm_apply.trans eq_comm
  simp only [h₁, h₂]
  ring

theorem mggAffineMatrix_row (u : ZMod n × ZMod n) :
    ∑ v, mggAffineMatrix n u v = 1 := by
  simp only [mggAffineMatrix, ← Finset.sum_div]
  rw [Finset.sum_comm]
  norm_num [Finset.sum_add_distrib]

/-- The eight affine transitions define a symmetric bistochastic kernel. -/
def mggAffineKernel : doublyStochastic ℝ (ZMod n × ZMod n) :=
  ⟨mggAffineMatrix n, mem_doublyStochastic_iff_sum.mpr
    ⟨fun u v => by unfold mggAffineMatrix; positivity,
      mggAffineMatrix_row n,
      fun v => by simp_rw [mggAffineMatrix_symm n]; exact mggAffineMatrix_row n v⟩⟩

/-- Matrix action is the literal average over the eight affine neighbours. -/
theorem mggAffineMatrix_mulVec (f : ZMod n × ZMod n → ℝ)
    (u : ZMod n × ZMod n) :
    (mggAffineMatrix n *ᵥ f) u =
      (∑ a : Fin 4, (f (mggGenerator n a u) + f ((mggGenerator n a).symm u))) / 8 := by
  simp only [Matrix.mulVec, dotProduct, mggAffineMatrix, div_mul_eq_mul_div,
    ← Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp [add_mul, Finset.sum_add_distrib]

/-- The affine walk preserves the sum of a function. -/
theorem sum_mggAffineMatrix_mulVec (f : ZMod n × ZMod n → ℝ) :
    ∑ u, (mggAffineMatrix n *ᵥ f) u = ∑ u, f u :=
  sum_mulVec_of_mem_doublyStochastic (mggAffineKernel n).property

/-- The affine walk contracts the sum of squares. -/
theorem mggAffineMatrix_sum_sq_le (f : ZMod n × ZMod n → ℝ) :
    ∑ u, (mggAffineMatrix n *ᵥ f) u ^ 2 ≤ ∑ u, f u ^ 2 :=
  bistochasticMixing_sum_sq_le (mggAffineKernel n) f

/-- Forward and inverse permutations have the same real quadratic form. -/
theorem sum_mul_perm_symm (e : Equiv.Perm (ZMod n × ZMod n))
    (f : ZMod n × ZMod n → ℝ) :
    ∑ u, f u * f (e.symm u) = ∑ u, f u * f (e u) := by
  rw [← Equiv.sum_comp e (fun u => f u * f (e.symm u))]
  simp only [Equiv.symm_apply_apply, mul_comm]

/-- Pairing inverse edges expresses the walk's quadratic form through four forward maps. -/
theorem mggAffineMatrix_quadratic (f : ZMod n × ZMod n → ℝ) :
    ∑ u, f u * (mggAffineMatrix n *ᵥ f) u =
      (∑ a : Fin 4, ∑ u, f u * f (mggGenerator n a u)) / 4 := by
  simp_rw [mggAffineMatrix_mulVec n f, ← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [mul_add, Finset.sum_add_distrib, sum_mul_perm_symm]
  ring

end GaloisForLFunctions.HTGeometry
