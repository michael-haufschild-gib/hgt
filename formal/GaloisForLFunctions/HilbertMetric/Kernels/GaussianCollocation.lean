import GaloisForLFunctions.HTGeometry.ExponentialKernelTotalPositivity
import GaloisForLFunctions.HilbertMetric.CentroidGauge
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gaussian interpolation on ordered grids

Salazar's diagonal factorization (arXiv:2607.02778, Lemma 4.1) applies to
two independent real grids. It gives strict signs for every ordered minor
and the alternating signs of the inverse interpolation matrix. An arithmetic
progression of centers gives an ordinary Vandermonde product.
-/

namespace GaloisForLFunctions.HilbertMetric
open HTGeometry Matrix Finset
noncomputable section

/-- Gaussian samples, with log precision `t` and possibly different row and column grids. -/
def gaussianCollocation {ι κ : Type*} (t : ℝ) (x : ι → ℝ) (y : κ → ℝ) : Matrix ι κ ℝ :=
  of fun i j => Real.exp (-Real.exp t * (x i - y j) ^ 2)

variable {n : ℕ}

private lemma gaussian_factor (a x y : ℝ) :
    Real.exp (-a * (x - y) ^ 2) =
      Real.exp (-a * x ^ 2) * (Real.exp (-a * y ^ 2) * Real.exp ((2 * a * x) * y)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The row and column gauges leave exactly the exponential node determinant. -/
theorem det_gaussianCollocation (t : ℝ) (x y : Fin n → ℝ) :
    (gaussianCollocation t x y).det =
      (∏ i, Real.exp (-Real.exp t * x i ^ 2)) *
      ((∏ j, Real.exp (-Real.exp t * y j ^ 2)) *
        (expNodeMatrix (fun i => 2 * Real.exp t * x i) y).det) := by
  rw [← det_mul_row, ← det_mul_column]
  congr 1
  ext i j
  exact gaussian_factor _ _ _

/-- All ordered mixed minors are strictly positive, even on irregular real grids. -/
theorem gaussianCollocation_det_pos (t : ℝ) (x y : Fin n ↪o ℝ) :
    0 < (gaussianCollocation t x y).det := by
  rw [det_gaussianCollocation]
  have h : StrictMono (fun i => 2 * Real.exp t * x i) :=
    fun _ _ hij => mul_lt_mul_of_pos_left (x.strictMono hij) (by positivity)
  exact mul_pos (prod_pos fun _ _ => Real.exp_pos _)
    (mul_pos (prod_pos fun _ _ => Real.exp_pos _) (det_expKernel_pos h y.strictMono))

/-- Salazar's discrete Gaussian Toeplitz kernel is strictly totally positive on
the full integer lattice, with no restriction on the signs of either grid. -/
theorem discreteGaussian_minor_pos (q : Set.Ioo (0:ℝ) 1) (x y : Fin n ↪o ℤ) :
    0 < (of fun i j => q.val ^ ((x i - y j).natAbs ^ 2)).det := by
  let e : ℤ ↪o ℝ := OrderEmbedding.ofStrictMono (fun k : ℤ => (k : ℝ)) (fun _ _ h => Int.cast_lt.mpr h)
  have hq : 0 < -Real.log q.val := neg_pos.mpr (Real.log_neg q.2.1 q.2.2)
  have he (i j : Fin n) : q.val ^ ((x i - y j).natAbs ^ 2) =
      gaussianCollocation (Real.log (-Real.log q.val)) (x.trans e) (y.trans e) i j := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos q.2.1]
    change Real.exp _ = Real.exp (-Real.exp (Real.log (-Real.log q.val)) *
      ((x i : ℝ) - (y j : ℝ)) ^ 2)
    rw [Real.exp_log hq, neg_neg]
    rw [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, sq_abs]
  have hm : (of fun i j => q.val ^ ((x i - y j).natAbs ^ 2)) =
      gaussianCollocation (Real.log (-Real.log q.val)) (x.trans e) (y.trans e) :=
    Matrix.ext fun i j => he i j
  rw [hm]
  exact gaussianCollocation_det_pos _ _ _

/-- Every ordered cross minor of the existing Gaussian distance matrix on the line is positive. -/
theorem gaussianDistanceMatrix_crossMinor_pos {m : ℕ} (t : ℝ) (x : Fin n ↪o ℝ)
    (r c : Fin m ↪o Fin n) :
    0 < ((gaussianDistanceMatrix (x : Fin n → ℝ) (Real.exp t)).submatrix r c).det := by
  simpa only [gaussianDistanceMatrix, submatrix, Real.norm_eq_abs, sq_abs,
    gaussianCollocation, of_apply, RelEmbedding.coe_trans, Function.comp_apply] using
    gaussianCollocation_det_pos t (r.trans x) (c.trans x)

/-- Gaussian interpolation on two ordered grids has a unique solution for every data vector. -/
theorem gaussianCollocation_interpolates (t : ℝ) (x y : Fin n ↪o ℝ) (v : Fin n → ℝ) :
    ∃! w, (gaussianCollocation t x y).mulVec w = v := by
  let M := gaussianCollocation t x y
  have hu : IsUnit M.det := (gaussianCollocation_det_pos t x y).ne'.isUnit
  refine ⟨M⁻¹.mulVec v, ?_, ?_⟩
  · change M.mulVec (M⁻¹.mulVec v) = v
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  · intro w hw
    change M.mulVec w = v at hw
    rw [← hw, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]

/-- The signed entries of the inverse are strictly positive, including off-diagonal entries. -/
theorem gaussianCollocation_inverse_checkerboard (t : ℝ) (x y : Fin (n+1) ↪o ℝ)
    (i j : Fin (n+1)) :
    0 < (-1 : ℝ) ^ (j.val + i.val) * (gaussianCollocation t x y)⁻¹ i j := by
  let M := gaussianCollocation t x y
  have hdet := gaussianCollocation_det_pos t x y
  have hminor : 0 < (M.submatrix j.succAbove i.succAbove).det :=
    gaussianCollocation_det_pos t
      ((Fin.succAboveOrderEmb j).trans x) ((Fin.succAboveOrderEmb i).trans y)
  change 0 < (-1 : ℝ) ^ (j.val + i.val) * M⁻¹ i j
  rw [inv_def, smul_apply, smul_eq_mul, adjugate_fin_succ_eq_det_submatrix]
  have hs : (-1 : ℝ) ^ (j.val + i.val) * (-1 : ℝ) ^ (j.val + i.val) = 1 := by
    rw [← mul_pow]
    simp
  calc
    0 < M.det⁻¹ * (M.submatrix j.succAbove i.succAbove).det :=
      mul_pos (inv_pos.mpr hdet) hminor
    _ = _ := by
      rw [Ring.inverse_eq_inv]
      linear_combination -(M.det⁻¹ * (M.submatrix j.succAbove i.succAbove).det) * hs

/-- On an arithmetic progression of centers the residual determinant is Vandermonde.
The identity also covers collisions and a negative mesh. -/
theorem gaussianCollocation_progression_det (t b h : ℝ) (x : Fin n → ℝ) :
    (gaussianCollocation t x (fun j => b + h * j.val)).det =
      (∏ i, Real.exp (-Real.exp t * x i ^ 2)) *
      ((∏ j : Fin n, Real.exp (-Real.exp t * (b + h * j.val) ^ 2)) *
      ((∏ i, Real.exp (2 * Real.exp t * x i * b)) *
      ∏ i : Fin n, ∏ j ∈ Ioi i,
        (Real.exp (2 * Real.exp t * x j * h) - Real.exp (2 * Real.exp t * x i * h)))) := by
  let z := fun i => Real.exp (2 * Real.exp t * x i * h)
  have hm : expNodeMatrix (fun i => 2 * Real.exp t * x i) (fun j => b + h * j.val) =
      of (fun i j => Real.exp (2 * Real.exp t * x i * b) * vandermonde z i j) := by
    ext i j
    simp only [expNodeMatrix, of_apply, vandermonde_apply, z, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [det_gaussianCollocation, hm, det_mul_column, det_vandermonde]

/-- A mixture of distinct Gaussian translates with nonzero amplitudes has
at most one fewer distinct real zeros than centers. -/
theorem gaussianTranslate_zero_bound (t : ℝ) (y : Fin (n+1) ↪o ℝ)
    (c : Fin (n+1) → ℝˣ) (Z : Finset ℝ) :
    (Z.filter fun x => (∑ i, (c i : ℝ) * Real.exp (-Real.exp t * (x - y i)^2)) = 0).card ≤ n := by
  classical
  let a := fun i => 2 * Real.exp t * y i
  let d := fun i => (c i : ℝ) * Real.exp (-Real.exp t * y i ^ 2)
  let S := Z.filter fun x => (∑ i, (c i : ℝ) * Real.exp (-Real.exp t * (x - y i)^2)) = 0
  have hzero (x : ℝ) (hx : x ∈ S) : expSum d a x = 0 := by
    have hz := (mem_filter.mp hx).2
    have he : Real.exp (-Real.exp t * x ^ 2) * expSum d a x =
        ∑ i, (c i : ℝ) * Real.exp (-Real.exp t * (x - y i)^2) := by
      rw [expSum, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [gaussian_factor]
      simp only [a, d]
      rw [show 2 * Real.exp t * y i * x = 2 * Real.exp t * x * y i by ring]
      ring
    exact (mul_eq_zero.mp (he.trans hz)).resolve_left (Real.exp_pos _).ne'
  have h := card_zeros_le_expSum (Nat.succ_pos n) d a
    (fun _ _ hij => mul_lt_mul_of_pos_left (y.strictMono hij) (by positivity))
    (fun i => mul_ne_zero (c i).ne_zero (Real.exp_pos _).ne') S hzero
  change S.card ≤ n
  omega

end
end GaloisForLFunctions.HilbertMetric
