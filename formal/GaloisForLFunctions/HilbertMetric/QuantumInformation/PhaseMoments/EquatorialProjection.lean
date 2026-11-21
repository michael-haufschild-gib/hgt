import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Equatorial decomposition of a qubit with its Pauli Z component erased

A trace-one qubit density matrix has twice its off-diagonal entry in
the closed unit disk. Equation (4) of Qian and Zhang (arXiv:2611.24473)
erases the difference of the diagonal entries. Two unit phases with
the given midpoint give an equal mixture of equatorial states.
-/

open Metric
open scoped BigOperators Matrix ComplexOrder

namespace GaloisForLFunctions.HilbertMetric.PhaseMoments

noncomputable section

private theorem exists_unitPhase_mul_norm (z : ℂ) :
    ∃ u : Circle, (u : ℂ) * (‖z‖ : ℂ) = z := by
  by_cases hz : z = 0
  · exact ⟨1, by simp [hz]⟩
  · have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    let u := z / (‖z‖ : ℂ)
    have hu : ‖u‖ = 1 := by
      rw [show u = z / (‖z‖ : ℂ) from rfl, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), div_self hr]
    refine ⟨⟨u, mem_sphere_zero_iff_norm.mpr hu⟩, ?_⟩
    exact div_mul_cancel₀ z (Complex.ofReal_ne_zero.mpr hr)

/-- Every point of the closed unit disk is a midpoint of two unit phases. -/
theorem exists_circle_midpoint (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∃ u v : Circle, ((u : ℂ) + v) / 2 = z := by
  obtain ⟨u, hu⟩ := exists_unitPhase_mul_norm z
  have hr : 0 ≤ 1 - ‖z‖ ^ 2 := sub_nonneg.mpr
    ((sq_le_sq₀ (norm_nonneg z) zero_le_one).mpr hz |>.trans_eq (one_pow 2))
  let s := Real.sqrt (1 - ‖z‖ ^ 2)
  have hs : s ^ 2 = 1 - ‖z‖ ^ 2 := Real.sq_sqrt hr
  let w : ℂ := (‖z‖ : ℂ) + (s : ℂ) * Complex.I
  have hw_re : w.re = ‖z‖ := by simp [w, Complex.mul_re]
  have hw_im : w.im = s := by simp [w, Complex.mul_im]
  have hw_sq : ‖w‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hw_re, hw_im, ← pow_two, ← pow_two, hs]
    ring
  have hw : ‖w‖ = 1 := (mul_self_inj (norm_nonneg w) zero_le_one).mp (by
    simpa only [pow_two, mul_one] using hw_sq)
  let v : Circle := ⟨w, mem_sphere_zero_iff_norm.mpr hw⟩
  refine ⟨u * v, u * v⁻¹, ?_⟩
  rw [Circle.coe_mul, Circle.coe_mul, Circle.coe_inv_eq_conj, ← mul_add, mul_div_assoc]
  have havg : (w + star w) / 2 = (‖z‖ : ℂ) := by
    rw [Complex.star_def, Complex.add_conj, hw_re, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  change (u : ℂ) * ((w + star w) / 2) = z
  rw [havg, hu]

/-- The affine disk of matrices with fixed diagonal half and off-diagonal z/2. -/
def equatorialDisk (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / 2, star z / 2; z / 2, 1 / 2]

/-- At a unit phase the disk matrix is a rank-one equatorial projector. -/
theorem equatorialDisk_eq_outer (z : Circle) :
    ∃ v : Fin 2 → ℂ, (∀ i, ‖v i‖ ^ 2 = 1 / 2) ∧
      equatorialDisk z = Matrix.vecMulVec v (star v) := by
  let v : Fin 2 → ℂ := ![1, (z : ℂ)] / (fun _ => (Real.sqrt 2 : ℂ))
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity : 0 ≤ (2 : ℝ))]
    exact Complex.ofReal_ofNat 2
  have hsR : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have hsC : star (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) :=
    Complex.conj_ofReal _
  have hz : (z : ℂ) * (starRingEnd ℂ) (z : ℂ) = 1 := by
    rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  refine ⟨v, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [v, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), hsR]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [equatorialDisk, Matrix.vecMulVec, v, star_div₀, hsC, div_mul_div_comm, hs, hz]

/-- The map that keeps the trace and off-diagonal entries and erases the
Pauli Z coefficient. -/
def erasePauliZ (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then A.trace / 2 else A i j

/-- Positivity bounds the off-diagonal magnitude by half the trace. -/
theorem twice_norm_qubit_offDiagonal_le_trace {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosSemidef) :
    2 * ‖A 1 0‖ ≤ A.trace.re := by
  have hdiag (i : Fin 2) : 0 ≤ (A i i).re ∧ 0 = (A i i).im :=
    Complex.nonneg_iff.mp hA.diag_nonneg
  have hreal (i : Fin 2) : ((A i i).re : ℂ) = A i i :=
    Complex.ext (Complex.ofReal_re _) (hdiag i).2
  have hdet : A.det = (((A 0 0).re * (A 1 1).re - ‖A 1 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two, ← hA.isHermitian.apply 0 1, mul_comm (star (A 1 0)),
      Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, ← hreal 0, ← hreal 1,
      Complex.ofReal_sub, Complex.ofReal_mul]
    simp only [Complex.ofReal_re]
  have hd := (Complex.nonneg_iff.mp hA.det_nonneg).1
  rw [hdet, Complex.ofReal_re] at hd
  rw [Matrix.trace_fin_two, Complex.add_re]
  apply (sq_le_sq₀ (by positivity) (add_nonneg (hdiag 0).1 (hdiag 1).1)).mp
  nlinarith only [hd, sq_nonneg ((A 0 0).re - (A 1 1).re)]

private theorem equatorialDisk_midpoint (x y : ℂ) :
    equatorialDisk ((x + y) / 2) =
      (2 : ℂ)⁻¹ • (equatorialDisk x + equatorialDisk y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [equatorialDisk, Matrix.smul_apply, star_div₀, star_add] <;> ring

/-- Erasing the Pauli Z component of any qubit density matrix gives the
equal mixture of two rank-one equatorial projectors. -/
theorem erasePauliZ_eq_midpoint {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosSemidef) (ht : A.trace = 1) :
    ∃ u v : Circle,
      erasePauliZ A = (2 : ℂ)⁻¹ • (equatorialDisk u + equatorialDisk v) := by
  have hb := twice_norm_qubit_offDiagonal_le_trace hA
  rw [ht, Complex.one_re] at hb
  have hn : ‖(2 : ℂ) * A 1 0‖ ≤ 1 := by simpa [norm_mul] using hb
  obtain ⟨u, v, huv⟩ := exists_circle_midpoint _ hn
  refine ⟨u, v, ?_⟩
  rw [← equatorialDisk_midpoint, huv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [erasePauliZ, equatorialDisk, ht, star_mul, hA.isHermitian.apply 0 1]

/-- Independently erasing Z on each site of a product state gives a
uniform mixture of equatorial product states, with at most two choices per site. -/
theorem exists_equatorial_product_mixture {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (hA : ∀ i, (A i).PosSemidef)
    (ht : ∀ i, (A i).trace = 1) :
    ∃ phase : (ι → Bool) → ι → Circle, ∀ x y : ι → Fin 2,
      (∏ i, erasePauliZ (A i) (x i) (y i)) =
        ((2 : ℂ) ^ Fintype.card ι)⁻¹ * ∑ b, ∏ i, equatorialDisk (phase b i) (x i) (y i) := by
  choose u v hv using fun i => erasePauliZ_eq_midpoint (hA i) (ht i)
  let z (i : ι) (b : Bool) : Circle := if b then u i else v i
  refine ⟨fun b i => z i (b i), fun x y => ?_⟩
  have hi (i : ι) : erasePauliZ (A i) (x i) (y i) =
      ∑ b : Bool, (2 : ℂ)⁻¹ * equatorialDisk (z i b) (x i) (y i) := by
    rw [hv i, Fintype.sum_bool]
    simp [z, Matrix.smul_apply, mul_add]
  simp_rw [hi]
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, inv_pow]

/-- Pauli Z erasure is positive on the single-qubit cone by averaging the
matrix with its transposed and relabelled copy. -/
theorem erasePauliZ_posSemidef {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) :
    (erasePauliZ A).PosSemidef := by
  let flip (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0
  have he : erasePauliZ A = (1 / 2 : ℝ) • (A + A.transpose.submatrix flip flip) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [erasePauliZ, flip, Matrix.trace_fin_two, Matrix.smul_apply, Complex.real_smul] <;> ring
  rw [he]
  exact (hA.add (hA.transpose.submatrix flip)).smul (by positivity)

/-- Apply Pauli Z erasure to the qubit while leaving an arbitrary finite
second register as the matrix-valued coefficients. -/
def erasePauliZLeft {ι : Type*} (A : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) :
    Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ :=
  fun p q => if p.1 = q.1 then (A (0, p.2) (0, q.2) + A (1, p.2) (1, q.2)) / 2 else A p q

/-- The extension acts as Pauli Z erasure tensored with the identity. -/
theorem erasePauliZLeft_apply_product {ι : Type*} (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix ι ι ℂ) (p q : Fin 2 × ι) :
    erasePauliZLeft (fun r s => A r.1 s.1 * B r.2 s.2) p q =
      erasePauliZ A p.1 q.1 * B p.2 q.2 := by
  by_cases h : p.1 = q.1
  · simp only [erasePauliZLeft, erasePauliZ, if_pos h, Matrix.trace_fin_two]
    ring
  · simp only [erasePauliZLeft, erasePauliZ, if_neg h]

/-- One retained auxiliary qubit suffices to disprove complete positivity.
The Bell projector acquires a negative expectation on the opposite Bell vector. -/
theorem erasePauliZLeft_not_positive :
    ∃ A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      A.PosSemidef ∧ ¬ (erasePauliZLeft A).PosSemidef := by
  let v : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else 0
  refine ⟨Matrix.vecMulVec v (star v), Matrix.posSemidef_vecMulVec_self_star v, fun h => ?_⟩
  let a : Fin 2 × Fin 2 := (0, 0)
  let b : Fin 2 × Fin 2 := (1, 1)
  let w : Fin 2 × Fin 2 → ℂ := Pi.single a 1 - Pi.single b 1
  have hfour (B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      star w ⬝ᵥ (B *ᵥ w) = B a a + B b b - B a b - B b a := by
    simp only [w, star_sub, Pi.star_single, star_one, Matrix.mulVec_sub,
      sub_dotProduct, dotProduct_sub, single_dotProduct, one_mul,
      Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply]
    ring
  have hneg := (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg w)).1
  rw [hfour] at hneg
  norm_num [erasePauliZLeft, a, b, Matrix.vecMulVec, v] at hneg

#print axioms exists_circle_midpoint
#print axioms equatorialDisk_eq_outer
#print axioms erasePauliZ_eq_midpoint
#print axioms exists_equatorial_product_mixture
#print axioms erasePauliZ_posSemidef
#print axioms erasePauliZLeft_not_positive

end

end GaloisForLFunctions.HilbertMetric.PhaseMoments
