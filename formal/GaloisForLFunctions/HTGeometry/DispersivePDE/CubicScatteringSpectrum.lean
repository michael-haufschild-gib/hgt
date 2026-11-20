import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringTau
import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDisplacementSpectrum
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Negative simple zeros of the positive cubic scattering polynomial

Splitting each exponential amplitude equally between the row and column
turns the wave matrix into a symmetric inverse Jordan response. Its nonzero
eigenvalues are positive and simple. The entire Hirota subset polynomial
therefore factors over the reals, also at coincident momenta.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScattering
open Finset Matrix Polynomial Unitary
open GaloisForLFunctions.HilbertMetric.CauchyDephasing
open GaloisForLFunctions.HilbertMetric.CauchyJordan
open GaloisForLFunctions.HilbertMetric.CauchySpectrum
variable {n : ℕ}

private def amplitude (r a : Fin n → ℝ) (i : Fin n) := Real.exp (a i/2)*Real.exp (r i/2)

/-- The levels of the symmetric Cauchy realization, including the zero modes
forced by repeated momenta. -/
def levels (r a : Fin n → ℝ) := (response_hermitian r (amplitude r a)).eigenvalues

private theorem half_exp (a : ℝ) : Real.exp (a/2)*Real.exp (a/2) = Real.exp a := by
  rw [← Real.exp_add,add_halves]

private theorem symmetric_evaluation (r a : Fin n → ℝ) (x : ℝ) :
    (1+x • waveMatrix r a).det = (1+x • response r (amplitude r a)).det := by
  let D := diagonal fun i : Fin n => Real.exp (a i/2)
  let M := of fun i j => Real.exp (a i/2)*coherence (r i) (r j)
  have hw : D*M=waveMatrix r a := by
    ext i j
    simp only [D,M,diagonal_mul,of_apply,waveMatrix,← mul_assoc,half_exp]
  have hs : M*D=response r (amplitude r a) := by
    ext i j
    simp only [D,M,mul_diagonal,of_apply,coherence,response,rate,amplitude]
    ring
  rw [← hw,← hs,← Matrix.smul_mul,det_one_add_mul_comm,Matrix.mul_smul]

private theorem evaluate_tau (r a : Fin n → ℝ) (x : ℝ) :
    (tauPolynomial r a).eval x = (1+x • waveMatrix r a).det := by
  change (evalRingHom x) (det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i=j <;> simp [RingHom.mapMatrix_apply,hij,mul_comm x]

private theorem spectral_det {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) (x : ℝ) :
    (1+x • M).det = ∏ i, (1+x*hM.eigenvalues i) := by
  let A := conjStarAlgAut ℝ _ hM.eigenvectorUnitary
  have hme : M = A (diagonal hM.eigenvalues) := by
    simpa only [RCLike.ofReal_real_eq_id,Function.id_comp] using hM.spectral_theorem
  have he : 1+x • M = A (diagonal (fun i => 1+x*hM.eigenvalues i)) := by
    rw [show diagonal (fun i => 1+x*hM.eigenvalues i) = 1+x • diagonal hM.eigenvalues by
      ext i j; by_cases hij : i=j <;> simp [hij,Matrix.one_apply],map_add,map_one,map_smul,← hme]
  rw [he]
  dsimp only [A,Unitary.conjStarAlgAut_apply]
  rw [Matrix.det_mul_comm,← Matrix.mul_assoc,Unitary.coe_star_mul_self,one_mul,Matrix.det_diagonal]

private def factor (level : ℝ) : ℝ[X] := 1+C level*X

/-- Exact real linear factorization of the Hirota subset polynomial. -/
theorem tau_spectral_product (r a : Fin n → ℝ) :
    tauPolynomial r a = ∏ i, (1+C (levels r a i)*X) := by
  apply Polynomial.funext
  intro x
  rw [evaluate_tau,symmetric_evaluation,spectral_det (response_hermitian r _)]
  simp only [Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,levels,mul_comm x]

private theorem characteristic_root (r a : Fin n → ℝ) (x : ℝ) :
    (tauPolynomial r a).IsRoot x ↔ ∃ i, 0 < levels r a i ∧ x = -(levels r a i)⁻¹ := by
  simp only [Polynomial.IsRoot,tau_spectral_product,Polynomial.eval_prod,Polynomial.eval_add,
    Polynomial.eval_one,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Finset.prod_eq_zero_iff,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    have hn : levels r a i ≠ 0 := by intro hz; rw [hz,zero_mul,add_zero] at hi; exact one_ne_zero hi
    refine ⟨i,lt_of_le_of_ne (levels_nonnegative r _ i) hn.symm,?_⟩
    field_simp [hn]
    linarith only [hi]
  · rintro ⟨i,hi,rfl⟩
    exact ⟨i,by rw [mul_neg,mul_inv_cancel₀ hi.ne',add_neg_cancel]⟩

/-- Each real root is the negative reciprocal of a unique positive level.
The eigenspace simplicity also rules out any repeated polynomial root. -/
theorem tau_root_simple (r a : Fin n → ℝ) (x : ℝ) :
    (tauPolynomial r a).IsRoot x → x<0 ∧ (tauPolynomial r a).derivative.eval x ≠ 0 := by
  classical
  intro hx
  obtain ⟨i,hi,rfl⟩ := (characteristic_root r a x).mp hx
  let level := levels r a i
  have hlevel : level ≠ 0 := hi.ne'
  have hroot : (factor level).eval (-level⁻¹) = 0 := by simp [factor,hlevel]
  let P := ∏ j ∈ univ.erase i, factor (levels r a j)
  have hP : P.eval (-level⁻¹) ≠ 0 := by
    rw [show P = ∏ j ∈ univ.erase i, factor (levels r a j) from rfl,Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj hzero
    have he : levels r a j=level := by
      simp only [factor,eval_add,eval_one,eval_mul,eval_C,eval_X] at hzero
      field_simp [hlevel] at hzero
      linarith only [hzero]
    exact ((spectral_collision r (amplitude r a) j i he).resolve_right hi.ne') |> (Finset.ne_of_mem_erase hj)
  have hf : tauPolynomial r a = P*factor level := by
    rw [tau_spectral_product]
    exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  refine ⟨neg_neg_of_pos (inv_pos.mpr hi),?_⟩
  rw [hf,Polynomial.derivative_mul,eval_add,eval_mul,eval_mul,hroot,mul_zero,zero_add]
  simpa [factor] using mul_ne_zero hP hlevel

end GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScattering
