import GaloisForLFunctions.HTGeometry.RegularLevelSetStratification
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem contDiff_mvPolynomial_eval_real {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ⊤ (fun x : Fin n → ℝ => MvPolynomial.eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (contDiff_const : ContDiff ℝ ⊤ (fun _ : Fin n → ℝ => c))
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P i hP =>
      simpa using hP.mul (contDiff_apply ℝ ℝ i)

theorem contDiff_mvPolynomial_eval_complex_real {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) :
    ContDiff ℝ ⊤ (fun x : Fin n → ℂ => MvPolynomial.eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (contDiff_const : ContDiff ℝ ⊤ (fun _ : Fin n → ℂ => c))
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P i hP =>
      simpa using hP.mul (contDiff_apply ℝ ℂ i)

theorem hasDerivAt_mvPolynomial_eval_curve_complex {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ)
    (g : Fin n → ℂ → ℂ) (g' : Fin n → ℂ) (x : ℂ)
    (hg : ∀ j, HasDerivAt (g j) (g' j) x) :
    HasDerivAt (fun s => MvPolynomial.eval (fun j => g j s) P)
      (∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j P) * g' j) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hcf : (fun s => MvPolynomial.eval (fun j => g j s) (MvPolynomial.C a)) =
          fun _ => a := by
        funext s
        simp
      rw [hcf]
      simp only [MvPolynomial.pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
      exact hasDerivAt_const x a
  | add p q hp hq =>
      have hf : (fun s => MvPolynomial.eval (fun j => g j s) (p + q)) =
          fun s => MvPolynomial.eval (fun j => g j s) p +
            MvPolynomial.eval (fun j => g j s) q := by
        funext s
        simp
      rw [hf]
      convert! hp.add hq using 1 <;>
        simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
      have hfun : (fun s => MvPolynomial.eval (fun j => g j s) (p * MvPolynomial.X i)) =
          fun s => MvPolynomial.eval (fun j => g j s) p * g i s := by
        funext s
        simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [hfun]
      convert! hp.mul (hg i) using 1 <;>
        simp only [MvPolynomial.pderiv_mul, map_add, MvPolynomial.eval_mul,
          MvPolynomial.eval_X, MvPolynomial.pderiv_X, Pi.single_apply, mul_ite,
          mul_one, mul_zero, add_mul, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      · rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · intro h
          simp at h

theorem surjective_fderiv_mvPolynomial_eval_complex_real_of_pderiv_ne_zero
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (i : Fin n)
    (hi : MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0) :
    Function.Surjective (fderiv ℝ (fun y : Fin n → ℂ => MvPolynomial.eval y P) x) := by
  let curve : ℂ → (Fin n → ℂ) := fun t => Function.update x i t
  have hcurveCoord : ∀ j, HasDerivAt (fun t => curve t j) (if j = i then 1 else 0) (x i) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [curve] using! (hasDerivAt_id (x i))
    · simpa [curve, hji] using (hasDerivAt_const (x i) (x j))
  have hcurveValue : curve (x i) = x := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [curve]
    · simp [curve, hji]
  have hslice : HasDerivAt
      (fun t => MvPolynomial.eval (curve t) P)
      (MvPolynomial.eval x (MvPolynomial.pderiv i P)) (x i) := by
    have h := hasDerivAt_mvPolynomial_eval_curve_complex P
      (fun j t => curve t j) (fun j => if j = i then 1 else 0) (x i) hcurveCoord
    change HasDerivAt (fun t => MvPolynomial.eval (curve t) P)
      (∑ j, MvPolynomial.eval (curve (x i)) (MvPolynomial.pderiv j P) *
        (if j = i then 1 else 0)) (x i) at h
    rw [hcurveValue] at h
    convert h using 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi'
      exact (hi' (Finset.mem_univ i)).elim
  have hsliceReal := hslice.hasFDerivAt.restrictScalars ℝ
  have hsliceSurj : Function.Surjective
      (fderiv ℝ (fun t => MvPolynomial.eval (curve t) P) (x i)) := by
    rw [hsliceReal.fderiv]
    intro y
    refine ⟨y / MvPolynomial.eval x (MvPolynomial.pderiv i P), ?_⟩
    change y / MvPolynomial.eval x (MvPolynomial.pderiv i P) *
        MvPolynomial.eval x (MvPolynomial.pderiv i P) = y
    exact div_mul_cancel₀ y hi
  have hFdiff : DifferentiableAt ℝ
      (fun y : Fin n → ℂ => MvPolynomial.eval y P) (curve (x i)) :=
    (contDiff_mvPolynomial_eval_complex_real P).differentiable (by simp) |>.differentiableAt
  have hcurveDiff : DifferentiableAt ℝ curve (x i) := by
    exact differentiableAt_pi.mpr fun j => (hcurveCoord j).hasFDerivAt.restrictScalars ℝ |>.differentiableAt
  have hcomp := fderiv_fun_comp (f := curve)
    (g := fun y : Fin n → ℂ => MvPolynomial.eval y P) (x i) hFdiff hcurveDiff
  rw [hcurveValue] at hcomp
  intro y
  obtain ⟨t, ht⟩ := hsliceSurj y
  refine ⟨fderiv ℝ curve (x i) t, ?_⟩
  have ht' := ht
  rw [hcomp] at ht'
  exact ht'

def complexMvPolynomialRegularZeroLocus {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) : Set (Fin n → ℂ) :=
  {x | MvPolynomial.eval x P = 0 ∧
    ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0}

theorem isOpen_exists_mvPolynomial_pderiv_eval_ne_zero_complex {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) :
    IsOpen {x : Fin n → ℂ |
      ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0} := by
  rw [show {x : Fin n → ℂ |
      ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0} =
      ⋃ i, {x | MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0} by
    ext x
    simp]
  apply isOpen_iUnion
  intro i
  exact isOpen_compl_singleton.preimage
    (contDiff_mvPolynomial_eval_complex_real (MvPolynomial.pderiv i P)).continuous

theorem complexMvPolynomialRegularZeroLocus_isLocalRegularLevelSetOfCodimAtLeast_two
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    IsLocalRegularLevelSetOfCodimAtLeast
      (complexMvPolynomialRegularZeroLocus P) 2 := by
  let O : Set (Fin n → ℂ) :=
    {x | ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0}
  have hO : IsOpen O := isOpen_exists_mvPolynomial_pderiv_eval_ne_zero_complex P
  have hsurj : ∀ x, MvPolynomial.eval x P = 0 → x ∈ O →
      Function.Surjective
        (fderiv ℝ (fun y : Fin n → ℂ => MvPolynomial.eval y P) x) := by
    intro x _ hxO
    obtain ⟨i, hi⟩ := hxO
    exact surjective_fderiv_mvPolynomial_eval_complex_real_of_pderiv_ne_zero P x i hi
  have hreg :=
    isLocalRegularLevelSetOfCodimAtLeast_zeroSet_inter_isOpen_finiteDimensional
      (fun y : Fin n → ℂ => MvPolynomial.eval y P)
      (by rw [Complex.finrank_real_complex])
      (contDiff_mvPolynomial_eval_complex_real P) hO hsurj
  simpa [complexMvPolynomialRegularZeroLocus, O] using! hreg

def complexMvPolynomialFamilyEval {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin m → ℂ :=
  fun j => MvPolynomial.eval x (P j)

theorem contDiff_complexMvPolynomialFamilyEval_real {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) :
    ContDiff ℝ ⊤ (complexMvPolynomialFamilyEval P) := by
  apply contDiff_pi'
  intro j
  exact contDiff_mvPolynomial_eval_complex_real (P j)

def complexMvPolynomialFamilyRegularZeroLocus {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) : Set (Fin n → ℂ) :=
  {x | complexMvPolynomialFamilyEval P x = 0 ∧
    Function.Surjective (fderiv ℝ (complexMvPolynomialFamilyEval P) x)}

theorem complexMvPolynomialFamilyRegularZeroLocus_isLocalRegularLevelSetOfCodimAtLeast
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) :
    IsLocalRegularLevelSetOfCodimAtLeast
      (complexMvPolynomialFamilyRegularZeroLocus P) (2 * m) := by
  let F : (Fin n → ℂ) → (Fin m → ℂ) := complexMvPolynomialFamilyEval P
  let O : Set (Fin n → ℂ) := {x | Function.Surjective (fderiv ℝ F x)}
  have hF : ContDiff ℝ ⊤ F := contDiff_complexMvPolynomialFamilyEval_real P
  have hO : IsOpen O :=
    isOpen_surjectiveContinuousLinearMapLocus.preimage
      (hF.continuous_fderiv (by simp))
  have hsurj : ∀ x, F x = 0 → x ∈ O →
      Function.Surjective (fderiv ℝ F x) := by
    intro x _ hx
    exact hx
  have hcodim : 2 * m ≤ Module.finrank ℝ (Fin m → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]
  have hreg :=
    isLocalRegularLevelSetOfCodimAtLeast_zeroSet_inter_isOpen_finiteDimensional
      F hcodim hF hO hsurj
  simpa [complexMvPolynomialFamilyRegularZeroLocus, F, O] using! hreg

end

end GaloisForLFunctions.HTGeometry
