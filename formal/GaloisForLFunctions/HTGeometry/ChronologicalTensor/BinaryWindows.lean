import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Sealing
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Binary homogenization by finite windows

Singleton and full windows realize each monomial in a homogeneous binary form.
Coefficient families recover arbitrary univariate polynomials on displacement-one
probes, and homogeneity gives their complete radial evaluation formula.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def binaryWindows : (d : ℕ) → Fin (d+1) → Fin d → Finset (Fin 2)
  | 0, _ => fun j => Fin.elim0 j
  | d+1, i => Fin.cases (fun _ => Finset.univ)
      (fun j => Fin.cons {0} (binaryWindows d j)) i

def binaryCoefficients (p : Polynomial ℝ) (d : ℕ) : Fin (d+1) → ℝ :=
  fun i => p.coeff i.val

theorem binaryWindows_value (d : ℕ) (i : Fin (d+1)) (g : Fin 2 → ℝ) :
    diagramValue (binaryWindows d i) g = (g 0)^i.val*(g 0+g 1)^(d-i.val) := by
  induction d with
  | zero =>
    simp [diagramValue]
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [binaryWindows,diagramValue,windowValue,Fin.sum_univ_two]
    · rw [diagramValue,Fin.prod_univ_succ]
      simp only [binaryWindows,Fin.cases_succ,Fin.cons_zero,Fin.cons_succ]
      change windowValue {0} g * diagramValue (binaryWindows d j) g = _
      rw [ih]
      simp only [windowValue,Finset.sum_singleton,Fin.val_succ,Nat.succ_sub_succ_eq_sub,pow_succ]
      ring

theorem binary_family_value (p : Polynomial ℝ) (d : ℕ) (g : Fin 2 → ℝ) :
    familyValue (binaryWindows d) (binaryCoefficients p d) g =
      ∑ i : Fin (d+1), p.coeff i.val*(g 0)^i.val*(g 0+g 1)^(d-i.val) := by
  simp only [familyValue,binaryCoefficients,binaryWindows_value,mul_assoc]

theorem binary_dehomogenize (p : Polynomial ℝ) (extra : ℕ) (x : ℝ) :
    familyValue (binaryWindows (p.natDegree+extra))
      (binaryCoefficients p (p.natDegree+extra)) ![x,1-x] = p.eval x := by
  rw [binary_family_value]
  simp only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [show x+(1-x)=1 by ring]
  simp only [one_pow,mul_one]
  rw [Polynomial.eval_eq_sum_range' (show p.natDegree < p.natDegree+extra+1 by omega),Finset.sum_range]

theorem binary_radial_value (p : Polynomial ℝ) (extra : ℕ) (x t : ℝ) :
    familyValue (binaryWindows (p.natDegree+extra))
      (binaryCoefficients p (p.natDegree+extra)) ![t*x,t*(1-x)] =
      t^(p.natDegree+extra)*p.eval x := by
  have he : (![t*x,t*(1-x)] : Fin 2 → ℝ) = fun i => t*(![x,1-x] : Fin 2 → ℝ) i := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      rfl
  rw [he,familyValue_scale,binary_dehomogenize]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
