import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# QNMAnchorNormalization

The affine anchor in Ferrer-Sánchez et al., arXiv:2608.19774, equation (3.4),
parametrizes precisely the functions taking value one at the anchor. Its action on
a linear equation has an explicit constant-mode residual defect.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

def qnmAnchor {X : Type*} (p : X) (f : X → ℂ) : X → ℂ :=
  fun x => 1 + f x - f p

theorem qnmAnchor_at {X : Type*} (p : X) (f : X → ℂ) : qnmAnchor p f p = 1 := by
  simp [qnmAnchor]

theorem range_qnmAnchor {X : Type*} (p : X) :
    Set.range (qnmAnchor p) = {f : X → ℂ | f p = 1} := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact qnmAnchor_at p g
  · intro hf
    change f p = 1 at hf
    refine ⟨f, ?_⟩
    funext x
    simp [qnmAnchor, hf]

theorem qnmAnchor_idempotent {X : Type*} (p : X) (f : X → ℂ) :
    qnmAnchor p (qnmAnchor p f) = qnmAnchor p f := by
  funext x
  simp [qnmAnchor]

theorem qnmAnchor_add_constant {X : Type*} (p : X) (f : X → ℂ) (c : ℂ) :
    qnmAnchor p (fun x => f x + c) = qnmAnchor p f := by
  funext x
  simp only [qnmAnchor]
  ring

theorem qnmAnchor_linear_residual {X V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : (X → ℂ) →ₗ[ℂ] V) (p : X) (f : X → ℂ) :
    L (qnmAnchor p f) = L f + (1 - f p) • L (fun _ => 1) := by
  have h : qnmAnchor p f = f + (1 - f p) • (fun _ => (1 : ℂ)) := by
    funext x
    simp only [qnmAnchor, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    ring
  rw [h, map_add, map_smul]

theorem qnmAnchor_ne_zero {X : Type*} (p : X) (f : X → ℂ) :
    qnmAnchor p f ≠ 0 := by
  intro h
  have hx := congrFun h p
  rw [qnmAnchor_at] at hx
  exact one_ne_zero hx

def qnmPolynomialAnchor (p : ℂ) (f : Polynomial ℂ) : Polynomial ℂ :=
  f + Polynomial.C (1 - f.eval p)

theorem eval_qnmPolynomialAnchor (p x : ℂ) (f : Polynomial ℂ) :
    (qnmPolynomialAnchor p f).eval x = qnmAnchor p (fun y => f.eval y) x := by
  simp only [qnmPolynomialAnchor, Polynomial.eval_add, Polynomial.eval_C, qnmAnchor]
  ring

theorem derivative_qnmPolynomialAnchor (p : ℂ) (f : Polynomial ℂ) :
    (qnmPolynomialAnchor p f).derivative = f.derivative := by
  simp [qnmPolynomialAnchor]

theorem qnmPolynomialAnchor_residual (p z : ℂ) (f : Polynomial ℂ) :
    (qnmPolynomialAnchor p f).derivative.derivative -
        Polynomial.C z * qnmPolynomialAnchor p f =
      f.derivative.derivative - Polynomial.C z * f - Polynomial.C (z * (1 - f.eval p)) := by
  simp [qnmPolynomialAnchor, mul_add, sub_add_eq_sub_sub]

end GaloisForLFunctions.HTGeometry
