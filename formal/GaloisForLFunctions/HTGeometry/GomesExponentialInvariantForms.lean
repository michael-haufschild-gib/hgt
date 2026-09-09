import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix

/-!
# Real and complex exponential invariant forms

The representation-category distinction in Gomes, arXiv:2607.24901, leads to a sharp
infinitesimal classification. A real exponential preserves a sesquilinear form exactly
when its generator is skew-adjoint relative to that form. Requiring all complex parameters
forces separate left and right annihilation, so every nonzero generator loses every
nondegenerate invariant form. No nilpotence or positivity is assumed.
-/

open scoped Matrix Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GaloisForLFunctions.HTGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real exponential invariance is exactly the infinitesimal skew-adjoint relation relative
to the chosen, possibly degenerate and non-Hermitian, form. -/
theorem real_exponential_sesquilinear_invariants
    (D H : Matrix n n ℂ) :
    (∀ t : ℝ, star (NormedSpace.exp (t • D)) * H * NormedSpace.exp (t • D) = H) ↔
      star D * H + H * D = 0 := by
  constructor
  · intro h
    have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • D)) D 0 := by
      simpa using hasDerivAt_exp_smul_const D (0 : ℝ)
    have hp := (hd.star.mul_const H).mul hd
    have hf : (fun t : ℝ => star (NormedSpace.exp (t • D)) * H *
        NormedSpace.exp (t • D)) = fun _ => H := funext h
    simp only [Pi.mul_def] at hp
    rw [hf] at hp
    simpa using hp.unique (hasDerivAt_const (0 : ℝ) H)
  · intro h t
    have hs : SemiconjBy H (t • D) (-(t • star D)) := by
      change H * (t • D) = (-(t • star D)) * H
      rw [Matrix.mul_smul,neg_mul,Matrix.smul_mul,← smul_neg]
      congr 1
      exact eq_neg_of_add_eq_zero_left (add_comm (star D * H) (H * D) ▸ h)
    have he := hs.exp_right
    change H * NormedSpace.exp (t • D) = NormedSpace.exp (-(t • star D)) * H at he
    rw [NormedSpace.star_exp,star_smul,star_trivial,mul_assoc,he,← mul_assoc,
      ← NormedSpace.exp_add_of_commute (Commute.refl (t • star D)).neg_right,
      add_neg_cancel,NormedSpace.exp_zero,one_mul]

/-- Allowing every complex parameter forces separate left and right annihilation of the form.
No Hermitian, positivity, invertibility, or nilpotence assumption is required. -/
theorem complex_exponential_sesquilinear_invariants
    (D H : Matrix n n ℂ) :
    (∀ z : ℂ, star (NormedSpace.exp (z • D)) * H * NormedSpace.exp (z • D) = H) ↔
      star D * H = 0 ∧ H * D = 0 := by
  constructor
  · intro h
    have hr := (real_exponential_sesquilinear_invariants D H).mp (fun t => by
      simpa only [Complex.coe_smul] using h (t : ℂ))
    have hi := (real_exponential_sesquilinear_invariants (Complex.I • D) H).mp (fun t => by
      simpa only [mul_smul,Complex.coe_smul] using h ((t : ℂ) * Complex.I))
    simp only [star_smul,Complex.star_def,Complex.conj_I,
      Matrix.smul_mul,Matrix.mul_smul] at hi
    constructor <;> ext i j
    · have hrij := congrFun (congrFun hr i) j
      have hiij := congrFun (congrFun hi i) j
      simp only [Matrix.add_apply,Matrix.zero_apply,Matrix.smul_apply,smul_eq_mul] at hrij hiij
      change (star D * H) i j = 0
      linear_combination (1 / 2 : ℂ) * hrij + (Complex.I / 2) * hiij +
        ((star D * H) i j - (H * D) i j) / 2 * Complex.I_sq
    · have hrij := congrFun (congrFun hr i) j
      have hiij := congrFun (congrFun hi i) j
      simp only [Matrix.add_apply,Matrix.zero_apply,Matrix.smul_apply,smul_eq_mul] at hrij hiij
      change (H * D) i j = 0
      linear_combination (1 / 2 : ℂ) * hrij - (Complex.I / 2) * hiij +
        ((H * D) i j - (star D * H) i j) / 2 * Complex.I_sq
  · rintro ⟨hl,hr⟩ z
    have hs : SemiconjBy H (z • D) 0 := by
      change H * (z • D) = 0 * H
      rw [Matrix.mul_smul,hr,smul_zero,zero_mul]
    have ht : SemiconjBy H 0 (star (z • D)) := by
      change H * 0 = star (z • D) * H
      rw [star_smul,Matrix.smul_mul,hl,smul_zero,mul_zero]
    have he : H * NormedSpace.exp (z • D) = H := by
      simpa only [SemiconjBy,NormedSpace.exp_zero,one_mul] using hs.exp_right
    have hf : star (NormedSpace.exp (z • D)) * H = H := by
      rw [NormedSpace.star_exp]
      simpa only [SemiconjBy,NormedSpace.exp_zero,mul_one] using ht.exp_right.symm
    rw [mul_assoc,he,hf]

/-- The usual real one-parameter unitary condition is exactly skew-adjointness. -/
theorem real_exponential_unitary_iff (D : Matrix n n ℂ) :
    (∀ t : ℝ, NormedSpace.exp (t • D) ∈ Matrix.unitaryGroup n ℂ) ↔ star D = -D := by
  have hf := real_exponential_sesquilinear_invariants D 1
  simp only [mul_one,one_mul] at hf
  constructor
  · intro h
    have hrel := hf.mp (fun t => Matrix.mem_unitaryGroup_iff'.mp (h t))
    exact eq_neg_of_add_eq_zero_left hrel
  · intro h t
    apply Matrix.mem_unitaryGroup_iff'.mpr
    exact hf.mpr (by rw [h,neg_add_cancel]) t

/-- A holomorphic exponential family is unitary for every complex parameter exactly when its
generator vanishes. This is stronger than requiring real-parameter unitarity. -/
theorem complex_exponential_unitary_iff (D : Matrix n n ℂ) :
    (∀ z : ℂ, NormedSpace.exp (z • D) ∈ Matrix.unitaryGroup n ℂ) ↔ D = 0 := by
  have hf := complex_exponential_sesquilinear_invariants D 1
  simp only [mul_one,one_mul] at hf
  constructor
  · intro h
    exact (hf.mp (fun z => Matrix.mem_unitaryGroup_iff'.mp (h z))).2
  · rintro rfl z
    simp [NormedSpace.exp_zero]

/-- Changing to any nondegenerate sesquilinear form cannot rescue a nonzero generator when all
complex translation parameters are required. -/
theorem complex_exponential_nondegenerate_form_iff (D : Matrix n n ℂ) :
    (∃ H : Matrix n n ℂ, IsUnit H ∧
      ∀ z : ℂ, star (NormedSpace.exp (z • D)) * H * NormedSpace.exp (z • D) = H) ↔ D = 0 := by
  constructor
  · rintro ⟨H,⟨u,rfl⟩,h⟩
    have hz := (complex_exponential_sesquilinear_invariants D (u : Matrix n n ℂ)).mp h
    have hc := congrArg (fun M => (↑(u⁻¹) : Matrix n n ℂ) * M) hz.2
    simpa only [← mul_assoc,Units.inv_mul,one_mul,mul_zero] using hc
  · rintro rfl
    exact ⟨1,isUnit_one,fun z => by simp [NormedSpace.exp_zero]⟩

end GaloisForLFunctions.HTGeometry
