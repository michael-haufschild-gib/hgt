import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnRepresentation
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Algebra of finite-rank group kernels

Finite-dimensional representation coefficients have finite column spaces. Finite rank is
preserved by sums, pointwise products, polynomial evaluation, and homomorphism pullback.
The proofs place the columns in finite-dimensional subspaces of the function algebra.
-/

open Module
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

private theorem finite_columnSpan_of_le {k : G → ℂ} (W : Submodule ℂ (G → ℂ))
    [Module.Finite ℂ W] (h : kernelColumnSpan k ≤ W) :
    Module.Finite ℂ (kernelColumnSpan k) := by
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  exact Module.Finite.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

/-- A finite family spanning every column makes the kernel finite rank. -/
theorem finite_columnSpan_of_features {k : G → ℂ} {ι : Type*} [_root_.Finite ι]
    (F : ι → G → ℂ)
    (h : ∀ g, kernelColumn k g ∈ Submodule.span ℂ (Set.range F)) :
    Module.Finite ℂ (kernelColumnSpan k) := by
  let W := Submodule.span ℂ (Set.range F)
  letI : Module.Finite ℂ W := Module.Finite.of_fg (Submodule.fg_span (Set.finite_range F))
  apply finite_columnSpan_of_le W
  apply Submodule.span_le.mpr
  rintro x ⟨g, rfl⟩
  exact h g

/-- Coefficients of finite-dimensional group representations have finite column rank. -/
theorem finite_columnSpan_of_representation {V : Type*} [AddCommMonoid V] [Module ℂ V]
    [Module.Finite ℂ V] (ρ : G →* End ℂ V) (L : V →ₗ[ℂ] ℂ) (v : V) :
    Module.Finite ℂ (kernelColumnSpan (fun g => L (ρ g v))) := by
  let F : V →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun w x => L (ρ x⁻¹ w)
      map_add' w z := by funext x; simp only [map_add, Pi.add_apply]
      map_smul' c w := by funext x; simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  apply finite_columnSpan_of_le (LinearMap.range F)
  apply Submodule.span_le.mpr
  rintro x ⟨g, rfl⟩
  refine ⟨ρ g v, ?_⟩
  funext y
  change L (ρ y⁻¹ (ρ g v)) = L (ρ (y⁻¹ * g) v)
  rw [map_mul, Module.End.mul_apply]

theorem finite_columnSpan_const (c : ℂ) :
    Module.Finite ℂ (kernelColumnSpan (fun _ : G => c)) := by
  apply finite_columnSpan_of_features (fun _ : Unit => fun _ : G => c)
  intro g
  exact Submodule.subset_span ⟨(), rfl⟩

theorem finite_columnSpan_smul (c : ℂ) (k : G → ℂ) [Module.Finite ℂ (kernelColumnSpan k)] :
    Module.Finite ℂ (kernelColumnSpan (fun g => c • k g)) := by
  apply finite_columnSpan_of_le (kernelColumnSpan k)
  apply Submodule.span_le.mpr
  rintro x ⟨g, rfl⟩
  exact (kernelColumnSpan k).smul_mem c (Submodule.subset_span ⟨g, rfl⟩)

theorem finite_columnSpan_add (k l : G → ℂ)
    [Module.Finite ℂ (kernelColumnSpan k)] [Module.Finite ℂ (kernelColumnSpan l)] :
    Module.Finite ℂ (kernelColumnSpan (fun g => k g + l g)) := by
  let S := kernelColumnSpan k
  let T := kernelColumnSpan l
  letI : Module.Finite ℂ ↥(S ⊔ T) := Module.Finite.of_fg
    ((Submodule.FG.of_finite (N := S)).sup (Submodule.FG.of_finite (N := T)))
  apply finite_columnSpan_of_le (S ⊔ T)
  apply Submodule.span_le.mpr
  rintro x ⟨g, rfl⟩
  exact (S ⊔ T).add_mem
    ((show S ≤ S ⊔ T from le_sup_left) (Submodule.subset_span ⟨g, rfl⟩))
    ((show T ≤ S ⊔ T from le_sup_right) (Submodule.subset_span ⟨g, rfl⟩))

/-- Pointwise products of finite-rank kernels remain finite rank. -/
theorem finite_columnSpan_mul (k l : G → ℂ)
    [Module.Finite ℂ (kernelColumnSpan k)] [Module.Finite ℂ (kernelColumnSpan l)] :
    Module.Finite ℂ (kernelColumnSpan (fun g => k g * l g)) := by
  let S := kernelColumnSpan k
  let T := kernelColumnSpan l
  letI : Module.Finite ℂ (S * T) := Module.Finite.of_fg
    ((Submodule.FG.of_finite (N := S)).mul (Submodule.FG.of_finite (N := T)))
  apply finite_columnSpan_of_le (S * T)
  apply Submodule.span_le.mpr
  rintro x ⟨g, rfl⟩
  exact Submodule.mul_mem_mul (Submodule.subset_span ⟨g, rfl⟩)
    (Submodule.subset_span ⟨g, rfl⟩)

theorem finite_columnSpan_sum {ι : Type*} (s : Finset ι) (k : ι → G → ℂ)
    (h : ∀ i ∈ s, Module.Finite ℂ (kernelColumnSpan (k i))) :
    Module.Finite ℂ (kernelColumnSpan (fun g => ∑ i ∈ s, k i g)) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro h
      rw [show (fun g => ∑ i ∈ (∅ : Finset ι), k i g) = (fun _ => 0) from
        funext (fun _ => Finset.sum_empty)]
      exact finite_columnSpan_const 0
  | @insert i s hi ih =>
      intro h
      letI := h i (Finset.mem_insert_self i s)
      letI := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [show (fun g => ∑ j ∈ insert i s, k j g) =
        (fun g => k i g + ∑ j ∈ s, k j g) from
        funext (fun _ => Finset.sum_insert hi)]
      exact finite_columnSpan_add (k i) (fun g => ∑ j ∈ s, k j g)

theorem finite_columnSpan_pow (k : G → ℂ) [Module.Finite ℂ (kernelColumnSpan k)] (n : ℕ) :
    Module.Finite ℂ (kernelColumnSpan (fun g => k g ^ n)) := by
  induction n with
  | zero =>
      rw [show (fun g => k g ^ 0) = (fun _ => 1) from funext (fun _ => pow_zero _)]
      exact finite_columnSpan_const 1
  | succ n ih =>
      letI := ih
      rw [show (fun g => k g ^ (n + 1)) = (fun g => k g ^ n * k g) from
        funext (fun _ => pow_succ _ _)]
      exact finite_columnSpan_mul (fun g => k g ^ n) k

/-- Polynomial evaluations preserve finite column rank. -/
theorem finite_columnSpan_polynomial (k : G → ℂ) [Module.Finite ℂ (kernelColumnSpan k)]
    (P : Polynomial ℂ) : Module.Finite ℂ (kernelColumnSpan (fun g => P.eval (k g))) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      letI := hP
      letI := hQ
      rw [show (fun g => (P + Q).eval (k g)) = (fun g => P.eval (k g) + Q.eval (k g)) from
        funext (fun _ => Polynomial.eval_add)]
      exact finite_columnSpan_add (fun g => P.eval (k g)) (fun g => Q.eval (k g))
  | monomial n c =>
      letI := finite_columnSpan_pow k n
      rw [show (fun g => (Polynomial.monomial n c).eval (k g)) = (fun g => c • k g ^ n) from
        funext (fun _ => by rw [Polynomial.eval_monomial, smul_eq_mul])]
      exact finite_columnSpan_smul c (fun g => k g ^ n)

/-- Pullback along a group homomorphism preserves finite column rank. -/
theorem finite_columnSpan_pullback {H : Type*} [Group H] (k : H → ℂ)
    [Module.Finite ℂ (kernelColumnSpan k)] (φ : G →* H) :
    Module.Finite ℂ (kernelColumnSpan (fun g => k (φ g))) := by
  let F := (LinearMap.funLeft ℂ ℂ φ).domRestrict (kernelColumnSpan k)
  apply finite_columnSpan_of_le (LinearMap.range F)
  apply Submodule.span_le.mpr
  rintro x ⟨g, rfl⟩
  refine ⟨⟨kernelColumn k (φ g), Submodule.subset_span ⟨φ g, rfl⟩⟩, ?_⟩
  funext y
  change k ((φ y)⁻¹ * φ g) = k (φ (y⁻¹ * g))
  rw [map_mul, map_inv]

#print axioms finite_columnSpan_of_representation
#print axioms finite_columnSpan_mul
#print axioms finite_columnSpan_polynomial
#print axioms finite_columnSpan_pullback
end GaloisForLFunctions.HeckeKreinToeplitz
