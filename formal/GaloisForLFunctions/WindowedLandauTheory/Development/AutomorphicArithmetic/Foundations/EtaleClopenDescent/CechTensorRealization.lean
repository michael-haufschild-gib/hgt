import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteGradedCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechCup
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Submodule.Bilinear

/-! The tensor product of the regular cochains on two finite covers
is realized by their tensor coefficients on joined intersections. -/

noncomputable section

open GlobalTheory.CechDR
open scoped TensorProduct

namespace GlobalTheory.WH

variable {k ι κ E M : Type} [Field k] [LinearOrder ι] [LinearOrder κ]
  [Fintype ι] [Fintype κ] [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M]

private abbrev chart {σ N : Type} [AddCommGroup N] [Module k N]
    (A : Finset σ → Submodule k N) (I : Finset σ) : Submodule k N :=
  if I.Nonempty then A I else ⊥

private def chartPi {σ N : Type} [AddCommGroup N] [Module k N] (A : Finset σ → Submodule k N) :
    regularCochains A ≃ₗ[k] (∀ I, chart A I) where
  toFun z I := ⟨z.val I, Submodule.mem_pi.mp z.property I (Set.mem_univ _)⟩
  invFun z := ⟨fun I => (z I).val, Submodule.mem_pi.mpr fun I _ => (z I).property⟩
  left_inv z := Subtype.ext rfl
  right_inv z := funext fun I => Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def tensorComponents (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k M) :
    regularCochains A ⊗[k] regularCochains B ≃ₗ[k] (∀ I J, chart A I ⊗[k] chart B J) :=
  (TensorProduct.congr (chartPi A) (chartPi B)).trans
    ((TensorProduct.piLeft (R := k) (M := fun I => chart A I) (N := ∀ J, chart B J)).trans
      (LinearEquiv.piCongrRight fun I =>
        TensorProduct.piRight (R := k) (S := k) (N := chart A I) (M := fun J => chart B J)))

private theorem tensorComponents_tmul (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k M)
    (a : regularCochains A) (b : regularCochains B) (I : Finset ι) (J : Finset κ) :
    tensorComponents A B (a ⊗ₜ b) I J = chartPi A a I ⊗ₜ chartPi B b J := by
  simp [tensorComponents]

private theorem range_tensor_subtype (P : Submodule k E) (Q : Submodule k M) :
    LinearMap.range (TensorProduct.map P.subtype Q.subtype) =
      Submodule.map₂ (TensorProduct.mk k E M) P Q := by
  refine le_antisymm ?_ (Submodule.map₂_le.mpr ?_)
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul x y =>
      rw [TensorProduct.map_tmul]
      exact Submodule.apply_mem_map₂ _ x.property y.property
  · intro x hx y hy
    exact ⟨(⟨x, hx⟩ : P) ⊗ₜ (⟨y, hy⟩ : Q), TensorProduct.map_tmul _ _ _ _⟩

/-- Tensor coefficients on a joined intersection, with zero coefficients
when either side of the intersection is empty. -/
def joinedTensorCoefficients (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k M)
    (s : Finset (ι ⊕ₗ κ)) : Submodule k (E ⊗[k] M) :=
  Submodule.map₂ (TensorProduct.mk k E M) (chart A (lft s)) (chart B (rgt s))

theorem joinedTensorCoefficients_eq (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k M)
    (s : Finset (ι ⊕ₗ κ)) :
    joinedTensorCoefficients A B s =
      if (lft s).Nonempty ∧ (rgt s).Nonempty then
        Submodule.map₂ (TensorProduct.mk k E M) (A (lft s)) (B (rgt s)) else ⊥ := by
  by_cases hI : (lft s).Nonempty <;> by_cases hJ : (rgt s).Nonempty <;>
    simp [joinedTensorCoefficients, chart, hI, hJ]

/-- Realize a tensor of regular cochains on the joined cover by its
components in the tensor product of the ambient coefficient modules. -/
def tensorToJoined (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k M) :
    regularCochains A ⊗[k] regularCochains B →ₗ[k] (Finset (ι ⊕ₗ κ) → E ⊗[k] M) :=
  LinearMap.pi fun s =>
    (TensorProduct.map (chart A (lft s)).subtype (chart B (rgt s)).subtype).comp
      ((LinearMap.proj (rgt s)).comp ((LinearMap.proj (lft s)).comp (tensorComponents A B).toLinearMap))

theorem tensorToJoined_tmul (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k M)
    (a : regularCochains A) (b : regularCochains B) :
    tensorToJoined A B (a ⊗ₜ b) = cechJoin (TensorProduct.mk k E M) a.val b.val := by
  funext s
  simp only [tensorToJoined, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearEquiv.coe_coe, tensorComponents_tmul, TensorProduct.map_tmul]
  rfl

/-- The realization has no kernel, since tensoring the component inclusions
over the coefficient field preserves injectivity. -/
theorem tensorToJoined_injective (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k M) :
    Function.Injective (tensorToJoined A B) := by
  intro t u h
  apply (tensorComponents A B).injective
  funext I J
  apply TensorProduct.map_injective_of_flat_flat (chart A I).subtype (chart B J).subtype
    Subtype.val_injective Subtype.val_injective
  simpa only [tensorToJoined, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearEquiv.coe_coe, lft_uni, rgt_uni] using congrFun h (uni I J)

theorem tensorToJoined_mem (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k M)
    (t : regularCochains A ⊗[k] regularCochains B) (s : Finset (ι ⊕ₗ κ)) :
    tensorToJoined A B t s ∈ joinedTensorCoefficients A B s := by
  rw [joinedTensorCoefficients, ← range_tensor_subtype]
  exact ⟨tensorComponents A B t (lft s) (rgt s), rfl⟩

/-- A joined cochain with the tensor coefficients prescribed at each
intersection is realized by a tensor of regular cochains. -/
theorem exists_tensorToJoined (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k M)
    (z : Finset (ι ⊕ₗ κ) → E ⊗[k] M) (hz : ∀ s, z s ∈ joinedTensorCoefficients A B s) :
    ∃ t, tensorToJoined A B t = z := by
  have hpre (I : Finset ι) (J : Finset κ) :
      ∃ w : chart A I ⊗[k] chart B J,
        TensorProduct.map (chart A I).subtype (chart B J).subtype w = z (uni I J) := by
    have h := hz (uni I J)
    simpa only [joinedTensorCoefficients, lft_uni, rgt_uni, ← range_tensor_subtype, LinearMap.mem_range] using h
  choose w hw using hpre
  let t := (tensorComponents A B).symm w
  refine ⟨t, funext fun s => ?_⟩
  obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
  simp only [tensorToJoined, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearEquiv.coe_coe, lft_uni, rgt_uni, t, LinearEquiv.apply_symm_apply, hw]

end GlobalTheory.WH
