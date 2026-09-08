import GaloisForLFunctions.HTGeometry.GomesFlatBoostTensorHolonomy
import GaloisForLFunctions.RHTower.RationalHurwitzLorentzBoost

/-!
# Tensor-matter visibility of the actual rational-Hurwitz boost

The associated-transport construction in arXiv:2404.10461 and the distinction
between representation carriers in arXiv:2607.24901v1 act on the existing
rational-Hurwitz boost. Its matrix agrees with the flat Cartan boost on pair
coordinates. Original fixed vectors detect neutral rapidity; associated tensor
matter retains a two-plane at every nondegenerate parameter. In particular,
nonzero parallel tensors exist at every complex parameter and modulus. This is
an exact visibility limitation, with no implication that any zeta zero exists
or lies off the critical line.
-/

open scoped TensorProduct
noncomputable section
namespace RHTower
open HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy

/-- The existing Hurwitz matrix acts exactly as the flat Cartan boost on pair coordinates. -/
theorem hurwitzBoost_pair_action (rho : ℂ) (n : ℕ) (v : Fibre) :
    (hurwitzBoost rho n).mulVec ![v.1,v.2] =
      ![(boost ((rho.re - 1/2) * Real.log n) v).1,
        (boost ((rho.re - 1/2) * Real.log n) v).2] := by
  funext i
  fin_cases i <;> simp [hurwitzBoost,lorentzBoost,boost_apply,Matrix.mulVec,dotProduct,
    Fin.sum_univ_two]

/-- Exact degeneracies of the actual Hurwitz rapidity, with no restriction on the modulus. -/
theorem hurwitzRapidity_eq_zero_iff (rho : ℂ) (n : ℕ) :
    (rho.re - 1/2) * Real.log n = 0 ↔ rho.re = 1/2 ∨ n=0 ∨ n=1 := by
  have hn : (n : ℝ) ≠ -1 := by
    have hp := Nat.cast_nonneg (α := ℝ) n
    linarith
  rw [mul_eq_zero,sub_eq_zero,Real.log_eq_zero]
  simp [hn]

/-- The original Hurwitz carrier has nonzero fixed vectors only at its exact neutral parameters. -/
theorem hurwitzBoost_fixed_pair_iff (rho : ℂ) (n : ℕ) (v : Fibre) :
    (hurwitzBoost rho n).mulVec ![v.1,v.2] = ![v.1,v.2] ↔
      rho.re = 1/2 ∨ n=0 ∨ n=1 ∨ v=0 := by
  rw [hurwitzBoost_pair_action]
  have he : ![(boost ((rho.re - 1/2) * Real.log n) v).1,
        (boost ((rho.re - 1/2) * Real.log n) v).2] = ![v.1,v.2] ↔
      boost ((rho.re - 1/2) * Real.log n) v = v := by
    constructor
    · intro h
      exact Prod.ext (congrFun h 0) (congrFun h 1)
    · intro h
      rw [h]
  rw [he,boost_fixed_vector_iff,hurwitzRapidity_eq_zero_iff]
  tauto

/-- Associated tensor holonomy of the actual rational-Hurwitz boost carrier. -/
def hurwitzTensorHolonomy (rho : ℂ) (n : ℕ) : Multiplicative ℤ →*
    ((Fibre ⊗[ℝ] Fibre) ≃ₗ[ℝ] (Fibre ⊗[ℝ] Fibre)) :=
  flatTensorHolonomy ((rho.re - 1/2) * Real.log n)

/-- The induced tensor has precisely the classified neutral two-plane at every nondegenerate parameter. -/
theorem hurwitzTensorHolonomy_fixed_space (rho : ℂ) (n : ℕ) (x : Fibre ⊗[ℝ] Fibre) :
    (∀ k : ℤ, hurwitzTensorHolonomy rho n (Multiplicative.ofAdd k) x = x) ↔
      rho.re = 1/2 ∨ n=0 ∨ n=1 ∨
        ∃ r s : ℝ, x = r • (eMinus ⊗ₜ[ℝ] ePlus) + s • (ePlus ⊗ₜ[ℝ] eMinus) := by
  rw [hurwitzTensorHolonomy,flatTensorHolonomy_fixed_space,hurwitzRapidity_eq_zero_iff]
  tauto

/-- Nonzero parallel tensor matter survives at every complex strip point and every modulus. -/
theorem hurwitzTensorHolonomy_parallel_nonzero (rho : ℂ) (n : ℕ) :
    ∃ x : Fibre ⊗[ℝ] Fibre, x ≠ 0 ∧
      ∀ k : ℤ, hurwitzTensorHolonomy rho n (Multiplicative.ofAdd k) x = x := by
  obtain ⟨x,hx,hfix⟩ := flatBoostTensor_parallel_nonzero ((rho.re - 1/2) * Real.log n)
  refine ⟨x,hx,?_⟩
  exact (flatTensorHolonomy_fixed_space _ x).mpr ((flatBoostTensor_fixed_space _ x).mp hfix)

end RHTower
