import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechDifferentialComplex
import Mathlib.LinearAlgebra.Trace

/-! A finite cocycle resolution of the identity computes the alternating
trace by its coordinate functionals. -/

noncomputable section

namespace GlobalTheory.CechDR

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M]

private theorem trace_of_resolution {V ι : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Fintype ι] (v : ι → V) (φ : ι → V →ₗ[k] k)
    (h : ∀ x, x = ∑ j, φ j x • v j) (u : V →ₗ[k] V) :
    LinearMap.trace k V u = ∑ j, φ j (u (v j)) := by
  have e : u = ∑ j, (φ j).smulRight (u (v j)) := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, ← map_smul u, ← map_sum]
    exact congrArg u (h x)
  conv_lhs => rw [e, map_sum]
  simp only [LinearMap.trace_smulRight]

/-- Compute the alternating trace from cocycle representatives and
linear functionals that descend through the boundary quotients. -/
theorem alternating_trace_of_cocycle_resolution (C : Cx k M)
    [∀ q : ℕ, Module.Finite k (C.H (q : ℤ))]
    (u : ∀ q : ℕ, C.H (q : ℤ) →ₗ[k] C.H (q : ℤ)) (d : ℕ) {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (a b : ∀ j, C.Z (p j : ℤ)) (φ : ι → M →ₗ[k] k)
    (hp : ∀ j, p j ≤ d) (hφ : ∀ j, ∀ y ∈ C.B (p j : ℤ), φ j y = 0)
    (hres : ∀ q : ℕ, ∀ x : C.Z (q : ℤ),
      x.val - ∑ j ∈ Finset.univ.filter (fun j => p j = q), φ j x.val • (a j).val ∈ C.B (q : ℤ))
    (hu : ∀ j, u (p j) (Submodule.Quotient.mk (a j)) = Submodule.Quotient.mk (b j)) :
    ∑ q ∈ Finset.range (d + 1), (-1 : k) ^ q * LinearMap.trace k _ (u q) =
      ∑ j, (-1 : k) ^ p j * φ j (b j).val := by
  classical
  have key (q : ℕ) : LinearMap.trace k _ (u q) =
      ∑ j ∈ Finset.univ.filter (fun j => p j = q), φ j (b j).val := by
    let a' (j : {j // p j = q}) : C.Z (q : ℤ) :=
      ⟨(a j.1).val, Eq.mp (congrArg (fun t : ℕ => (a j.1).val ∈ C.Z (t : ℤ)) j.2)
        (a j.1).property⟩
    let v (j : {j // p j = q}) : C.H (q : ℤ) :=
      Submodule.Quotient.mk (a' j)
    let ψ (j : {j // p j = q}) : C.H (q : ℤ) →ₗ[k] k :=
      Submodule.liftQ _ ((φ j.1).comp (C.Z (q : ℤ)).subtype)
        (fun x hx => hφ j.1 x.val (by rw [j.2]; exact hx))
    have hid (z : C.H (q : ℤ)) : z = ∑ j, ψ j z • v j := by
      induction z using Submodule.Quotient.induction_on with
      | H x =>
        have e : ∑ j, ψ j (Submodule.Quotient.mk x) • v j =
            ((C.B q).submoduleOf (C.Z q)).mkQ
              (∑ j : {j // p j = q}, φ j.1 x.val • a' j) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          change φ j.1 x.val • ((C.B q).submoduleOf (C.Z q)).mkQ (a' j) =
            ((C.B q).submoduleOf (C.Z q)).mkQ (φ j.1 x.val • a' j)
          exact (map_smul _ _ _).symm
        rw [e, Submodule.mkQ_apply, Submodule.Quotient.eq]
        change ((x - ∑ j : {j // p j = q}, φ j.1 x.val • a' j : C.Z (q : ℤ)) : M) ∈ C.B (q : ℤ)
        have hr := hres q x
        rw [Finset.sum_subtype (Finset.univ.filter fun j => p j = q)
          (p := fun j => p j = q) (by simp)] at hr
        simpa only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, a'] using hr
    rw [trace_of_resolution v ψ hid, Finset.sum_subtype
      (Finset.univ.filter fun j => p j = q) (p := fun j => p j = q) (by simp)]
    refine Finset.sum_congr rfl ?_
    rintro ⟨j, rfl⟩ _
    show ψ ⟨j, rfl⟩ (u (p j) (Submodule.Quotient.mk (a j))) = φ j (b j).val
    rw [hu j] <;> rfl
  calc
    _ = ∑ q ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.univ.filter (fun j => p j = q), (-1 : k) ^ p j * φ j (b j).val := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [key, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j hj =>
        congrArg (fun t : ℕ => (-1 : k) ^ t * φ j (b j).val) (Finset.mem_filter.mp hj).2.symm
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hp j))) _

end GlobalTheory.CechDR
