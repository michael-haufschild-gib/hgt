import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.BlockUnipotentRadicals
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix

/-! A continuous field isomorphism transports smoothness and
Jacquet vanishing. Coordinate radicals are preserved by entrywise
application of the isomorphism. -/

noncomputable section

open Matrix Representation

namespace GlobalTheory.GLp

variable {k l : Type} [Field k] [Field l] {n : ℕ}

theorem mem_blockUnipotentRadical_map_iff
    (e : k ≃+* l) (b : Fin n → ℕ) (x : GL (Fin n) k) :
    GeneralLinearGroup.map e.toRingHom x ∈ blockUnipotentRadical l b ↔
      x ∈ blockUnipotentRadical k b := by
  simp only [mem_blockUnipotentRadical, Matrix.sub_apply, sub_eq_zero]
  have h1 (i j : Fin n) : e ((1 : Matrix (Fin n) (Fin n) k) i j) = (1 : Matrix (Fin n) (Fin n) l) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  constructor
  · intro h i j hij
    apply e.injective
    rw [h1]
    exact h i j hij
  · intro h i j hij
    rw [← h1]
    exact congrArg e (h i j hij)

theorem isSmoothCuspidal_comp_fieldEquiv
    [TopologicalSpace k] [TopologicalSpace l]
    (e : k ≃+* l) (he : Continuous e)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) l) V) (hρ : IsSmoothCuspidal ρ) :
    IsSmoothCuspidal (ρ.comp (GeneralLinearGroup.map e.toRingHom)) := by
  let f := GeneralLinearGroup.map (n := Fin n) e.toRingHom
  have hf : Continuous f := Units.continuous_map (continuous_id.matrix_map he)
  refine ⟨fun v => (hρ.1 v).preimage hf, fun b hb => ?_⟩
  let H := blockUnipotentRadical k b
  let H' := blockUnipotentRadical l b
  let g : H →* H' :=
    (f.comp H.subtype).codRestrict H' (fun x =>
      (mem_blockUnipotentRadical_map_iff e b x.val).mpr x.2)
  have hg : Function.Surjective g := by
    intro x
    let y := GeneralLinearGroup.map (n := Fin n) e.symm.toRingHom x.val
    have hy : y ∈ H := (mem_blockUnipotentRadical_map_iff e.symm b x.val).mpr x.2
    refine ⟨⟨y, hy⟩, Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))⟩
    exact e.apply_symm_apply (x.val.val i j)
  change Coinvariants.ker ((ρ.comp H'.subtype).comp g) = ⊤
  rw [← hρ.2 b hb]
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨⟨a, v⟩, rfl⟩
    exact Coinvariants.sub_mem_ker (g a) v
  · rintro _ ⟨⟨a, v⟩, rfl⟩
    obtain ⟨c, rfl⟩ := hg a
    exact Coinvariants.sub_mem_ker (ρ := (ρ.comp H'.subtype).comp g) c v

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.isSmoothCuspidal_comp_fieldEquiv
