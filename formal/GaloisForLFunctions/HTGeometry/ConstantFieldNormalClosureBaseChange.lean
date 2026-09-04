import GaloisForLFunctions.HTGeometry.ConstantFieldGaloisBaseChange

/-!
# Normal closures under algebraically closed constant extension

Scalar extension of a finite Galois normal closure remains the normal closure of the scalar-
extended source.  The proof transports every old source embedding and shows their images still
generate the whole tensor extension.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

variable {k F S L K : Type*} [Field k] [IsAlgClosed k]
  [Field F] [Field S] [Field L] [Field K]
  [Algebra k F] [Algebra k K] [Algebra F S] [Algebra F L]
  [Algebra k S] [Algebra k L] [IsScalarTower k F S] [IsScalarTower k F L]

/-- Normal closures remain normal closures after extending an algebraically closed constant
field. -/
theorem constantScalarExtension_isNormalClosure
    (i : S →ₐ[F] L)
    [FiniteDimensional F S] [FiniteDimensional F L]
    [IsNormalClosure F S L] [IsGalois F L] :
    IsNormalClosure (constantScalarBase k F K)
      (constantScalarExtension k F S K)
      (constantScalarExtension k F L K) := by
  let B := constantScalarBase k F K
  let S' := constantScalarExtension k F S K
  let L' := constantScalarExtension k F L K
  letI : IsGalois B L' := constantScalarExtension_isGalois
  apply (Algebra.IsAlgebraic.isNormalClosure_iff).2
  let iS : S' →ₐ[B] L' := ABHN.algHomBaseChange (L := B) i
  refine ⟨fun x => ?_, ?_⟩
  · rw [← minpoly.algHom_eq iS iS.injective x]
    exact Normal.splits' (iS x)
  let N : IntermediateField B L' := IntermediateField.normalClosure B S' L'
  let iL : L →ₐ[F] L' := Algebra.TensorProduct.includeRight
  let M : IntermediateField F L :=
    { carrier := {x | iL x ∈ N}
      zero_mem' := by
        change iL 0 ∈ N
        rw [map_zero]
        exact N.zero_mem
      add_mem' := by
        intro x y hx hy
        change iL (x + y) ∈ N
        rw [map_add]
        exact N.add_mem hx hy
      one_mem' := by
        change iL 1 ∈ N
        rw [map_one]
        exact N.one_mem
      mul_mem' := by
        intro x y hx hy
        change iL (x * y) ∈ N
        rw [map_mul]
        exact N.mul_mem hx hy
      inv_mem' := by
        intro x hx
        change iL x⁻¹ ∈ N
        rw [map_inv₀]
        exact N.inv_mem hx
      algebraMap_mem' := by
        intro c
        change iL (algebraMap F L c) ∈ N
        have hbase := N.algebraMap_mem (algebraMap F B c)
        simpa [iL, B, L'] using hbase }
  have hle : IntermediateField.normalClosure F S L ≤ M := by
    rw [normalClosure_le_iff]
    intro f y hy
    obtain ⟨x, rfl⟩ := hy
    change iL (f x) ∈ N
    let f' : S' →ₐ[B] L' := ABHN.algHomBaseChange (L := B) f
    have hrange : f' ((1 : B) ⊗ₜ[F] x) ∈ f'.fieldRange := ⟨_, rfl⟩
    have hsub : f'.fieldRange ≤ N :=
      le_iSup (fun g : S' →ₐ[B] L' => g.fieldRange) f'
    have := hsub hrange
    simpa [f', iL, N, S', L', ABHN.algHomBaseChange] using this
  have holdTop : IntermediateField.normalClosure F S L = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp
      (inferInstance : IsNormalClosure F S L)).2
  have hMTop : M = ⊤ := by
    apply top_unique
    rw [← holdTop]
    exact hle
  have hright (x : L) : iL x ∈ N := by
    have hx : x ∈ M := by rw [hMTop]; trivial
    exact hx
  change N = ⊤
  apply top_unique
  intro z hz
  clear hz
  induction z using TensorProduct.induction_on with
  | zero => exact N.zero_mem
  | tmul a x =>
      have ha := N.algebraMap_mem a
      have hx := hright x
      change a ⊗ₜ[F] x ∈ N
      rw [show a ⊗ₜ[F] x =
          algebraMap B L' a * iL x by
            simp [iL, L']
            rw [Algebra.algebraMap_self]
            rfl]
      exact N.mul_mem ha hx
  | add x y hx hy => exact N.add_mem hx hy

end

end GaloisForLFunctions.HTGeometry
