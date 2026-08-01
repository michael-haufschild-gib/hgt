import GaloisForLFunctions.RHTower.DeningerKronecker
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.GDelta.Basic

/-!
# Residual density of the nondegenerate locus

The vectors not orthogonal to any member of a countable family of nonzero vectors form a dense
`Gδ` set: each orthogonal hyperplane is closed with empty interior, and a Baire space is not a
countable union of such sets.

This is why a residual set of Kummer leaves has dense Kronecker orbit: the annihilator of the
associated one-parameter subgroup is trivial exactly on that locus.

* `deningerHyperplane_dense_compl` : the complement of one hyperplane is open and dense.
* `deningerNondegenerate_dense` : the nondegenerate locus is dense.
* `deningerNondegenerate_isGδ` : it is `Gδ`.
* `deningerNondegenerate_smul`, `deningerNondegenerate_isometry` : it is stable under nonzero
  scaling and under isometries permuting the family.
-/

namespace RHTower

open scoped InnerProductSpace

section Residual

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The locus where a vector is not orthogonal to `v`. -/
def deningerNonPerp (v : H) : Set H := {h : H | ⟪v, h⟫_ℝ ≠ 0}

omit [CompleteSpace H] in
theorem deningerNonPerp_isOpen (v : H) : IsOpen (deningerNonPerp v) := by
  have : deningerNonPerp v = (((innerSL ℝ v).ker : Submodule ℝ H) : Set H)ᶜ := by
    ext h
    simp [deningerNonPerp]
  rw [this]
  exact ((innerSL ℝ v).isClosed_ker).isOpen_compl

omit [CompleteSpace H] in
/-- **The complement of an orthogonal hyperplane is dense.**  The hyperplane is a proper closed
subspace, so it has empty interior. -/
theorem deningerHyperplane_dense_compl {v : H} (hv : v ≠ 0) : Dense (deningerNonPerp v) := by
  have hne : ((innerSL ℝ v).ker : Submodule ℝ H) ≠ ⊤ := by
    intro htop
    have hmem : v ∈ ((innerSL ℝ v).ker : Submodule ℝ H) := htop ▸ Submodule.mem_top
    have : ⟪v, v⟫_ℝ = 0 := by simpa using hmem
    exact hv (inner_self_eq_zero.mp this)
  have hint : interior ((((innerSL ℝ v).ker : Submodule ℝ H)) : Set H) = ∅ := by
    by_contra hcon
    exact hne (Submodule.eq_top_of_nonempty_interior' _
      (Set.nonempty_iff_ne_empty.mpr hcon))
  have hcompl : deningerNonPerp v = (((innerSL ℝ v).ker : Submodule ℝ H) : Set H)ᶜ := by
    ext h
    simp [deningerNonPerp]
  rw [hcompl, ← interior_eq_empty_iff_dense_compl]
  exact hint

/-- **The nondegenerate locus of a countable family of nonzero vectors is dense.** -/
theorem deningerNondegenerate_dense {ι : Type*} [Countable ι] (f : ι → H)
    (hf : ∀ i, f i ≠ 0) : Dense (⋂ i, deningerNonPerp (f i)) :=
  dense_iInter_of_isOpen (fun i => deningerNonPerp_isOpen (f i))
    (fun i => deningerHyperplane_dense_compl (hf i))

omit [CompleteSpace H] in
/-- **The nondegenerate locus is `Gδ`.** -/
theorem deningerNondegenerate_isGδ {ι : Type*} [Countable ι] (f : ι → H) :
    IsGδ (⋂ i, deningerNonPerp (f i)) :=
  IsGδ.iInter fun i => (deningerNonPerp_isOpen (f i)).isGδ

omit [CompleteSpace H] in
/-- Membership in the nondegenerate locus says exactly that no member of the family is orthogonal
to the vector: the annihilator of the associated one-parameter subgroup is trivial. -/
theorem deningerMem_nondegenerate {ι : Type*} (f : ι → H) (h : H) :
    h ∈ (⋂ i, deningerNonPerp (f i)) ↔ ∀ i, ⟪f i, h⟫_ℝ ≠ 0 := by
  simp [deningerNonPerp]

omit [CompleteSpace H] in
/-- **The nondegenerate locus is stable under nonzero real scaling.** -/
theorem deningerNondegenerate_smul {ι : Type*} (f : ι → H) {c : ℝ} (hc : c ≠ 0) {h : H}
    (hh : h ∈ ⋂ i, deningerNonPerp (f i)) : c • h ∈ ⋂ i, deningerNonPerp (f i) := by
  rw [deningerMem_nondegenerate] at hh ⊢
  intro i
  rw [real_inner_smul_right]
  exact mul_ne_zero hc (hh i)

omit [CompleteSpace H] in
/-- **The nondegenerate locus is stable under an isometry permuting the family.**  This is the
Galois invariance: Galois maps permute the nonzero Kummer vectors. -/
theorem deningerNondegenerate_isometry {ι : Type*} (f : ι → H) (U : H ≃ₗᵢ[ℝ] H)
    (hU : ∀ i, U.symm (f i) ∈ Set.range f) {h : H}
    (hh : h ∈ ⋂ i, deningerNonPerp (f i)) : U h ∈ ⋂ i, deningerNonPerp (f i) := by
  rw [deningerMem_nondegenerate] at hh ⊢
  intro i
  obtain ⟨j, hj⟩ := hU i
  have hinner : ⟪f i, U h⟫_ℝ = ⟪f j, h⟫_ℝ := by
    rw [hj, ← U.inner_map_map (U.symm (f i)) h, U.apply_symm_apply]
  rw [hinner]
  exact hh j

end Residual

end RHTower
