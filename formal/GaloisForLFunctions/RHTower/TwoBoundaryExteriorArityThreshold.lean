import GaloisForLFunctions.RHTower.VonMangoldtGammaAllDepthCauchy

/-!
# Four-direction threshold for a two-boundary exterior response

The canonical von Mangoldt--Gamma Cauchy compression removes two boundary modes.  A nonzero
second-compound response after that compression therefore cannot be carried by only two or three
source directions: the compressed exterior pair already consumes two further independent
directions.

This module proves the exact finite-dimensional threshold.  It is the positive survivor of the
failed two-anchor target: any source realization of a nonzero balanced exterior Gram determinant
must have at least four independent source directions before compression.  No Xi zero, target
coefficient, positivity conjecture, or asymptotic estimate is used.
-/

open scoped ComplexOrder

namespace RHTower

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Projection to the complement of a boundary subspace stays inside any finite source subspace
which already contains the boundary modes. -/
theorem twoBoundaryOrthogonalProjection_mem_source
    (S U : Submodule ℂ E) [S.HasOrthogonalProjection]
    (hSU : S ≤ U) {x : E} (hx : x ∈ U) :
    Sᗮ.starProjection x ∈ U := by
  rw [S.starProjection_orthogonal_val]
  exact U.sub_mem hx (hSU (S.orthogonalProjectionOnto x).property)

/-- **Four-direction threshold.**  If two independent vectors survive after removing a
two-dimensional boundary subspace, then the source subspace before compression has dimension at
least four. -/
theorem twoBoundaryExterior_nonzero_forces_four_sourceDirections
    (S U : Submodule ℂ E) [S.HasOrthogonalProjection] [FiniteDimensional ℂ U]
    (hSU : S ≤ U) (hSrank : Module.finrank ℂ S = 2)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U)
    (hExterior : LinearIndependent ℂ ![Sᗮ.starProjection x, Sᗮ.starProjection y]) :
    4 ≤ Module.finrank ℂ U := by
  let T : Submodule ℂ E := Sᗮ ⊓ U
  have hxT : Sᗮ.starProjection x ∈ T := ⟨
    (Sᗮ.orthogonalProjectionOnto x).property,
    twoBoundaryOrthogonalProjection_mem_source S U hSU hx⟩
  have hyT : Sᗮ.starProjection y ∈ T := ⟨
    (Sᗮ.orthogonalProjectionOnto y).property,
    twoBoundaryOrthogonalProjection_mem_source S U hSU hy⟩
  let v : Fin 2 → T := ![
    ⟨Sᗮ.starProjection x, hxT⟩,
    ⟨Sᗮ.starProjection y, hyT⟩]
  have hExteriorT : LinearIndependent ℂ v := by
    have hcomp : T.subtype ∘ v =
        ![Sᗮ.starProjection x, Sᗮ.starProjection y] := by
      funext i
      fin_cases i <;> rfl
    apply (T.subtype.linearIndependent_iff_of_injOn
      T.injective_subtype.injOn).mp
    rw [hcomp]
    exact hExterior
  have hTlower : 2 ≤ Module.finrank ℂ T := by
    simpa using hExteriorT.fintype_card_le_finrank
  have hsplit := Submodule.finrank_add_inf_finrank_orthogonal hSU
  change Module.finrank ℂ S + Module.finrank ℂ T = Module.finrank ℂ U at hsplit
  omega

/-- A nonzero two-by-two Gram determinant in the balanced sector is the metric form of the same
four-direction threshold. -/
theorem twoBoundaryBalancedGramDet_nonzero_forces_four_sourceDirections
    (S U : Submodule ℂ E) [S.HasOrthogonalProjection] [FiniteDimensional ℂ U]
    (hSU : S ≤ U) (hSrank : Module.finrank ℂ S = 2)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U)
    (hdet : (Matrix.gram ℂ ![Sᗮ.starProjection x, Sᗮ.starProjection y]).det ≠ 0) :
    4 ≤ Module.finrank ℂ U := by
  apply twoBoundaryExterior_nonzero_forces_four_sourceDirections S U hSU hSrank hx hy
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mp hdet

/-- Consequently, any finite source packet known a priori to have at most `M` independent source
directions needs `M ≥ 4` before its two-boundary balanced exterior metric can be nonzero. -/
theorem four_le_sourceArity_of_twoBoundaryBalancedGramDet_nonzero
    (S U : Submodule ℂ E) [S.HasOrthogonalProjection] [FiniteDimensional ℂ U]
    (hSU : S ≤ U) (hSrank : Module.finrank ℂ S = 2)
    {M : ℕ} (hUrank : Module.finrank ℂ U ≤ M)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U)
    (hdet : (Matrix.gram ℂ ![Sᗮ.starProjection x, Sᗮ.starProjection y]).det ≠ 0) :
    4 ≤ M := by
  exact (twoBoundaryBalancedGramDet_nonzero_forces_four_sourceDirections
    S U hSU hSrank hx hy hdet).trans hUrank

end

end RHTower
