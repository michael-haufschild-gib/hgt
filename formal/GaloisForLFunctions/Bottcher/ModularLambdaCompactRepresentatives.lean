/-
# Compact representatives for modular-lambda fibres

This file extracts a usable selection statement from the properness proof of `λ̄`.
For a compact set of base values in `ℂ∖{0,1}`, there is a single compact subset of `ℍ`
meeting every corresponding `λ`-fibre.  Combined with the Cayley compact-bound lemma, this is
the deck-normalization producer for the compact basepoint branch.
-/
import GaloisForLFunctions.Bottcher.ModularLambdaProperness
import GaloisForLFunctions.Bottcher.ModularLambdaDeckNormal

open UpperHalfPlane CongruenceSubgroup MulAction
open scoped MatrixGroups UpperHalfPlane

namespace Bottcher

local notation "qmk" => Quotient.mk (MulAction.orbitRel (Gamma 2 ⧸ projKer) ℍ)

/-- A compact set of punctured-sphere values has compactly bounded upper-half-plane
representatives under `λ`. -/
theorem exists_compact_lambdaPunct_representatives {K : Set Punctured} (hK : IsCompact K) :
    ∃ T : Set ℍ, IsCompact T ∧
      ∀ w ∈ K, ∃ τ : ℍ, τ ∈ T ∧ lambdaPunct τ = w := by
  classical
  haveI hnorm := Gamma_normal 2
  obtain ⟨M, hM⟩ := cusp_height_bound hK
  set S : Set ℍ := ModularGroup.truncatedFundamentalDomain M ∩ lambdaPunct ⁻¹' (Kprime K) with hSdef
  have hKpcl : IsClosed (Kprime K) := (isCompact_Kprime hK).isClosed
  have hScompact : IsCompact S :=
    (ModularGroup.isCompact_truncatedFundamentalDomain M).inter_right
      (hKpcl.preimage continuous_lambdaPunct)
  set T : Set ℍ := ⋃ (cq : SL(2, ℤ) ⧸ Gamma 2), (fun z : ℍ => cq.out • z) '' S with hTdef
  have hTcompact : IsCompact T := by
    apply isCompact_iUnion
    intro cq
    exact hScompact.image (continuous_sl2z_smul cq.out)
  refine ⟨T, hTcompact, ?_⟩
  intro w hwK
  obtain ⟨z, hz⟩ := lambdaPunct_surjective w
  have hzK : lambdaPunct z ∈ K := by
    rw [hz]
    exact hwK
  obtain ⟨g, hgfd⟩ := ModularGroup.exists_smul_mem_fd z
  have hgK' : lambdaPunct (g • z) ∈ Kprime K := lambdaPunct_smul_mem_Kprime g hzK
  have hgim : (((g • z) : ℍ) : ℂ).im ≤ M := hM (g • z) hgK'
  have hgS : g • z ∈ S := ⟨⟨hgfd, hgim⟩, hgK'⟩
  set cq : SL(2, ℤ) ⧸ Gamma 2 := QuotientGroup.mk g⁻¹ with hcqdef
  set c : SL(2, ℤ) := cq.out with hcdef
  have hceq : (QuotientGroup.mk c : SL(2, ℤ) ⧸ Gamma 2) = QuotientGroup.mk g⁻¹ := by
    rw [hcdef]
    exact Quotient.out_eq cq
  have hcg : c⁻¹ * g⁻¹ ∈ Gamma 2 := QuotientGroup.eq.mp hceq
  have hγ : g⁻¹ * c⁻¹ ∈ Gamma 2 := by
    have h := hnorm.conj_mem _ hcg g⁻¹
    have he : g⁻¹ * (c⁻¹ * g⁻¹) * (g⁻¹)⁻¹ = g⁻¹ * c⁻¹ := by group
    rwa [he] at h
  set γ : Gamma 2 := ⟨g⁻¹ * c⁻¹, hγ⟩ with hγdef
  have hγz : (γ : Gamma 2) • (c • (g • z)) = z := by
    show ((g⁻¹ * c⁻¹ : SL(2, ℤ))) • (c • (g • z)) = z
    rw [mul_smul, inv_smul_smul, inv_smul_smul]
  have hqeq : qmk (c • (g • z)) = qmk z := by
    conv_rhs => rw [← hγz]
    exact (qmk_smul_eq γ (c • (g • z))).symm
  refine ⟨c • (g • z), ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨cq, g • z, hgS, rfl⟩
  · have hlambda : lambdaPunct (c • (g • z)) = lambdaPunct z := by
      have hbar : lambdaBar (qmk (c • (g • z))) = lambdaBar (qmk z) := by rw [hqeq]
      simpa [lambdaBar_comp_mk] using! hbar
    rw [hlambda, hz]

/-- Compact base values have uniformly Cayley-bounded modular representatives. -/
theorem exists_uniform_cayley_bound_of_compact_values {a : ℕ → Punctured} {K : Set Punctured}
    (hK : IsCompact K) (haK : ∀ n, a n ∈ K) :
    ∃ s : ℝ, s < 1 ∧
      ∀ n, ∃ τ : ℍ, modularLambda (τ : ℂ) = (a n : ℂ) ∧ ‖cayley (τ : ℂ)‖ ≤ s := by
  obtain ⟨T, hTcompact, hT⟩ := exists_compact_lambdaPunct_representatives hK
  exact exists_uniform_cayley_bound_of_compact_preimages hTcompact
    (fun n => by
      obtain ⟨τ, hτT, hτeq⟩ := hT (a n) (haK n)
      exact ⟨τ, hτT, congrArg Subtype.val hτeq⟩)

end Bottcher
