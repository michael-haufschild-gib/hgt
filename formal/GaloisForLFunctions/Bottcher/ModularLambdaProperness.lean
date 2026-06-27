/-
# `λ̄ : ℍ/PΓ(2) → ℂ∖{0,1}` is proper — hence a covering map

This discharges the single hypothesis left open by `ModularLambdaQuotientLift`: the modular `λ̄` descended to
the modular curve `Y(2) = ℍ/PΓ(2)` is a **proper** map. Granting it (proved here), `λ̄` is a proper local
homeomorphism, hence a covering map (`isCoveringMap_lambdaBar`).

## The cusp-escape argument

Properness is `∀ K compact, IsCompact (λ̄⁻¹ K)` (`isProperMap_iff_isCompact_preimage`; `ℂ∖{0,1}` is T2 and
compactly coherent). The mechanism:

* **Anharmonic orbit `K'`** (`Kprime`): translating a point into the `SL(2,ℤ)` fundamental domain twists `λ`
  by the anharmonic `S₃`-action (`exists_anharm_eq`), so `λ` of the translate lands in the finite union of
  `S₃`-images of `K` — still compact, still avoiding `{0,1}`.
* **Cusp height bound** (`cusp_height_bound`): since `λ → 0` *uniformly* as `Im → ∞`
  (`tendsto_modularLambda_atImInfty`, a `comap`-`atTop` limit) and `K'` is bounded away from `0`, any `w` with
  `λ w ∈ K'` has `Im w` capped by some `M`. So the fundamental-domain part of `λ⁻¹K'` lives in the **compact**
  truncated domain `S = 𝒟_{≤M} ∩ λ⁻¹K'`.
* **Folding by `SL(2,ℤ)/Γ(2)`**: `Γ(2)` is normal of finite index, so the finite quotient acts on `Y(2)`.
  Every `q z ∈ λ̄⁻¹K` equals `q(c•(g•z))` for a coset representative `c`, with `g•z ∈ S`. Hence
  `λ̄⁻¹K ⊆ ⋃_c q(c•S)`, a finite union of compact sets; being closed, `λ̄⁻¹K` is compact.

Note this needs `λ̄` only as a **covering** (any degree), never injective — the argument-principle/degree-1
crux is entirely bypassed. With `IsCoveringMap λ̄` in hand, `λ = λ̄ ∘ q` is the modular `λ` exhibited as a
covering of `ℂ∖{0,1}` (the universal property feeding the three-value Montel lift, `#30`).
-/
import Mathlib
import GaloisForLFunctions.Bottcher.Gamma2QuotientCovering
import GaloisForLFunctions.Bottcher.ModularLambdaCovering
import GaloisForLFunctions.Bottcher.ModularLambdaUnconditional
import GaloisForLFunctions.Bottcher.ModularLambdaQuotientLift
import GaloisForLFunctions.Bottcher.CoveringComp

open UpperHalfPlane CongruenceSubgroup MulAction
open scoped MatrixGroups

namespace Bottcher

local notation "qmk" => Quotient.mk (MulAction.orbitRel (Gamma 2 ⧸ projKer) ℍ)

/-- The quotient map `q : ℍ → ℍ/PΓ(2)` is `Γ(2)`-invariant: `q(γ • w) = q w`. -/
theorem qmk_smul_eq (γ : Gamma 2) (w : ℍ) : qmk (γ • w) = qmk w := by
  apply Quotient.sound
  show (γ • w) ∈ MulAction.orbit (Gamma 2 ⧸ projKer) w
  exact ⟨QuotientGroup.mk γ, mk_smul γ w⟩

/-- The **anharmonic orbit** of `K`: the union of the (finite) `S₃`-permutation images of `K`. Compact,
and contained in `ℂ∖{0,1}` (each anharmonic element is a permutation of `Punctured`). -/
noncomputable def Kprime (K : Set Punctured) : Set Punctured :=
  ⋃ (φ : ↥anharmonicGroup), (⇑(φ : Equiv.Perm Punctured)) '' K

theorem isCompact_Kprime {K : Set Punctured} (hK : IsCompact K) : IsCompact (Kprime K) := by
  apply isCompact_iUnion
  intro φ
  exact hK.image (continuous_of_mem_anharmonicGroup φ.2)

/-- `λ` of an `SL(2,ℤ)`-translate of `z` lands in the anharmonic orbit of any set containing `λ z`. -/
theorem lambdaPunct_smul_mem_Kprime {K : Set Punctured} (g : SL(2, ℤ)) {z : ℍ}
    (hz : lambdaPunct z ∈ K) : lambdaPunct (g • z) ∈ Kprime K := by
  obtain ⟨φ, hφmem, hφeq⟩ := exists_anharm_eq g
  rw [hφeq z]
  exact Set.mem_iUnion.mpr ⟨⟨φ, hφmem⟩, Set.mem_image_of_mem _ hz⟩

/-- **The cusp height bound.** If `λ w ∈ K'` for a compact `K'` avoiding `0`, then `Im w ≤ M` for a uniform
`M`: since `λ → 0` as `Im → ∞` and `K'` is bounded away from `0`, large `Im` is impossible. -/
theorem cusp_height_bound {K : Set Punctured} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ w : ℍ, lambdaPunct w ∈ Kprime K → (w : ℂ).im ≤ M := by
  rcases (Kprime K).eq_empty_or_nonempty with hempty | hne
  · refine ⟨0, fun w hw => ?_⟩
    rw [hempty] at hw
    exact hw.elim
  set K'c : Set ℂ := Subtype.val '' (Kprime K) with hK'c
  have hK'c_cpt : IsCompact K'c := (isCompact_Kprime hK).image continuous_subtype_val
  have hK'c_ne : K'c.Nonempty := hne.image _
  obtain ⟨z₀, hz₀mem, hz₀min⟩ := hK'c_cpt.exists_isMinOn hK'c_ne continuous_norm.continuousOn
  have hz₀ne : z₀ ≠ 0 := by
    obtain ⟨p, hp, rfl⟩ := hz₀mem
    exact (mem_compl01.mp p.2).1
  set ε : ℝ := ‖z₀‖ with hεdef
  have hε : 0 < ε := by rw [hεdef]; exact norm_pos_iff.mpr hz₀ne
  have hεle : ∀ z ∈ K'c, ε ≤ ‖z‖ := fun z hz => hz₀min hz
  have hev : ∀ᶠ τ : ℂ in Filter.comap Complex.im Filter.atTop, ‖modularLambda τ‖ < ε := by
    have := tendsto_modularLambda_atImInfty.eventually (Metric.ball_mem_nhds (0 : ℂ) hε)
    filter_upwards [this] with τ hτ
    simpa [Metric.mem_ball, dist_eq_norm] using hτ
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  refine ⟨M, fun w hw => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hbound : ‖modularLambda (w : ℂ)‖ < ε := hM (w : ℂ).im hlt.le (w : ℂ) rfl
  have hmem : modularLambda (w : ℂ) ∈ K'c := ⟨lambdaPunct w, hw, rfl⟩
  exact absurd (hεle _ hmem) (not_le.mpr hbound)

/-- Continuity of a single `SL(2,ℤ)`-translation on `ℍ` (restriction of the continuous `SL(2,ℝ)`-action). -/
theorem continuous_sl2z_smul (c : SL(2, ℤ)) : Continuous (fun z : ℍ => c • z) := by
  have hfun : (fun z : ℍ => c • z) = (fun z : ℍ => castSL2R c • z) := rfl
  rw [hfun]; exact continuous_const_smul _

/-- **`λ̄ : ℍ/PΓ(2) → ℂ∖{0,1}` is a proper map.** Preimages of compacts are compact, by cusp escape plus
folding by the finite group `SL(2,ℤ)/Γ(2)`. See the file header. -/
theorem isProperMap_lambdaBar : IsProperMap lambdaBar := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_lambdaBar, fun K hK => ?_⟩
  haveI hnorm := Gamma_normal 2
  obtain ⟨M, hM⟩ := cusp_height_bound hK
  set S : Set ℍ := ModularGroup.truncatedFundamentalDomain M ∩ lambdaPunct ⁻¹' (Kprime K) with hSdef
  have hKpcl : IsClosed (Kprime K) := (isCompact_Kprime hK).isClosed
  have hScompact : IsCompact S :=
    (ModularGroup.isCompact_truncatedFundamentalDomain M).inter_right
      (hKpcl.preimage continuous_lambdaPunct)
  set RHS : Set (Quotient (MulAction.orbitRel (Gamma 2 ⧸ projKer) ℍ)) :=
    ⋃ (cq : SL(2, ℤ) ⧸ Gamma 2), (fun z => qmk (cq.out • z)) '' S with hRHSdef
  have hRHScompact : IsCompact RHS := by
    apply isCompact_iUnion
    intro cq
    exact hScompact.image (continuous_quotient_mk'.comp (continuous_sl2z_smul cq.out))
  have hclosed : IsClosed (lambdaBar ⁻¹' K) := hK.isClosed.preimage continuous_lambdaBar
  have hsub : lambdaBar ⁻¹' K ⊆ RHS := by
    intro y hy
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective y
    have hzK : lambdaPunct z ∈ K := hy
    obtain ⟨g, hgfd⟩ := ModularGroup.exists_smul_mem_fd z
    have hgK' : lambdaPunct (g • z) ∈ Kprime K := lambdaPunct_smul_mem_Kprime g hzK
    have hgim : (((g • z) : ℍ) : ℂ).im ≤ M := hM (g • z) hgK'
    have hgS : g • z ∈ S := ⟨⟨hgfd, hgim⟩, hgK'⟩
    set cq : SL(2, ℤ) ⧸ Gamma 2 := QuotientGroup.mk g⁻¹ with hcqdef
    set c : SL(2, ℤ) := cq.out with hcdef
    have hceq : (QuotientGroup.mk c : SL(2, ℤ) ⧸ Gamma 2) = QuotientGroup.mk g⁻¹ := by
      rw [hcdef]; exact Quotient.out_eq cq
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
    exact Set.mem_iUnion.mpr ⟨cq, g • z, hgS, hqeq⟩
  exact hRHScompact.of_isClosed_subset hclosed hsub

/-- **`λ̄ : ℍ/PΓ(2) → ℂ∖{0,1}` is a covering map** (unconditional). A proper local homeomorphism with
Hausdorff source is a covering; properness is `isProperMap_lambdaBar`, local-homeomorphy is
`isLocalHomeomorph_lambdaBar`. The modular curve `Y(2)` covers the thrice-punctured sphere. -/
theorem isCoveringMap_lambdaBar' : IsCoveringMap lambdaBar :=
  isCoveringMap_lambdaBar isProperMap_lambdaBar

/-- **`λ̄` is a FINITE-degree covering**: every fibre is finite (compact, since `λ̄` is proper, ∩ discrete,
since `λ̄` is a local homeomorphism). So `Y(2) → ℂ∖{0,1}` has finite degree — the key hypothesis making
the composition `λ = λ̄ ∘ q` reduce to a finite combine of the two coverings' even-coverings. -/
theorem lambdaBar_fibre_finite (w : Punctured) : (lambdaBar ⁻¹' {w}).Finite :=
  Set.finite_coe_iff.mp (fibre_finite isLocalHomeomorph_lambdaBar isProperMap_lambdaBar w)

/-- **`λ : ℍ → ℂ∖{0,1}` is a covering map** (unconditional). `λ = λ̄ ∘ q` factors as the composition of two
covering maps — the quotient covering `q : ℍ → ℍ/PΓ(2)` (`isCoveringMap_quotientMk_pgamma2`) and the
finite-degree modular covering `λ̄ : ℍ/PΓ(2) → ℂ∖{0,1}` (`isCoveringMap_lambdaBar'`) — and a composition of
covering maps with finite outer fibre is a covering map (`isCoveringMap_comp`, built from scratch). This is
`ℍ` exhibited as a covering space of the thrice-punctured sphere: the input the three-value Montel lift
(`#30`) consumes, with the degree-1/injectivity (argument-principle) crux entirely bypassed. -/
theorem isCoveringMap_lambdaPunct : IsCoveringMap lambdaPunct := by
  rw [← lambdaBar_comp_mk]
  exact isCoveringMap_comp isCoveringMap_quotientMk_pgamma2 isCoveringMap_lambdaBar' lambdaBar_fibre_finite

end Bottcher
