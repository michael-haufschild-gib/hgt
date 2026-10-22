import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHalfDensityFiniteXiJetRepairIndex

/-!
# Horizontal-anchor capacity of the half-density Xi-jet relation

The closed half-density realization has two independent directions: completion transports source
histories vertically, while an auxiliary record must resolve the horizontal ambiguity left inside a
source fibre.  For a finite off-line Xi packet, this file proves an exact capacity conservation law:

`visible horizontal-anchor rank + unresolved horizontal rank = total analytic Xi multiplicity`.

Consequently perfect vertical gluing does not compensate for a horizontal anchor of insufficient
rank.  Below total multiplicity there is a vertically constant two-level field whose horizontal
endpoints are distinct but indistinguishable to both source projection and proposed anchor.

This is a falsifiable quantitative consequence of the bidescent interpretation.  It does not prove
the source-forced horizontal vanishing law or RH.
-/

open Complex Filter Set Topology
open scoped Classical

namespace RHTower

noncomputable section

universe u

/-- Restriction of a proposed horizontal anchor to the source-invisible Xi-jet defect. -/
def deningerMeyerFiniteXiJetHorizontalAnchorRestriction
    (S : Finset XiDivisorSupport)
    (E : Type u) [AddCommGroup E] [Module ℂ E]
    (record : ↥(deningerMeyerFiniteXiJetClosedRelation S) →ₗ[ℂ] E) :
    deningerMeyerFiniteXiJetGraphVertical S →ₗ[ℂ] E :=
  record.comp
    ((LinearMap.ker (deningerMeyerFiniteXiJetClosedSourceProjection S)).subtype.comp
      (deningerMeyerFiniteXiJetVerticalToSourceKernel S))

/-- Exact capacity budget: visible anchor rank plus unresolved rank is Xi multiplicity. -/
theorem deningerMeyerFiniteXiJet_horizontalAnchor_rank_add_unresolvedRank
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2)
    (E : Type u) [AddCommGroup E] [Module ℂ E]
    (record : ↥(deningerMeyerFiniteXiJetClosedRelation S) →ₗ[ℂ] E) :
    Module.finrank ℂ
        (LinearMap.range
          (deningerMeyerFiniteXiJetHorizontalAnchorRestriction S E record)) +
      Module.finrank ℂ
        (LinearMap.ker
          (deningerMeyerFiniteXiJetHorizontalAnchorRestriction S E record)) =
      deningerMeyerFiniteXiTotalMultiplicity S := by
  calc
    _ = Module.finrank ℂ (deningerMeyerFiniteXiJetGraphVertical S) :=
      (deningerMeyerFiniteXiJetHorizontalAnchorRestriction S E record).finrank_range_add_finrank_ker
    _ = deningerMeyerFiniteXiTotalMultiplicity S :=
      finrank_deningerMeyerFiniteXiJetGraphVertical_of_offline S hoffline

/-- Every anchor coordinate omitted below Xi multiplicity remains as unresolved rank. -/
theorem deningerMeyerFiniteXiJet_horizontalAnchor_unresolvedRank_lower_bound
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2)
    (E : Type u) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (record : ↥(deningerMeyerFiniteXiJetClosedRelation S) →ₗ[ℂ] E) :
    deningerMeyerFiniteXiTotalMultiplicity S - Module.finrank ℂ E ≤
      Module.finrank ℂ
        (LinearMap.ker
          (deningerMeyerFiniteXiJetHorizontalAnchorRestriction S E record)) := by
  rw [Nat.sub_le_iff_le_add]
  calc
    deningerMeyerFiniteXiTotalMultiplicity S =
        Module.finrank ℂ
            (LinearMap.range
              (deningerMeyerFiniteXiJetHorizontalAnchorRestriction S E record)) +
          Module.finrank ℂ
            (LinearMap.ker
              (deningerMeyerFiniteXiJetHorizontalAnchorRestriction S E record)) :=
      (deningerMeyerFiniteXiJet_horizontalAnchor_rank_add_unresolvedRank
        S hoffline E record).symm
    _ ≤ Module.finrank ℂ E +
          Module.finrank ℂ
            (LinearMap.ker
              (deningerMeyerFiniteXiJetHorizontalAnchorRestriction S E record)) :=
      Nat.add_le_add_right
        (Submodule.finrank_le
          (LinearMap.range
            (deningerMeyerFiniteXiJetHorizontalAnchorRestriction S E record))) _
    _ = Module.finrank ℂ
            (LinearMap.ker
              (deningerMeyerFiniteXiJetHorizontalAnchorRestriction S E record)) +
          Module.finrank ℂ E := Nat.add_comm _ _

/-- A sub-multiplicity horizontal anchor leaves a genuine unresolved horizontal pair even inside
a perfectly vertically glued two-level field. -/
theorem deningerMeyerFiniteXiJet_exists_verticallyExact_unresolvedHorizontalPair
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2)
    (E : Type u) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (record : ↥(deningerMeyerFiniteXiJetClosedRelation S) →ₗ[ℂ] E)
    (hsmall : Module.finrank ℂ E < deningerMeyerFiniteXiTotalMultiplicity S) :
    ∃ F : Bool → Bool → ↥(deningerMeyerFiniteXiJetClosedRelation S),
      (∀ a₀ a₁ b, F a₀ b = F a₁ b) ∧
      (∀ a,
        deningerMeyerFiniteXiJetClosedSourceProjection S (F a false) =
          deningerMeyerFiniteXiJetClosedSourceProjection S (F a true)) ∧
      (∀ a, record (F a false) = record (F a true)) ∧
      F false false ≠ F false true := by
  let anchor :=
    deningerMeyerFiniteXiJetHorizontalAnchorRestriction S E record
  have hker : LinearMap.ker anchor ≠ ⊥ := by
    intro hbot
    have hinjective : Function.Injective anchor := LinearMap.ker_eq_bot.mp hbot
    have hle : Module.finrank ℂ (deningerMeyerFiniteXiJetGraphVertical S) ≤
        Module.finrank ℂ E :=
      LinearMap.finrank_le_finrank_of_injective hinjective
    rw [finrank_deningerMeyerFiniteXiJetGraphVertical_of_offline S hoffline] at hle
    exact (Nat.not_le_of_lt hsmall) hle
  obtain ⟨y, hyker, hyne⟩ := (Submodule.ne_bot_iff (LinearMap.ker anchor)).mp hker
  have hyzero : anchor y = 0 := LinearMap.mem_ker.mp hyker
  let vmap := deningerMeyerFiniteXiJetVerticalToSourceKernel S
  let uK := vmap y
  have huKne : uK ≠ 0 := by
    intro huKzero
    apply hyne
    apply (deningerMeyerFiniteXiJetVerticalToSourceKernel_bijective S).1
    simpa [uK] using huKzero
  have hune : uK.1 ≠ 0 := by
    intro huzero
    apply huKne
    exact Subtype.ext huzero
  have husource : deningerMeyerFiniteXiJetClosedSourceProjection S uK.1 = 0 :=
    uK.2
  have hurecord : record uK.1 = 0 := by
    simpa [anchor, deningerMeyerFiniteXiJetHorizontalAnchorRestriction, vmap, uK] using hyzero
  let F : Bool → Bool → ↥(deningerMeyerFiniteXiJetClosedRelation S) :=
    fun _ b => if b = true then uK.1 else 0
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro a₀ a₁ b
    rfl
  · intro a
    simp [F, husource]
  · intro a
    simp [F, hurecord]
  · simpa [F] using hune.symm

end
end RHTower
