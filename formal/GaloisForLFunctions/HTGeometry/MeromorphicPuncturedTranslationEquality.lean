import GaloisForLFunctions.HTGeometry.MeromorphicPuncturedRepresentation
import GaloisForLFunctions.HTGeometry.AnalyticSubringFractionEvaluation

/-!
# From fraction-field translation identities to punctured-local identities

An equality in the global meromorphic fraction field between a punctured-local represented
element and a translation coboundary is converted into the corresponding punctured-local
identity of ordinary quotient functions.  This is the denominator-clearing bridge needed to
transport algebraic difference-differential identities to pole-orbit arguments.
-/

open Filter Set Topology Function Complex

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance puncturedTranslationEqualityDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

/-- A global fraction-field translation-coboundary identity implies the literal quotient
coboundary identity on the punctured neighborhood of every point. -/
theorem HasPuncturedMeromorphicRep.eq_shiftCoboundary_nhdsNE
    {x : meroField Set.univ} {φ : ℂ → ℂ} (hx : HasPuncturedMeromorphicRep x φ)
    (q : ℂ) {a b : analyticSubring Set.univ} (hb : b ≠ 0)
    {f g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfa : Germ.coeRingHom (𝓟 Set.univ) f = (a : Germ (𝓟 Set.univ) ℂ))
    (hgb : Germ.coeRingHom (𝓟 Set.univ) g = (b : Germ (𝓟 Set.univ) ℂ))
    (hfield : x =
      addTranslationMeroEquiv q
          (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
            algebraMap (analyticSubring Set.univ) (meroField Set.univ) b) -
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ) (meroField Set.univ) b) :
    ∀ z, φ =ᶠ[𝓝[≠] z]
      (fun w => f (w + q) / g (w + q) - f w / g w) := by
  obtain ⟨A, B, F, G, hB, hF, hG, hFA, hGB, hxfrac, hxev⟩ := hx
  have hmap_ne {c : analyticSubring Set.univ} (hc : c ≠ 0) :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) c ≠ 0 :=
    fun hz => hc ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using hz))
  have hTb : addTranslationAnalyticEquiv q b ≠ 0 :=
    fun hz => hb ((addTranslationAnalyticEquiv q).injective (by simpa using hz))
  have hcrossField := hfield
  rw [hxfrac, map_div₀, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap] at hcrossField
  field_simp [hmap_ne hB, hmap_ne hb, hmap_ne hTb] at hcrossField
  simp only [← map_mul, ← map_sub] at hcrossField
  have hcross :
      A * (addTranslationAnalyticEquiv q b * b) =
        B * (addTranslationAnalyticEquiv q a * b -
          a * addTranslationAnalyticEquiv q b) := by
    have hcross' := (IsFractionRing.injective
      (analyticSubring Set.univ) (meroField Set.univ)) hcrossField
    linear_combination hcross'
  have heval_A (z : ℂ) : univGermEval z (A : Germ (𝓟 Set.univ) ℂ) = F z := by
    rw [← hFA]
    rfl
  have heval_B (z : ℂ) : univGermEval z (B : Germ (𝓟 Set.univ) ℂ) = G z := by
    rw [← hGB]
    rfl
  have heval_a (z : ℂ) : univGermEval z (a : Germ (𝓟 Set.univ) ℂ) = f z := by
    rw [← hfa]
    rfl
  have heval_b (z : ℂ) : univGermEval z (b : Germ (𝓟 Set.univ) ℂ) = g z := by
    rw [← hgb]
    rfl
  have hcrossEval (z : ℂ) :
      F z * (g (z + q) * g z) =
        G z * (f (z + q) * g z - f z * g (z + q)) := by
    have hz := congrArg (fun c : analyticSubring Set.univ =>
      univGermEval z (c : Germ (𝓟 Set.univ) ℂ)) hcross
    simpa only [univGermEval_analyticSubring_mul,
      univGermEval_analyticSubring_sub,
      univGermEval_addTranslationAnalyticEquiv,
      heval_A, heval_B, heval_a, heval_b] using hz
  have hgshift : AnalyticOnNhd ℂ (fun z => g (z + q)) Set.univ :=
    hg.comp (analyticOnNhd_addTranslation q _) (Set.mapsTo_univ _ _)
  have hgbshift : Germ.coeRingHom (𝓟 Set.univ) (fun z => g (z + q)) =
      (addTranslationAnalyticEquiv q b : Germ (𝓟 Set.univ) ℂ) := by
    change Germ.ofFun (l := 𝓟 Set.univ) (fun z => g (z + q)) =
      (b : Germ (𝓟 Set.univ) ℂ).compTendsto (addTranslation q)
        (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _))
    rw [← hgb]
    rfl
  intro z
  have hGne := analyticSubring_rep_eventually_ne_zero hB hG hGB z
  have hgne := analyticSubring_rep_eventually_ne_zero hb hg hgb z
  have hgsne := analyticSubring_rep_eventually_ne_zero hTb hgshift hgbshift z
  filter_upwards [hxev z, hGne, hgne, hgsne] with w hxw hGw hgw hgsw
  have hce := hcrossEval w
  field_simp [hGw, hgw, hgsw] at hxw ⊢
  rw [hxw] at hce
  apply mul_left_cancel₀ hGw
  linear_combination hce

end

end GaloisForLFunctions
