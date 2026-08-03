import GaloisForLFunctions.HTGeometry.PuncturedRepresentativeUniqueness
import GaloisForLFunctions.HTGeometry.MeromorphicTranslation

/-!
# Punctured representatives of the pieces of a ladder identity

Two constructions produce the representatives a ladder identity is built from.

*The logarithmic derivative of an entire germ* is represented by `f'/f`, because the derivation of
the field restricts to differentiation of the analytic germs.

*A translate* is represented by the translated function, because translation of the field is
precomposition on the germs and the punctured neighbourhood of a point is carried to the punctured
neighbourhood of its translate.

Together with the uniqueness of a punctured representative, these turn a pointwise ladder identity,
valid off the poles, into an identity in the meromorphic differential field.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

attribute [local instance] puncturedRepDomain puncturedRepComplexAlgebraAnalytic
  puncturedRepComplexAlgebraMero puncturedRepDifferential

/-! ## The logarithmic derivative of an entire germ -/

/-- **The logarithmic derivative of an entire germ is represented by `f'/f`.** -/
theorem hasPuncturedMeromorphicRep_logDeriv {a : analyticSubring (Set.univ : Set ℂ)} (ha : a ≠ 0)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hfa : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) f = (a : Germ _ ℂ)) :
    HasPuncturedMeromorphicRep
      (Differential.logDeriv (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a))
      (fun z => deriv f z / f z) := by
  have hderiv : (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a)′
      = algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (analyticSubringDeriv isOpen_univ a) :=
    meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ Set.univ_nonempty a
  have hlog : Differential.logDeriv
      (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a)
      = algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (analyticSubringDeriv isOpen_univ a) /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) a := by
    rw [Differential.logDeriv, hderiv]
  rw [hlog]
  refine hasPuncturedMeromorphicRep_fraction ha hf.deriv hf ?_ hfa
  rw [analyticSubringDeriv_coe, ← hfa]
  rfl

/-! ## Translates -/

theorem tendsto_nhdsNE_add (q z : ℂ) :
    Filter.Tendsto (fun w : ℂ => w + q) (𝓝[≠] z) (𝓝[≠] (z + q)) := by
  refine Filter.Tendsto.inf ?_ ?_
  · exact (continuous_add_const q).continuousAt
  · refine Filter.tendsto_principal_principal.mpr fun w hw => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw ⊢
    intro hcon
    exact hw (by linear_combination hcon)

/-- **A translate is represented by the translated function.** -/
theorem HasPuncturedMeromorphicRep.translate {x : meroField (Set.univ : Set ℂ)} {φ : ℂ → ℂ}
    (q : ℂ) (hx : HasPuncturedMeromorphicRep x φ) :
    HasPuncturedMeromorphicRep (addTranslationMeroEquiv q x) (fun z => φ (z + q)) := by
  obtain ⟨a, b, f, g, hb, hf, hg, hfa, hgb, hxeq, hxev⟩ := hx
  refine ⟨addTranslationAnalyticEquiv q a, addTranslationAnalyticEquiv q b,
    fun z => f (z + q), fun z => g (z + q), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon
    exact hb ((addTranslationAnalyticEquiv q).injective (by rw [hcon, map_zero]))
  · exact hf.comp (analyticOnNhd_addTranslation q _) (Set.mapsTo_univ _ _)
  · exact hg.comp (analyticOnNhd_addTranslation q _) (Set.mapsTo_univ _ _)
  · have hco : ((addTranslationAnalyticEquiv q a : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
        = (a : Germ (𝓟 (Set.univ : Set ℂ)) ℂ).compTendsto (addTranslation q)
          (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) := rfl
    rw [hco, ← hfa]
    rfl
  · have hco : ((addTranslationAnalyticEquiv q b : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
        = (b : Germ (𝓟 (Set.univ : Set ℂ)) ℂ).compTendsto (addTranslation q)
          (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) := rfl
    rw [hco, ← hgb]
    rfl
  · rw [hxeq, map_div₀, addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap]
  · intro z
    exact (hxev (z + q)).comp_tendsto (tendsto_nhdsNE_add q z)

/-! ## Differences -/

/-- Punctured-local representatives are closed under subtraction. -/
theorem HasPuncturedMeromorphicRep.sub {x y : meroField (Set.univ : Set ℂ)} {φ ψ : ℂ → ℂ}
    (hx : HasPuncturedMeromorphicRep x φ) (hy : HasPuncturedMeromorphicRep y ψ) :
    HasPuncturedMeromorphicRep (x - y) fun z => φ z - ψ z := by
  have h := hx.add (hy.const_mul (-1))
  have hconst : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (constToAnalytic Set.univ (-1)) = -1 := by
    rw [map_neg, map_one, map_neg, map_one]
  rw [hconst] at h
  have hval : x + -1 * y = x - y := by ring
  rw [hval] at h
  refine h.congr_fun fun _ => Filter.Eventually.of_forall fun w => ?_
  show φ w + -1 * ψ w = φ w - ψ w
  ring

/-! ## Rational functions -/

/-- **A rational function is represented by its numerator over its denominator.** -/
theorem hasPuncturedMeromorphicRep_ratfuncToMero (r : RatFunc ℂ) :
    HasPuncturedMeromorphicRep
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
        Set.infinite_univ r)
      (fun z => r.num.eval z / r.denom.eval z) := by
  have hden : polyToAnalytic (Set.univ : Set ℂ) r.denom ≠ 0 := by
    intro hcon
    exact r.denom_ne_zero
      (polyToAnalytic_injective Set.univ Set.infinite_univ (by rw [hcon, map_zero]))
  have hval : ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
        Set.infinite_univ r
      = algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ r.num) /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ r.denom) := by
    conv_lhs => rw [← RatFunc.num_div_denom r]
    rw [map_div₀, ratfuncToMero_algebraMap_polynomial, ratfuncToMero_algebraMap_polynomial]
    rfl
  rw [hval]
  exact hasPuncturedMeromorphicRep_fraction hden (analyticOnNhd_polyEval _ r.num)
    (analyticOnNhd_polyEval _ r.denom) rfl rfl

/-- **A rational punctured representative identifies the element as a rational function.**  This is
what makes a correction term proved rational off the poles into an element of the coordinate field,
hence differentially algebraic. -/
theorem eq_ratfuncToMero_of_hasPuncturedMeromorphicRep_ratio {x : meroField (Set.univ : Set ℂ)}
    {p q : Polynomial ℂ} (hq : q ≠ 0)
    (hx : HasPuncturedMeromorphicRep x (fun z => p.eval z / q.eval z)) :
    x = ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) q) := by
  have hqA : polyToAnalytic (Set.univ : Set ℂ) q ≠ 0 := by
    intro hcon
    exact hq (polyToAnalytic_injective Set.univ Set.infinite_univ (hcon.trans (map_zero _).symm))
  have hval : ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
        Set.infinite_univ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p /
          algebraMap (Polynomial ℂ) (RatFunc ℂ) q)
      = algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ p) /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ q) := by
    rw [map_div₀, ratfuncToMero_algebraMap_polynomial, ratfuncToMero_algebraMap_polynomial]
    rfl
  refine eq_of_hasPuncturedMeromorphicRep hx ?_
  rw [hval]
  exact hasPuncturedMeromorphicRep_fraction hqA (analyticOnNhd_polyEval _ p)
    (analyticOnNhd_polyEval _ q) rfl rfl

end

end GaloisForLFunctions
