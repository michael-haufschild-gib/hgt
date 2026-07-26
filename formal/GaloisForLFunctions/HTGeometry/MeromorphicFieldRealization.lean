import GaloisForLFunctions.HTGeometry.AnalyticSubringFractionEvaluation
import GaloisForLFunctions.HTGeometry.MeromorphicEllipticCompositum
import GaloisForLFunctions.HTGeometry.EllipticClearedOrders
import GaloisForLFunctions.HTGeometry.EllipticPrincipalJet
import GaloisForLFunctions.HTGeometry.MeromorphicOrderLocalPeriod

/-!
# Realizing a translation-fixed meromorphic germ as a periodic function

An element of the global meromorphic field is a fraction of two entire germs, so it is represented
by an honest meromorphic function `A / B`.  This file transports the algebraic statement "the
element is fixed by the translation `q`" into the analytic statement "the canonical normal form of
`A / B` is periodic with period `q`", which is the exact hypothesis shape of the elliptic
differential-algebraicity theorem.

* **`fraction_eventually_periodic_of_addTranslationMeroEquiv_fixed`** — a translation-fixed
  fraction is periodic on a punctured neighbourhood of every point;
* **`periodic_toMeromorphicNFOn_of_eventually_punctured_meromorphic`** — punctured-local
  periodicity makes the canonical normal form periodic, with no analyticity hypothesis: at a pole
  the normal form takes the value `0` on both sides, and the orders agree because meromorphic order
  ignores the value at the centre.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance meromorphicFieldRealizationDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicFieldRealizationDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-! ## Translated representatives -/

/-- A translated entire function represents the translated germ. -/
theorem addTranslationAnalyticEquiv_rep (q : ℂ) {a : analyticSubring (Set.univ : Set ℂ)}
    {A : ℂ → ℂ} (hA : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) A = (a : Germ (𝓟 Set.univ) ℂ)) :
    Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (fun z => A (z + q)) =
      ((addTranslationAnalyticEquiv q a : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ) := by
  change _ = ((precompAnalytic (analyticOnNhd_addTranslation q _)
    (Set.mapsTo_univ _ _) a : analyticSubring (Set.univ : Set ℂ)) :
      Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
  rw [precompAnalytic_coe, ← hA]
  change (↑(fun z => A (z + q)) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) =
    (↑A : Germ (𝓟 (Set.univ : Set ℂ)) ℂ).compTendsto (addTranslation q)
      (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _))
  rw [Germ.coe_compTendsto]
  rfl

/-- Translation of entire functions preserves entirety. -/
theorem analyticOnNhd_comp_addTranslation {A : ℂ → ℂ}
    (hA : AnalyticOnNhd ℂ A (Set.univ : Set ℂ)) (q : ℂ) :
    AnalyticOnNhd ℂ (fun z => A (z + q)) (Set.univ : Set ℂ) :=
  hA.comp (analyticOnNhd_id.add analyticOnNhd_const) (Set.mapsTo_univ _ _)

/-! ## From a fixed germ to a punctured-local functional period -/

/-- **A translation-fixed meromorphic germ has punctured-locally periodic representatives.**  The
algebraic identity `σ_q x = x` cross-multiplies to an identity of entire germs, which is a genuine
pointwise identity; dividing back is legitimate off the isolated zeros of the denominator. -/
theorem fraction_eventually_periodic_of_addTranslationMeroEquiv_fixed (q : ℂ)
    {a b : analyticSubring (Set.univ : Set ℂ)} (hb : b ≠ 0)
    {A B : ℂ → ℂ} (hB : AnalyticOnNhd ℂ B (Set.univ : Set ℂ))
    (hAa : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) A = (a : Germ (𝓟 Set.univ) ℂ))
    (hBb : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) B = (b : Germ (𝓟 Set.univ) ℂ))
    (hfix : addTranslationMeroEquiv q
        (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
          algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b) =
      algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b)
    (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, A (w + q) / B (w + q) = A w / B w := by
  have hσb0 : addTranslationAnalyticEquiv q b ≠ 0 := by
    intro h
    apply hb
    have := congrArg (addTranslationAnalyticEquiv q).symm h
    rwa [RingEquiv.symm_apply_apply, map_zero] at this
  have heq :
      algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
          (addTranslationAnalyticEquiv q a) /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
          (addTranslationAnalyticEquiv q b) =
      algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b := by
    rw [← addTranslationMeroEquiv_algebraMap q a, ← addTranslationMeroEquiv_algebraMap q b,
      ← map_div₀]
    exact hfix
  exact analyticSubring_fraction_eventuallyEq_of_field_eq hσb0 hb
    (analyticOnNhd_comp_addTranslation hB q) hB
    (addTranslationAnalyticEquiv_rep q hAa) (addTranslationAnalyticEquiv_rep q hBb)
    hAa hBb heq z

/-! ## Punctured-local periodicity gives a periodic normal form -/

/-- **The canonical normal form of a punctured-locally periodic meromorphic function is
periodic.**  No analyticity is assumed: where the function is regular the two sides agree by
continuity, and at a pole both sides are the normal-form value `0`, since meromorphic order is
insensitive to the value at the centre and therefore transports along the period. -/
theorem periodic_toMeromorphicNFOn_of_eventually_punctured_meromorphic
    {f : ℂ → ℂ} (hf : MeromorphicOn f (Set.univ : Set ℂ)) (p : ℂ)
    (hlocal : ∀ z, ∀ᶠ w in 𝓝[≠] z, f (w + p) = f w) :
    Function.Periodic (toMeromorphicNFOn f (Set.univ : Set ℂ)) p := by
  set F := toMeromorphicNFOn f (Set.univ : Set ℂ) with hFdef
  have hNF : MeromorphicNFOn F (Set.univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  have hord : ∀ w : ℂ, meromorphicOrderAt F w = meromorphicOrderAt f w := fun w => by
    rw [hFdef, meromorphicOrderAt_toMeromorphicNFOn hf (Set.mem_univ w)]
  intro z
  have hordeq : meromorphicOrderAt F (z + p) = meromorphicOrderAt F z := by
    rw [hord, hord]
    exact meromorphicOrderAt_add_eq_of_eventually_periodic (hlocal z)
  have htend : Filter.Tendsto (fun w : ℂ => w + p) (𝓝[≠] z) (𝓝[≠] (z + p)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((by fun_prop : Continuous fun w : ℂ => w + p).tendsto z).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw ⊢
      exact fun hcon => hw (by linear_combination hcon)
  have hFshift : (fun w => F (w + p)) =ᶠ[𝓝[≠] z] F := by
    have h1 : (fun w => F (w + p)) =ᶠ[𝓝[≠] z] fun w => f (w + p) :=
      (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ (z + p))).comp_tendsto htend
    have h2 : (fun w => f (w + p)) =ᶠ[𝓝[≠] z] f := hlocal z
    have h3 : f =ᶠ[𝓝[≠] z] F :=
      (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)).symm
    exact (h1.trans h2).trans h3
  rcases lt_or_ge (meromorphicOrderAt F z) 0 with hneg | hnonneg
  · have h1 : F z = 0 := eq_zero_of_meromorphicOrderAt_neg (hNF (Set.mem_univ z)) hneg
    have h2 : F (z + p) = 0 :=
      eq_zero_of_meromorphicOrderAt_neg (hNF (Set.mem_univ (z + p))) (hordeq.trans_lt hneg)
    rw [h1, h2]
  · have ha1 : AnalyticAt ℂ F z :=
      (hNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hnonneg
    have ha2 : AnalyticAt ℂ F (z + p) :=
      (hNF (Set.mem_univ (z + p))).meromorphicOrderAt_nonneg_iff_analyticAt.mp
        (hordeq.symm ▸ hnonneg)
    have hc1 : ContinuousAt (fun w => F (w + p)) z :=
      ContinuousAt.comp (g := F) (f := fun w : ℂ => w + p) (x := z) ha2.continuousAt
        (by fun_prop)
    exact (eventuallyEq_nhds_of_nhdsNE_of_continuousAt hFshift hc1
      ha1.continuousAt).eq_of_nhds

end

end GaloisForLFunctions.HTGeometry
