import GaloisForLFunctions.AnalyticSubringEvaluation

/-!
# Punctured evaluation of global meromorphic fractions

A nonzero global analytic denominator is nonzero on a punctured neighborhood of every point.
Consequently equality in the fraction field gives equality of quotient representatives on every
punctured neighborhood.  This is the field-to-meromorphic-function bridge needed to transfer
global fraction identities to native meromorphic orders at poles.
-/

open Filter Set Topology

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance analyticSubringFractionEvaluationDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

/-- A representative of a nonzero global analytic germ is nonzero on the punctured neighborhood
of every point. -/
theorem analyticSubring_rep_eventually_ne_zero
    {b : analyticSubring (Set.univ : Set ℂ)} (hb : b ≠ 0)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    (hgb : Germ.coeRingHom (𝓟 Set.univ) g = (b : Germ (𝓟 Set.univ) ℂ))
    (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 := by
  apply (hg z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
  intro hlocal
  apply hb
  apply Subtype.ext
  rw [← hgb, ZeroMemClass.coe_zero]
  apply Germ.coe_eq.mpr
  have hall : Set.EqOn g 0 Set.univ :=
    hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hlocal
  exact eventually_principal.mpr hall

/-- Equality of two global meromorphic fractions gives equality of any chosen analytic quotient
representatives on the punctured neighborhood of every point. -/
theorem analyticSubring_fraction_eventuallyEq_of_field_eq
    {a b c d : analyticSubring (Set.univ : Set ℂ)}
    (hb : b ≠ 0) (hd : d ≠ 0)
    {f g u v : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Set.univ) (hv : AnalyticOnNhd ℂ v Set.univ)
    (hfa : Germ.coeRingHom (𝓟 Set.univ) f = (a : Germ (𝓟 Set.univ) ℂ))
    (hgb : Germ.coeRingHom (𝓟 Set.univ) g = (b : Germ (𝓟 Set.univ) ℂ))
    (huc : Germ.coeRingHom (𝓟 Set.univ) u = (c : Germ (𝓟 Set.univ) ℂ))
    (hvd : Germ.coeRingHom (𝓟 Set.univ) v = (d : Germ (𝓟 Set.univ) ℂ))
    (heq : algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) b =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) c /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) d)
    (z : ℂ) : (fun w => f w / g w) =ᶠ[𝓝[≠] z] (fun w => u w / v w) := by
  have hbF : algebraMap (analyticSubring Set.univ) (meroField Set.univ) b ≠ 0 :=
    fun h => hb ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using h))
  have hdF : algebraMap (analyticSubring Set.univ) (meroField Set.univ) d ≠ 0 :=
    fun h => hd ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using h))
  have hcrossF := (div_eq_div_iff hbF hdF).mp heq
  have hcross : a * d = c * b := by
    apply (IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
    simpa only [map_mul] using hcrossF
  have hcrossG := congrArg Subtype.val hcross
  change a.1 * d.1 = c.1 * b.1 at hcrossG
  rw [← hfa, ← hgb, ← huc, ← hvd] at hcrossG
  change Germ.ofFun (l := 𝓟 Set.univ) (fun w => f w * v w) =
    Germ.ofFun (l := 𝓟 Set.univ) (fun w => u w * g w) at hcrossG
  rw [Germ.coe_eq] at hcrossG
  have hgv := analyticSubring_rep_eventually_ne_zero hb hg hgb z
  have hvv := analyticSubring_rep_eventually_ne_zero hd hv hvd z
  filter_upwards [hgv, hvv] with w hgw hvw
  exact (div_eq_div_iff hgw hvw).2 (hcrossG (Set.mem_univ w))

end

end GaloisForLFunctions
