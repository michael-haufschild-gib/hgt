/-
# u₀ transcendental at the Böttcher joint carrier `meroField`

The three `u0_phi_independence` theorems are stated over an abstract field `M ⊇ ℂ(z)` holding both
`u₀` and `φ_b`. The faithful carrier the Böttcher proof instantiates `M` by is
`Bottcher.meroField U` (fraction field of `Bottcher.analyticSubring U`, the analytic functions on a
connected open `U`), for `U` a deep ball in the common exterior — and that ball lies in `Ext`, so
`u₀` is analytic there and drops into the *same* carrier as `φ_b`.

This file discharges the `hTranscendental` hypothesis **at that real carrier**: it places `u₀` in
`Bottcher.analyticSubring U` for any `U ⊆ Ext` and proves it transcendental over `ℂ[z]`, by routing a
relation through the germ identity to a vanishing function on `U`, extending it to all of `Ext` by the
identity theorem (`isConnected_Ext`), and applying `u0_no_relation_ringHom`.

So of the two inputs to `q62_mixed` (`hTranscendental`, `mono`), the transcendence half is now
available at the carrier the named theorems instantiate over; the remaining `mono` (the dyadic
monodromy tower scaling `φ_b`, fixing the single-valued `u₀`) is the Böttcher-side analytic
construction. The field lift `ℂ[z] → ℂ(z)` is the standard `FractionRing`/`IsFractionRing` transfer
(demonstrated for the standalone carrier in `U0Transcendence.u0Field_transcendental`).
-/
import GaloisForLFunctions.U0.U0Transcendence
import GaloisForLFunctions.Bottcher.MeromorphicField
import GaloisForLFunctions.Bottcher.Q62Field
import GaloisForLFunctions.Bottcher.Q62

open Polynomial Filter Topology U0 U0NaturalBoundary U0Transcendence Bottcher

namespace U0MeroCarrier

variable {U : Set ℂ}

/-- `u₀` as an analytic germ on `U ⊆ Ext` — an element of the Böttcher joint carrier's domain
`analyticSubring U`. -/
noncomputable def u0AnSub (hU : U ⊆ Ext) : analyticSubring U :=
  ⟨(u0 : Germ (𝓟 U) ℂ), ⟨u0, u0_analyticOnNhd_Ext.mono hU, rfl⟩⟩

/-- ℂ[z]-algebra structure on the carrier domain via the Böttcher polynomial-germ hom `polyToAnalytic`
(hypothesis-free, valid for every `U`). -/
noncomputable instance algU : Algebra (Polynomial ℂ) (analyticSubring U) :=
  (polyToAnalytic U).toAlgebra

/-- The germ-level relation identity at the Böttcher carrier: the subtype image of `aeval (u0AnSub) P`
is the germ of the relation function `z ↦ P(z, u₀(z))` (= `evalU0 P`). -/
@[aesop safe]
theorem subtype_aeval (hU : U ⊆ Ext)
    (algInst : Algebra (Polynomial ℂ) (analyticSubring U))
    (halg : algebraMap (Polynomial ℂ) (analyticSubring U) = polyToAnalytic U)
    (P : (Polynomial ℂ)[X]) :
    (analyticSubring U).subtype (aeval (u0AnSub hU) P)
      = ((evalU0 P : ℂ → ℂ) : Germ (𝓟 U) ℂ) := by
  have lhs : (analyticSubring U).subtype (aeval (u0AnSub hU) P)
      = eval₂ ((Germ.coeRingHom (𝓟 U)).comp (RingHom.pi (fun z => Polynomial.evalRingHom z)))
          (u0 : Germ (𝓟 U) ℂ) P := by
    rw [aeval_def, hom_eval₂, halg]; rfl
  have rhs : ((evalU0 P : ℂ → ℂ) : Germ (𝓟 U) ℂ)
      = eval₂ ((Germ.coeRingHom (𝓟 U)).comp (RingHom.pi (fun z => Polynomial.evalRingHom z)))
          (u0 : Germ (𝓟 U) ℂ) P := by
    show Germ.coeRingHom (𝓟 U)
        (eval₂ (RingHom.pi (fun z => Polynomial.evalRingHom z)) u0 P) = _
    rw [hom_eval₂]; rfl
  rw [lhs, rhs]

/-- **`u₀` is transcendental over `ℂ[z]` in the Böttcher joint carrier (PROVEN).** For any connected
open infinite `U ⊆ Ext`, the germ `u0AnSub` satisfies no nonzero polynomial relation over `ℂ[z]`. This
is the `hTranscendental` input of the three `u0_phi_independence` theorems, discharged at the very
carrier `Bottcher.meroField`/`analyticSubring` they are instantiated over. -/
@[aesop safe]
theorem u0AnSub_transcendental (hUo : IsOpen U) (_hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUinf : U.Infinite) (hU : U ⊆ Ext) :
    Transcendental (Polynomial ℂ) (u0AnSub hU) := by
  rw [transcendental_iff]
  intro P hP
  have hsub := subtype_aeval hU algU (RingHom.algebraMap_toAlgebra _) P
  rw [hP, map_zero] at hsub
  have hgerm : ((evalU0 P : ℂ → ℂ) : Germ (𝓟 U) ℂ) = 0 := hsub.symm
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  have hUzero : ∀ z ∈ U, evalU0 P z = 0 := fun z hz => eventually_principal.mp hgerm z hz
  rcases Nat.eq_zero_or_pos P.natDegree with hd0 | hd1
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hd0]
    have hc : U ⊆ {x | (P.coeff 0).IsRoot x} := by
      intro z hz
      have hz2 := hUzero z hz
      rw [Polynomial.eq_C_of_natDegree_eq_zero hd0, evalU0_apply, eval₂_C, coe_evalRingHom] at hz2
      exact hz2
    rw [Polynomial.eq_zero_of_infinite_isRoot _ (hUinf.mono hc), map_zero]
  · refine (u0_no_relation_ringHom P hd1 ?_).elim
    have han : AnalyticOnNhd ℂ (evalU0 P) Ext := by
      have he : evalU0 P = fun z => P.eval₂ (evalRingHom z) (u0 z) := funext (evalU0_apply P)
      rw [he]; exact relation_analytic P
    obtain ⟨z₁, hz₁⟩ := hUne
    have hfreq : ∃ᶠ z in 𝓝[≠] z₁, evalU0 P z = 0 :=
      ((Filter.eventually_iff.mpr (Filter.mem_of_superset (hUo.mem_nhds hz₁)
        (fun z hz => hUzero z hz))).filter_mono nhdsWithin_le_nhds).frequently
    exact fun z hz => han.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isConnected_Ext.isPreconnected (hU hz₁) hfreq hz

/-- **u₀ transcendental over the field `ℂ(z)` in the joint carrier `meroField U` (PROVEN).** The field
form of `u0AnSub_transcendental` — exactly the `hTranscendental : Transcendental K u₀` input of
`q62_mixed`, at `K = ℂ(z) = RatFunc ℂ` and `M = Bottcher.meroField U` for any connected-open-infinite
`U ⊆ Ext`. Lift of the `ℂ[z]` transcendence through the injective `analyticSubring U ↪ meroField U`
(`transcendental_algHom_inj`) and the fraction-field transfer `IsFractionRing.isAlgebraic_iff`. With
this, instantiating the three `u0_phi_independence` theorems at `Bottcher.meroField (deepBall …)`
discharges `hTranscendental` outright; only `mono` (the dyadic monodromy tower) remains. -/
@[aesop safe]
theorem u0Mero_transcendental {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU : U ⊆ Ext) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU)) := by
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI algR : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  haveI tower : IsScalarTower (Polynomial ℂ) (RatFunc ℂ) (meroField U) := by
    apply IsScalarTower.of_algebraMap_eq
    intro p
    show algebraMap (Polynomial ℂ) (meroField U) p = (ratfuncToMero U hUo hUc hUne hUinf)
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
    rw [ratfuncToMero_algebraMap_polynomial]
    rfl
  have h1 : Transcendental (Polynomial ℂ)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU)) :=
    transcendental_algHom_inj (IsScalarTower.toAlgHom (Polynomial ℂ) (analyticSubring U) (meroField U))
      (FaithfulSMul.algebraMap_injective (analyticSubring U) (meroField U))
      (u0AnSub_transcendental hUo hUc hUne hUinf hU)
  exact (IsFractionRing.isAlgebraic_iff (Polynomial ℂ) (RatFunc ℂ) (meroField U)).not.mp h1

/-- **u₀ ⟂ φ_b at the real faithful carrier, conditional on `mono` alone (PROVEN).** The genuine
algebraic independence of the Böttcher coordinate `φ_b` and the c-velocity `u₀` over `ℂ(z)`, stated in
the meromorphic field `M = Bottcher.meroField U` where both are the *actual analytic functions* — so
`NoRelation` here *is* the real independence (`meroField` faithfulness). This is the `q62_mixed`
instantiation for the u₀ case: `hphib` is discharged by `Bottcher.phiMero_ne_zero`, and
`hTranscendental` by `u0Mero_transcendental`. The **only** remaining input is `mono` — the dyadic
monodromy scaling `φ_b` while fixing the single-valued `u₀` — i.e. the Böttcher `DyadicMonodromyTower`.
Compared to the abstract `u0_phi_independence_abstract`, this carries one hypothesis instead of two,
at the concrete carrier the named theorems are instantiated over. -/
@[aesop safe]
theorem u0_phib_independence_concrete (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ Ext)
    {b : ℂ} (hU_esc : U ⊆ escapeOpen b) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    (∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
      d < m ∧ orderOf ζ = m
      ∧ σ (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext))
        = algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)
      ∧ σ ζ = ζ ∧ σ (phiMero b hU_esc) = ζ * phiMero b hU_esc) →
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) := by
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI algR : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro monoF
  exact q62_mixed (phiMero b hU_esc)
    (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext))
    (phiMero_ne_zero hUo hUc hUne hU_esc)
    (u0Mero_transcendental hUo hUc hUne hUinf hU_ext) monoF

end U0MeroCarrier
