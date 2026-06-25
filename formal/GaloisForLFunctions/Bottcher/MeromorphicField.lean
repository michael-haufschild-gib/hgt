/-
# The meromorphic function field on a connected open set

The faithful carrier field for the q62 instantiation. `q62_independence` is stated over an abstract
field `M` holding the Böttcher coordinates; to make it unconditional we must instantiate `M` by a
*genuine* field containing the actual `φ_c` as functions (not a toy with formally-independent
variables). For the connected case `φ_c` is single-valued analytic on the exterior `Ω_c`, so the
right `M` is the field of meromorphic functions on a connected open `U ⊆ Ω_c`.

Construction (constraint, not flow — the field is fixed by the identity theorem, no generative rule):
* `analyticSubring U` — the analytic functions on `U`, realized as germs modulo agreement on `U`
  (`Germ (𝓟 U) ℂ`); a subring of the germ ring.
* `isDomain_analyticSubring` — it is an **integral domain** when `U` is connected (open, nonempty):
  no nonzero zero-divisors is exactly the identity theorem (`analyticOnNhd_domain`).
* `FractionRing (analyticSubring U)` — its fraction field is the **meromorphic function field** on
  `U`; a `Field` once the domain property is in scope. `ℂ(z)` embeds (rational = poly / poly), and
  `φ_c` lives in it as the germ of the genuine Böttcher coordinate.
-/
import GaloisForLFunctions.Bottcher.AnalyticDomain
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.FieldTheory.RatFunc.Basic

open Filter Topology Set Polynomial Function

namespace Bottcher

variable (U : Set ℂ)

/-- The subring of `Germ (𝓟 U) ℂ` of germs having an analytic-on-`U` representative: the ring of
analytic functions on `U`, realized modulo agreement on `U`. Closed under `+, *, -` and contains the
constants, since these operations preserve analyticity. -/
def analyticSubring : Subring (Germ (𝓟 U) ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ (Germ.coeRingHom (𝓟 U) f) = g}
  mul_mem' := by rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f * g, hf.mul hg, by rw [map_mul]⟩
  one_mem' := ⟨1, analyticOnNhd_const, map_one _⟩
  add_mem' := by rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f + g, hf.add hg, by rw [map_add]⟩
  zero_mem' := ⟨0, analyticOnNhd_const, map_zero _⟩
  neg_mem' := by rintro a ⟨f, hf, rfl⟩; exact ⟨-f, hf.neg, by rw [map_neg]⟩

/-- **The analytic functions on a connected open set form an integral domain.** No nonzero
zero-divisors is the identity theorem (`analyticOnNhd_domain`: a product vanishing on connected `U`
forces a factor to vanish); nontrivial because `U ≠ ∅` makes the constants `0, 1` distinct germs.
The carrier ring whose fraction field is the meromorphic function field on `U`. -/
theorem isDomain_analyticSubring (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    IsDomain (analyticSubring U) := by
  haveI hnb : (𝓟 U).NeBot := principal_neBot_iff.mpr hUne
  haveI hnt : Nontrivial (analyticSubring U) := by
    refine ⟨0, 1, ?_⟩
    intro h
    have hv := congrArg (Subtype.val) h
    rw [ZeroMemClass.coe_zero, OneMemClass.coe_one] at hv
    exact zero_ne_one hv
  haveI hnzd : NoZeroDivisors (analyticSubring U) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have hval : (a : Germ (𝓟 U) ℂ) * (b : Germ (𝓟 U) ℂ) = 0 := by
      have h2 := congrArg (Subtype.val) hab
      rwa [MulMemClass.coe_mul, ZeroMemClass.coe_zero] at h2
    have hfa' : (a : Germ (𝓟 U) ℂ) = (↑f : Germ (𝓟 U) ℂ) := hfa.symm
    have hgb' : (b : Germ (𝓟 U) ℂ) = (↑g : Germ (𝓟 U) ℂ) := hgb.symm
    rw [hfa', hgb', ← Germ.coe_mul, ← Germ.coe_zero, Germ.coe_eq] at hval
    have heq : EqOn (fun x => f x * g x) 0 U := fun x hx => eventually_principal.mp hval x hx
    rcases analyticOnNhd_domain hf hg hUc hUo heq with h0 | h0
    · left
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, hfa', ← Germ.coe_zero, Germ.coe_eq]
      exact eventually_principal.mpr h0
    · right
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, hgb', ← Germ.coe_zero, Germ.coe_eq]
      exact eventually_principal.mpr h0
  exact NoZeroDivisors.to_isDomain _

/-- The **meromorphic function field on `U`**: the fraction field of the analytic-function domain.
This is the faithful carrier `M` for the q62 instantiation — it contains the genuine Böttcher
coordinates as germs and `ℂ(z)` as fractions of polynomials. It is a `Field` whenever `U` is
connected, open and nonempty: under `letI := isDomain_analyticSubring U hUo hUc hUne`, the `Field`
instance on `FractionRing` of a domain is found by `inferInstance` (Field-2). -/
abbrev meroField : Type := FractionRing (analyticSubring U)

/-- Confirmation (Field-2): with the domain property in scope, `meroField U` has a `Field`
structure — `FractionRing` of an integral domain is a field. -/
example (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    Nonempty (Field (meroField U)) :=
  letI := isDomain_analyticSubring U hUo hUc hUne
  ⟨inferInstance⟩

/-! ## Field-3: the base field `ℂ(z)` embeds in `M`

`K = ℂ(z) = RatFunc ℂ` embeds into the meromorphic field `M = meroField U` (rational = poly / poly).
Built bottom-up: polynomials map to their eval-function germs (`polyToAnalytic`), injectively when
`U` is infinite (a polynomial vanishing on an infinite set is `0`); composing with the fraction-field
map and lifting through the universal property of `RatFunc ℂ = FractionRing ℂ[X]` gives the field
embedding `ratfuncToMero : ℂ(z) ↪ M`. -/

/-- A polynomial's evaluation function `z ↦ p(z)` is analytic on `U` (it is entire). -/
theorem analyticOnNhd_polyEval (p : Polynomial ℂ) :
    AnalyticOnNhd ℂ (fun z => p.eval z) U := by
  have h : AnalyticOnNhd ℂ (fun z => aeval z p) (univ : Set ℂ) := analyticOnNhd_id.aeval_polynomial p
  have heq : (fun z => aeval z p) = (fun z => p.eval z) := by
    funext z; simp [aeval_def, eval₂_at_apply]
  rw [heq] at h; exact h.mono (subset_univ U)

/-- The ring hom `ℂ[X] →+* analyticSubring U`, sending a polynomial to the germ of its evaluation
function `z ↦ p(z)`. -/
noncomputable def polyToAnalytic : Polynomial ℂ →+* analyticSubring U :=
  ((Germ.coeRingHom (𝓟 U)).comp (Pi.ringHom (fun z => Polynomial.evalRingHom z))).codRestrict
    (analyticSubring U) (fun p => ⟨fun z => p.eval z, analyticOnNhd_polyEval U p, rfl⟩)

/-- `polyToAnalytic` is **injective** when `U` is infinite: a polynomial whose evaluation vanishes on
the infinite set `U` has infinitely many roots, hence is the zero polynomial. -/
theorem polyToAnalytic_injective (hUinf : U.Infinite) : Injective (polyToAnalytic U) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hgerm : (↑(fun z => p.eval z) : Germ (𝓟 U) ℂ) = 0 := by
    have h2 := congrArg (Subtype.val) hp
    rwa [ZeroMemClass.coe_zero] at h2
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  have hroots : U ⊆ {x | p.IsRoot x} := fun z hz => eventually_principal.mp hgerm z hz
  exact Polynomial.eq_zero_of_infinite_isRoot p (hUinf.mono hroots)

/-- `ℂ[X] →+* M`: polynomials as meromorphic functions (composition with the fraction-field map). -/
noncomputable def polyToMero : Polynomial ℂ →+* meroField U :=
  (algebraMap (analyticSubring U) (meroField U)).comp (polyToAnalytic U)

/-- `polyToMero` is injective (composite of `polyToAnalytic_injective` and the fraction-field map). -/
theorem polyToMero_injective (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUinf : U.Infinite) : Injective (polyToMero U) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  exact (IsFractionRing.injective (analyticSubring U) (meroField U)).comp
    (polyToAnalytic_injective U hUinf)

/-- **`K = ℂ(z) ↪ M`**: the ring embedding of the base field `RatFunc ℂ` into the meromorphic field
`M = meroField U`, by lifting the injective `polyToMero` through the universal property of
`RatFunc ℂ = FractionRing ℂ[X]`. The base field of the q62 statement living inside the carrier. -/
noncomputable def ratfuncToMero (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUinf : U.Infinite) : RatFunc ℂ →+* meroField U :=
  haveI := isDomain_analyticSubring U hUo hUc hUne
  IsFractionRing.lift (polyToMero_injective U hUo hUc hUne hUinf)

/-! ## Field-5 bridge: the base-field embedding agrees with the polynomial eval-germ

A step toward connected-case faithfulness: a relation `P(φ_{c₁},φ_{c₂})=0` over `K=ℂ(z)` evaluated in
`M` corresponds to the genuine meromorphic function `z ↦ P(z,φ_{c₁}(z),φ_{c₂}(z))` on `U` — so
`NoRelation` over `M` *is* the actual independence. This lemma is the coefficient step: the embedding
`ℂ(z)↪M` sends a polynomial to its real eval-germ. -/

/-- The `ℂ(z)↪M` embedding (`ratfuncToMero`) agrees with `polyToMero` on polynomials: a polynomial
coefficient `p(z)` of a relation maps, under the base-field embedding, to the genuine eval-germ
`z ↦ p(z)` in `M`. (`IsFractionRing.lift_algebraMap`.) -/
theorem ratfuncToMero_algebraMap_polynomial (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (p : Polynomial ℂ) :
    ratfuncToMero U hUo hUc hUne hUinf (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = polyToMero U p := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  exact IsFractionRing.lift_algebraMap (polyToMero_injective U hUo hUc hUne hUinf) p

/-- **Element-level faithfulness**: an analytic-germ element maps to `0` in `M` iff it is already `0`
in the carrier domain (the fraction-field map is injective). -/
theorem meroField_algebraMap_eq_zero_iff (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (x : analyticSubring U) :
    algebraMap (analyticSubring U) (meroField U) x = 0 ↔ x = 0 := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  rw [← map_zero (algebraMap (analyticSubring U) (meroField U))]
  exact (IsFractionRing.injective (analyticSubring U) (meroField U)).eq_iff

/-- **Function-level faithfulness**: for `f` analytic on `U`, its image in `M` is `0` iff `f` vanishes
on `U`. A meromorphic element of `M` is thus determined by its function — so `NoRelation` over `M` is
the genuine statement about the actual functions, not a formal artefact. This is the faithfulness
that makes the connected-case `meroField`/`phiMero` instantiation non-circular: proving `NoRelation`
in `M` *is* proving the actual algebraic independence of the Böttcher coordinates on `U`. -/
theorem meroField_germ_eq_zero_iff (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    algebraMap (analyticSubring U) (meroField U) ⟨Germ.coeRingHom (𝓟 U) f, ⟨f, hf, rfl⟩⟩ = 0
      ↔ EqOn f 0 U := by
  rw [meroField_algebraMap_eq_zero_iff U hUo hUc hUne]
  constructor
  · intro h
    have hg : (Germ.coeRingHom (𝓟 U) f) = (0 : Germ (𝓟 U) ℂ) := by
      have := congrArg Subtype.val h; rwa [ZeroMemClass.coe_zero] at this
    rw [show Germ.coeRingHom (𝓟 U) f = (↑f : Germ (𝓟 U) ℂ) from rfl, ← Germ.coe_zero, Germ.coe_eq]
      at hg
    exact fun z hz => eventually_principal.mp hg z hz
  · intro h
    apply Subtype.ext
    show (↑f : Germ (𝓟 U) ℂ) = 0
    rw [← Germ.coe_zero, Germ.coe_eq]
    exact eventually_principal.mpr h

/-- The constant ring hom `ℂ →+* analyticSubring U`: `a ↦` germ of the constant function `a`. The
scalar embedding of the carrier, used to evaluate `ℂ`-coefficients of a relation. -/
noncomputable def constToAnalytic (U : Set ℂ) : ℂ →+* analyticSubring U :=
  ((Germ.coeRingHom (𝓟 U)).comp (Pi.ringHom (fun _ : ℂ => RingHom.id ℂ))).codRestrict
    (analyticSubring U) (fun a => ⟨fun _ => a, analyticOnNhd_const, rfl⟩)

/-- **Meromorphic faithfulness (fraction form).** For `a, b` analytic germs with `b ≠ 0`, the
meromorphic element `a/b ∈ M` is `0` iff the numerator `a = 0`. The building block that reduces a
`ℂ(z)`-coefficient (meromorphic) `NoRelation` evaluation to the vanishing of its analytic numerator,
where the bivariate faithfulness applies. -/
theorem meroField_div_eq_zero_iff [IsDomain (analyticSubring U)] (a b : analyticSubring U)
    (hb : b ≠ 0) :
    (algebraMap (analyticSubring U) (meroField U) a)
      / (algebraMap (analyticSubring U) (meroField U) b) = 0 ↔ a = 0 := by
  have hinj := IsFractionRing.injective (analyticSubring U) (meroField U)
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact hinj (h.trans (map_zero _).symm)
    · exact absurd (hinj (h.trans (map_zero _).symm)) hb
  · intro h; left; rw [h, map_zero]

/-- **Clearing denominators.** The base-field embedding of a rational function `r ∈ ℂ(z)` into `M`
equals the meromorphic germ `polyToMero(num r) / polyToMero(denom r)` — numerator and denominator as
genuine eval-germs. With `meroField_div_eq_zero_iff`, this reduces a `ℂ(z)`-coefficient relation to
its analytic numerator, where the bivariate faithfulness applies. -/
theorem ratfuncToMero_eq_div [IsDomain (analyticSubring U)]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite) (r : RatFunc ℂ) :
    ratfuncToMero U hUo hUc hUne hUinf r = polyToMero U r.num / polyToMero U r.denom := by
  conv_lhs => rw [← RatFunc.num_div_denom r]
  rw [map_div₀, ratfuncToMero_algebraMap_polynomial, ratfuncToMero_algebraMap_polynomial]

end Bottcher

namespace Bottcher

/-- **Precomposition by an analytic self-map preserves the analytic-germ domain.** If `g` is analytic
on `U` and maps `U` into `U`, then for any analytic germ `a ∈ analyticSubring U`, the precomposition
`a ∘ g` (`Germ.compTendsto`) is again in `analyticSubring U` — composition of analytic functions is
analytic. This is the well-definedness of the deck/monodromy operator on the **domain** carrier
`analyticSubring`/`meroField` (the identity-theorem field), the carrier on which the scaling
automorphism `σ` that `hDisc` needs can actually live — unlike the principal-filter `coverGerm`, which
is `ℂ^S` and is never a domain. The deck automorphism is exactly such a precomposition by a
self-biholomorphism of a connected `U`. -/
theorem precomp_mem_analyticSubring {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U U) {a : Germ (𝓟 U) ℂ} (ha : a ∈ analyticSubring U) :
    a.compTendsto g (tendsto_principal_principal.mpr hmaps) ∈ analyticSubring U := by
  obtain ⟨f, hf, rfl⟩ := ha
  exact ⟨f ∘ g, hf.comp hg hmaps,
    (Germ.coe_compTendsto f (tendsto_principal_principal.mpr hmaps)).symm⟩

end Bottcher

namespace Bottcher

/-- Precomposition by a self-map `g` (as a `Tendsto` on `𝓟 U`) as a **ring endomorphism** of the germ
ring `Germ (𝓟 U) ℂ`: `a ↦ a ∘ g`. Composition is a ring hom because it is so pointwise. -/
noncomputable def precompGermHom {U : Set ℂ} {g : ℂ → ℂ} (h : Tendsto g (𝓟 U) (𝓟 U)) :
    Germ (𝓟 U) ℂ →+* Germ (𝓟 U) ℂ where
  toFun a := a.compTendsto g h
  map_one' := by rw [← Germ.coe_one, Germ.coe_compTendsto]; rfl
  map_zero' := by rw [← Germ.coe_zero, Germ.coe_compTendsto]; rfl
  map_mul' a b := by
    induction a using Germ.inductionOn with
    | _ F => induction b using Germ.inductionOn with
      | _ G => simp only [← Germ.coe_mul, Germ.coe_compTendsto]; rfl
  map_add' a b := by
    induction a using Germ.inductionOn with
    | _ F => induction b using Germ.inductionOn with
      | _ G => simp only [← Germ.coe_add, Germ.coe_compTendsto]; rfl

/-- **The deck/monodromy operator as a ring endomorphism of the analytic-germ domain.** For `g`
analytic on `U` with `g(U) ⊆ U`, precomposition `a ↦ a ∘ g` is a ring endomorphism of
`analyticSubring U` (well-defined by `precomp_mem_analyticSubring`, ring hom by `precompGermHom`). When
`g` is a self-biholomorphism this upgrades to an automorphism (next step) and lifts to a `meroField U`
field automorphism — the genuine carrier for the scaling automorphism `σ` of `hDisc`. -/
noncomputable def precompAnalytic {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U U) : analyticSubring U →+* analyticSubring U :=
  ((precompGermHom (tendsto_principal_principal.mpr hmaps)).comp
      (analyticSubring U).subtype).codRestrict (analyticSubring U)
    (fun x => precomp_mem_analyticSubring hg hmaps x.2)

end Bottcher

namespace Bottcher

@[simp] theorem precompAnalytic_coe {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U U) (a : analyticSubring U) :
    ((precompAnalytic hg hmaps a : analyticSubring U) : Germ (𝓟 U) ℂ)
      = (a : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps) := rfl

/-- **The deck operator is a ring automorphism of the analytic-germ domain when `g` is a
self-biholomorphism of `U`.** Given mutually inverse analytic self-maps `g, g'` of `U`
(`g∘g' = g'∘g = id` on `U`), precomposition by `g` is a `RingEquiv` of `analyticSubring U`, inverse
precomposition by `g'`. The genuine `σ`: an automorphism of a DOMAIN, which lifts to the meromorphic
field `meroField U` and supplies the disconnected-case monodromy `q62_disconnected_both` consumes. -/
noncomputable def precompAnalyticEquiv {U : Set ℂ} {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U) :
    analyticSubring U ≃+* analyticSubring U where
  toFun := precompAnalytic hg hmaps
  invFun := precompAnalytic hg' hmaps'
  left_inv a := by
    apply Subtype.ext
    rw [precompAnalytic_coe, precompAnalytic_coe]
    induction (a : Germ (𝓟 U) ℂ) using Germ.inductionOn with
    | _ F =>
      rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
      exact Germ.coe_eq.mpr (eventually_principal.mpr fun x hx => by
        have h1 : g (g' x) = x := by simpa [Function.comp_apply] using hgg' hx
        simp only [Function.comp_apply, h1])
  right_inv a := by
    apply Subtype.ext
    rw [precompAnalytic_coe, precompAnalytic_coe]
    induction (a : Germ (𝓟 U) ℂ) using Germ.inductionOn with
    | _ F =>
      rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
      exact Germ.coe_eq.mpr (eventually_principal.mpr fun x hx => by
        have h1 : g' (g x) = x := by simpa [Function.comp_apply] using hg'g hx
        simp only [Function.comp_apply, h1])
  map_mul' := map_mul (precompAnalytic hg hmaps)
  map_add' := map_add (precompAnalytic hg hmaps)

end Bottcher

namespace Bottcher

/-- **`σ` fixes every `g`-invariant germ.** If an analytic germ `a` is invariant under precomposition
by `g` (`a ∘ g = a`), then the deck automorphism `precompAnalyticEquiv` fixes it. This is the single
mechanism behind both `K`-linearity and the fixed coordinate: on the cover annulus the base function
`z` (the projection) satisfies `z ∘ g = z` (`g` permutes sheets over the same base), hence `σ z = z`
(so `σ` fixes `ℂ(z)`); likewise `φ_{c₂} ∘ g = φ_{c₂}` gives `σ φ_{c₂} = φ_{c₂}` — exactly the
`σ G = G` datum of `q62_disconnected_both`. -/
theorem precompAnalyticEquiv_apply_of_invariant {U : Set ℂ} {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    {a : analyticSubring U}
    (ha : (a : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
            = (a : Germ (𝓟 U) ℂ)) :
    precompAnalyticEquiv hg hg' hmaps hmaps' hgg' hg'g a = a := by
  apply Subtype.ext
  show ((precompAnalytic hg hmaps a : analyticSubring U) : Germ (𝓟 U) ℂ) = (a : Germ (𝓟 U) ℂ)
  rw [precompAnalytic_coe]; exact ha

end Bottcher

namespace Bottcher

/-- **`σ` scales a `ζ`-relatively-invariant germ by `ζ`.** If `a ∘ g = ζ · a` (constant `ζ`), then the
deck automorphism multiplies `a` by `ζ`: `σ a = ζ · a` (at the germ level). On the cover annulus the
fibre coordinate `φ_{c₁}` satisfies `φ_{c₁} ∘ g = ζ · φ_{c₁}` (the deck rotation scales the `2ⁿ`-th
root by a primitive root of unity), giving exactly the `σ F = ζ · F` datum of
`q62_disconnected_both`. -/
theorem precompAnalyticEquiv_apply_of_scale {U : Set ℂ} {g g' : ℂ → ℂ} {ζ : ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    {a : analyticSubring U}
    (ha : (a : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
            = (ζ : Germ (𝓟 U) ℂ) * (a : Germ (𝓟 U) ℂ)) :
    ((precompAnalyticEquiv hg hg' hmaps hmaps' hgg' hg'g a : analyticSubring U) : Germ (𝓟 U) ℂ)
      = (ζ : Germ (𝓟 U) ℂ) * (a : Germ (𝓟 U) ℂ) := by
  show ((precompAnalytic hg hmaps a : analyticSubring U) : Germ (𝓟 U) ℂ) = _
  rw [precompAnalytic_coe]; exact ha

end Bottcher

namespace Bottcher

/-- **The deck automorphism on the meromorphic field `M = meroField U`.** Lifts the analytic-germ
domain automorphism `precompAnalyticEquiv` (precomposition by the self-biholomorphism `g`) through the
fraction field, giving a field automorphism `meroField U ≃+* meroField U`. This is the genuine `σ` of
the disconnected case, now living on the field `M` — the carrier `q62_disconnected_both` consumes. -/
noncomputable def precompMeroEquiv {U : Set ℂ} {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    meroField U ≃+* meroField U :=
  haveI := isDomain_analyticSubring U hUo hUc hUne
  IsFractionRing.ringEquivOfRingEquiv (precompAnalyticEquiv hg hg' hmaps hmaps' hgg' hg'g)

/-- `σ` on `M` agrees with `σ` on the domain, through the fraction-field embedding: for an analytic
germ `a`, `σ (algebraMap … a) = algebraMap … (σ a)`. The bridge for transporting the fixed/scaled
coordinate relations from `analyticSubring` up to `meroField`. -/
theorem precompMeroEquiv_algebraMap {U : Set ℂ} {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (a : analyticSubring U) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (analyticSubring U) (meroField U) a)
      = algebraMap (analyticSubring U) (meroField U)
          (precompAnalyticEquiv hg hg' hmaps hmaps' hgg' hg'g a) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

end Bottcher

namespace Bottcher

/-- The **deck rotation** `w ↦ ζ·w` — the deck transformation of the dyadic cover expressed in the
cover coordinate `w`; it permutes the `2ⁿ` sheets by a `2ⁿ`-th root of unity `ζ`. This is the concrete
self-biholomorphism `g` that instantiates the abstract `precompAnalyticEquiv`. -/
def rotation (ζ : ℂ) : ℂ → ℂ := fun w => ζ * w

/-- The deck rotation is analytic (entire). -/
theorem analyticOnNhd_rotation (ζ : ℂ) (U : Set ℂ) : AnalyticOnNhd ℂ (rotation ζ) U :=
  analyticOnNhd_const.mul analyticOnNhd_id

/-- `rotation ζ ∘ rotation ζ⁻¹ = id` — the deck rotation is a self-biholomorphism with inverse the
opposite rotation (the deck group is a group). -/
theorem rotation_comp_inv (ζ : ℂ) (hζ : ζ ≠ 0) (U : Set ℂ) :
    Set.EqOn (rotation ζ ∘ rotation ζ⁻¹) id U := fun w _ => by
  simp only [rotation, Function.comp_apply, id_eq, ← mul_assoc, mul_inv_cancel₀ hζ, one_mul]

/-- A **unimodular** rotation maps the norm-annulus `{ρ < |w| < R}` into itself (it preserves `|w|`):
the deck rotation is a self-map of the cover annulus `Ã`. -/
theorem rotation_mapsTo_annulus {ζ : ℂ} (hζ : ‖ζ‖ = 1) (ρ R : ℝ) :
    Set.MapsTo (rotation ζ) {w | ρ < ‖w‖ ∧ ‖w‖ < R} {w | ρ < ‖w‖ ∧ ‖w‖ < R} := by
  rintro w ⟨h1, h2⟩
  simp only [rotation, Set.mem_setOf_eq, norm_mul, hζ, one_mul]
  exact ⟨h1, h2⟩

end Bottcher

namespace Bottcher

/-- **Concrete deck automorphism via the rotation.** Instantiating the abstract `precompMeroEquiv`
with the genuine deck rotation `w ↦ ζ·w` (here on `U = univ`, the model carrier) yields an explicit
field automorphism of `meroField univ` — the full chain
`rotation → precompAnalyticEquiv → precompMeroEquiv` realized on a concrete self-biholomorphism. The
real disconnected case replaces `univ` by the cover annulus `Ã` and supplies the genuine
analytically-continued Böttcher lifts; the automorphism machinery is exactly this. -/
noncomputable def rotationDeckEquiv (ζ : ℂ) (hζ0 : ζ ≠ 0) :
    meroField (Set.univ : Set ℂ) ≃+* meroField (Set.univ : Set ℂ) :=
  precompMeroEquiv (analyticOnNhd_rotation ζ _) (analyticOnNhd_rotation ζ⁻¹ _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (rotation_comp_inv ζ hζ0 _)
    (by have h := rotation_comp_inv ζ⁻¹ (inv_ne_zero hζ0) (Set.univ : Set ℂ)
        rwa [inv_inv] at h)
    isOpen_univ isPreconnected_univ Set.univ_nonempty

end Bottcher

namespace Bottcher

/-- **The deck automorphism as a `K`-algebra automorphism.** If `precompMeroEquiv` fixes the image of
the base field `K` in `M = meroField U` (which holds when `K = ℂ(z)` embeds via `g`-invariant germs —
the projection on the cover annulus, `precompAnalyticEquiv_apply_of_invariant`), it upgrades to a
`K`-algebra automorphism `M ≃ₐ[K] M` — the exact type `q62_disconnected_both` requires for its
monodromy datum `σ`. -/
noncomputable def precompMeroAlgEquiv {U : Set ℂ} {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (hK : ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
            (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    meroField U ≃ₐ[K] meroField U :=
  AlgEquiv.ofRingEquiv hK

end Bottcher

namespace Bottcher

/-- **`σ` fixes the `meroField` image of a `g`-invariant germ.** Lifting
`precompAnalyticEquiv_apply_of_invariant` through `algebraMap`: if `a ∘ g = a` then
`σ (algebraMap a) = algebraMap a` in `meroField U`. This supplies, at the field level, both the
`σ G = G` datum (`G = φ_{c₂}` germ) and the `K`-linearity (`σ` fixes the `ℂ(z)`-image, the projection
germ) that `q62_disconnected_both` / `precompMeroAlgEquiv` consume. -/
theorem precompMeroEquiv_algebraMap_fix {U : Set ℂ} {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {a : analyticSubring U}
    (ha : (a : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
            = (a : Germ (𝓟 U) ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (analyticSubring U) (meroField U) a)
      = algebraMap (analyticSubring U) (meroField U) a := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  rw [precompMeroEquiv_algebraMap, precompAnalyticEquiv_apply_of_invariant
    hg hg' hmaps hmaps' hgg' hg'g ha]

end Bottcher

namespace Bottcher

/-- **`σ` scales the `meroField` image of a `ζ₀`-relatively-invariant germ by the constant `ζ₀`.**
Lifting the germ-level scaling through `algebraMap`: if `a ∘ g = ζ₀ · a` (with `ζ₀` the constant germ
`constToAnalytic U ζ₀`) then `σ (algebraMap a) = algebraMap (ζ₀) * algebraMap a` in `meroField U`. This
is the `σ F = ζ · F` datum (`F = φ_{c₁}` germ, `ζ = algebraMap (constToAnalytic ζ₀)`) of
`q62_disconnected_both`. -/
theorem precompMeroEquiv_algebraMap_scale {U : Set ℂ} {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (ζ₀ : ℂ) {a : analyticSubring U}
    (ha : (a : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
            = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a : Germ (𝓟 U) ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (analyticSubring U) (meroField U) a)
      = algebraMap (analyticSubring U) (meroField U) (constToAnalytic U ζ₀)
        * algebraMap (analyticSubring U) (meroField U) a := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  have hscale : precompAnalyticEquiv hg hg' hmaps hmaps' hgg' hg'g a
      = constToAnalytic U ζ₀ * a := by
    apply Subtype.ext
    show ((precompAnalytic hg hmaps a : analyticSubring U) : Germ (𝓟 U) ℂ) = _
    rw [precompAnalytic_coe, ha, MulMemClass.coe_mul]
  rw [precompMeroEquiv_algebraMap, hscale, map_mul]

end Bottcher

namespace Bottcher

/-- **The constant `ζ₀` keeps its order in `meroField U`.** The composite `ℂ →+* meroField U`
(constants → analytic germs → fractions) is a ring hom out of the field `ℂ`, hence injective, so it
preserves multiplicative order: `orderOf (algebraMap (constToAnalytic ζ₀)) = orderOf ζ₀`. With
`exists_dyadic_order_gt` this supplies the `orderOf ζ = m > d` datum of `q62_disconnected_both` at the
field level — the `meroField` analogue of `orderOf_const_coverGerm`. -/
theorem orderOf_algebraMap_constToAnalytic {U : Set ℂ} [IsDomain (analyticSubring U)] (ζ₀ : ℂ) :
    orderOf (algebraMap (analyticSubring U) (meroField U) (constToAnalytic U ζ₀)) = orderOf ζ₀ := by
  let f : ℂ →+* meroField U :=
    (algebraMap (analyticSubring U) (meroField U)).comp (constToAnalytic U)
  exact orderOf_injective f.toMonoidHom f.injective ζ₀

end Bottcher

namespace Bottcher

/-- **The constant germ is `g`-invariant.** Precomposition by any self-map fixes a constant germ
(`(fun _ ↦ ζ₀) ∘ g = fun _ ↦ ζ₀`). Hence via `precompMeroEquiv_algebraMap_fix` the deck automorphism
fixes the constant `ζ = algebraMap (constToAnalytic ζ₀)` — the `σ ζ = ζ` datum of
`q62_disconnected_both`. -/
theorem constToAnalytic_compTendsto {U : Set ℂ} {g : ℂ → ℂ} (h : Filter.Tendsto g (𝓟 U) (𝓟 U))
    (ζ₀ : ℂ) :
    ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto g h
      = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) := by
  show (↑(fun _ : ℂ => ζ₀) : Germ (𝓟 U) ℂ).compTendsto g h = ↑(fun _ : ℂ => ζ₀)
  rw [Germ.coe_compTendsto]
  rfl

end Bottcher

-- (rebuild trigger)

namespace Bottcher
open Polynomial Filter

/-- **Projection-based base embedding `K = ℂ(p₀) → analyticSubring U`.** The identity-coordinate
embedding `polyToAnalytic` (`X ↦ z`) forces any `K`-fixing deck `g` to satisfy `g = id` on a planar
`U` — so the deck is trivial and `q62_disconnected_both`'s monodromy cannot be realized on a planar
domain with the identity base. To carry the genuine cover monodromy (deck fixes the *projection*,
permutes sheets), the base must embed via a chosen analytic *projection* `p₀ ∈ analyticSubring U`:
`q ↦ q(p₀)` (`eval₂RingHom`). Then `K = ℂ(p₀)`, and any deck self-map `g` with `p₀∘g = p₀` fixes all of
`K` — the structure a nontrivial order-`2ⁿ` sheet-permuting deck needs. The algebraic enabler for the
connected dyadic-cover carrier (`p₀` = the `2ⁿ`-fold covering projection of the cover annulus). -/
noncomputable def polyToAnalyticVia (U : Set ℂ) (p₀ : analyticSubring U) :
    Polynomial ℂ →+* analyticSubring U :=
  Polynomial.eval₂RingHom (constToAnalytic U) p₀

@[simp] theorem polyToAnalyticVia_X (U : Set ℂ) (p₀ : analyticSubring U) :
    polyToAnalyticVia U p₀ Polynomial.X = p₀ := by simp [polyToAnalyticVia]

@[simp] theorem polyToAnalyticVia_C (U : Set ℂ) (p₀ : analyticSubring U) (a : ℂ) :
    polyToAnalyticVia U p₀ (Polynomial.C a) = constToAnalytic U a := by simp [polyToAnalyticVia]

/-- The deck ring operator `precompAnalytic` fixes the constant subring (`constToAnalytic_compTendsto`,
constants are `g`-invariant since `(fun _ ↦ c) ∘ g = fun _ ↦ c`). -/
theorem precompAnalytic_constToAnalytic {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U U) (c : ℂ) :
    precompAnalytic hg hmaps (constToAnalytic U c) = constToAnalytic U c := by
  apply Subtype.ext
  rw [precompAnalytic_coe]
  exact constToAnalytic_compTendsto (tendsto_principal_principal.mpr hmaps) c

/-- **The deck operator fixes the whole projection-base `K = ℂ(p₀)` when `p₀∘g = p₀`.** If the chosen
projection germ `p₀` is `g`-invariant, every `q(p₀) ∈ K` is fixed by the deck ring operator
`precompAnalytic`: two ring homs `ℂ[X] → analyticSubring U` agreeing on the constants
(`precompAnalytic_constToAnalytic`) and on `X ↦ p₀` (`hp0`) are equal (`Polynomial.ringHom_ext`). This
is the key step making the deck a genuine `K`-algebra map with `K` embedded via the covering
projection — exactly what a nontrivial sheet-permuting order-`2ⁿ` deck requires, which the identity
embedding cannot supply on a planar domain. -/
theorem precompAnalytic_polyToAnalyticVia_fix {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U U) {p₀ : analyticSubring U}
    (hp0 : precompAnalytic hg hmaps p₀ = p₀) (q : Polynomial ℂ) :
    precompAnalytic hg hmaps (polyToAnalyticVia U p₀ q) = polyToAnalyticVia U p₀ q := by
  have hcomp : (precompAnalytic hg hmaps).comp (polyToAnalyticVia U p₀) = polyToAnalyticVia U p₀ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, polyToAnalyticVia_C]
      exact precompAnalytic_constToAnalytic hg hmaps a
    · simp only [RingHom.comp_apply, polyToAnalyticVia_X]
      exact hp0
  exact RingHom.congr_fun hcomp q

end Bottcher
