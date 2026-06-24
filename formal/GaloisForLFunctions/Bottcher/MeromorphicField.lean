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

end Bottcher
