/-
# Several-variable analytic-germ domain — keystone for the product-cover carrier

`hDisc` needs a carrier that is BOTH a field AND carries the deck transformation `deckMap₁`
(`(z,v₁,v₂) ↦ (z, ζ·v₁, v₂)`, scaling `φ_{c₁}=v₁` and fixing `z, φ_{c₂}=v₂` — `BasinBranching.lean`).
The deck lives naturally on the **product cover** `commonPullback ⊆ ℂ³`, but `coverGerm` (functions on
`ℂ³`) is never a domain. The fix: `meroField` over a *connected* piece of the product cover. The keystone
is that analytic functions on a connected open subset of a several-variable space still form an integral
domain — which holds because Mathlib's identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) is valid over an **arbitrary** normed space `E`,
not just `ℂ`. This file proves that general domain property; the rest of `MeromorphicField`'s
construction (germ subring → `FractionRing` → precomposition deck) is `E`-agnostic and lifts on top.
-/
import GaloisForLFunctions.Bottcher.MeromorphicField

open Filter Topology

namespace Bottcher

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Several-variable identity-theorem domain property.** If `f, g` are analytic on a connected open
`U ⊆ E` (any normed `ℂ`-space `E`) and `f·g ≡ 0` on `U`, then `f ≡ 0` or `g ≡ 0` on `U`. The proof is
the one-variable `analyticOnNhd_domain` verbatim — it never used that the domain is `ℂ`, only that the
codomain `ℂ` is a field (`mul_eq_zero`) and the general identity theorem holds. For `E = ℂ³` this is the
integral-domain property of analytic functions on a connected piece of the product cover. -/
theorem analyticOnNhd_domain_gen {U : Set E} {f g : E → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) (hUo : IsOpen U) (hfg : Set.EqOn (fun z => f z * g z) 0 U) :
    Set.EqOn f 0 U ∨ Set.EqOn g 0 U := by
  by_cases h : Set.EqOn f 0 U
  · exact Or.inl h
  · right
    simp only [Set.EqOn, not_forall] at h
    obtain ⟨z₀, hz₀U, hz₀⟩ := h
    have hz₀ne : f z₀ ≠ 0 := fun hc => hz₀ (by simp [hc])
    have hcont : ContinuousAt f z₀ := (hf z₀ hz₀U).continuousAt
    have hg0 : ∀ᶠ z in 𝓝 z₀, g z = 0 := by
      filter_upwards [hcont.eventually_ne hz₀ne, hUo.mem_nhds hz₀U] with z hzne hzU
      have hz := hfg hzU
      simp only [Pi.zero_apply] at hz
      exact (mul_eq_zero.mp hz).resolve_left hzne
    exact hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hz₀U hg0

variable (U : Set E)

/-- **Several-variable analytic-germ subring.** Germs (modulo agreement on `U ⊆ E`) of functions
`E → ℂ` with an analytic-on-`U` representative; a subring of `Germ (𝓟 U) ℂ`. The `E = ℂ³` instance is
the carrier of analytic functions on a piece of the product cover, on which the deck `deckMap₁` acts. -/
def analyticSubringGen : Subring (Germ (𝓟 U) ℂ) where
  carrier := {g | ∃ f : E → ℂ, AnalyticOnNhd ℂ f U ∧ (Germ.coeRingHom (𝓟 U) f) = g}
  mul_mem' := by rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f * g, hf.mul hg, by rw [map_mul]⟩
  one_mem' := ⟨1, analyticOnNhd_const, map_one _⟩
  add_mem' := by rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f + g, hf.add hg, by rw [map_add]⟩
  zero_mem' := ⟨0, analyticOnNhd_const, map_zero _⟩
  neg_mem' := by rintro a ⟨f, hf, rfl⟩; exact ⟨-f, hf.neg, by rw [map_neg]⟩

/-- **The several-variable analytic-germ ring is an integral domain** on a connected open nonempty
`U ⊆ E`. No nonzero zero-divisors is the general identity theorem (`analyticOnNhd_domain_gen`);
nontrivial because `U ≠ ∅` makes `0 ≠ 1`. For `E = ℂ³` and `U` a connected piece of the product cover,
this makes `FractionRing (analyticSubringGen U)` a genuine field — the carrier that is simultaneously a
field and carries the `deckMap₁` deck (impossible on the planar exterior). -/
theorem isDomain_analyticSubringGen (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    IsDomain (analyticSubringGen U) := by
  haveI hnb : (𝓟 U).NeBot := principal_neBot_iff.mpr hUne
  haveI hnt : Nontrivial (analyticSubringGen U) := by
    refine ⟨0, 1, ?_⟩
    intro h
    have hv := congrArg (Subtype.val) h
    rw [ZeroMemClass.coe_zero, OneMemClass.coe_one] at hv
    exact zero_ne_one hv
  haveI hnzd : NoZeroDivisors (analyticSubringGen U) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have hval : (a : Germ (𝓟 U) ℂ) * (b : Germ (𝓟 U) ℂ) = 0 := by
      have h2 := congrArg (Subtype.val) hab
      rwa [MulMemClass.coe_mul, ZeroMemClass.coe_zero] at h2
    have hfa' : (a : Germ (𝓟 U) ℂ) = (↑f : Germ (𝓟 U) ℂ) := hfa.symm
    have hgb' : (b : Germ (𝓟 U) ℂ) = (↑g : Germ (𝓟 U) ℂ) := hgb.symm
    rw [hfa', hgb', ← Germ.coe_mul, ← Germ.coe_zero, Germ.coe_eq] at hval
    have heq : Set.EqOn (fun x => f x * g x) 0 U := fun x hx => eventually_principal.mp hval x hx
    rcases analyticOnNhd_domain_gen hf hg hUc hUo heq with h0 | h0
    · left
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, hfa', ← Germ.coe_zero, Germ.coe_eq]
      exact eventually_principal.mpr h0
    · right
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, hgb', ← Germ.coe_zero, Germ.coe_eq]
      exact eventually_principal.mpr h0
  exact NoZeroDivisors.to_isDomain _

/-- The **several-variable meromorphic function field**: the fraction field of `analyticSubringGen U`.
A `Field` whenever `U ⊆ E` is connected, open, nonempty. For `E = ℂ³`, `U` a connected piece of the
product cover, this is the field carrier `q62_disconnected_both` needs WITH the deck — the synthesis the
planar `meroField` could not provide. -/
abbrev meroFieldGen := FractionRing (analyticSubringGen U)

example (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    Nonempty (Field (meroFieldGen U)) :=
  letI := isDomain_analyticSubringGen U hUo hUc hUne
  ⟨inferInstance⟩

/-! ## The deck (precomposition) machinery over `E` — generalizes `MeromorphicField`'s `ℂ` version. -/

/-- Precomposition by an analytic self-map `g : E → E` preserves the analytic-germ domain. -/
theorem precomp_mem_analyticSubringGen {g : E → E} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U U) {a : Germ (𝓟 U) ℂ} (ha : a ∈ analyticSubringGen U) :
    a.compTendsto g (tendsto_principal_principal.mpr hmaps) ∈ analyticSubringGen U := by
  obtain ⟨f, hf, rfl⟩ := ha
  exact ⟨f ∘ g, hf.comp hg hmaps,
    (Germ.coe_compTendsto f (tendsto_principal_principal.mpr hmaps)).symm⟩

/-- Precomposition by a self-map `g` as a ring endomorphism of the germ ring `Germ (𝓟 U) ℂ`. -/
noncomputable def precompGermHomGen {g : E → E} (h : Tendsto g (𝓟 U) (𝓟 U)) :
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

/-- The deck operator as a ring endomorphism of the analytic-germ domain (`g` self-map of `U ⊆ E`). -/
noncomputable def precompAnalyticGen {g : E → E} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U U) : analyticSubringGen U →+* analyticSubringGen U :=
  ((precompGermHomGen U (tendsto_principal_principal.mpr hmaps)).comp
      (analyticSubringGen U).subtype).codRestrict (analyticSubringGen U)
    (fun x => precomp_mem_analyticSubringGen U hg hmaps x.2)

@[simp] theorem precompAnalyticGen_coe {g : E → E} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U U) (a : analyticSubringGen U) :
    ((precompAnalyticGen U hg hmaps a : analyticSubringGen U) : Germ (𝓟 U) ℂ)
      = (a : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps) := rfl

/-- The deck operator is a ring automorphism when `g` is a self-biholomorphism of `U ⊆ E`. -/
noncomputable def precompAnalyticEquivGen {g g' : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U) :
    analyticSubringGen U ≃+* analyticSubringGen U where
  toFun := precompAnalyticGen U hg hmaps
  invFun := precompAnalyticGen U hg' hmaps'
  left_inv a := by
    apply Subtype.ext
    rw [precompAnalyticGen_coe, precompAnalyticGen_coe]
    induction (a : Germ (𝓟 U) ℂ) using Germ.inductionOn with
    | _ F =>
      rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
      exact Germ.coe_eq.mpr (eventually_principal.mpr fun x hx => by
        have h1 : g (g' x) = x := by simpa [Function.comp_apply] using hgg' hx
        simp only [Function.comp_apply, h1])
  right_inv a := by
    apply Subtype.ext
    rw [precompAnalyticGen_coe, precompAnalyticGen_coe]
    induction (a : Germ (𝓟 U) ℂ) using Germ.inductionOn with
    | _ F =>
      rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
      exact Germ.coe_eq.mpr (eventually_principal.mpr fun x hx => by
        have h1 : g' (g x) = x := by simpa [Function.comp_apply] using hg'g hx
        simp only [Function.comp_apply, h1])
  map_mul' := map_mul (precompAnalyticGen U hg hmaps)
  map_add' := map_add (precompAnalyticGen U hg hmaps)

/-- `σ` fixes every `g`-invariant germ. -/
theorem precompAnalyticEquivGen_apply_of_invariant {g g' : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    {a : analyticSubringGen U}
    (ha : (a : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
            = (a : Germ (𝓟 U) ℂ)) :
    precompAnalyticEquivGen U hg hg' hmaps hmaps' hgg' hg'g a = a := by
  apply Subtype.ext
  show ((precompAnalyticGen U hg hmaps a : analyticSubringGen U) : Germ (𝓟 U) ℂ) = (a : Germ (𝓟 U) ℂ)
  rw [precompAnalyticGen_coe]; exact ha

/-- `σ` scales a `ζ`-relatively-invariant germ by `ζ`. -/
theorem precompAnalyticEquivGen_apply_of_scale {g g' : E → E} {ζ : ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    {a : analyticSubringGen U}
    (ha : (a : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
            = (ζ : Germ (𝓟 U) ℂ) * (a : Germ (𝓟 U) ℂ)) :
    ((precompAnalyticEquivGen U hg hg' hmaps hmaps' hgg' hg'g a : analyticSubringGen U)
        : Germ (𝓟 U) ℂ) = (ζ : Germ (𝓟 U) ℂ) * (a : Germ (𝓟 U) ℂ) := by
  show ((precompAnalyticGen U hg hmaps a : analyticSubringGen U) : Germ (𝓟 U) ℂ) = _
  rw [precompAnalyticGen_coe]; exact ha

/-- **The deck automorphism on the several-variable meromorphic field `meroFieldGen U`.** Lifts
`precompAnalyticEquivGen` through the fraction field. For `E = ℂ³`, `g = deckMap₁ ζ` on a connected
piece of the product cover, this is the genuine `σ` of the disconnected case — scaling `φ_{c₁}=v₁`,
fixing `φ_{c₂}=v₂` and `z` — now a HONEST field automorphism (the planar carrier could not host it). -/
noncomputable def precompMeroEquivGen {g g' : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    meroFieldGen U ≃+* meroFieldGen U :=
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  IsFractionRing.ringEquivOfRingEquiv (precompAnalyticEquivGen U hg hg' hmaps hmaps' hgg' hg'g)

/-- `σ` on `meroFieldGen` agrees with `σ` on the domain through the fraction-field embedding. -/
theorem precompMeroEquivGen_algebraMap {g g' : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (a : analyticSubringGen U) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (analyticSubringGen U) (meroFieldGen U) a)
      = algebraMap (analyticSubringGen U) (meroFieldGen U)
          (precompAnalyticEquivGen U hg hg' hmaps hmaps' hgg' hg'g a) := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

end Bottcher
