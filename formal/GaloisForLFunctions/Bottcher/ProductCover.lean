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
import GaloisForLFunctions.Bottcher.CoverMonodromy
import GaloisForLFunctions.Bottcher.Q62

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

/-- Constant functions as analytic germs on a several-variable carrier. -/
noncomputable def constToAnalyticGen : ℂ →+* analyticSubringGen U :=
  ((Germ.coeRingHom (𝓟 U)).comp (RingHom.pi (fun _ : E => RingHom.id ℂ))).codRestrict
    (analyticSubringGen U) (fun a => ⟨fun _ => a, analyticOnNhd_const, rfl⟩)

/-- Constants are fixed by every precomposition operator. -/
theorem constToAnalyticGen_compTendsto {g : E → E} (h : Filter.Tendsto g (𝓟 U) (𝓟 U))
    (ζ₀ : ℂ) :
    ((constToAnalyticGen U ζ₀ : analyticSubringGen U) : Germ (𝓟 U) ℂ).compTendsto g h
      = ((constToAnalyticGen U ζ₀ : analyticSubringGen U) : Germ (𝓟 U) ℂ) := by
  show (↑(fun _ : E => ζ₀) : Germ (𝓟 U) ℂ).compTendsto g h = ↑(fun _ : E => ζ₀)
  rw [Germ.coe_compTendsto]
  rfl

/-- The analytic-germ precomposition operator fixes constants. -/
theorem precompAnalyticGen_constToAnalyticGen {g : E → E} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U U) (c : ℂ) :
    precompAnalyticGen U hg hmaps (constToAnalyticGen U c) = constToAnalyticGen U c := by
  apply Subtype.ext
  rw [precompAnalyticGen_coe]
  exact constToAnalyticGen_compTendsto U (tendsto_principal_principal.mpr hmaps) c

/-- The constant multiplier keeps its order after embedding in the several-variable meromorphic
field. -/
theorem orderOf_algebraMap_constToAnalyticGen [IsDomain (analyticSubringGen U)] (ζ₀ : ℂ) :
    orderOf (algebraMap (analyticSubringGen U) (meroFieldGen U) (constToAnalyticGen U ζ₀))
      = orderOf ζ₀ := by
  let f : ℂ →+* meroFieldGen U :=
    (algebraMap (analyticSubringGen U) (meroFieldGen U)).comp (constToAnalyticGen U)
  exact orderOf_injective f.toMonoidHom f.injective ζ₀

/-- Upgrade a `g`-invariant analytic germ to a fixed meromorphic field element. -/
theorem precompMeroEquivGen_algebraMap_fix {g g' : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {a : analyticSubringGen U}
    (ha : (a : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
            = (a : Germ (𝓟 U) ℂ)) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (analyticSubringGen U) (meroFieldGen U) a)
      = algebraMap (analyticSubringGen U) (meroFieldGen U) a := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  rw [precompMeroEquivGen_algebraMap,
    precompAnalyticEquivGen_apply_of_invariant U hg hg' hmaps hmaps' hgg' hg'g ha]

/-- Upgrade a relatively-invariant analytic germ to a scaled meromorphic field element. -/
theorem precompMeroEquivGen_algebraMap_scale {g g' : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (ζ₀ : ℂ) {a : analyticSubringGen U}
    (ha : (a : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
            = ((constToAnalyticGen U ζ₀ : analyticSubringGen U) : Germ (𝓟 U) ℂ)
              * (a : Germ (𝓟 U) ℂ)) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (analyticSubringGen U) (meroFieldGen U) a)
      = algebraMap (analyticSubringGen U) (meroFieldGen U) (constToAnalyticGen U ζ₀)
        * algebraMap (analyticSubringGen U) (meroFieldGen U) a := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  have hscale : precompAnalyticEquivGen U hg hg' hmaps hmaps' hgg' hg'g a
      = constToAnalyticGen U ζ₀ * a := by
    apply Subtype.ext
    show ((precompAnalyticGen U hg hmaps a : analyticSubringGen U) : Germ (𝓟 U) ℂ) = _
    rw [precompAnalyticGen_coe, ha, MulMemClass.coe_mul]
  rw [precompMeroEquivGen_algebraMap, hscale, map_mul]

/-- The several-variable meromorphic deck automorphism as a `K`-algebra automorphism, once the deck
fixes the embedded base field. -/
noncomputable def precompMeroAlgEquivGen {g g' : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroFieldGen U)]
    (hK : ∀ k : K, precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
            (algebraMap K (meroFieldGen U) k) = algebraMap K (meroFieldGen U) k) :
    meroFieldGen U ≃ₐ[K] meroFieldGen U :=
  AlgEquiv.ofRingEquiv hK

/-- **Several-variable `monoF` witness.**  A z-fixing/product-cover deck self-biholomorphism with
`a₁ ∘ g = ζ₀ a₁`, `a₂ ∘ g = a₂`, and base-field fixing gives the exact `monoF` tuple over
`meroFieldGen U`. -/
theorem monoF_witness_gen
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroFieldGen U)]
    (a₁ a₂ : analyticSubringGen U) (d : ℕ) (ζ₀ : ℂ) {g g' : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hord : d < orderOf ζ₀)
    (hscale : (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalyticGen U ζ₀ : analyticSubringGen U) : Germ (𝓟 U) ℂ)
          * (a₁ : Germ (𝓟 U) ℂ))
    (hinv : (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = (a₂ : Germ (𝓟 U) ℂ))
    (hK : ∀ k : K, precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap K (meroFieldGen U) k) = algebraMap K (meroFieldGen U) k) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    ∃ (σ : meroFieldGen U ≃ₐ[K] meroFieldGen U) (ζ : meroFieldGen U) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧
      σ (algebraMap (analyticSubringGen U) (meroFieldGen U) a₂)
        = algebraMap (analyticSubringGen U) (meroFieldGen U) a₂ ∧
      σ ζ = ζ ∧
      σ (algebraMap (analyticSubringGen U) (meroFieldGen U) a₁)
        = ζ * algebraMap (analyticSubringGen U) (meroFieldGen U) a₁ := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  refine ⟨precompMeroAlgEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne hK,
    algebraMap (analyticSubringGen U) (meroFieldGen U) (constToAnalyticGen U ζ₀), orderOf ζ₀,
    hord, orderOf_algebraMap_constToAnalyticGen U ζ₀, ?_, ?_, ?_⟩
  · show precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap _ _ a₂) = algebraMap _ _ a₂
    exact precompMeroEquivGen_algebraMap_fix U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne hinv
  · show precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap _ _ (constToAnalyticGen U ζ₀)) = algebraMap _ _ (constToAnalyticGen U ζ₀)
    exact precompMeroEquivGen_algebraMap_fix U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
      (constToAnalyticGen_compTendsto U (tendsto_principal_principal.mpr hmaps) ζ₀)
  · show precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap _ _ a₁) = _
    exact precompMeroEquivGen_algebraMap_scale U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
      ζ₀ hscale

/-- **Several-variable `monoG` witness.**  The symmetric scaling deck tuple for the second coordinate
over `meroFieldGen U`. -/
theorem monoG_witness_gen
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroFieldGen U)]
    (a₂ : analyticSubringGen U) (d : ℕ) (ζ₀ : ℂ) {g g' : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hord : d < orderOf ζ₀)
    (hscale : (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalyticGen U ζ₀ : analyticSubringGen U) : Germ (𝓟 U) ℂ)
          * (a₂ : Germ (𝓟 U) ℂ))
    (hK : ∀ k : K, precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap K (meroFieldGen U) k) = algebraMap K (meroFieldGen U) k) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    ∃ (σ : meroFieldGen U ≃ₐ[K] meroFieldGen U) (ζ : meroFieldGen U),
      d < orderOf ζ ∧ σ ζ = ζ ∧
      σ (algebraMap (analyticSubringGen U) (meroFieldGen U) a₂)
        = ζ * algebraMap (analyticSubringGen U) (meroFieldGen U) a₂ := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  refine ⟨precompMeroAlgEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne hK,
    algebraMap (analyticSubringGen U) (meroFieldGen U) (constToAnalyticGen U ζ₀), ?_, ?_, ?_⟩
  · rw [orderOf_algebraMap_constToAnalyticGen U]; exact hord
  · show precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap _ _ (constToAnalyticGen U ζ₀)) = algebraMap _ _ (constToAnalyticGen U ζ₀)
    exact precompMeroEquivGen_algebraMap_fix U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
      (constToAnalyticGen_compTendsto U (tendsto_principal_principal.mpr hmaps) ζ₀)
  · show precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap _ _ a₂) = _
    exact precompMeroEquivGen_algebraMap_scale U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
      ζ₀ hscale

/-- Projection-base embedding `ℂ[z] → analyticSubringGen U`, via an analytic projection germ `p₀`.
This is the several-variable analogue of `polyToAnalyticVia`: on a product cover, `p₀` is the
deck-invariant base coordinate `z`. -/
noncomputable def polyToAnalyticViaGen (p₀ : analyticSubringGen U) :
    Polynomial ℂ →+* analyticSubringGen U :=
  Polynomial.eval₂RingHom (constToAnalyticGen U) p₀

@[simp] theorem polyToAnalyticViaGen_X (p₀ : analyticSubringGen U) :
    polyToAnalyticViaGen U p₀ Polynomial.X = p₀ := by simp [polyToAnalyticViaGen]

@[simp] theorem polyToAnalyticViaGen_C (p₀ : analyticSubringGen U) (a : ℂ) :
    polyToAnalyticViaGen U p₀ (Polynomial.C a) = constToAnalyticGen U a := by
  simp [polyToAnalyticViaGen]

/-- The several-variable precomposition operator fixes the whole projection base when it fixes the
projection germ `p₀`. -/
theorem precompAnalyticGen_polyToAnalyticViaGen_fix {g : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U U) {p₀ : analyticSubringGen U}
    (hp0 : precompAnalyticGen U hg hmaps p₀ = p₀) (q : Polynomial ℂ) :
    precompAnalyticGen U hg hmaps (polyToAnalyticViaGen U p₀ q)
      = polyToAnalyticViaGen U p₀ q := by
  have hcomp : (precompAnalyticGen U hg hmaps).comp (polyToAnalyticViaGen U p₀)
      = polyToAnalyticViaGen U p₀ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, polyToAnalyticViaGen_C]
      exact precompAnalyticGen_constToAnalyticGen U hg hmaps a
    · simp only [RingHom.comp_apply, polyToAnalyticViaGen_X]
      exact hp0
  exact RingHom.congr_fun hcomp q

/-- Germ of the projection-base embedding: `q ↦ q(p₀)`. -/
theorem polyToAnalyticViaGen_coe (p₀ : analyticSubringGen U) {f₀ : E → ℂ}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀) (q : Polynomial ℂ) :
    ((polyToAnalyticViaGen U p₀ q : analyticSubringGen U) : Germ (𝓟 U) ℂ)
      = ↑(fun z => q.eval (f₀ z)) := by
  induction q using Polynomial.induction_on with
  | C a =>
    rw [polyToAnalyticViaGen_C]
    show ((constToAnalyticGen U a : analyticSubringGen U) : Germ (𝓟 U) ℂ) = _
    apply Germ.coe_eq.mpr
    exact Filter.eventually_principal.mpr (fun _ _ => by simp [Polynomial.eval_C])
  | add p r hp hr =>
    rw [map_add, Subring.coe_add, hp, hr, ← Germ.coe_add]
    apply Germ.coe_eq.mpr
    exact Filter.eventually_principal.mpr (fun _ _ => by simp [Polynomial.eval_add])
  | monomial n a _ =>
    rw [map_mul, map_pow, polyToAnalyticViaGen_C, polyToAnalyticViaGen_X, Subring.coe_mul,
        SubmonoidClass.coe_pow]
    have h1 : ((constToAnalyticGen U a : analyticSubringGen U) : Germ (𝓟 U) ℂ)
        = ↑(fun _ : E => a) := rfl
    rw [h1, hp0, ← Germ.coe_pow, ← Germ.coe_mul]
    apply Germ.coe_eq.mpr
    exact Filter.eventually_principal.mpr (fun _ _ => by
      simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X])

/-- The projection-base polynomial embedding is injective when the projection has infinite image. -/
theorem polyToAnalyticViaGen_injective (p₀ : analyticSubringGen U) {f₀ : E → ℂ}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀) (hinf : (f₀ '' U).Infinite) :
    Function.Injective (polyToAnalyticViaGen U p₀) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hg : ((polyToAnalyticViaGen U p₀ q : analyticSubringGen U) : Germ (𝓟 U) ℂ) = 0 := by
    rw [hq]
    exact ZeroMemClass.coe_zero _
  rw [polyToAnalyticViaGen_coe U p₀ hp0, ← Germ.coe_zero, Germ.coe_eq] at hg
  have hroots : f₀ '' U ⊆ {x | q.IsRoot x} := by
    rintro x ⟨z, hz, rfl⟩
    exact Filter.eventually_principal.mp hg z hz
  exact Polynomial.eq_zero_of_infinite_isRoot q (hinf.mono hroots)

/-- `ℂ[z] → meroFieldGen U` via a projection germ. -/
noncomputable def polyToMeroViaGen (p₀ : analyticSubringGen U) :
    Polynomial ℂ →+* meroFieldGen U :=
  (algebraMap (analyticSubringGen U) (meroFieldGen U)).comp (polyToAnalyticViaGen U p₀)

/-- The meromorphic projection-base polynomial embedding is injective when the projection has
infinite image. -/
theorem polyToMeroViaGen_injective (p₀ : analyticSubringGen U) {f₀ : E → ℂ}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀) (hinf : (f₀ '' U).Infinite)
    (_hUo : IsOpen U) (_hUc : IsPreconnected U) (_hUne : U.Nonempty) :
    Function.Injective (polyToMeroViaGen U p₀) := by
  haveI := isDomain_analyticSubringGen U _hUo _hUc _hUne
  exact (IsFractionRing.injective (analyticSubringGen U) (meroFieldGen U)).comp
    (polyToAnalyticViaGen_injective U p₀ hp0 hinf)

/-- `K = ℂ(z)` embedded into the several-variable meromorphic field through a deck-invariant
projection `p₀`. -/
noncomputable def ratfuncToMeroViaGen (p₀ : analyticSubringGen U) {f₀ : E → ℂ}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀) (hinf : (f₀ '' U).Infinite)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    RatFunc ℂ →+* meroFieldGen U :=
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  IsFractionRing.lift (polyToMeroViaGen_injective U p₀ hp0 hinf hUo hUc hUne)

/-- Lifting projection-base fixing through the several-variable fraction field. -/
theorem precompMeroEquivGen_polyToAnalyticViaGen_fix {g g' : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubringGen U} (hp0 : precompAnalyticGen U hg hmaps p₀ = p₀)
    (q : Polynomial ℂ) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (analyticSubringGen U) (meroFieldGen U) (polyToAnalyticViaGen U p₀ q))
      = algebraMap (analyticSubringGen U) (meroFieldGen U) (polyToAnalyticViaGen U p₀ q) := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  apply precompMeroEquivGen_algebraMap_fix U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
  rw [← precompAnalyticGen_coe U hg hmaps (polyToAnalyticViaGen U p₀ q),
      precompAnalyticGen_polyToAnalyticViaGen_fix U hg hmaps hp0 q]

/-- The deck fixes the whole `RatFunc ℂ` projection base embedded through `p₀`. -/
theorem precompMeroEquivGen_ratfuncToMeroViaGen_fix {g g' : E → E}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubringGen U} {f₀ : E → ℂ}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀) (hinf : (f₀ '' U).Infinite)
    (hfix : precompAnalyticGen U hg hmaps p₀ = p₀) (k : RatFunc ℂ) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (ratfuncToMeroViaGen U p₀ hp0 hinf hUo hUc hUne k)
      = ratfuncToMeroViaGen U p₀ hp0 hinf hUo hUc hUne k := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  have key : ((precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne).toRingHom).comp
      (ratfuncToMeroViaGen U p₀ hp0 hinf hUo hUc hUne)
      = ratfuncToMeroViaGen U p₀ hp0 hinf hUo hUc hUne := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro p
    rw [RingHom.comp_apply]
    rw [show ratfuncToMeroViaGen U p₀ hp0 hinf hUo hUc hUne
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
        = polyToMeroViaGen U p₀ p from IsFractionRing.lift_algebraMap _ p]
    show precompMeroEquivGen U hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (analyticSubringGen U) (meroFieldGen U) (polyToAnalyticViaGen U p₀ p))
      = algebraMap (analyticSubringGen U) (meroFieldGen U) (polyToAnalyticViaGen U p₀ p)
    exact precompMeroEquivGen_polyToAnalyticViaGen_fix U hg hg' hmaps hmaps' hgg' hg'g
      hUo hUc hUne hfix p
  exact RingHom.congr_fun key k

end Bottcher

namespace Bottcher

/-! ## Concrete coordinate germs on the product-cover carrier -/

/-- The base coordinate `z` is analytic on any product-cover piece. -/
theorem analyticOnNhd_product_z (U : Set (ℂ × ℂ × ℂ)) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => p.1) U := by
  intro _ _
  exact analyticAt_fst

/-- The first branch coordinate `v₁` is analytic on any product-cover piece. -/
theorem analyticOnNhd_product_v1 (U : Set (ℂ × ℂ × ℂ)) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => p.2.1) U := by
  intro _ _
  exact analyticAt_fst.comp analyticAt_snd

/-- The second branch coordinate `v₂` is analytic on any product-cover piece. -/
theorem analyticOnNhd_product_v2 (U : Set (ℂ × ℂ × ℂ)) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => p.2.2) U := by
  intro _ _
  exact analyticAt_snd.comp analyticAt_snd

/-- The analytic-germ base coordinate on a product-cover piece. -/
noncomputable def zCoordGen (U : Set (ℂ × ℂ × ℂ)) : analyticSubringGen U :=
  ⟨(↑(fun p : ℂ × ℂ × ℂ => p.1) : Germ (𝓟 U) ℂ),
    fun p : ℂ × ℂ × ℂ => p.1, analyticOnNhd_product_z U, rfl⟩

/-- The analytic-germ first branch coordinate on a product-cover piece. -/
noncomputable def v1CoordGen (U : Set (ℂ × ℂ × ℂ)) : analyticSubringGen U :=
  ⟨(↑(fun p : ℂ × ℂ × ℂ => p.2.1) : Germ (𝓟 U) ℂ),
    fun p : ℂ × ℂ × ℂ => p.2.1, analyticOnNhd_product_v1 U, rfl⟩

/-- The analytic-germ second branch coordinate on a product-cover piece. -/
noncomputable def v2CoordGen (U : Set (ℂ × ℂ × ℂ)) : analyticSubringGen U :=
  ⟨(↑(fun p : ℂ × ℂ × ℂ => p.2.2) : Germ (𝓟 U) ℂ),
    fun p : ℂ × ℂ × ℂ => p.2.2, analyticOnNhd_product_v2 U, rfl⟩

/-- If `v₁` is pointwise nonzero on the carrier, then its meromorphic field element is nonzero. -/
theorem v1CoordGen_algebraMap_ne_zero_of_forall {U : Set (ℂ × ℂ × ℂ)}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hv1 : ∀ p ∈ U, p.2.1 ≠ 0) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U) ≠ 0 := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  intro h
  have hmap0 : algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U)
      = algebraMap (analyticSubringGen U) (meroFieldGen U) 0 := by
    simpa using h
  have hv0 : v1CoordGen U = 0 :=
    (IsFractionRing.injective (analyticSubringGen U) (meroFieldGen U)) hmap0
  have hgerm : (v1CoordGen U : Germ (𝓟 U) ℂ) = 0 := by
    exact congrArg Subtype.val hv0
  rw [show (v1CoordGen U : Germ (𝓟 U) ℂ)
        = (↑(fun p : ℂ × ℂ × ℂ => p.2.1) : Germ (𝓟 U) ℂ) from rfl,
      ← Germ.coe_zero, Germ.coe_eq] at hgerm
  obtain ⟨p, hp⟩ := hUne
  exact hv1 p hp (Filter.eventually_principal.mp hgerm p hp)

/-- If `v₂` is pointwise nonzero on the carrier, then its meromorphic field element is nonzero. -/
theorem v2CoordGen_algebraMap_ne_zero_of_forall {U : Set (ℂ × ℂ × ℂ)}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hv2 : ∀ p ∈ U, p.2.2 ≠ 0) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U) ≠ 0 := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  intro h
  have hmap0 : algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U)
      = algebraMap (analyticSubringGen U) (meroFieldGen U) 0 := by
    simpa using h
  have hv0 : v2CoordGen U = 0 :=
    (IsFractionRing.injective (analyticSubringGen U) (meroFieldGen U)) hmap0
  have hgerm : (v2CoordGen U : Germ (𝓟 U) ℂ) = 0 := by
    exact congrArg Subtype.val hv0
  rw [show (v2CoordGen U : Germ (𝓟 U) ℂ)
        = (↑(fun p : ℂ × ℂ × ℂ => p.2.2) : Germ (𝓟 U) ℂ) from rfl,
      ← Germ.coe_zero, Germ.coe_eq] at hgerm
  obtain ⟨p, hp⟩ := hUne
  exact hv2 p hp (Filter.eventually_principal.mp hgerm p hp)

/-- On a piece of the common pullback cover, `v₁` is a nonzero meromorphic field element. -/
theorem v1CoordGen_algebraMap_ne_zero_of_subset_commonPullback {U : Set (ℂ × ℂ × ℂ)}
    {c₁ c₂ : ℂ} {n m : ℕ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hsub : U ⊆ commonPullback c₁ c₂ n m) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U) ≠ 0 :=
  v1CoordGen_algebraMap_ne_zero_of_forall hUo hUc hUne (fun _ hp => (hsub hp).2.1)

/-- On a piece of the common pullback cover, `v₂` is a nonzero meromorphic field element. -/
theorem v2CoordGen_algebraMap_ne_zero_of_subset_commonPullback {U : Set (ℂ × ℂ × ℂ)}
    {c₁ c₂ : ℂ} {n m : ℕ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hsub : U ⊆ commonPullback c₁ c₂ n m) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U) ≠ 0 :=
  v2CoordGen_algebraMap_ne_zero_of_forall hUo hUc hUne (fun _ hp => (hsub hp).2.2.2)

/-- The `c₁` product-cover deck is analytic. -/
theorem analyticOnNhd_deckMap₁ (ζ : ℂ) (U : Set (ℂ × ℂ × ℂ)) :
    AnalyticOnNhd ℂ (deckMap₁ ζ) U := by
  intro _ _
  exact analyticAt_fst.prod
    ((analyticAt_const.mul (analyticAt_fst.comp analyticAt_snd)).prod
      (analyticAt_snd.comp analyticAt_snd))

/-- The `c₂` product-cover deck is analytic. -/
theorem analyticOnNhd_deckMap₂ (ζ : ℂ) (U : Set (ℂ × ℂ × ℂ)) :
    AnalyticOnNhd ℂ (deckMap₂ ζ) U := by
  intro _ _
  exact analyticAt_fst.prod
    ((analyticAt_fst.comp analyticAt_snd).prod
      (analyticAt_const.mul (analyticAt_snd.comp analyticAt_snd)))

/-- `deckMap₁ ζ` followed by `deckMap₁ ζ⁻¹` is the identity. -/
theorem deckMap₁_comp_inv_eqOn {ζ : ℂ} (hζ : ζ ≠ 0) (U : Set (ℂ × ℂ × ℂ)) :
    Set.EqOn (deckMap₁ ζ ∘ deckMap₁ ζ⁻¹) id U := by
  intro p _
  simp [deckMap₁, hζ]

/-- `deckMap₁ ζ⁻¹` followed by `deckMap₁ ζ` is the identity. -/
theorem deckMap₁_inv_comp_eqOn {ζ : ℂ} (hζ : ζ ≠ 0) (U : Set (ℂ × ℂ × ℂ)) :
    Set.EqOn (deckMap₁ ζ⁻¹ ∘ deckMap₁ ζ) id U := by
  intro p _
  simp [deckMap₁, hζ]

/-- `deckMap₂ ζ` followed by `deckMap₂ ζ⁻¹` is the identity. -/
theorem deckMap₂_comp_inv_eqOn {ζ : ℂ} (hζ : ζ ≠ 0) (U : Set (ℂ × ℂ × ℂ)) :
    Set.EqOn (deckMap₂ ζ ∘ deckMap₂ ζ⁻¹) id U := by
  intro p _
  simp [deckMap₂, hζ]

/-- `deckMap₂ ζ⁻¹` followed by `deckMap₂ ζ` is the identity. -/
theorem deckMap₂_inv_comp_eqOn {ζ : ℂ} (hζ : ζ ≠ 0) (U : Set (ℂ × ℂ × ℂ)) :
    Set.EqOn (deckMap₂ ζ⁻¹ ∘ deckMap₂ ζ) id U := by
  intro p _
  simp [deckMap₂, hζ]

/-- The `c₁` deck fixes the base coordinate. -/
theorem zCoordGen_deckMap₁ {U : Set (ℂ × ℂ × ℂ)} {ζ : ℂ}
    (hmaps : Set.MapsTo (deckMap₁ ζ) U U) :
    (zCoordGen U : Germ (𝓟 U) ℂ).compTendsto (deckMap₁ ζ)
        (tendsto_principal_principal.mpr hmaps)
      = (zCoordGen U : Germ (𝓟 U) ℂ) := by
  change (↑(fun p : ℂ × ℂ × ℂ => p.1) : Germ (𝓟 U) ℂ).compTendsto
      (deckMap₁ ζ) (tendsto_principal_principal.mpr hmaps)
    = (↑(fun p : ℂ × ℂ × ℂ => p.1) : Germ (𝓟 U) ℂ)
  rw [Germ.coe_compTendsto]
  rfl

/-- The `c₁` deck scales the first branch coordinate. -/
theorem v1CoordGen_deckMap₁ {U : Set (ℂ × ℂ × ℂ)} {ζ : ℂ}
    (hmaps : Set.MapsTo (deckMap₁ ζ) U U) :
    (v1CoordGen U : Germ (𝓟 U) ℂ).compTendsto (deckMap₁ ζ)
        (tendsto_principal_principal.mpr hmaps)
      = ((constToAnalyticGen U ζ : analyticSubringGen U) : Germ (𝓟 U) ℂ)
        * (v1CoordGen U : Germ (𝓟 U) ℂ) := by
  change (↑(fun p : ℂ × ℂ × ℂ => p.2.1) : Germ (𝓟 U) ℂ).compTendsto
      (deckMap₁ ζ) (tendsto_principal_principal.mpr hmaps)
    = (↑(fun _ : ℂ × ℂ × ℂ => ζ) : Germ (𝓟 U) ℂ)
      * (↑(fun p : ℂ × ℂ × ℂ => p.2.1) : Germ (𝓟 U) ℂ)
  rw [Germ.coe_compTendsto, ← Germ.coe_mul]
  rfl

/-- The `c₁` deck fixes the second branch coordinate. -/
theorem v2CoordGen_deckMap₁ {U : Set (ℂ × ℂ × ℂ)} {ζ : ℂ}
    (hmaps : Set.MapsTo (deckMap₁ ζ) U U) :
    (v2CoordGen U : Germ (𝓟 U) ℂ).compTendsto (deckMap₁ ζ)
        (tendsto_principal_principal.mpr hmaps)
      = (v2CoordGen U : Germ (𝓟 U) ℂ) := by
  change (↑(fun p : ℂ × ℂ × ℂ => p.2.2) : Germ (𝓟 U) ℂ).compTendsto
      (deckMap₁ ζ) (tendsto_principal_principal.mpr hmaps)
    = (↑(fun p : ℂ × ℂ × ℂ => p.2.2) : Germ (𝓟 U) ℂ)
  rw [Germ.coe_compTendsto]
  rfl

/-- The `c₂` deck fixes the base coordinate. -/
theorem zCoordGen_deckMap₂ {U : Set (ℂ × ℂ × ℂ)} {ζ : ℂ}
    (hmaps : Set.MapsTo (deckMap₂ ζ) U U) :
    (zCoordGen U : Germ (𝓟 U) ℂ).compTendsto (deckMap₂ ζ)
        (tendsto_principal_principal.mpr hmaps)
      = (zCoordGen U : Germ (𝓟 U) ℂ) := by
  change (↑(fun p : ℂ × ℂ × ℂ => p.1) : Germ (𝓟 U) ℂ).compTendsto
      (deckMap₂ ζ) (tendsto_principal_principal.mpr hmaps)
    = (↑(fun p : ℂ × ℂ × ℂ => p.1) : Germ (𝓟 U) ℂ)
  rw [Germ.coe_compTendsto]
  rfl

/-- The `c₂` deck fixes the first branch coordinate. -/
theorem v1CoordGen_deckMap₂ {U : Set (ℂ × ℂ × ℂ)} {ζ : ℂ}
    (hmaps : Set.MapsTo (deckMap₂ ζ) U U) :
    (v1CoordGen U : Germ (𝓟 U) ℂ).compTendsto (deckMap₂ ζ)
        (tendsto_principal_principal.mpr hmaps)
      = (v1CoordGen U : Germ (𝓟 U) ℂ) := by
  change (↑(fun p : ℂ × ℂ × ℂ => p.2.1) : Germ (𝓟 U) ℂ).compTendsto
      (deckMap₂ ζ) (tendsto_principal_principal.mpr hmaps)
    = (↑(fun p : ℂ × ℂ × ℂ => p.2.1) : Germ (𝓟 U) ℂ)
  rw [Germ.coe_compTendsto]
  rfl

/-- The `c₂` deck scales the second branch coordinate. -/
theorem v2CoordGen_deckMap₂ {U : Set (ℂ × ℂ × ℂ)} {ζ : ℂ}
    (hmaps : Set.MapsTo (deckMap₂ ζ) U U) :
    (v2CoordGen U : Germ (𝓟 U) ℂ).compTendsto (deckMap₂ ζ)
        (tendsto_principal_principal.mpr hmaps)
      = ((constToAnalyticGen U ζ : analyticSubringGen U) : Germ (𝓟 U) ℂ)
        * (v2CoordGen U : Germ (𝓟 U) ℂ) := by
  change (↑(fun p : ℂ × ℂ × ℂ => p.2.2) : Germ (𝓟 U) ℂ).compTendsto
      (deckMap₂ ζ) (tendsto_principal_principal.mpr hmaps)
    = (↑(fun _ : ℂ × ℂ × ℂ => ζ) : Germ (𝓟 U) ℂ)
      * (↑(fun p : ℂ × ℂ × ℂ => p.2.2) : Germ (𝓟 U) ℂ)
  rw [Germ.coe_compTendsto, ← Germ.coe_mul]
  rfl

/-- **The concrete product-cover `c₁` deck supplies `monoF`.**  On any connected open product-cover
piece invariant under `deckMap₁ ζ₀` and its inverse, the map `(z,v₁,v₂) ↦ (z,ζ₀v₁,v₂)` is a
z-fixing meromorphic field automorphism: it fixes the second branch coordinate and scales the first. -/
theorem monoF_witness_product_deckMap₁ {U : Set (ℂ × ℂ × ℂ)}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroFieldGen U)]
    (d : ℕ) (ζ₀ : ℂ) (hζ₀ : ζ₀ ≠ 0)
    (hmaps : Set.MapsTo (deckMap₁ ζ₀) U U)
    (hmaps' : Set.MapsTo (deckMap₁ ζ₀⁻¹) U U)
    (hord : d < orderOf ζ₀)
    (hK : ∀ k : K,
      precompMeroEquivGen U (analyticOnNhd_deckMap₁ ζ₀ U) (analyticOnNhd_deckMap₁ ζ₀⁻¹ U)
        hmaps hmaps' (deckMap₁_comp_inv_eqOn hζ₀ U) (deckMap₁_inv_comp_eqOn hζ₀ U)
        hUo hUc hUne (algebraMap K (meroFieldGen U) k)
        = algebraMap K (meroFieldGen U) k) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    ∃ (σ : meroFieldGen U ≃ₐ[K] meroFieldGen U) (ζ : meroFieldGen U) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧
      σ (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U))
        = algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U) ∧
      σ ζ = ζ ∧
      σ (algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U))
        = ζ * algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U) := by
  exact monoF_witness_gen U hUo hUc hUne (v1CoordGen U) (v2CoordGen U) d ζ₀
    (analyticOnNhd_deckMap₁ ζ₀ U) (analyticOnNhd_deckMap₁ ζ₀⁻¹ U)
    hmaps hmaps' (deckMap₁_comp_inv_eqOn hζ₀ U) (deckMap₁_inv_comp_eqOn hζ₀ U)
    hord (v1CoordGen_deckMap₁ hmaps) (v2CoordGen_deckMap₁ hmaps) hK

/-- **The concrete product-cover `c₂` deck supplies `monoG`.**  Symmetric to
`monoF_witness_product_deckMap₁`: `(z,v₁,v₂) ↦ (z,v₁,ζ₀v₂)` scales the second branch coordinate on
the several-variable meromorphic field. -/
theorem monoG_witness_product_deckMap₂ {U : Set (ℂ × ℂ × ℂ)}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroFieldGen U)]
    (d : ℕ) (ζ₀ : ℂ) (hζ₀ : ζ₀ ≠ 0)
    (hmaps : Set.MapsTo (deckMap₂ ζ₀) U U)
    (hmaps' : Set.MapsTo (deckMap₂ ζ₀⁻¹) U U)
    (hord : d < orderOf ζ₀)
    (hK : ∀ k : K,
      precompMeroEquivGen U (analyticOnNhd_deckMap₂ ζ₀ U) (analyticOnNhd_deckMap₂ ζ₀⁻¹ U)
        hmaps hmaps' (deckMap₂_comp_inv_eqOn hζ₀ U) (deckMap₂_inv_comp_eqOn hζ₀ U)
        hUo hUc hUne (algebraMap K (meroFieldGen U) k)
        = algebraMap K (meroFieldGen U) k) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    ∃ (σ : meroFieldGen U ≃ₐ[K] meroFieldGen U) (ζ : meroFieldGen U),
      d < orderOf ζ ∧ σ ζ = ζ ∧
      σ (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U))
        = ζ * algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U) := by
  exact monoG_witness_gen U hUo hUc hUne (v2CoordGen U) d ζ₀
    (analyticOnNhd_deckMap₂ ζ₀ U) (analyticOnNhd_deckMap₂ ζ₀⁻¹ U)
    hmaps hmaps' (deckMap₂_comp_inv_eqOn hζ₀ U) (deckMap₂_inv_comp_eqOn hζ₀ U)
    hord (v2CoordGen_deckMap₂ hmaps) hK

/-- **Product-cover hDisc carrier close.**  On a connected open product-cover piece, the concrete
z-fixing decks `deckMap₁` and `deckMap₂`, if available with unbounded dyadic order and base-field
fixing, give `NoRelation` for the two branch-coordinate meromorphic functions.  This is the
`meroFieldGen` version of the disconnected/disconnected hdisc assembly; the remaining geometric input
is exactly the construction of such invariant connected cover pieces and their `K = ℂ(z)` embedding. -/
theorem noRelation_productCover_of_deckMaps {U : Set (ℂ × ℂ × ℂ)}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroFieldGen U)]
    (hF : haveI := isDomain_analyticSubringGen U hUo hUc hUne
      algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U) ≠ 0)
    (hG0 : haveI := isDomain_analyticSubringGen U hUo hUc hUne
      algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U) ≠ 0)
    (deckF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (hζ₀ : ζ₀ ≠ 0)
        (hmaps : Set.MapsTo (deckMap₁ ζ₀) U U)
        (hmaps' : Set.MapsTo (deckMap₁ ζ₀⁻¹) U U),
        d < orderOf ζ₀ ∧
        ∀ k : K,
          precompMeroEquivGen U (analyticOnNhd_deckMap₁ ζ₀ U) (analyticOnNhd_deckMap₁ ζ₀⁻¹ U)
            hmaps hmaps' (deckMap₁_comp_inv_eqOn hζ₀ U) (deckMap₁_inv_comp_eqOn hζ₀ U)
            hUo hUc hUne (algebraMap K (meroFieldGen U) k)
            = algebraMap K (meroFieldGen U) k)
    (deckG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (hζ₀ : ζ₀ ≠ 0)
        (hmaps : Set.MapsTo (deckMap₂ ζ₀) U U)
        (hmaps' : Set.MapsTo (deckMap₂ ζ₀⁻¹) U U),
        d < orderOf ζ₀ ∧
        ∀ k : K,
          precompMeroEquivGen U (analyticOnNhd_deckMap₂ ζ₀ U) (analyticOnNhd_deckMap₂ ζ₀⁻¹ U)
            hmaps hmaps' (deckMap₂_comp_inv_eqOn hζ₀ U) (deckMap₂_inv_comp_eqOn hζ₀ U)
            hUo hUc hUne (algebraMap K (meroFieldGen U) k)
            = algebraMap K (meroFieldGen U) k) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    NoRelation K
      (algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U))
      (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U)) := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  refine q62_disconnected_both
    (algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U))
    (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U))
    hF hG0 ?_ ?_
  · intro d
    obtain ⟨ζ₀, hζ₀, hmaps, hmaps', hord, hK⟩ := deckF d
    exact monoF_witness_product_deckMap₁ hUo hUc hUne d ζ₀ hζ₀ hmaps hmaps' hord hK
  · intro d
    obtain ⟨ζ₀, hζ₀, hmaps, hmaps', hord, hK⟩ := deckG d
    exact monoG_witness_product_deckMap₂ hUo hUc hUne d ζ₀ hζ₀ hmaps hmaps' hord hK

/-- **Product-cover hDisc close with automatic `ℂ(z)` fixing.**  The base field is embedded as
`ℂ(zCoordGen)` via `ratfuncToMeroViaGen`. Since both concrete deck maps fix `zCoordGen`, the whole
`RatFunc ℂ` base is fixed automatically; the only deck inputs left are invariant connected carrier
pieces and unbounded-order multipliers. -/
theorem noRelation_productCover_projectionBase_of_deckMaps {U : Set (ℂ × ℂ × ℂ)}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hzInf : ((fun p : ℂ × ℂ × ℂ => p.1) '' U).Infinite)
    (hF :
      haveI := isDomain_analyticSubringGen U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
        (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
          rfl hzInf hUo hUc hUne).toAlgebra
      algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U) ≠ 0)
    (hG0 :
      haveI := isDomain_analyticSubringGen U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
        (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
          rfl hzInf hUo hUc hUne).toAlgebra
      algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U) ≠ 0)
    (deckF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₁ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₁ ζ₀⁻¹) U U),
        d < orderOf ζ₀)
    (deckG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₂ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₂ ζ₀⁻¹) U U),
        d < orderOf ζ₀) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
      (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
        rfl hzInf hUo hUc hUne).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U))
      (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U)) := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
    (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
      rfl hzInf hUo hUc hUne).toAlgebra
  refine noRelation_productCover_of_deckMaps (U := U) (K := RatFunc ℂ)
    hUo hUc hUne hF hG0 ?_ ?_
  · intro d
    obtain ⟨ζ₀, hζ₀, hmaps, hmaps', hord⟩ := deckF d
    refine ⟨ζ₀, hζ₀, hmaps, hmaps', hord, ?_⟩
    intro k
    have hfix : precompAnalyticGen U (analyticOnNhd_deckMap₁ ζ₀ U) hmaps (zCoordGen U)
        = zCoordGen U := by
      apply Subtype.ext
      rw [precompAnalyticGen_coe]
      exact zCoordGen_deckMap₁ hmaps
    exact precompMeroEquivGen_ratfuncToMeroViaGen_fix U
      (analyticOnNhd_deckMap₁ ζ₀ U) (analyticOnNhd_deckMap₁ ζ₀⁻¹ U)
      hmaps hmaps' (deckMap₁_comp_inv_eqOn hζ₀ U) (deckMap₁_inv_comp_eqOn hζ₀ U)
      hUo hUc hUne (p₀ := zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
      rfl hzInf hfix k
  · intro d
    obtain ⟨ζ₀, hζ₀, hmaps, hmaps', hord⟩ := deckG d
    refine ⟨ζ₀, hζ₀, hmaps, hmaps', hord, ?_⟩
    intro k
    have hfix : precompAnalyticGen U (analyticOnNhd_deckMap₂ ζ₀ U) hmaps (zCoordGen U)
        = zCoordGen U := by
      apply Subtype.ext
      rw [precompAnalyticGen_coe]
      exact zCoordGen_deckMap₂ hmaps
    exact precompMeroEquivGen_ratfuncToMeroViaGen_fix U
      (analyticOnNhd_deckMap₂ ζ₀ U) (analyticOnNhd_deckMap₂ ζ₀⁻¹ U)
      hmaps hmaps' (deckMap₂_comp_inv_eqOn hζ₀ U) (deckMap₂_inv_comp_eqOn hζ₀ U)
      hUo hUc hUne (p₀ := zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
      rfl hzInf hfix k

/-- **Product-cover hDisc close on common-pullback pieces.**  If the connected carrier lies inside
the common pullback cover, then `v₁` and `v₂` are automatically nonzero.  Combined with the
projection-base version, this leaves only the actual geometric deck inputs: invariant connected
pieces, infinite base projection, and unbounded z-fixing deck maps. -/
theorem noRelation_productCover_projectionBase_of_commonPullback_deckMaps
    {U : Set (ℂ × ℂ × ℂ)} {c₁ c₂ : ℂ} {n m : ℕ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hzInf : ((fun p : ℂ × ℂ × ℂ => p.1) '' U).Infinite)
    (hsub : U ⊆ commonPullback c₁ c₂ n m)
    (deckF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₁ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₁ ζ₀⁻¹) U U),
        d < orderOf ζ₀)
    (deckG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₂ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₂ ζ₀⁻¹) U U),
        d < orderOf ζ₀) :
    haveI := isDomain_analyticSubringGen U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
      (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
        rfl hzInf hUo hUc hUne).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U))
      (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U)) := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
    (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
      rfl hzInf hUo hUc hUne).toAlgebra
  refine noRelation_productCover_projectionBase_of_deckMaps hUo hUc hUne hzInf ?_ ?_ deckF deckG
  · exact v1CoordGen_algebraMap_ne_zero_of_subset_commonPullback hUo hUc hUne hsub
  · exact v2CoordGen_algebraMap_ne_zero_of_subset_commonPullback hUo hUc hUne hsub

end Bottcher
