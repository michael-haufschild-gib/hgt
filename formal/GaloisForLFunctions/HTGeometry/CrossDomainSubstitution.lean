import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge

/-!
# Substituting an inner germ into the meromorphic field of its target

Precomposition by an analytic map `g : U → V` carries analytic functions on `V` to analytic
functions on `U`, hence is a ring homomorphism of the analytic-germ domains.  When a nonzero
analytic function on `V` cannot vanish identically along `g` — the identity theorem for a
nonconstant inner map — the homomorphism is injective and extends to the meromorphic function
fields.

That extension is the transport used to move algebraic relations between the jets of an outer germ
from its own domain to the domain of a family of inner maps.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Bottcher

variable {U V : Set ℂ}

/-- Precomposition preserves analytic germs across domains. -/
theorem substGerm_mem_analyticSubring {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) {a : Germ (𝓟 V) ℂ} (ha : a ∈ analyticSubring V) :
    a.compTendsto g (tendsto_principal_principal.mpr hmaps) ∈ analyticSubring U := by
  obtain ⟨f, hf, rfl⟩ := ha
  exact ⟨f ∘ g, hf.comp hg hmaps,
    (Germ.coe_compTendsto f (tendsto_principal_principal.mpr hmaps)).symm⟩

/-- Precomposition as a ring homomorphism between germ rings over different domains. -/
noncomputable def substGermHom {g : ℂ → ℂ} (h : Tendsto g (𝓟 U) (𝓟 V)) :
    Germ (𝓟 V) ℂ →+* Germ (𝓟 U) ℂ where
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

/-- Substitution of an inner analytic map as a ring homomorphism of analytic-germ domains. -/
noncomputable def substAnalytic {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) : analyticSubring V →+* analyticSubring U :=
  ((substGermHom (tendsto_principal_principal.mpr hmaps)).comp
      (analyticSubring V).subtype).codRestrict (analyticSubring U)
    (fun x => substGerm_mem_analyticSubring hg hmaps x.2)

@[simp] theorem substAnalytic_coe {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) (a : analyticSubring V) :
    ((substAnalytic hg hmaps a : analyticSubring U) : Germ (𝓟 U) ℂ)
      = (a : Germ (𝓟 V) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps) := rfl

theorem substAnalytic_analyticFunctionElement {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f V) :
    substAnalytic hg hmaps (analyticFunctionElement f hf)
      = analyticFunctionElement (f ∘ g) (hf.comp hg hmaps) := by
  apply Subtype.ext
  rw [substAnalytic_coe]
  exact Germ.coe_compTendsto f (tendsto_principal_principal.mpr hmaps)

/-- The identity-theorem hypothesis: a function analytic on the target vanishing along the inner
map vanishes identically. -/
def SubstitutionFaithful (U V : Set ℂ) (g : ℂ → ℂ) : Prop :=
  ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f V → (∀ t ∈ U, f (g t) = 0) → ∀ z ∈ V, f z = 0

/-- **A faithful substitution is injective on analytic germs.** -/
theorem substAnalytic_injective {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) (hfaith : SubstitutionFaithful U V g) :
    Function.Injective (substAnalytic hg hmaps) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨f, hf, hfa⟩ := a.2
  have h1 : ((substAnalytic hg hmaps a : analyticSubring U) : Germ (𝓟 U) ℂ) = 0 := by
    rw [ha]; rfl
  rw [substAnalytic_coe, ← hfa] at h1
  have h1' : ((f ∘ g : ℂ → ℂ) : Germ (𝓟 U) ℂ) = 0 := by
    rw [← Germ.coe_compTendsto f (tendsto_principal_principal.mpr hmaps)]
    exact h1
  have h2 : ∀ t ∈ U, f (g t) = 0 := by
    have hev : (f ∘ g : ℂ → ℂ) =ᶠ[𝓟 U] 0 :=
      Germ.coe_eq.mp (h1'.trans (Germ.coe_zero (l := 𝓟 U) (M := ℂ)).symm)
    intro t ht
    exact (eventually_principal.mp hev) t ht
  have h3 := hfaith f hf h2
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, ← hfa]
  have : (f : ℂ → ℂ) =ᶠ[𝓟 V] 0 := eventually_principal.mpr h3
  exact (Germ.coe_eq.mpr this).trans (Germ.coe_zero (l := 𝓟 V) (M := ℂ))

/-! ## The substitution homomorphism of meromorphic fields -/

/-- **Substitution of an inner germ, on meromorphic function fields.** -/
noncomputable def substMero (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U V)
    (hfaith : SubstitutionFaithful U V g) : meroField V →+* meroField U :=
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
  IsFractionRing.lift (A := analyticSubring V) (K := meroField V) (L := meroField U)
    (g := (algebraMap (analyticSubring U) (meroField U)).comp (substAnalytic hg hmaps))
    (by
      rw [RingHom.coe_comp]
      exact Function.Injective.comp (IsFractionRing.injective (analyticSubring U) (meroField U))
        (substAnalytic_injective hg hmaps hfaith))

theorem substMero_analyticMeroElement (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U V)
    (hfaith : SubstitutionFaithful U V g) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f V) :
    substMero hUo hUc hUne hVo hVc hVne hg hmaps hfaith (analyticMeroElement f hf)
      = analyticMeroElement (f ∘ g) (hf.comp hg hmaps) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
  show IsFractionRing.lift _ (algebraMap (analyticSubring V) (meroField V)
      (analyticFunctionElement f hf)) = _
  rw [IsFractionRing.lift_algebraMap]
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [substAnalytic_analyticFunctionElement]
  rfl

end GaloisForLFunctions.HTGeometry
