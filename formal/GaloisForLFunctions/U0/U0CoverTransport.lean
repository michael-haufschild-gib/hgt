/-
# Cross-set precomposition and the u₀ transcendence transport to the cover carrier

The genuine monodromy carrier of `u₀ ⟂ φ_b` is `Bottcher.meroField Ã` on the cover annulus
`Ã = {ρ < |w| < R}`, where `φ_b = w` (the coordinate) and the base `z = p₀ = w^{2ⁿ}` (the
`2ⁿ`-fold projection), `ℂ(z) = ℂ(p₀)` (parallel Böttcher construction
`precompAnalytic_rotation_coverProj_fix`). The u₀ germ there is `u₀ ∘ p₀` (`w ↦ u₀(w^{2ⁿ})`), and the
`hG` input of `noRelation_of_mixed_lifts` is its transcendence over `ℂ(z)`.

That transcendence **transports** from the base: `u₀` is transcendental over `ℂ(z)` on a base region
`B` (`U0MeroCarrier.u0Mero_transcendental`), and precomposition by the projection `p₀ : Ã → B` is an
injective `ℂ(z)`-algebra hom `meroField B → meroField Ã` sending `u₀ ↦ u₀∘p₀` and `z ↦ p₀`, so
`transcendental_algHom_inj` carries transcendence across. The injectivity is the identity theorem: if
`a∘p₀ = 0` on `Ã` then `a = 0` on `p₀(Ã) = B`.

This file builds the **cross-set precomposition** `analyticSubring V → analyticSubring U` (for an
analytic `g : U → V`), generalizing `Bottcher.precompAnalytic` (the self-map case `V = U`), plus its
injectivity under surjectivity of `g`. These are stable (committed `MeromorphicField` primitives only),
decoupled from the in-flux cover construction.
-/
import GaloisForLFunctions.Bottcher.MeromorphicField
import GaloisForLFunctions.U0.U0MeroCarrier

open Filter Topology Bottcher U0Transcendence

namespace U0CoverTransport

variable {U V : Set ℂ}

/-- **Cross-set analytic membership.** If `a` is the germ of a function analytic on `V` and
`g : U → V` is analytic with `MapsTo g U V`, then `a ∘ g` is the germ of a function analytic on `U`.
Generalizes `Bottcher.precomp_mem_analyticSubring` from self-maps to maps `U → V`. -/
theorem precomp_mem_analyticSubring_cross {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V)) {a : Germ (𝓟 V) ℂ}
    (ha : a ∈ analyticSubring V) :
    a.compTendsto g h ∈ analyticSubring U := by
  obtain ⟨f, hf, rfl⟩ := ha
  exact ⟨f ∘ g, hf.comp hg hmaps, (Germ.coe_compTendsto f h).symm⟩

/-- **Cross-set precomposition as a ring hom on germs** `Germ (𝓟 V) ℂ → Germ (𝓟 U) ℂ`, `a ↦ a ∘ g`. -/
noncomputable def precompGermHomCross {g : ℂ → ℂ} (h : Tendsto g (𝓟 U) (𝓟 V)) :
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

/-- **Cross-set precomposition as a ring hom on analytic subrings** `analyticSubring V →
analyticSubring U`, for an analytic `g : U → V`. The `V = U` case is `Bottcher.precompAnalytic`. -/
noncomputable def precompAnalyticCross {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V)) :
    analyticSubring V →+* analyticSubring U :=
  ((precompGermHomCross h).comp (analyticSubring V).subtype).codRestrict (analyticSubring U)
    (fun x => precomp_mem_analyticSubring_cross hg hmaps h x.2)

@[simp] theorem precompAnalyticCross_coe {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V)) (a : analyticSubring V) :
    ((precompAnalyticCross hg hmaps h a : analyticSubring U) : Germ (𝓟 U) ℂ)
      = (a : Germ (𝓟 V) ℂ).compTendsto g h := rfl

/-- **Germ-level injectivity of `· ∘ g` under surjectivity.** If `g` maps `U` onto `V`, then
`x ↦ x.compTendsto g h` is injective on `Germ (𝓟 V) ℂ`: two germs agreeing after `∘g` on `U` agree on
`g(U) = V`. -/
theorem compTendsto_injective_of_surjOn {g : ℂ → ℂ} (h : Tendsto g (𝓟 U) (𝓟 V))
    (hsurj : Set.SurjOn g U V) {x y : Germ (𝓟 V) ℂ}
    (hxy : x.compTendsto g h = y.compTendsto g h) : x = y := by
  induction x using Germ.inductionOn with
  | _ F => induction y using Germ.inductionOn with
    | _ G =>
      rw [Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_eq, eventuallyEq_principal] at hxy
      rw [Germ.coe_eq, eventuallyEq_principal]
      intro z hz
      obtain ⟨w, hw, rfl⟩ := hsurj hz
      exact hxy hw

theorem precompAnalyticCross_injective {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V)) (hsurj : Set.SurjOn g U V) :
    Function.Injective (precompAnalyticCross hg hmaps h) := by
  intro a b hab
  apply Subtype.ext
  apply compTendsto_injective_of_surjOn h hsurj
  simpa only [precompAnalyticCross_coe] using congrArg Subtype.val hab

/-- **Cross-set precomposition lifted to the meromorphic fields** `meroField V → meroField U`. Since
`precompAnalyticCross` is an injective ring hom between domains, it sends non-zero-divisors to
non-zero-divisors, so it extends to the fraction fields by `IsLocalization.map`. This is the
`ℂ(z)`-algebra hom (over the projection `z ↦ p₀`) that carries `u₀`'s transcendence from the base to the
cover via `transcendental_algHom_inj`. -/
noncomputable def precompMeroCross {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V)) (hsurj : Set.SurjOn g U V)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI := isDomain_analyticSubring V hVo hVc hVne
    meroField V →+* meroField U :=
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI := isDomain_analyticSubring V hVo hVc hVne
  IsLocalization.map (meroField U) (precompAnalyticCross hg hmaps h)
    (M := nonZeroDivisors (analyticSubring V)) (T := nonZeroDivisors (analyticSubring U))
    (fun x hx => by
      rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
      exact fun hc => (mem_nonZeroDivisors_iff_ne_zero.mp hx)
        (precompAnalyticCross_injective hg hmaps h hsurj (by rw [hc, map_zero])))

/-- `precompMeroCross` is injective — it is a ring hom out of the field `meroField V`. -/
theorem precompMeroCross_injective {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V)) (hsurj : Set.SurjOn g U V)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI := isDomain_analyticSubring V hVo hVc hVne
    Function.Injective (precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne) := by
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI := isDomain_analyticSubring V hVo hVc hVne
  exact (precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne).injective

/-- **Transcendence transports across the cover precomposition.** If both fraction fields carry a
`ℂ(z)`-algebra structure and `precompMeroCross` is `ℂ(z)`-linear (`hcompat`: it sends the base `ℂ(z)`
generator to the cover's), then it is an injective `ℂ(z)`-algebra hom, so it carries transcendence:
`x` transcendental over `ℂ(z)` in the base ⟹ `precompMeroCross x` transcendental over `ℂ(z)` in the
cover. Applied with `x = u₀`-on-base (`u0Mero_transcendental`) and the cover the annulus `Ã`, this is
exactly the `hG` input of `noRelation_of_mixed_lifts`; the only carrier-coupled hypothesis is `hcompat`
(`z ↦ p₀ = w^{2ⁿ}`). -/
theorem transcendental_precompMeroCross {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V)) (hsurj : Set.SurjOn g U V)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty)
    [haveI := isDomain_analyticSubring V hVo hVc hVne; Algebra (RatFunc ℂ) (meroField V)]
    [haveI := isDomain_analyticSubring U hUo hUc hUne; Algebra (RatFunc ℂ) (meroField U)]
    (hcompat : haveI := isDomain_analyticSubring U hUo hUc hUne
      haveI := isDomain_analyticSubring V hVo hVc hVne
      ∀ k : RatFunc ℂ, precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne
          (algebraMap (RatFunc ℂ) (meroField V) k) = algebraMap (RatFunc ℂ) (meroField U) k)
    {x : haveI := isDomain_analyticSubring V hVo hVc hVne; meroField V}
    (hx : haveI := isDomain_analyticSubring V hVo hVc hVne; Transcendental (RatFunc ℂ) x) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := isDomain_analyticSubring V hVo hVc hVne
    Transcendental (RatFunc ℂ)
      (precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne x) := by
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI := isDomain_analyticSubring V hVo hVc hVne
  let φ : meroField V →ₐ[RatFunc ℂ] meroField U :=
    { precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne with commutes' := hcompat }
  exact transcendental_algHom_inj φ
    (precompMeroCross_injective hg hmaps h hsurj hUo hUc hUne hVo hVc hVne) hx

end U0CoverTransport

namespace U0CoverTransport

/-- Concrete cover-transport of `u₀` transcendence: the base carrier theorem supplies `u₀`
transcendence, and cross-set precomposition carries it to the cover carrier under the projection's
`ℂ(z)`-compatibility. This is the cover-side `hG` input for the U0-phi lift route, with only the
projection algebra compatibility left explicit. -/
theorem u0_transcendental_precompMeroCross {U V : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V))
    (hsurj : Set.SurjOn g U V)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (hV_ext : V ⊆ U0NaturalBoundary.Ext)
    [haveI := isDomain_analyticSubring U hUo hUc hUne; Algebra (RatFunc ℂ) (meroField U)]
    (hcompat : haveI := isDomain_analyticSubring U hUo hUc hUne
      haveI := isDomain_analyticSubring V hVo hVc hVne
      letI : Algebra (RatFunc ℂ) (meroField V) := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
      ∀ k : RatFunc ℂ, precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne
          (algebraMap (RatFunc ℂ) (meroField V) k) = algebraMap (RatFunc ℂ) (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := isDomain_analyticSubring V hVo hVc hVne
    letI : Algebra (RatFunc ℂ) (meroField V) := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    Transcendental (RatFunc ℂ)
      (precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne
        (algebraMap (analyticSubring V) (meroField V) (U0MeroCarrier.u0AnSub hV_ext))) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  haveI := isDomain_analyticSubring V hVo hVc hVne
  letI : Algebra (RatFunc ℂ) (meroField V) := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
  exact transcendental_precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne hcompat
    (U0MeroCarrier.u0Mero_transcendental hVo hVc hVne hVinf hV_ext)

end U0CoverTransport

namespace U0CoverTransport

/-- `precompMeroCross` agrees with `precompAnalyticCross` on analytic numerator elements. -/
theorem precompMeroCross_algebraMap {U V : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V))
    (hsurj : Set.SurjOn g U V)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (a : analyticSubring V) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := isDomain_analyticSubring V hVo hVc hVne
    precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne
      (algebraMap (analyticSubring V) (meroField V) a)
      = algebraMap (analyticSubring U) (meroField U) (precompAnalyticCross hg hmaps h a) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  haveI := isDomain_analyticSubring V hVo hVc hVne
  rw [precompMeroCross, IsLocalization.map_eq]

end U0CoverTransport

namespace U0CoverTransport

/-- Cross-set precomposition fixes constant analytic germs. -/
theorem precompAnalyticCross_constToAnalytic {U V : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V))
    (c : ℂ) :
    precompAnalyticCross hg hmaps h (constToAnalytic V c) = constToAnalytic U c := by
  apply Subtype.ext
  rw [precompAnalyticCross_coe]
  change ((↑(fun _ : ℂ => c) : Germ (𝓟 V) ℂ).compTendsto g h)
      = (↑(fun _ : ℂ => c) : Germ (𝓟 U) ℂ)
  rw [Germ.coe_compTendsto]
  exact Germ.coe_eq.mpr (Filter.eventually_principal.mpr (fun _ _ => rfl))

/-- Cross-set precomposition sends the identity-base polynomial embedding on `V` to the projection-base
polynomial embedding on `U`, once the projection germ `p₀` is represented by the map `g`. -/
theorem precompAnalyticCross_polyToAnalyticVia {U V : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V))
    {p₀ : analyticSubring U} (hp0g : (p₀ : Germ (𝓟 U) ℂ) = ↑g) (q : Polynomial ℂ) :
    precompAnalyticCross hg hmaps h (polyToAnalytic V q) = polyToAnalyticVia U p₀ q := by
  have hcomp : (precompAnalyticCross hg hmaps h).comp (polyToAnalytic V) =
      polyToAnalyticVia U p₀ := by
    apply Polynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, polyToAnalyticVia_C]
      apply Subtype.ext
      rw [precompAnalyticCross_coe]
      change ((↑(fun z : ℂ => (Polynomial.C c).eval z) : Germ (𝓟 V) ℂ).compTendsto g h)
          = (↑(fun _ : ℂ => c) : Germ (𝓟 U) ℂ)
      rw [Germ.coe_compTendsto]
      simp
      exact fun _ _ => rfl
    · rw [RingHom.comp_apply, polyToAnalyticVia_X]
      apply Subtype.ext
      rw [precompAnalyticCross_coe]
      change ((↑(fun z : ℂ => Polynomial.X.eval z) : Germ (𝓟 V) ℂ).compTendsto g h)
          = (p₀ : Germ (𝓟 U) ℂ)
      rw [hp0g, Germ.coe_compTendsto]
      simp
      exact fun _ _ => rfl
  exact RingHom.congr_fun hcomp q

/-- The cross-set precomposition from a base region `V` to a cover region `U` is automatically
`RatFunc ℂ`-linear when the cover's base algebra is generated by the projection germ represented by
`g`. This discharges the `hcompat` input of the U0 precomp transport route from the concrete projection
identity. -/
theorem precompMeroCross_ratfuncToMeroVia {U V : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V))
    (hsurj : Set.SurjOn g U V)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    {p₀ : analyticSubring U} {f₀ : ℂ → ℂ} (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (hinf : (f₀ '' U).Infinite) (hp0g : (p₀ : Germ (𝓟 U) ℂ) = ↑g) (k : RatFunc ℂ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := isDomain_analyticSubring V hVo hVc hVne
    precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne
        (ratfuncToMero V hVo hVc hVne hVinf k)
      = ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne k := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  haveI := isDomain_analyticSubring V hVo hVc hVne
  have key : (precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne).comp
      (ratfuncToMero V hVo hVc hVne hVinf) = ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro p
    rw [RingHom.comp_apply,
        ratfuncToMero_algebraMap_polynomial V hVo hVc hVne hVinf p,
        show ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
          = polyToMeroVia p₀ p from IsFractionRing.lift_algebraMap _ p]
    show precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne
        (algebraMap (analyticSubring V) (meroField V) (polyToAnalytic V p)) = _
    rw [precompMeroCross_algebraMap, precompAnalyticCross_polyToAnalyticVia hg hmaps h hp0g]
    rfl
  exact RingHom.congr_fun key k

end U0CoverTransport
