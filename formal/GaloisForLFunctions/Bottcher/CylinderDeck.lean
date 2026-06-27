/-
# The genuine hDisc deck: pointwise cylinder-loop monodromy ⟹ monoF, on a FIXED cover

This is the CORRECT assembly for the disconnected monodromy — the one the value-annulus route
(`DeckAnnulus`) could not satisfy.  The defect there was bounded order: a deck fixing the second
coordinate on a value-annulus carrier `U_n` has order capped at `2ⁿ`, and raising `n` changes the
scaling coordinate `a₁ = bc₁^{1/2ⁿ}`.  `hliftF` instead needs, on ONE fixed cover `U`, a deck of order
`> d` for EVERY `d`, scaling the FIXED `a₁ = φ_{c₁}`.

That is exactly the disconnected cylinder-loop monodromy: on the cover `U` where the multivalued
`φ_{c₁}` is continued single-valued, going around a closed depth-`n` cylinder loop (enclosing a
Cantor-cluster of Brolin mass `2⁻ⁿ`) scales `φ_{c₁}` by `exp(2πi·2⁻ⁿ)` (`period_eq`:
`∮ d log φ_{c₁} = 2πi·mass`), of order `2ⁿ`, while the base point `z` returns to itself (the loop is
closed) so `φ_{c₂}` and `ℂ(z)` are fixed.  The Cantor structure supplies arbitrarily deep cylinders, so
the order is UNBOUNDED on the one fixed cover — precisely `hliftF`.

`monoF_of_pointwise_deck` performs the assembly: from the deck `g` of one cylinder loop, given POINTWISE
as `f₁(g z) = ζ₀·f₁ z` (scale `bc₁`), `f₂(g z) = f₂ z` (fix `bc₂`), plus base-fixing, it produces the
`monoF` automorphism.  The pointwise→germ step is `CoverDeckScaling.compTendsto_germ_scaling`/`_fixed`;
the close is `monoF_witness`.  The sole remaining analytic input is the deck `g` itself — the closed
Cantor-cylinder loop and its `bc₁`-monodromy realized as an analytic self-map of the cover.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.Q62Assembly
import GaloisForLFunctions.Bottcher.CoverDeckScaling
import GaloisForLFunctions.Bottcher.AlgIndep
import GaloisForLFunctions.Bottcher.CoverConstruction
import GaloisForLFunctions.Bottcher.DeckBiholo

open Filter Topology Set

namespace Bottcher

/-- **Pointwise cylinder-monodromy deck ⟹ `monoF` σ-data (genuine `bc₁`-scaling route).**  Given the
analytic deck `g` of a depth-`n` cylinder loop on a FIXED cover `U` — scaling the genuine `a₁ = φ_{c₁}`
germ by `ζ₀` POINTWISE (`f₁(g z) = ζ₀·f₁ z`), fixing the genuine `a₂ = φ_{c₂}` (`f₂(g z) = f₂ z`), and
fixing the base `K` — produce the `monoF`/`hliftF` automorphism `σ` with `σ a₁ = ζ·a₁`, `σ a₂ = a₂`,
`orderOf ζ > d`.  Here `a₁ = bc₁` is FIXED and the deck order grows with the cylinder depth `n` (the
Cantor structure gives arbitrarily deep cylinders), so over a single cover `U` this supplies `hliftF`'s
`∀d`-unbounded monodromy — what the value-annulus root-deck (bounded order `≤ 2ⁿ` per carrier) could
not.  The lone remaining analytic input is the deck `g` of the closed Cantor-cylinder loop. -/
theorem monoF_of_pointwise_deck {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (a₁ a₂ : analyticSubring U) {f₁ f₂ : ℂ → ℂ}
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑f₁) (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑f₂)
    (d : ℕ) (ζ₀ : ℂ) {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hord : d < orderOf ζ₀)
    (hscale_pt : ∀ z ∈ U, f₁ (g z) = ζ₀ * f₁ z)
    (hfix_pt : ∀ z ∈ U, f₂ (g z) = f₂ z)
    (hK : ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    ∃ (σ : meroField U ≃ₐ[K] meroField U) (ζ : meroField U) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₂)
        = algebraMap (analyticSubring U) (meroField U) a₂ ∧
      σ ζ = ζ ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₁)
        = ζ * algebraMap (analyticSubring U) (meroField U) a₁ := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  have hscale : (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
      = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) := by
    rw [ha₁]; exact compTendsto_germ_scaling ζ₀ hmaps hscale_pt
  have hinv : (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
      = (a₂ : Germ (𝓟 U) ℂ) := by
    rw [ha₂]; exact compTendsto_germ_fixed hmaps hfix_pt
  exact monoF_witness hUo hUc hUne a₁ a₂ d ζ₀ hg hg' hmaps hmaps' hgg' hg'g hord hscale hinv hK

/-- **End-to-end disconnected spine: cylinder-deck tower ⟹ hDisc (NoRelation).**  From the genuine
analytic deck tower on a FIXED cover `U` — per depth `d`, the cylinder-loop deck `g` scaling `a₁ = φ_{c₁}`
by `ζ₀` (order `> d`), fixing `a₂ = φ_{c₂}` and `ℂ(z)` — plus `φ_{c₂}` transcendental and `φ_{c₁} ≠ 0`,
the unbounded-monodromy obstruction gives `NoRelation ℂ(z)(φ_{c₁}, φ_{c₂})` = the disconnected `hDisc`.
The per-depth `σ`-data is `monoF_of_pointwise_deck`; the close is `algIndep_of_unbounded_monodromy`.
Crucially the multiplier `ζ₀` of order `2ⁿ > d` is **Brolin-free**: `Winding.pathInt_iterate_comp` shows
the `n`-fold loop pullback (a `γ` with `f^[n]∘γ` = base loop) has period `2πi/2ⁿ` with NO equilibrium
measure — so the long-feared GAP A (Brolin cylinder mass) is NOT on the critical path.  The lone
remaining input is the geometric deck tower `deck` itself: the closed cylinder loop's monodromy realized
as an analytic self-map `g` of the cover (the multivalued-`φ_{c₁}` continuation, `CoverConstruction`). -/
theorem hDisc_of_cylinder_tower {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    [Algebra (RatFunc ℂ) (meroField U)]
    (a₁ a₂ : analyticSubring U) {f₁ f₂ : ℂ → ℂ}
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑f₁) (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑f₂)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (deck : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧ (∀ z ∈ U, f₁ (g z) = ζ₀ * f₁ z) ∧ (∀ z ∈ U, f₂ (g z) = f₂ z) ∧
        ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap (RatFunc ℂ) (meroField U) k) = algebraMap (RatFunc ℂ) (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  intro P hrel
  refine algIndep_of_unbounded_monodromy _ _ hGtr hF (fun d => ?_) P hrel
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hscale, hfix, hK⟩ := deck d
  exact monoF_of_pointwise_deck hUo hUc hUne a₁ a₂ ha₁ ha₂ d ζ₀ hg hg' hmaps hmaps' hgg' hg'g
    hord hscale hfix hK

/-- **Universal-cover-strip deck: the genuine `z`-fixing realization is consistent.**  The `z`-fixing
deck cannot live in `z`-space or a value annulus (there `z` is injectively recovered from the coordinate,
forcing the deck trivial — the proven value-annulus dead-end).  The genuine realization: the cover `U` is
the universal cover (a strip) of a depth-`n` cylinder annulus, the deck `T` is the `π₁`-generator
translation (once around the cylinder), the base projection `π` is PERIODIC (`π∘T = π`, deck-INVARIANT),
`F₁ = bc₁`-lift is QUASI-periodic (`F₁∘T = ζ₀·F₁`, the monodromy phase `ζ₀ = exp(2πi/2ⁿ)` from
`Winding.pathInt_iterate_comp`, Brolin-free), and `F₂ = bc₂` factors through the base (`F₂ = b∘π`).  This
lemma confirms the realization is internally consistent: the deck `T` then SCALES `F₁` and FIXES `F₂`
pointwise — exactly the pointwise data `monoF_of_pointwise_deck` consumes — with the `φ_{c₂}`-fixing
AUTOMATIC (it factors through the deck-invariant periodic base).  The remaining analytic core is
CONSTRUCTING `(U, T, π, F₁)`: the universal-cover strip of a genuine depth-`n` cylinder annulus
(`FigureEightCapstone` two-lobe split at the Green critical level) with its quasi-periodic `bc₁`-lift. -/
theorem universal_cover_strip_deck_consistent {U : Set ℂ} {T π F₁ F₂ b : ℂ → ℂ} {ζ₀ : ℂ}
    (hTmaps : Set.MapsTo T U U)
    (hπper : ∀ z ∈ U, π (T z) = π z)
    (hF1quasi : ∀ z ∈ U, F₁ (T z) = ζ₀ * F₁ z)
    (hF2base : ∀ z ∈ U, F₂ z = b (π z)) :
    (∀ z ∈ U, F₁ (T z) = ζ₀ * F₁ z) ∧ (∀ z ∈ U, F₂ (T z) = F₂ z) := by
  refine ⟨hF1quasi, fun z hz => ?_⟩
  rw [hF2base (T z) (hTmaps hz), hF2base z hz, hπper z hz]

/-- **Quasi-periodicity of the strip lift from a constant period (the FTC core).**  On the
universal-cover strip, the lift `F` of `bc₁` is quasi-periodic under the translation deck `w ↦ w+1`: if
along the period segment `[0,1]` the lift `F` (restricted to the segment) is nonzero and differentiable,
and a running antiderivative `I` of its logarithmic derivative `F'/F` has total increment `c` over the
period, then `F 1 = exp(c)·F 0` — i.e. the monodromy multiplier is `ζ₀ = exp(c)`.  With `c = ∮ d log bc₁ =
2πi/2ⁿ` (the depth-`n` cylinder period, from the functional-equation halving `pathInt_comp_quadratic`),
this is `F∘T = ζ₀·F` with `ζ₀ = exp(2πi/2ⁿ)` of order `2ⁿ` — exactly the pointwise scaling
`monoF_of_pointwise_deck` consumes.  The FTC heart of the strip quasi-periodic lift
(`exp_logDeriv_antiderivative` at the period basepoint), turning the cylinder PERIOD into the deck's
pointwise SCALING.  Remaining for the deck: build the strip cover + the lift `F` + the period value. -/
theorem quasiperiodic_lift_of_period {F I : ℝ → ℂ} {c φ0 : ℂ}
    (hF : ∀ t ∈ Set.Icc (0:ℝ) 1, F t ≠ 0)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt F (deriv F t) t)
    (hI : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt I (deriv F t / F t) t)
    (hperiod : I 1 - I 0 = c) (hφ0 : F 0 = φ0) :
    F 1 = Complex.exp c * φ0 := by
  have h := exp_logDeriv_antiderivative (φ := F) (I := I) (by norm_num : (0:ℝ) ≤ 1) hF hdF hI
  rw [hperiod] at h
  have hF0 : F 0 ≠ 0 := hF 0 (by norm_num)
  rw [← hφ0, h]
  exact (div_mul_cancel₀ (F 1) hF0).symm

/-- **Projection-periodic cylinder deck tower ⟹ hDisc.**  This is the z-fixing deck interface in the
form the remaining disconnected geometry should construct.  On one fixed cover `U`, suppose the deck
map at every depth is a self-biholomorphism `g` whose base projection is periodic
(`π∘g = π`) and whose first lifted coordinate is quasi-periodic (`f₁∘g = ζ₀ f₁`).  If the second
coordinate factors through that projection (`f₂ = b∘π`), then the deck automatically fixes `f₂`; the
only nontrivial pointwise input left is the `φ_{c₁}` scaling.  Therefore the resulting tower is exactly
the `deck` hypothesis of `hDisc_of_cylinder_tower`, and the unbounded-monodromy obstruction proves
`NoRelation ℂ(z)(a₁,a₂)`.

This packages the intended disconnected monodromy loop: the loop is represented on the universal-cover
strip by the deck `g`; z-fixing is the projection-periodicity `π∘g = π`; `φ_{c₂}`-fixing is not a
separate analytic burden once `φ_{c₂}` is pulled back from the base. -/
theorem hDisc_of_periodic_projection_tower {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    [Algebra (RatFunc ℂ) (meroField U)]
    (a₁ a₂ : analyticSubring U) {f₁ f₂ π b : ℂ → ℂ}
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑f₁) (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑f₂)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (hF2base : ∀ z ∈ U, f₂ z = b (π z))
    (deck : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧ (∀ z ∈ U, π (g z) = π z) ∧
        (∀ z ∈ U, f₁ (g z) = ζ₀ * f₁ z) ∧
        ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap (RatFunc ℂ) (meroField U) k) = algebraMap (RatFunc ℂ) (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  refine hDisc_of_cylinder_tower hUo hUc hUne a₁ a₂ ha₁ ha₂ hF hGtr ?_
  intro d
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hπper, hF1, hK⟩ := deck d
  have hfix := (universal_cover_strip_deck_consistent (U := U) (T := g) (π := π)
    (F₁ := f₁) (F₂ := f₂) (b := b) (ζ₀ := ζ₀) hmaps hπper hF1 hF2base).2
  exact ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hF1, hfix, hK⟩

/-- **Projection-base periodic deck tower ⟹ hDisc, with base-field fixing automatic.**  This is the
sharper fixed-cover interface for the disconnected monodromy loop.  The deck constructor now supplies
only the actual geometry: a self-biholomorphic deck `g`, projection periodicity `π∘g = π`, and the
quasi-periodic first lift `f₁∘g = ζ₀ f₁` with unbounded order.  The `RatFunc ℂ`-linearity is no longer a
separate hypothesis: once the cover base is embedded as `ℂ(p₀)` through the deck-invariant projection
`p₀ = π`, `monoF_witness_projection_base` proves the deck fixes that whole base field.  The second
coordinate is fixed because it factors through the same projection. -/
theorem hDisc_of_periodic_projection_base_tower {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U} {π : ℂ → ℂ}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (a₁ a₂ : analyticSubring U) {f₁ f₂ b : ℂ → ℂ}
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑f₁) (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑f₂)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr :
      letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroField U) :=
        (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
      Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (hF2base : ∀ z ∈ U, f₂ z = b (π z))
    (deck : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧ (∀ z ∈ U, π (g z) = π z) ∧
        (∀ z ∈ U, f₁ (g z) = ζ₀ * f₁ z)) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  intro P hrel
  refine algIndep_of_unbounded_monodromy _ _ hGtr hF (fun d => ?_) P hrel
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hπper, hF1⟩ := deck d
  have hpfix : precompAnalytic hg hmaps p₀ = p₀ := by
    apply Subtype.ext
    rw [precompAnalytic_coe, hp0, Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr (fun z hz => hπper z hz)
  have hscale : (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
      = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) := by
    rw [ha₁]
    exact compTendsto_germ_scaling ζ₀ hmaps hF1
  have hfix_pt := (universal_cover_strip_deck_consistent (U := U) (T := g) (π := π)
    (F₁ := f₁) (F₂ := f₂) (b := b) (ζ₀ := ζ₀) hmaps hπper hF1 hF2base).2
  have hinv : (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
      = (a₂ : Germ (𝓟 U) ℂ) := by
    rw [ha₂]
    exact compTendsto_germ_fixed hmaps hfix_pt
  exact monoF_witness_projection_base hUo hUc hUne hp0 hπinf a₁ a₂ d ζ₀ hg hg' hmaps hmaps'
    hgg' hg'g hpfix hord hscale hinv

/-- **Uniformized projection-base tower ⟹ hDisc.**  This packages the final deck construction step
available once the genuine cover annulus has been uniformized by a single-valued lift
`φ : U ≃ V`.  For each large order, the actual deck is not assumed abstractly: it is the conjugated
rotation `g = ψ ∘ (×ζ₀) ∘ φ`.  If the projection factors as `π = q∘φ` and `q` is invariant under the
chosen rotations on `V`, then `π∘g = π`, so the whole `RatFunc ℂ` base is fixed automatically by the
projection-base machinery.  Thus the remaining analytic work is exactly the uniformized annulus plus
its rotation-stable projection factor. -/
theorem hDisc_of_uniformized_projection_base_tower {U V : Set ℂ} {φ ψ π q b : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H : LiftUniformization U V φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (a₁ a₂ : analyticSubring U) {f₂ : ℂ → ℂ}
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑φ) (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑f₂)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr :
      letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroField U) :=
        (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
      Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (hF2base : ∀ z ∈ U, f₂ z = b (π z))
    (rotTower : ∀ d : ℕ, ∃ ζ₀ : ℂ,
        ζ₀ ≠ 0 ∧ d < orderOf ζ₀ ∧
        Set.MapsTo (rotation ζ₀) V V ∧ Set.MapsTo (rotation ζ₀⁻¹) V V ∧
        (∀ y ∈ V, q (rotation ζ₀ y) = q y)) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  refine hDisc_of_periodic_projection_base_tower hUo hUc hUne hp0 hπinf a₁ a₂ ha₁ ha₂ hF hGtr
    hF2base ?_
  intro d
  obtain ⟨ζ₀, hζ0, hord, hrot, hrot', hqfix⟩ := rotTower d
  refine ⟨ζ₀, deckRot ψ φ ζ₀, deckRot ψ φ ζ₀⁻¹,
    analyticOnNhd_deckRot H hrot, analyticOnNhd_deckRot H hrot',
    mapsTo_deckRot H hrot, mapsTo_deckRot H hrot',
    eqOn_deckRot_comp hζ0 H hrot', eqOn_deckRot_comp' hζ0 H hrot,
    hord, ?_, ?_⟩
  · intro z hz
    have hgz : deckRot ψ φ ζ₀ z ∈ U := mapsTo_deckRot H hrot hz
    calc
      π (deckRot ψ φ ζ₀ z) = q (φ (deckRot ψ φ ζ₀ z)) := hπfactor _ hgz
      _ = q (rotation ζ₀ (φ z)) := by
        rw [deckRot_lift_scale H hrot z hz]
        rfl
      _ = q (φ z) := hqfix (φ z) (H.hφmaps hz)
      _ = π z := (hπfactor z hz).symm
  · exact deckRot_lift_scale H hrot

end Bottcher
