/-
# hDisc capstone: q62 disconnected/disconnected from deep radical data

Ties the deep-level analytic bricks into the top reduction
`Q62RadicalReduction.q62_disconnected_of_radical_data`.  The per-depth `data` tuple it consumes has
three analytic clauses; two are discharged here from the bricks of `BottcherIterateNonSquare`:

* non-square `∀ b, b² ≠ a` — `bottcherIterateGerm_not_isSquare`;
* radical relation `φ_{c₁}^{2^k} = i a` — `radical_relation_germ`;
* `i GB = φ_{c₂}` — from `restrictMeroHom_algebraMap` and the supplied `φ_{c₂}` germ on `Ext`.

`i = restrictMeroHom` is upgraded to a `ℂ(z)`-algebra hom by `restrictMeroHom_ratfuncToMero` (as in
`noRelation_of_restrict`).  The result reduces `hDisc` (disconnected) to the two genuine geometric
inputs, now isolated: per depth, (a) a deeper connected `Ext ⊇ U` carrying the closed odd-period loop
`hloops` (the depth-`k` figure-eight lobe), and (b) a `φ_{c₂}` germ on `Ext` restricting to `φ_{c₂}` on
`U` (the `c₁ ≠ c₂` distinct-precritical compatibility).  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.BottcherIterateNonSquare
import GaloisForLFunctions.Bottcher.Q62RadicalReduction

open Complex Set Filter Polynomial

namespace Bottcher

/-- **[hDisc capstone] q62 disconnected/disconnected from deep radical data.**  Assembles the genuine
independence `NoRelation ℂ(z) (φ_{c₁}, φ_{c₂})` (base algebra `ratfuncToMero U`) from: `φ_{c₁} ≠ 0`,
`φ_{c₂}` transcendental, `U` in the deep escape regime with `a₁ = bottcherCoord c₁`, and — per depth `d`
— a deeper connected domain `Ext ⊇ U` carrying the radicand `bottcherCoord c₁∘f^[d+1]`, a `φ_{c₂}` germ
`GBExt` restricting to `a₂`, and the closed odd-period loop datum `hloops`.  The non-square clause is
`bottcherIterateGerm_not_isSquare`, the radical relation is `radical_relation_germ`, and `i =
restrictMeroHom` is the `ℂ(z)`-algebra descent.  Reduces hDisc to the geometric loop + the φ_{c₂}
domain-compatibility. -/
theorem q62_disconnected_of_deepData {c₁ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (deepdata : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁)
        (aExt GBExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt GBExt = a₂ ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI algU := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply q62_disconnected_of_radical_data hUo hUc hUne a₁ a₂ hF hGtr
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, aExt, GBExt, haExt, hGB, hloops⟩ := deepdata d
  haveI := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
  letI algExt := (ratfuncToMero Ext hExto hExtc.isPreconnected hExtc.nonempty hExtinf).toAlgebra
  let i : meroField Ext →ₐ[RatFunc ℂ] meroField U :=
    { restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne with
      commutes' := fun r => RingHom.congr_fun
        (restrictMeroHom_ratfuncToMero hUExt hExto hExtc.isPreconnected hExtc.nonempty hExtinf
          hUo hUc hUne hUinf) r }
  refine ⟨meroField Ext, inferInstance, inferInstance, i,
    algebraMap (analyticSubring Ext) (meroField Ext) aExt,
    algebraMap (analyticSubring Ext) (meroField Ext) GBExt, d + 1,
    Nat.le_add_left 1 d, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ d))
  · exact bottcherIterateGerm_not_isSquare (d+1) hExto hExtc hExtesc hloops aExt haExt.symm
  · show (algebraMap (analyticSubring U) (meroField U) a₁) ^ (2 ^ (d+1))
        = restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne
            (algebraMap (analyticSubring Ext) (meroField Ext) aExt)
    exact radical_relation_germ (d+1) hUExt hUo hUc hUne hExto hExtc.isPreconnected hExtc.nonempty
      hUesc a₁ aExt ha₁ haExt
  · show restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne
        (algebraMap (analyticSubring Ext) (meroField Ext) GBExt)
      = algebraMap (analyticSubring U) (meroField U) a₂
    rw [restrictMeroHom_algebraMap, hGB]

end Bottcher

namespace Bottcher

/-- **[hDisc capstone, φ_{c₂} discharged] q62 disc/disc from deep data with `Ext ⊆ escapeOpen c₂`.**
Refines `q62_disconnected_of_deepData`: the `φ_{c₂}` germ `GBExt` is constructed internally as
`bottcherCoord c₂` on `Ext` (analytic there since `Ext ⊆ escapeOpen c₂`), restricting to `a₂ =
bottcherCoord c₂` on `U`.  So the φ_{c₂} compatibility collapses to the containment `Ext ⊆ escapeOpen c₂`
— leaving, per depth, a single geometric input: a deep connected `Ext` (with `U ⊆ Ext`, `f^[d+1]·∈`
escape `c₁`, `Ext ⊆ escape c₂`) carrying a closed loop whose radicand period is odd (the disconnected
two-lobe loop). Every algebraic/analytic clause of `hDisc` (disconnected) is discharged. -/
theorem q62_disconnected_of_deepData_escape {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (deepdata : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁)
        (_hExtc₂ : Ext ⊆ escapeOpen c₂)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply q62_disconnected_of_deepData hUo hUc hUne hUinf hUesc a₁ a₂ ha₁ hF hGtr
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, aExt, haExt, hloops⟩ := deepdata d
  have hbc₂an : AnalyticOnNhd ℂ (bottcherCoord c₂) Ext :=
    ((differentiableOn_bottcherCoord c₂).analyticOnNhd (isOpen_escapeOpen c₂)).mono hExtc₂
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc,
    aExt, ⟨(↑(bottcherCoord c₂) : Germ (𝓟 Ext) ℂ), bottcherCoord c₂, hbc₂an, rfl⟩,
    haExt, ?_, hloops⟩
  apply Subtype.ext
  show (↑(bottcherCoord c₂) : Germ (𝓟 Ext) ℂ).compTendsto id
        (tendsto_principal_principal.mpr (fun x hx => hUExt hx))
      = (a₂ : Germ (𝓟 U) ℂ)
  rw [ha₂, Germ.coe_compTendsto]; rfl

end Bottcher

namespace Bottcher

/-- **[hDisc capstone, image-winding input] q62 disc/disc from topological deep data.**
This is the escape-form hDisc close with the loop hypothesis lowered from the analytic radicand period
to odd logarithmic winding of the image loop `(f^[d+1])∘γ`.  The chain-rule/winding bridge in
`BottcherIterateNonSquare` supplies the radicand period consumed by
`q62_disconnected_of_deepData_escape`. -/
theorem q62_disconnected_of_imageWindingDeepData_escape {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (deepdata : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁)
        (_hExtc₂ : Ext ⊆ escapeOpen c₂)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ : ℝ, HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                ((quadratic c₁)^[d+1] (γ θ))⁻¹ *
                  ((∏ j ∈ Finset.range (d+1), 2 * (quadratic c₁)^[j] (γ θ)) * γ' θ))
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_deepData_escape hUo hUc hUne hUinf hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, aExt, haExt, hloops⟩ :=
    deepdata d
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, aExt, haExt, ?_⟩
  intro T hTcount
  obtain ⟨γ, γ', m, hγExt, hγcont, hγ'cont, hdγ, hγclosed, havoid, hwind⟩ :=
    hloops T hTcount
  refine ⟨γ, γ', m, hγExt, hγcont, hγ'cont, ?_, hγclosed, havoid, ?_⟩
  · intro θ _hθ
    exact hdγ θ
  · have hesc : ∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∈ escapeOpen c₁ :=
      fun θ => hExtesc (γ θ) (hγExt θ)
    have hclosed' :
        (quadratic c₁)^[d+1] (γ (2 * Real.pi)) = (quadratic c₁)^[d+1] (γ 0) := by
      rw [hγclosed]
    have hperiod :=
      pathInt_logDeriv_bottcherIterate_eq_imageInv (c := c₁) (d+1)
        hesc hdγ hγcont hγ'cont hclosed'
    exact hperiod.trans hwind

end Bottcher

namespace Bottcher

/-- Deep-data q62 disconnected close with both coordinates supplied by their own non-square radical
data. This removes the explicit `φ_{c₂}` transcendence input from the deep-data capstone. -/
theorem q62_disconnected_of_deepData_two_radical {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc₁ : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (hUesc₂ : ∀ z ∈ U, ‖c₂‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (deepdataF : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁)
        (aExt GBExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt GBExt = a₂ ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)))
    (deepdataG : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic c₂)^[d+1] z ∈ escapeOpen c₂)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord c₂ ((quadratic c₂)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic c₂)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord c₂ ((quadratic c₂)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI algU := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply q62_disconnected_of_two_radical_data hUo hUc hUne a₁ a₂ hF hG
  · intro d
    obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, aExt, GBExt, haExt, hGB, hloops⟩ :=
      deepdataF d
    haveI := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
    letI algExt := (ratfuncToMero Ext hExto hExtc.isPreconnected hExtc.nonempty hExtinf).toAlgebra
    let i : meroField Ext →ₐ[RatFunc ℂ] meroField U :=
      { restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne with
        commutes' := fun r => RingHom.congr_fun
          (restrictMeroHom_ratfuncToMero hUExt hExto hExtc.isPreconnected hExtc.nonempty hExtinf
            hUo hUc hUne hUinf) r }
    refine ⟨meroField Ext, inferInstance, inferInstance, i,
      algebraMap (analyticSubring Ext) (meroField Ext) aExt,
      algebraMap (analyticSubring Ext) (meroField Ext) GBExt, d + 1,
      Nat.le_add_left 1 d, ?_, ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ d))
    · exact bottcherIterateGerm_not_isSquare (d+1) hExto hExtc hExtesc hloops aExt haExt.symm
    · show (algebraMap (analyticSubring U) (meroField U) a₁) ^ (2 ^ (d+1))
          = restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne
              (algebraMap (analyticSubring Ext) (meroField Ext) aExt)
      exact radical_relation_germ (d+1) hUExt hUo hUc hUne hExto hExtc.isPreconnected hExtc.nonempty
        hUesc₁ a₁ aExt ha₁ haExt
    · show restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne
          (algebraMap (analyticSubring Ext) (meroField Ext) GBExt)
        = algebraMap (analyticSubring U) (meroField U) a₂
      rw [restrictMeroHom_algebraMap, hGB]
  · intro d
    obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, aExt, haExt, hloops⟩ := deepdataG d
    haveI := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
    letI algExt := (ratfuncToMero Ext hExto hExtc.isPreconnected hExtc.nonempty hExtinf).toAlgebra
    let i : meroField Ext →ₐ[RatFunc ℂ] meroField U :=
      { restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne with
        commutes' := fun r => RingHom.congr_fun
          (restrictMeroHom_ratfuncToMero hUExt hExto hExtc.isPreconnected hExtc.nonempty hExtinf
            hUo hUc hUne hUinf) r }
    refine ⟨meroField Ext, inferInstance, inferInstance, i,
      algebraMap (analyticSubring Ext) (meroField Ext) aExt, d + 1,
      Nat.le_add_left 1 d, ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ d))
    · exact bottcherIterateGerm_not_isSquare (d+1) hExto hExtc hExtesc hloops aExt haExt.symm
    · show (algebraMap (analyticSubring U) (meroField U) a₂) ^ (2 ^ (d+1))
          = restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne
              (algebraMap (analyticSubring Ext) (meroField Ext) aExt)
      exact radical_relation_germ (d+1) hUExt hUo hUc hUne hExto hExtc.isPreconnected hExtc.nonempty
        hUesc₂ a₂ aExt ha₂ haExt

end Bottcher

namespace Bottcher

/-- Escape-form deep-data q62 disconnected close with both coordinates supplied by their own non-square
radical data. This combines `q62_disconnected_of_deepData_escape`'s internal construction of the
`φ₂` restriction with the two-radical theorem that derives `φ₂` transcendence from its own tower. -/
theorem q62_disconnected_of_deepData_escape_two_radical {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc₁ : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (hUesc₂ : ∀ z ∈ U, ‖c₂‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (deepdataF : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁)
        (_hExtc₂ : Ext ⊆ escapeOpen c₂)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)))
    (deepdataG : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic c₂)^[d+1] z ∈ escapeOpen c₂)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord c₂ ((quadratic c₂)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic c₂)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord c₂ ((quadratic c₂)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply q62_disconnected_of_deepData_two_radical hUo hUc hUne hUinf hUesc₁ hUesc₂ a₁ a₂ ha₁ ha₂ hF hG
  · intro d
    obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, aExt, haExt, hloops⟩ := deepdataF d
    have hbc₂an : AnalyticOnNhd ℂ (bottcherCoord c₂) Ext :=
      ((differentiableOn_bottcherCoord c₂).analyticOnNhd (isOpen_escapeOpen c₂)).mono hExtc₂
    refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc,
      aExt, ⟨(↑(bottcherCoord c₂) : Germ (𝓟 Ext) ℂ), bottcherCoord c₂, hbc₂an, rfl⟩,
      haExt, ?_, hloops⟩
    apply Subtype.ext
    show (↑(bottcherCoord c₂) : Germ (𝓟 Ext) ℂ).compTendsto id
          (tendsto_principal_principal.mpr (fun x hx => hUExt hx))
        = (a₂ : Germ (𝓟 U) ℂ)
    rw [ha₂, Germ.coe_compTendsto]
    rfl
  · exact deepdataG

/-- Image-winding form of the two-radical q62 disconnected close.  Each radical tower supplies only
the odd winding of the image loop `(f^[d+1])∘γ`; the analytic radicand periods required by
`q62_disconnected_of_deepData_two_radical` are recovered by the chain-rule/winding bridge. -/
theorem q62_disconnected_of_imageWindingDeepData_two_radical {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc₁ : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (hUesc₂ : ∀ z ∈ U, ‖c₂‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (deepdataF : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁)
        (aExt GBExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt GBExt = a₂ ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ : ℝ, HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                ((quadratic c₁)^[d+1] (γ θ))⁻¹ *
                  ((∏ j ∈ Finset.range (d+1), 2 * (quadratic c₁)^[j] (γ θ)) * γ' θ))
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)))
    (deepdataG : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic c₂)^[d+1] z ∈ escapeOpen c₂)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord c₂ ((quadratic c₂)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ : ℝ, HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic c₂)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                ((quadratic c₂)^[d+1] (γ θ))⁻¹ *
                  ((∏ j ∈ Finset.range (d+1), 2 * (quadratic c₂)^[j] (γ θ)) * γ' θ))
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_deepData_two_radical hUo hUc hUne hUinf hUesc₁ hUesc₂
    a₁ a₂ ha₁ ha₂ hF hG
  · intro d
    obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, aExt, GBExt, haExt, hGB,
      hloops⟩ := deepdataF d
    refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, aExt, GBExt, haExt, hGB, ?_⟩
    intro T hTcount
    obtain ⟨γ, γ', m, hγExt, hγcont, hγ'cont, hdγ, hγclosed, havoid, hwind⟩ :=
      hloops T hTcount
    refine ⟨γ, γ', m, hγExt, hγcont, hγ'cont, ?_, hγclosed, havoid, ?_⟩
    · intro θ _hθ
      exact hdγ θ
    · have hesc : ∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∈ escapeOpen c₁ :=
        fun θ => hExtesc (γ θ) (hγExt θ)
      have hclosed' :
          (quadratic c₁)^[d+1] (γ (2 * Real.pi)) = (quadratic c₁)^[d+1] (γ 0) := by
        rw [hγclosed]
      have hperiod :=
        pathInt_logDeriv_bottcherIterate_eq_imageInv (c := c₁) (d+1)
          hesc hdγ hγcont hγ'cont hclosed'
      exact hperiod.trans hwind
  · intro d
    obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, aExt, haExt, hloops⟩ :=
      deepdataG d
    refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, aExt, haExt, ?_⟩
    intro T hTcount
    obtain ⟨γ, γ', m, hγExt, hγcont, hγ'cont, hdγ, hγclosed, havoid, hwind⟩ :=
      hloops T hTcount
    refine ⟨γ, γ', m, hγExt, hγcont, hγ'cont, ?_, hγclosed, havoid, ?_⟩
    · intro θ _hθ
      exact hdγ θ
    · have hesc : ∀ θ : ℝ, (quadratic c₂)^[d+1] (γ θ) ∈ escapeOpen c₂ :=
        fun θ => hExtesc (γ θ) (hγExt θ)
      have hclosed' :
          (quadratic c₂)^[d+1] (γ (2 * Real.pi)) = (quadratic c₂)^[d+1] (γ 0) := by
        rw [hγclosed]
      have hperiod :=
        pathInt_logDeriv_bottcherIterate_eq_imageInv (c := c₂) (d+1)
          hesc hdγ hγcont hγ'cont hclosed'
      exact hperiod.trans hwind

/-- Image-winding form of the escape two-radical q62 disconnected close.  The first tower also
supplies the escape-domain compatibility for `φ₂`; both odd radicand periods are derived from image
winding before applying `q62_disconnected_of_deepData_escape_two_radical`. -/
theorem q62_disconnected_of_imageWindingDeepData_escape_two_radical {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc₁ : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (hUesc₂ : ∀ z ∈ U, ‖c₂‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (deepdataF : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁)
        (_hExtc₂ : Ext ⊆ escapeOpen c₂)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord c₁ ((quadratic c₁)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ : ℝ, HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                ((quadratic c₁)^[d+1] (γ θ))⁻¹ *
                  ((∏ j ∈ Finset.range (d+1), 2 * (quadratic c₁)^[j] (γ θ)) * γ' θ))
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)))
    (deepdataG : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic c₂)^[d+1] z ∈ escapeOpen c₂)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord c₂ ((quadratic c₂)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ : ℝ, HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic c₂)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                ((quadratic c₂)^[d+1] (γ θ))⁻¹ *
                  ((∏ j ∈ Finset.range (d+1), 2 * (quadratic c₂)^[j] (γ θ)) * γ' θ))
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_deepData_escape_two_radical hUo hUc hUne hUinf hUesc₁ hUesc₂
    a₁ a₂ ha₁ ha₂ hF hG
  · intro d
    obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, aExt, haExt, hloops⟩ :=
      deepdataF d
    refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, aExt, haExt, ?_⟩
    intro T hTcount
    obtain ⟨γ, γ', m, hγExt, hγcont, hγ'cont, hdγ, hγclosed, havoid, hwind⟩ :=
      hloops T hTcount
    refine ⟨γ, γ', m, hγExt, hγcont, hγ'cont, ?_, hγclosed, havoid, ?_⟩
    · intro θ _hθ
      exact hdγ θ
    · have hesc : ∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) ∈ escapeOpen c₁ :=
        fun θ => hExtesc (γ θ) (hγExt θ)
      have hclosed' :
          (quadratic c₁)^[d+1] (γ (2 * Real.pi)) = (quadratic c₁)^[d+1] (γ 0) := by
        rw [hγclosed]
      have hperiod :=
        pathInt_logDeriv_bottcherIterate_eq_imageInv (c := c₁) (d+1)
          hesc hdγ hγcont hγ'cont hclosed'
      exact hperiod.trans hwind
  · intro d
    obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, aExt, haExt, hloops⟩ :=
      deepdataG d
    refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, aExt, haExt, ?_⟩
    intro T hTcount
    obtain ⟨γ, γ', m, hγExt, hγcont, hγ'cont, hdγ, hγclosed, havoid, hwind⟩ :=
      hloops T hTcount
    refine ⟨γ, γ', m, hγExt, hγcont, hγ'cont, ?_, hγclosed, havoid, ?_⟩
    · intro θ _hθ
      exact hdγ θ
    · have hesc : ∀ θ : ℝ, (quadratic c₂)^[d+1] (γ θ) ∈ escapeOpen c₂ :=
        fun θ => hExtesc (γ θ) (hγExt θ)
      have hclosed' :
          (quadratic c₂)^[d+1] (γ (2 * Real.pi)) = (quadratic c₂)^[d+1] (γ 0) := by
        rw [hγclosed]
      have hperiod :=
        pathInt_logDeriv_bottcherIterate_eq_imageInv (c := c₂) (d+1)
          hesc hdγ hγcont hγ'cont hclosed'
      exact hperiod.trans hwind

end Bottcher
