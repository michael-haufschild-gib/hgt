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
