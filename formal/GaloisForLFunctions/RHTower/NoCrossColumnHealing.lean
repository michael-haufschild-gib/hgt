/-
Cross-column healing is impossible for a finite column product: analytic continuation of a
factored carrier transfers to each factor off the partner's divisor, so no finite regrouping of
columns can carry the product past a boundary point that obstructs one column while the others are
regular and nonvanishing there.

Write a carrier as a product `F = Φ · Ψ` on a domain `Ω`.  If `F` and the partner `Ψ` both extend
analytically to a larger domain `Ω'`, then the column `Φ` extends analytically to `Ω'` minus the
zero set of the extended partner, realized explicitly as the quotient `F'/Ψ'`.  The quotient is
analytic at every point where the denominator is nonzero (`AnalyticAt.div`), and it agrees with `Φ`
wherever the factorization holds and the partner does not vanish.  This is the positive
healing-transfer lemma.

The contrapositive is the no-healing law.  Suppose the column `Φ` admits no analytic element at a
boundary point `b` (a pointwise natural-boundary obstruction, `NoExtensionAt`), while the partner
`Ψ` has an analytic element there that is *nonvanishing* at `b`.  Then the product `F = Φ · Ψ` can
have no analytic element at `b` either: an element `g` of the product, divided by the nonvanishing
partner element `ψ'`, would furnish the forbidden element `g/ψ'` for `Φ` on a neighbourhood of `b`
where `ψ'` stays away from zero (continuity of `ψ'`, `ψ' b ≠ 0`).  The nonvanishing hypothesis
`ψ' b ≠ 0` is exactly the "off the partner's divisor" caveat: healing is blocked at every boundary
point where the partner does not vanish, and the partner's zeros are discrete, so a continuum of
obstructed points — a natural boundary of one column — survives multiplication.

Iterating over a finite product against one distinguished factor (regrouping the remaining columns
into a single partner via `Finset.mul_prod_erase`) shows the same for any finite Finset product:
a natural boundary of a single column is inherited by every finite column product except along the
partners' discrete zero sets.  Continuation beyond all columns at once — the habitat of
interferential (no-factor-vanishing) zeros — is therefore unreachable with finitely many columns
and is an irreducibly infinite-product phenomenon.
-/
import Mathlib

namespace RHTower

noncomputable section

/-! ### §1 The healing-transfer lemma (positive form)

If the product `F` and the partner `Ψ` both continue analytically to a larger domain `Ω'`, the
column `Φ` continues to `Ω'` off the extended partner's zero set, as the quotient `F'/Ψ'`. -/

/-- **Healing transfer.**  If a factorization `Φ s = F' s / Ψ' s` holds on `Ω`, and `F'`, `Ψ'` are
analytic on the enlarged domain `Ω'`, then `Φ` extends to an analytic function `Φ'` on
`{s ∈ Ω' | Ψ' s ≠ 0}` — the enlarged domain minus the extended partner's divisor — namely the
quotient `Φ' = F'/Ψ'`, which is analytic at each point of the set because the denominator is
nonzero there (`AnalyticAt.div`) and agrees with `Φ` on `Ω` off the divisor. -/
theorem column_extends_of_product_extends {Ω Ω' : Set ℂ} {F' Ψ' Φ : ℂ → ℂ}
    (hF' : AnalyticOnNhd ℂ F' Ω') (hΨ' : AnalyticOnNhd ℂ Ψ' Ω')
    (hfac : ∀ s ∈ Ω, Φ s = F' s / Ψ' s) :
    ∃ Φ' : ℂ → ℂ, AnalyticOnNhd ℂ Φ' {s ∈ Ω' | Ψ' s ≠ 0} ∧
      ∀ s ∈ Ω, Ψ' s ≠ 0 → Φ' s = Φ s := by
  refine ⟨fun s => F' s / Ψ' s, ?_, ?_⟩
  · intro s hs
    exact (hF' s hs.1).div (hΨ' s hs.1) hs.2
  · intro s hs _
    exact (hfac s hs).symm

/-! ### §2 The pointwise obstruction and the no-healing law -/

/-- **No analytic element at a boundary point.**  `Φ` admits no analytic element at `b` agreeing
with it on the overlap: there is no open `U ∋ b` carrying an analytic `g` with `g = Φ` on `U ∩ Ω`.
This is the pointwise constituent of a natural boundary. -/
def NoExtensionAt (Φ : ℂ → ℂ) (Ω : Set ℂ) (b : ℂ) : Prop :=
  ¬ ∃ (U : Set ℂ) (g : ℂ → ℂ), IsOpen U ∧ b ∈ U ∧ AnalyticOnNhd ℂ g U ∧
      ∀ s ∈ U ∩ Ω, g s = Φ s

/-- **Boundary no-extension transports to every interior germ.**  On a preconnected analytic
continuation domain, `NoExtensionAt Φ Ω b` rules out an entire function agreeing with `Φ` near
any base point of `Ω`.  Analytic uniqueness propagates the local agreement throughout `Ω`, and the
entire function would then itself be the forbidden analytic element at `b`. -/
theorem no_entire_germ_extension_of_noExtensionAt
    {Φ : ℂ → ℂ} {Ω : Set ℂ} {a b : ℂ}
    (hΦ : AnalyticOnNhd ℂ Φ Ω) (hΩ : IsPreconnected Ω)
    (ha : a ∈ Ω) (hno : NoExtensionAt Φ Ω b) :
    ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Set.univ ∧
      Filter.EventuallyEq (nhds a) Φ g := by
  rintro ⟨g, hg, heq⟩
  have hgΩ : AnalyticOnNhd ℂ g Ω :=
    fun z _ => hg z (Set.mem_univ z)
  have hEqOn : Set.EqOn Φ g Ω :=
    hΦ.eqOn_of_preconnected_of_eventuallyEq hgΩ hΩ ha heq
  exact hno ⟨Set.univ, g, isOpen_univ, Set.mem_univ b, hg, fun z hz =>
    (hEqOn hz.2).symm⟩

/-- **No cross-column healing.**  If the column `Φ` has no analytic element at `b`, while the
partner `Ψ` has an analytic element `ψ'` at `b` that is *nonvanishing* there (`ψ' b ≠ 0`), then the
product `F = Φ · Ψ` has no analytic element at `b`.  Indeed, an analytic element `g` of the product
would yield `g/ψ'` as an analytic element for `Φ` on a neighbourhood of `b` where `ψ'` stays
nonzero (continuity of `ψ'` at `b` and `ψ' b ≠ 0` give `ψ' ≠ 0` eventually), and there
`g/ψ' = (Φ·Ψ)/Ψ = Φ`, contradicting the obstruction.  The hypothesis `ψ' b ≠ 0` is the "off the
partner's divisor" caveat: healing is blocked precisely where the partner does not vanish. -/
theorem no_healing {Ω : Set ℂ} {Φ Ψ F : ℂ → ℂ} {b : ℂ}
    (hfac : ∀ s ∈ Ω, F s = Φ s * Ψ s)
    (hΦnb : NoExtensionAt Φ Ω b)
    (hΨ : ∃ (U : Set ℂ) (ψ' : ℂ → ℂ), IsOpen U ∧ b ∈ U ∧ AnalyticOnNhd ℂ ψ' U ∧
        ψ' b ≠ 0 ∧ ∀ s ∈ U ∩ Ω, ψ' s = Ψ s) :
    ¬ ∃ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V ∧ b ∈ V ∧ AnalyticOnNhd ℂ g V ∧
        ∀ s ∈ V ∩ Ω, g s = F s := by
  rintro ⟨V, g, hVopen, hbV, hgan, hgeq⟩
  obtain ⟨U, ψ', hUopen, hbU, hψan, hψb, hψeq⟩ := hΨ
  -- The partner element stays nonzero on some open `W ∋ b`.
  have hne : ∀ᶠ z in nhds b, ψ' z ≠ 0 :=
    (hψan b hbU).continuousAt.eventually_ne hψb
  obtain ⟨W, hWne, hWopen, hbW⟩ := eventually_nhds_iff.1 hne
  -- `g/ψ'` is a forbidden analytic element for `Φ` on `U ∩ V ∩ W`.
  refine hΦnb ⟨U ∩ V ∩ W, fun s => g s / ψ' s, (hUopen.inter hVopen).inter hWopen,
    ⟨⟨hbU, hbV⟩, hbW⟩, ?_, ?_⟩
  · intro s hs
    exact (hgan s hs.1.2).div (hψan s hs.1.1) (hWne s hs.2)
  · intro s hs
    obtain ⟨⟨⟨hsU, hsV⟩, hsW⟩, hsΩ⟩ := hs
    have hψs0 : ψ' s ≠ 0 := hWne s hsW
    have hg : g s = F s := hgeq s ⟨hsV, hsΩ⟩
    have hψ : ψ' s = Ψ s := hψeq s ⟨hsU, hsΩ⟩
    have hΨs0 : Ψ s ≠ 0 := hψ ▸ hψs0
    show g s / ψ' s = Φ s
    rw [hg, hψ, hfac s hsΩ]
    exact mul_div_cancel_right₀ (Φ s) hΨs0

/-! ### §3 The finite-product corollary

Regroup a finite Finset product `∏ i ∈ t, Φ i` as one distinguished column `Φ i₀` against the
product of the others, and apply the no-healing law: a natural boundary of `Φ i₀` is inherited by
the whole product except along the partners' discrete zero set. -/

/-- **No healing across a finite column product.**  If a distinguished column `Φ i₀` (`i₀ ∈ t`) has
no analytic element at `b`, while the product of the remaining columns `∏ i ∈ t.erase i₀, Φ i` has
an analytic element nonvanishing at `b`, then the full product `F = ∏ i ∈ t, Φ i` has no analytic
element at `b`.  Regroup `F` as `Φ i₀ · (∏ i ∈ t.erase i₀, Φ i)` by `Finset.mul_prod_erase` and
apply `no_healing`; the general case follows by relabelling the distinguished factor. -/
theorem no_healing_finset {ι : Type*} [DecidableEq ι] {t : Finset ι} {Ω : Set ℂ}
    {Φ : ι → ℂ → ℂ} {F : ℂ → ℂ} {b : ℂ}
    {i₀ : ι} (hi₀ : i₀ ∈ t)
    (hfac : ∀ s ∈ Ω, F s = ∏ i ∈ t, Φ i s)
    (hnb : NoExtensionAt (Φ i₀) Ω b)
    (hrest : ∃ (U : Set ℂ) (ψ' : ℂ → ℂ), IsOpen U ∧ b ∈ U ∧ AnalyticOnNhd ℂ ψ' U ∧
        ψ' b ≠ 0 ∧ ∀ s ∈ U ∩ Ω, ψ' s = ∏ i ∈ t.erase i₀, Φ i s) :
    ¬ ∃ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V ∧ b ∈ V ∧ AnalyticOnNhd ℂ g V ∧
        ∀ s ∈ V ∩ Ω, g s = F s := by
  refine no_healing (Φ := Φ i₀) (Ψ := fun s => ∏ i ∈ t.erase i₀, Φ i s) ?_ hnb hrest
  intro s hs
  rw [hfac s hs, ← Finset.mul_prod_erase t (fun i => Φ i s) hi₀]

end

end RHTower
