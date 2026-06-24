/-
# Field-6: the geometric monodromy on the cover germ ring (discharging `hDisc`)

The disconnected-case monodromy automorphism `σ_n` cannot live on the field of single-valued
functions on a ball near `∞` — there `φ_{c₁}` is single-valued, so scaling it is not an automorphism.
The automorphism is the **deck transformation of the cover**: over the cover variety `commonPullback`
(where `v₁` is a branch of `φ_{c₁}` and `v₂ = φ_{c₂}`), `deckMap₁ ζ : (z,v₁,v₂) ↦ (z, ζ·v₁, v₂)`
permutes the `v₁`-branches and is a genuine self-map of the cover (`deckMap₁_mapsTo`, for
`ζ^(2ⁿ)=1`). Precomposition descends it to the **cover germ ring** `Germ (𝓟 commonPullback) ℂ`, where
it scales the coordinate germ `v₁` by `ζ`, fixes `z` (= base field `ℂ(z)`) and `v₂` (= `φ_{c₂}`) — the
exact `σ_n` data that `q62_disconnected_both` consumes, now realised on a carrier that constrains
`v₁, v₂` to the actual Böttcher branches (not the independent coordinates of `ℂ³`).

This file builds the descent and its coordinate action. The remaining Field-6 steps: upgrade
`deckGerm` to a ring/algebra automorphism, the unbounded-order tower (`exists_dyadic_primitive`), and
the fraction field of the (connected) cover with `φ_{c₂}` transcendental.
-/
import GaloisForLFunctions.Bottcher.BasinBranching
import Mathlib.Order.Filter.Germ.Basic

open Filter Topology Set

namespace Bottcher

variable {c₁ c₂ : ℂ} {n m : ℕ}

/-- The germ ring on the cover variety `commonPullback`: functions on `ℂ³` modulo agreement on the
cover. The faithful carrier where the deck automorphism `σ_n` lives (`v₁` is multivalued over `z`). -/
abbrev coverGerm (c₁ c₂ : ℂ) (n m : ℕ) : Type := Germ (𝓟 (commonPullback c₁ c₂ n m)) ℂ

/-- `deckMap₁ ζ` is a self-map of the cover (as a filter tendsto on `𝓟 commonPullback`) when
`ζ^(2ⁿ)=1`. -/
theorem deckMap₁_tendsto {ζ : ℂ} (hpow : ζ ^ (2 ^ n) = 1) :
    Tendsto (deckMap₁ ζ) (𝓟 (commonPullback c₁ c₂ n m)) (𝓟 (commonPullback c₁ c₂ n m)) :=
  tendsto_principal_principal.mpr (fun x hx => deckMap₁_mapsTo hpow hx)

/-- The descended deck map on cover germs: precomposition with `deckMap₁ ζ`. The geometric `σ_n`
on the faithful carrier. -/
noncomputable def deckGerm {ζ : ℂ} (hpow : ζ ^ (2 ^ n) = 1) :
    coverGerm c₁ c₂ n m → coverGerm c₁ c₂ n m :=
  fun g => g.compTendsto (deckMap₁ ζ) (deckMap₁_tendsto hpow)

/-- The base coordinate germ `z` (generates `K = ℂ(z)` inside the cover germ ring). -/
noncomputable def zGerm : coverGerm c₁ c₂ n m := (fun p => p.1 : ℂ × ℂ × ℂ → ℂ)
/-- The first root coordinate germ `v₁ = φ_{c₁}` (the multivalued branch). -/
noncomputable def v1Germ : coverGerm c₁ c₂ n m := (fun p => p.2.1 : ℂ × ℂ × ℂ → ℂ)
/-- The second root coordinate germ `v₂ = φ_{c₂}`. -/
noncomputable def v2Germ : coverGerm c₁ c₂ n m := (fun p => p.2.2 : ℂ × ℂ × ℂ → ℂ)

/-- **`σ_n` scales `v₁ = φ_{c₁}` by `ζ`** on the cover germ ring. -/
theorem deckGerm_v1 {ζ : ℂ} (hpow : ζ ^ (2 ^ n) = 1) :
    deckGerm hpow (v1Germ : coverGerm c₁ c₂ n m) = (ζ : coverGerm c₁ c₂ n m) * v1Germ := rfl

/-- **`σ_n` fixes `z`** (so it is a `K = ℂ(z)`-automorphism). -/
theorem deckGerm_z {ζ : ℂ} (hpow : ζ ^ (2 ^ n) = 1) :
    deckGerm hpow (zGerm : coverGerm c₁ c₂ n m) = zGerm := rfl

/-- **`σ_n` fixes `v₂ = φ_{c₂}`** (the fixed coordinate of the monodromy obstruction). -/
theorem deckGerm_v2 {ζ : ℂ} (hpow : ζ ^ (2 ^ n) = 1) :
    deckGerm hpow (v2Germ : coverGerm c₁ c₂ n m) = v2Germ := rfl

/-! ## 6b: `σ_n` as a ring automorphism of the cover germ ring -/

/-- `(ζ⁻¹)^(2ⁿ) = 1` follows from `ζ^(2ⁿ) = 1`. -/
theorem inv_pow_eq_one {ζ : ℂ} (hpow : ζ ^ (2 ^ n) = 1) : (ζ⁻¹) ^ (2 ^ n) = 1 := by
  rw [inv_pow, hpow, inv_one]

/-- **`σ_n` as a ring automorphism** of the cover germ ring, with inverse the descent of
`deckMap₁ ζ⁻¹`. The geometric monodromy upgraded to the algebraic form `q62_disconnected_both`
needs (modulo passing to the fraction field and `K`-linearity, which `deckGerm_z` supplies). -/
noncomputable def deckGermEquiv {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ n) = 1) :
    coverGerm c₁ c₂ n m ≃+* coverGerm c₁ c₂ n m where
  toFun := deckGerm hpow
  invFun := deckGerm (inv_pow_eq_one hpow)
  left_inv g := by
    induction g using Germ.inductionOn with
    | _ F =>
      have hp : ∀ p, deckMap₁ ζ (deckMap₁ ζ⁻¹ p) = p := by
        intro p
        rw [← Function.comp_apply (f := deckMap₁ ζ), deckMap₁_comp, mul_inv_cancel₀ hζ]
        simp [deckMap₁]
      have hfun : (F ∘ deckMap₁ ζ) ∘ deckMap₁ ζ⁻¹ = F := by
        funext p; simp only [Function.comp_apply, hp]
      simp only [deckGerm, Germ.coe_compTendsto, hfun]
  right_inv g := by
    induction g using Germ.inductionOn with
    | _ F =>
      have hp : ∀ p, deckMap₁ ζ⁻¹ (deckMap₁ ζ p) = p := by
        intro p
        rw [← Function.comp_apply (f := deckMap₁ ζ⁻¹), deckMap₁_comp, inv_mul_cancel₀ hζ]
        simp [deckMap₁]
      have hfun : (F ∘ deckMap₁ ζ⁻¹) ∘ deckMap₁ ζ = F := by
        funext p; simp only [Function.comp_apply, hp]
      simp only [deckGerm, Germ.coe_compTendsto, hfun]
  map_mul' g₁ g₂ := by
    induction g₁ using Germ.inductionOn with
    | _ F₁ => induction g₂ using Germ.inductionOn with
      | _ F₂ => simp only [deckGerm, ← Germ.coe_mul, Germ.coe_compTendsto]; rfl
  map_add' g₁ g₂ := by
    induction g₁ using Germ.inductionOn with
    | _ F₁ => induction g₂ using Germ.inductionOn with
      | _ F₂ => simp only [deckGerm, ← Germ.coe_add, Germ.coe_compTendsto]; rfl

@[simp] theorem deckGermEquiv_v1 {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ n) = 1) :
    deckGermEquiv hζ hpow (v1Germ : coverGerm c₁ c₂ n m) = (ζ : coverGerm c₁ c₂ n m) * v1Germ := rfl

@[simp] theorem deckGermEquiv_z {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ n) = 1) :
    deckGermEquiv hζ hpow (zGerm : coverGerm c₁ c₂ n m) = zGerm := rfl

@[simp] theorem deckGermEquiv_v2 {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ n) = 1) :
    deckGermEquiv hζ hpow (v2Germ : coverGerm c₁ c₂ n m) = v2Germ := rfl

/-! ## 6c: `σ_n` fixes the multiplier constant -/

/-- `σ_n` fixes every constant (in particular the dyadic multiplier `ζ`): it is the descent of a
precomposition, and constants pull back to themselves. Together with `deckGermEquiv_v1`
(`σ_n v₁ = ζ·v₁`) and `deckGermEquiv_v2` (`σ_n v₂ = v₂`), this is the full coordinate action the
monodromy obstruction `eq_zero_of_monodromy` consumes: `σ ζ = ζ`, `σ F = ζ·F`, `σ G = G`. -/
theorem deckGermEquiv_const {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ n) = 1) (a : ℂ) :
    deckGermEquiv hζ hpow ((a : coverGerm c₁ c₂ n m)) = (a : coverGerm c₁ c₂ n m) := by
  show deckGerm hpow (a : coverGerm c₁ c₂ n m) = a
  simp only [deckGerm, Germ.const_compTendsto]

/-! ## 6c′: the cover is nonempty; the multiplier `ζ` has order `2ⁿ` in the carrier -/

/-- The common cover is **nonempty**: a deep-enough real point `R` carries the actual section
`(R, φ_{c₁}(R), φ_{c₂}(R))` (via `bottcher_mem_commonPullback`). -/
theorem commonPullback_nonempty (c₁ c₂ : ℂ) (n m : ℕ) :
    (commonPullback c₁ c₂ n m).Nonempty := by
  set R : ℝ := max 2 (max ‖c₁‖ ‖c₂‖) + 1 with hR
  have hR2 : (2 : ℝ) < R := by
    have := le_max_left 2 (max ‖c₁‖ ‖c₂‖); rw [hR]; linarith
  have hc1 : ‖c₁‖ ≤ R := by
    have h1 := le_max_left ‖c₁‖ ‖c₂‖; have h2 := le_max_right 2 (max ‖c₁‖ ‖c₂‖); rw [hR]; linarith
  have hc2 : ‖c₂‖ ≤ R := by
    have h1 := le_max_right ‖c₁‖ ‖c₂‖; have h2 := le_max_right 2 (max ‖c₁‖ ‖c₂‖); rw [hR]; linarith
  have hnorm : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  refine ⟨((R : ℂ), bottcherCoord c₁ (R : ℂ), bottcherCoord c₂ (R : ℂ)), ?_⟩
  apply bottcher_mem_commonPullback <;> rw [hnorm] <;> assumption

/-- The principal filter on the (nonempty) cover is `NeBot`, so the constant embedding
`ℂ → coverGerm` is injective and the carrier is nontrivial. -/
instance coverGerm_principal_neBot (c₁ c₂ : ℂ) (n m : ℕ) :
    (𝓟 (commonPullback c₁ c₂ n m)).NeBot :=
  principal_neBot_iff.mpr (commonPullback_nonempty c₁ c₂ n m)

/-- **The dyadic multiplier `ζ` keeps its order `2ⁿ` as a constant of the cover germ ring.** The
constant embedding `ℂ → coverGerm` is an injective monoid hom (cover nonempty ⟹ `const_inj`), so it
preserves multiplicative order — the `orderOf ζ = m` datum (`m = 2ⁿ`) the monodromy tower feeds to
`eq_zero_of_monodromy`. -/
theorem orderOf_const_coverGerm (ζ : ℂ) :
    orderOf ((ζ : coverGerm c₁ c₂ n m)) = orderOf ζ := by
  let f : ℂ →* coverGerm c₁ c₂ n m :=
    { toFun := fun a => (a : coverGerm c₁ c₂ n m)
      map_one' := rfl
      map_mul' := fun a b => rfl }
  exact orderOf_injective f (fun a b h => Germ.const_inj.mp h) ζ

end Bottcher
