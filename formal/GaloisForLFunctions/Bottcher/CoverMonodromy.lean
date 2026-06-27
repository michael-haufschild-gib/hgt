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
  tendsto_principal_principal.mpr (fun _ hx => deckMap₁_mapsTo hpow hx)

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
  grind [inv_pow]

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

/-! ## 6e-prep: the symmetric `c₂`-monodromy (scales `v₂`, fixes `v₁`)

By the symmetry `c₁ ↔ c₂`, the cover also carries the `c₂`-deck transformation, scaling `v₂ = φ_{c₂}`
by a `2ᵐ`-th root of unity while fixing `z` and `v₁ = φ_{c₁}`. This is the `monoG` datum
`q62_disconnected_both` needs (and, via `transcendental_of_monodromy`, makes `φ_{c₂}`'s transcendence
a consequence rather than a separate hypothesis — Field-6e). -/

/-- The `c₂`-deck transformation: scales `v₂` by `ζ`, FIXES `z` and `v₁`. -/
def deckMap₂ (ζ : ℂ) : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ := fun p => (p.1, p.2.1, ζ * p.2.2)

theorem deckMap₂_mapsTo {ζ : ℂ} (hζ : ζ ^ (2 ^ m) = 1) :
    Set.MapsTo (deckMap₂ ζ) (commonPullback c₁ c₂ n m) (commonPullback c₁ c₂ n m) := by
  rintro ⟨z, v₁, v₂⟩ ⟨h1, h10, h2, h20⟩
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow (by positivity)] at hζ; exact one_ne_zero hζ.symm
  grind [commonPullback, deckMap₂, mul_pow]

theorem deckMap₂_comp (ζ η : ℂ) : deckMap₂ ζ ∘ deckMap₂ η = deckMap₂ (ζ * η) := by
  funext p
  grind [deckMap₂]

theorem deckMap₂_tendsto {ζ : ℂ} (hζ : ζ ^ (2 ^ m) = 1) :
    Tendsto (deckMap₂ ζ) (𝓟 (commonPullback c₁ c₂ n m)) (𝓟 (commonPullback c₁ c₂ n m)) :=
  tendsto_principal_principal.mpr (fun _ hx => deckMap₂_mapsTo hζ hx)

/-- The descended `c₂`-deck on cover germs (`σ'_m`). -/
noncomputable def deckGerm₂ {ζ : ℂ} (hζ : ζ ^ (2 ^ m) = 1) :
    coverGerm c₁ c₂ n m → coverGerm c₁ c₂ n m :=
  fun g => g.compTendsto (deckMap₂ ζ) (deckMap₂_tendsto hζ)

/-- `σ'_m` scales `v₂ = φ_{c₂}` by `ζ`. -/
theorem deckGerm₂_v2 {ζ : ℂ} (hζ : ζ ^ (2 ^ m) = 1) :
    deckGerm₂ hζ (v2Germ : coverGerm c₁ c₂ n m) = (ζ : coverGerm c₁ c₂ n m) * v2Germ := rfl
/-- `σ'_m` fixes `v₁ = φ_{c₁}`. -/
theorem deckGerm₂_v1 {ζ : ℂ} (hζ : ζ ^ (2 ^ m) = 1) :
    deckGerm₂ hζ (v1Germ : coverGerm c₁ c₂ n m) = v1Germ := rfl
/-- `σ'_m` fixes `z` (= K). -/
theorem deckGerm₂_z {ζ : ℂ} (hζ : ζ ^ (2 ^ m) = 1) :
    deckGerm₂ hζ (zGerm : coverGerm c₁ c₂ n m) = zGerm := rfl

/-- **`σ'_m` as a ring automorphism** of the cover germ ring, inverse to the deck with multiplier
`ζ⁻¹`.  This is the symmetric field-6 germ carrier for the `c₂`-monodromy: it fixes `z` and `v₁`,
and scales `v₂`. -/
noncomputable def deckGermEquiv₂ {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ m) = 1) :
    coverGerm c₁ c₂ n m ≃+* coverGerm c₁ c₂ n m where
  toFun := deckGerm₂ hpow
  invFun := deckGerm₂ (inv_pow_eq_one (n := m) hpow)
  left_inv g := by
    induction g using Germ.inductionOn with
    | _ F =>
      have hp : ∀ p, deckMap₂ ζ (deckMap₂ ζ⁻¹ p) = p := by
        intro p
        rw [← Function.comp_apply (f := deckMap₂ ζ), deckMap₂_comp, mul_inv_cancel₀ hζ]
        simp [deckMap₂]
      have hfun : (F ∘ deckMap₂ ζ) ∘ deckMap₂ ζ⁻¹ = F := by
        funext p; simp only [Function.comp_apply, hp]
      simp only [deckGerm₂, Germ.coe_compTendsto, hfun]
  right_inv g := by
    induction g using Germ.inductionOn with
    | _ F =>
      have hp : ∀ p, deckMap₂ ζ⁻¹ (deckMap₂ ζ p) = p := by
        intro p
        rw [← Function.comp_apply (f := deckMap₂ ζ⁻¹), deckMap₂_comp, inv_mul_cancel₀ hζ]
        simp [deckMap₂]
      have hfun : (F ∘ deckMap₂ ζ⁻¹) ∘ deckMap₂ ζ = F := by
        funext p; simp only [Function.comp_apply, hp]
      simp only [deckGerm₂, Germ.coe_compTendsto, hfun]
  map_mul' g₁ g₂ := by
    induction g₁ using Germ.inductionOn with
    | _ F₁ => induction g₂ using Germ.inductionOn with
      | _ F₂ => simp only [deckGerm₂, ← Germ.coe_mul, Germ.coe_compTendsto]; rfl
  map_add' g₁ g₂ := by
    induction g₁ using Germ.inductionOn with
    | _ F₁ => induction g₂ using Germ.inductionOn with
      | _ F₂ => simp only [deckGerm₂, ← Germ.coe_add, Germ.coe_compTendsto]; rfl

@[simp] theorem deckGermEquiv₂_v2 {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ m) = 1) :
    deckGermEquiv₂ hζ hpow (v2Germ : coverGerm c₁ c₂ n m)
      = (ζ : coverGerm c₁ c₂ n m) * v2Germ := rfl

@[simp] theorem deckGermEquiv₂_v1 {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ m) = 1) :
    deckGermEquiv₂ hζ hpow (v1Germ : coverGerm c₁ c₂ n m) = v1Germ := rfl

@[simp] theorem deckGermEquiv₂_z {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ m) = 1) :
    deckGermEquiv₂ hζ hpow (zGerm : coverGerm c₁ c₂ n m) = zGerm := rfl

/-- The `c₂` deck fixes every constant, hence fixes its multiplier. -/
theorem deckGermEquiv₂_const {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ m) = 1) (a : ℂ) :
    deckGermEquiv₂ hζ hpow ((a : coverGerm c₁ c₂ n m)) = (a : coverGerm c₁ c₂ n m) := by
  show deckGerm₂ hpow (a : coverGerm c₁ c₂ n m) = a
  simp only [deckGerm₂, Germ.const_compTendsto]

end Bottcher

namespace Bottcher

/-! ## 6c″: the unbounded-order dyadic tower of multipliers

The monodromy obstruction `q62_disconnected_both` consumes, for every depth `d`, a deck multiplier
`ζ` whose order exceeds `d`. The orders available on the cover are the powers `2^k` (the `k`-th dyadic
level), realised by primitive `2^k`-th roots of unity in `ℂ`. Since `2^k → ∞`, the tower has
unbounded order — exactly the `∀ d, ∃ … d < orderOf ζ` shape the obstruction needs. -/

/-- **The dyadic order tower in `ℂ`.** For every depth `d` there is a `2^k`-th root of unity `ζ`
(a genuine primitive one, `orderOf ζ = 2^k`) with `2^k > d`. The multiplier supply for the unbounded
monodromy tower, before transfer to the cover carrier. -/
theorem exists_dyadic_order_gt (d : ℕ) :
    ∃ (k : ℕ) (ζ : ℂ), ζ ^ (2 ^ k) = 1 ∧ ζ ≠ 0 ∧ orderOf ζ = 2 ^ k ∧ d < 2 ^ k := by
  obtain ⟨ζ, hord, hpow⟩ := exists_dyadic_primitive (d + 1)
  have hk : (0 : ℕ) < 2 ^ (d + 1) := by positivity
  have hne : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hk.ne'] at hpow; exact one_ne_zero hpow.symm
  exact ⟨d + 1, ζ, hpow, hne, hord, lt_trans (Nat.lt_succ_self d) Nat.lt_two_pow_self⟩

/-- **The dyadic order tower transferred to the cover germ ring.** For every depth `d` there is a
`2^k`-th root of unity `ζ` whose order *as a constant of the cover carrier* `coverGerm` is `2^k > d`
(the constant embedding preserves order, `orderOf_const_coverGerm`). This is the carrier-level
multiplier datum the disconnected-case obstruction feeds to `eq_zero_of_monodromy`: an automorphism
multiplier of unbounded order living in the same field as `φ_{c₁}, φ_{c₂}`. -/
theorem exists_dyadic_order_gt_coverGerm (c₁ c₂ : ℂ) (n m : ℕ) (d : ℕ) :
    ∃ (k : ℕ) (ζ : ℂ), ζ ^ (2 ^ k) = 1 ∧ ζ ≠ 0 ∧
      orderOf ((ζ : coverGerm c₁ c₂ n m)) = 2 ^ k ∧ d < 2 ^ k := by
  obtain ⟨k, ζ, hpow, hne, hord, hd⟩ := exists_dyadic_order_gt d
  exact ⟨k, ζ, hpow, hne, by rw [orderOf_const_coverGerm]; exact hord, hd⟩

/-- **Cover-germ `monoF` coordinate datum.**  For every bound `d`, the common pullback cover at a
deep enough `c₁`-level carries a genuine z-fixing deck automorphism: it fixes `z` and `v₂`, fixes its
constant multiplier, and scales `v₁` by a multiplier whose order exceeds `d`.  This is the
coordinate-level disconnected monodromy loop before passage to the connected meromorphic field
carrier. -/
theorem coverGerm_monoF_datum (c₁ c₂ : ℂ) (m d : ℕ) :
    ∃ (k : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ k) = 1),
      d < orderOf ((ζ : coverGerm c₁ c₂ k m)) ∧
      deckGermEquiv hζ hpow (zGerm : coverGerm c₁ c₂ k m) = zGerm ∧
      deckGermEquiv hζ hpow (v2Germ : coverGerm c₁ c₂ k m) = v2Germ ∧
      deckGermEquiv hζ hpow ((ζ : coverGerm c₁ c₂ k m)) = (ζ : coverGerm c₁ c₂ k m) ∧
      deckGermEquiv hζ hpow (v1Germ : coverGerm c₁ c₂ k m)
        = (ζ : coverGerm c₁ c₂ k m) * v1Germ := by
  obtain ⟨k, ζ, hpow, hζ, hord, hd⟩ := exists_dyadic_order_gt d
  have hcarrier : orderOf ((ζ : coverGerm c₁ c₂ k m)) = 2 ^ k := by
    rw [orderOf_const_coverGerm]
    exact hord
  refine ⟨k, ζ, hζ, hpow, ?_, deckGermEquiv_z hζ hpow, deckGermEquiv_v2 hζ hpow,
    deckGermEquiv_const hζ hpow ζ, deckGermEquiv_v1 hζ hpow⟩
  rwa [hcarrier]

/-- **Cover-germ `monoG` coordinate datum.**  Symmetric to `coverGerm_monoF_datum`: at a deep enough
`c₂`-level the second deck fixes `z` and `v₁`, fixes its constant multiplier, and scales `v₂` by
unbounded dyadic order. -/
theorem coverGerm_monoG_datum (c₁ c₂ : ℂ) (n d : ℕ) :
    ∃ (k : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ k) = 1),
      d < orderOf ((ζ : coverGerm c₁ c₂ n k)) ∧
      deckGermEquiv₂ hζ hpow (zGerm : coverGerm c₁ c₂ n k) = zGerm ∧
      deckGermEquiv₂ hζ hpow (v1Germ : coverGerm c₁ c₂ n k) = v1Germ ∧
      deckGermEquiv₂ hζ hpow ((ζ : coverGerm c₁ c₂ n k)) = (ζ : coverGerm c₁ c₂ n k) ∧
      deckGermEquiv₂ hζ hpow (v2Germ : coverGerm c₁ c₂ n k)
        = (ζ : coverGerm c₁ c₂ n k) * v2Germ := by
  obtain ⟨k, ζ, hpow, hζ, hord, hd⟩ := exists_dyadic_order_gt d
  have hcarrier : orderOf ((ζ : coverGerm c₁ c₂ n k)) = 2 ^ k := by
    rw [orderOf_const_coverGerm]
    exact hord
  refine ⟨k, ζ, hζ, hpow, ?_, deckGermEquiv₂_z hζ hpow, deckGermEquiv₂_v1 hζ hpow,
    deckGermEquiv₂_const hζ hpow ζ, deckGermEquiv₂_v2 hζ hpow⟩
  rwa [hcarrier]

end Bottcher

namespace Bottcher

/-- **The two formal decks commute.** `deckMap₁ ζ` (scales `v₁`, fixes `z,v₂`) and `deckMap₂ η`
(scales `v₂`, fixes `z,v₁`) act on independent coordinates, so they commute:
`deckMap₁ ζ ∘ deckMap₂ η = deckMap₂ η ∘ deckMap₁ ζ` (both send `(z,v₁,v₂) ↦ (z, ζv₁, ηv₂)`). Hence the
joint deck group generated on the common cover is the **abelian product** `μ_{2ⁿ} × μ_{2ᵐ}` — the
formal model of the two *independent* monodromies (one scaling `φ_{c₁}`, the other `φ_{c₂}`). This
product/commuting structure is exactly what makes `σ_n(φ_{c₂}) = φ_{c₂}` compatible with
`σ_m(φ_{c₁}) = φ_{c₁}` simultaneously: the `monoF` (scale `F=v₁`, fix `G=v₂`) and `monoG` (scale `G`,
fix `F`) data of `q62_disconnected_both` coexist on one carrier. Axiom-clean. -/
theorem deckMap₁_deckMap₂_comm (ζ η : ℂ) :
    deckMap₁ ζ ∘ deckMap₂ η = deckMap₂ η ∘ deckMap₁ ζ := by
  funext p
  grind [deckMap₁, deckMap₂]

end Bottcher
