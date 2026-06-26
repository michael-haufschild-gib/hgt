/-
# Deck-transformation scaling of the Böttcher coordinate (hDisc cover lane)

The disconnected-case lift data needs a self-map `g` of the cover that *fixes the base projection*
`f_c^[n]` (a deck transformation: `f_c^[n] ∘ g = f_c^[n]`) yet **scales** the Böttcher coordinate
`φ_c ∘ g = ζ · φ_c` by a `2ⁿ`-th root of unity `ζ`. This file proves the value-level mechanism of that
scaling, directly from the iterated functional equation `φ_c(f_c^[n] z) = φ_c(z)^{2ⁿ}`
(`bottcherCoord_iterate_escape`): two escape points with the same `f_c^[n]`-image have Böttcher values
differing by a `2ⁿ`-th root of unity. This is the exact source of the dyadic monodromy multiplier as a
map property (the deck group `μ_{2ⁿ}` acting by multiplication), and the `c₁`/`c₂` asymmetry the lift
data exploits: a deck transformation of `f_{c₁}^[n]` scales `φ_{c₁}` by a primitive root but can leave
`φ_{c₂}` fixed (its loop is null-homotopic in the other basin).
-/
import GaloisForLFunctions.Bottcher.LiftExists
import GaloisForLFunctions.Bottcher.MeromorphicField
import GaloisForLFunctions.Bottcher.FarFieldUnivalence
import GaloisForLFunctions.Bottcher.FarFieldSurjective

open Complex Set Filter Topology

namespace Bottcher

/-- **Deck scaling of the Böttcher coordinate.** Two escape points `w, z` with the same `f_c^[n]`-image
(a deck-transformation pair) have Böttcher values differing by a `2ⁿ`-th root of unity:
`φ_c w = ζ · φ_c z` with `ζ^{2ⁿ} = 1`. Immediate from the iterated functional equation
`φ_c(f_c^[n] ·) = φ_c(·)^{2ⁿ}` (`bottcherCoord_iterate_escape`): `(φ_c w)^{2ⁿ} = (φ_c z)^{2ⁿ}`, so their
ratio `ζ` is a `2ⁿ`-th root of unity. The value-level core of the deck group `μ_{2ⁿ}` acting by
multiplication on `φ_c`. -/
theorem bottcherCoord_deck_scaling {c : ℂ} {n : ℕ} {z w : ℂ}
    (hz : z ∈ escapeOpen c) (hw : w ∈ escapeOpen c)
    (hdeck : (quadratic c)^[n] w = (quadratic c)^[n] z) :
    ∃ ζ : ℂ, ζ ^ (2 ^ n) = 1 ∧ bottcherCoord c w = ζ * bottcherCoord c z := by
  have h1 : bottcherCoord c w ^ (2 ^ n) = bottcherCoord c z ^ (2 ^ n) := by
    rw [← bottcherCoord_iterate_escape hw n, ← bottcherCoord_iterate_escape hz n, hdeck]
  have hz0 : bottcherCoord c z ≠ 0 := bottcherCoord_ne_zero c z
  refine ⟨bottcherCoord c w / bottcherCoord c z, ?_, ?_⟩
  · rw [div_pow, h1, div_self (pow_ne_zero _ hz0)]
  · field_simp

/-- **The deck multiplier as a genuine `2ⁿ`-th root of unity in `ℂˣ`.** Packages
`bottcherCoord_deck_scaling`'s `ζ` as an element of the `2ⁿ`-th roots of unity `rootsOfUnity (2ⁿ) ℂ`
(`ζ` is a unit since `‖ζ‖ = 1`), the form the deck-group identification `μ_{2ⁿ} = (powMonoidHom 2ⁿ).ker`
consumes. -/
theorem bottcherCoord_deck_scaling_norm {c : ℂ} {n : ℕ} {z w : ℂ}
    (hz : z ∈ escapeOpen c) (hw : w ∈ escapeOpen c)
    (hdeck : (quadratic c)^[n] w = (quadratic c)^[n] z) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ζ ^ (2 ^ n) = 1 ∧ bottcherCoord c w = ζ * bottcherCoord c z := by
  obtain ⟨ζ, hζpow, hζeq⟩ := bottcherCoord_deck_scaling hz hw hdeck
  exact ⟨ζ, Complex.norm_eq_one_of_pow_eq_one hζpow (pow_ne_zero n (by norm_num)), hζpow, hζeq⟩

/-- **Pointwise scaling ⟹ germ-level scaling clause (lift-data bridge).** If a self-map `g` of `U`
multiplies `f₁` by the constant `ζ₀` pointwise on `U`, then at the germ level
`(f₁).compTendsto g = constToAnalytic ζ₀ · f₁` — exactly the scaling clause of `hliftF`. Reduces the
analytic lift datum to a pointwise deck identity; combined with `bottcherCoord_deck_scaling` it turns a
geometric deck transformation into the germ-field scaling `q62_independence_disconnected_of_lifts`
consumes. -/
theorem compTendsto_germ_scaling {U : Set ℂ} {g f₁ : ℂ → ℂ} (ζ₀ : ℂ)
    (hmaps : Set.MapsTo g U U)
    (hscale : ∀ z ∈ U, f₁ (g z) = ζ₀ * f₁ z) :
    (↑f₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
      = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (↑f₁ : Germ (𝓟 U) ℂ) := by
  rw [Germ.coe_compTendsto]
  have hconst : ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
      = (↑(fun _ : ℂ => ζ₀) : Germ (𝓟 U) ℂ) := rfl
  rw [hconst, ← Germ.coe_mul, Germ.coe_eq]
  exact eventually_principal.mpr (fun z hz => hscale z hz)

/-- **Pointwise invariance ⟹ germ-level fixing clause (lift-data bridge).** If a self-map `g` of `U`
fixes `f₂` pointwise on `U`, then `(f₂).compTendsto g = f₂` at the germ level — the fixing clause of
`hliftF`/`hliftG` (applied to `φ_{c₂}` and to the base projection, the latter discharging
"`g` fixes `ℂ(z)`"). -/
theorem compTendsto_germ_fixed {U : Set ℂ} {g f₂ : ℂ → ℂ}
    (hmaps : Set.MapsTo g U U)
    (hfix : ∀ z ∈ U, f₂ (g z) = f₂ z) :
    (↑f₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
      = (↑f₂ : Germ (𝓟 U) ℂ) := by
  rw [Germ.coe_compTendsto, Germ.coe_eq]
  exact eventually_principal.mpr (fun z hz => hfix z hz)

/-- **Far-field deck condition: value-scaling ⟹ projection fixed.** Two far-field points whose Böttcher
values differ by a `2ⁿ`-th root of unity have the same `f_c^[n]`-image (converse of
`bottcherCoord_deck_scaling`, via far-field injectivity L2 `bottcherCoord_injOn_far`). So on the far
field the deck-pair relation `f_c^[n] z' = f_c^[n] z` is EQUIVALENT to `φ_c z' = ζ·φ_c z`, `ζ^{2ⁿ}=1` —
the value-coordinate model `w ↦ ζw` of the dyadic deck group `μ_{2ⁿ}` the deck map `g` is read off from. -/
theorem iterate_eq_of_bottcherCoord_scaling {c : ℂ} {R : ℝ} (n : ℕ) {ζ z z' : ℂ}
    (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2)
    (hz : R < ‖z‖) (hz' : R < ‖z'‖)
    (hζ : ζ ^ (2 ^ n) = 1) (hscale : bottcherCoord c z' = ζ * bottcherCoord c z) :
    (quadratic c)^[n] z' = (quadratic c)^[n] z := by
  have hRmax : max 2 ‖c‖ < R := by nlinarith [le_max_left 2 ‖c‖, norm_nonneg c]
  have hzE : z ∈ escapeOpen c := lt_trans hRmax hz
  have hz'E : z' ∈ escapeOpen c := lt_trans hRmax hz'
  have hval : bottcherCoord c ((quadratic c)^[n] z') = bottcherCoord c ((quadratic c)^[n] z) := by
    rw [bottcherCoord_iterate_escape hz'E n, bottcherCoord_iterate_escape hzE n, hscale,
      mul_pow, hζ, one_mul]
  have hzn : R < ‖(quadratic c)^[n] z‖ :=
    lt_of_lt_of_le hz (norm_iterate_ge (mem_escapeOpen_regime hzE).1 (mem_escapeOpen_regime hzE).2 n)
  have hz'n : R < ‖(quadratic c)^[n] z'‖ :=
    lt_of_lt_of_le hz' (norm_iterate_ge (mem_escapeOpen_regime hz'E).1 (mem_escapeOpen_regime hz'E).2 n)
  exact bottcherCoord_injOn_far hR1 hR2 hz'n hzn hval

/-- **Far-field deck image (the pointwise deck map).** For a `2ⁿ`-th root of unity `ζ` and a far-field
`z` whose Böttcher value is deep enough, there is a far-field `z'` with `φ_c z' = ζ·φ_c z` AND
`f_c^[n] z' = f_c^[n] z` — the deck partner of `z` under `μ_{2ⁿ}`. Assembles far-field surjectivity
(`exists_far_preimage`: the preimage of `ζ·φ_c z`, which has the same modulus as `φ_c z` since `‖ζ‖=1`)
with the deck condition (`iterate_eq_of_bottcherCoord_scaling`). This realizes the value of the deck map
`g(z) = ψ(ζ·φ_c z)`; with `ψ` analytic (L3) it is the analytic deck self-map of the far field — the seed
continued inward to the cylinders for `hliftF`. -/
theorem exists_deck_image {c : ℂ} {R : ℝ} (n : ℕ) {ζ z : ℂ}
    (hζ : ζ ^ (2 ^ n) = 1) (hζ1 : ‖ζ‖ = 1)
    (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2)
    (hz : R < ‖z‖)
    (hb1 : 768 * ‖c‖ + 64 < ‖bottcherCoord c z‖ ^ 2)
    (hb2 : 8 * max 2 ‖c‖ < ‖bottcherCoord c z‖)
    (hb3 : 2 * R < ‖bottcherCoord c z‖) :
    ∃ z', R < ‖z'‖ ∧ bottcherCoord c z' = ζ * bottcherCoord c z ∧
          (quadratic c)^[n] z' = (quadratic c)^[n] z := by
  have hnorm : ‖ζ * bottcherCoord c z‖ = ‖bottcherCoord c z‖ := by rw [norm_mul, hζ1, one_mul]
  obtain ⟨z', hz'ge, hz'eq⟩ := exists_far_preimage (c := c) (w := ζ * bottcherCoord c z)
    (by rw [hnorm]; exact hb1) (by rw [hnorm]; exact hb2)
  have hz'far : R < ‖z'‖ := by
    have h := hz'ge; rw [hnorm] at h; linarith [hb3]
  exact ⟨z', hz'far, hz'eq, iterate_eq_of_bottcherCoord_scaling n hR1 hR2 hz hz'far hζ hz'eq⟩

/-- **The analytic far-field deck map** `g(z) = ψ(ζ·φ_c z)`. For a `2ⁿ`-th root of unity `ζ` and `z`
whose Böttcher value is deep enough, `g` is analytic at `z`, lands in the far field, scales the Böttcher
coordinate by `ζ` (`φ_c(g z) = ζ·φ_c z`), and fixes the projection `f_c^[n]` (`f_c^[n](g z) = f_c^[n] z`).
This realizes the deck transformation of `f_c^[n]` as a genuine analytic self-map: the `φ_{c₁}`-scaling
and projection-fixing clauses of `hliftF`. (The remaining `hliftF` clause, `φ_{c₂}∘g = φ_{c₂}`, is the
cylinder-loop input from L1 `pathInt_dlog_lift_closed_eq_zero`, which the FAR-FIELD deck map does NOT
satisfy — there the loop encloses both Julia sets — and is the genuine remaining analytic construction.) -/
theorem exists_far_deckMap (c : ℂ) (n : ℕ) {ζ : ℂ} (hζ : ζ ^ (2 ^ n) = 1) (hζ1 : ‖ζ‖ = 1)
    {R : ℝ} (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2) :
    ∃ ψ : ℂ → ℂ, ∀ z : ℂ, R < ‖z‖ →
        768 * ‖c‖ + 64 < ‖bottcherCoord c z‖ ^ 2 → 8 * max 2 ‖c‖ < ‖bottcherCoord c z‖ →
        2 * R < ‖bottcherCoord c z‖ →
        AnalyticAt ℂ (fun w => ψ (ζ * bottcherCoord c w)) z ∧
        bottcherCoord c (ψ (ζ * bottcherCoord c z)) = ζ * bottcherCoord c z ∧
        (quadratic c)^[n] (ψ (ζ * bottcherCoord c z)) = (quadratic c)^[n] z := by
  obtain ⟨ψ, hψleft, hψan, hψright⟩ := exists_analytic_inverse_far (c := c) hR1 hR2
  refine ⟨ψ, fun z hz hb1 hb2 hb3 => ?_⟩
  -- the deck partner z' (far field) with φ_c z' = ζ φ_c z
  obtain ⟨z', hz'far, hz'eq, hz'iter⟩ := exists_deck_image n hζ hζ1 hR1 hR2 hz hb1 hb2 hb3
  -- ψ at ζ φ_c z = φ_c z'  inverts to z'
  have hψval : ψ (ζ * bottcherCoord c z) = z' := by rw [← hz'eq]; exact hψleft z' hz'far
  refine ⟨?_, ?_, ?_⟩
  · -- analytic: ψ analytic at φ_c z' (= ζ φ_c z), composed with the analytic ζ·φ_c
    have hφan : AnalyticAt ℂ (fun w => ζ * bottcherCoord c w) z := by
      have : max 2 ‖c‖ < ‖z‖ := lt_trans (by nlinarith [le_max_left 2 ‖c‖, norm_nonneg c]) hz
      exact analyticAt_const.mul (analyticOnNhd_bottcherCoord_full c z this)
    have hψatz' : AnalyticAt ℂ ψ (ζ * bottcherCoord c z) := by
      rw [← hz'eq]; exact hψan z' hz'far
    have hcomp : AnalyticAt ℂ (ψ ∘ (fun w => ζ * bottcherCoord c w)) z := by
      apply AnalyticAt.comp
      · exact hψatz'
      · exact hφan
    exact hcomp
  · rw [hψval]; exact hz'eq
  · rw [hψval]; exact hz'iter

end Bottcher

namespace Bottcher

open Set

/-- **The deck `g = ψ∘ρ∘φ` fixes every ρ-invariant function of the lift (the `a₂`/projection-fixing
mechanism).** Companion to `deck_scaling_of_invertible_lift` (which *scales* the lift `φ`):
if `a₂ = h∘φ` for an `h` invariant under the value-rotation `ρ` (`h∘ρ = h` on `V`), then `a₂∘g = a₂`
on `U`. Proof: `φ(g z) = φ(ψ(ρ(φ z))) = ρ(φ z)` (the section identity `φ∘ψ = id`), so
`a₂(g z) = h(ρ(φ z)) = h(φ z) = a₂ z`. This is the precise reason the SAME deck that scales `φ̃_{c₁}`
leaves `a₂ = φ_{c₂}∘p₀` and the projection `p₀` FIXED on a cylinder chart: both are `ρ`-invariant
functions of `φ̃_{c₁}` (functions of `φ̃_{c₁}^{2ⁿ} = φ_{c₁}∘f^[n]∘p₀`). Together with
`deck_scaling_of_invertible_lift` it turns a single cylinder chart `ψ` (inverse of `φ̃_{c₁}` on a
`ζ`-invariant value annulus) into the FULL `monoF_witness_projection_base` lift datum — scale `a₁`,
fix `a₂`, fix `p₀` — which the far-field deck (`exists_far_deckMap`) cannot supply (there the loop
encloses both Julia sets, so `a₂` is scaled, not fixed). Axiom-clean. -/
theorem deck_fixes_invariant_of_lift {U V : Set ℂ} {φ ψ ρ h a₂ : ℂ → ℂ}
    (hinv : Set.EqOn (φ ∘ ψ) id V) (hρmaps : Set.MapsTo ρ V V)
    (hφmaps : Set.MapsTo φ U V)
    (hgmaps : Set.MapsTo (ψ ∘ ρ ∘ φ) U U)
    (hhinv : Set.EqOn (h ∘ ρ) h V)
    (ha₂ : Set.EqOn a₂ (h ∘ φ) U) :
    Set.EqOn (a₂ ∘ (ψ ∘ ρ ∘ φ)) a₂ U := by
  intro z hz
  have hφz : φ z ∈ V := hφmaps hz
  have hρφz : ρ (φ z) ∈ V := hρmaps hφz
  have hgz : (ψ ∘ ρ ∘ φ) z ∈ U := hgmaps hz
  have hφgz : φ ((ψ ∘ ρ ∘ φ) z) = ρ (φ z) := by
    have := hinv hρφz
    simpa [Function.comp] using this
  calc a₂ ((ψ ∘ ρ ∘ φ) z)
      = h (φ ((ψ ∘ ρ ∘ φ) z)) := by simpa [Function.comp] using ha₂ hgz
    _ = h (ρ (φ z)) := by rw [hφgz]
    _ = h (φ z) := by simpa [Function.comp] using hhinv hφz
    _ = a₂ z := by simpa [Function.comp] using (ha₂ hz).symm

end Bottcher
