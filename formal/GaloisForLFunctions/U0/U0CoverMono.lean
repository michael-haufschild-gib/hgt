/-
# u₀ on the Böttcher cover: the fixed coordinate of the dyadic monodromy

The disconnected-case monodromy of the u₀ ⟂ φ_b independence lives on the **cover** germ ring
`Bottcher.coverGerm` (where φ_b is a multivalued branch), not on the single-valued `meroField` carrier
— on the latter, scaling φ_b is not an automorphism (`Bottcher.CoverMonodromy` header). This file
supplies the u₀ half of the cover monodromy datum: u₀, being single-valued (a function of the base
coordinate `z`), lifts to the cover as a germ fixed by the deck transformation.

Combined with the Böttcher agent's `deckGermEquiv` (σ scales `v₁ = φ_b`, fixes `z` and constants;
`deckGermEquiv_v1`/`_z`/`_const`, `orderOf_const_coverGerm`), this completes the **full coordinate
action** the `q62_mixed` monodromy hypothesis requires, with `G = u₀`, `F = φ_b`:

* `σ u₀ = u₀`   — `deckGermEquiv_u0` (below),
* `σ φ_b = ζ·φ_b` — `Bottcher.deckGermEquiv_v1`,
* `σ ζ = ζ`     — `Bottcher.deckGermEquiv_const`,
* `orderOf ζ = 2ⁿ` (unbounded) — `Bottcher.orderOf_const_coverGerm` + `Bottcher.orderOf_dyadicRoot`.

What remains to assemble the field-level `mono` of `q62_mixed`: the **fraction field of the cover**
(`Bottcher` "Field-6", in progress) — a `Field M ⊇ ℂ(z)` with `σ` lifted to `M ≃ₐ[ℂ(z)] M` — and the
transcendence of u₀ over ℂ(z) *in that field* (the cover-carrier analogue of
`U0Transcendence.u0_no_relation`, since the cover's `z`-projection meets `Ext`). The coordinate action
here is the ring-level core those steps lift.
-/
import GaloisForLFunctions.U0.U0Transcendence
import GaloisForLFunctions.Bottcher.CoverMonodromy

open Filter Topology U0 U0NaturalBoundary U0Transcendence Bottcher Polynomial

namespace U0CoverMono

variable {c₁ c₂ : ℂ} {n m : ℕ}

/-- u₀ as a function of the base coordinate `z`, lifted to the Böttcher cover germ ring. It depends
only on `z = p.1`; since the deck transformation fixes `z`, this germ is fixed by the monodromy — the
single-valued `G` of `q62_mixed`. -/
noncomputable def u0Cover : coverGerm c₁ c₂ n m := (fun p : ℂ × ℂ × ℂ => u0 p.1)

/-- **σ_n fixes u₀** on the cover germ ring (deck map level). u₀ is single-valued (a function of `z`),
and `deckMap₁` fixes the `z`-coordinate. -/
@[aesop safe]
theorem deckGerm_u0 {ζ : ℂ} (hpow : ζ ^ (2 ^ n) = 1) :
    deckGerm hpow (u0Cover : coverGerm c₁ c₂ n m) = u0Cover := rfl

/-- **σ_n fixes u₀** as the ring automorphism `deckGermEquiv`. This is the `σ G = G` clause of the
dyadic-monodromy datum of `q62_mixed`, for `G = u₀` — the structural payoff of u₀ being single-valued:
it is *always* fixed by the tower, with no rigidity input. -/
@[aesop safe]
theorem deckGermEquiv_u0 {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ n) = 1) :
    deckGermEquiv hζ hpow (u0Cover : coverGerm c₁ c₂ n m) = u0Cover := rfl

/-- **Full coordinate action of the dyadic monodromy for `u₀ ⟂ φ_b`, on the cover germ ring (PROVEN).**
For a `2ⁿ`-th root of unity `ζ`, the deck automorphism `σ = deckGermEquiv ζ` scales `φ_b = v₁` by `ζ`,
fixes `u₀`, and fixes `ζ`. This is precisely the per-`ζ` data of `q62_mixed`'s `mono` hypothesis (with
`F = φ_b`, `G = u₀`); only the field structure and the order/unboundedness packaging remain to turn it
into the `∀ d, ∃ σ ζ m, …` datum over the cover's fraction field. -/
@[aesop safe]
theorem cover_mono_action {ζ : ℂ} (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ n) = 1) :
    deckGermEquiv hζ hpow (u0Cover : coverGerm c₁ c₂ n m) = u0Cover
    ∧ deckGermEquiv hζ hpow (v1Germ : coverGerm c₁ c₂ n m) = (ζ : coverGerm c₁ c₂ n m) * v1Germ
    ∧ deckGermEquiv hζ hpow ((ζ : coverGerm c₁ c₂ n m)) = (ζ : coverGerm c₁ c₂ n m) :=
  ⟨deckGermEquiv_u0 hζ hpow, deckGermEquiv_v1 hζ hpow, deckGermEquiv_const hζ hpow ζ⟩

/-- **u₀ satisfies no polynomial relation over ℂ(z) on the cover germ ring (PROVEN).** For nonzero
`P ∈ ℂ[z][Y]` of positive `Y`-degree, the relation germ `z ↦ P(z, u₀(z))` is nonzero in
`coverGerm c₁ c₂ n m`: vanishing there forces vanishing on the deep-exterior section
`(z, φ_{c₁}(z), φ_{c₂}(z))` (an open subset of `Ext`, via `bottcher_mem_commonPullback`), hence on all
of `Ext` by the identity theorem (`isConnected_Ext`), contradicting `u0_no_relation`. This is the
cover-carrier transcendence input, ready to lift to the cover's fraction field (Böttcher "Field-6")
as the `hTranscendental` of the `q62_mixed` instantiation. -/
@[aesop safe]
theorem u0Cover_no_relation (P : (Polynomial ℂ)[X]) (hP : 1 ≤ P.natDegree)
    (hrel : ((fun p : ℂ × ℂ × ℂ => evalU0 P p.1 : ℂ × ℂ × ℂ → ℂ) : coverGerm c₁ c₂ n m) = 0) :
    False := by
  rw [← Germ.coe_zero, Germ.coe_eq] at hrel
  have hcov : ∀ p ∈ commonPullback c₁ c₂ n m, evalU0 P p.1 = 0 :=
    fun p hp => eventually_principal.mp hrel p hp
  set Mb : ℝ := max 2 (max ‖c₁‖ ‖c₂‖) with hMb
  have hdeep : ∀ z : ℂ, Mb < ‖z‖ → evalU0 P z = 0 := by
    intro z hz
    have hz2 : 2 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
    have hc1 : ‖c₁‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_right 2 _)) hz)
    have hc2 : ‖c₂‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt
      (le_trans (le_max_right _ _) (le_max_right 2 _)) hz)
    have hmem := hcov (z, bottcherCoord c₁ z, bottcherCoord c₂ z)
      (bottcher_mem_commonPullback hc1 hz2 hc2 hz2)
    exact hmem
  have han : AnalyticOnNhd ℂ (evalU0 P) Ext := by
    have he : evalU0 P = fun z => P.eval₂ (evalRingHom z) (u0 z) := funext (evalU0_apply P)
    rw [he]; exact relation_analytic P
  have hz1mem : ((Mb + 1 : ℝ) : ℂ) ∈ {z : ℂ | Mb < ‖z‖} := by
    simp only [Set.mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by have := le_max_left 2 (max ‖c₁‖ ‖c₂‖); linarith)]; linarith
  have hz1ext : ((Mb + 1 : ℝ) : ℂ) ∈ Ext := by
    have h2 : (2:ℝ) ≤ Mb := le_max_left _ _
    simp only [Ext, Set.mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith)]; linarith
  have hopen : IsOpen {z : ℂ | Mb < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hExt : ∀ z ∈ Ext, evalU0 P z = 0 := by
    have hfreq : ∃ᶠ z in 𝓝[≠] ((Mb + 1 : ℝ) : ℂ), evalU0 P z = 0 :=
      ((Filter.eventually_iff.mpr (Filter.mem_of_superset (hopen.mem_nhds hz1mem)
        (fun z hz => hdeep z hz))).filter_mono nhdsWithin_le_nhds).frequently
    exact fun z hz => han.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isConnected_Ext.isPreconnected hz1ext hfreq hz
  exact u0_no_relation_ringHom P hP hExt

end U0CoverMono
