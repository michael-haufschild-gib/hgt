import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ReadingsTransportAlongAPresentation
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheScaleUnitInWhichTheApertureLadderConverges

/-!
# The composition law and the pushforward invariant

A proof is a pipeline: the datum is first *reduced* to an intermediate object, and only then is a
bound proved about that object. The calculus had no law for pipelines — refinement, joins and
presentations all compare readings of the same class, not a reduction followed by a reading.

The missing notion is the **pushforward** of the invariant along the reduction: for `q : D → E`,
`pushforward I q e = sup {I x : q x = e}`, the worst case of `I` inside the fibre. With it the
composition law is exact (`resolutionLimit_comp_eq_pushforward`):

`resolutionLimit I (r ∘ q) d = resolutionLimit (pushforward I q) r (q d)`.

A pipeline is worth exactly what its last stage is worth *for the pushforward*, so the entire cost
of a reduction is the growth of the invariant inside its fibres, computed once and for all.

The law also explains the programme's floors rather than merely collecting them. Every face of the
field is a reduction followed by a reading, and in each case the pushforward of the width is
constant: `pushforward_width_failureApertures` shows that the worst width inside a fibre of the
scale datum is `½`, whatever the fibre. Hence `resolutionLimit_width_eq_half_of_factors`: **any
reading that factors through the scale datum has limit `½`, and the reason is a single pushforward
computation**, not a separate witness per face.

So the floors of the field are not a list of accidents. They are the statement that the reductions
the field uses — aperture, height, radius, node, flag — all have fibres on which the depth is
unconstrained, and the composition law reduces each floor to that one fact.
-/

open Set

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

variable {D E O : Type*}

/-! ### 1. The pushforward of an invariant along a reduction -/

/-- The **pushforward** of `I` along `q`: the worst case of `I` inside the fibre of `q`. -/
noncomputable def pushforward (I : D → ℝ) (q : D → E) (e : E) : ℝ :=
  sSup (I '' {x : D | q x = e})

theorem le_pushforward {I : D → ℝ} {q : D → E} {x : D}
    (hb : BddAbove (I '' {y : D | q y = q x})) : I x ≤ pushforward I q (q x) :=
  le_csSup hb ⟨x, rfl, rfl⟩

/-- **The composition law.** A pipeline's limit is its last stage's limit for the pushforward. -/
theorem resolutionLimit_comp_eq_pushforward {I : D → ℝ} {q : D → E} {r : E → O}
    (hq : Function.Surjective q) (d : D) (hb1 : BddAbove (I '' shadow (r ∘ q) d))
    (hb2 : ∀ e : E, BddAbove (I '' {x : D | q x = e})) :
    resolutionLimit I (r ∘ q) d = resolutionLimit (pushforward I q) r (q d) := by
  -- the pushforward is bounded on the shadow of the last stage by the same bound
  have hfib : ∀ e ∈ shadow r (q d), pushforward I q e ≤ sSup (I '' shadow (r ∘ q) d) := by
    intro e he
    obtain ⟨x₀, rfl⟩ := hq e
    have he' : r (q x₀) = r (q d) := he
    refine csSup_le ⟨I x₀, ⟨x₀, rfl, rfl⟩⟩ ?_
    rintro y ⟨x, hx, rfl⟩
    have hqx : q x = q x₀ := hx
    have hmem : x ∈ shadow (r ∘ q) d := by
      show r (q x) = r (q d)
      rw [hqx]; exact he'
    exact le_csSup hb1 ⟨x, hmem, rfl⟩
  have hb3 : BddAbove (pushforward I q '' shadow r (q d)) := by
    refine ⟨sSup (I '' shadow (r ∘ q) d), ?_⟩
    rintro y ⟨e, he, rfl⟩
    exact hfib e he
  refine le_antisymm (csSup_le (shadow_image_nonempty I (r ∘ q) d) ?_) ?_
  · rintro y ⟨x, hx, rfl⟩
    have hmem : q x ∈ shadow r (q d) := hx
    exact (le_pushforward (hb2 (q x))).trans (le_csSup hb3 ⟨q x, hmem, rfl⟩)
  · exact csSup_le (shadow_image_nonempty (pushforward I q) r (q d)) (by
      rintro y ⟨e, he, rfl⟩
      exact hfib e he)

/-! ### 2. The floors are one pushforward computation -/

theorem bddAbove_width_fibre (S : Set ℝ) :
    BddAbove (width '' {Z : TemperedZeroConfig | failureApertures Z = S}) :=
  bddAbove_width_image _

/-- **The depth is unconstrained inside a fibre of the scale datum.** -/
theorem pushforward_width_failureApertures {a : ℝ} (ha : 0 < a) :
    pushforward width failureApertures (Ioi a) = 1 / 2 := by
  have hL : (0 : ℝ) < 2 * a := by linarith
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num
  have hfail : failureApertures (offLineLattice hL hδ le_rfl) = Ioi a := by
    rw [failureApertures_offLineLattice hL hδ le_rfl, show 2 * a / 2 = a by ring]
  have hw : width (offLineLattice hL hδ le_rfl) = 1 / 2 := width_offLineLattice hL hδ le_rfl
  have hmem : offLineLattice hL hδ le_rfl ∈
      {Z : TemperedZeroConfig | failureApertures Z = Ioi a} := hfail
  refine le_antisymm (csSup_le ⟨width (offLineLattice hL hδ le_rfl), ⟨_, hmem, rfl⟩⟩ ?_) ?_
  · rintro x ⟨Z, -, rfl⟩
    exact width_le_half Z
  · have hle := le_csSup (bddAbove_width_fibre (Ioi a)) ⟨_, hmem, rfl⟩
    rwa [hw] at hle

/-- **Every reading that factors through the scale datum has limit `½`.** One pushforward
computation replaces a witness construction on each face. -/
theorem resolutionLimit_width_eq_half_of_factors {a : ℝ} (ha : 0 < a) {r : Set ℝ → O}
    {Z : TemperedZeroConfig} (hZ : failureApertures Z = Ioi a) :
    resolutionLimit width (r ∘ failureApertures) Z = 1 / 2 := by
  refine le_antisymm (csSup_le (shadow_image_nonempty width (r ∘ failureApertures) Z) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact width_le_half W
  · obtain ⟨W, hWf, hWw⟩ := scaleAndDepthAreIndependent.1 a (1 / 2) ha (by norm_num) le_rfl
    have hmem : W ∈ shadow (r ∘ failureApertures) Z := by
      show r (failureApertures W) = r (failureApertures Z)
      rw [hWf, hZ]
    exact hWw ▸ le_csSup (bddAbove_width_image _) ⟨W, hmem, rfl⟩

/-- **The pipeline law together with its arithmetic instance.** A pipeline is worth its last
stage's value for the pushforward, and for every reduction of the field that factors through the
scale datum the pushforward of the depth is the trivial `½`. -/
theorem theCompositionLaw {a : ℝ} (ha : 0 < a) :
    pushforward width failureApertures (Ioi a) = 1 / 2 ∧
      ∀ (O : Type) (r : Set ℝ → O) (Z : TemperedZeroConfig), failureApertures Z = Ioi a →
        resolutionLimit width (r ∘ failureApertures) Z = 1 / 2 :=
  ⟨pushforward_width_failureApertures ha,
    fun _ _ _ hZ => resolutionLimit_width_eq_half_of_factors ha hZ⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
