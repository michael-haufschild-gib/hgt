/-
# One-sided points, visibility from infinity, and the general-point tip certificate (L3)

The sound "part A" of the audited answer to open problem 5, in general-point form (the
`holeFreeTip_of_collar` datum without the collar/Schoenflies specialization).

* `OneSidedAt c x` — `x` is a boundary point of `filledJulia c` with a single local access to the
  exterior: for all small `ρ`, `ball x ρ \ filledJulia c` is connected.  (The `∀`-small-`ρ` form;
  the fixed-`ρ` form of the answer has a radius-monotonicity gap.)
* `VisibleFromInfinity c₁ c₂ x` — `x` is on `∂W`, encoded operationally as: there is an unbounded
  preconnected subset `W` of the joint complement with `x ∈ closure W`.  This is the exact content
  of "the local exterior of `x` reaches `∞`".
* `ExposedOneSided c₁ c₂` — the open-problem-6 statement (for one ordering): a one-sided point of
  `J_{c₁}`, off `K_{c₂}`, visible from infinity.

The **certificate lemma** `holeFreeTip_of_oneSided` turns any such exposed one-sided point into the
`HoleFreeTip` datum the both-connected pair chain consumes.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.TipWApproach

open Set Metric Bornology

namespace Bottcher

/-- **One-sided boundary point.** `x` lies on the Julia set of `c` and has a single local access
to the exterior: for every small radius `ρ`, the punctured ball `ball x ρ \ filledJulia c` is
connected. -/
def OneSidedAt (c x : ℂ) : Prop :=
  x ∈ frontier (filledJulia c) ∧
    ∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → IsConnected (Metric.ball x ρ \ filledJulia c)

/-- **Visible from infinity** (`x ∈ ∂W`, operationally): there is an unbounded preconnected subset
`W` of the joint complement `ℂ ∖ (K₁ ∪ K₂)` with `x` in its closure — i.e. the exterior near `x`
connects to `∞`. -/
def VisibleFromInfinity (c₁ c₂ x : ℂ) : Prop :=
  ∃ W : Set ℂ, IsPreconnected W ∧ ¬ IsBounded W ∧
    W ⊆ (filledJulia c₁ ∪ filledJulia c₂)ᶜ ∧ x ∈ closure W

/-- **Exposed one-sided point** — the open-problem-6 statement for the ordering `(c₁, c₂)`: some
one-sided point of `J_{c₁}`, off `K_{c₂}`, is visible from infinity. -/
def ExposedOneSided (c₁ c₂ : ℂ) : Prop :=
  ∃ x, OneSidedAt c₁ x ∧ x ∉ filledJulia c₂ ∧ VisibleFromInfinity c₁ c₂ x

/-- **Density of one-sided points** — the classical ray-landing input, consumed as a named Prop:
one-sided points are dense in the Julia set (β-fixed point one-sided, its regular backward orbit
dense). -/
def OneSidedDense (c : ℂ) : Prop :=
  ∀ p ∈ frontier (filledJulia c), ∀ ε > 0, ∃ q, OneSidedAt c q ∧ dist p q < ε

/-- **The general-point tip certificate.** An exposed one-sided point of `J_{c₁}` yields the
`HoleFreeTip` datum: pick `r` below both the one-sided radius and the distance to `K_{c₂}`; the
punctured ball is connected and, being anchored to the visibility carrier `W`, every basin point of
the ball lies in the unbounded preconnected set `(ball x r \ K₁) ∪ W ⊆ (K₁ ∪ K₂)ᶜ`. -/
theorem holeFreeTip_of_oneSided {c₁ c₂ x : ℂ}
    (hos : OneSidedAt c₁ x) (hx2 : x ∉ filledJulia c₂)
    (hvis : VisibleFromInfinity c₁ c₂ x) :
    ∃ r > 0, HoleFreeTip c₁ c₂ x r := by
  obtain ⟨hfront, ρ₀, hρ₀, hconn⟩ := hos
  obtain ⟨W, hWconn, hWunbd, hWcompl, hxW⟩ := hvis
  -- a `K₂`-free ball around `x`
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl x hx2
  set r : ℝ := min δ ρ₀ with hrdef
  have hr : 0 < r := lt_min hδ hρ₀
  have hrδ : r ≤ δ := min_le_left _ _
  have hrρ₀ : r ≤ ρ₀ := min_le_right _ _
  have hballδ : Metric.ball x r ⊆ (filledJulia c₂)ᶜ :=
    (Metric.ball_subset_ball hrδ).trans hδsub
  -- the punctured ball is connected (one-sidedness at radius `r`)
  have hpunct : IsConnected (Metric.ball x r \ filledJulia c₁) := hconn r hr hrρ₀
  -- a shared anchor point of `ball x r \ K₁` and `W`
  obtain ⟨w₀, hw₀ball, hw₀W⟩ :=
    mem_closure_iff.mp hxW _ Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hw₀notK₁ : w₀ ∉ filledJulia c₁ := fun h => hWcompl hw₀W (Or.inl h)
  have hw₀mem : w₀ ∈ Metric.ball x r \ filledJulia c₁ := ⟨hw₀ball, hw₀notK₁⟩
  -- the escape carrier `V := (ball x r \ K₁) ∪ W`, uniform in the basin point
  set V : Set ℂ := (Metric.ball x r \ filledJulia c₁) ∪ W with hVdef
  have hVconn : IsPreconnected V :=
    hpunct.isPreconnected.union w₀ hw₀mem hw₀W hWconn
  have hVunbd : ¬ IsBounded V := fun hbd => hWunbd (hbd.subset subset_union_right)
  have hVcompl : V ⊆ (filledJulia c₁ ∪ filledJulia c₂)ᶜ := by
    rintro z (⟨hzb, hzK₁⟩ | hzW)
    · rintro (h | h)
      · exact hzK₁ h
      · exact hballδ hzb h
    · exact hWcompl hzW
  -- assemble the `HoleFreeTip`
  refine ⟨r, hr, hr, hfront, ?_, ?_⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    exact hballδ hz1 hz2
  · intro q hq hqK₁
    exact ⟨V, Or.inl ⟨hq, hqK₁⟩, hVconn, hVunbd, hVcompl⟩

end Bottcher
