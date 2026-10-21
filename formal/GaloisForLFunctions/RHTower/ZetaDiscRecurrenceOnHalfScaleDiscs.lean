import GaloisForLFunctions.RHTower.ZetaDiscRecurrenceOnZeroFreeDiscs

/-!
# Fixed-base recurrence of `ζ` on every half-scale disc of the strip

A closed disc `closedBall c r` is *half-scale* when its doubled closure lies in the right
half-strip: `0 < r`, `1/2 < Re c − 2r` and `Re c + 2r < 1` (`IsHalfScaleStripDisc`).  With the
Pechersky prime-sum lemma at its natural rate (`ρ < 1 − Re z₀`), the Hardy disc of radius
`ρ = 3r/2` about `c` is admissible for every half-scale disc, and the only zero-free hypothesis
needed is on the ball of radius `2r`:

* `zetaDiscStronglyRecurrentOn_of_zeroFree_halfScale`: if `ζ` has no zero on `ball c (2r)`, then
  `ζ` is strongly recurrent on `closedBall c r`;
* `zetaDiscStronglyRecurrentOn_of_riemannHypothesis`: under RH, `ζ` is strongly recurrent on
  every half-scale disc;
* `riemannHypothesis_iff_forall_halfScale_zetaDiscStronglyRecurrentOn`: RH holds if and only if
  `ζ` is strongly recurrent on every half-scale disc (the converse is the local Bagchi
  criterion), with the head-target form
  `riemannHypothesis_iff_forall_halfScale_headTargetUniformlyDense`.

The former constraint `3ρ < 1 − Re z₀` reached only discs with `r < (1 − Re c)/3`, so the
"every half-scale disc" form was out of reach.  The remaining gap to all closed discs of the strip
is the doubled-closure margin of the Euler tail law, not the Pechersky lemma.
-/

open Complex Filter Topology Metric MeasureTheory Set

noncomputable section

namespace RHTower

/-- A closed disc of positive radius whose doubled closure lies in the right half-strip. -/
def IsHalfScaleStripDisc (c : ℂ) (r : ℝ) : Prop :=
  0 < r ∧ 1 / 2 < c.re - 2 * r ∧ c.re + 2 * r < 1

/-- **Recurrence on a zero-free half-scale disc.**  If `ζ` has no zero on `ball c (2r)` and
`closedBall c r` is half-scale, then `ζ` is strongly recurrent on `closedBall c r`.  The Hardy
disc has radius `3r/2`, the zero-free disc has radius `(3r/2)(4/3) = 2r`, and the recurrence
disc is the sub-disc of radius `(3r/2)(2/3) = r`. -/
theorem zetaDiscStronglyRecurrentOn_of_zeroFree_halfScale {c : ℂ} {r : ℝ}
    (hK : IsHalfScaleStripDisc c r) (hζ : ∀ z ∈ ball c (2 * r), riemannZeta z ≠ 0) :
    ZetaDiscStronglyRecurrentOn (closedBall c r) := by
  obtain ⟨hr, h0, h1⟩ := hK
  have hr8 : r < 1 / 8 := by linarith
  have h := zetaDiscStronglyRecurrentOn_of_zeroFree c (ρ := 3 / 2 * r) (by positivity)
    (by linarith) (by linarith) (by linarith) (by linarith) (R₂ := 4 / 3) (by norm_num)
    (by linarith) (fun z hz => hζ z (by rwa [show 3 / 2 * r * (4 / 3) = 2 * r by ring] at hz))
    (r₁ := 2 / 3) (by norm_num) (by norm_num) (by linarith) (by linarith)
  rwa [show 3 / 2 * r * (2 / 3) = r by ring] at h

/-- Under RH, `ζ` has no zero on `ball c (2r)` for every half-scale disc. -/
theorem riemannZeta_ne_zero_on_ball_two_mul_of_riemannHypothesis (hRH : RiemannHypothesis)
    {c : ℂ} {r : ℝ} (hK : IsHalfScaleStripDisc c r) :
    ∀ z ∈ ball c (2 * r), riemannZeta z ≠ 0 := fun z hz =>
  riemannZeta_ne_zero_on_ball_of_riemannHypothesis hRH c z
    (ball_subset_ball (by linarith [hK.2.1]) hz)

/-- **RH gives fixed-base recurrence on every half-scale disc.** -/
theorem zetaDiscStronglyRecurrentOn_of_riemannHypothesis (hRH : RiemannHypothesis) {c : ℂ}
    {r : ℝ} (hK : IsHalfScaleStripDisc c r) : ZetaDiscStronglyRecurrentOn (closedBall c r) :=
  zetaDiscStronglyRecurrentOn_of_zeroFree_halfScale hK
    (riemannZeta_ne_zero_on_ball_two_mul_of_riemannHypothesis hRH hK)

/-- Every point of the right half-strip is the centre of a half-scale disc. -/
theorem exists_isHalfScaleStripDisc {z₀ : ℂ} (h1 : 1 / 2 < z₀.re) (h2 : z₀.re < 1) :
    ∃ r : ℝ, IsHalfScaleStripDisc z₀ r := by
  refine ⟨min ((z₀.re - 1 / 2) / 4) ((1 - z₀.re) / 4), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · linarith [min_le_left ((z₀.re - 1 / 2) / 4) ((1 - z₀.re) / 4)]
  · linarith [min_le_right ((z₀.re - 1 / 2) / 4) ((1 - z₀.re) / 4)]

/-- **Bagchi's criterion at half scale.**  The Riemann hypothesis holds if and only if `ζ` is
strongly recurrent on every closed disc whose doubled closure lies in the right half-strip. -/
theorem riemannHypothesis_iff_forall_halfScale_zetaDiscStronglyRecurrentOn :
    RiemannHypothesis ↔ ∀ (c : ℂ) (r : ℝ), IsHalfScaleStripDisc c r →
      ZetaDiscStronglyRecurrentOn (closedBall c r) := by
  constructor
  · intro hRH c r hK
    exact zetaDiscStronglyRecurrentOn_of_riemannHypothesis hRH hK
  · intro h
    rw [riemannHypothesis_iff_forall_exists_zetaDiscStronglyRecurrentOn]
    intro z₀ h1 h2
    obtain ⟨r, hK⟩ := exists_isHalfScaleStripDisc h1 h2
    exact ⟨r, hK.1, h z₀ r hK⟩

/-- **Bagchi's criterion at half scale, head-target form.**  The Riemann hypothesis holds if and
only if on every half-scale disc the head-target heights have uniformly positive lower density. -/
theorem riemannHypothesis_iff_forall_halfScale_headTargetUniformlyDense :
    RiemannHypothesis ↔ ∀ (c : ℂ) (r : ℝ), IsHalfScaleStripDisc c r →
      HeadTargetUniformlyDense (closedBall c r) := by
  rw [riemannHypothesis_iff_forall_halfScale_zetaDiscStronglyRecurrentOn]
  refine forall_congr' fun c => forall_congr' fun r => imp_congr_right fun hK => ?_
  exact zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense hK.1 hK.2.1 hK.2.2

end RHTower
