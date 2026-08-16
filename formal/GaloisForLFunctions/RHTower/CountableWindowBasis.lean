import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# A countable rational-window basis detects off-seam divisor mass

For a discrete divisor the off-seam width functional `D₂(R) = ∑_{ρ ∈ R} m_ρ (Re ρ - ½)²` vanishes on
every window exactly when it vanishes on the countable family of windows with rational corners
whose boundary avoids the divisor.  The only content is that a discrete set can be isolated by
rational windows: around each point choose a ball meeting the set only there, and a rational
rectangle inside that ball.  Its closure stays inside the ball, so the boundary carries no divisor
point.

With strictly positive multiplicities the rational-window condition forces every divisor point onto
the critical line.
-/

noncomputable section

namespace RHTower

open Complex

/-- The open window with rational corners. -/
def ratRectangle (a b c d : ℚ) : Set ℂ :=
  {z : ℂ | (a : ℝ) < z.re ∧ z.re < (b : ℝ) ∧ (c : ℝ) < z.im ∧ z.im < (d : ℝ)}

theorem isOpen_ratRectangle (a b c d : ℚ) : IsOpen (ratRectangle a b c d) := by
  have h1 : IsOpen {z : ℂ | (a : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | z.re < (b : ℝ)} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {z : ℂ | (c : ℝ) < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have h4 : IsOpen {z : ℂ | z.im < (d : ℝ)} := isOpen_lt Complex.continuous_im continuous_const
  have : ratRectangle a b c d =
      {z : ℂ | (a : ℝ) < z.re} ∩ {z : ℂ | z.re < (b : ℝ)} ∩
        ({z : ℂ | (c : ℝ) < z.im} ∩ {z : ℂ | z.im < (d : ℝ)}) := by
    ext z
    simp [ratRectangle, and_assoc]
  rw [this]
  exact ((h1.inter h2).inter (h3.inter h4))

/-- Every point has arbitrarily small rational windows around it. -/
theorem exists_ratRectangle_subset_ball (ρ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b c d : ℚ, ρ ∈ ratRectangle a b c d ∧
      ratRectangle a b c d ⊆ Metric.ball ρ ε := by
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show ρ.re - ε / 4 < ρ.re by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show ρ.re < ρ.re + ε / 4 by linarith)
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show ρ.im - ε / 4 < ρ.im by linarith)
  obtain ⟨d, hd1, hd2⟩ := exists_rat_btwn (show ρ.im < ρ.im + ε / 4 by linarith)
  refine ⟨a, b, c, d, ⟨ha2, hb1, hc2, hd1⟩, fun z hz => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hre : |z.re - ρ.re| < ε / 2 := by
    rw [abs_lt]
    constructor <;> linarith
  have him : |z.im - ρ.im| < ε / 2 := by
    rw [abs_lt]
    constructor <;> linarith
  have hdist : dist z ρ ≤ |z.re - ρ.re| + |z.im - ρ.im| := by
    rw [Complex.dist_eq]
    simpa [Complex.sub_re, Complex.sub_im] using Complex.norm_le_abs_re_add_abs_im (z - ρ)
  rw [Metric.mem_ball]
  linarith

/-- **Isolating rational window.**  Around every point of a discrete set there is a rational
window whose closure meets the set only in that point; in particular its boundary avoids the
set. -/
theorem exists_isolating_ratRectangle {S : Set ℂ}
    (hdisc : ∀ z ∈ S, ∃ ε > 0, ∀ w ∈ S, dist w z < ε → w = z) {ρ : ℂ} (hρ : ρ ∈ S) :
    ∃ a b c d : ℚ, ρ ∈ ratRectangle a b c d ∧
      S ∩ closure (ratRectangle a b c d) ⊆ {ρ} ∧
      S ∩ frontier (ratRectangle a b c d) = ∅ := by
  obtain ⟨ε, hε, hiso⟩ := hdisc ρ hρ
  obtain ⟨a, b, c, d, hmem, hsub⟩ := exists_ratRectangle_subset_ball ρ (half_pos hε)
  have hclos : closure (ratRectangle a b c d) ⊆ Metric.ball ρ ε := by
    refine le_trans (closure_mono hsub) ?_
    refine le_trans Metric.closure_ball_subset_closedBall ?_
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    linarith
  have hsingle : S ∩ closure (ratRectangle a b c d) ⊆ {ρ} := by
    rintro w ⟨hwS, hwc⟩
    exact hiso w hwS (by simpa [Metric.mem_ball] using hclos hwc)
  refine ⟨a, b, c, d, hmem, hsingle, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro w ⟨hwS, hwf⟩
  have hwc : w ∈ closure (ratRectangle a b c d) := hwf.1
  have hwρ : w = ρ := hsingle ⟨hwS, hwc⟩
  subst hwρ
  have hint : w ∈ interior (ratRectangle a b c d) := by
    rw [(isOpen_ratRectangle a b c d).interior_eq]
    exact hmem
  exact hwf.2 hint

/-- The off-seam width mass of a finite family of divisor atoms. -/
def offSeamMass (m : ℂ → ℝ) (F : Finset ℂ) : ℝ :=
  ∑ ρ ∈ F, m ρ * (ρ.re - 1 / 2) ^ 2

theorem offSeamMass_eq_zero_iff {m : ℂ → ℝ} {F : Finset ℂ} (hm : ∀ ρ ∈ F, 0 ≤ m ρ) :
    offSeamMass m F = 0 ↔ ∀ ρ ∈ F, m ρ * (ρ.re - 1 / 2) ^ 2 = 0 := by
  rw [offSeamMass, Finset.sum_eq_zero_iff_of_nonneg]
  intro ρ hρ
  exact mul_nonneg (hm ρ hρ) (sq_nonneg _)

/-- **The countable window basis.**  For a discrete divisor, vanishing of the off-seam width on
every window is equivalent to its vanishing on the countable family of rational windows whose
boundary avoids the divisor. -/
theorem offSeam_vanishes_iff_ratRectangles {S : Set ℂ} {m : ℂ → ℝ}
    (hdisc : ∀ z ∈ S, ∃ ε > 0, ∀ w ∈ S, dist w z < ε → w = z) :
    (∀ ρ ∈ S, m ρ * (ρ.re - 1 / 2) ^ 2 = 0) ↔
      ∀ a b c d : ℚ, S ∩ frontier (ratRectangle a b c d) = ∅ →
        ∀ ρ ∈ S ∩ ratRectangle a b c d, m ρ * (ρ.re - 1 / 2) ^ 2 = 0 := by
  constructor
  · intro h a b c d _ ρ hρ
    exact h ρ hρ.1
  · intro h ρ hρ
    obtain ⟨a, b, c, d, hmem, -, hfront⟩ := exists_isolating_ratRectangle hdisc hρ
    exact h a b c d hfront ρ ⟨hρ, hmem⟩

/-- **No off-seam zero survives.**  With strictly positive multiplicities, vanishing on the
rational window basis forces every divisor point onto the critical line. -/
theorem re_eq_half_of_ratRectangles {S : Set ℂ} {m : ℂ → ℝ}
    (hdisc : ∀ z ∈ S, ∃ ε > 0, ∀ w ∈ S, dist w z < ε → w = z)
    (hm : ∀ ρ ∈ S, 0 < m ρ)
    (h : ∀ a b c d : ℚ, S ∩ frontier (ratRectangle a b c d) = ∅ →
      ∀ ρ ∈ S ∩ ratRectangle a b c d, m ρ * (ρ.re - 1 / 2) ^ 2 = 0) :
    ∀ ρ ∈ S, ρ.re = 1 / 2 := by
  intro ρ hρ
  have hzero := (offSeam_vanishes_iff_ratRectangles hdisc).mpr h ρ hρ
  have hmpos := hm ρ hρ
  have hsq : (ρ.re - 1 / 2) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hzero with hc | hc
    · exact absurd hc (ne_of_gt hmpos)
    · exact hc
  have : ρ.re - 1 / 2 = 0 := by
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  linarith

end RHTower
