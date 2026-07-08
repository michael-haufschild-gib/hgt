/-
The annulus gluing criterion and the sweep-stable obstruction.

The two slit charts cover the open annulus, and their overlap is the disjoint
union of the upper and lower half-annuli — both preconnected, each containing one
basepoint.  On each overlap component two chart square roots differ by a constant
sign, read at the component's basepoint; the deck class is the ratio of the two
signs.  Hence: chart roots glue to a GLOBAL analytic square root on the annulus
exactly when the deck class is `1` — the class is the (mod 2) obstruction to a
global branch, the annulus incarnation of the argument principle's parity.

Combined with the tilt sweep: the transported roots `sweepRoot P t` are chart
roots of the swept member `A^t·f` with the SAME deck class, so a nontrivial class
obstructs a global square root at EVERY stage of the sweep simultaneously — the
parity obstruction is invariant under the whole prime-steering family, which is
what pins the weld's remaining step to branch selection rather than winding.
-/
import GaloisForLFunctions.RHTower.TiltSweepDiscriminator

noncomputable section

namespace RHTower

open Complex Metric Finset

/-! ### §1 The overlap components: the upper and lower half-annuli -/

/-- The upper half-annulus. -/
def overlapTop (a : ℂ) (r₀ R : ℝ) : Set ℂ :=
  {z | 0 < (z - a).im} ∩ (ball a R \ closedBall a r₀)

/-- The lower half-annulus. -/
def overlapBot (a : ℂ) (r₀ R : ℝ) : Set ℂ :=
  {z | (z - a).im < 0} ∩ (ball a R \ closedBall a r₀)

theorem isOpen_overlapTop (a : ℂ) (r₀ R : ℝ) : IsOpen (overlapTop a r₀ R) :=
  (isOpen_lt continuous_const (Complex.continuous_im.comp
    (continuous_id.sub continuous_const))).inter
    (isOpen_ball.sdiff isClosed_closedBall)

theorem isOpen_overlapBot (a : ℂ) (r₀ R : ℝ) : IsOpen (overlapBot a r₀ R) :=
  (isOpen_lt (Complex.continuous_im.comp
    (continuous_id.sub continuous_const)) continuous_const).inter
    (isOpen_ball.sdiff isClosed_closedBall)

/-- The upper half-annulus is a polar rectangle, hence preconnected. -/
theorem isPreconnected_overlapTop (a : ℂ) {r₀ R : ℝ} (h0 : 0 ≤ r₀) :
    IsPreconnected (overlapTop a r₀ R) := by
  have himg : overlapTop a r₀ R =
      polarMap a '' (Set.Ioo r₀ R ×ˢ Set.Ioo 0 Real.pi) := by
    ext z
    constructor
    · rintro ⟨him, hball, hout⟩
      have him' : 0 < (z - a).im := him
      have hz0 : z - a ≠ 0 := fun h => by
        rw [h] at him'
        simp at him'
      have hnorm_pos : (0 : ℝ) < ‖z - a‖ := norm_pos_iff.mpr hz0
      have hsin : 0 < Real.sin (z - a).arg := by
        rw [Complex.sin_arg]
        exact div_pos him' hnorm_pos
      refine ⟨(‖z - a‖, (z - a).arg), ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
      · simpa [Complex.dist_eq] using hout
      · simpa [mem_ball, Complex.dist_eq] using hball
      · by_contra hle
        push_cast at hle
        have h1 : (z - a).arg ≤ 0 := le_of_not_gt hle
        have h2 := Real.sin_nonpos_of_nonpos_of_neg_pi_le h1
          (le_of_lt (Complex.neg_pi_lt_arg _))
        linarith
      · rcases lt_or_eq_of_le (Complex.arg_le_pi (z - a)) with h | h
        · exact h
        · exfalso
          rw [h, Real.sin_pi] at hsin
          exact lt_irrefl 0 hsin
      · show a + (‖z - a‖ : ℂ) * exp (((z - a).arg : ℂ) * I) = z
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    · rintro ⟨⟨ρ, θ⟩, ⟨⟨hρ₁, hρ₂⟩, ⟨hθ₁, hθ₂⟩⟩, rfl⟩
      have hρpos : 0 < ρ := lt_of_le_of_lt h0 hρ₁
      have hnorm : ‖polarMap a (ρ, θ) - a‖ = ρ := norm_polarMap_sub hρpos
      refine ⟨?_, ?_, ?_⟩
      · show 0 < (polarMap a (ρ, θ) - a).im
        have hval : polarMap a (ρ, θ) - a = (ρ : ℂ) * exp ((θ : ℂ) * I) := by
          rw [polarMap]
          ring
        have him : ((ρ : ℂ) * exp ((θ : ℂ) * I)).im = ρ * Real.sin θ := by
          rw [Complex.mul_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im,
            Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
        rw [hval, him]
        exact mul_pos hρpos (Real.sin_pos_of_pos_of_lt_pi hθ₁ hθ₂)
      · rw [mem_ball, Complex.dist_eq, hnorm]
        exact hρ₂
      · rw [mem_closedBall, Complex.dist_eq, hnorm]
        simpa using hρ₁
  rw [himg]
  exact (((convex_Ioo r₀ R).prod (convex_Ioo 0 Real.pi)).isPreconnected).image
    _ (continuous_polarMap a).continuousOn

/-- The lower half-annulus is a polar rectangle, hence preconnected. -/
theorem isPreconnected_overlapBot (a : ℂ) {r₀ R : ℝ} (h0 : 0 ≤ r₀) :
    IsPreconnected (overlapBot a r₀ R) := by
  have himg : overlapBot a r₀ R =
      polarMap a '' (Set.Ioo r₀ R ×ˢ Set.Ioo (-Real.pi) 0) := by
    ext z
    constructor
    · rintro ⟨him, hball, hout⟩
      have him' : (z - a).im < 0 := him
      have hz0 : z - a ≠ 0 := fun h => by
        rw [h] at him'
        simp at him'
      have hnorm_pos : (0 : ℝ) < ‖z - a‖ := norm_pos_iff.mpr hz0
      have hsin : Real.sin (z - a).arg < 0 := by
        rw [Complex.sin_arg]
        exact div_neg_of_neg_of_pos him' hnorm_pos
      refine ⟨(‖z - a‖, (z - a).arg), ⟨⟨?_, ?_⟩, ⟨Complex.neg_pi_lt_arg _, ?_⟩⟩, ?_⟩
      · simpa [Complex.dist_eq] using hout
      · simpa [mem_ball, Complex.dist_eq] using hball
      · by_contra hle
        push_cast at hle
        have h1 : 0 ≤ (z - a).arg := le_of_not_gt hle
        have h2 := Real.sin_nonneg_of_nonneg_of_le_pi h1 (Complex.arg_le_pi _)
        linarith
      · show a + (‖z - a‖ : ℂ) * exp (((z - a).arg : ℂ) * I) = z
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    · rintro ⟨⟨ρ, θ⟩, ⟨⟨hρ₁, hρ₂⟩, ⟨hθ₁, hθ₂⟩⟩, rfl⟩
      have hρpos : 0 < ρ := lt_of_le_of_lt h0 hρ₁
      have hnorm : ‖polarMap a (ρ, θ) - a‖ = ρ := norm_polarMap_sub hρpos
      refine ⟨?_, ?_, ?_⟩
      · show (polarMap a (ρ, θ) - a).im < 0
        have hval : polarMap a (ρ, θ) - a = (ρ : ℂ) * exp ((θ : ℂ) * I) := by
          rw [polarMap]
          ring
        have him : ((ρ : ℂ) * exp ((θ : ℂ) * I)).im = ρ * Real.sin θ := by
          rw [Complex.mul_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im,
            Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
        rw [hval, him]
        have hsin : Real.sin θ < 0 := by
          have h := Real.sin_pos_of_pos_of_lt_pi (x := -θ) (by linarith) (by linarith)
          rw [Real.sin_neg] at h
          linarith
        exact mul_neg_of_pos_of_neg hρpos hsin
      · rw [mem_ball, Complex.dist_eq, hnorm]
        exact hρ₂
      · rw [mem_closedBall, Complex.dist_eq, hnorm]
        simpa using hρ₁
  rw [himg]
  exact (((convex_Ioo r₀ R).prod (convex_Ioo (-Real.pi) 0)).isPreconnected).image
    _ (continuous_polarMap a).continuousOn

theorem overlapTop_subset_chartRA (a : ℂ) (r₀ R : ℝ) :
    overlapTop a r₀ R ⊆ chartRA a r₀ R := fun _ hz =>
  ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz.1)), hz.2⟩

theorem overlapTop_subset_chartLA (a : ℂ) (r₀ R : ℝ) :
    overlapTop a r₀ R ⊆ chartLA a r₀ R := fun z hz =>
  ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by
    have h : (a - z).im = -((z - a).im) := by
      simp [Complex.sub_im]
    rw [h]
    exact neg_ne_zero.mpr (ne_of_gt hz.1))), hz.2⟩

theorem overlapBot_subset_chartRA (a : ℂ) (r₀ R : ℝ) :
    overlapBot a r₀ R ⊆ chartRA a r₀ R := fun _ hz =>
  ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_lt hz.1)), hz.2⟩

theorem overlapBot_subset_chartLA (a : ℂ) (r₀ R : ℝ) :
    overlapBot a r₀ R ⊆ chartLA a r₀ R := fun z hz =>
  ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by
    have h : (a - z).im = -((z - a).im) := by
      simp [Complex.sub_im]
    rw [h]
    exact neg_ne_zero.mpr (ne_of_lt hz.1))), hz.2⟩

/-- The chart overlap is exactly the two half-annuli. -/
theorem chart_inter_subset_overlaps (a : ℂ) (r₀ R : ℝ) :
    chartRA a r₀ R ∩ chartLA a r₀ R ⊆ overlapTop a r₀ R ∪ overlapBot a r₀ R := by
  rintro z ⟨⟨hslitR, hann⟩, ⟨hslitL, -⟩⟩
  have him : (z - a).im ≠ 0 := by
    intro h0
    rcases Complex.mem_slitPlane_iff.mp hslitR with hre | him'
    · rcases Complex.mem_slitPlane_iff.mp hslitL with hre' | him''
      · have h : (a - z).re = -((z - a).re) := by
          simp [Complex.sub_re]
        rw [h] at hre'
        linarith
      · have h : (a - z).im = -((z - a).im) := by
          simp [Complex.sub_im]
        rw [h, h0] at him''
        simp at him''
    · exact him' h0
  rcases lt_or_gt_of_ne him with h | h
  · exact Or.inr ⟨h, hann⟩
  · exact Or.inl ⟨h, hann⟩

/-- The two slit charts cover the annulus. -/
theorem annulus_subset_charts_union {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) :
    ball a R \ closedBall a r₀ ⊆ chartRA a r₀ R ∪ chartLA a r₀ R :=
  annulus_subset_charts h0

/-- The basepoints sit in the two overlap components. -/
theorem basepoints_mem_overlaps {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R) :
    a + (((r₀ + R) / 2 : ℝ) : ℂ) * I ∈ overlapTop a r₀ R ∧
    a - (((r₀ + R) / 2 : ℝ) : ℂ) * I ∈ overlapBot a r₀ R := by
  obtain ⟨hP, hM⟩ := annulus_basepoints_mem h0 hrR
  have hc : 0 < (r₀ + R) / 2 := by linarith
  constructor
  · refine ⟨?_, hP.1.2⟩
    show 0 < (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I - a).im
    simp [Complex.add_im, Complex.mul_im]
    linarith
  · refine ⟨?_, hM.1.2⟩
    show (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I - a).im < 0
    simp [Complex.mul_im]
    linarith

/-! ### §2 The gluing criterion -/

/-- **Trivial deck class glues**: chart square roots with deck class `1` assemble
into a global analytic square root on the annulus — the sign read at the top
basepoint corrects the left chart coherently across BOTH overlap components. -/
theorem exists_global_sqrt_of_deckClass_one {f G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 = f z)
    (hfP : f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hfM : f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hdeck : deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = 1) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball a R \ closedBall a r₀) ∧
      ∀ z ∈ ball a R \ closedBall a r₀, F z ^ 2 = f z := by
  classical
  obtain ⟨hpPT, hpMB⟩ := basepoints_mem_overlaps h0 hrR
  obtain ⟨hεsq, hEqT⟩ := pow_root_ratio (by norm_num : (0 : ℕ) < 2)
    (isOpen_overlapTop a r₀ R) (isPreconnected_overlapTop a h0)
    (fun z hz => hG₁ z (overlapTop_subset_chartRA a r₀ R hz))
    (fun z hz => hG₂ z (overlapTop_subset_chartLA a r₀ R hz))
    (fun z hz => hpG₁ z (overlapTop_subset_chartRA a r₀ R hz))
    (fun z hz => hpG₂ z (overlapTop_subset_chartLA a r₀ R hz))
    hpPT hfP
  obtain ⟨hδsq, hEqB⟩ := pow_root_ratio (by norm_num : (0 : ℕ) < 2)
    (isOpen_overlapBot a r₀ R) (isPreconnected_overlapBot a h0)
    (fun z hz => hG₁ z (overlapBot_subset_chartRA a r₀ R hz))
    (fun z hz => hG₂ z (overlapBot_subset_chartLA a r₀ R hz))
    (fun z hz => hpG₁ z (overlapBot_subset_chartRA a r₀ R hz))
    (fun z hz => hpG₂ z (overlapBot_subset_chartLA a r₀ R hz))
    hpMB hfM
  set ε : ℂ := G₁ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
    / G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) with hεdef
  set δ : ℂ := G₁ (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
    / G₂ (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) with hδdef
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [h] at hδsq
    norm_num at hδsq
  have hεδ : ε = δ := (div_eq_one_iff_eq hδ0).mp hdeck
  have hEqOverlap : ∀ z ∈ chartRA a r₀ R ∩ chartLA a r₀ R, G₁ z = ε * G₂ z := by
    intro z hz
    rcases chart_inter_subset_overlaps a r₀ R hz with h | h
    · exact hEqT h
    · rw [hεδ]
      exact hEqB h
  refine ⟨fun z => if z ∈ chartRA a r₀ R then G₁ z else ε * G₂ z, ?_, ?_⟩
  · intro z hz
    by_cases hzRA : z ∈ chartRA a r₀ R
    · exact (hG₁ z hzRA).congr
        (Filter.eventuallyEq_of_mem ((isOpen_chartRA a r₀ R).mem_nhds hzRA)
          fun w hw => (if_pos hw).symm)
    · have hzLA : z ∈ chartLA a r₀ R := by
        rcases annulus_subset_charts_union h0 hz with h | h
        · exact absurd h hzRA
        · exact h
      refine AnalyticAt.congr (f := fun w => ε * G₂ w)
        (analyticAt_const.mul (hG₂ z hzLA))
        (Filter.eventuallyEq_of_mem ((isOpen_chartLA a r₀ R).mem_nhds hzLA)
          fun w hw => ?_)
      by_cases hwRA : w ∈ chartRA a r₀ R
      · rw [if_pos hwRA]
        exact (hEqOverlap w ⟨hwRA, hw⟩).symm
      · rw [if_neg hwRA]
  · intro z hz
    show (if z ∈ chartRA a r₀ R then G₁ z else ε * G₂ z) ^ 2 = f z
    by_cases hzRA : z ∈ chartRA a r₀ R
    · rw [if_pos hzRA]
      exact hpG₁ z hzRA
    · have hzLA : z ∈ chartLA a r₀ R := by
        rcases annulus_subset_charts_union h0 hz with h | h
        · exact absurd h hzRA
        · exact h
      rw [if_neg hzRA, mul_pow, hεsq, one_mul]
      exact hpG₂ z hzLA

/-- **A global square root trivializes the deck class**: both chart roots are
constant-sign multiples of the restriction, and the constants cancel in the
double ratio. -/
theorem deckClass_eq_one_of_global_sqrt {f G₁ G₂ F : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 = f z)
    (hF : AnalyticOnNhd ℂ F (ball a R \ closedBall a r₀))
    (hpF : ∀ z ∈ ball a R \ closedBall a r₀, F z ^ 2 = f z)
    (hfP : f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hfM : f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0) :
    deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = 1 := by
  obtain ⟨hPmem, hMmem⟩ := annulus_basepoints_mem h0 hrR
  have hR : 0 < R := lt_of_le_of_lt h0 hrR
  obtain ⟨hc₁sq, hEq₁⟩ := pow_root_ratio (by norm_num : (0 : ℕ) < 2)
    (isOpen_chartRA a r₀ R) (isPreconnected_chartRA a h0)
    hG₁ (fun z hz => hF z hz.2) hpG₁ (fun z hz => hpF z hz.2) hPmem.1 hfP
  obtain ⟨hc₂sq, hEq₂⟩ := pow_root_ratio (by norm_num : (0 : ℕ) < 2)
    (isOpen_chartLA a r₀ R) (isPreconnected_chartLA a h0)
    hG₂ (fun z hz => hF z hz.2) hpG₂ (fun z hz => hpF z hz.2) hPmem.2 hfP
  have hFP : F (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h
    have := hpF _ hPmem.1.2
    rw [h] at this
    exact hfP (by rw [← this]; ring)
  have hFM : F (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h
    have := hpF _ hMmem.1.2
    rw [h] at this
    exact hfM (by rw [← this]; ring)
  have hc₁0 : G₁ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      / F (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h
    rw [h] at hc₁sq
    norm_num at hc₁sq
  have hc₂0 : G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      / F (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h
    rw [h] at hc₂sq
    norm_num at hc₂sq
  set c₁ : ℂ := G₁ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
    / F (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) with hc₁def
  set c₂ : ℂ := G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
    / F (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) with hc₂def
  have e1P : G₁ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      = c₁ * F (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) := hEq₁ hPmem.1
  have e2P : G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      = c₂ * F (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) := hEq₂ hPmem.2
  have e1M : G₁ (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      = c₁ * F (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) := hEq₁ hMmem.1
  have e2M : G₂ (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      = c₂ * F (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) := hEq₂ hMmem.2
  rw [deckClass, e1P, e2P, e1M, e2M, mul_div_mul_comm, mul_div_mul_comm,
    div_self hFP, div_self hFM, mul_one, div_self (div_ne_zero hc₁0 hc₂0)]

/-! ### §3 The sweep-stable obstruction -/

/-- **The parity obstruction survives the whole sweep**: if the member's chart
roots have nontrivial deck class, then NO stage of the anchor sweep admits a
global square root on the annulus.  The transported roots are chart roots of the
swept member with the member's own class, so the gluing criterion fails
uniformly in `t` — the steering family cannot open the two-sheeted cover. -/
theorem no_global_sqrt_along_sweep_of_deckClass_ne_one {P : Finset ℕ}
    (hP : ∀ p ∈ P, 2 ≤ p) {f G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hre : ∀ z ∈ ball a R \ closedBall a r₀, 0 < z.re)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 = f z)
    (hfP : f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hfM : f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hdeck : deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 1) (t : ℝ) :
    ¬∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball a R \ closedBall a r₀) ∧
      ∀ z ∈ ball a R \ closedBall a r₀,
        F z ^ 2 = anchorSweep P t z * f z := by
  rintro ⟨F, hFan, hpF⟩
  have h1 := deckClass_eq_one_of_global_sqrt (f := fun z => anchorSweep P t z * f z)
    h0 hrR
    (sweepRoot_analyticOnNhd hP t hG₁ (fun z hz => hre z hz.2))
    (sweepRoot_analyticOnNhd hP t hG₂ (fun z hz => hre z hz.2))
    (sweepRoot_sq hpG₁ P t) (sweepRoot_sq hpG₂ P t)
    hFan hpF
    (mul_ne_zero (anchorSweep_ne_zero P t _) hfP)
    (mul_ne_zero (anchorSweep_ne_zero P t _) hfM)
  rw [deckClass_sweepRoot] at h1
  exact hdeck h1

end RHTower
