import GaloisForLFunctions.RHTower.DiscWindow

/-!
# The DISC extraction: the family of line-predicted classes decides the rung

`LineHolography k` is the statement that EVERY reflection-closed enclosed ξ-presentation with
true-order multiplicities has level-`2^{k+1}` deck class equal to its line-predicted class
`exp(2πi·L/2^{k+1})`.  The forward direction is the per-presentation DISC reading.  The
extraction direction recovers the per-zero rung from the family: around a hypothetical
right-half zero, a generic line center is chosen so that no other off-line zero lies at the pair
distance (the bad heights form a finite set, one per zero), and two nested presentations through
that center — one just inside the pair circle, one just outside — have right-half order sums
differing by exactly the zero's own order, so the two divisibilities subtract to the rung datum.
Hence `RHLadder k ⟺ LineHolography k`, and RH is the totality of the line holographies: the
line-predicted class is the second boundary functional that, jointly with the loop class,
decides the ladder — per zero, not merely per window sum.
-/

namespace RHTower

open Complex Set Metric

/-- The critical-line center at height `y`. -/
noncomputable def lineCtr (y : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I

theorem lineCtr_re (y : ℝ) : (lineCtr y).re = 1 / 2 := by simp [lineCtr]

theorem lineCtr_im (y : ℝ) : (lineCtr y).im = y := by simp [lineCtr]

/-- Squared distance to a line center, in coordinates. -/
theorem dist_lineCtr_sq (v : ℂ) (y : ℝ) :
    dist v (lineCtr y) ^ 2 = (v.re - 1 / 2) ^ 2 + (v.im - y) ^ 2 := by
  rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    lineCtr_re, lineCtr_im]
  ring

/-- **Generic line centers separate the pair distance.**  For an off-line point `ρ` and any
finite set `Z`, all but finitely many heights `y` give a line center from which no member of `Z`
other than `ρ` and its mirror lies at the distance of `ρ`: for fixed `w` the bad heights solve a
linear equation, degenerate only for the mirror pair. -/
theorem exists_good_line_center {ρ : ℂ} (Z : Finset ℂ) :
    ∃ y : ℝ, ρ.im - 1 < y ∧ y < ρ.im + 1 ∧
      ∀ w ∈ Z, w ≠ ρ → w ≠ lineReflect ρ →
        dist w (lineCtr y) ≠ dist ρ (lineCtr y) := by
  classical
  set Bad : Set ℝ :=
    ⋃ w ∈ Z, {y : ℝ | w ≠ ρ ∧ w ≠ lineReflect ρ ∧ dist w (lineCtr y) = dist ρ (lineCtr y)}
    with hBad
  have hfin : Bad.Finite := by
    refine Set.Finite.biUnion Z.finite_toSet ?_
    intro w _
    by_cases hqual : w ≠ ρ ∧ w ≠ lineReflect ρ
    · apply Set.Subsingleton.finite
      intro y₁ hy₁ y₂ hy₂
      obtain ⟨-, -, he₁⟩ := hy₁
      obtain ⟨-, -, he₂⟩ := hy₂
      have hsq₁ : (w.re - 1 / 2) ^ 2 + (w.im - y₁) ^ 2
          = (ρ.re - 1 / 2) ^ 2 + (ρ.im - y₁) ^ 2 := by
        have h2 : dist w (lineCtr y₁) ^ 2 = dist ρ (lineCtr y₁) ^ 2 := by rw [he₁]
        rw [dist_lineCtr_sq, dist_lineCtr_sq] at h2
        exact h2
      have hsq₂ : (w.re - 1 / 2) ^ 2 + (w.im - y₂) ^ 2
          = (ρ.re - 1 / 2) ^ 2 + (ρ.im - y₂) ^ 2 := by
        have h2 : dist w (lineCtr y₂) ^ 2 = dist ρ (lineCtr y₂) ^ 2 := by rw [he₂]
        rw [dist_lineCtr_sq, dist_lineCtr_sq] at h2
        exact h2
      rcases eq_or_ne w.im ρ.im with him | him
      · exfalso
        rw [him] at hsq₁
        have hfac : (w.re - ρ.re) * (w.re + ρ.re - 1) = 0 := by nlinarith [hsq₁]
        rcases mul_eq_zero.mp hfac with h | h
        · exact hqual.1 (Complex.ext (by linarith) him)
        · refine hqual.2 (Complex.ext ?_ ?_)
          · rw [lineReflect_re]
            linarith
          · rw [show (lineReflect ρ).im = ρ.im from by simp [lineReflect]]
            exact him
      · have hkey : (y₁ - y₂) * (w.im - ρ.im) = 0 := by nlinarith [hsq₁, hsq₂]
        rcases mul_eq_zero.mp hkey with h | h
        · linarith
        · exact absurd (by linarith : w.im = ρ.im) him
    · convert Set.finite_empty
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hqual
  have hIoo : (Set.Ioo (ρ.im - 1) (ρ.im + 1)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨y, hyIoo, hyBad⟩ := (hIoo.sdiff hfin).nonempty
  refine ⟨y, hyIoo.1, hyIoo.2, ?_⟩
  intro w hwZ hw1 hw2 heq
  exact hyBad (Set.mem_biUnion hwZ ⟨hw1, hw2, heq⟩)

private theorem lineReflect_zero_ball {c : ℂ} (hc : c.re = 1 / 2) {r : ℝ} {w : ℂ}
    (hw : w ∈ ball c r) (hw0 : xi w = 0) :
    lineReflect w ∈ ball c r ∧ xi (lineReflect w) = 0 := by
  constructor
  · rw [mem_ball, dist_lineReflect_center hc]
    exact mem_ball.mp hw
  · simp only [lineReflect]
    rw [xi_one_sub, xi_conj, hw0, map_zero]

/-- **Line holography at level `k`**: every reflection-closed enclosed ξ-presentation with
true-order multiplicities has level-`2^{k+1}` deck class equal to its line-predicted class. -/
def LineHolography (k : ℕ) : Prop :=
  ∀ (t : Finset ℂ) (m : ℂ → ℕ) (h G₁ G₂ : ℂ → ℂ) (a : ℂ) (r₀ R : ℝ),
    0 ≤ r₀ → r₀ < R →
    (∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt xi z) →
    (∀ z ∈ t, lineReflect z ∈ t) →
    (∀ z ∈ t, ‖z - a‖ ≤ r₀) →
    AnalyticOnNhd ℂ h (ball a R) → (∀ z ∈ ball a R, h z ≠ 0) →
    (∀ z ∈ ball a R, xi z = (∏ w ∈ t, (z - w) ^ m w) * h z) →
    AnalyticOnNhd ℂ G₁ (chartRA a r₀ R) → AnalyticOnNhd ℂ G₂ (chartLA a r₀ R) →
    (∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 ^ (k + 1) = xi z) →
    (∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 ^ (k + 1) = xi z) →
    deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      = Complex.exp (2 * (Real.pi : ℂ) * I *
          ((∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z : ℕ) : ℂ)
          / ((2 ^ (k + 1) : ℕ) : ℂ))

/-- Rung ⟹ holography: the per-presentation DISC reading, with the certificate data supplied by
the ladder at every right-half element (non-zeros contribute zero multiplicity). -/
theorem lineHolography_of_rhLadder {k : ℕ} (hlad : RHLadder k) : LineHolography k := by
  intro t m h G₁ G₂ a r₀ R h0 hrR hm hclosed hρ hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂
  rw [xi_deckClass_eq_line_iff_right_dvd h0 hrR hm hclosed hρ hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂]
  refine Finset.dvd_sum ?_
  intro z hz
  rw [Finset.mem_filter] at hz
  by_cases hz0 : xi z = 0
  · have hdvd := hlad z (mem_rightHalf.mpr hz.2) hz0
    rw [← hm z hz.1] at hdvd
    exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd
  · have hord0 : analyticOrderAt xi z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hz0)
    have hm0 : m z = 0 := by
      have hz1 := hm z hz.1
      rw [hord0] at hz1
      exact_mod_cast hz1
    rw [hm0]
    exact dvd_zero _

/-- **The first line-holography interface is unconditional.**  Level zero asks only divisibility by
`1`; the unconditional base rung therefore supplies every reflection-closed presentation with its
level-two deck/line identity. -/
theorem lineHolography_zero : LineHolography 0 :=
  lineHolography_of_rhLadder rhLadder_zero

/-- **Holography ⟹ rung (the extraction).**  Around a hypothetical right-half zero, pick a
generic line center whose pair circle carries no other off-line zero; the two nested
presentations through that center — just inside and just outside the pair circle — have
right-half order sums differing by exactly the zero's order, so the two line-holography
divisibilities subtract to the zero's own rung datum. -/
theorem rhLadder_of_lineHolography {k : ℕ} (H : LineHolography k) : RHLadder k := by
  classical
  intro ρ hρmem hρzero
  have hρre : 1 / 2 < ρ.re := mem_rightHalf.mp hρmem
  set d : ℝ := ρ.re - 1 / 2 with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  set m : ℂ → ℕ := fun z => (analyticOrderAt xi z).toNat with hm_def
  -- reference zero set (center-independent) and a good line center
  have hZfin := xi_zeros_finite_ball ρ (2 * d + 3)
  obtain ⟨y, hy1, hy2, hgood⟩ := exists_good_line_center (ρ := ρ) hZfin.toFinset
  set c : ℂ := lineCtr y with hc_def
  have hc_re : c.re = 1 / 2 := by rw [hc_def]; exact lineCtr_re y
  set D₀ : ℝ := dist ρ c with hD₀_def
  have hD₀_ge : d ≤ D₀ := by
    rw [hD₀_def, Complex.dist_eq]
    calc d = |(ρ - c).re| := by
          rw [Complex.sub_re, hc_re, ← hd_def, abs_of_pos hd]
      _ ≤ ‖ρ - c‖ := Complex.abs_re_le_norm _
  have hD₀_pos : 0 < D₀ := lt_of_lt_of_le hd hD₀_ge
  have hsqD₀ : D₀ ^ 2 = d ^ 2 + (ρ.im - y) ^ 2 := by
    rw [hD₀_def, hc_def, dist_lineCtr_sq, hd_def]
  have hD₀_lt : D₀ < d + 1 := by
    by_contra hge
    have hge' : d + 1 ≤ D₀ := not_lt.mp hge
    have h1 : (d + 1) ^ 2 ≤ D₀ ^ 2 := by nlinarith
    have him : (ρ.im - y) ^ 2 < 1 := by nlinarith
    nlinarith
  -- every zero near the center is in the reference set
  have href : ∀ z : ℂ, dist z c < D₀ + 1 → xi z = 0 → z ∈ hZfin.toFinset := by
    intro z hz hz0
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, hz0⟩
    rw [mem_ball]
    have hcρ : dist c ρ = D₀ := by rw [dist_comm, ← hD₀_def]
    calc dist z ρ ≤ dist z c + dist c ρ := dist_triangle z c ρ
      _ = dist z c + D₀ := by rw [hcρ]
      _ < 2 * d + 3 := by nlinarith
  set Dists : Finset ℝ := hZfin.toFinset.image (fun w => dist w c) with hDists
  -- outer radius: just above the pair circle, below the next zero distance
  set S₂ : Finset ℝ := Dists.filter (fun r => D₀ < r) with hS₂
  set R₂ : ℝ := if hS : S₂.Nonempty then min ((D₀ + S₂.min' hS) / 2) (D₀ + 1 / 2)
    else D₀ + 1 / 2 with hR₂
  have hS₂prop : ∀ r ∈ S₂, D₀ < r := by
    intro r hr
    rw [hS₂] at hr
    exact (Finset.mem_filter.mp hr).2
  have hR₂_gt : D₀ < R₂ := by
    rw [hR₂]
    split_ifs with hS
    · exact lt_min (by linarith [hS₂prop _ (S₂.min'_mem hS)]) (by linarith)
    · linarith
  have hR₂_le : R₂ ≤ D₀ + 1 / 2 := by
    rw [hR₂]
    split_ifs with hS
    · exact min_le_right _ _
    · exact le_refl _
  have hmemS₂ : ∀ z : ℂ, z ∈ hZfin.toFinset → D₀ < dist z c → dist z c ∈ S₂ := by
    intro z hzin hgt
    rw [hS₂, hDists]
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hzin, hgt⟩
  have hshell₂ : ∀ z : ℂ, xi z = 0 → dist z c < R₂ → dist z c ≤ D₀ := by
    intro z hz0 hzR
    by_contra hgt
    have hgt' : D₀ < dist z c := not_le.mp hgt
    have hzin : z ∈ hZfin.toFinset := href z (by linarith) hz0
    have hmem := hmemS₂ z hzin hgt'
    have hS : S₂.Nonempty := ⟨_, hmem⟩
    have hmin := S₂.min'_le _ hmem
    rw [hR₂, dif_pos hS] at hzR
    have h1 : dist z c < (D₀ + S₂.min' hS) / 2 := lt_of_lt_of_le hzR (min_le_left _ _)
    linarith [hS₂prop _ (S₂.min'_mem hS)]
  -- inner radius: just below the pair circle, above every closer zero distance
  set S₁ : Finset ℝ := Dists.filter (fun r => r < D₀) with hS₁
  set rmax : ℝ := if hS : S₁.Nonempty then max (S₁.max' hS) 0 else 0 with hrmax
  have hS₁prop : ∀ r ∈ S₁, r < D₀ := by
    intro r hr
    rw [hS₁] at hr
    exact (Finset.mem_filter.mp hr).2
  have hrmax_nonneg : 0 ≤ rmax := by
    rw [hrmax]
    split_ifs with hS
    · exact le_max_right _ _
    · exact le_refl 0
  have hrmax_lt : rmax < D₀ := by
    rw [hrmax]
    split_ifs with hS
    · exact max_lt (hS₁prop _ (S₁.max'_mem hS)) hD₀_pos
    · exact hD₀_pos
  have hmemS₁ : ∀ z : ℂ, z ∈ hZfin.toFinset → dist z c < D₀ → dist z c ∈ S₁ := by
    intro z hzin hlt
    rw [hS₁, hDists]
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hzin, hlt⟩
  have hle_rmax : ∀ r ∈ S₁, r ≤ rmax := by
    intro r hr
    have hS : S₁.Nonempty := ⟨_, hr⟩
    calc r ≤ S₁.max' hS := S₁.le_max' _ hr
      _ ≤ rmax := by rw [hrmax, dif_pos hS]; exact le_max_left _ _
  set R₁ : ℝ := (rmax + D₀) / 2 with hR₁
  have hR₁_gt : rmax < R₁ := by rw [hR₁]; linarith
  have hR₁_lt : R₁ < D₀ := by rw [hR₁]; linarith
  have hR₁_pos : 0 < R₁ := by rw [hR₁]; linarith
  set r₁ : ℝ := (rmax + R₁) / 2 with hr₁
  have hr₁_pos : 0 < r₁ := by rw [hr₁]; linarith
  have hr₁_gt : rmax ≤ r₁ := by rw [hr₁]; linarith
  have hr₁_lt : r₁ < R₁ := by rw [hr₁]; linarith
  have hshell₁ : ∀ z : ℂ, xi z = 0 → dist z c < R₁ → dist z c ≤ rmax := by
    intro z hz0 hzR
    have hzin : z ∈ hZfin.toFinset := href z (by linarith) hz0
    exact hle_rmax _ (hmemS₁ z hzin (by linarith))
  -- the two presentations
  have hfin₂ := xi_zeros_finite_ball c R₂
  have hfin₁ := xi_zeros_finite_ball c R₁
  set t₂ : Finset ℂ := hfin₂.toFinset with ht₂
  set t₁ : Finset ℂ := hfin₁.toFinset with ht₁
  have ht₂mem : ∀ {z : ℂ}, z ∈ t₂ ↔ z ∈ ball c R₂ ∧ xi z = 0 := by
    intro z
    rw [ht₂, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have ht₁mem : ∀ {z : ℂ}, z ∈ t₁ ↔ z ∈ ball c R₁ ∧ xi z = 0 := by
    intro z
    rw [ht₁, Set.Finite.mem_toFinset]
    exact Iff.rfl
  -- common data for a presentation over a line-centered ball
  have hm_coe : ∀ z ∈ t₂, ((m z : ℕ) : ℕ∞) = analyticOrderAt xi z := by
    intro z _
    rw [hm_def]
    exact ENat.coe_toNat (xi_order_ne_top z)
  have hm_coe₁ : ∀ z ∈ t₁, ((m z : ℕ) : ℕ∞) = analyticOrderAt xi z := by
    intro z _
    rw [hm_def]
    exact ENat.coe_toNat (xi_order_ne_top z)
  have hclosed₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂ := by
    intro z hz
    have hz' := ht₂mem.mp hz
    obtain ⟨hb, h0⟩ := lineReflect_zero_ball hc_re hz'.1 hz'.2
    exact ht₂mem.mpr ⟨hb, h0⟩
  have hclosed₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁ := by
    intro z hz
    have hz' := ht₁mem.mp hz
    obtain ⟨hb, h0⟩ := lineReflect_zero_ball hc_re hz'.1 hz'.2
    exact ht₁mem.mpr ⟨hb, h0⟩
  have hencl₂ : ∀ w ∈ t₂, ‖w - c‖ ≤ D₀ := by
    intro w hw
    have hw' := ht₂mem.mp hw
    have := hshell₂ w hw'.2 (mem_ball.mp hw'.1)
    rwa [Complex.dist_eq] at this
  have hencl₁ : ∀ w ∈ t₁, ‖w - c‖ ≤ r₁ := by
    intro w hw
    have hw' := ht₁mem.mp hw
    have h1 := hshell₁ w hw'.2 (mem_ball.mp hw'.1)
    rw [Complex.dist_eq] at h1
    linarith
  -- the outer presentation and its holography reading
  obtain ⟨h₂, h₂an, h₂0, hfact₂⟩ := exists_multi_peel_orders isOpen_ball
    (xi_analyticOnNhd _) t₂ (fun w hw => (ht₂mem.mp hw).1)
    (fun z hz h0 => ht₂mem.mpr ⟨hz, h0⟩) (fun w _ => xi_order_ne_top w)
  have hfact₂' : ∀ z ∈ ball c R₂, xi z = (∏ w ∈ t₂, (z - w) ^ m w) * h₂ z := by
    intro z hz
    rw [hm_def]
    exact hfact₂ z hz
  obtain ⟨⟨G₁, hG₁an, hG₁pow⟩, G₂, hG₂an, hG₂pow⟩ :=
    exists_annular_roots_of_enclosed hD₀_pos hR₂_gt (xi_analyticOnNhd _)
      hencl₂ h₂0 hfact₂' (pow_pos two_pos (k + 1))
  have hclass₂ := H t₂ m h₂ G₁ G₂ c D₀ R₂ (le_of_lt hD₀_pos) hR₂_gt hm_coe hclosed₂
    hencl₂ h₂an h₂0 hfact₂' hG₁an hG₂an hG₁pow hG₂pow
  have hdvd₂ : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m z :=
    (xi_deckClass_eq_line_iff_right_dvd (le_of_lt hD₀_pos) hR₂_gt hm_coe hclosed₂
      hencl₂ h₂an h₂0 hfact₂' hG₁an hG₂an hG₁pow hG₂pow).mp hclass₂
  -- the inner presentation and its holography reading
  obtain ⟨h₁, h₁an, h₁0, hfact₁⟩ := exists_multi_peel_orders isOpen_ball
    (xi_analyticOnNhd _) t₁ (fun w hw => (ht₁mem.mp hw).1)
    (fun z hz h0 => ht₁mem.mpr ⟨hz, h0⟩) (fun w _ => xi_order_ne_top w)
  have hfact₁' : ∀ z ∈ ball c R₁, xi z = (∏ w ∈ t₁, (z - w) ^ m w) * h₁ z := by
    intro z hz
    rw [hm_def]
    exact hfact₁ z hz
  obtain ⟨⟨G₁', hG₁an', hG₁pow'⟩, G₂', hG₂an', hG₂pow'⟩ :=
    exists_annular_roots_of_enclosed hr₁_pos hr₁_lt (xi_analyticOnNhd _)
      hencl₁ h₁0 hfact₁' (pow_pos two_pos (k + 1))
  have hclass₁ := H t₁ m h₁ G₁' G₂' c r₁ R₁ (le_of_lt hr₁_pos) hr₁_lt hm_coe₁ hclosed₁
    hencl₁ h₁an h₁0 hfact₁' hG₁an' hG₂an' hG₁pow' hG₂pow'
  have hdvd₁ : 2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m z :=
    (xi_deckClass_eq_line_iff_right_dvd (le_of_lt hr₁_pos) hr₁_lt hm_coe₁ hclosed₁
      hencl₁ h₁an h₁0 hfact₁' hG₁an' hG₂an' hG₁pow' hG₂pow').mp hclass₁
  -- the difference of the two right-half sums is exactly the order of ρ
  have ht₁₂ : t₁ ⊆ t₂ := by
    intro z hz
    have hz' := ht₁mem.mp hz
    refine ht₂mem.mpr ⟨?_, hz'.2⟩
    have := mem_ball.mp hz'.1
    exact mem_ball.mpr (by linarith [hR₁_lt, hR₂_gt])
  have hfsub : t₁.filter (fun z => 1 / 2 < z.re) ⊆ t₂.filter (fun z => 1 / 2 < z.re) :=
    Finset.filter_subset_filter _ ht₁₂
  have hsplit := Finset.sum_sdiff (f := m) hfsub
  have hdiff : t₂.filter (fun z => 1 / 2 < z.re) \ t₁.filter (fun z => 1 / 2 < z.re)
      = {ρ} := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton, not_and]
    constructor
    · rintro ⟨⟨hwt₂, hwre⟩, hnot⟩
      have hw2 := ht₂mem.mp hwt₂
      have hnott₁ : w ∉ t₁ := fun hw₁ => hnot hw₁ hwre
      have hge : R₁ ≤ dist w c := by
        by_contra hlt
        exact hnott₁ (ht₁mem.mpr ⟨mem_ball.mpr (not_le.mp hlt), hw2.2⟩)
      have hle : dist w c ≤ D₀ := hshell₂ w hw2.2 (mem_ball.mp hw2.1)
      have hEQ : dist w c = D₀ := by
        rcases lt_or_eq_of_le hle with hlt | he
        · exfalso
          have hzin : w ∈ hZfin.toFinset := href w (by linarith) hw2.2
          have h1 := hle_rmax _ (hmemS₁ w hzin hlt)
          linarith
        · exact he
      by_contra hwρ
      have hwlρ : w ≠ lineReflect ρ := by
        intro he
        rw [he, lineReflect_re] at hwre
        linarith
      have hwZ : w ∈ hZfin.toFinset := href w (by linarith) hw2.2
      exact hgood w hwZ hwρ hwlρ (hEQ.trans hD₀_def)
    · rintro rfl
      refine ⟨⟨?_, hρre⟩, ?_⟩
      · refine ht₂mem.mpr ⟨mem_ball.mpr ?_, hρzero⟩
        rw [← hD₀_def]
        exact hR₂_gt
      · intro hρt₁ _
        have h1 := ht₁mem.mp hρt₁
        have h2 := mem_ball.mp h1.1
        rw [← hD₀_def] at h2
        linarith
  rw [hdiff, Finset.sum_singleton] at hsplit
  -- 2^k ∣ m ρ + N₁ and 2^k ∣ N₁ force 2^k ∣ m ρ
  have hdvd_sum : 2 ^ k ∣ m ρ + ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m z := by
    rw [hsplit]
    exact hdvd₂
  rw [add_comm] at hdvd_sum
  have hdvdρ : 2 ^ k ∣ m ρ := (Nat.dvd_add_right hdvd₁).mp hdvd_sum
  have hcoe : analyticOrderAt xi ρ = (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat (xi_order_ne_top ρ)).symm
  rw [hcoe]
  exact Nat.cast_dvd_cast hdvdρ

/-- **Rung ⟺ line holography.**  The level-`k` rung holds iff every reflection-closed enclosed
ξ-presentation has level-`2^{k+1}` deck class equal to its line-predicted class: the family of
DISC bits over all presentations is trivial exactly on the rung. -/
theorem rhLadder_iff_lineHolography (k : ℕ) : RHLadder k ↔ LineHolography k :=
  ⟨lineHolography_of_rhLadder, rhLadder_of_lineHolography⟩

/-- **RH as total line holography**: RH holds iff at every level the loop classes of all
enclosed presentations agree with their line predictions. -/
theorem rh_iff_forall_lineHolography : RiemannHypothesis ↔ ∀ k, LineHolography k := by
  rw [rh_iff_forall_ladder]
  exact forall_congr' fun k => rhLadder_iff_lineHolography k

end RHTower
