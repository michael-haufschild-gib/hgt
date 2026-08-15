import GaloisForLFunctions.RHTower.SelbergClass.BarnesFiniteRectangleExplicitSum
import GaloisForLFunctions.RHTower.SelbergClass.BarnesHorizontalEdges
import GaloisForLFunctions.RHTower.SelbergClass.BarnesTwoGammaLineIntegrable
import GaloisForLFunctions.PNTPlus.PerronFormula

/-!
# Fixed finite Barnes vertical shift

This module shifts the concrete Barnes two-Gamma contour across exactly the
finitely many poles `0, -1, ..., -m`.  It proves neither an infinite Barnes
identity nor a binomial-series expansion or analytic continuation statement.

The left line has negative real part, so its integrability is proved here from
the arbitrary-strip Gamma estimate; the positive-line integrability theorem is
used only on the right line.
-/

open Complex Filter Set MeasureTheory
open scoped BigOperators Topology Interval

namespace RHTower

noncomputable section

private theorem continuous_barnesJ_left_line
    {ξ η : ℂ} {m : ℕ} {c : ℝ} (hc : 0 < c) (hcξ : c < ξ.re) (hη : η ≠ 0) :
    Continuous (fun t : ℝ =>
      barnesJ ξ η ((-((m : ℝ) + 1 / 2) : ℂ) + (t : ℂ) * I)) := by
  let L : ℝ := -((m : ℝ) + 1 / 2)
  let line : ℝ → ℂ := fun t => (L : ℂ) + (t : ℂ) * I
  have hline : Continuous line :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hLc : L ≤ c := by
    dsimp [L]
    have hm : (0 : ℝ) ≤ m := by positivity
    linarith
  have hright : Continuous (fun t : ℝ => Gamma (line t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hpole : ∀ n : ℕ, line t ≠ -(n : ℂ) := by
      intro n h
      have hre := congrArg Complex.re h
      dsimp [line, L] at hre
      have hmn : 2 * (n : ℝ) = 2 * (m : ℝ) + 1 := by
        norm_num at hre ⊢
        linarith
      have hnat : 2 * n = 2 * m + 1 := by
        exact_mod_cast hmn
      omega
    exact (HTGeometry.analyticAt_Gamma_off_poles hpole).continuousAt.comp hline.continuousAt
  have hleft : Continuous (fun t : ℝ => Gamma (ξ - line t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hpos : 0 < (ξ - line t).re := by
      have hlineRe : (line t).re = L := by
        dsimp [line]
        simp
      rw [Complex.sub_re, hlineRe]
      linarith
    have hsubAt : ContinuousAt (fun z : ℂ => ξ - z) (line t) :=
      (continuous_const.sub continuous_id).continuousAt
    have hgammaSubAt : ContinuousAt (fun z : ℂ => Gamma (ξ - z)) (line t) :=
      (HTGeometry.analyticAt_Gamma_of_re_pos hpos).continuousAt.comp hsubAt
    have hcomp : ContinuousAt (Gamma ∘ fun t : ℝ => ξ - line t) t :=
      hgammaSubAt.comp hline.continuousAt
    simpa [Function.comp_def] using hcomp
  have hpow : Continuous (fun t : ℝ => η ^ (-line t)) :=
    Continuous.const_cpow hline.neg (Or.inl hη)
  convert (hleft.mul hright).mul hpow using 1
  ext t
  simp [barnesJ, line, L]

private theorem integrable_barnesJ_left_line
    {ξ η : ℂ} {m : ℕ} {c : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hη : η ≠ 0) (harg : |Complex.arg η| < Real.pi) :
    Integrable (fun t : ℝ =>
      barnesJ ξ η ((-((m : ℝ) + 1 / 2) : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨hδ, C, N, hC, htail⟩ :=
    exists_bound_norm_barnesJ_horizontal (m := m) hc hcξ hη harg
  let L : ℝ := -((m : ℝ) + 1 / 2)
  let R : ℝ := |ξ.im| + 1
  let g : ℝ → ℝ := fun t =>
    C * |t| ^ N * Real.exp (-(Real.pi - |Complex.arg η|) * |t|)
  have hg : Integrable g := by
    dsimp [g]
    simpa [mul_assoc] using
      (HTGeometry.integrable_abs_pow_mul_exp_neg_abs N hδ).const_mul C
  have hcont : Continuous (fun t : ℝ =>
      barnesJ ξ η ((L : ℂ) + (t : ℂ) * I)) := by
    simpa [L] using continuous_barnesJ_left_line (m := m) hc hcξ hη
  have hmid : IntegrableOn (fun t : ℝ =>
      barnesJ ξ η ((L : ℂ) + (t : ℂ) * I)) (Icc (-R) R) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have htailOn : IntegrableOn (fun t : ℝ =>
      barnesJ ξ η ((L : ℂ) + (t : ℂ) * I)) (Icc (-R) R)ᶜ := by
    refine Integrable.mono' hg.integrableOn hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
    have hR : R ≤ |t| := by
      by_contra hnot
      have hlt : |t| < R := lt_of_not_ge hnot
      apply ht
      constructor
      · nlinarith [neg_abs_le t]
      · nlinarith [le_abs_self t]
    dsimp only [g]
    have hLc : L ≤ c := by
      dsimp [L]
      have hm : (0 : ℝ) ≤ m := by positivity
      linarith
    by_cases ht0 : 0 ≤ t
    · have hpoint := htail 1 |t| L (by norm_num) (by simpa [R] using hR)
        (by simp [L]) hLc
      have hmul : (1 : ℝ) * |t| = t := by rw [abs_of_nonneg ht0]; ring
      rw [hmul] at hpoint
      rw [← neg_mul] at hpoint
      simpa only [L] using hpoint
    · have ht0' : t ≤ 0 := le_of_not_ge ht0
      have hpoint := htail (-1) |t| L (by norm_num) (by simpa [R] using hR)
        (by simp [L]) hLc
      have hmul : (-1 : ℝ) * |t| = t := by rw [abs_of_nonpos ht0']; ring
      rw [hmul] at hpoint
      rw [← neg_mul] at hpoint
      simpa only [L] using hpoint
  have htotal : Integrable (fun t : ℝ =>
      barnesJ ξ η ((L : ℂ) + (t : ℂ) * I)) := by
    rw [← integrableOn_univ, ← union_compl_self (Icc (-R) R)]
    exact hmid.union htailOn
  simpa [L] using htotal

/-- The fixed finite Barnes displacement is oriented as right vertical line
minus left vertical line.  Only poles `0, -1, ..., -m` are crossed. -/
theorem verticalIntegral'_barnesJ_sub_left_eq_range_sum
    {ξ η : ℂ} {m : ℕ} {c : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hη : η ≠ 0) (harg : |Complex.arg η| < Real.pi) :
    VerticalIntegral' (barnesJ ξ η) c -
        VerticalIntegral' (barnesJ ξ η) (-((m : ℝ) + 1 / 2)) =
      ∑ n ∈ Finset.range (m + 1),
        ((-1 : ℂ) ^ n / (n.factorial : ℂ)) * Gamma (ξ + n) * η ^ n := by
  let L : ℝ := -((m : ℝ) + 1 / 2)
  have htop : Tendsto (fun y : ℝ =>
      ∫ x in L..c, barnesJ ξ η ((x : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
    simpa [L] using tendsto_barnesJ_top_horizontal_edge (m := m) hc hcξ hη harg
  have hbot : Tendsto (fun y : ℝ =>
      ∫ x in L..c, barnesJ ξ η ((x : ℂ) + (y : ℂ) * I)) atBot (𝓝 0) := by
    have hbottom := tendsto_barnesJ_bottom_horizontal_edge (m := m) hc hcξ hη harg
    refine Filter.Tendsto.congr' ?_ (hbottom.comp tendsto_neg_atBot_atTop)
    filter_upwards [] with y
    simp only [Function.comp_apply]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x
    intro _
    congr 1
    push_cast
    ring
  have hleft : Integrable (fun y : ℝ =>
      barnesJ ξ η ((L : ℂ) + (y : ℂ) * I)) := by
    simpa [L] using integrable_barnesJ_left_line (m := m) hc hcξ hη harg
  have hright : Integrable (fun y : ℝ =>
      barnesJ ξ η ((c : ℂ) + (y : ℂ) * I)) := by
    convert integrable_barnesTwoGammaIntegrand (ξ := ξ) (η := η) hc hcξ hη harg using 1
    ext y
    simp [barnesJ, barnesTwoGammaIntegrand]
  have hraw := RectangleIntegral_tendsTo_VerticalIntegral
    (σ := L) (σ' := c) (f := barnesJ ξ η) hbot htop hleft hright
  let κ : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  have hscaled := hraw.const_smul κ
  have hrect : Tendsto (fun T : ℝ =>
      RectangleIntegral' (barnesJ ξ η) (barnesLeftCorner m T) (barnesRightCorner c T)) atTop
      (𝓝 (VerticalIntegral' (barnesJ ξ η) c - VerticalIntegral' (barnesJ ξ η) L)) := by
    have hfun : (fun T : ℝ =>
        κ • RectangleIntegral (barnesJ ξ η) ((L : ℂ) - I * (T : ℂ))
          ((c : ℂ) + I * (T : ℂ))) =
        fun T : ℝ => RectangleIntegral' (barnesJ ξ η)
          (barnesLeftCorner m T) (barnesRightCorner c T) := by
      funext T
      change κ • RectangleIntegral (barnesJ ξ η) ((L : ℂ) - I * (T : ℂ))
          ((c : ℂ) + I * (T : ℂ)) =
        (1 / (2 * (Real.pi : ℂ) * I) : ℂ) • RectangleIntegral (barnesJ ξ η)
          (barnesLeftCorner m T) (barnesRightCorner c T)
      dsimp [κ]
      have hleftCorner : barnesLeftCorner m T = ((L : ℂ) - I * (T : ℂ)) := by
        simp [barnesLeftCorner, L]
        ring
      have hrightCorner : barnesRightCorner c T = ((c : ℂ) + I * (T : ℂ)) := by
        simp [barnesRightCorner]
        ring
      rw [hleftCorner, hrightCorner]
    have hlim : κ •
        (VerticalIntegral (barnesJ ξ η) c - VerticalIntegral (barnesJ ξ η) L) =
        VerticalIntegral' (barnesJ ξ η) c - VerticalIntegral' (barnesJ ξ η) L := by
      change κ •
          (VerticalIntegral (barnesJ ξ η) c - VerticalIntegral (barnesJ ξ η) L) =
        (1 / (2 * (Real.pi : ℂ) * I) : ℂ) • VerticalIntegral (barnesJ ξ η) c -
          (1 / (2 * (Real.pi : ℂ) * I) : ℂ) • VerticalIntegral (barnesJ ξ η) L
      dsimp [κ]
      ring
    rw [hfun, hlim] at hscaled
    exact hscaled
  let S : ℂ := ∑ n ∈ Finset.range (m + 1),
    ((-1 : ℂ) ^ n / (n.factorial : ℂ)) * Gamma (ξ + n) * η ^ n
  have hrectEq : ∀ᶠ T : ℝ in atTop,
      RectangleIntegral' (barnesJ ξ η) (barnesLeftCorner m T) (barnesRightCorner c T) = S := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simpa [S] using rectangleIntegral_barnesJ_eq_range_sum (m := m) hc hcξ hT hη
  have hrectS : Tendsto (fun T : ℝ =>
      RectangleIntegral' (barnesJ ξ η) (barnesLeftCorner m T) (barnesRightCorner c T)) atTop
      (𝓝 S) := Filter.EventuallyEq.tendsto hrectEq
  have hdiff : VerticalIntegral' (barnesJ ξ η) c - VerticalIntegral' (barnesJ ξ η) L = S :=
    tendsto_nhds_unique hrect hrectS
  simpa [L, S] using hdiff

end

end RHTower
