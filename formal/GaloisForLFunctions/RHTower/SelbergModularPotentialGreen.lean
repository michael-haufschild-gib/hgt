import GaloisForLFunctions.RHTower.SelbergModularArcIntegration

/-!
# Planar Green formula for a modular scalar potential

A C² scalar potential with the stated matching side and unit-circle currents has
its standard planar Laplacian integral equal to its top current. Smoothness and
both matching conditions remain explicit. The Maass trace and its regularized
amplitude verify those conditions from their original modular invariance.
The proof uses ordinary area measure, both Fubini orders, and actual FTC.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergModularPotentialGreen
open SelbergMaassMean SelbergMaassTraceEnergy SelbergMaassTraceStokes
  SelbergModularDomainSlices SelbergModularArcIntegration
noncomputable section

variable (F : ℂ → ℝ) (hF : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im})

/-- A scalar potential's actual first coordinate current. -/
def currentAt (v : ℂ) (x y : ℝ) : ℝ := dir v F (point x y)

/-- A scalar potential's actual second derivative in standard planar coordinates. -/
def secondAt (v w : ℂ) (p : ℝ × ℝ) : ℝ := dir v (dir w F) (point p.1 p.2)

include hF

/-- Actual C² regularity gives C¹ directional derivatives. -/
theorem first_regular (v : ℂ) : ContDiffOn ℝ 1 (dir v F) {z : ℂ | 0 < z.im} :=
  dir_contDiffOn hF (by norm_num) v

/-- Actual C² regularity gives continuous second derivatives. -/
theorem second_regular (v w : ℂ) : ContinuousOn (dir v (dir w F)) {z : ℂ | 0 < z.im} :=
  (dir_contDiffOn (first_regular F hF w) (m := 0) (by norm_num) v).continuousOn

/-- The actual vertical derivative of each potential current slice is its second chart derivative. -/
theorem currentAt_vertical (v : ℂ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (currentAt F v x)
      (dir Complex.I (dir v (F)) (point x y)) y := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact (((first_regular F hF v).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      y (point_vertical x y)

/-- The actual horizontal derivative of each potential current slice is its second chart derivative. -/
theorem currentAt_horizontal (v : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t => currentAt F v t y)
      (dir 1 (dir v (F)) (point x y)) x := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact (((first_regular F hF v).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      x (point_horizontal x y)

/-- Every actual current has a continuous horizontal slice. -/
theorem currentAt_horizontal_continuous (v : ℂ) {y : ℝ} (hy : 0 < y) : Continuous (fun x => currentAt F v x y) :=
  continuous_iff_continuousAt.mpr (fun x => (currentAt_horizontal F hF v hy x).continuousAt)

/-- Every second current derivative has continuous positive-height slices. -/
theorem second_current_vertical_continuousOn (v w : ℂ) (x : ℝ) :
    ContinuousOn (fun y => dir v (dir w (F)) (point x y)) (Ioi 0) := by
  intro y hy
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact (((second_regular F hF v w).continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds hp)).comp (point_vertical x y).continuousAt).continuousWithinAt

/-- Every second current derivative has continuous horizontal slices. -/
theorem second_current_horizontal_continuous (v w : ℂ) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => dir v (dir w (F)) (point x y)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact ((second_regular F hF v w).continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds hp)).comp (f := fun t : ℝ => point t y) (point_horizontal x y).continuousAt

/-- Vertical FTC for an scalar potential's first directional current. -/
theorem vertical_current_integral (v : ℂ) (x : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b, dir Complex.I (dir v (F)) (point x y)) =
      currentAt F v x b - currentAt F v x a := by
  have hpos : uIcc a b ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact lt_of_lt_of_le (lt_min ha hb) hy.1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => currentAt_vertical F hF v x (hpos hy))
    ((second_current_vertical_continuousOn F hF Complex.I v x).mono hpos).intervalIntegrable

/-- Horizontal FTC for an scalar potential's first directional current. -/
theorem horizontal_current_integral (v : ℂ) {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    (∫ x in a..b, dir 1 (dir v (F)) (point x y)) =
      currentAt F v b y - currentAt F v a y :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => currentAt_horizontal F hF v hy x)
    ((second_current_horizontal_continuous F hF 1 v hy).intervalIntegrable _ _)


/-- C² potential regularity gives joint continuity on every compact cell. -/
theorem secondAt_continuousOn (v w : ℂ) (Y : ℝ) :
    ContinuousOn (secondAt F v w) (cell Y) := by
  apply (second_regular F hF v w).comp
    (show Continuous (fun p : ℝ × ℝ => point p.1 p.2) by unfold point; fun_prop).continuousOn
  intro p hp
  have hy := hp.2.1
  change 0 < (point p.1 p.2).im
  simp only [point, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
  linarith

/-- The actual second potential derivative is integrable for standard domain area measure. -/
theorem secondAt_integrableOn (v w : ℂ) (Y : ℝ) :
    IntegrableOn (secondAt F v w) (domain Y) :=
  ((secondAt_continuousOn F hF v w Y).mono (domain_subset_cell Y)).integrableOn_compact
    (isCompact_domain Y)

/-- The scalar potential's first current restricts continuously to the circular boundary. -/
theorem current_arc_continuousOn (v : ℂ) :
    ContinuousOn (fun x => currentAt F v x (arcHeight x))
      (Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
  apply (first_regular F hF v).continuousOn.comp
    (show Continuous (fun x => point x (arcHeight x)) by
      unfold point; exact Complex.continuous_ofReal.add ((Complex.continuous_ofReal.comp continuous_arcHeight).mul continuous_const)).continuousOn
  intro x hx
  change 0 < (point x (arcHeight x)).im
  simpa [point] using arcHeight_pos hx

/-- Horizontal Fubini, side FTC, and the exact circular substitution identify the area term. -/
theorem horizontal_area_eq_arc
    (hside : ∀ {y : ℝ}, 0 < y → currentAt F 1 (1 / 2) y = currentAt F 1 (-(1 / 2)) y) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, secondAt F 1 1 p) =
      ∫ x in (0 : ℝ)..(1 / 2), x / arcHeight x *
        (currentAt F 1 (-x) (arcHeight x) - currentAt F 1 x (arcHeight x)) := by
  let J := secondAt F 1 1
  let S : ℝ → ℝ := horizontalSliceIntegral J Y
  let g : ℝ → ℝ := fun y => currentAt F 1 (-sideRadius y) y - currentAt F 1 (sideRadius y) y
  have hi := secondAt_integrableOn F hF 1 1 Y
  have hS : Integrable S := integrable_horizontalSliceIntegral hi
  have hfloor : arcFloor ≤ 1 := arcHeight_le_one ⟨by norm_num, le_rfl⟩
  have he : (∫ p in domain Y, J p) = ∫ y in arcFloor..1, g y := by
    rw [setIntegral_eq_horizontal hi, integral_horizontalSliceIntegral_eq_interval J hY]
    change (∫ y in arcFloor..Y, S y) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (b := (1 : ℝ)) hS.intervalIntegrable hS.intervalIntegrable]
    have hlow : (∫ y in arcFloor..1, S y) = ∫ y in arcFloor..1, g y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyI : y ∈ Icc arcFloor 1 := by simpa [uIcc_of_le hfloor] using hy
      have hy0 := arcFloor_pos.trans_le hyI.1
      change horizontalSliceIntegral J Y y = g y
      rw [horizontalSliceIntegral_eq_sides J hY hyI (second_current_horizontal_continuous F hF 1 1 hy0)]
      change (∫ x in (-(1 / 2 : ℝ))..(-sideRadius y), dir 1 (dir 1 (F)) (point x y)) +
        (∫ x in sideRadius y..(1 / 2), dir 1 (dir 1 (F)) (point x y)) = _
      rw [horizontal_current_integral F hF 1 hy0, horizontal_current_integral F hF 1 hy0,
        hside hy0]
      dsimp only [g]
      ring
    have hhigh : (∫ y in (1 : ℝ)..Y, S y) = 0 := by
      rw [← intervalIntegral.integral_zero (a := (1 : ℝ)) (b := Y)]
      apply intervalIntegral.integral_congr
      intro y hy
      have hyI : y ∈ Icc (1 : ℝ) Y := by simpa [uIcc_of_le hY] using hy
      have hy0 : 0 < y := by linarith [hyI.1]
      change horizontalSliceIntegral J Y y = 0
      rw [horizontalSliceIntegral_eq_full J hyI]
      change (∫ x in (-(1 / 2 : ℝ))..(1 / 2), dir 1 (dir 1 (F)) (point x y)) = 0
      rw [horizontal_current_integral F hF 1 hy0, hside hy0, sub_self]
    rw [hlow, hhigh, add_zero]
  rw [he, arc_change_of_variables g]
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Icc (0 : ℝ) (1 / 2) := by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
  dsimp only [g]
  rw [sideRadius_arcHeight hxI]

/-- Inversion turns the horizontal area term into the full lower vertical current. -/
theorem horizontal_area_eq_bottom
    (hside : ∀ {y : ℝ}, 0 < y → currentAt F 1 (1 / 2) y = currentAt F 1 (-(1 / 2)) y)
    (harc : ∀ {x y : ℝ}, 0 < y → x ^ (2 : ℕ) + y ^ (2 : ℕ) = 1 →
      (x / y) * (currentAt F 1 (-x) y - currentAt F 1 x y) -
        currentAt F Complex.I (-x) y - currentAt F Complex.I x y = 0) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, secondAt F 1 1 p) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt F Complex.I x (arcHeight x) := by
  rw [horizontal_area_eq_arc F hF hside hY, fold_integral (current_arc_continuousOn F hF Complex.I)]
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Icc (0 : ℝ) (1 / 2) := by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
  have hxF : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hxI.1], hxI.2⟩
  have hc := harc (x := x) (arcHeight_pos hxF)
    (by rw [arcHeight_sq hxF]; ring)
  have hneg : arcHeight (-x) = arcHeight x := by simp [arcHeight]
  dsimp only
  rw [hneg]
  linarith

/-- Vertical Fubini and actual FTC retain both the top and circular boundary terms. -/
theorem vertical_area_eq_top_sub_bottom {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, secondAt F Complex.I Complex.I p) =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt F Complex.I x Y) -
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt F Complex.I x (arcHeight x) := by
  rw [setIntegral_eq_vertical hY (secondAt_integrableOn F hF Complex.I Complex.I Y)]
  have hy : 0 < Y := by linarith
  have hb : IntervalIntegrable (fun x => currentAt F Complex.I x (arcHeight x))
      volume (-(1 / 2 : ℝ)) (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] using current_arc_continuousOn F hF Complex.I
  rw [← intervalIntegral.integral_sub ((currentAt_horizontal_continuous F hF Complex.I hy).intervalIntegrable _ _) hb]
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa [uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] using hx
  exact vertical_current_integral F hF Complex.I x (arcHeight_pos hxI) hy

/-- Standard planar Green identity with the side and circular conditions explicit. -/
theorem area_laplacian_eq_top
    (hside : ∀ {y : ℝ}, 0 < y → currentAt F 1 (1 / 2) y = currentAt F 1 (-(1 / 2)) y)
    (harc : ∀ {x y : ℝ}, 0 < y → x ^ (2 : ℕ) + y ^ (2 : ℕ) = 1 →
      (x / y) * (currentAt F 1 (-x) y - currentAt F 1 x y) -
        currentAt F Complex.I (-x) y - currentAt F Complex.I x y = 0)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, realLaplacian F (point p.1 p.2)) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt F Complex.I x Y := by
  change (∫ p in domain Y, secondAt F 1 1 p + secondAt F Complex.I Complex.I p) = _
  rw [integral_add (secondAt_integrableOn F hF 1 1 Y)
    (secondAt_integrableOn F hF Complex.I Complex.I Y),
    horizontal_area_eq_bottom F hF hside harc hY, vertical_area_eq_top_sub_bottom F hF hY]
  ring

end
end GaloisForLFunctions.RHTower.SelbergModularPotentialGreen
