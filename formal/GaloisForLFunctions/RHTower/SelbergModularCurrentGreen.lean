import GaloisForLFunctions.RHTower.SelbergModularArcIntegration

/-!
# Complete modular Green formula for physical vector currents

Both Fubini descriptions of the actual compact modular core and first-derivative
FTC give Green's formula for a C¹ planar vector current. The formula retains the
entire vertical-side jump, horizontal top, and paired circular normal-density
flux. No matching-side condition or circular cancellation is assumed.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergModularCurrentGreen
open SelbergMaassMean SelbergMaassTraceEnergy SelbergMaassTraceStokes
open SelbergModularDomainSlices SelbergModularArcIntegration
noncomputable section

variable (F : ℂ → ℝ) (hF : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im})
include hF

private theorem derivative_continuousOn (v : ℂ) :
    ContinuousOn (dir v F) {z : ℂ | 0 < z.im} :=
  (dir_contDiffOn hF (m := 0) (by norm_num) v).continuousOn

private theorem slice_continuous {y : ℝ} (hy : 0 < y) : Continuous (fun x => F (point x y)) := by
  apply hF.continuousOn.comp_continuous (show Continuous (fun x => point x y) by unfold point; fun_prop)
  intro x
  simpa [point] using hy

private theorem derivative_slice_continuous (v : ℂ) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => dir v F (point x y)) := by
  apply (derivative_continuousOn F hF v).comp_continuous
    (show Continuous (fun x => point x y) by unfold point; fun_prop)
  intro x
  simpa [point] using hy

private theorem height_continuousOn (a : ℝ → ℝ) (ha : Continuous a) :
    ContinuousOn (fun y => F (point (a y) y)) (Ioi (0 : ℝ)) := by
  apply hF.continuousOn.comp
    (show Continuous (fun y => point (a y) y) by unfold point; fun_prop).continuousOn
  intro y hy
  simpa [point] using hy

private theorem height_intervalIntegrable (a : ℝ → ℝ) (ha : Continuous a)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    IntervalIntegrable (fun y => F (point (a y) y)) volume b c :=
  ((height_continuousOn F hF a ha).mono
    (fun _ ht => lt_of_lt_of_le (lt_min hb hc) ht.1)).intervalIntegrable

private theorem horizontal_ftc {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    (∫ x in a..b, dir 1 F (point x y))=F (point b y)-F (point a y) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _
    ((derivative_slice_continuous F hF 1 hy).intervalIntegrable a b)
  intro x _
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact ((hF.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)

private theorem vertical_ftc (x : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b, dir Complex.I F (point x y))=F (point x b)-F (point x a) := by
  have hd : ContinuousOn (fun y => dir Complex.I F (point x y)) (Ioi (0 : ℝ)) := by
    apply (derivative_continuousOn F hF Complex.I).comp
      (show Continuous (fun y => point x y) by unfold point; fun_prop).continuousOn
    intro y hy
    simpa [point] using hy
  have hsub : uIcc a b ⊆ Ioi (0 : ℝ) := fun _ ht => lt_of_lt_of_le (lt_min ha hb) ht.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ ((hd.mono hsub).intervalIntegrable)
  intro y hy
  have hp : 0 < (point x y).im := by simpa [point] using hsub hy
  exact ((hF.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt y (point_vertical x y)

/-- Every physical first derivative of a C¹ current is integrable on the compact modular core. -/
theorem derivative_integrableOn (v : ℂ) (Y : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => dir v F (point p.1 p.2)) (domain Y) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => dir v F (point p.1 p.2)) (cell Y) := by
    apply (derivative_continuousOn F hF v).comp
      (show Continuous (fun p : ℝ × ℝ => point p.1 p.2) by unfold point; fun_prop).continuousOn
    intro p hp
    have hy := hp.2.1
    change 0 < (point p.1 p.2).im
    simp only [point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add]
    linarith
  exact (hc.mono (domain_subset_cell Y)).integrableOn_compact (isCompact_domain Y)

/-- A physical C¹ current is continuous along the complete circular core boundary. -/
theorem arc_continuousOn :
    ContinuousOn (fun x => F (point x (arcHeight x))) (Icc (-(1/2 : ℝ)) (1/2)) := by
  apply hF.continuousOn.comp
    (show Continuous (fun x => point x (arcHeight x)) by
      unfold point
      exact Complex.continuous_ofReal.add ((Complex.continuous_ofReal.comp continuous_arcHeight).mul continuous_const)).continuousOn
  intro x hx
  simpa [point] using arcHeight_pos hx

/-- Horizontal Green integration retains both actual side traces and the curved-arc current. -/
theorem horizontal_area_eq_side_arc {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, dir 1 F (point p.1 p.2)) =
      (∫ y in arcFloor..Y, F (point (1/2) y)-F (point (-(1/2)) y))+
      ∫ x in (0 : ℝ)..(1/2), (x/arcHeight x)*
        (F (point (-x) (arcHeight x))-F (point x (arcHeight x))) := by
  let J := fun p : ℝ × ℝ => dir 1 F (point p.1 p.2)
  let S := horizontalSliceIntegral J Y
  let H := fun y => F (point (1/2) y)-F (point (-(1/2)) y)
  let g := fun y => F (point (-sideRadius y) y)-F (point (sideRadius y) y)
  have hi := derivative_integrableOn F hF 1 Y
  have hS : Integrable S := integrable_horizontalSliceIntegral hi
  have hfloor : arcFloor ≤ 1 := arcHeight_le_one ⟨by norm_num,le_rfl⟩
  have hH {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable H volume a b :=
    (height_intervalIntegrable F hF (fun _ => 1/2) continuous_const ha hb).sub
      (height_intervalIntegrable F hF (fun _ => -(1/2)) continuous_const ha hb)
  have hg : IntervalIntegrable g volume arcFloor 1 :=
    (height_intervalIntegrable F hF (fun y => -sideRadius y)
      (by unfold sideRadius; fun_prop) arcFloor_pos (by norm_num)).sub
      (height_intervalIntegrable F hF sideRadius (by unfold sideRadius; fun_prop) arcFloor_pos (by norm_num))
  have hlow : (∫ y in arcFloor..1, S y)=(∫ y in arcFloor..1, H y)+(∫ y in arcFloor..1, g y) := by
    rw [← intervalIntegral.integral_add (hH arcFloor_pos (by norm_num)) hg]
    apply intervalIntegral.integral_congr
    intro y hy
    have hyI : y ∈ Icc arcFloor 1 := by simpa [uIcc_of_le hfloor] using hy
    have hy0 := arcFloor_pos.trans_le hyI.1
    change horizontalSliceIntegral J Y y = _
    rw [horizontalSliceIntegral_eq_sides J hY hyI (derivative_slice_continuous F hF 1 hy0)]
    change (∫ x in (-(1/2 : ℝ))..(-sideRadius y), dir 1 F (point x y))+
      (∫ x in sideRadius y..(1/2), dir 1 F (point x y)) = _
    rw [horizontal_ftc F hF hy0,horizontal_ftc F hF hy0]
    dsimp only [H,g]
    ring
  have hhigh : (∫ y in (1 : ℝ)..Y, S y)=∫ y in (1 : ℝ)..Y, H y := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hyI : y ∈ Icc (1 : ℝ) Y := by simpa [uIcc_of_le hY] using hy
    have hy0 : 0 < y := by linarith [hyI.1]
    change horizontalSliceIntegral J Y y = _
    rw [horizontalSliceIntegral_eq_full J hyI]
    exact horizontal_ftc F hF hy0 _ _
  have he : (∫ p in domain Y, J p)=(∫ y in arcFloor..Y, H y)+∫ y in arcFloor..1, g y := by
    rw [setIntegral_eq_horizontal hi,integral_horizontalSliceIntegral_eq_interval J hY]
    change (∫ y in arcFloor..Y, S y) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (1 : ℝ)) hS.intervalIntegrable hS.intervalIntegrable,
      hlow,hhigh,← intervalIntegral.integral_add_adjacent_intervals
        (hH arcFloor_pos (by norm_num : (0 : ℝ) < 1)) (hH (by norm_num : (0 : ℝ) < 1) (by linarith : 0 < Y))]
    ring
  rw [he,arc_change_of_variables g]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Icc (0 : ℝ) (1/2) := by simpa using hx
  dsimp only [g]
  rw [sideRadius_arcHeight hxI]

/-- Vertical Green integration retains the top and the entire curved lower boundary. -/
theorem vertical_area_eq_top_arc {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, dir Complex.I F (point p.1 p.2)) =
      (∫ x in (-(1/2 : ℝ))..(1/2), F (point x Y))-
        ∫ x in (-(1/2 : ℝ))..(1/2), F (point x (arcHeight x)) := by
  rw [setIntegral_eq_vertical hY (derivative_integrableOn F hF Complex.I Y)]
  have hy : 0 < Y := by linarith
  have hb : IntervalIntegrable (fun x => F (point x (arcHeight x))) volume (-(1/2)) (1/2) := by
    apply ContinuousOn.intervalIntegrable
    simpa using arc_continuousOn F hF
  rw [← intervalIntegral.integral_sub ((slice_continuous F hF hy).intervalIntegrable _ _) hb]
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Icc (-(1/2 : ℝ)) (1/2) := by simpa using hx
  exact vertical_ftc F hF x (arcHeight_pos hxI) hy

/-- The complete paired outward normal-density flux of a planar current on the modular arc. -/
def normalPair (F G : ℂ → ℝ) (x : ℝ) : ℝ :=
  (-x/arcHeight x)*F (point x (arcHeight x))-G (point x (arcHeight x))+
    (x/arcHeight x)*F (point (-x) (arcHeight x))-G (point (-x) (arcHeight x))

/-- Green's formula for a physical C¹ vector current, with every side, top, and arc term retained. -/
theorem current_green_identity (G : ℂ → ℝ) (hG : ContDiffOn ℝ 1 G {z : ℂ | 0 < z.im})
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, dir 1 F (point p.1 p.2)+dir Complex.I G (point p.1 p.2)) =
      (∫ y in arcFloor..Y, F (point (1/2) y)-F (point (-(1/2)) y))+
      (∫ x in (-(1/2 : ℝ))..(1/2), G (point x Y))+
        ∫ x in (0 : ℝ)..(1/2), normalPair F G x := by
  rw [integral_add (derivative_integrableOn F hF 1 Y) (derivative_integrableOn G hG Complex.I Y),
    horizontal_area_eq_side_arc F hF hY,vertical_area_eq_top_arc G hG hY,fold_integral (arc_continuousOn G hG)]
  have hneg (x : ℝ) : arcHeight (-x)=arcHeight x := by simp [arcHeight]
  have hsub : uIcc (0 : ℝ) (1/2) ⊆ Icc (-(1/2 : ℝ)) (1/2) := by
    intro x hx
    have h : x ∈ Icc (0 : ℝ) (1/2) := by simpa using hx
    exact ⟨by linarith [h.1],h.2⟩
  have href {B : ℝ → ℝ} (hb : ContinuousOn B (Icc (-(1/2 : ℝ)) (1/2))) :
      ContinuousOn (fun x => B (-x)) (Icc (-(1/2 : ℝ)) (1/2)) :=
    hb.comp continuous_neg.continuousOn (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  have hh : IntervalIntegrable (fun x => (x/arcHeight x)*
      (F (point (-x) (arcHeight x))-F (point x (arcHeight x)))) volume 0 (1/2) := by
    have hfc := href (arc_continuousOn F hF)
    simp only [hneg] at hfc
    exact (((continuousOn_id.div continuous_arcHeight.continuousOn
      (fun x hx => (arcHeight_pos hx).ne')).mul (hfc.sub (arc_continuousOn F hF))).mono hsub).intervalIntegrable
  have hb : IntervalIntegrable (fun x => G (point (-x) (arcHeight x))+G (point x (arcHeight x)))
      volume 0 (1/2) := by
    have hgc := href (arc_continuousOn G hG)
    simp only [hneg] at hgc
    exact ((hgc.add (arc_continuousOn G hG)).mono hsub).intervalIntegrable
  have he : (∫ x in (0 : ℝ)..(1/2), normalPair F G x) =
      (∫ x in (0 : ℝ)..(1/2), (x/arcHeight x)*
        (F (point (-x) (arcHeight x))-F (point x (arcHeight x))))-
      ∫ x in (0 : ℝ)..(1/2), G (point (-x) (arcHeight x))+G (point x (arcHeight x)) := by
    rw [← intervalIntegral.integral_sub hh hb]
    apply intervalIntegral.integral_congr
    intro x _
    unfold normalPair
    ring
  rw [he]
  simp only [hneg]
  ring

end
end GaloisForLFunctions.RHTower.SelbergModularCurrentGreen
