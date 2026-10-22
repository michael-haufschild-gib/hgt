import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectSturmTransport
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureProjectiveGlobal

/-! Exact primitive transport for the complete theta curvature defect.
The positive source defect H has a strictly increasing normalized ratio H/F.
The explicit primitive G satisfies G'=-F and tends to zero. Positivity of
b=c''-4c and b'=-H force the strict reserve b-GH/F>0, hence a finite
comparison for b/G. No limit for b or H is assumed. Full C5 compensation
and arbitrary-degree positivity remain separate open problems. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section

local notation "q" => thetaCuspLikelihoodCoordinate
local notation "F" => fun x => sourceDefectFactor (q x)

def sourceDefectPrimitive (x : ℝ) : ℝ := 216*(q x+3/2)^2/(q x)^4

theorem sourceDefectPrimitive_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < sourceDefectPrimitive x := by
  have hq := thetaCuspLikelihoodCoordinate_pos hx
  unfold sourceDefectPrimitive
  positivity

theorem hasDerivAt_sourceDefectPrimitive {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt sourceDefectPrimitive (-F x) x := by
  have hq := thetaCuspLikelihoodCoordinate_pos hx
  have hd := ((((hasDerivAt_id (q x)).add_const (3/2:ℝ)).pow 2).const_mul 216).div
    ((hasDerivAt_id (q x)).pow 4) (pow_ne_zero _ hq.ne')
  convert! hd.comp x (hasDerivAt_thetaCuspLikelihoodCoordinate x) using 1
  dsimp only [Pi.pow_apply,id_eq]
  rw [thetaCuspC5FarTail_scale_eq_coordinate_add]
  unfold sourceDefectFactor
  field_simp [hq.ne']
  ring

theorem sourceDefectPrimitive_tendsto_zero :
    Tendsto sourceDefectPrimitive atTop (nhds 0) := by
  have h2 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 2 (by norm_num)
  have h3 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 3 (by norm_num)
  have h4 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 4 (by norm_num)
  have h := ((h2.const_mul 216).add (h3.const_mul 648)).add (h4.const_mul 486)
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  have hq := thetaCuspLikelihoodCoordinate_pos hx
  unfold sourceDefectPrimitive
  field_simp [hq.ne']
  ring

theorem normalizedSourceDefect_strictMonoOn :
    StrictMonoOn normalizedSourceDefect (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_normalizedSourceDefect hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := (interior_subset hx)
    rw [(hasDerivAt_normalizedSourceDefect hx0).deriv]
    exact div_pos (defectSturmFlux_pos hx0)
      (sq_pos_of_pos (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx0)))

private theorem hasDerivAt_curvatureDefect_neg_jet (x : ℝ) :
    HasDerivAt curvatureDefect (-sourceDefectJet x) x := by
  convert! hasDerivAt_curvatureDefect x using 1
  unfold thetaCuspLogCurvatureJetThree thetaCuspLogCurvatureJet sourceDefectJet
  ring

def sourcePrimitiveReserve (x : ℝ) : ℝ :=
  curvatureDefect x-sourceDefectPrimitive x*normalizedSourceDefect x

theorem sourcePrimitiveReserve_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ sourcePrimitiveReserve x := by
  let r := normalizedSourceDefect x
  have hd (y : ℝ) (hy : x ≤ y) :
      HasDerivAt (fun z => curvatureDefect z-r*sourceDefectPrimitive z)
        (-sourceDefectJet y+r*F y) y := by
    convert! (hasDerivAt_curvatureDefect_neg_jet y).sub
      ((hasDerivAt_sourceDefectPrimitive (hx.trans hy)).const_mul r) using 1
    ring
  have hm : AntitoneOn (fun y => curvatureDefect y-r*sourceDefectPrimitive y) (Ici x) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hxy : x ≤ y := interior_subset hy
      rw [(hd y hxy).deriv]
      have hR := normalizedSourceDefect_strictMonoOn.monotoneOn hx (hx.trans hxy) hxy
      have hF := sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos (hx.trans hxy))
      have hmul : r*F y ≤ sourceDefectJet y := (le_div_iff₀ hF).mp hR
      linarith
  have hlim : Tendsto (fun y => -r*sourceDefectPrimitive y) atTop (nhds 0) := by
    simpa only [mul_zero] using sourceDefectPrimitive_tendsto_zero.const_mul (-r)
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with y hy
  have hmxy := hm (show x ∈ Ici x from mem_Ici.mpr le_rfl) hy hy
  have hb := curvatureDefect_pos (hx.trans hy)
  dsimp only [sourcePrimitiveReserve]
  dsimp only [r] at *
  linarith

theorem hasDerivAt_sourcePrimitiveReserve {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt sourcePrimitiveReserve
      (-sourceDefectPrimitive x*defectSturmFlux x/(F x)^2) x := by
  have hF := sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx)
  convert! (hasDerivAt_curvatureDefect_neg_jet x).sub
    ((hasDerivAt_sourceDefectPrimitive hx).mul (hasDerivAt_normalizedSourceDefect hx)) using 1
  unfold normalizedSourceDefect
  field_simp [hF.ne']
  ring

theorem sourcePrimitiveReserve_strictAntiOn :
    StrictAntiOn sourcePrimitiveReserve (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_sourcePrimitiveReserve hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := interior_subset hx
    rw [(hasDerivAt_sourcePrimitiveReserve hx0).deriv]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos (sourceDefectPrimitive_pos hx0))
        (defectSturmFlux_pos hx0))
      (sq_pos_of_pos (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx0)))

theorem sourcePrimitiveReserve_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < sourcePrimitiveReserve x := by
  have hx1 : 0 ≤ x+1 := by linarith
  exact (sourcePrimitiveReserve_nonneg hx1).trans_lt
    (sourcePrimitiveReserve_strictAntiOn hx hx1 (by linarith))

theorem sourceDefectPrimitive_mul_rate {x : ℝ} (hx : 0 ≤ x) :
    sourceDefectPrimitive x*(4+12/q x)=F x := by
  have hq := thetaCuspLikelihoodCoordinate_pos hx
  unfold sourceDefectPrimitive sourceDefectFactor
  field_simp [hq.ne']
  ring

/-- Actual curvature-defect slope cap from the exact tail primitive. -/
theorem curvatureDefect_slope_comparison {x : ℝ} (hx : 0 ≤ x) :
    sourceDefectJet x < (4+12/q x)*curvatureDefect x := by
  have hq := thetaCuspLikelihoodCoordinate_pos hx
  have hF := sourceDefectFactor_pos hq
  have hC := sourcePrimitiveReserve_pos hx
  have hlt : sourceDefectPrimitive x*normalizedSourceDefect x < curvatureDefect x :=
    sub_pos.mp hC
  have hid : sourceDefectJet x=F x*normalizedSourceDefect x := by
    unfold normalizedSourceDefect
    field_simp
  calc
    sourceDefectJet x=F x*normalizedSourceDefect x := hid
    _ = (4+12/q x)*(sourceDefectPrimitive x*normalizedSourceDefect x) := by
      rw [← sourceDefectPrimitive_mul_rate hx]
      ring
    _ < (4+12/q x)*curvatureDefect x := mul_lt_mul_of_pos_left hlt (by positivity)

def normalizedCurvatureDefect (x : ℝ) : ℝ :=
  curvatureDefect x/sourceDefectPrimitive x

theorem hasDerivAt_normalizedCurvatureDefect {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt normalizedCurvatureDefect
      (F x*sourcePrimitiveReserve x/(sourceDefectPrimitive x)^2) x := by
  have hF := sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx)
  convert! (hasDerivAt_curvatureDefect_neg_jet x).div
    (hasDerivAt_sourceDefectPrimitive hx) (sourceDefectPrimitive_pos hx).ne' using 1
  unfold sourcePrimitiveReserve normalizedSourceDefect
  field_simp [hF.ne']
  ring

theorem normalizedCurvatureDefect_strictMonoOn :
    StrictMonoOn normalizedCurvatureDefect (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_normalizedCurvatureDefect hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := interior_subset hx
    rw [(hasDerivAt_normalizedCurvatureDefect hx0).deriv]
    exact div_pos (mul_pos (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx0))
      (sourcePrimitiveReserve_pos hx0)) (sq_pos_of_pos (sourceDefectPrimitive_pos hx0))

theorem curvatureDefect_primitive_transport {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    sourceDefectPrimitive b*curvatureDefect a < sourceDefectPrimitive a*curvatureDefect b := by
  have h := normalizedCurvatureDefect_strictMonoOn ha (ha.trans hab.le) hab
  have he := (div_lt_div_iff₀ (sourceDefectPrimitive_pos ha)
    (sourceDefectPrimitive_pos (ha.trans hab.le))).mp h
  nlinarith only [he]

end
end RHTower.ThetaCuspDefect
