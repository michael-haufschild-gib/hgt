import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheNumberOfMeasurementsAtEachZeroDepth
import Mathlib.Analysis.Convex.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# A convex summability gauge for transverse displacement

When every positive depth leaves only finitely many points, integrate the
reciprocal of one plus the number of points at or above that depth. This
strictly increasing convex gauge assigns total mass at most one half to
every finite sample of distinct points. Conversely, a positive increasing
gauge with bounded sample mass forces every positive depth layer finite.
The reciprocal count implements the superlevel-set construction from
Choquet integration directly on the zero configuration.
-/

noncomputable section
open Set Filter MeasureTheory Finset Zeta23
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
namespace GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

private def closedDepthLayer (Z : ZeroConfig) (t : ℝ) :=
  {z | z ∈ Z.carrier ∧ t ≤ rightDisplacement z}

private theorem closedLayer_finite (Z : ZeroConfig) (h : ApproachesLine Z) {t : ℝ} (ht : 0 < t) :
    (closedDepthLayer Z t).Finite := by
  apply (h (t/2) (half_pos ht)).subset
  intro z hz
  obtain ⟨hz,hz'⟩ := hz
  have hx : t/2 < max (z.re-1/2) 0 := (half_lt_self ht).trans_le hz'
  have hr := (lt_max_iff.mp hx).resolve_right (not_lt.mpr (half_pos ht).le)
  exact ⟨hz,by linarith only [hr]⟩

private def layerSlope (Z : ZeroConfig) (t : ℝ) : ℝ :=
  if 0 < t then (1+((closedDepthLayer Z t).ncard:ℝ))⁻¹ else 0

/-- Primitive of the reciprocal count of all points at or above the depth.
The closed threshold includes ties at the depth of an observed point. -/
def displacementGauge (Z : ZeroConfig) (t : ℝ) := ∫ u in (0:ℝ)..t, layerSlope Z u

private theorem slope_mem (Z : ZeroConfig) (t : ℝ) : layerSlope Z t ∈ Set.Icc (0:ℝ) 1 := by
  rw [layerSlope]
  split
  · exact ⟨by positivity,inv_le_one_of_one_le₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))⟩
  · exact ⟨le_rfl,zero_le_one⟩

private theorem slope_mono (Z : ZeroConfig) (hz : ApproachesLine Z) : Monotone (layerSlope Z) := by
  intro x y hxy
  by_cases hx : 0 < x
  · have hy := hx.trans_le hxy
    have hsub : closedDepthLayer Z y ⊆ closedDepthLayer Z x := fun z h => ⟨h.1,hxy.trans h.2⟩
    rw [layerSlope,if_pos hx,layerSlope,if_pos hy]
    exact inv_anti₀ (by positivity) (add_le_add (le_refl (1:ℝ)) (Nat.cast_le.mpr
      (Set.ncard_le_ncard hsub (closedLayer_finite Z hz hx))))
  · rw [layerSlope,if_neg hx]
    exact (slope_mem Z y).1

private theorem gauge_increment (Z : ZeroConfig) (h : ApproachesLine Z) (x y : ℝ) :
    displacementGauge Z y-displacementGauge Z x = ∫ t in x..y, layerSlope Z t := by
  let hm := slope_mono Z h
  exact sub_eq_iff_eq_add.mpr ((intervalIntegral.integral_add_adjacent_intervals
    (hm.intervalIntegrable (μ:=volume) (a:=0) (b:=x)) (hm.intervalIntegrable (μ:=volume) (a:=x) (b:=y))).symm.trans
      (add_comm _ _))

private theorem slope_bounds_increment (Z : ZeroConfig) (h : ApproachesLine Z) {x y : ℝ} (hxy : x ≤ y) :
    (y-x)*layerSlope Z x ≤ displacementGauge Z y-displacementGauge Z x ∧
      displacementGauge Z y-displacementGauge Z x ≤ (y-x)*layerSlope Z y := by
  let hm := slope_mono Z h
  rw [gauge_increment Z h]
  have hlo := intervalIntegral.integral_mono_on (μ:=volume) hxy intervalIntegrable_const
    hm.intervalIntegrable (fun t ht => hm ht.1)
  have hhi := intervalIntegral.integral_mono_on (μ:=volume) hxy hm.intervalIntegrable
    intervalIntegrable_const (fun t ht => hm ht.2)
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using And.intro hlo hhi

/-- The canonical gauge is convex, nonexpansive and strictly increasing
on nonnegative depths, even when the full off-line set is infinite. -/
theorem displacementGauge_regular (Z : ZeroConfig) (h : ApproachesLine Z) :
    displacementGauge Z 0=0 ∧ ConvexOn ℝ Set.univ (displacementGauge Z) ∧
    StrictMonoOn (displacementGauge Z) (Set.Ici 0) ∧
    ∀ x y : ℝ, x ≤ y → displacementGauge Z y-displacementGauge Z x ∈ Set.Icc 0 (y-x) := by
  have hinc {x y : ℝ} (hxy : x ≤ y) := slope_bounds_increment Z h hxy
  have hmono : Monotone (displacementGauge Z) := fun x y hxy => sub_nonneg.mp
    ((mul_nonneg (sub_nonneg.mpr hxy) (slope_mem Z x).1).trans (hinc hxy).1)
  refine ⟨by simp [displacementGauge],convexOn_of_slope_mono_adjacent convex_univ ?_,?_,?_⟩
  · intro x y z _ _ hxy hyz
    refine ((div_le_iff₀ (sub_pos.mpr hxy)).mpr ?_).trans ((le_div_iff₀ (sub_pos.mpr hyz)).mpr ?_)
    · simpa only [mul_comm (layerSlope Z y)] using (hinc hxy.le).2
    · simpa only [mul_comm (layerSlope Z y)] using (hinc hyz.le).1
  · intro x hx y _ hxy
    let m := (x+y)/2
    have hxm : x < m := by dsimp only [m]; linarith only [hxy]
    have hmy : m < y := by dsimp only [m]; linarith only [hxy]
    have hm0 : 0 < m := (show 0 ≤ x from hx).trans_lt hxm
    have hw : 0 < layerSlope Z m := by rw [layerSlope,if_pos hm0]; positivity
    exact (hmono hxm.le).trans_lt (sub_pos.mp ((mul_pos (sub_pos.mpr hmy) hw).trans_le (hinc hmy.le).1))
  · intro x y hxy
    exact ⟨sub_nonneg.mpr (hmono hxy),((hinc hxy).2).trans (mul_le_of_le_one_right
      (sub_nonneg.mpr hxy) (slope_mem Z y).2)⟩

/-- Uniform total gauge mass at most the half-width of the critical strip.
At each positive depth, integrating the superlevel count cancels its
normalizing denominator. -/
theorem finite_sum_displacementGauge (Z : ZeroConfig) (h : ApproachesLine Z)
    (S : Finset ℂ) (hS : (S : Set ℂ) ⊆ Z.carrier) :
    (∑ z ∈ S, displacementGauge Z (rightDisplacement z)) ≤ 1/2 := by
  classical
  let f (z : ℂ) := (Set.Iic (rightDisplacement z)).indicator (layerSlope Z)
  let hm := slope_mono Z h
  have hi (z : ℂ) : IntervalIntegrable (f z) volume 0 (1/2) :=
    intervalIntegrable_iff.mpr ((hm.intervalIntegrable (μ:=volume) (a:=0) (b:=1/2)).def'.indicator measurableSet_Iic)
  have hx (z : ℂ) (hz : z ∈ S) : rightDisplacement z ∈ Set.Icc (0:ℝ) (1/2) := by
    refine ⟨le_max_right _ _,max_le ?_ (by norm_num)⟩
    linarith only [(Z.strip z (hS hz)).2]
  have hs : (∑ z ∈ S, displacementGauge Z (rightDisplacement z)) =
      ∫ t in (0:ℝ)..(1/2), ∑ z ∈ S, f z t := by
    rw [intervalIntegral.integral_finsetSum (fun z _ => hi z)]
    exact sum_congr rfl fun z hz => (intervalIntegral.integral_indicator (f:=layerSlope Z) (hx z hz)).symm
  have hpt (t : ℝ) : (∑ z ∈ S, f z t) ≤ 1 := by
    let T := S.filter (fun z => t ≤ rightDisplacement z)
    have he : (∑ z ∈ S, f z t) = T.card*layerSlope Z t := by
      calc _ = ∑ z ∈ T, layerSlope Z t := by
              rw [sum_filter]
              exact sum_congr rfl fun z _ => rfl
        _ = _ := by simp
    rw [he,layerSlope]
    split
    · rename_i ht
      have hsub : (T:Set ℂ) ⊆ closedDepthLayer Z t := fun z hz =>
        ⟨hS (mem_filter.mp hz).1,(mem_filter.mp hz).2⟩
      have hn := Set.ncard_le_ncard hsub (closedLayer_finite Z h ht)
      rw [Set.ncard_coe_finset] at hn
      rw [←div_eq_mul_inv,div_le_one (by positivity)]
      linarith only [show (T.card:ℝ) ≤ (closedDepthLayer Z t).ncard by exact_mod_cast hn]
    · simp
  rw [hs]
  have hd := intervalIntegral.integral_mono_on (μ:=volume) (by norm_num : (0:ℝ) ≤ 1/2)
    (IntervalIntegrable.sum S fun z _ => hi z) intervalIntegrable_const (fun t _ => hpt t)
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] using hd

/-- A convex gauge of slope at most one, positive at every positive
depth, bounds the total displacement mass over all finite samples. -/
def hasSummableConvexDisplacementGauge (Z : ZeroConfig) : Prop :=
  ∃ g : ℝ → ℝ, g 0=0 ∧ ConvexOn ℝ Set.univ g ∧ StrictMonoOn g (Set.Ici 0) ∧
    (∀ x y : ℝ, x ≤ y → g y-g x ∈ Set.Icc 0 (y-x)) ∧
    ∀ S : Finset ℂ, (S:Set ℂ) ⊆ Z.carrier → (∑ z ∈ S, g (rightDisplacement z)) ≤ 1/2

/-- Approach to the critical line is equivalent to bounded total gauge mass. -/
theorem approach_iff_convex_gauge (Z : ZeroConfig) :
    ApproachesLine Z ↔ hasSummableConvexDisplacementGauge Z := by
  classical
  constructor
  · intro h
    obtain ⟨h0,hcv,hs,hl⟩ := displacementGauge_regular Z h
    exact ⟨_,h0,hcv,hs,hl,finite_sum_displacementGauge Z h⟩
  · rintro ⟨g,h0,_,hs,_,hm⟩ t ht
    have hgt : 0 < g t := by
      simpa only [h0] using hs (by simp : (0:ℝ) ∈ Set.Ici 0) (show t ∈ Set.Ici 0 from ht.le) ht
    by_contra hinf
    obtain ⟨k,hk⟩ := exists_nat_gt ((1/2:ℝ)/g t)
    obtain ⟨U,hU,hf,hc⟩ := (show (rightOf Z t).Infinite from hinf).exists_subset_ncard_eq k
    let S := hf.toFinset
    have hcS : S.card=k := (Set.ncard_eq_toFinset_card U hf).symm.trans hc
    have hz (z : ℂ) (hz : z ∈ S) := hU (hf.mem_toFinset.mp hz)
    have hu := hm S (fun z h => (hz z h).1)
    have hh := sum_le_sum (s:=S) (f:=fun _ => g t) fun z h =>
      hs.monotoneOn ht.le (show rightDisplacement z ∈ Set.Ici 0 from le_max_right _ _)
        ((show t < z.re-1/2 by linarith only [(hz z h).2]).le.trans (le_max_left _ _))
    simp only [sum_const,nsmul_eq_mul,hcS] at hh
    linarith only [hu,hh,(div_lt_iff₀ hgt).mp hk]

theorem actual_approach_iff_convex_gauge : _root_.RHTower.BacklundConverse.ZerosApproachLine ↔
    hasSummableConvexDisplacementGauge zetaZeroConfig := by
  rw [←ZetaAbscissa.zetaZeroConfig_approachesLine_iff]
  exact approach_iff_convex_gauge _

#print axioms finite_sum_displacementGauge
#print axioms actual_approach_iff_convex_gauge

end GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
