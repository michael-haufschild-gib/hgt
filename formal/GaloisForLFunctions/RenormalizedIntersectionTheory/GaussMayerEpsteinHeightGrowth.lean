import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinHeatRepresentation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Local uniform height growth for the actual continued Epstein field.
The Gaussian bounds reduce all height dependence to one sublinear power;
continuity controls the remaining spectral coefficient away from its poles. -/

open Complex Real Set Filter Topology MeasureTheory
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerEpsteinHeatBounds MayerEpsteinQuadrants MayerEpsteinHeatRepresentation
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinHeightGrowth

private def normalizer (w : ℂ) : ℂ :=
  (Real.pi : ℂ)^(w/2)/2*(Complex.Gamma (w/2))⁻¹

private theorem differentiable_normalizer : Differentiable ℂ normalizer := by
  have hn : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp : Differentiable ℂ (fun w : ℂ => (Real.pi : ℂ)^(w/2)) := by
    simp only [Complex.cpow_def_of_ne_zero hn]
    fun_prop
  exact (hp.div_const 2).mul
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.div_const 2))

/-- Spectral coefficient in the Gaussian height estimate. -/
def growthCoefficient (η β : ℝ) (w : ℂ) : ℝ :=
  ‖normalizer w‖*((thetaSum 1+1)*thetaMoment (2-β)+thetaSum 1*thetaMoment 0+
    thetaMoment η+2/‖w‖+2/‖w-2‖)

private theorem continuousAt_growthCoefficient (η β : ℝ) {w : ℂ}
    (hw0 : w ≠ 0) (hw2 : w ≠ 2) : ContinuousAt (growthCoefficient η β) w := by
  unfold growthCoefficient
  have hN : ContinuousAt (fun z : ℂ => ‖normalizer z‖) w :=
    differentiable_normalizer.continuous.continuousAt.norm
  have h0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have h2 : ‖w-2‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw2)
  exact hN.mul (((continuousAt_const.add
    (continuousAt_const.div continuousAt_id.norm h0))).add
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const).norm h2))

private theorem growthCoefficient_nonneg {η β : ℝ} (w : ℂ) :
    0 ≤ growthCoefficient η β w := by
  have hθ : 0 ≤ thetaSum 1 := (one_le_thetaSum zero_lt_one).trans' zero_le_one
  have hM0 := thetaMoment_nonneg (0 : ℝ)
  have hMη := thetaMoment_nonneg η
  have hMβ := thetaMoment_nonneg (2-β)
  unfold growthCoefficient
  positivity

/-- A sublinear height power bounds the field with an explicit spectral coefficient. -/
theorem norm_epsteinField_le_power {w : ℂ} (hw2 : w ≠ 2) {η β y : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hηw : η ≤ w.re) (hβ : 1 < β)
    (hwβ : w.re ≤ β) (hy : 1 ≤ y) :
    ‖epsteinField w y‖ ≤ growthCoefficient η β w*y^(1-η) := by
  have hw0 : w ≠ 0 := by intro h; simp only [h,Complex.zero_re] at hηw; linarith only [hη0,hηw]
  have h2 : 0 < ‖w-2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw2)
  have hpole : 2/(y*‖w-2‖) ≤ 2/‖w-2‖ := by
    apply div_le_div_of_nonneg_left (by norm_num) h2
    nlinarith only [hy,h2]
  have hx : 1 ≤ y^(1-η) := Real.one_le_rpow hy (by linarith only [hη1])
  have hθ : 0 ≤ thetaSum 1 := (one_le_thetaSum zero_lt_one).trans' zero_le_one
  have hM0 := thetaMoment_nonneg (0 : ℝ)
  have hMη := thetaMoment_nonneg η
  have hMβ := thetaMoment_nonneg (2-β)
  have hrest : 0 ≤ (thetaSum 1+1)*thetaMoment (2-β)+thetaSum 1*thetaMoment 0+
      2/‖w‖+2/‖w-2‖ := by positivity
  have hscale := mul_nonneg (sub_nonneg.mpr hx) hrest
  have hbound := norm_epsteinField_le hw2 hη0 hη1 hηw hβ hwβ hy
  have hn : (Real.pi : ℂ)^(w/2)/(2*Complex.Gamma (w/2))=normalizer w := by
    unfold normalizer
    simp only [div_eq_mul_inv,mul_inv]
    ring
  rw [hn] at hbound
  unfold growthCoefficient
  calc
    _ ≤ _ := hbound
    _ ≤ ‖normalizer w‖*((thetaSum 1+1)*thetaMoment (2-β)+thetaSum 1*thetaMoment 0+
          thetaMoment η+2/‖w‖+2/‖w-2‖)*y^(1-η) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      nlinarith only [hpole,hscale]

/-- The spectral coefficient is uniformly bounded on a ball with fixed real-part margins. -/
theorem locally_bounded_growthCoefficient {w₀ : ℂ} (hw₀ : 0 < w₀.re) (hw₂ : w₀ ≠ 2) :
    ∃ η β C r : ℝ, 0 < η ∧ η < 1 ∧ 1 < β ∧ 0 < C ∧ 0 < r ∧
      ∀ w ∈ Metric.ball w₀ r, η ≤ w.re ∧ w.re ≤ β ∧ w ≠ 2 ∧
        growthCoefficient η β w ≤ C := by
  let η : ℝ := min 1 w₀.re/2
  let β : ℝ := w₀.re+2
  have hη0 : 0 < η := div_pos (lt_min zero_lt_one hw₀) (by norm_num)
  have hη1 : η < 1 := by dsimp [η]; linarith only [min_le_left (1 : ℝ) w₀.re]
  have hηw : η < w₀.re := by dsimp [η]; linarith only [min_le_right (1 : ℝ) w₀.re,hw₀]
  have hβ : 1 < β := by dsimp [β]; linarith only [hw₀]
  have hwβ : w₀.re < β := by dsimp [β]; linarith
  have hw0 : w₀ ≠ 0 := by intro h; simp [h] at hw₀
  have hc := continuousAt_growthCoefficient η β hw0 hw₂
  have hev : ∀ᶠ w in 𝓝 w₀, η < w.re ∧ w.re < β ∧ w ≠ 2 ∧
      growthCoefficient η β w < growthCoefficient η β w₀+1 := by
    have hlow : ∀ᶠ w in 𝓝 w₀, η < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hηw
    have hupp : ∀ᶠ w in 𝓝 w₀, w.re < β :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hwβ
    have hcoef : ∀ᶠ w in 𝓝 w₀,
        growthCoefficient η β w < growthCoefficient η β w₀+1 :=
      hc.eventually (isOpen_Iio.mem_nhds (lt_add_one (growthCoefficient η β w₀)))
    filter_upwards [hlow,hupp,isOpen_ne.mem_nhds hw₂,hcoef] with w h1 h2 h3 h4
    exact ⟨h1,h2,h3,h4⟩
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨η,β,growthCoefficient η β w₀+1,r,hη0,hη1,hβ,?_,hr,?_⟩
  · linarith only [growthCoefficient_nonneg (η := η) (β := β) w₀]
  · intro w hw
    obtain ⟨h1,h2,h3,h4⟩ := hball hw
    exact ⟨h1.le,h2.le,h3,h4.le⟩

/-- Uniform sublinear growth on a spectral ball inside the source half-plane. -/
theorem locally_uniform_height_growth {w₀ : ℂ} (hw₀ : 0 < w₀.re) (hw₂ : w₀ ≠ 2) :
    ∃ η C r : ℝ, 0 < η ∧ η < 1 ∧ 0 < C ∧ 0 < r ∧
      ∀ w ∈ Metric.ball w₀ r, η ≤ w.re ∧ w ≠ 2 ∧
        ∀ y : ℝ, 1 ≤ y → ‖epsteinField w y‖ ≤ C*y^(1-η) := by
  obtain ⟨η,β,C,r,hη0,hη1,hβ,hC,hr,hball⟩ := locally_bounded_growthCoefficient hw₀ hw₂
  refine ⟨η,C,r,hη0,hη1,hC,hr,?_⟩
  intro w hw
  obtain ⟨h1,h2,h3,h4⟩ := hball w hw
  refine ⟨h1,h3,fun y hy => ?_⟩
  exact (norm_epsteinField_le_power h3 hη0 hη1 h1 hβ h2 hy).trans
    (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (zero_lt_one.trans_le hy).le _))

#print axioms norm_epsteinField_le_power
#print axioms locally_bounded_growthCoefficient
#print axioms locally_uniform_height_growth
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinHeightGrowth
