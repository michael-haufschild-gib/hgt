import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # Direction-based forecasts of the distinguished first wait -/
open MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.AngularPrediction
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Success is the loss of threshold mass under one dilation. The same
identity applies when the budget and the forecast are chosen from the
coupling direction, provided the resulting clock has degree minus one. -/
theorem forecast_mass_difference (F g : (ι → ℝ) → ℝ) (hF : Measurable F) (hg : Measurable g)
    (h₀ : ∀ x, 0 ≤ g x) {a : ℝ} (ha : 1 ≤ a)
    (hscale : ∀ x, a*F (a • x)=F x) (hang : ∀ x, g (a • x)=g x) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    let E := {x | g x < F x}
    μ.real {x | g x < F x ∧ F x ≤ a*g x} =
      μ.real E-μ.real ((fun x : ι → ℝ => a • x) ⁻¹' E) := by
  intro μ E
  let G := {x | a*g x < F x}
  have hp := zero_lt_one.trans_le ha
  have hm : MeasurableSet G := measurableSet_lt (hg.const_mul a) hF
  have hs : G ⊆ E := fun x hx => (le_mul_of_one_le_left (h₀ x) ha).trans_lt hx
  have hg' : (fun x : ι → ℝ => a • x) ⁻¹' E = G := by
    ext x
    change g (a • x) < F (a • x) ↔ a*g x < F x
    rw [hang,←hscale x]
    exact (mul_lt_mul_iff_right₀ hp).symm
  have he : {x | g x < F x ∧ F x ≤ a*g x} = E \ G := by
    ext x
    change (g x < F x ∧ F x ≤ a*g x) ↔ g x < F x ∧ ¬ a*g x < F x
    rw [not_lt]
  rw [he,hg',measureReal_sdiff hs hm (measure_ne_top _ _)]

/-- A forecaster who sees only direction can choose any radial band.
The physical clock is strictly positive on the directions where the band
can score. -/
def radialForecast (F : (ι → ℝ) → ℝ) (a r : ℝ) (x : ι → ℝ) : ℝ :=
  F x*‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖/(a*r)

theorem radialForecast_smul {F : (ι → ℝ) → ℝ} (hom : ∀ b > (0:ℝ), ∀ x, b*F (b • x)=F x)
    (a r : ℝ) {b : ℝ} (hb : 0 < b) (x : ι → ℝ) : radialForecast F a r (b • x)=radialForecast F a r x := by
  change F (b • x)*‖b • (WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖/(a*r)=_
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hb]
  unfold radialForecast
  rw [←mul_assoc,mul_comm (F (b • x)) b,hom b hb]

theorem radialForecast_score (F : (ι → ℝ) → ℝ) (x : ι → ℝ) (hx : 0 < F x)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (radialForecast F a r x < F x ∧ F x ≤ a*radialForecast F a r x) ↔
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ∈ Ico r (a*r) := by
  let R := ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖
  have har := mul_pos ha hr
  change (F x*R/(a*r) < F x ∧ F x ≤ a*(F x*R/(a*r))) ↔ r ≤ R ∧ R < a*r
  rw [show a*(F x*R/(a*r))=F x*R/r by field_simp [ha.ne',hr.ne'],div_lt_iff₀ har,le_div_iff₀ hr,
    mul_lt_mul_iff_right₀ hx,mul_le_mul_iff_right₀ hx,and_comm]

#print axioms forecast_mass_difference
#print axioms radialForecast_score
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.AngularPrediction
