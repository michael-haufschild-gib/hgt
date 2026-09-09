import GaloisForLFunctions.HTGeometry.HardyBoundaryCayleyIdentification

/-!
# Exact local zero-set transport through the boundary Cayley isometry

The actual half-density never vanishes, and the standard Cauchy measure has
the same null sets as Lebesgue measure. The explicit inverse chart identifies
real neighborhoods with circle arcs at every finite Cayley point.
-/

open MeasureTheory Complex Filter Topology Metric Set
open scoped ENNReal NNReal lp
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem realCayley_ne_one (x : ℝ) : realCayley x ≠ 1 := by
  intro h
  have he : (x : ℂ) - I = (x : ℂ) + I :=
    (div_eq_one_iff_eq (real_add_I_ne_zero x)).1 h
  have hi := congrArg Complex.im he
  norm_num at hi

private def cayleyInverseChart (z : ℂ) : ℝ := (I * (1+z) / (1-z)).re

private theorem cayleyInverseChart_realCayley (x : ℝ) : cayleyInverseChart (realCayley x) = x := by
  have hd : 1 - realCayley x ≠ 0 := sub_ne_zero.mpr (Ne.symm (realCayley_ne_one x))
  have he : I * (1 + realCayley x) / (1 - realCayley x) = (x : ℂ) := by
    apply (div_eq_iff hd).2
    unfold realCayley
    field_simp [real_add_I_ne_zero x]
    ring
  exact congrArg Complex.re he

private theorem cayleyInverseChart_continuousAt (c : ℝ) :
    ContinuousAt cayleyInverseChart (realCayley c) := by
  unfold cayleyInverseChart
  have hc : ContinuousAt (fun z : ℂ => I * (1+z) / (1-z)) (realCayley c) :=
    (continuousAt_const.mul (continuousAt_const.add continuousAt_id)).div
    (continuousAt_const.sub continuousAt_id)
    (sub_ne_zero.mpr (Ne.symm (realCayley_ne_one c)))
  exact Complex.continuous_re.continuousAt.comp hc

/-- A positive circle arc around any finite Cayley point pulls back inside any prescribed real gap. -/
theorem exists_circleCayley_arc_inside_realGap (c a : ℝ) :
    ∃ b : ℝ, ∀ x : ℝ,
      dist (circleCayley x : ℂ) (circleCayley c : ℂ) < Real.exp b → dist x c < Real.exp a := by
  have ht : Tendsto cayleyInverseChart (𝓝 (realCayley c)) (𝓝 c) := by
    simpa only [cayleyInverseChart_realCayley] using (cayleyInverseChart_continuousAt c).tendsto
  have hnear := ht.eventually (Metric.ball_mem_nhds c (Real.exp_pos a))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨Real.log r,fun x hx => ?_⟩
  have hm : realCayley x ∈ ball (realCayley c) r := by
    change dist (realCayley x) (realCayley c) < r
    simpa only [circleCayley_coe,Real.exp_log hr] using hx
  have h := hball hm
  change dist (cayleyInverseChart (realCayley x)) c < Real.exp a at h
  rwa [cayleyInverseChart_realCayley] at h

private theorem cayley_halfDensity_ne_zero (x : ℝ) :
    (Real.sqrt Real.pi : ℂ)⁻¹ * ((x : ℂ) + I)⁻¹ ≠ 0 :=
  mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))))
    (inv_ne_zero (real_add_I_ne_zero x))

private theorem measurable_arc_zero_predicate (f : Lp ℂ 2 circleLebesgue) (c b : ℝ) :
    MeasurableSet {ζ : Circle | dist (ζ : ℂ) (circleCayley c : ℂ) < Real.exp b → f ζ = 0} := by
  simp only [imp_iff_not_or]
  have harc : MeasurableSet {ζ : Circle | dist (ζ : ℂ) (circleCayley c : ℂ) < Real.exp b} := by
    change @MeasurableSet Circle (borel Circle)
      {ζ : Circle | dist (ζ : ℂ) (circleCayley c : ℂ) < Real.exp b}
    letI : MeasurableSpace Circle := borel Circle
    rw [show {ζ : Circle | dist (ζ : ℂ) (circleCayley c : ℂ) < Real.exp b} =
      (fun ζ : Circle => (ζ : ℂ)) ⁻¹' ball (circleCayley c : ℂ) (Real.exp b) by ext ζ; rfl]
    exact @IsOpen.measurableSet Circle _ _ (borel Circle) ⟨le_rfl⟩
      (isOpen_ball.preimage continuous_subtype_val)
  exact harc.compl.union
    (measurableSet_eq_fun (Lp.stronglyMeasurable f).measurable measurable_const)

private theorem line_gap_gives_circle_arc (f : Lp ℂ 2 circleLebesgue) (c a : ℝ)
    (hgap : ∀ᵐ x : ℝ ∂volume, dist x c < Real.exp a → circleLineCayleyIsometry f x = 0) :
    ∃ b : ℝ, ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) (circleCayley c : ℂ) < Real.exp b → f ζ = 0 := by
  obtain ⟨b,hb⟩ := exists_circleCayley_arc_inside_realGap c a
  refine ⟨b,?_⟩
  have hp : ∀ᵐ x : ℝ ∂volume,
      dist (circleCayley x : ℂ) (circleCayley c : ℂ) < Real.exp b → f (circleCayley x) = 0 := by
    filter_upwards [hgap,circleLineCayleyIsometry_ae_explicit f] with x hx he
    intro hnear
    have hz := he.symm.trans (hx (hb x hnear))
    exact (mul_eq_zero.mp hz).resolve_left (cayley_halfDensity_ne_zero x)
  have hw := (withDensity_absolutelyContinuous (volume : Measure ℝ)
    (realDensity standardCauchyWeight)).ae_le hp
  have hm := (ae_map_iff circleCayley_weighted_measurePreserving.measurable.aemeasurable
    (measurable_arc_zero_predicate f c b)).2 hw
  rw [circleCayley_weighted_measurePreserving.map_eq] at hm
  exact hm

private theorem circle_arc_gives_line_gap (f : Lp ℂ 2 circleLebesgue) (c b : ℝ)
    (hgap : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) (circleCayley c : ℂ) < Real.exp b → f ζ = 0) :
    ∃ a : ℝ, ∀ᵐ x : ℝ ∂volume, dist x c < Real.exp a → circleLineCayleyIsometry f x = 0 := by
  have ht : Tendsto realCayley (𝓝 c) (𝓝 (realCayley c)) := continuous_realCayley.continuousAt.tendsto
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (ht.eventually
    (Metric.ball_mem_nhds (realCayley c) (Real.exp_pos b)))
  refine ⟨Real.log r,?_⟩
  have hw := circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae.eventually hgap
  have hp := (ae_withDensity_iff (measurable_realDensity measurable_standardCauchyWeight)).1 hw
  filter_upwards [hp,circleLineCayleyIsometry_ae_explicit f] with x hx he
  intro hnear
  have hreal : x ∈ ball c r := by simpa only [mem_ball,Real.exp_log hr] using hnear
  have hc : dist (circleCayley x : ℂ) (circleCayley c : ℂ) < Real.exp b := hball hreal
  have hd : realDensity standardCauchyWeight x ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (standardCauchyWeight_pos x))
  rw [he,hx hd hc,mul_zero]

/-- The actual boundary Cayley isometry preserves and reflects the existence of a local a.e. zero gap. -/
theorem circleLineCayleyIsometry_local_zero_iff (f : Lp ℂ 2 circleLebesgue) (c : ℝ) :
    (∃ a : ℝ, ∀ᵐ x : ℝ ∂volume,
      dist x c < Real.exp a → circleLineCayleyIsometry f x = 0) ↔
    (∃ b : ℝ, ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) (circleCayley c : ℂ) < Real.exp b → f ζ = 0) := by
  constructor
  · rintro ⟨a,ha⟩
    exact line_gap_gives_circle_arc f c a ha
  · rintro ⟨b,hb⟩
    exact circle_arc_gives_line_gap f c b hb

end
end GaloisForLFunctions.HTGeometry.FokasLenells
