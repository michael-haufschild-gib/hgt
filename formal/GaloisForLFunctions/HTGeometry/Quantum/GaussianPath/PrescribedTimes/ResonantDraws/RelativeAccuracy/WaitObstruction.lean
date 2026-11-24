import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateScalarProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.SmallTimeLaw.RelativeDensity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.DisorderTails

/-! # A necessary observation delay for posterior first-wait accuracy -/
open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
noncomputable section
open SharpOccupation

/-- Every positive delay from the true crossing has positive probability
of an empty reading. Positive Gaussian dilations preserve null events
and a sufficiently late reading has strictly positive limiting mass. -/
theorem positive_crossing_snapshot (k j : ℕ) {ε : ℝ} (hε : 0<ε) (hε' : ε<sqrt 2) :
    let n := k+1
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n j (9/80)
    ∀ t > (0:ℝ), 0<μ.real {x | pathGateDistance n 0 x (σ x+t)≤ε} := by
  intro n μ σ t ht
  let E (s : ℝ) := {x | pathGateDistance n 0 x (σ x+s)≤ε}
  have hm (s) : MeasurableSet (E s) := measurable_origin_event n 0 ε s σ (measurable_crossingOrigin ..)
  have hl := (gaussian_late_scalar_probability k j hε hε').2
  have hp : 0<((2^(k+3):ℕ):ℝ)*(physicalArc ε)^(2^(k+3)-1:ℕ) :=
    mul_pos (by positivity) (pow_pos (physicalArc_spec hε hε').1.1 _)
  obtain ⟨u,hu,hu'⟩ := ((hl.eventually_const_lt hp).and (eventually_gt_atTop (0:ℝ))).exists
  let a := u/t
  have ha : 0<a := div_pos hu' ht
  have he : (fun x : PrefixIndex n → ℝ => a • x) ⁻¹' E t = E u := by
    ext x
    change (pathGateDistance n 0 (a • x) (σ (a • x)+t)≤ε) ↔ _
    rw [distance_dilate,mul_add,smul_crossingOrigin n j (9/80) ha,div_mul_cancel₀ u ht.ne']
    rfl
  apply ENNReal.toReal_pos _ (measure_ne_top _ _)
  intro hn
  have hh := SmallTimeLaw.gaussian_inverse_scale_law (ι:=PrefixIndex n) (inv_pos.mpr ha)
  simp only [inv_inv] at hh
  have hz : μ (E u)=0 := by
    rw [←he,←Measure.map_apply (f:=fun x : PrefixIndex n → ℝ => a • x) (by fun_prop) (hm t),hh]
    exact withDensity_absolutelyContinuous _ _ hn
  exact hu.not_ge (show μ.real (E u)≤0 by rw [Measure.real,hz,ENNReal.toReal_zero])

/-- At the deadline equal to the observation delay, an empty reading has
already terminated every return clock. Two weak cuts leave prior tail
mass at least c/t¹⁸, uniformly in large prefix size. -/
theorem gaussian_first_wait_posterior_obstruction :
    ∃ c > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n P (9/80)
      ∀ t ≥ (1:ℝ), ∀ s≤P/2,
        let E := {x | pathGateDistance n 0 x (σ x+t)≤1/10}
        let B := {x | crossingWait n P s x≤t}
        0<μ.real E ∧ μ.real (B ∩ E)/μ.real E=1 ∧ c≤t^18*|μ.real (B ∩ E)/μ.real E-μ.real B| := by
  obtain ⟨c,hc,h⟩ := WeakBonds.gaussian_uniform_first_excursion_tail
  refine ⟨c,hc,?_⟩
  filter_upwards [h] with k hk
  intro n P μ σ t ht s hs E B
  have htol : (1/10:ℝ)<sqrt 2 := by
    nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  have ht' := zero_lt_one.trans_le ht
  have hp := positive_crossing_snapshot k P (by norm_num : (0:ℝ)<1/10) htol t ht'
  have hsub : E ⊆ B := fun x hx => (crossingWait_antitone (Nat.zero_le s) x).trans
    ((crossingWait_le_iff n P 0 x t).mpr ⟨_,⟨le_add_of_nonneg_right ht'.le,le_rfl⟩,hx⟩)
  have he : μ.real (B ∩ E)/μ.real E=1 := by rw [inter_eq_right.mpr hsub,div_self hp.ne']
  refine ⟨hp,he,?_⟩
  have hm : MeasurableSet B := measurableSet_le (measurable_crossingWait ..) measurable_const
  have htail : c≤t^18*μ.real Bᶜ := (hk t ht).trans (mul_le_mul_of_nonneg_left
    (measureReal_mono (fun y hy => (hy.2 s hs).not_ge)) (pow_nonneg ht'.le _))
  rw [measureReal_compl hm] at htail
  rw [he,abs_of_nonneg (sub_nonneg.mpr ((measureReal_mono (μ:=μ) (subset_univ B)).trans_eq probReal_univ))]
  exact htail

#print axioms positive_crossing_snapshot
#print axioms gaussian_first_wait_posterior_obstruction
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
