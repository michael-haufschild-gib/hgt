import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # Forecast intervals for the actual Gaussian first return after a robust crossing -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
noncomputable section

private theorem band_of_dilation {ι : Type*} [Fintype ι] (f : (ι→ℝ)→ℝ) (hf : Measurable f)
    (S : Set (ι→ℝ)) (hS : MeasurableSet S) {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t)
    (hS' : ∀ x, a • x ∈ S → x∈S) (hscale : ∀ x, a*f (a • x)=f x) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    μ.real {x∈S | f x ∈ Ioc t (a*t)} ≤
      (1-(a^Fintype.card ι)⁻¹)*μ.real {x∈S | t < f x} := by
  intro μ
  let E := {x∈S | t < f x}
  let G := {x∈S | a*t < f x}
  have hm : MeasurableSet E := hS.inter (measurableSet_lt measurable_const hf)
  have hG : MeasurableSet G := hS.inter (measurableSet_lt measurable_const hf)
  have hpos := zero_lt_one.trans_le ha
  have hpow : 0 < a^Fintype.card ι := pow_pos hpos _
  have hsub : G⊆E := fun _ hx => ⟨hx.1,(le_mul_of_one_le_left ht ha).trans_lt hx.2⟩
  have hmap : (fun x : ι→ℝ => a • x) ⁻¹' E ⊆ G := by
    intro x hx
    exact ⟨hS' x hx.1,(mul_lt_mul_of_pos_left hx.2 hpos).trans_eq (hscale x)⟩
  have hprice := (gaussian_dilation_comparison ha E hm).trans
    (mul_le_mul_of_nonneg_left (measureReal_mono (μ:=μ) hmap) hpow.le)
  have hlow : (a^Fintype.card ι)⁻¹*μ.real E ≤ μ.real G := by
    rw [←div_eq_inv_mul]
    exact (div_le_iff₀ hpow).mpr (by simpa only [mul_comm] using hprice)
  have he : {x∈S | f x ∈ Ioc t (a*t)}=E \ G := by
    ext x
    change (x∈S ∧ t < f x ∧ f x ≤ a*t) ↔ (x∈S ∧ t < f x) ∧ ¬(x∈S ∧ a*t < f x)
    constructor
    · exact fun h => ⟨⟨h.1,h.2.1⟩,fun hh => h.2.2.not_gt hh.2⟩
    · exact fun h => ⟨h.1.1,h.1.2,le_of_not_gt (fun hh => h.2 ⟨h.1.1,hh⟩)⟩
  rw [he,measureReal_sdiff hsub hG (measure_ne_top _ _)]
  change μ.real E-μ.real G ≤ (1-_)*μ.real E
  linarith only [hlow]

/-- Among samples still waiting at t whose first crossing exceeds u, the
fraction returning by at is at most one minus the inverse volume dilation.
This bound holds at every time and every pair of gate budgets. -/
theorem first_wait_survival_band (n j s : ℕ) {t u a : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (ha : 1 ≤ a) :
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n j (9/80)
    let Δ := crossingWait n j s
    μ.real {x | u < σ x ∧ Δ x ∈ Ioc t (a*t)} ≤
      (1-(a^Fintype.card (ChainLabel (n+2)))⁻¹)*μ.real {x | u < σ x ∧ t < Δ x} := by
  intro μ σ Δ
  let S := {x | u < σ x}
  have hp := zero_lt_one.trans_le ha
  have hS : MeasurableSet S := measurableSet_lt measurable_const (measurable_crossingOrigin ..)
  have hin (x) (hx : a • x∈S) : x∈S :=
    ((le_mul_of_one_le_left hu ha).trans_lt (mul_lt_mul_of_pos_left hx hp)).trans_eq
      (smul_crossingOrigin n j (9/80) hp x)
  simpa only [S,Set.mem_setOf_eq,μ,Fintype.card_fin] using band_of_dilation Δ (measurable_crossingWait ..) S hS ha ht hin
    (smul_crossingWait n j s hp)

#print axioms first_wait_survival_band
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
