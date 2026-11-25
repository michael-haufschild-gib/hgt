import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns.CutoffPrice
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.PhysicalWidths
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.PlateauDelay

/-! # Early scalar returns from each prescribed spectral antipode -/

open Set MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
open PrescribedTimes AntipodalHorizons
noncomputable section

theorem measurable_turnEvent (k w : ℕ) (ε : ℝ) :
    MeasurableSet (turnEvent (k+1) w ε) := by
  let n := k+1
  have hg := (continuous_prefix_width k).measurable
  have ht : Measurable (fullTurn n w) := by
    unfold fullTurn
    exact (measurable_const (a:=(w:ℝ)*(2*π))).div hg
  let v := fun x : PrefixIndex n→ℝ => (x,fullTurn n w x)
  let f := fun p : (PrefixIndex n→ℝ) × ℝ => pathGateDistance n 0 p.1 p.2
  have hv : Measurable v := (measurable_id' (α:=PrefixIndex n→ℝ)).prodMk ht
  have hf : Measurable f := (continuous_distance n 0).measurable
  exact (measurableSet_le (measurable_const (a:=(2:ℝ))) hg).inter
    (measurableSet_le (hf.comp hv) (measurable_const (a:=ε)))

private theorem hit_gives_wait (k m w : ℕ) (hm : m+1≤w) {ε : ℝ} (hε : 0<ε)
    (ω : PathPauliDisorder) :
    let u := pathPauliDisorderShell ω (k+1)
    let x := fun i => u (pathCoeffEquiv (k+1) i)
    x∈turnEvent (k+1) w ε → elapsed k m ε ω≤π*((w:ℝ)-((m:ℝ)+1/2)) := by
  intro u x hx
  let g := circuitHamiltonianSpectralWidth (prefixGenerator (k+1) x)
  have hg : 2≤g := hx.1
  have hp : 0<g := zero_lt_two.trans_le hg
  let a := origin k m ω
  let t := fullTurn (k+1) w x
  have ha : a=(((m:ℝ)+1/2)*(2*π))/g := by
    change date _ _ _ _ _ = _
    rw [show g=_ from intrinsic_sorted_width k x]
    simp only [date,add_zero,mul_div_assoc,x,u]
  have ht : t-a=((w:ℝ)-((m:ℝ)+1/2))*(2*π)/g := by
    rw [ha]
    change (w:ℝ)*(2*π)/g-_=_
    ring
  have hw : 0≤(w:ℝ)-((m:ℝ)+1/2) := by
    have h : (m:ℝ)+1≤(w:ℝ) := by exact_mod_cast hm
    linarith only [h]
  have hfit : HasProjectiveCircuitApproximation (k+3) ε 0
      (unitaryEvolution (pathHamiltonian u) t) := by
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
    have hd := hx.2
    change Metric.infDist (unitaryEvolution (numberedGenerator (k+1) x) t) _ ≤ ε at hd
    rw [numberedGenerator_shell u] at hd
    exact hd
  have hta : a≤t := sub_nonneg.mp ((div_nonneg (mul_nonneg hw two_pi_pos.le) hp.le).trans_eq ht.symm)
  have hfirst := (PrecisionReturns.firstVisit_isLeast (register k ω) a 0 hε).2 ⟨hta,hfit⟩
  change PrecisionReturns.firstVisit (register k ω) a 0 ε-a ≤ _
  refine (sub_le_sub_right hfirst a).trans ?_
  rw [ht,div_le_iff₀ hp]
  have hh := mul_le_mul_of_nonneg_left hg (mul_nonneg pi_pos.le hw)
  linarith only [hh]

private theorem fullTurnMass_le_wait (k w : ℕ) {ε : ℝ} (hε : 0<ε) :
    fullTurnMass (k+1) w ε ≤ pathPauliDisorderLaw.real
      {ω | ∀ j : ℕ, j<w → elapsed k j ε ω≤π*((w:ℝ)-((j:ℝ)+1/2))} := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  change (Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1).real (turnEvent _ w ε) ≤ _
  have he := (gaussian_pauli_prefix_coordinates_law (k+1)).measureReal_preimage
    (measurable_turnEvent k w ε).nullMeasurableSet
  exact he.symm.le.trans (measureReal_mono
    (fun {ω} hω j hj => hit_gives_wait k j w hj hε ω hω) (measure_ne_top _ _))

/-- Every prescribed antipode has a first physical scalar wait with a
finite probability floor. At the selected turn's immediately preceding
antipode the same floor applies to a wait of at most π/2 time units. -/
theorem gaussian_two_prescribed_wait_floors {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℕ, 1≤B ∧ ∃ c>(0:ℝ), ∀ k m : ℕ,
      let M := B^(blockDimension (k+1))
      ∃ w∈Icc (m+1) ((m+1)*M),
        c≤((m:ℝ)+1)^9*(M:ℝ)^10*pathPauliDisorderLaw.real
          {ω | ∀ j : ℕ, j<w → elapsed k j ε ω≤π*((w:ℝ)-((j:ℝ)+1/2))} := by
  obtain ⟨B,hB,c,hc,h⟩ := gaussian_full_turn_price hε
  refine ⟨B,hB,c,hc,?_⟩
  intro k m M
  obtain ⟨w,hw,hh⟩ := h (k+1) m
  refine ⟨w,hw,?_⟩
  exact hh.trans (mul_le_mul_of_nonneg_left (fullTurnMass_le_wait k w hε) (by positivity))

#print axioms gaussian_two_prescribed_wait_floors
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
