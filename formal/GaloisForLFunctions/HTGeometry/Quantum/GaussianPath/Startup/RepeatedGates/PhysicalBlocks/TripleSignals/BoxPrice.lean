import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.DisjointBoxes

/-! # Gaussian cost of a calibrated three-site exchange -/
open MeasureTheory ProbabilityTheory Real Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
noncomputable section

private def pdfFloor (R : ℝ) := (sqrt (2*π))⁻¹ * exp (-(R^2)/2)

private theorem pdf_floor_pos (R : ℝ) : 0 < pdfFloor R := by
  unfold pdfFloor
  positivity

private theorem interval_mass {c r R : ℝ} (hr : 0≤r) (hc : |c|+r≤R) :
    ENNReal.ofReal (2*r*pdfFloor R) ≤ gaussianReal 0 1 (Set.Icc (c-r) (c+r)) := by
  rw [gaussianReal_apply _ one_ne_zero]
  have hl (x : ℝ) (hx : x∈Set.Icc (c-r) (c+r)) : ENNReal.ofReal (pdfFloor R) ≤ gaussianPDF 0 1 x := by
    have hx' : |x|≤R := abs_le.mpr ⟨by linarith only [hx.1,neg_abs_le c,hc],
      by linarith only [hx.2,le_abs_self c,hc]⟩
    have hsq : x^2≤R^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx' 2
    apply ENNReal.ofReal_le_ofReal
    rw [gaussianPDFReal,pdfFloor]
    simp only [NNReal.coe_one,mul_one,sub_zero]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith only [hsq])) (by positivity)
  refine (setLIntegral_mono' measurableSet_Icc hl).trans_eq' ?_
  rw [setLIntegral_const,Real.volume_Icc,show c+r-(c-r)=2*r by ring,
    ←ENNReal.ofReal_mul (pdf_floor_pos R).le,mul_comm]

/-- A lower bound on the exact probability that all 48 coefficients
fall in the calibrated box. -/
def packetProbabilityFloor (q r : ℝ) := (2*r*pdfFloor (|q|+r))^48

theorem packet_probability_pos {q r : ℝ} (hr : 0<r) : 0<packetProbabilityFloor q r :=
  pow_pos (mul_pos (mul_pos (by norm_num) hr) (pdf_floor_pos _)) _

theorem packet_probability_formula (q r : ℝ) :
    packetProbabilityFloor q r = (2*r/(sqrt (2*π)))^48 * exp (-24*(|q|+r)^2) := by
  unfold packetProbabilityFloor pdfFloor
  rw [←mul_assoc,mul_pow,←Real.exp_nat_mul]
  congr 2 <;> ring

theorem calibrated_box_mass (q : ℝ) {r : ℝ} (hr : 0≤r) :
    packetProbabilityFloor q r ≤ gaussianBoxMass
      (fun i => boxField q i-r) (fun i => boxField q i+r) := by
  let b := 2*r*pdfFloor (|q|+r)
  have hb : 0≤b := mul_nonneg (by positivity) (pdf_floor_pos _).le
  have hc (i : TripleBoxIndex) : |boxField q i|≤|q| := by
    unfold boxField
    split <;> simp [abs_nonneg]
  have hi (i : TripleBoxIndex) := interval_mass hr (add_le_add_right (hc i) r)
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
  change ENNReal.ofReal (b^48) ≤ (Measure.infinitePi _ ) _
  rw [Measure.infinitePi_eq_pi,Measure.pi_pi]
  have hcard : Fintype.card TripleBoxIndex=48 := by
    simp [TripleBoxIndex,PathPauliDirections,Fintype.card_prod,Fintype.card_sum]
  calc ENNReal.ofReal (b^48) = ∏ _i : TripleBoxIndex, ENNReal.ofReal b := by
         rw [prod_const,card_univ,hcard,ENNReal.ofReal_pow hb]
       _ ≤ _ := prod_le_prod' (fun i _ => hi i)

#print axioms calibrated_box_mass
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
