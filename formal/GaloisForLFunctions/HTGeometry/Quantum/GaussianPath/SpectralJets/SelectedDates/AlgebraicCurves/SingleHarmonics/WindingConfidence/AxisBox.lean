import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NormalizedRadius.BulkEnergy

/-! # Independent Gaussian mass of a strong axis and a set of weak couplings -/

open Finset MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
open WeakBonds.NormalizedRadius
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A distinguished coefficient belongs to [1,2], exactly the specified
weak coordinates are restricted in size, and all others are free. -/
def axisBox (S : Finset ι) (j : ι) (δ : ℝ) : Set (ι→ℝ) :=
  Set.univ.pi fun i => if i∈S then Icc (-δ) δ else if i=j then Icc 1 2 else Set.univ

theorem axisBox_bounds (S : Finset ι) {j : ι} (hj : j∉S) {δ : ℝ} {x : ι→ℝ}
    (hx : x∈axisBox S j δ) : x j∈Icc 1 2 ∧ ∀ i∈S, |x i|≤δ := by
  constructor
  · simpa only [hj,if_false,if_true] using hx j (Set.mem_univ j)
  · intro i hi
    exact abs_le.mpr (by simpa only [hi,if_true,mem_Icc] using hx i (Set.mem_univ i))

/-- The ninth-power price of weakening one bond is independent of the
number of unrestricted Gaussian coefficients. -/
theorem axisBox_mass (S : Finset ι) {j : ι} (hj : j∉S) {δ : ℝ} (hδ : 0≤δ) (hδ' : δ≤1) :
    bulkMass*(2*gaussianDensityFloor*δ)^S.card ≤
      (Measure.pi fun _ : ι => gaussianReal 0 1).real (axisBox S j δ) := by
  let γ := gaussianReal 0 1
  letI : IsProbabilityMeasure γ := by dsimp only [γ]; infer_instance
  let B (i : ι) := if i∈S then Icc (-δ) δ else if i=j then Icc 1 2 else Set.univ
  change _ ≤ (Measure.pi (fun _ : ι => γ) (Set.univ.pi B)).toReal
  rw [Measure.pi_pi,ENNReal.toReal_prod,←Finset.prod_mul_prod_compl S (fun i => (γ (B i)).toReal)]
  have hweak : (∏ i∈S, (γ (B i)).toReal)=γ.real (Icc (-δ) δ)^S.card := by
    calc _ = ∏ _i∈S, γ.real (Icc (-δ) δ) := prod_congr rfl fun i hi => by simp only [B,hi,if_true,Measure.real]
         _ = _ := prod_const _
  have hstrong : (∏ i∈Sᶜ, (γ (B i)).toReal)=bulkMass := by
    rw [prod_eq_single j]
    · simp only [B,hj,if_false,if_true,bulkMass,γ,Measure.real]
    · intro i hi hij
      simp only [B,Finset.mem_compl.mp hi,if_false,hij,measure_univ,ENNReal.toReal_one]
    · exact fun h => (h (Finset.mem_compl.mpr hj)).elim
  have h := ENNReal.toReal_mono (measure_ne_top γ (Icc (-δ) δ)) (gaussianReal_Icc_lower hδ')
  rw [ENNReal.toReal_ofReal (mul_nonneg gaussianDensityFloor_pos.le (mul_nonneg zero_le_two hδ))] at h
  have hbase : 2*gaussianDensityFloor*δ ≤ γ.real (Icc (-δ) δ) :=
    (show 2*gaussianDensityFloor*δ=gaussianDensityFloor*(2*δ) by ring).trans_le h
  rw [hweak,hstrong,mul_comm bulkMass]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀
    (mul_nonneg (mul_nonneg zero_le_two gaussianDensityFloor_pos.le) hδ) hbase _) bulkMass_pos.le

#print axioms axisBox_mass
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
