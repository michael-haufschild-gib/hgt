import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalEnergy

/-!
# Sharp thermal energy contraction and extremal modes

The energy-loss mechanism of arXiv:2609.04530 yields exact defects between the
thermal channel energy and its fast/slow exponential bounds. Equality classifies
the population and coherence sectors. Nonzero Pauli-Z and Pauli-X modes attain
the bounds, proving sharpness. Positive rates and times are constructed, and
all matrix inputs remain unrestricted.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Physical positive time constructed from an unrestricted real coordinate. -/
def spinThermalPositiveTime (q : ℝ) : NNReal := ⟨Real.exp q, (Real.exp_pos q).le⟩

/-- Constructed positive damping and time give a strictly subunit survival mass. -/
theorem spinThermalPositiveTime_mass_lt_one (s q : ℝ) :
    spinDecayMass (Real.exp s) (spinThermalPositiveTime q) < 1 := by
  change Real.exp (-2 * (Real.exp s) ^ 2 * Real.exp q) < 1
  rw [Real.exp_lt_one_iff]
  have hp : 0 < 2 * (Real.exp s) ^ 2 * Real.exp q := by positivity
  linarith

/-- Exact physical-channel energy formula in terms of its surviving population. -/
theorem spinThermalEnergy_channel (a u : ℝ) (t : NNReal) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalEnergy u ((spinThermalChannel a u t).map ρ) =
      (spinDecayMass a t) ^ 2 * spinThermalPopulationEnergy u ρ +
        spinDecayMass a t * spinThermalCoherenceEnergy ρ := by
  rw [← spinThermalEvolution_channel, spinThermalEnergy_evolution]
  have he : Real.exp (-4 * a ^ 2 * (t : ℝ)) = (spinDecayMass a t) ^ 2 := by
    simp only [spinDecayMass, pow_two]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  rfl

/-- Exact defect above the fast-decay energy bound. -/
theorem spinThermalEnergy_channel_lower_defect (a u : ℝ) (t : NNReal) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalEnergy u ((spinThermalChannel a u t).map ρ) -
      (spinDecayMass a t) ^ 2 * spinThermalEnergy u ρ =
      spinDecayMass a t * (1 - spinDecayMass a t) * spinThermalCoherenceEnergy ρ := by
  rw [spinThermalEnergy_channel, spinThermalEnergy_split]
  ring

/-- Exact defect below the slow-decay energy bound. -/
theorem spinThermalEnergy_channel_upper_defect (a u : ℝ) (t : NNReal) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinDecayMass a t * spinThermalEnergy u ρ -
      spinThermalEnergy u ((spinThermalChannel a u t).map ρ) =
      spinDecayMass a t * (1 - spinDecayMass a t) * spinThermalPopulationEnergy u ρ := by
  rw [spinThermalEnergy_channel, spinThermalEnergy_split]
  ring

/-- Sharp two-sided contraction enclosure for every raw input matrix. -/
theorem spinThermalEnergy_channel_bounds (a u : ℝ) (t : NNReal) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinDecayMass a t) ^ 2 * spinThermalEnergy u ρ ≤
      spinThermalEnergy u ((spinThermalChannel a u t).map ρ) ∧
    spinThermalEnergy u ((spinThermalChannel a u t).map ρ) ≤ spinDecayMass a t * spinThermalEnergy u ρ := by
  obtain ⟨hp, hc⟩ := spinThermalEnergy_sectors_nonneg u ρ
  have hm := mul_nonneg (spinDecayMass_pos a t).le (sub_nonneg.mpr (spinDecayMass_le_one a t))
  constructor
  · have h := spinThermalEnergy_channel_lower_defect a u t ρ
    have hn := mul_nonneg hm hc
    linarith
  · have h := spinThermalEnergy_channel_upper_defect a u t ρ
    have hn := mul_nonneg hm hp
    linarith

/-- For strictly positive damping and time, fast-bound equality identifies exactly zero coherence. -/
theorem spinThermalEnergy_channel_lower_eq_iff (s u q : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalEnergy u ((spinThermalChannel (Real.exp s) u (spinThermalPositiveTime q)).map ρ) =
      (spinDecayMass (Real.exp s) (spinThermalPositiveTime q)) ^ 2 * spinThermalEnergy u ρ ↔
      spinThermalCoherenceEnergy ρ = 0 := by
  rw [← sub_eq_zero, spinThermalEnergy_channel_lower_defect, mul_eq_zero]
  have hp : spinDecayMass (Real.exp s) (spinThermalPositiveTime q) *
      (1 - spinDecayMass (Real.exp s) (spinThermalPositiveTime q)) ≠ 0 :=
    ne_of_gt (mul_pos (spinDecayMass_pos _ _) (sub_pos.mpr (spinThermalPositiveTime_mass_lt_one s q)))
  exact or_iff_right hp

/-- Slow-bound equality identifies exactly zero centered population energy. -/
theorem spinThermalEnergy_channel_upper_eq_iff (s u q : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalEnergy u ((spinThermalChannel (Real.exp s) u (spinThermalPositiveTime q)).map ρ) =
      spinDecayMass (Real.exp s) (spinThermalPositiveTime q) * spinThermalEnergy u ρ ↔
      spinThermalPopulationEnergy u ρ = 0 := by
  rw [eq_comm, ← sub_eq_zero, spinThermalEnergy_channel_upper_defect, mul_eq_zero]
  have hp : spinDecayMass (Real.exp s) (spinThermalPositiveTime q) *
      (1 - spinDecayMass (Real.exp s) (spinThermalPositiveTime q)) ≠ 0 :=
    ne_of_gt (mul_pos (spinDecayMass_pos _ _) (sub_pos.mpr (spinThermalPositiveTime_mass_lt_one s q)))
  exact or_iff_right hp

/-- The Pauli-Z matrix attains the fast bound for every bath and physical time. -/
theorem spinThermalEnergy_channel_pauliZ (a u : ℝ) (t : NNReal) :
    spinThermalEnergy u ((spinThermalChannel a u t).map QuantumAlg.pauliZ) =
      (spinDecayMass a t) ^ 2 * spinThermalEnergy u QuantumAlg.pauliZ := by
  have hC : spinThermalCoherenceEnergy QuantumAlg.pauliZ = 0 := by
    simp [spinThermalCoherenceEnergy, QuantumAlg.pauliZ]
  have h := spinThermalEnergy_channel_lower_defect a u t QuantumAlg.pauliZ
  rw [hC, mul_zero] at h
  exact sub_eq_zero.mp h

/-- The Pauli-X matrix attains the slow bound for every bath and physical time. -/
theorem spinThermalEnergy_channel_pauliX (a u : ℝ) (t : NNReal) :
    spinThermalEnergy u ((spinThermalChannel a u t).map QuantumAlg.pauliX) =
      spinDecayMass a t * spinThermalEnergy u QuantumAlg.pauliX := by
  have hP : spinThermalPopulationEnergy u QuantumAlg.pauliX = 0 := by
    simp [spinThermalPopulationEnergy, spinThermalCentered_entries, QuantumAlg.pauliX, Matrix.trace, Fin.sum_univ_two]
  have h := spinThermalEnergy_channel_upper_defect a u t QuantumAlg.pauliX
  rw [hP, mul_zero] at h
  exact (sub_eq_zero.mp h).symm

/-- Applying another thermal step never increases the centered Hilbert--Schmidt energy. -/
theorem spinThermalEnergy_channel_progress (a u : ℝ) (s t : NNReal) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalEnergy u ((spinThermalChannel a u (s + t)).map ρ) ≤
      spinThermalEnergy u ((spinThermalChannel a u t).map ρ) := by
  rw [spinThermalChannel_add]
  change spinThermalEnergy u ((spinThermalChannel a u s).map ((spinThermalChannel a u t).map ρ)) ≤ _
  have hb := (spinThermalEnergy_channel_bounds a u s ((spinThermalChannel a u t).map ρ)).2
  have hE : 0 ≤ spinThermalEnergy u ((spinThermalChannel a u t).map ρ) :=
    finiteMatrixHilbertSchmidtEnergy_nonneg _
  exact hb.trans (mul_le_of_le_one_left hE (spinDecayMass_le_one a s))

/-- Both bounding modes have nonzero energy, so the attained bounds are nontrivial. -/
theorem spinThermalEnergy_pauli (u : ℝ) :
    spinThermalEnergy u QuantumAlg.pauliZ = 2 ∧ spinThermalEnergy u QuantumAlg.pauliX = 2 := by
  constructor <;> rw [spinThermalEnergy_split] <;>
    simp [spinThermalPopulationEnergy, spinThermalCoherenceEnergy, spinThermalCentered_entries,
      QuantumAlg.pauliZ, QuantumAlg.pauliX, Matrix.trace, Fin.sum_univ_two] <;> ring

end
end GaloisForLFunctions.HTGeometry.SchafferExl
