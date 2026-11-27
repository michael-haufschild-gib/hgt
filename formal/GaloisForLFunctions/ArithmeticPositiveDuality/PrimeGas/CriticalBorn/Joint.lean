import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Law
import GaloisForLFunctions.HTGeometry.CompletedObserverTimeTorus

/-! # Joint sampling of elementary prime phases at finitely many heights -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- Simultaneous phase readings of the same harmonically sampled prime. -/
def jointLaw (ω : ι → ℝ) := packetLaw (fun p => finiteClockPhasePoint ω (-Real.log p))

/-- The joint character of order n is the elementary phase at the sum of
the integer multiples of the measurement heights. -/
theorem joint_moment (ω : ι → ℝ) (n : ι → ℤ) (N : ℕ) :
    (∫ z, UnitAddTorus.mFourier n z ∂(jointLaw ω N : Measure (UnitAddTorus ι))) =
      coefficient (finiteTorusCharacterDetuning n ω) (-1) N := by
  rw [jointLaw,packet_integral,coefficient]
  simp only [mFourier_finiteClockPhasePoint,phase,Circle.coe_exp,neg_neg,zpow_one,
    neg_mul,mul_comm (Real.log _) (finiteTorusCharacterDetuning n ω)]

/-- Every integer resonance is exact at finite cutoff. Every other joint
character disappears in the limit. -/
theorem joint_moment_limit (ω : ι → ℝ) (n : ι → ℤ) :
    Tendsto (fun N => ∫ z, UnitAddTorus.mFourier n z ∂(jointLaw ω N : Measure (UnitAddTorus ι)))
      atTop (𝓝 (if finiteTorusCharacterDetuning n ω = 0 then 1 else 0)) := by
  simp only [joint_moment]
  split_ifs with h
  · simp only [h,zero_height_coefficient]
    exact tendsto_const_nhds
  · exact nonzero_mode _ h _ (by norm_num)

/-- Critical prime sampling and uniform continuous time have the same
limiting Haar law. Its torus dimension is the rational rank of the heights. -/
theorem joint_orbit_law (ω : ι → ℝ) :
    ∃ (r : ℕ) (M : ι → Fin r → ℤ),
      closure (Set.range (finiteClockPhasePoint ω)) = Set.range (torusIntegerHom M) ∧
      Function.Injective (torusIntegerHom M) ∧
      r = Module.finrank ℚ (Submodule.span ℚ (Set.range ω)) ∧
      Tendsto (jointLaw ω) atTop (𝓝 (orbitClosureHaar M)) ∧
      Tendsto (finiteTorusPhaseProbabilityMeasure ω) atTop (𝓝 (orbitClosureHaar M)) := by
  obtain ⟨r, γ, M, A, hindep, -, -, hM, hA, hrank⟩ := exists_frequency_integer_basis ω
  refine ⟨r, M, closure_range_finiteClockPhasePoint_eq ω γ M hindep hM,
    torusIntegerHom_injective M A hA, hrank, ?_,
    finiteTorusPhaseProbabilityMeasure_tendsto_orbitClosureHaar ω γ M hindep hM⟩
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro n
  rw [orbitClosureHaar_mFourier_integral]
  have resonance : finiteTorusCharacterDetuning n ω = 0 ↔ (fun j => ∑ i, n i * M i j) = 0 := by
    rw [finiteTorusCharacterDetuning_of_integer_presentation ω γ M hM n]
    refine ⟨hindep _, fun h => ?_⟩
    rw [h]
    simp [finiteTorusCharacterDetuning]
  simpa only [resonance] using joint_moment_limit ω n

#print axioms joint_moment
#print axioms joint_moment_limit
#print axioms joint_orbit_law

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
