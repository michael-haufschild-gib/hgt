import GaloisForLFunctions.HTGeometry.KleinGordonEigenStateNonzero

/-!
# The periodic clock keeps exact time

Every hypothesis of the eigen-clock law is now available for the flattening potential: it is bounded
by `b`, its band compression is self-adjoint, its monodromy at `2π` fixes the band, and the band
carries a nonzero state. So the general theorem applies, and its conclusion is the exact conservation
the plane rotation exhibits directly:

`E(2πn) = E(0)`.

This is the general machinery of the card checked against a model where the answer is known.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section PeriodicConserved

variable {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The periodic clock keeps exact time**, by the general eigen-clock law. -/
theorem exists_periodic_clock_energy_conserved [Nontrivial E] (hbpos : 0 < b) (hb1 : b < 1)
    (y : Lp ℂ 2 (volume : Measure E)) (n : ℕ) :
    ∃ z : Lp ℂ 2 (volume : Measure E),
      kgPair E (kgFreqLowOp (Real.sqrt b) z, kgLowPassOp (Real.sqrt b) y) ≠ 0 ∧
      ‖kgFieldGradT (fun _ : ℝ => kgBandOp (fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hbpos.le
            (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hbpos.le))) (Real.sqrt b))
          (kgFreqLowOp (Real.sqrt b) z) (kgLowPassOp (Real.sqrt b) y)
          ((n : ℝ) * (2 * Real.pi))‖ ^ (2 : ℕ)
        + ‖kgFieldVelT (fun _ : ℝ => kgBandOp (fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hbpos.le
            (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hbpos.le))) (Real.sqrt b))
          (kgFreqLowOp (Real.sqrt b) z) (kgLowPassOp (Real.sqrt b) y)
          ((n : ℝ) * (2 * Real.pi))‖ ^ (2 : ℕ)
        = ‖kgFreqLowOp (Real.sqrt b) z‖ ^ (2 : ℕ) + ‖kgLowPassOp (Real.sqrt b) y‖ ^ (2 : ℕ) := by
  have hb0 : (0 : ℝ) ≤ b := hbpos.le
  have hRpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbpos
  obtain ⟨z, hzfix, hzne⟩ := exists_ne_zero_eigen_state (E := E) hRpos y
  refine ⟨z, hzne, ?_⟩
  have hMp : ‖fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
      (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))‖ ≤ b := norm_fourierMulCLM_le _ _ _
  have hW : ‖kgBandOp (fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
      (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) (Real.sqrt b)‖ ≤ b :=
    norm_kgBandOp_le hb0 hMp _
  have hsa : ∀ u v : Lp ℂ 2 (volume : Measure E),
      (inner ℂ (kgBandOp (fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
        (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) (Real.sqrt b) u) v : ℂ)
      = inner ℂ u (kgBandOp (fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
        (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) (Real.sqrt b) v) :=
    kgBandOp_inner (fourierMulCLM_inner _ _ _
      (starRingEnd_kgRealPotSymbol (kgFlatPot b))) _
  have hWb : ∀ r : ℝ, ‖(fun _ : ℝ => kgBandOp (fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
      (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) (Real.sqrt b)) r‖ ≤ b := fun _ => hW
  have hWs : ∀ u : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ =>
      (fun _ : ℝ => kgBandOp (fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
        (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) (Real.sqrt b)) r u :=
    fun _ => continuous_const
  have heig := kgMonodromy_kgFlatPot_eigen (E := E) hb0 hb1 hWb hWs z y
  exact kgFieldEnergy_eigen_conserved_of_small_potential hb0 hb1 hW hsa hWb hWs
    (kgFreqLowOp (Real.sqrt b) z) (kgLowPassOp (Real.sqrt b) y) hzne heig n

end PeriodicConserved

end GaloisForLFunctions.HTGeometry
