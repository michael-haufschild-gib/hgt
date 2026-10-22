import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonPeriodicClockConserved

/-!
# The unit-modulus law, checked against the tuned clock

The general theory derives `|k| = 1` for every attained multiplier of a weak static real potential
from the two-sided bound on the powers of the monodromy. The tuned clock computes its multiplier
directly: it is `e^{−icT}`, of modulus one by inspection.

Applying the general law to that clock therefore recomputes a known number. The two derivations are
independent — one spectral, one explicit — and they agree.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TunedUnitModulus

variable {b c : ℝ}

/-- **The unit-modulus law applied to the tuned clock.** -/
theorem exists_tuned_clock_multiplier_norm_one [Nontrivial E] (hbpos : 0 < b) (hb1 : b < 1)
    (hc0 : 0 < c) (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (T : ℝ) :
    ∃ z : Lp ℂ 2 (volume : Measure E),
      kgPair E (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) z,
        kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • z)) ≠ 0
      ∧ ‖kgTunedPhase c T‖ = 1 := by
  have hb0 : (0 : ℝ) ≤ b := hbpos.le
  have hRpos : 0 < Real.sqrt (c ^ (2 : ℕ) - 1 + b) := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨z, hzne, hzfix⟩ := exists_ne_zero_kgLowPassOp_fixed (E := E) hRpos
  have hne : kgPair E (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) z,
      kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • z)) ≠ 0 :=
    kgPair_ne_zero_of_fst (kgFreqLowOp_ne_zero_of_fixed hzne hzfix)
  refine ⟨z, hne, ?_⟩
  have hMp : ‖fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
      (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))‖ ≤ b :=
    norm_fourierMulCLM_le _ _ _
  have hW : ‖kgBandOp (fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
      (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
      (Real.sqrt (c ^ (2 : ℕ) - 1 + b))‖ ≤ b := norm_kgBandOp_le hb0 hMp _
  have hsa : ∀ u v : Lp ℂ 2 (volume : Measure E),
      (inner ℂ (kgBandOp (fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
        (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) u) v : ℂ)
      = inner ℂ u (kgBandOp (fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
        (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) v) :=
    kgBandOp_inner (fourierMulCLM_inner _ _ _
      (starRingEnd_kgRealPotSymbol (kgTunedPot b c))) _
  have hWb : ∀ r : ℝ, ‖(fun _ : ℝ => kgBandOp (fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
      (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
      (Real.sqrt (c ^ (2 : ℕ) - 1 + b))) r‖ ≤ b := fun _ => hW
  have hWs : ∀ u : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ =>
      (fun _ : ℝ => kgBandOp (fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
        (Real.sqrt (c ^ (2 : ℕ) - 1 + b))) r u := fun _ => continuous_const
  obtain ⟨heig, _⟩ :=
    kgMonodromy_kgTunedPot_circle_eigen (E := E) hb0 hb1 hc0 hc1 hcb hWb hWs z T
  exact norm_floquet_multiplier_eq_one_of_small_potential hb0 hb1 hW hsa hWb hWs
    (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) z)
    (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • z)) hne heig

end TunedUnitModulus

end GaloisForLFunctions.HTGeometry
