import GaloisForLFunctions.HTGeometry.KleinGordonMonodromyFixed

/-!
# The Floquet eigen-class, inhabited

The band compression of a self-adjoint operator is self-adjoint, so the compressed flattening
potential meets every hypothesis of the small-potential theory. Its monodromy at `2π` fixes the whole
band, which is the eigenvector equation of the Floquet layer with multiplier one:

`M v = 1 · v`.

Every statement proved for eigen-solutions therefore has a model.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The band compression of a self-adjoint operator is self-adjoint.** -/
theorem kgBandOp_inner {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (R : ℝ) (f g : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgBandOp W₀ R f) g : ℂ) = inner ℂ f (kgBandOp W₀ R g) := by
  rw [kgBandOp_apply, kgBandOp_apply, kgLowPassOp_inner, hsa, kgLowPassOp_inner]

section EigenWitness

variable {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The periodic clock is a Floquet eigen-solution with multiplier one.** -/
theorem kgMonodromy_kgFlatPot_eigen (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hWb : ∀ r : ℝ, ‖kgBandOpT (fun _ : ℝ => fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
        (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) (Real.sqrt b) r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ =>
      kgBandOpT (fun _ : ℝ => fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
        (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) (Real.sqrt b) r z)
    (x y : Lp ℂ 2 (volume : Measure E)) :
    kgMonodromy (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
          (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) (Real.sqrt b)) b hb0 hWb hWs
        (2 * Real.pi)
        (kgPair E (kgFreqLowOp (Real.sqrt b) x, kgLowPassOp (Real.sqrt b) y))
      = (1 : ℂ) • kgPair E (kgFreqLowOp (Real.sqrt b) x, kgLowPassOp (Real.sqrt b) y) := by
  rw [kgMonodromy_apply, kgPeriodMap_apply, one_smul]
  simp only [kgPair_fst, kgPair_snd]
  exact kgMonodromy_kgFlatPot_fixed hb0 hb1 x y

end EigenWitness

end GaloisForLFunctions.HTGeometry
