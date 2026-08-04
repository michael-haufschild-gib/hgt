import GaloisForLFunctions.HTGeometry.ClockDiagonalTransverseLift
import GaloisForLFunctions.HTGeometry.ClockThreeDimensionalDetermination

/-!
# Clock probes for potentials coupling two transverse coordinates

The analytic construction is unchanged: the solution of the characteristic clock equation is the
same, and so is the field built from its real part. Only the geometry changes — the transverse
variable is now the diagonal of two coordinates — and the d'Alembertian of the diagonal lift is the
same as before, so the same field is a clock probe.

The consequences follow as they did for one transverse coordinate: the potential is determined by
its probes, and the two-species scale law holds.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped ContDiff

namespace ClockDatum

variable {V Vs Vt : ℝ → ℝ → ℂ → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

/-- **Clock probes at an arbitrary event, for potentials coupling two transverse coordinates.** -/
theorem exists_clockProbe_diagTransverse_at
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0) (hT : 0 < T) (n : ℕ)
    (x : Fin (n + 4) → ℝ)
    (hmass : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀,
      ‖V (s + (x 0 + x 1)) (t + (x 0 - x 1)) z‖ ≤ Mv) :
    ∃ W : Set (Fin (n + 4) → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ U : (Fin (n + 4) → ℝ) → ℝ,
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 2))
            (slabEps_ne_zero (n + 2))).chart.dalembert
          (diagTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n) U W ∧
        (∀ y ∈ W, U y ≠ 0) ∧ U x = 1 := by
  classical
  set ξ₀ : ℝ := x 0 + x 1 with hξ₀
  set η₀ : ℝ := x 0 - x 1 with hη₀
  have hD' := hD.translate ξ₀ η₀ hmass
  have hVreal' : ∀ s t w : ℝ, (translatePotential V ξ₀ η₀ s t ((w : ℝ) : ℂ)).im = 0 :=
    fun s t w => hVreal (s + ξ₀) (t + η₀) w
  set u₀ : ℝ → ℝ → ℝ → ℝ :=
    fun s t w => probeU (translatePotential V ξ₀ η₀) T (s - ξ₀) (t - η₀) w with hu₀
  have hUcont : Continuous (diagTransLift u₀ n) := by
    rw [diagTransLift_eq_comp]
    exact (hD'.continuous_probeU.comp (continuous_translateMap ξ₀ η₀)).comp
      (diagCLM n).continuous
  have hnull : diagCLM n x = ((ξ₀, η₀), diagUnitScale * (x 2 + x 3)) := rfl
  have hT0 : |(0 : ℝ)| < T := by simpa using hT
  have hxbox : x ∈ diagTransBox (translateSet (clockBox T) ξ₀ η₀) n := by
    rw [mem_diagTransBox, hnull]
    refine ⟨?_, ?_⟩ <;> simpa using hT
  have hone : diagTransLift u₀ n x = 1 := by
    show probeU (translatePotential V ξ₀ η₀) T (ξ₀ - ξ₀) (η₀ - η₀)
      (diagUnitScale * (x 2 + x 3)) = 1
    rw [sub_self, sub_self, probeU, boxClamp_eq_self (le_of_lt hT0),
      clockSolution_zero_zero hD'.pos hD'.pot hD'.massNonneg hD'.mass hD'.radNonneg hD'.rad
        hD'.sideNonneg hD'.small (hD'.absIm (diagUnitScale * (x 2 + x 3)))]
    norm_num
  refine ⟨diagTransBox (translateSet (clockBox T) ξ₀ η₀) n ∩ {y | diagTransLift u₀ n y ≠ 0},
    (isOpen_diagTransBox (isOpen_translateSet (isOpen_clockBox T) ξ₀ η₀) n).inter
      (isOpen_ne.preimage hUcont),
    ⟨hxbox, by rw [Set.mem_setOf_eq, hone]; exact one_ne_zero⟩, diagTransLift u₀ n,
    ?_, fun y hy => hy.2, hone⟩
  refine solvesPotentialWaveOn_diagTransLift (hD'.isC1On3_probeU.translate ξ₀ η₀)
    (hD'.isC1On3_probeA.translate ξ₀ η₀) (hD'.isC1On3_probeB.translate ξ₀ η₀)
    (hD'.isC1On3_probeC.translate ξ₀ η₀) (fun y hy => hy.1) fun y hy => ?_
  have hybox : diagCLM n y ∈ translateSet (clockBox T) ξ₀ η₀ := hy.1
  have hs : |y 0 + y 1 - ξ₀| < T := hybox.1
  have ht : |y 0 - y 1 - η₀| < T := hybox.2
  have hchar := probe_characteristic (V := translatePotential V ξ₀ η₀) (T := T) hVreal'
    hs ht (w := diagUnitScale * (y 2 + y 3))
  have hVeq : translatePotential V ξ₀ η₀ (y 0 + y 1 - ξ₀) (y 0 - y 1 - η₀)
      ((diagUnitScale * (y 2 + y 3) : ℝ) : ℂ)
      = V (y 0 + y 1) (y 0 - y 1) ((diagUnitScale * (y 2 + y 3) : ℝ) : ℂ) := by
    rw [translatePotential, sub_add_cancel, sub_add_cancel]
  rw [hVeq] at hchar
  exact hchar

/-- **Such a potential has probes on open regions at every event.** -/
theorem openProbes_diagTransverse (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ) :
    OpenProbes
      (SmoothPseudoMetric.ofSignature (slabEps (n + 2))
        (slabEps_ne_zero (n + 2))).chart.dalembert
      (diagTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n) := by
  intro x
  obtain ⟨W, hWopen, hxW, U, hUon, hUne, _⟩ :=
    hD.exists_clockProbe_diagTransverse_at hVreal hT n x
      (fun s t _ _ z hz => hbound (s + (x 0 + x 1)) (t + (x 0 - x 1)) z hz)
  exact ⟨W, hWopen, hxW, U, hUon, hUne⟩

/-- **Such a potential is determined by its probes.** -/
theorem diagTransversePotential_eq_of_openProbes
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ)
    {other : (Fin (n + 4) → ℝ) → ℝ}
    (h : ∀ (u : (Fin (n + 4) → ℝ) → ℝ) (W : Set (Fin (n + 4) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 2))
            (slabEps_ne_zero (n + 2))).chart.dalembert
          (diagTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 2))
            (slabEps_ne_zero (n + 2))).chart.dalembert other u W) :
    other = diagTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n :=
  potential_eq_of_openProbes (hD.openProbes_diagTransverse hVreal hbound hT n) h

/-- **The two-species scale law for a potential coupling two transverse coordinates.** -/
theorem twoSpecies_scale_reconstruction_diagTransverse
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ) (a : ℝ)
    {massSq : ℝ} (hmassSq : massSq ≠ 0)
    {σ : (Fin (n + 4) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (heff : (SmoothPseudoMetric.ofSignature (slabEps (n + 2))
        (slabEps_ne_zero (n + 2))).chart.conformalPotential a massSq σ
      = diagTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n)
    {other₁ other₂ : (Fin (n + 4) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (n + 4) → ℝ) → ℝ) (W : Set (Fin (n + 4) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 2))
            (slabEps_ne_zero (n + 2))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (n + 2))
            (slabEps_ne_zero (n + 2))).chart.conformalPotential a massSq σ) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 2))
            (slabEps_ne_zero (n + 2))).chart.dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (n + 4) → ℝ) → ℝ) (W : Set (Fin (n + 4) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 2))
            (slabEps_ne_zero (n + 2))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (n + 2))
            (slabEps_ne_zero (n + 2))).chart.conformalPotential a 0 σ) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 2))
            (slabEps_ne_zero (n + 2))).chart.dalembert other₂ u W)
    (x : Fin (n + 4) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ x) := by
  have hop : OpenProbes
      (SmoothPseudoMetric.ofSignature (slabEps (n + 2))
        (slabEps_ne_zero (n + 2))).chart.dalembert
      ((SmoothPseudoMetric.ofSignature (slabEps (n + 2))
        (slabEps_ne_zero (n + 2))).chart.conformalPotential a massSq σ) := by
    rw [heff]
    exact hD.openProbes_diagTransverse hVreal hbound hT n
  exact scale_reconstruction_of_openProbes _ a hσ hmassSq hop h₁ h₂ x

end ClockDatum

end GaloisForLFunctions.HTGeometry
