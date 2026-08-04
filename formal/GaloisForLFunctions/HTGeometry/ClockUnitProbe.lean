import GaloisForLFunctions.HTGeometry.ClockUnitTransverseLift
import GaloisForLFunctions.HTGeometry.ClockThreeDimensionalDetermination

/-!
# Clock probes for potentials coupling the transverse coordinates along one direction

The analytic construction is unchanged once more. The field is the real part of the same solution of
the characteristic clock equation, and the d'Alembertian of the lift along a unit direction is the
same as for a single transverse coordinate, so the same field is a clock probe.

The class of potentials reached is the widest of the chapter: a potential depending on the two null
coordinates continuously differentiably and on one arbitrary linear combination of all the transverse
coordinates analytically.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped ContDiff

variable {n : ℕ} {u A B C Aa Ab Ac Ba Bb Bc Ca Cb Cc : ℝ → ℝ → ℝ → ℝ}
  {Ω : Set ((ℝ × ℝ) × ℝ)}

/-- **A field of the null coordinates and one transverse combination solving the characteristic
equation is a clock probe.** -/
theorem solvesPotentialWaveAt_unitTransLift {v : ℝ → ℝ → ℝ → ℝ} {c : Fin (n + 2) → ℝ}
    (hc : UnitDirection n c) (h : IsC1On3 u A B C Ω) (hA : IsC1On3 A Aa Ab Ac Ω)
    (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω) {x : Fin (n + 2) → ℝ}
    (hx : unitCLM n c x ∈ Ω)
    (hchar : Ab (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
        + Ba (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
      = (Cc (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
        + v (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
          * u (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)) / 2) :
    SolvesPotentialWaveAt
      (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
      (unitTransLift v c) (unitTransLift u c) x := by
  show (SmoothPseudoMetric.ofSignature (slabEps n)
      (slabEps_ne_zero n)).chart.dalembert (unitTransLift u c) x
      + unitTransLift v c x * unitTransLift u c x = 0
  rw [dalembert_unitTransLift hc h hA hB hC hx, hchar]
  show -2 * ((Cc (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
      + v (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
        * u (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)) / 2)
      + Cc (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
      + v (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
        * u (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i) = 0
  ring

/-- **The same, throughout a region on which the characteristic equation holds.** -/
theorem solvesPotentialWaveOn_unitTransLift {v : ℝ → ℝ → ℝ → ℝ} {c : Fin (n + 2) → ℝ}
    (hc : UnitDirection n c) (h : IsC1On3 u A B C Ω) (hA : IsC1On3 A Aa Ab Ac Ω)
    (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω)
    {W : Set (Fin (n + 2) → ℝ)} (hW : W ⊆ unitTransBox Ω c)
    (hchar : ∀ y ∈ W, Ab (y 0 + y 1) (y 0 - y 1) (∑ i, c i * y i)
        + Ba (y 0 + y 1) (y 0 - y 1) (∑ i, c i * y i)
      = (Cc (y 0 + y 1) (y 0 - y 1) (∑ i, c i * y i)
        + v (y 0 + y 1) (y 0 - y 1) (∑ i, c i * y i)
          * u (y 0 + y 1) (y 0 - y 1) (∑ i, c i * y i)) / 2) :
    SolvesPotentialWaveOn
      (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
      (unitTransLift v c) (unitTransLift u c) W :=
  fun y hy => solvesPotentialWaveAt_unitTransLift hc h hA hB hC (hW hy) (hchar y hy)

namespace ClockDatum

variable {V Vs Vt : ℝ → ℝ → ℂ → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

/-- **Clock probes at an arbitrary event, for a potential coupling the transverse coordinates along
one direction.** -/
theorem exists_clockProbe_unitTransverse_at
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0) (hT : 0 < T) (n : ℕ)
    {c : Fin (n + 2) → ℝ} (hc : UnitDirection n c) (x : Fin (n + 2) → ℝ)
    (hmass : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀,
      ‖V (s + (x 0 + x 1)) (t + (x 0 - x 1)) z‖ ≤ Mv) :
    ∃ W : Set (Fin (n + 2) → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ U : (Fin (n + 2) → ℝ) → ℝ,
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          (unitTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) c) U W ∧
        (∀ y ∈ W, U y ≠ 0) ∧ U x = 1 := by
  classical
  set ξ₀ : ℝ := x 0 + x 1 with hξ₀
  set η₀ : ℝ := x 0 - x 1 with hη₀
  have hD' := hD.translate ξ₀ η₀ hmass
  have hVreal' : ∀ s t w : ℝ, (translatePotential V ξ₀ η₀ s t ((w : ℝ) : ℂ)).im = 0 :=
    fun s t w => hVreal (s + ξ₀) (t + η₀) w
  set u₀ : ℝ → ℝ → ℝ → ℝ :=
    fun s t w => probeU (translatePotential V ξ₀ η₀) T (s - ξ₀) (t - η₀) w with hu₀
  have hUcont : Continuous (unitTransLift u₀ c) := by
    rw [unitTransLift_eq_comp]
    exact (hD'.continuous_probeU.comp (continuous_translateMap ξ₀ η₀)).comp
      (unitCLM n c).continuous
  have hnull : unitCLM n c x = ((ξ₀, η₀), ∑ i, c i * x i) := unitCLM_apply c x
  have hT0 : |(0 : ℝ)| < T := by simpa using hT
  have hxbox : x ∈ unitTransBox (translateSet (clockBox T) ξ₀ η₀) c := by
    rw [mem_unitTransBox, hnull]
    refine ⟨?_, ?_⟩ <;> simpa using hT
  have hone : unitTransLift u₀ c x = 1 := by
    show probeU (translatePotential V ξ₀ η₀) T (ξ₀ - ξ₀) (η₀ - η₀) (∑ i, c i * x i) = 1
    rw [sub_self, sub_self, probeU, boxClamp_eq_self (le_of_lt hT0),
      clockSolution_zero_zero hD'.pos hD'.pot hD'.massNonneg hD'.mass hD'.radNonneg hD'.rad
        hD'.sideNonneg hD'.small (hD'.absIm (∑ i, c i * x i))]
    norm_num
  refine ⟨unitTransBox (translateSet (clockBox T) ξ₀ η₀) c ∩ {y | unitTransLift u₀ c y ≠ 0},
    (isOpen_unitTransBox (isOpen_translateSet (isOpen_clockBox T) ξ₀ η₀) c).inter
      (isOpen_ne.preimage hUcont),
    ⟨hxbox, by rw [Set.mem_setOf_eq, hone]; exact one_ne_zero⟩, unitTransLift u₀ c,
    ?_, fun y hy => hy.2, hone⟩
  refine solvesPotentialWaveOn_unitTransLift hc (hD'.isC1On3_probeU.translate ξ₀ η₀)
    (hD'.isC1On3_probeA.translate ξ₀ η₀) (hD'.isC1On3_probeB.translate ξ₀ η₀)
    (hD'.isC1On3_probeC.translate ξ₀ η₀) (fun y hy => hy.1) fun y hy => ?_
  have hybox : unitCLM n c y ∈ translateSet (clockBox T) ξ₀ η₀ := hy.1
  rw [unitCLM_apply] at hybox
  have hs : |y 0 + y 1 - ξ₀| < T := hybox.1
  have ht : |y 0 - y 1 - η₀| < T := hybox.2
  have hchar := probe_characteristic (V := translatePotential V ξ₀ η₀) (T := T) hVreal'
    hs ht (w := ∑ i, c i * y i)
  have hVeq : translatePotential V ξ₀ η₀ (y 0 + y 1 - ξ₀) (y 0 - y 1 - η₀)
      ((∑ i, c i * y i : ℝ) : ℂ)
      = V (y 0 + y 1) (y 0 - y 1) ((∑ i, c i * y i : ℝ) : ℂ) := by
    rw [translatePotential, sub_add_cancel, sub_add_cancel]
  rw [hVeq] at hchar
  exact hchar

/-- **Such a potential has probes on open regions at every event.** -/
theorem openProbes_unitTransverse (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ)
    {c : Fin (n + 2) → ℝ} (hc : UnitDirection n c) :
    OpenProbes
      (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
      (unitTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) c) := by
  intro x
  obtain ⟨W, hWopen, hxW, U, hUon, hUne, _⟩ :=
    hD.exists_clockProbe_unitTransverse_at hVreal hT n hc x
      (fun s t _ _ z hz => hbound (s + (x 0 + x 1)) (t + (x 0 - x 1)) z hz)
  exact ⟨W, hWopen, hxW, U, hUon, hUne⟩

/-- **Such a potential is determined by its probes.** -/
theorem unitTransversePotential_eq_of_openProbes
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ)
    {c : Fin (n + 2) → ℝ} (hc : UnitDirection n c)
    {other : (Fin (n + 2) → ℝ) → ℝ}
    (h : ∀ (u : (Fin (n + 2) → ℝ) → ℝ) (W : Set (Fin (n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          (unitTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) c) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          other u W) :
    other = unitTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) c :=
  potential_eq_of_openProbes (hD.openProbes_unitTransverse hVreal hbound hT n hc) h

/-- **The two-species scale law for a potential coupling the transverse coordinates along one
direction**, in every dimension at least two. -/
theorem twoSpecies_scale_reconstruction_unitTransverse
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ) (a : ℝ)
    {c : Fin (n + 2) → ℝ} (hc : UnitDirection n c)
    {massSq : ℝ} (hmassSq : massSq ≠ 0)
    {σ : (Fin (n + 2) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (heff : (SmoothPseudoMetric.ofSignature (slabEps n)
        (slabEps_ne_zero n)).chart.conformalPotential a massSq σ
      = unitTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) c)
    {other₁ other₂ : (Fin (n + 2) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (n + 2) → ℝ) → ℝ) (W : Set (Fin (n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps n)
            (slabEps_ne_zero n)).chart.conformalPotential a massSq σ) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          other₁ u W)
    (h₂ : ∀ (u : (Fin (n + 2) → ℝ) → ℝ) (W : Set (Fin (n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps n)
            (slabEps_ne_zero n)).chart.conformalPotential a 0 σ) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          other₂ u W)
    (x : Fin (n + 2) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ x) := by
  have hop : OpenProbes
      (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
      ((SmoothPseudoMetric.ofSignature (slabEps n)
        (slabEps_ne_zero n)).chart.conformalPotential a massSq σ) := by
    rw [heff]
    exact hD.openProbes_unitTransverse hVreal hbound hT n hc
  exact scale_reconstruction_of_openProbes _ a hσ hmassSq hop h₁ h₂ x

end ClockDatum

end GaloisForLFunctions.HTGeometry
