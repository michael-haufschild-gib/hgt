import GaloisForLFunctions.HTGeometry.ClockProbeOscillatorySeparation

/-!
# Plane-wave probes and the constant potentials

The separation result shows that a determined potential need not carry a nowhere-vanishing probe.
The higher-dimensional witnesses of that phenomenon are the plane waves.

On a chart of constant signature the linear phase `⟪n,x⟫` has vanishing d'Alembertian and constant
carré du champ `G(n,n)`, so the chain rule turns `cos(⟪n,x⟫ + θ)` into a solution of
`□u + G(n,n) u = 0`. Sliding the offset `θ` produces, at every event, a probe nonvanishing there.
Hence every constant potential in the range of `n ↦ G(n,n)` is determined — and on Minkowski space
that range is all of `ℝ`.

Constant potentials are exactly the mass terms of the clock species in flat space, so this closes
the flat case of the inverse step for both species at once.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

variable {d : ℕ}

/-! ## The linear phase on a constant-signature chart -/

theorem coordPartial_covectorPhase (n : Fin (d + 1) → ℝ) (i : Fin (d + 1))
    (x : Fin (d + 1) → ℝ) : coordPartial i (covectorPhase n) x = n i := by
  have h : coordPartial i (covectorLift n fun t => t) x = n i * 1 :=
    coordPartial_covectorLift (hasDerivAt_id (covectorPhase n x)) i
  rw [mul_one] at h
  exact h

theorem contDiff_covectorPhase (n : Fin (d + 1) → ℝ) :
    ContDiff ℝ ∞ (covectorPhase (d := d) n) := by
  rw [← covectorCLM_coe n]
  exact (covectorCLM n).contDiff

/-- The metric norm of a covector for a constant signature. -/
noncomputable def covectorNormConst (eps n : Fin (d + 1) → ℝ) : ℝ :=
  ∑ i, (eps i)⁻¹ * (n i * n i)

theorem gradPair_covectorPhase (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    (n : Fin (d + 1) → ℝ) (x : Fin (d + 1) → ℝ) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.gradPair
        (covectorPhase n) (covectorPhase n) x = covectorNormConst eps n := by
  rw [ofSignature_gradPair, covectorNormConst]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordPartial_covectorPhase]
  ring

theorem dalembert_covectorPhase (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    (n : Fin (d + 1) → ℝ) (x : Fin (d + 1) → ℝ) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert (covectorPhase n) x = 0 := by
  rw [SmoothPseudoMetric.ofSignature_dalembert eps heps (contDiff_covectorPhase n) x]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hconst : coordPartial i (covectorPhase (d := d) n) = fun _ => n i := by
    funext y
    exact coordPartial_covectorPhase n i y
  rw [hconst, coordPartial_const]
  ring

/-! ## Plane-wave probes -/

/-- Plane wave of covector `n` and offset `θ`. -/
noncomputable def planeWave (n : Fin (d + 1) → ℝ) (θ : ℝ) : (Fin (d + 1) → ℝ) → ℝ :=
  fun x => Real.cos (covectorPhase n x + θ)

theorem planeWave_self (n : Fin (d + 1) → ℝ) (x : Fin (d + 1) → ℝ) :
    planeWave n (-covectorPhase n x) x = 1 := by
  show Real.cos (covectorPhase n x + -covectorPhase n x) = 1
  simp

/-- **The plane wave solves the constant-potential clock equation.** -/
theorem solvesPotentialWave_planeWave (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    (n : Fin (d + 1) → ℝ) (θ : ℝ) :
    SolvesPotentialWave (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
      (fun _ => covectorNormConst eps n) (planeWave n θ) := by
  intro x
  have hw1 : ∀ t ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun s => Real.cos (s + θ)) (-Real.sin (t + θ)) t := by
    intro t _
    have h := ((hasDerivAt_id t).add_const θ).cos
    rw [mul_one] at h
    exact h
  have hw2 : ∀ t ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun s => -Real.sin (s + θ)) (-Real.cos (t + θ)) t := by
    intro t _
    have h := (((hasDerivAt_id t).add_const θ).sin).neg
    rw [mul_one] at h
    exact h
  have hred := dalembert_comp (SmoothPseudoMetric.ofSignature eps heps).chart
    (contDiff_covectorPhase n) isOpen_univ hw1 hw2 (x := x) (Set.mem_univ _)
  show (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
      (fun y => Real.cos (covectorPhase n y + θ)) x
      + covectorNormConst eps n * Real.cos (covectorPhase n x + θ) = 0
  rw [hred, gradPair_covectorPhase, dalembert_covectorPhase]
  ring

/-- **Every metric norm of a covector is a determined constant potential.** -/
theorem noCommonZero_covectorNormConst (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    (n : Fin (d + 1) → ℝ) :
    NoCommonZero (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
      (fun _ => covectorNormConst eps n) := by
  intro x
  refine ⟨planeWave n (-covectorPhase n x), ?_, ?_⟩
  · rw [mem_solutionSet_iff]
    exact solvesPotentialWave_planeWave eps heps n _
  · rw [planeWave_self]
    exact one_ne_zero

/-! ## Every constant potential on Minkowski space -/

theorem covectorNormConst_single (eps : Fin (d + 1) → ℝ) (k : Fin (d + 1)) (a : ℝ) :
    covectorNormConst eps (Pi.single k a) = (eps k)⁻¹ * (a * a) := by
  rw [covectorNormConst, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_apply, if_neg hj]
    ring
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem exists_covectorNormConst_minkowski (c : ℝ) :
    ∃ n : Fin (d + 1 + 1) → ℝ,
      covectorNormConst (fun i => if (i : ℕ) = 0 then -1 else 1) n = c := by
  rcases le_or_gt 0 c with hc | hc
  · refine ⟨Pi.single 1 (Real.sqrt c), ?_⟩
    rw [covectorNormConst_single, Real.mul_self_sqrt hc]
    simp
  · refine ⟨Pi.single 0 (Real.sqrt (-c)), ?_⟩
    have hnc : (0 : ℝ) ≤ -c := by linarith
    rw [covectorNormConst_single, Real.mul_self_sqrt hnc]
    norm_num

/-- **Every constant potential on Minkowski space is determined.** In flat space the clock
potential of a species is its squared mass, so the inverse step is closed there for both species at
once, with no nondegeneracy hypothesis. -/
theorem noCommonZero_const_minkowski (c : ℝ) :
    NoCommonZero (SmoothPseudoMetric.minkowski (d + 1 + 1)).chart.dalembert (fun _ => c) := by
  obtain ⟨n, hn⟩ := exists_covectorNormConst_minkowski (d := d) c
  rw [SmoothPseudoMetric.minkowski, ← hn]
  exact noCommonZero_covectorNormConst _ _ n

/-- **Determination of a constant potential on Minkowski space.** -/
theorem potential_eq_const_minkowski {c : ℝ} {other : (Fin (d + 1 + 1) → ℝ) → ℝ}
    (hother : ∀ u ∈ solutionSet (SmoothPseudoMetric.minkowski (d + 1 + 1)).chart.dalembert
        (fun _ => c),
      SolvesPotentialWave (SmoothPseudoMetric.minkowski (d + 1 + 1)).chart.dalembert other u) :
    other = fun _ => c :=
  potential_eq_of_noCommonZero (noCommonZero_const_minkowski c) hother

end GaloisForLFunctions.HTGeometry
