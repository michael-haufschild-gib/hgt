import GaloisForLFunctions.HTGeometry.ClockProbeRiccati

/-!
# The pointwise probe condition alone carries no information

`LocalProbesOn` asks, at each event of a region, for a probe solving the equation *for one
potential* at that event and nonvanishing there. For the second-derivative operator that demand is
empty: a quadratic can be fitted to any prescribed potential value at any single event.

So the pointwise condition is satisfied by every potential whatsoever, and cannot by itself separate
two candidates. The content lives entirely in the *shared* requirement of
`potential_eqOn_of_localProbes`: the probe must solve the equation for **both** candidate potentials
at the event. Physically that is the right reading — the probe is an observed solution of the actual
species, and the candidate potentials are both tested against that same observation.

This file proves the vacuity, so the distinction is on the record rather than implicit.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Quadratic probe matching a prescribed potential value at one event. -/
noncomputable def quadraticProbe (value a : ℝ) : ℝ → ℝ :=
  fun x => 1 - (value / 2) * (x - a) ^ 2

theorem quadraticProbe_self (value a : ℝ) : quadraticProbe value a a = 1 := by
  simp [quadraticProbe]

theorem hasDerivAt_quadraticProbe (value a x : ℝ) :
    HasDerivAt (quadraticProbe value a) (-(value * (x - a))) x := by
  have hbase : HasDerivAt (fun t : ℝ => (t - a) ^ 2) (2 * (x - a)) x := by
    simpa using ((hasDerivAt_id x).sub_const a).pow 2
  have hmul : HasDerivAt (fun t : ℝ => (value / 2) * (t - a) ^ 2)
      ((value / 2) * (2 * (x - a))) x := hbase.const_mul (value / 2)
  have hsub : HasDerivAt (quadraticProbe value a) (0 - (value / 2) * (2 * (x - a))) x := by
    simpa [quadraticProbe] using (hasDerivAt_const x (1 : ℝ)).sub hmul
  have hval : (0 : ℝ) - (value / 2) * (2 * (x - a)) = -(value * (x - a)) := by ring
  rwa [hval] at hsub

theorem deriv_quadraticProbe (value a : ℝ) :
    deriv (quadraticProbe value a) = fun x => -(value * (x - a)) := by
  funext x
  exact (hasDerivAt_quadraticProbe value a x).deriv

theorem secondDeriv_quadraticProbe (value a x : ℝ) :
    secondDeriv (quadraticProbe value a) x = -value := by
  have h : HasDerivAt (fun t : ℝ => -(value * (t - a))) (-(value * 1)) x := by
    exact (((hasDerivAt_id x).sub_const a).const_mul value).neg
  rw [secondDeriv, deriv_quadraticProbe, h.deriv]
  ring

/-- **A quadratic solves any prescribed potential at a single event.** -/
theorem solvesPotentialWaveAt_quadraticProbe (potential : ℝ → ℝ) (a : ℝ) :
    SolvesPotentialWaveAt secondDeriv potential (quadraticProbe (potential a) a) a := by
  rw [SolvesPotentialWaveAt, secondDeriv_quadraticProbe, quadraticProbe_self]
  ring

/-- **The pointwise probe condition holds for every potential.** -/
theorem localProbesOn_trivial (potential : ℝ → ℝ) (region : Set ℝ) :
    LocalProbesOn secondDeriv potential region := by
  intro a _
  refine ⟨quadraticProbe (potential a) a, solvesPotentialWaveAt_quadraticProbe potential a, ?_⟩
  rw [quadraticProbe_self]
  exact one_ne_zero

/-- **Hence the pointwise condition separates nothing.** Two different potentials both satisfy it
on every region. -/
theorem exists_ne_potential_with_localProbesOn (region : Set ℝ) :
    ∃ potential₁ potential₂ : ℝ → ℝ,
      potential₁ ≠ potential₂ ∧
        LocalProbesOn secondDeriv potential₁ region ∧
        LocalProbesOn secondDeriv potential₂ region := by
  refine ⟨fun _ => 0, fun _ => 1, ?_, localProbesOn_trivial _ region,
    localProbesOn_trivial _ region⟩
  intro hEq
  have := congrFun hEq 0
  norm_num at this

/-- **The shared requirement is what has content.** A probe solving the equation for two potentials
at one event, and nonvanishing there, forces them to agree there. -/
theorem potential_eq_of_shared_probe {potential₁ potential₂ u : ℝ → ℝ} {a : ℝ}
    (h₁ : SolvesPotentialWaveAt secondDeriv potential₁ u a)
    (h₂ : SolvesPotentialWaveAt secondDeriv potential₂ u a) (hu : u a ≠ 0) :
    potential₁ a = potential₂ a :=
  potential_eq_of_solvesPotentialWaveAt h₁ h₂ hu

/-- The quadratic probe is shared only when the two potentials already agree at the event. -/
theorem solvesPotentialWaveAt_quadraticProbe_iff (potential₁ potential₂ : ℝ → ℝ) (a : ℝ) :
    SolvesPotentialWaveAt secondDeriv potential₂ (quadraticProbe (potential₁ a) a) a ↔
      potential₂ a = potential₁ a := by
  rw [SolvesPotentialWaveAt, secondDeriv_quadraticProbe, quadraticProbe_self]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

end GaloisForLFunctions.HTGeometry
