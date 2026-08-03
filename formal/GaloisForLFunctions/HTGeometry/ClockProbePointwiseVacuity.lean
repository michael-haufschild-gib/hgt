import GaloisForLFunctions.HTGeometry.ClockProbeRiccati

/-!
# The pointwise probe condition alone carries no information

`LocalProbesOn` asks, at each event of a region, for a probe solving the equation *for one
potential* at that event and nonvanishing there. For the second-derivative operator that demand is
empty: a cosine or hyperbolic cosine of the right frequency, centred at the event, matches any
prescribed potential value there.

So the pointwise condition holds for every potential whatsoever and cannot by itself separate two
candidates. The content lives entirely in the *shared* requirement of
`potential_eqOn_of_localProbes`: the probe must solve the equation for **both** candidate potentials
at the event. Physically that is the right reading — the probe is an observed solution of the actual
species, and both candidate potentials are tested against that same observation.

Indeed a probe nonvanishing at an event is shared by two potentials exactly when they already agree
there, so sharedness is the whole of the hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

theorem coshProbe_self (s a : ℝ) : coshProbe s a a = 1 := by
  simp [coshProbe]

/-- **A centred cosine matches any nonnegative potential value at its centre.** -/
theorem solvesPotentialWaveAt_cosProbe_self (potential : ℝ → ℝ) (a : ℝ)
    (hpos : 0 ≤ potential a) :
    SolvesPotentialWaveAt secondDeriv potential
      (cosProbe (Real.sqrt (potential a)) a) a := by
  rw [SolvesPotentialWaveAt, secondDeriv_cosProbe, cosProbe_self,
    Real.sq_sqrt hpos]
  ring

/-- **A centred hyperbolic cosine matches any negative potential value at its centre.** -/
theorem solvesPotentialWaveAt_coshProbe_self (potential : ℝ → ℝ) (a : ℝ)
    (hneg : potential a ≤ 0) :
    SolvesPotentialWaveAt secondDeriv potential
      (coshProbe (Real.sqrt (-potential a)) a) a := by
  have hnn : 0 ≤ -potential a := by linarith
  rw [SolvesPotentialWaveAt, secondDeriv_coshProbe, coshProbe_self,
    Real.sq_sqrt hnn]
  ring

/-- **The pointwise probe condition holds for every potential.** -/
theorem localProbesOn_trivial (potential : ℝ → ℝ) (region : Set ℝ) :
    LocalProbesOn secondDeriv potential region := by
  intro a _
  rcases le_or_gt 0 (potential a) with hpos | hneg
  · refine ⟨cosProbe (Real.sqrt (potential a)) a,
      solvesPotentialWaveAt_cosProbe_self potential a hpos, ?_⟩
    rw [cosProbe_self]
    exact one_ne_zero
  · refine ⟨coshProbe (Real.sqrt (-potential a)) a,
      solvesPotentialWaveAt_coshProbe_self potential a (le_of_lt hneg), ?_⟩
    rw [coshProbe_self]
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

/-! ## Sharedness is the whole hypothesis -/

/-- **A probe nonvanishing at an event is shared by two potentials exactly when they agree there.**

So the useful hypothesis is not that a probe exists for each candidate separately, but that one and
the same probe solves for both — which is what an observed solution supplies. -/
theorem solvesPotentialWaveAt_iff_of_ne_zero {X : Type*} {wave : (X → ℝ) → (X → ℝ)}
    {potential₁ potential₂ u : X → ℝ} {a : X}
    (h₁ : SolvesPotentialWaveAt wave potential₁ u a) (hu : u a ≠ 0) :
    SolvesPotentialWaveAt wave potential₂ u a ↔ potential₂ a = potential₁ a := by
  constructor
  · intro h₂
    exact potential_eq_of_solvesPotentialWaveAt h₂ h₁ hu
  · intro hEq
    rw [SolvesPotentialWaveAt, hEq]
    exact h₁

/-- The corrected reading of local determination: shared probes, not per-potential probes. -/
theorem potential_eqOn_of_shared_localProbes {X : Type*} {wave : (X → ℝ) → (X → ℝ)}
    {potential other : X → ℝ} {region : Set X}
    (hshared : ∀ x ∈ region, ∃ u : X → ℝ,
      SolvesPotentialWaveAt wave potential u x ∧
        SolvesPotentialWaveAt wave other u x ∧ u x ≠ 0) :
    Set.EqOn other potential region :=
  potential_eqOn_of_localProbes hshared

end GaloisForLFunctions.HTGeometry
