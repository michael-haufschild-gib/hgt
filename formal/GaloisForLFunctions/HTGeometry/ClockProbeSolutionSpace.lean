import GaloisForLFunctions.HTGeometry.ClockProbeNonvanishing

/-!
# The solution space, and why pointwise probes suffice

Determination needs a probe family with no common zero. Demanding a *single* globally nonvanishing
probe is much stronger than necessary. For a linear wave operator the solutions form a linear space,
so the determination locus of the full solution space is the complement of its common zero set, and
it is enough to have, **for each event separately**, some solution nonvanishing there.

That is exactly what solvability of the Cauchy problem with normalized data supplies, and it is a
strictly weaker demand than a globally nonvanishing probe: the solutions may be different at
different events.

The consequence is the clean statement of potential recovery: two potentials with the same solution
space are equal as soon as that space has no common zero.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {X : Type u}

/-- A wave operator is linear when it is additive and homogeneous. -/
structure LinearWave (wave : (X → ℝ) → (X → ℝ)) : Prop where
  map_add : ∀ u v, wave (u + v) = wave u + wave v
  map_smul : ∀ (c : ℝ) (u), wave (c • u) = c • wave u

/-- The solution space of a potential-dressed wave equation. -/
def solutionSet (wave : (X → ℝ) → (X → ℝ)) (potential : X → ℝ) : Set (X → ℝ) :=
  {u | SolvesPotentialWave wave potential u}

theorem mem_solutionSet_iff (wave : (X → ℝ) → (X → ℝ)) (potential u : X → ℝ) :
    u ∈ solutionSet wave potential ↔ SolvesPotentialWave wave potential u := Iff.rfl

theorem zero_mem_solutionSet {wave : (X → ℝ) → (X → ℝ)} (hlin : LinearWave wave)
    (potential : X → ℝ) : (0 : X → ℝ) ∈ solutionSet wave potential := by
  intro x
  have h0 : wave (0 : X → ℝ) = 0 := by
    have := hlin.map_smul 0 (0 : X → ℝ)
    simpa using this
  simp [h0]

theorem add_mem_solutionSet {wave : (X → ℝ) → (X → ℝ)} (hlin : LinearWave wave)
    {potential u v : X → ℝ} (hu : u ∈ solutionSet wave potential)
    (hv : v ∈ solutionSet wave potential) : u + v ∈ solutionSet wave potential := by
  intro x
  have hu' := hu x
  have hv' := hv x
  rw [hlin.map_add]
  simp only [Pi.add_apply]
  linarith

theorem smul_mem_solutionSet {wave : (X → ℝ) → (X → ℝ)} (hlin : LinearWave wave)
    {potential u : X → ℝ} (c : ℝ) (hu : u ∈ solutionSet wave potential) :
    c • u ∈ solutionSet wave potential := by
  intro x
  have hu' := hu x
  rw [hlin.map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  calc c * wave u x + potential x * (c * u x)
      = c * (wave u x + potential x * u x) := by ring
    _ = 0 := by rw [hu', mul_zero]

/-! ## Pointwise probes -/

/-- The solution space has no common zero: at each event some solution is nonvanishing. -/
def NoCommonZero (wave : (X → ℝ) → (X → ℝ)) (potential : X → ℝ) : Prop :=
  ∀ x : X, ∃ u ∈ solutionSet wave potential, u x ≠ 0

theorem potentialDeterminationSet_solutionSet_eq_univ_iff
    (wave : (X → ℝ) → (X → ℝ)) (potential : X → ℝ) :
    potentialDeterminationSet (solutionSet wave potential) = Set.univ ↔
      NoCommonZero wave potential := by
  constructor
  · intro h x
    have hx : x ∈ potentialDeterminationSet (solutionSet wave potential) := by
      rw [h]
      trivial
    exact hx
  · intro h
    exact Set.eq_univ_of_forall fun x => h x

/-- **Pointwise probes suffice.** If at each event some solution is nonvanishing there, any
potential with the same solution space is the same potential. -/
theorem potential_eq_of_noCommonZero {wave : (X → ℝ) → (X → ℝ)} {potential other : X → ℝ}
    (hno : NoCommonZero wave potential)
    (hother : ∀ u ∈ solutionSet wave potential, SolvesPotentialWave wave other u) :
    other = potential := by
  funext x
  obtain ⟨u, hu, hux⟩ := hno x
  exact potential_eq_of_solvesPotentialWave (hother u hu) hu hux

/-- **Two potentials with the same solution space are equal.** -/
theorem potential_eq_of_solutionSet_eq {wave : (X → ℝ) → (X → ℝ)} {potential other : X → ℝ}
    (hno : NoCommonZero wave potential)
    (hset : solutionSet wave other = solutionSet wave potential) :
    other = potential := by
  refine potential_eq_of_noCommonZero hno fun v hv => ?_
  rw [← hset] at hv
  exact hv

/-- Normalized Cauchy data at every event give the no-common-zero condition. -/
theorem noCommonZero_of_exists_normalized {wave : (X → ℝ) → (X → ℝ)} {potential : X → ℝ}
    (hnorm : ∀ x : X, ∃ u ∈ solutionSet wave potential, u x = 1) :
    NoCommonZero wave potential := by
  intro x
  obtain ⟨u, hu, hux⟩ := hnorm x
  exact ⟨u, hu, by rw [hux]; exact one_ne_zero⟩

/-- A globally nonvanishing probe is a special case, so the pointwise condition is strictly
weaker. -/
theorem noCommonZero_of_nonvanishing_probe {wave : (X → ℝ) → (X → ℝ)} {potential u : X → ℝ}
    (hu : ∀ x, u x ≠ 0) (hsolve : SolvesPotentialWave wave potential u) :
    NoCommonZero wave potential :=
  fun x => ⟨u, hsolve, hu x⟩

/-! ## The two-species consequence -/

/-- **Pointwise probes for both species reconstruct the conformal scale everywhere.** -/
theorem reconstructedScale_eq_of_noCommonZero
    {wave₁ wave₂ : (X → ℝ) → (X → ℝ)} {potential₁ potential₂ other₁ other₂ : X → ℝ}
    {massSq₁ massSq₂ : ℝ}
    (hno₁ : NoCommonZero wave₁ potential₁) (hno₂ : NoCommonZero wave₂ potential₂)
    (hother₁ : ∀ u ∈ solutionSet wave₁ potential₁, SolvesPotentialWave wave₁ other₁ u)
    (hother₂ : ∀ u ∈ solutionSet wave₂ potential₂, SolvesPotentialWave wave₂ other₂ u) :
    reconstructedScale other₁ other₂ massSq₁ massSq₂ =
      reconstructedScale potential₁ potential₂ massSq₁ massSq₂ := by
  rw [potential_eq_of_noCommonZero hno₁ hother₁, potential_eq_of_noCommonZero hno₂ hother₂]

/-! ## The condition is inhabited -/

/-- The axis exponential of a diagonal chart supplies the no-common-zero condition. -/
theorem noCommonZero_axisPotential {d : ℕ} (eps : Fin d → ℝ) (heps : ∀ i, eps i ≠ 0)
    (i₀ : Fin d) (s : ℝ) :
    NoCommonZero (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
      (axisPotential eps i₀ s) :=
  noCommonZero_of_nonvanishing_probe
    (fun x => axisExponential_ne_zero one_ne_zero x)
    (solvesPotentialWave_axisExponential eps heps i₀ s 1)

end GaloisForLFunctions.HTGeometry
