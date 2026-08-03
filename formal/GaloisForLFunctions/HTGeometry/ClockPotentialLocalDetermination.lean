import GaloisForLFunctions.HTGeometry.ClockProbeOneDimensional

/-!
# Local probes suffice: determination never needs a global solution

Every determination statement so far asked for probes solving the wave equation at *every* event.
That is more than the argument uses. The proof that a probe pins the potential at an event reads the
equation only at that event, so a probe solving on a region determines the potential on that region,
and nothing outside is required.

This matters because existence theory for wave equations is local: solutions come with a domain.
The statements here are the interface such an existence theorem plugs into, and they make every
global statement proved earlier a corollary.

The local notion is strictly weaker: there are probes solving on a proper region and nowhere else.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {X : Type u}

/-- A probe solves the potential-dressed wave equation at a single event. -/
def SolvesPotentialWaveAt (wave : (X → ℝ) → (X → ℝ)) (potential u : X → ℝ) (x : X) : Prop :=
  wave u x + potential x * u x = 0

/-- A probe solves the equation throughout a region. -/
def SolvesPotentialWaveOn (wave : (X → ℝ) → (X → ℝ)) (potential u : X → ℝ)
    (region : Set X) : Prop :=
  ∀ x ∈ region, SolvesPotentialWaveAt wave potential u x

theorem solvesPotentialWaveAt_of_solves {wave : (X → ℝ) → (X → ℝ)} {potential u : X → ℝ}
    (h : SolvesPotentialWave wave potential u) (x : X) :
    SolvesPotentialWaveAt wave potential u x := h x

theorem solvesPotentialWaveOn_of_solves {wave : (X → ℝ) → (X → ℝ)} {potential u : X → ℝ}
    (h : SolvesPotentialWave wave potential u) (region : Set X) :
    SolvesPotentialWaveOn wave potential u region := fun x _ => h x

/-- **The pointwise core.** A probe nonvanishing at an event pins the potential there, using the
equation only at that event. -/
theorem potential_eq_of_solvesPotentialWaveAt {wave : (X → ℝ) → (X → ℝ)}
    {potential₁ potential₂ u : X → ℝ} {x : X}
    (h₁ : SolvesPotentialWaveAt wave potential₁ u x)
    (h₂ : SolvesPotentialWaveAt wave potential₂ u x) (hu : u x ≠ 0) :
    potential₁ x = potential₂ x := by
  have hdiff : (potential₁ x - potential₂ x) * u x = 0 := by
    simp only [SolvesPotentialWaveAt] at h₁ h₂
    nlinarith [h₁, h₂]
  rcases mul_eq_zero.mp hdiff with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hu

/-- A family of local probes, one for each event of a region. -/
def LocalProbesOn (wave : (X → ℝ) → (X → ℝ)) (potential : X → ℝ) (region : Set X) : Prop :=
  ∀ x ∈ region, ∃ u : X → ℝ, SolvesPotentialWaveAt wave potential u x ∧ u x ≠ 0

/-- **Local probes determine the potential on their region.** -/
theorem potential_eqOn_of_localProbes {wave : (X → ℝ) → (X → ℝ)}
    {potential other : X → ℝ} {region : Set X}
    (hlocal : ∀ x ∈ region, ∃ u : X → ℝ,
      SolvesPotentialWaveAt wave potential u x ∧
        SolvesPotentialWaveAt wave other u x ∧ u x ≠ 0) :
    Set.EqOn other potential region := by
  intro x hx
  obtain ⟨u, h₁, h₂, hu⟩ := hlocal x hx
  exact potential_eq_of_solvesPotentialWaveAt h₂ h₁ hu

/-- **A probe solving only on a region still determines the potential there.** -/
theorem potential_eqOn_of_solvesOn {wave : (X → ℝ) → (X → ℝ)}
    {potential other u : X → ℝ} {region : Set X}
    (h₁ : SolvesPotentialWaveOn wave potential u region)
    (h₂ : SolvesPotentialWaveOn wave other u region)
    (hu : ∀ x ∈ region, u x ≠ 0) :
    Set.EqOn other potential region := by
  intro x hx
  exact potential_eq_of_solvesPotentialWaveAt (h₂ x hx) (h₁ x hx) (hu x hx)

/-- The global determination theorem is the case `region = univ`. -/
theorem potential_eq_of_localProbes_univ {wave : (X → ℝ) → (X → ℝ)}
    {potential other : X → ℝ}
    (hlocal : ∀ x : X, ∃ u : X → ℝ,
      SolvesPotentialWaveAt wave potential u x ∧
        SolvesPotentialWaveAt wave other u x ∧ u x ≠ 0) :
    other = potential := by
  funext x
  exact potential_eqOn_of_localProbes (region := Set.univ)
    (fun y _ => hlocal y) (Set.mem_univ x)

/-- Globally solvable probe families give local probes, so the earlier statements are corollaries. -/
theorem localProbes_of_noCommonZero {wave : (X → ℝ) → (X → ℝ)} {potential : X → ℝ}
    (hno : NoCommonZero wave potential) (region : Set X) :
    LocalProbesOn wave potential region := by
  intro x _
  obtain ⟨u, hu, hux⟩ := hno x
  exact ⟨u, hu x, hux⟩

/-! ## The scale on a region -/

/-- **Local probes for both species reconstruct the conformal scale on their common region.** -/
theorem reconstructedScale_eqOn_of_localProbes
    {wave₁ wave₂ : (X → ℝ) → (X → ℝ)}
    {potential₁ potential₂ other₁ other₂ : X → ℝ} {massSq₁ massSq₂ : ℝ} {region : Set X}
    (hlocal₁ : ∀ x ∈ region, ∃ u : X → ℝ,
      SolvesPotentialWaveAt wave₁ potential₁ u x ∧
        SolvesPotentialWaveAt wave₁ other₁ u x ∧ u x ≠ 0)
    (hlocal₂ : ∀ x ∈ region, ∃ u : X → ℝ,
      SolvesPotentialWaveAt wave₂ potential₂ u x ∧
        SolvesPotentialWaveAt wave₂ other₂ u x ∧ u x ≠ 0) :
    Set.EqOn (reconstructedScale other₁ other₂ massSq₁ massSq₂)
      (reconstructedScale potential₁ potential₂ massSq₁ massSq₂) region := by
  intro x hx
  have e₁ := potential_eqOn_of_localProbes hlocal₁ hx
  have e₂ := potential_eqOn_of_localProbes hlocal₂ hx
  simp only [reconstructedScale, e₁, e₂]

/-! ## The local notion is strictly weaker -/

/-- A probe can solve on a proper region and nowhere else. -/
theorem exists_solvesOn_not_solves :
    ∃ (wave : (ℝ → ℝ) → (ℝ → ℝ)) (potential u : ℝ → ℝ) (region : Set ℝ),
      SolvesPotentialWaveOn wave potential u region ∧
        ¬ SolvesPotentialWave wave potential u := by
  refine ⟨fun _ => id, fun _ => 0, fun _ => 1, {0}, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    simp [SolvesPotentialWaveAt, hx]
  · intro h
    have := h 1
    simp at this

/-- The one-dimensional oscillatory probes are local probes on every region. -/
theorem localProbes_oscillatory (k : ℝ) (region : Set ℝ) :
    LocalProbesOn secondDeriv (fun _ => k ^ 2) region :=
  localProbes_of_noCommonZero (noCommonZero_oscillatory k) region

end GaloisForLFunctions.HTGeometry
