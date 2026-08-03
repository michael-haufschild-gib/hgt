import GaloisForLFunctions.HTGeometry.ClockProbeAxisExponential

/-!
# A single nowhere-vanishing probe determines the potential on any geometry

The flat construction used a transitive translation action. That hypothesis is removable. A probe
that vanishes nowhere has determination locus the whole event set by itself, so no group action, no
homogeneity and no flatness are needed.

Running the wave equation backwards turns this into a construction rather than a hypothesis: for
*any* nowhere-vanishing `u`, the potential `-(□u)/u` is solved by `u`, and it is the only potential
that is. The potentials admitting a nowhere-vanishing probe are therefore exactly the potentials of
that form, and every one of them is completely determined.

On a conformally rescaled Minkowski chart — a genuinely non-flat geometry — every exponential
`e^{f}` is such a probe, so the determination statement covers a variable-potential family on a
curved background.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff

universe u

/-! ## The potential induced by a nowhere-vanishing probe -/

section Induced

variable {X : Type u}

/-- The potential that a given probe solves. -/
noncomputable def inducedPotential (wave : (X → ℝ) → (X → ℝ)) (u : X → ℝ) : X → ℝ :=
  fun x => -(wave u x / u x)

/-- **Every nowhere-vanishing probe solves an explicit potential.** -/
theorem solvesPotentialWave_inducedPotential (wave : (X → ℝ) → (X → ℝ)) {u : X → ℝ}
    (hu : ∀ x, u x ≠ 0) : SolvesPotentialWave wave (inducedPotential wave u) u := by
  intro x
  simp only [inducedPotential]
  rw [neg_mul, div_mul_cancel₀ _ (hu x)]
  ring

/-- A nowhere-vanishing probe determines the potential at every event by itself. -/
theorem potentialDeterminationSet_singleton_of_ne_zero {u : X → ℝ} (hu : ∀ x, u x ≠ 0) :
    potentialDeterminationSet {u} = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  exact ⟨u, rfl, hu x⟩

/-- **One nowhere-vanishing probe pins the potential globally, on any geometry.** -/
theorem potential_eq_inducedPotential {wave : (X → ℝ) → (X → ℝ)} {u : X → ℝ}
    (hu : ∀ x, u x ≠ 0) {other : X → ℝ} (hother : SolvesPotentialWave wave other u) :
    other = inducedPotential wave u := by
  funext x
  exact potential_eq_of_solvesPotentialWave hother
    (solvesPotentialWave_inducedPotential wave hu) (hu x)

/-- **Characterization.** A potential admits a nowhere-vanishing probe exactly when it is induced
by one. -/
theorem exists_nonvanishing_probe_iff (wave : (X → ℝ) → (X → ℝ)) (potential : X → ℝ) :
    (∃ u : X → ℝ, (∀ x, u x ≠ 0) ∧ SolvesPotentialWave wave potential u) ↔
      ∃ u : X → ℝ, (∀ x, u x ≠ 0) ∧ potential = inducedPotential wave u := by
  constructor
  · rintro ⟨u, hu, hsolve⟩
    exact ⟨u, hu, potential_eq_inducedPotential hu hsolve⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, solvesPotentialWave_inducedPotential wave hu⟩

/-- **Two nowhere-vanishing probes reconstruct the conformal scale on any geometry.** -/
theorem reconstructedScale_eq_of_nonvanishing_probes
    {wave₁ wave₂ : (X → ℝ) → (X → ℝ)} {u₁ u₂ : X → ℝ}
    (hu₁ : ∀ x, u₁ x ≠ 0) (hu₂ : ∀ x, u₂ x ≠ 0)
    {potential₁ potential₂ other₁ other₂ : X → ℝ} {massSq₁ massSq₂ : ℝ}
    (h₁ : SolvesPotentialWave wave₁ potential₁ u₁)
    (hother₁ : SolvesPotentialWave wave₁ other₁ u₁)
    (h₂ : SolvesPotentialWave wave₂ potential₂ u₂)
    (hother₂ : SolvesPotentialWave wave₂ other₂ u₂) :
    reconstructedScale potential₁ potential₂ massSq₁ massSq₂ =
      reconstructedScale other₁ other₂ massSq₁ massSq₂ := by
  have e₁ : potential₁ = other₁ :=
    (potential_eq_inducedPotential hu₁ h₁).trans
      (potential_eq_inducedPotential hu₁ hother₁).symm
  have e₂ : potential₂ = other₂ :=
    (potential_eq_inducedPotential hu₂ h₂).trans
      (potential_eq_inducedPotential hu₂ hother₂).symm
  rw [e₁, e₂]

end Induced

/-! ## Exponential probes on an arbitrary smooth chart -/

section Chart

variable {d : ℕ}

/-- Exponentials never vanish, so they are probes on every geometry. -/
theorem exp_comp_ne_zero (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Real.exp (f x) ≠ 0 :=
  Real.exp_ne_zero _

/-- **On any smooth metric chart, every exponential probe determines its potential everywhere.** -/
theorem potential_eq_inducedPotential_exp (M : SmoothMetricChart d)
    (f : (Fin d → ℝ) → ℝ) {other : (Fin d → ℝ) → ℝ}
    (hother : SolvesPotentialWave M.dalembert other (fun x => Real.exp (f x))) :
    other = inducedPotential M.dalembert (fun x => Real.exp (f x)) :=
  potential_eq_inducedPotential (fun x => exp_comp_ne_zero f x) hother

/-- **The determination statement covers a curved background.** On a conformally rescaled Minkowski
chart every exponential probe determines its potential at every event. -/
theorem potential_eq_inducedPotential_exp_conformalMinkowski
    {sigma : (Fin d → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    (f : (Fin d → ℝ) → ℝ) {other : (Fin d → ℝ) → ℝ}
    (hother : SolvesPotentialWave
      ((SmoothPseudoMetric.minkowski d).conformal sigma hsigma).chart.dalembert other
      (fun x => Real.exp (f x))) :
    other = inducedPotential
      ((SmoothPseudoMetric.minkowski d).conformal sigma hsigma).chart.dalembert
      (fun x => Real.exp (f x)) :=
  potential_eq_inducedPotential_exp _ f hother

/-- **Two exponential probes reconstruct the conformal scale on a curved background.** -/
theorem reconstructedScale_eq_of_exp_probes (M₁ M₂ : SmoothMetricChart d)
    (f₁ f₂ : (Fin d → ℝ) → ℝ)
    {potential₁ potential₂ other₁ other₂ : (Fin d → ℝ) → ℝ} {massSq₁ massSq₂ : ℝ}
    (h₁ : SolvesPotentialWave M₁.dalembert potential₁ (fun x => Real.exp (f₁ x)))
    (hother₁ : SolvesPotentialWave M₁.dalembert other₁ (fun x => Real.exp (f₁ x)))
    (h₂ : SolvesPotentialWave M₂.dalembert potential₂ (fun x => Real.exp (f₂ x)))
    (hother₂ : SolvesPotentialWave M₂.dalembert other₂ (fun x => Real.exp (f₂ x))) :
    reconstructedScale potential₁ potential₂ massSq₁ massSq₂ =
      reconstructedScale other₁ other₂ massSq₁ massSq₂ :=
  reconstructedScale_eq_of_nonvanishing_probes (fun x => exp_comp_ne_zero f₁ x)
    (fun x => exp_comp_ne_zero f₂ x) h₁ hother₁ h₂ hother₂

end Chart

end GaloisForLFunctions.HTGeometry
