import GaloisForLFunctions.HTGeometry.ClockTwoSpeciesConformalTime

/-!
# The two-species law along an arbitrary non-null basis slicing

The conformal-time reconstruction singles out the zeroth coordinate. The argument uses nothing about
it beyond non-nullity, so it runs along any basis direction of a constant-signature chart.

For a conformal factor constant on the level sets of the `k`-th coordinate the effective potential
of a clock species is again a function of that coordinate,

`V_μ^σ(x) = μ e^{2σ(xᵏ)} - a (ε_k)⁻¹ σ''(xᵏ) - a² (ε_k)⁻¹ σ'(xᵏ)²`,

probes exist by the covector-slicing theorem, and two species with distinct calibrated masses
recover `e^{2σ}` pointwise.

Taking `k = 0` is the cosmological case. Taking `k` spatial is the **static** case: a conformal
factor varying with height, which is the geometry of the clock-comparison experiment.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

variable {d : ℕ}

/-! ## The lifted conformal factor along a basis direction -/

theorem contDiff_basisLift {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (k : Fin (d + 1)) :
    ContDiff ℝ ∞ (covectorLift (Pi.single k (1 : ℝ)) σ₀) :=
  hσ.comp (contDiff_covectorPhase _)

theorem coordPartial_basisLift {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (k i : Fin (d + 1))
    (x : Fin (d + 1) → ℝ) :
    coordPartial i (covectorLift (Pi.single k (1 : ℝ)) σ₀) x
      = (if i = k then (1 : ℝ) else 0)
          * deriv σ₀ (covectorPhase (Pi.single k (1 : ℝ)) x) := by
  have hd : HasDerivAt σ₀ (deriv σ₀ (covectorPhase (Pi.single k (1 : ℝ)) x))
      (covectorPhase (Pi.single k (1 : ℝ)) x) :=
    (hσ.differentiable (by simp) _).hasDerivAt
  rw [coordPartial_covectorLift hd i, Pi.single_apply]

theorem coordPartial_basisLift_self {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (k : Fin (d + 1))
    (x : Fin (d + 1) → ℝ) :
    coordPartial k (covectorLift (Pi.single k (1 : ℝ)) σ₀) x
      = deriv σ₀ (covectorPhase (Pi.single k (1 : ℝ)) x) := by
  rw [coordPartial_basisLift hσ k k]
  simp

theorem coordPartial_basisLift_ne {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) {k i : Fin (d + 1)}
    (hi : i ≠ k) (x : Fin (d + 1) → ℝ) :
    coordPartial i (covectorLift (Pi.single k (1 : ℝ)) σ₀) x = 0 := by
  rw [coordPartial_basisLift hσ k i]
  simp [hi]

theorem coordPartial_sq_basisLift_self {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (k : Fin (d + 1))
    (x : Fin (d + 1) → ℝ) :
    coordPartial k (coordPartial k (covectorLift (Pi.single k (1 : ℝ)) σ₀)) x
      = deriv (deriv σ₀) (covectorPhase (Pi.single k (1 : ℝ)) x) := by
  have hfun : coordPartial k (covectorLift (Pi.single k (1 : ℝ)) σ₀)
      = covectorLift (Pi.single k (1 : ℝ)) (deriv σ₀) := by
    funext y
    exact coordPartial_basisLift_self hσ k y
  rw [hfun]
  exact coordPartial_basisLift_self (contDiff_deriv_infty hσ) k x

theorem coordPartial_sq_basisLift_ne {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) {k i : Fin (d + 1)}
    (hi : i ≠ k) (x : Fin (d + 1) → ℝ) :
    coordPartial i (coordPartial i (covectorLift (Pi.single k (1 : ℝ)) σ₀)) x = 0 := by
  have hfun : coordPartial i (covectorLift (Pi.single k (1 : ℝ)) σ₀) = fun _ => 0 := by
    funext y
    exact coordPartial_basisLift_ne hσ hi y
  rw [hfun]
  exact coordPartial_const i 0 x

theorem dalembert_basisLift_flat (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (k : Fin (d + 1)) (x : Fin (d + 1) → ℝ) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
        (covectorLift (Pi.single k (1 : ℝ)) σ₀) x
      = (eps k)⁻¹ * deriv (deriv σ₀) (covectorPhase (Pi.single k (1 : ℝ)) x) := by
  rw [SmoothPseudoMetric.ofSignature_dalembert eps heps (contDiff_basisLift hσ k) x,
    Finset.sum_eq_single k]
  · rw [coordPartial_sq_basisLift_self hσ k x]
  · intro i _ hi
    rw [coordPartial_sq_basisLift_ne hσ hi x, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem gradPair_basisLift_flat (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (k : Fin (d + 1)) (x : Fin (d + 1) → ℝ) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.gradPair
        (covectorLift (Pi.single k (1 : ℝ)) σ₀) (covectorLift (Pi.single k (1 : ℝ)) σ₀) x
      = (eps k)⁻¹ * (deriv σ₀ (covectorPhase (Pi.single k (1 : ℝ)) x)
          * deriv σ₀ (covectorPhase (Pi.single k (1 : ℝ)) x)) := by
  rw [ofSignature_gradPair, Finset.sum_eq_single k]
  · rw [coordPartial_basisLift_self hσ k x]
    ring
  · intro i _ hi
    rw [coordPartial_basisLift_ne hσ hi x]
    ring
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem conformalPotential_basisLift (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (k : Fin (d + 1)) (a massSq : ℝ)
    (x : Fin (d + 1) → ℝ) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.conformalPotential a massSq
        (covectorLift (Pi.single k (1 : ℝ)) σ₀) x
      = conformalTimePotential (eps k)⁻¹ a massSq σ₀
          (covectorPhase (Pi.single k (1 : ℝ)) x) := by
  rw [SmoothMetricChart.conformalPotential, SmoothMetricChart.conformalDefect,
    dalembert_basisLift_flat eps heps hσ k x, gradPair_basisLift_flat eps heps hσ k x,
    conformalTimePotential]
  rfl

/-! ## Probes and determination along the slicing -/

theorem flat_inverseMetric_slicing (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    (k : Fin (d + 1)) : ∀ x : Fin (d + 1) → ℝ,
    (SmoothPseudoMetric.ofSignature eps heps).chart.inverseMetric x
      = (fun _ : ℝ => Matrix.diagonal fun i => (eps i)⁻¹)
          (covectorPhase (Pi.single k (1 : ℝ)) x) := fun x =>
  SmoothPseudoMetric.ofSignature_inverseMetric eps heps x

theorem flat_density_slicing (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    (k : Fin (d + 1)) : ∀ x : Fin (d + 1) → ℝ,
    (SmoothPseudoMetric.ofSignature eps heps).chart.density x
      = (fun _ : ℝ => Real.sqrt |∏ j, eps j|)
          (covectorPhase (Pi.single k (1 : ℝ)) x) := fun x =>
  SmoothPseudoMetric.ofSignature_density eps heps x

theorem flat_slicing_coeff_contDiff (eps : Fin (d + 1) → ℝ) (i j : Fin (d + 1)) :
    ContDiff ℝ 1 fun t : ℝ =>
      (fun _ : ℝ => Matrix.diagonal fun l => (eps l)⁻¹) t i j := contDiff_const

theorem flat_slicing_norm_ne_zero (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    (k : Fin (d + 1)) (t : ℝ) :
    (fun _ : ℝ => Real.sqrt |∏ j, eps j|) t *
        covectorNorm (fun _ : ℝ => Matrix.diagonal fun i => (eps i)⁻¹)
          (Pi.single k (1 : ℝ)) t ≠ 0 := by
  have hpos : (0 : ℝ) < Real.sqrt |∏ j, eps j| := by
    rw [← SmoothPseudoMetric.ofSignature_density eps heps (0 : Fin (d + 1) → ℝ)]
    exact (SmoothPseudoMetric.ofSignature eps heps).chart.density_pos _
  rw [covectorNorm_basis]
  show Real.sqrt |∏ j, eps j| * (Matrix.diagonal fun i => (eps i)⁻¹) k k ≠ 0
  rw [Matrix.diagonal_apply_eq]
  exact mul_ne_zero (ne_of_gt hpos) (inv_ne_zero (heps k))

/-- **Clock probes for a species on a basis-sliced conformal chart.** -/
theorem exists_basisSlicing_localProbe (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (k : Fin (d + 1)) (a massSq b : ℝ) :
    ∃ (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin (d + 1) → ℝ, covectorPhase (Pi.single k (1 : ℝ)) x = b → u x = 1) ∧
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase (Pi.single k (1 : ℝ)) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (covectorLift (Pi.single k (1 : ℝ))
            (conformalTimePotential (eps k)⁻¹ a massSq σ₀)) u x) :=
  exists_covector_localProbe (flat_inverseMetric_slicing eps heps k)
    (flat_density_slicing eps heps k) contDiff_const (flat_slicing_coeff_contDiff eps)
    (flat_slicing_norm_ne_zero eps heps k)
    (contDiff_conformalTimePotential (eps k)⁻¹ a massSq hσ) b

/-- **The effective potential is pinned by the species' clock data.** -/
theorem basisSlicing_potential_determined (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (k : Fin (d + 1)) (a massSq : ℝ)
    {other : (Fin (d + 1) → ℝ) → ℝ}
    (hother : ∀ (b : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase (Pi.single k (1 : ℝ)) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (covectorLift (Pi.single k (1 : ℝ))
            (conformalTimePotential (eps k)⁻¹ a massSq σ₀)) u x) →
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase (Pi.single k (1 : ℝ)) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          other u x)) :
    other = covectorLift (Pi.single k (1 : ℝ))
      (conformalTimePotential (eps k)⁻¹ a massSq σ₀) :=
  chartPotential_eq_of_covector (flat_inverseMetric_slicing eps heps k)
    (flat_density_slicing eps heps k) contDiff_const (flat_slicing_coeff_contDiff eps)
    (flat_slicing_norm_ne_zero eps heps k)
    (contDiff_conformalTimePotential (eps k)⁻¹ a massSq hσ) hother

/-- **The two-species law along an arbitrary non-null basis slicing.** For `k = 0` this is the
cosmological reconstruction; for `k` spatial it is the static one, the geometry of two clocks at
different heights of a gravitational potential. -/
theorem twoSpecies_basisSlicing_reconstruction (eps : Fin (d + 1) → ℝ)
    (heps : ∀ i, eps i ≠ 0) {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (k : Fin (d + 1)) (a : ℝ)
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    {other₁ other₂ : (Fin (d + 1) → ℝ) → ℝ}
    (h₁ : ∀ (b : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase (Pi.single k (1 : ℝ)) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (covectorLift (Pi.single k (1 : ℝ))
            (conformalTimePotential (eps k)⁻¹ a massSq₁ σ₀)) u x) →
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase (Pi.single k (1 : ℝ)) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          other₁ u x))
    (h₂ : ∀ (b : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase (Pi.single k (1 : ℝ)) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (covectorLift (Pi.single k (1 : ℝ))
            (conformalTimePotential (eps k)⁻¹ a massSq₂ σ₀)) u x) →
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase (Pi.single k (1 : ℝ)) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          other₂ u x))
    (x : Fin (d + 1) → ℝ) :
    reconstructedScale other₁ other₂ massSq₁ massSq₂ x
      = Real.exp (2 * σ₀ (covectorPhase (Pi.single k (1 : ℝ)) x)) := by
  rw [basisSlicing_potential_determined eps heps hσ k a massSq₁ h₁,
    basisSlicing_potential_determined eps heps hσ k a massSq₂ h₂, reconstructedScale]
  show (conformalTimePotential (eps k)⁻¹ a massSq₁ σ₀
        (covectorPhase (Pi.single k (1 : ℝ)) x)
      - conformalTimePotential (eps k)⁻¹ a massSq₂ σ₀
        (covectorPhase (Pi.single k (1 : ℝ)) x)) / (massSq₁ - massSq₂)
    = Real.exp (2 * σ₀ (covectorPhase (Pi.single k (1 : ℝ)) x))
  rw [conformalTimePotential_difference]
  field_simp [sub_ne_zero.mpr hmass]

/-- **The static case.** On Minkowski space with the conformal factor a function of the first
spatial coordinate, two species recover the scale at every event. -/
theorem twoSpecies_staticSlicing_reconstruction {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a : ℝ)
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    {other₁ other₂ : (Fin (d + 1 + 1) → ℝ) → ℝ}
    (h₁ : ∀ (b : ℝ) (u : (Fin (d + 1 + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1 + 1) → ℝ,
        covectorPhase (Pi.single (1 : Fin (d + 1 + 1)) (1 : ℝ)) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.minkowski (d + 1 + 1)).chart.dalembert
          (covectorLift (Pi.single (1 : Fin (d + 1 + 1)) (1 : ℝ))
            (conformalTimePotential
              ((fun i : Fin (d + 1 + 1) => if (i : ℕ) = 0 then (-1 : ℝ) else 1) 1)⁻¹
              a massSq₁ σ₀)) u x) →
      (∀ x : Fin (d + 1 + 1) → ℝ,
        covectorPhase (Pi.single (1 : Fin (d + 1 + 1)) (1 : ℝ)) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.minkowski (d + 1 + 1)).chart.dalembert
          other₁ u x))
    (h₂ : ∀ (b : ℝ) (u : (Fin (d + 1 + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1 + 1) → ℝ,
        covectorPhase (Pi.single (1 : Fin (d + 1 + 1)) (1 : ℝ)) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.minkowski (d + 1 + 1)).chart.dalembert
          (covectorLift (Pi.single (1 : Fin (d + 1 + 1)) (1 : ℝ))
            (conformalTimePotential
              ((fun i : Fin (d + 1 + 1) => if (i : ℕ) = 0 then (-1 : ℝ) else 1) 1)⁻¹
              a massSq₂ σ₀)) u x) →
      (∀ x : Fin (d + 1 + 1) → ℝ,
        covectorPhase (Pi.single (1 : Fin (d + 1 + 1)) (1 : ℝ)) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.minkowski (d + 1 + 1)).chart.dalembert
          other₂ u x))
    (x : Fin (d + 1 + 1) → ℝ) :
    reconstructedScale other₁ other₂ massSq₁ massSq₂ x
      = Real.exp (2 * σ₀ (x 1)) := by
  have hbasis : covectorPhase (Pi.single (1 : Fin (d + 1 + 1)) (1 : ℝ)) x = x 1 :=
    covectorPhase_basis 1 x
  rw [← hbasis]
  exact twoSpecies_basisSlicing_reconstruction _ _ hσ 1 a hmass h₁ h₂ x

end GaloisForLFunctions.HTGeometry
