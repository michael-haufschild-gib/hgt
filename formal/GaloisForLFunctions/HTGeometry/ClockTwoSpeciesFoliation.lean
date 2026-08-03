import GaloisForLFunctions.HTGeometry.ClockTwoSpeciesBasisSlicing

/-!
# The two-species law on any chart admitting a foliation

The basis-slicing reconstruction still assumes a constant-signature chart and a coordinate slicing.
Neither is needed. The chain rule for the chart d'Alembertian turns a conformal factor constant on
the leaves of any foliation into a leaf-label function of the two foliation invariants:

`□(σ₀ ∘ φ) = Γ(φ,φ) σ₀''(φ) + (□φ) σ₀'(φ)`,  `Γ(σ₀∘φ, σ₀∘φ) = Γ(φ,φ) σ₀'(φ)²`.

So whenever `Γ(φ,φ) = P ∘ φ` with `P` nowhere zero and `□φ = R ∘ φ`, the effective potential of a
clock species is `V_μ^σ = F ∘ φ` with

`F(t) = μ e^{2σ₀(t)} - a(P(t)σ₀''(t) + R(t)σ₀'(t)) - a² P(t) σ₀'(t)²`,

probes for it are constructed by the foliation theorem, and two species with distinct calibrated
masses recover `e^{2σ}` pointwise.

This is the widest form of the card's headline reached so far: arbitrary chart, arbitrary foliation
with leaf-label invariants, arbitrary conformal factor constant on the leaves.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

variable {d : ℕ}

/-! ## The carré du champ of a composite -/

/-- **Chain rule for the carré du champ.** -/
theorem gradPair_comp (M : SmoothMetricChart d) {φ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hφ : DifferentiableAt ℝ φ x) {w : ℝ → ℝ} {c : ℝ} (hw : HasDerivAt w c (φ x)) :
    M.gradPair (fun y => w (φ y)) (fun y => w (φ y)) x = M.gradPair φ φ x * (c * c) := by
  simp only [SmoothMetricChart.gradPair]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordPartial_comp hφ hw i, coordPartial_comp hφ hw j]
  ring

/-! ## The effective potential as a leaf-label function -/

/-- Effective clock potential of a conformal factor constant on the leaves of a foliation. -/
noncomputable def foliationPotential (P R : ℝ → ℝ) (a massSq : ℝ) (σ₀ : ℝ → ℝ) : ℝ → ℝ :=
  fun t => massSq * Real.exp (2 * σ₀ t)
    - (a * (P t * deriv (deriv σ₀) t + R t * deriv σ₀ t)
        + a ^ 2 * (P t * (deriv σ₀ t * deriv σ₀ t)))

theorem conformalPotential_foliation (M : SmoothMetricChart d) {φ : (Fin d → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {P R : ℝ → ℝ}
    (hP : ∀ x, M.gradPair φ φ x = P (φ x)) (hR : ∀ x, M.dalembert φ x = R (φ x))
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a massSq : ℝ) (x : Fin d → ℝ) :
    M.conformalPotential a massSq (fun y => σ₀ (φ y)) x
      = foliationPotential P R a massSq σ₀ (φ x) := by
  have hd1 : ∀ t ∈ (Set.univ : Set ℝ), HasDerivAt σ₀ (deriv σ₀ t) t := fun t _ =>
    (hσ.differentiable (by simp) t).hasDerivAt
  have hd2 : ∀ t ∈ (Set.univ : Set ℝ), HasDerivAt (deriv σ₀) (deriv (deriv σ₀) t) t :=
    fun t _ => ((contDiff_deriv_infty hσ).differentiable (by simp) t).hasDerivAt
  have hdal := dalembert_comp M hφ isOpen_univ hd1 hd2 (x := x) (Set.mem_univ _)
  have hgp := gradPair_comp M (differentiableAt_of_contDiff_infty hφ x)
    ((hσ.differentiable (by simp) (φ x)).hasDerivAt)
  rw [SmoothMetricChart.conformalPotential, SmoothMetricChart.conformalDefect, hdal, hgp,
    hP x, hR x, foliationPotential]

theorem contDiff_foliationPotential {P R : ℝ → ℝ} (hPc : ContDiff ℝ 1 P) (hRc : ContDiff ℝ 1 R)
    (a massSq : ℝ) {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) :
    ContDiff ℝ 1 (foliationPotential P R a massSq σ₀) := by
  have h1 : ContDiff ℝ ∞ (deriv σ₀) := contDiff_deriv_infty hσ
  have h2 : ContDiff ℝ ∞ (deriv (deriv σ₀)) := contDiff_deriv_infty h1
  have hexp : ContDiff ℝ 1 fun t => massSq * Real.exp (2 * σ₀ t) :=
    contDiff_const.mul ((Real.contDiff_exp.comp (contDiff_const.mul hσ)).of_le (by simp))
  have hterm1 : ContDiff ℝ 1 fun t =>
      a * (P t * deriv (deriv σ₀) t + R t * deriv σ₀ t) :=
    contDiff_const.mul ((hPc.mul (h2.of_le (by simp))).add (hRc.mul (h1.of_le (by simp))))
  have hterm2 : ContDiff ℝ 1 fun t => a ^ 2 * (P t * (deriv σ₀ t * deriv σ₀ t)) :=
    contDiff_const.mul (hPc.mul ((h1.of_le (by simp)).mul (h1.of_le (by simp))))
  exact hexp.sub (hterm1.add hterm2)

/-! ## Probes, determination, and the reconstruction -/

/-- **Clock probes for a species on a foliated conformal chart.** -/
theorem exists_foliationConformal_localProbe (M : SmoothMetricChart d)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) {P R : ℝ → ℝ}
    (hP : ∀ x, M.gradPair φ φ x = P (φ x)) (hR : ∀ x, M.dalembert φ x = R (φ x))
    (hPc : ContDiff ℝ 1 P) (hRc : ContDiff ℝ 1 R) (hP0 : ∀ t, P t ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a massSq b : ℝ) :
    ∃ (u : (Fin d → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin d → ℝ, φ x = b → u x = 1) ∧
      (∀ x : Fin d → ℝ, φ x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert
          (fun y => foliationPotential P R a massSq σ₀ (φ y)) u x) :=
  exists_foliation_localProbe hφ hP hR hPc hRc hP0
    (contDiff_foliationPotential hPc hRc a massSq hσ) b

/-- **The effective potential is pinned by the species' clock data.** -/
theorem foliationConformal_potential_determined (M : SmoothMetricChart d)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) {P R : ℝ → ℝ}
    (hP : ∀ x, M.gradPair φ φ x = P (φ x)) (hR : ∀ x, M.dalembert φ x = R (φ x))
    (hPc : ContDiff ℝ 1 P) (hRc : ContDiff ℝ 1 R) (hP0 : ∀ t, P t ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a massSq : ℝ)
    {other : (Fin d → ℝ) → ℝ}
    (hother : ∀ (b : ℝ) (u : (Fin d → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin d → ℝ, φ x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert
          (fun y => foliationPotential P R a massSq σ₀ (φ y)) u x) →
      (∀ x : Fin d → ℝ, φ x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert other u x)) :
    other = fun y => foliationPotential P R a massSq σ₀ (φ y) :=
  chartPotential_eq_of_foliation hφ hP hR hPc hRc hP0
    (contDiff_foliationPotential hPc hRc a massSq hσ) hother

theorem foliationPotential_difference (P R : ℝ → ℝ) (a massSq₁ massSq₂ : ℝ) (σ₀ : ℝ → ℝ)
    (t : ℝ) :
    foliationPotential P R a massSq₁ σ₀ t - foliationPotential P R a massSq₂ σ₀ t
      = (massSq₁ - massSq₂) * Real.exp (2 * σ₀ t) := by
  simp only [foliationPotential]
  ring

/-- **The two-species law on any chart admitting a foliation with leaf-label invariants.** -/
theorem twoSpecies_foliation_reconstruction (M : SmoothMetricChart d)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) {P R : ℝ → ℝ}
    (hP : ∀ x, M.gradPair φ φ x = P (φ x)) (hR : ∀ x, M.dalembert φ x = R (φ x))
    (hPc : ContDiff ℝ 1 P) (hRc : ContDiff ℝ 1 R) (hP0 : ∀ t, P t ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a : ℝ)
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    {other₁ other₂ : (Fin d → ℝ) → ℝ}
    (h₁ : ∀ (b : ℝ) (u : (Fin d → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin d → ℝ, φ x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert
          (fun y => foliationPotential P R a massSq₁ σ₀ (φ y)) u x) →
      (∀ x : Fin d → ℝ, φ x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert other₁ u x))
    (h₂ : ∀ (b : ℝ) (u : (Fin d → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin d → ℝ, φ x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert
          (fun y => foliationPotential P R a massSq₂ σ₀ (φ y)) u x) →
      (∀ x : Fin d → ℝ, φ x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert other₂ u x))
    (x : Fin d → ℝ) :
    reconstructedScale other₁ other₂ massSq₁ massSq₂ x = Real.exp (2 * σ₀ (φ x)) := by
  rw [foliationConformal_potential_determined M hφ hP hR hPc hRc hP0 hσ a massSq₁ h₁,
    foliationConformal_potential_determined M hφ hP hR hPc hRc hP0 hσ a massSq₂ h₂,
    reconstructedScale]
  show (foliationPotential P R a massSq₁ σ₀ (φ x)
      - foliationPotential P R a massSq₂ σ₀ (φ x)) / (massSq₁ - massSq₂)
    = Real.exp (2 * σ₀ (φ x))
  rw [foliationPotential_difference]
  field_simp [sub_ne_zero.mpr hmass]

/-- The determined object is the card's own effective potential `V_μ^σ`. -/
theorem conformalPotential_eq_foliationPotential (M : SmoothMetricChart d)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) {P R : ℝ → ℝ}
    (hP : ∀ x, M.gradPair φ φ x = P (φ x)) (hR : ∀ x, M.dalembert φ x = R (φ x))
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a massSq : ℝ) :
    M.conformalPotential a massSq (fun y => σ₀ (φ y))
      = fun y => foliationPotential P R a massSq σ₀ (φ y) := by
  funext x
  exact conformalPotential_foliation M hφ hP hR hσ a massSq x

end GaloisForLFunctions.HTGeometry
