import GaloisForLFunctions.HTGeometry.ClockPotentialLocalDetermination
import GaloisForLFunctions.HTGeometry.ClockProbeSeparablePotential
import GaloisForLFunctions.HTGeometry.ConformalMetricClockCalculus

/-!
# The conformal calculus at the regularity a probe actually has

The divergence-form operator of a chart differentiates a function twice, and its conformal
transformation law differentiates the flux once. Neither consumes infinite smoothness: what is used
is that the function and each of its first partial derivatives are differentiable.

A clock probe produced by a hyperbolic construction is known to have exactly that much regularity
and no more, so the conformal law and the Leibniz rules are proved here under it. The consequence is
that probes transfer along a conformal rescaling of the chart, with an explicit transformation of
the potential in which no first-order derivative of the field survives.
-/

namespace GaloisForLFunctions.HTGeometry

open ExponentialSecondOrderClockCalculus

open scoped ContDiff

namespace SmoothMetricChart

variable {d : ℕ} (M : SmoothMetricChart d)

/-! ## The regularity class -/

/-- A function whose value and first partial derivatives are differentiable everywhere. This is the
regularity the divergence-form operator consumes. -/
structure DifferentiablePartials (u : (Fin d → ℝ) → ℝ) : Prop where
  base : ∀ x : Fin d → ℝ, DifferentiableAt ℝ u x
  coord : ∀ (i : Fin d) (x : Fin d → ℝ), DifferentiableAt ℝ (coordPartial i u) x

theorem DifferentiablePartials.of_contDiff {u : (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) :
    DifferentiablePartials u where
  base := fun x => differentiableAt_of_contDiff_infty hu x
  coord := fun i x => differentiableAt_of_contDiff_infty (contDiff_coordPartial hu i) x

theorem coordPartial_mul_fun {f u : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hu : DifferentiablePartials u) (i : Fin d) :
    coordPartial i (fun y => f y * u y) =
      fun y => f y * coordPartial i u y + u y * coordPartial i f y := by
  funext y
  exact coordPartial_mul (differentiableAt_of_contDiff_infty hf y) (hu.base y) i

theorem DifferentiablePartials.mul_left {f u : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hu : DifferentiablePartials u) : DifferentiablePartials (fun y => f y * u y) where
  base := fun x => (differentiableAt_of_contDiff_infty hf x).mul (hu.base x)
  coord := by
    intro i x
    rw [coordPartial_mul_fun hf hu i]
    exact ((differentiableAt_of_contDiff_infty hf x).mul (hu.coord i x)).add
      ((hu.base x).mul (differentiableAt_of_contDiff_infty (contDiff_coordPartial hf i) x))

/-! ## The regularity class on a region -/

/-- The same regularity, asked only on a region: what a probe solving on a tube actually has. -/
structure DifferentiablePartialsOn (u : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) : Prop where
  base : ∀ x ∈ W, DifferentiableAt ℝ u x
  coord : ∀ (i : Fin d), ∀ x ∈ W, DifferentiableAt ℝ (coordPartial i u) x

theorem DifferentiablePartials.on {u : (Fin d → ℝ) → ℝ} (hu : DifferentiablePartials u)
    (W : Set (Fin d → ℝ)) : DifferentiablePartialsOn u W where
  base := fun x _ => hu.base x
  coord := fun i x _ => hu.coord i x

theorem DifferentiablePartialsOn.mono {u : (Fin d → ℝ) → ℝ} {W W' : Set (Fin d → ℝ)}
    (h : W' ⊆ W) (hu : DifferentiablePartialsOn u W) : DifferentiablePartialsOn u W' where
  base := fun x hx => hu.base x (h hx)
  coord := fun i x hx => hu.coord i x (h hx)

theorem coordPartial_mul_eqOn {f u : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hf : ContDiff ℝ ∞ f) (hu : DifferentiablePartialsOn u W) (i : Fin d) :
    Set.EqOn (coordPartial i fun y => f y * u y)
      (fun y => f y * coordPartial i u y + u y * coordPartial i f y) W := by
  intro y hy
  exact coordPartial_mul (differentiableAt_of_contDiff_infty hf y) (hu.base y hy) i

theorem DifferentiablePartialsOn.mul_left {f u : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hW : IsOpen W) (hf : ContDiff ℝ ∞ f) (hu : DifferentiablePartialsOn u W) :
    DifferentiablePartialsOn (fun y => f y * u y) W where
  base := fun x hx => (differentiableAt_of_contDiff_infty hf x).mul (hu.base x hx)
  coord := by
    intro i x hx
    have heq : (coordPartial i fun y => f y * u y) =ᶠ[nhds x]
        fun y => f y * coordPartial i u y + u y * coordPartial i f y :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx) (coordPartial_mul_eqOn hf hu i)
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    exact ((differentiableAt_of_contDiff_infty hf x).mul (hu.coord i x hx)).add
      ((hu.base x hx).mul (differentiableAt_of_contDiff_infty (contDiff_coordPartial hf i) x))

/-! ## The flux is differentiable -/

theorem differentiableAt_flux_on {u : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hu : DifferentiablePartialsOn u W) (i : Fin d) {x : Fin d → ℝ} (hx : x ∈ W) :
    DifferentiableAt ℝ (M.flux u i) x := by
  show DifferentiableAt ℝ
    (fun y => M.density y * ∑ j, M.inverseMetric y i j * coordPartial j u y) x
  refine (differentiableAt_of_contDiff_infty M.contDiff_density x).mul ?_
  have hterm : ∀ j : Fin d, DifferentiableAt ℝ
      (fun y : Fin d → ℝ => M.inverseMetric y i j * coordPartial j u y) x := fun j =>
    (differentiableAt_of_contDiff_infty (M.contDiff_inverseMetric i j) x).mul (hu.coord j x hx)
  exact DifferentiableAt.fun_sum fun j _ => hterm j

theorem differentiableAt_flux {u : (Fin d → ℝ) → ℝ} (hu : DifferentiablePartials u) (i : Fin d)
    (x : Fin d → ℝ) : DifferentiableAt ℝ (M.flux u i) x :=
  M.differentiableAt_flux_on (hu.on Set.univ) i (Set.mem_univ x)

/-! ## The conformal transformation law -/

/-- **The conformal transformation law of the d'Alembertian, at probe regularity.** -/
theorem dalembert_conformalRescale_of_differentiablePartialsOn (sigma : (Fin d → ℝ) → ℝ)
    (hsigma : ContDiff ℝ ∞ sigma) {u : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hu : DifferentiablePartialsOn u W) {x : Fin d → ℝ} (hx : x ∈ W) :
    (M.conformalRescale sigma hsigma).dalembert u x =
      Real.exp (-2 * sigma x) *
        (M.dalembert u x + ((d : ℝ) - 2) * M.gradPair sigma u x) := by
  have hweight : ContDiff ℝ ∞ fun y => Real.exp (((d : ℝ) - 2) * sigma y) :=
    Real.contDiff_exp.comp (contDiff_const.mul hsigma)
  have hderiv : ∀ i : Fin d,
      coordPartial i ((M.conformalRescale sigma hsigma).flux u i) x =
        Real.exp (((d : ℝ) - 2) * sigma x) *
          (((d : ℝ) - 2) * coordPartial i sigma x * M.flux u i x +
            coordPartial i (M.flux u i) x) := by
    intro i
    rw [M.flux_conformalRescale sigma hsigma u i]
    rw [coordPartial_mul (differentiableAt_of_contDiff_infty hweight x)
      (M.differentiableAt_flux_on hu i hx) i]
    rw [coordPartial_exp
        (differentiableAt_of_contDiff_infty (contDiff_const.mul hsigma) x) i,
      coordPartial_const_mul (differentiableAt_of_contDiff_infty hsigma x) _ i]
    ring
  have hsum :
      ∑ i, coordPartial i ((M.conformalRescale sigma hsigma).flux u i) x =
        Real.exp (((d : ℝ) - 2) * sigma x) *
          (((d : ℝ) - 2) * ∑ i, coordPartial i sigma x * M.flux u i x +
            ∑ i, coordPartial i (M.flux u i) x) := by
    have h1 : ∑ i, coordPartial i ((M.conformalRescale sigma hsigma).flux u i) x =
        ∑ i, (Real.exp (((d : ℝ) - 2) * sigma x) *
              (((d : ℝ) - 2) * (coordPartial i sigma x * M.flux u i x)) +
            Real.exp (((d : ℝ) - 2) * sigma x) * coordPartial i (M.flux u i) x) :=
      Finset.sum_congr rfl fun i _ => by rw [hderiv i]; ring
    rw [h1, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
  have hinv : (Real.exp ((d : ℝ) * sigma x))⁻¹ * Real.exp (((d : ℝ) - 2) * sigma x) =
      Real.exp (-2 * sigma x) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hdensity : ((M.conformalRescale sigma hsigma).density x)⁻¹ =
      (Real.exp ((d : ℝ) * sigma x))⁻¹ * (M.density x)⁻¹ := by
    rw [conformalRescale_density, mul_inv]
  calc
    (M.conformalRescale sigma hsigma).dalembert u x
        = ((M.conformalRescale sigma hsigma).density x)⁻¹ *
            ∑ i, coordPartial i ((M.conformalRescale sigma hsigma).flux u i) x := rfl
    _ = ((Real.exp ((d : ℝ) * sigma x))⁻¹ * Real.exp (((d : ℝ) - 2) * sigma x)) *
          ((M.density x)⁻¹ *
            (((d : ℝ) - 2) * ∑ i, coordPartial i sigma x * M.flux u i x +
              ∑ i, coordPartial i (M.flux u i) x)) := by
          rw [hdensity, hsum]; ring
    _ = Real.exp (-2 * sigma x) *
          (((d : ℝ) - 2) *
              ((M.density x)⁻¹ * ∑ i, coordPartial i sigma x * M.flux u i x) +
            (M.density x)⁻¹ * ∑ i, coordPartial i (M.flux u i) x) := by
          rw [hinv]; ring
    _ = Real.exp (-2 * sigma x) *
          (M.dalembert u x + ((d : ℝ) - 2) * M.gradPair sigma u x) := by
          rw [M.inv_density_mul_sum_flux sigma u x]
          simp only [dalembert]
          ring

/-- **The conformal transformation law of the d'Alembertian, at probe regularity.** -/
theorem dalembert_conformalRescale_of_differentiablePartials (sigma : (Fin d → ℝ) → ℝ)
    (hsigma : ContDiff ℝ ∞ sigma) {u : (Fin d → ℝ) → ℝ} (hu : DifferentiablePartials u)
    (x : Fin d → ℝ) :
    (M.conformalRescale sigma hsigma).dalembert u x =
      Real.exp (-2 * sigma x) *
        (M.dalembert u x + ((d : ℝ) - 2) * M.gradPair sigma u x) :=
  M.dalembert_conformalRescale_of_differentiablePartialsOn sigma hsigma (hu.on Set.univ)
    (Set.mem_univ x)

/-! ## Leibniz rules with one smooth factor -/

theorem flux_mul_left_apply {f u : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hf : ContDiff ℝ ∞ f) (hu : DifferentiablePartialsOn u W) (i : Fin d) {x : Fin d → ℝ}
    (hx : x ∈ W) :
    M.flux (fun y => f y * u y) i x = f x * M.flux u i x + u x * M.flux f i x := by
  have hpd : ∀ j : Fin d, coordPartial j (fun y => f y * u y) x =
      f x * coordPartial j u x + u x * coordPartial j f x := fun j =>
    coordPartial_mul (differentiableAt_of_contDiff_infty hf x) (hu.base x hx) j
  simp only [flux]
  have hstep : ∑ j, M.inverseMetric x i j * coordPartial j (fun y => f y * u y) x =
      f x * (∑ j, M.inverseMetric x i j * coordPartial j u x) +
        u x * (∑ j, M.inverseMetric x i j * coordPartial j f x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hpd j]; ring
  rw [hstep]
  ring

theorem flux_mul_left {f u : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hu : DifferentiablePartials u) (i : Fin d) :
    M.flux (fun y => f y * u y) i =
      fun x => f x * M.flux u i x + u x * M.flux f i x := by
  funext x
  exact M.flux_mul_left_apply hf (hu.on Set.univ) i (Set.mem_univ x)

theorem gradPair_mul_right_left_on (k : (Fin d → ℝ) → ℝ) {f u : (Fin d → ℝ) → ℝ}
    {W : Set (Fin d → ℝ)} (hf : ContDiff ℝ ∞ f) (hu : DifferentiablePartialsOn u W)
    {x : Fin d → ℝ} (hx : x ∈ W) :
    M.gradPair k (fun y => f y * u y) x =
      f x * M.gradPair k u x + u x * M.gradPair k f x := by
  have hpd : ∀ j : Fin d, coordPartial j (fun y => f y * u y) x =
      f x * coordPartial j u x + u x * coordPartial j f x := fun j =>
    coordPartial_mul (differentiableAt_of_contDiff_infty hf x) (hu.base x hx) j
  simp only [gradPair]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hpd j]
  ring

theorem gradPair_mul_right_left (k : (Fin d → ℝ) → ℝ) {f u : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : DifferentiablePartials u) (x : Fin d → ℝ) :
    M.gradPair k (fun y => f y * u y) x =
      f x * M.gradPair k u x + u x * M.gradPair k f x :=
  M.gradPair_mul_right_left_on k hf (hu.on Set.univ) (Set.mem_univ x)

/-- **The second-order Leibniz rule with one smooth factor**, at probe regularity. -/
theorem dalembert_mul_left_on {f u : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (hW : IsOpen W)
    (hf : ContDiff ℝ ∞ f) (hu : DifferentiablePartialsOn u W) {x : Fin d → ℝ} (hx : x ∈ W) :
    M.dalembert (fun y => f y * u y) x =
      f x * M.dalembert u x + u x * M.dalembert f x + 2 * M.gradPair f u x := by
  have hfluxf := M.contDiff_flux hf
  have hd : ∀ i : Fin d,
      coordPartial i (M.flux (fun y => f y * u y) i) x =
        f x * coordPartial i (M.flux u i) x + M.flux u i x * coordPartial i f x +
          (u x * coordPartial i (M.flux f i) x + M.flux f i x * coordPartial i u x) := by
    intro i
    have hfluxeq : M.flux (fun y => f y * u y) i =ᶠ[nhds x]
        fun y => f y * M.flux u i y + u y * M.flux f i y :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx) fun y hy => M.flux_mul_left_apply hf hu i hy
    rw [coordPartial_congr hfluxeq i]
    have h₁ : DifferentiableAt ℝ (fun y : Fin d → ℝ => f y * M.flux u i y) x :=
      (differentiableAt_of_contDiff_infty hf x).mul (M.differentiableAt_flux_on hu i hx)
    have h₂ : DifferentiableAt ℝ (fun y : Fin d → ℝ => u y * M.flux f i y) x :=
      (hu.base x hx).mul (differentiableAt_of_contDiff_infty (hfluxf i) x)
    rw [coordPartial_add h₁ h₂ i]
    rw [coordPartial_mul (differentiableAt_of_contDiff_infty hf x)
        (M.differentiableAt_flux_on hu i hx) i,
      coordPartial_mul (hu.base x hx)
        (differentiableAt_of_contDiff_infty (hfluxf i) x) i]
  have hsplit : ∑ i, coordPartial i (M.flux (fun y => f y * u y) i) x =
      f x * (∑ i, coordPartial i (M.flux u i) x) +
        u x * (∑ i, coordPartial i (M.flux f i) x) +
        (∑ i, coordPartial i f x * M.flux u i x) +
        (∑ i, coordPartial i u x * M.flux f i x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hd i]; ring
  have h1 := M.inv_density_mul_sum_flux f u x
  have h2 := M.inv_density_mul_sum_flux u f x
  have h3 := M.gradPair_comm u f x
  simp only [dalembert]
  rw [hsplit]
  have hring : (M.density x)⁻¹ *
      (f x * (∑ i, coordPartial i (M.flux u i) x) +
        u x * (∑ i, coordPartial i (M.flux f i) x) +
        (∑ i, coordPartial i f x * M.flux u i x) +
        (∑ i, coordPartial i u x * M.flux f i x)) =
      f x * ((M.density x)⁻¹ * ∑ i, coordPartial i (M.flux u i) x) +
        u x * ((M.density x)⁻¹ * ∑ i, coordPartial i (M.flux f i) x) +
        ((M.density x)⁻¹ * ∑ i, coordPartial i f x * M.flux u i x) +
        ((M.density x)⁻¹ * ∑ i, coordPartial i u x * M.flux f i x) := by ring
  rw [hring, h1, h2, h3]
  ring

/-- **The second-order Leibniz rule with one smooth factor**, at probe regularity. -/
theorem dalembert_mul_left {f u : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hu : DifferentiablePartials u) (x : Fin d → ℝ) :
    M.dalembert (fun y => f y * u y) x =
      f x * M.dalembert u x + u x * M.dalembert f x + 2 * M.gradPair f u x :=
  M.dalembert_mul_left_on isOpen_univ hf (hu.on Set.univ) (Set.mem_univ x)

/-! ## Conjugation by the conformal weight -/

/-- **The conformal conjugation identity at probe regularity.** Conjugating by `e^{-aσ}`,
`a = (d-2)/2`, cancels every first-order derivative of the field: only the original operator and a
scalar defect survive. -/
theorem dalembert_conformalRescale_conjugation_of_differentiablePartialsOn
    (sigma : (Fin d → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma) {u : (Fin d → ℝ) → ℝ}
    {W : Set (Fin d → ℝ)} (hW : IsOpen W) (hu : DifferentiablePartialsOn u W)
    {x : Fin d → ℝ} (hx : x ∈ W) :
    (M.conformalRescale sigma hsigma).dalembert
        (fun y => Real.exp (-conformalDimensionWeight d * sigma y) * u y) x =
      Real.exp (-2 * sigma x) * Real.exp (-conformalDimensionWeight d * sigma x) *
        (M.dalembert u x -
          (conformalDimensionWeight d * M.dalembert sigma x +
            conformalDimensionWeight d ^ (2 : ℕ) * M.gradPair sigma sigma x) * u x) := by
  set a : ℝ := conformalDimensionWeight d with ha
  have hweight : ContDiff ℝ ∞ fun y => Real.exp (-a * sigma y) :=
    Real.contDiff_exp.comp (contDiff_const.mul hsigma)
  have hprod : DifferentiablePartialsOn (fun y => Real.exp (-a * sigma y) * u y) W :=
    DifferentiablePartialsOn.mul_left hW hweight hu
  have hdim : ((d : ℝ) - 2) = 2 * a := by
    rw [ha, conformalDimensionWeight]
    ring
  rw [M.dalembert_conformalRescale_of_differentiablePartialsOn sigma hsigma hprod hx,
    M.dalembert_mul_left_on hW hweight hu hx, M.dalembert_expSmul (-a) hsigma x,
    M.gradPair_expSmul_left (-a) hsigma u x,
    M.gradPair_mul_right_left_on sigma hweight hu hx,
    M.gradPair_expSmul_right (-a) hsigma sigma x, hdim]
  ring

/-- **The conformal conjugation identity at probe regularity.** -/
theorem dalembert_conformalRescale_conjugation_of_differentiablePartials
    (sigma : (Fin d → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma) {u : (Fin d → ℝ) → ℝ}
    (hu : DifferentiablePartials u) (x : Fin d → ℝ) :
    (M.conformalRescale sigma hsigma).dalembert
        (fun y => Real.exp (-conformalDimensionWeight d * sigma y) * u y) x =
      Real.exp (-2 * sigma x) * Real.exp (-conformalDimensionWeight d * sigma x) *
        (M.dalembert u x -
          (conformalDimensionWeight d * M.dalembert sigma x +
            conformalDimensionWeight d ^ (2 : ℕ) * M.gradPair sigma sigma x) * u x) :=
  M.dalembert_conformalRescale_conjugation_of_differentiablePartialsOn sigma hsigma isOpen_univ
    (hu.on Set.univ) (Set.mem_univ x)

/-! ## Probe transfer -/

/-- The potential seen on the rescaled chart by the conjugated field. -/
noncomputable def conformalTransferPotential (sigma V : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun x => Real.exp (-2 * sigma x) *
    (V x + conformalDimensionWeight d * M.dalembert sigma x +
      conformalDimensionWeight d ^ (2 : ℕ) * M.gradPair sigma sigma x)

/-- **Probes transfer along a conformal rescaling.** A field solving the potential wave equation on
the chart gives, after conjugation by the conformal weight, a field solving it on the rescaled chart
for the transferred potential. -/
theorem solvesPotentialWaveAt_conformalRescale_on (sigma : (Fin d → ℝ) → ℝ)
    (hsigma : ContDiff ℝ ∞ sigma) {V u : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (hW : IsOpen W)
    (hu : DifferentiablePartialsOn u W) {x : Fin d → ℝ} (hx : x ∈ W)
    (h : SolvesPotentialWaveAt M.dalembert V u x) :
    SolvesPotentialWaveAt (M.conformalRescale sigma hsigma).dalembert
      (M.conformalTransferPotential sigma V)
      (fun y => Real.exp (-conformalDimensionWeight d * sigma y) * u y) x := by
  set a : ℝ := conformalDimensionWeight d with ha
  have hwave : M.dalembert u x = -(V x * u x) := by
    have := h
    rw [SolvesPotentialWaveAt] at this
    linarith
  show (M.conformalRescale sigma hsigma).dalembert
      (fun y => Real.exp (-a * sigma y) * u y) x +
      M.conformalTransferPotential sigma V x * (Real.exp (-a * sigma x) * u x) = 0
  rw [M.dalembert_conformalRescale_conjugation_of_differentiablePartialsOn sigma hsigma hW hu hx,
    conformalTransferPotential, hwave]
  ring

/-- **Probes transfer along a conformal rescaling.** -/
theorem solvesPotentialWaveAt_conformalRescale (sigma : (Fin d → ℝ) → ℝ)
    (hsigma : ContDiff ℝ ∞ sigma) {V u : (Fin d → ℝ) → ℝ} (hu : DifferentiablePartials u)
    {x : Fin d → ℝ} (h : SolvesPotentialWaveAt M.dalembert V u x) :
    SolvesPotentialWaveAt (M.conformalRescale sigma hsigma).dalembert
      (M.conformalTransferPotential sigma V)
      (fun y => Real.exp (-conformalDimensionWeight d * sigma y) * u y) x :=
  M.solvesPotentialWaveAt_conformalRescale_on sigma hsigma isOpen_univ (hu.on Set.univ)
    (Set.mem_univ x) h

end SmoothMetricChart

end GaloisForLFunctions.HTGeometry
