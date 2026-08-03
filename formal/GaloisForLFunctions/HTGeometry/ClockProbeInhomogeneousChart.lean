import GaloisForLFunctions.HTGeometry.ClockProbeFoliationReduction

/-!
# Clock probes in a chart inhomogeneous along its own leaves

The slicing theorems require the chart data to be constant on the leaves. The foliation theorem does
not: it asks only that the two invariants `Γ(φ,φ)` and `□φ` be functions of the leaf label. This
file exhibits a chart where the difference is real.

The metric is `g = diag(-1, e^{2σ}, …, e^{2σ})` for an **arbitrary** smooth conformal factor `σ`
subject to one condition: its derivative along the zeroth direction is a function of the zeroth
coordinate. Writing `σ = α(x⁰) + β(x)` with `β` transverse, the geometry varies arbitrarily along
each leaf `{x⁰ = const}`, so no slicing theorem applies — yet

`Γ(dx⁰, dx⁰) = -1`,  `□x⁰ = -d ∂₀σ`

are functions of `x⁰`, and the clock potential is determined.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

/-- Diagonal of the inverse conformally rescaled metric. -/
noncomputable def inhomDiag {d : ℕ} (σ : (Fin (d + 1) → ℝ) → ℝ) (x : Fin (d + 1) → ℝ)
    (i : Fin (d + 1)) : ℝ :=
  if i = 0 then -1 else Real.exp (-2 * σ x)

/-- The chart of `g = diag(-1, e^{2σ}, …, e^{2σ})` for an arbitrary smooth conformal factor. -/
noncomputable def inhomChart {d : ℕ} {σ : (Fin (d + 1) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) :
    SmoothMetricChart (d + 1) where
  inverseMetric x := Matrix.diagonal (inhomDiag σ x)
  density x := Real.exp (d * σ x)
  contDiff_inverseMetric := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
      by_cases hj0 : j = 0
      · rw [hj0]
        have h : (fun x : Fin (d + 1) → ℝ => Matrix.diagonal (inhomDiag σ x) 0 0)
            = fun _ => (-1 : ℝ) := by
          funext x
          simp [inhomDiag]
        rw [h]
        exact contDiff_const
      · have h : (fun x : Fin (d + 1) → ℝ => Matrix.diagonal (inhomDiag σ x) j j)
            = fun x => Real.exp (-2 * σ x) := by
          funext x
          simp [inhomDiag, hj0]
        rw [h]
        exact Real.contDiff_exp.comp (contDiff_const.mul hσ)
    · have h : (fun x : Fin (d + 1) → ℝ => Matrix.diagonal (inhomDiag σ x) i j)
          = fun _ => (0 : ℝ) := by
        funext x
        simp [hij]
      rw [h]
      exact contDiff_const
  contDiff_density := Real.contDiff_exp.comp (contDiff_const.mul hσ)
  density_pos := fun _ => Real.exp_pos _
  inverseMetric_symm := by
    intro x i j
    simp only [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rfl
    · rw [if_neg hij, if_neg (Ne.symm hij)]

theorem inhomChart_inverseMetric {d : ℕ} {σ : (Fin (d + 1) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (x : Fin (d + 1) → ℝ) (i j : Fin (d + 1)) :
    (inhomChart hσ).inverseMetric x i j = Matrix.diagonal (inhomDiag σ x) i j := rfl

theorem inhomChart_density {d : ℕ} {σ : (Fin (d + 1) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (x : Fin (d + 1) → ℝ) :
    (inhomChart (d := d) hσ).density x = Real.exp (d * σ x) := rfl

/-! ## The zeroth coordinate as leaf label -/

/-- Partial derivatives of a coordinate function. -/
theorem coordPartial_coord {d : ℕ} (i k : Fin d) (x : Fin d → ℝ) :
    coordPartial i (fun y : Fin d → ℝ => y k) x = if k = i then 1 else 0 := by
  have hp : HasFDerivAt (fun y : Fin d → ℝ => y k)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k).hasFDerivAt
  rw [coordPartial, hp.fderiv]
  simp [Pi.single_apply]

theorem coordPartial_coord_zero {d : ℕ} (x : Fin (d + 1) → ℝ) :
    coordPartial (0 : Fin (d + 1)) (fun y : Fin (d + 1) → ℝ => y 0) x = 1 := by
  rw [coordPartial_coord]
  simp

theorem coordPartial_coord_ne {d : ℕ} {i : Fin (d + 1)} (hi : i ≠ 0) (x : Fin (d + 1) → ℝ) :
    coordPartial i (fun y : Fin (d + 1) → ℝ => y 0) x = 0 := by
  rw [coordPartial_coord, if_neg (Ne.symm hi)]

theorem contDiff_coord_zero {d : ℕ} :
    ContDiff ℝ ∞ fun y : Fin (d + 1) → ℝ => y 0 :=
  contDiff_apply ℝ ℝ 0

/-- **The leaf label is null-free.** Its carré du champ is the constant `-1`. -/
theorem gradPair_coord_zero {d : ℕ} {σ : (Fin (d + 1) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (x : Fin (d + 1) → ℝ) :
    (inhomChart hσ).gradPair (fun y => y 0) (fun y => y 0) x = -1 := by
  rw [SmoothMetricChart.gradPair, Finset.sum_eq_single (0 : Fin (d + 1))]
  · rw [Finset.sum_eq_single (0 : Fin (d + 1))]
    · rw [coordPartial_coord_zero x, inhomChart_inverseMetric]
      simp [inhomDiag]
    · intro j _ hj
      rw [coordPartial_coord_ne hj x, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coordPartial_coord_ne hi x, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h

theorem flux_coord_zero_ne {d : ℕ} {σ : (Fin (d + 1) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    {i : Fin (d + 1)} (hi : i ≠ 0) :
    (inhomChart hσ).flux (fun y => y 0) i = fun _ => (0 : ℝ) := by
  funext y
  simp only [SmoothMetricChart.flux]
  have hs : ∑ j, (inhomChart hσ).inverseMetric y i j *
      coordPartial j (fun z : Fin (d + 1) → ℝ => z 0) y = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = 0
    · subst hj
      rw [inhomChart_inverseMetric]
      simp [hi]
    · rw [coordPartial_coord_ne hj y, mul_zero]
  rw [hs, mul_zero]

theorem flux_coord_zero_eq {d : ℕ} {σ : (Fin (d + 1) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) :
    (inhomChart (d := d) hσ).flux (fun y => y 0) 0
      = fun y => (-1 : ℝ) * Real.exp (d * σ y) := by
  funext y
  simp only [SmoothMetricChart.flux]
  have hs : ∑ j, (inhomChart hσ).inverseMetric y 0 j *
      coordPartial j (fun z : Fin (d + 1) → ℝ => z 0) y = -1 := by
    rw [Finset.sum_eq_single (0 : Fin (d + 1))]
    · rw [coordPartial_coord_zero y, inhomChart_inverseMetric]
      simp [inhomDiag]
    · intro j _ hj
      rw [coordPartial_coord_ne hj y, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h
  rw [hs, inhomChart_density]
  ring

/-- **The d'Alembertian of the leaf label** is the drift of the conformal factor. -/
theorem dalembert_coord_zero {d : ℕ} {σ : (Fin (d + 1) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (x : Fin (d + 1) → ℝ) :
    (inhomChart hσ).dalembert (fun y => y 0) x = -((d : ℝ) * coordPartial 0 σ x) := by
  have hσd : ∀ y : Fin (d + 1) → ℝ, DifferentiableAt ℝ σ y := fun y =>
    differentiableAt_of_contDiff_infty hσ y
  have hscale : ∀ y : Fin (d + 1) → ℝ, DifferentiableAt ℝ (fun z => (d : ℝ) * σ z) y :=
    fun y => (hσd y).const_mul _
  have hexp : DifferentiableAt ℝ (fun z => Real.exp ((d : ℝ) * σ z)) x :=
    (hscale x).exp
  have hsum : ∑ i, coordPartial i ((inhomChart hσ).flux (fun y => y 0) i) x
      = coordPartial (0 : Fin (d + 1)) ((inhomChart hσ).flux (fun y => y 0) 0) x := by
    refine Finset.sum_eq_single (0 : Fin (d + 1)) ?_ ?_
    · intro i _ hi
      rw [flux_coord_zero_ne hσ hi]
      exact coordPartial_const i 0 x
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h
  have hcp : coordPartial (0 : Fin (d + 1)) ((inhomChart hσ).flux (fun y => y 0) 0) x
      = (-1 : ℝ) * (Real.exp ((d : ℝ) * σ x) * ((d : ℝ) * coordPartial 0 σ x)) := by
    rw [flux_coord_zero_eq hσ, coordPartial_const_mul hexp (-1 : ℝ) 0,
      coordPartial_exp (hscale x) 0, coordPartial_const_mul (hσd x) (d : ℝ) 0]
  have hne : Real.exp ((d : ℝ) * σ x) ≠ 0 := Real.exp_ne_zero _
  rw [SmoothMetricChart.dalembert, hsum, hcp, inhomChart_density]
  field_simp

/-! ## Probes and determination -/

/-- **Clock probes in a chart inhomogeneous along its leaves.** The only condition on the conformal
factor is that its drift along the zeroth direction be a function of the zeroth coordinate. -/
theorem exists_inhom_localProbe {d : ℕ} {σ : (Fin (d + 1) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 1 A) (hdrift : ∀ x, coordPartial 0 σ x = A (x 0))
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (a : ℝ) :
    ∃ (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin (d + 1) → ℝ, x 0 = a → u x = 1) ∧
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (a - ε) (a + ε) →
        SolvesPotentialWaveAt (inhomChart hσ).dalembert (fun y => V (y 0)) u x) := by
  refine exists_foliation_localProbe contDiff_coord_zero (P := fun _ => (-1 : ℝ))
    (R := fun t => -((d : ℝ) * A t)) (fun x => gradPair_coord_zero hσ x) ?_ contDiff_const
    ((contDiff_const.mul hA).neg) (fun _ => by norm_num) hV a
  intro x
  rw [dalembert_coord_zero hσ x, hdrift x]

/-- **Determination in a chart inhomogeneous along its leaves, unconditionally.** -/
theorem inhom_potential_eq {d : ℕ} {σ : (Fin (d + 1) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 1 A) (hdrift : ∀ x, coordPartial 0 σ x = A (x 0))
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) {other : (Fin (d + 1) → ℝ) → ℝ}
    (hother : ∀ (b : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (inhomChart hσ).dalembert (fun y => V (y 0)) u x) →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (inhomChart hσ).dalembert other u x)) :
    other = fun y => V (y 0) := by
  refine chartPotential_eq_of_foliation contDiff_coord_zero (P := fun _ => (-1 : ℝ))
    (R := fun t => -((d : ℝ) * A t)) (fun x => gradPair_coord_zero hσ x) ?_ contDiff_const
    ((contDiff_const.mul hA).neg) (fun _ => by norm_num) hV hother
  intro x
  rw [dalembert_coord_zero hσ x, hdrift x]

/-! ## The class is genuinely beyond the slicing theorems -/

/-- **The chart is not constant along its leaves.** Where the conformal factor differs at two
points of one leaf, so does the metric — so no slicing theorem applies to it. -/
theorem inhomChart_not_leafConstant {d : ℕ} {σ : (Fin (d + 1) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    {x y : Fin (d + 1) → ℝ} (hσxy : σ x ≠ σ y) (i : Fin (d + 1)) (hi : i ≠ 0) :
    (inhomChart hσ).inverseMetric x i i ≠ (inhomChart hσ).inverseMetric y i i := by
  rw [inhomChart_inverseMetric, inhomChart_inverseMetric]
  simp only [Matrix.diagonal_apply_eq, inhomDiag, if_neg hi]
  rw [Ne, Real.exp_eq_exp]
  intro h
  exact hσxy (by linarith)

/-! ## An explicit inhomogeneous member of the class -/

/-- Expansion history plus a transverse profile: `σ(x) = α(x⁰) + x¹`. -/
noncomputable def tiltedFactor {d : ℕ} (α : ℝ → ℝ) : (Fin (d + 1 + 1) → ℝ) → ℝ :=
  fun x => α (x 0) + x 1

theorem contDiff_tiltedFactor {d : ℕ} {α : ℝ → ℝ} (hα : ContDiff ℝ ∞ α) :
    ContDiff ℝ ∞ (tiltedFactor (d := d) α) :=
  (hα.comp (contDiff_apply ℝ ℝ 0)).add (contDiff_apply ℝ ℝ 1)

theorem coordPartial_zero_tiltedFactor {d : ℕ} {α : ℝ → ℝ} (hα : ContDiff ℝ ∞ α)
    (x : Fin (d + 1 + 1) → ℝ) :
    coordPartial 0 (tiltedFactor (d := d) α) x = deriv α (x 0) := by
  have hαd : DifferentiableAt ℝ α (x 0) := hα.differentiable (by simp) (x 0)
  have hproj0 : DifferentiableAt ℝ (fun y : Fin (d + 1 + 1) → ℝ => y 0) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1 + 1) => ℝ) 0).differentiableAt
  have hf : DifferentiableAt ℝ (fun y : Fin (d + 1 + 1) → ℝ => α (y 0)) x :=
    hαd.comp x hproj0
  have hg : DifferentiableAt ℝ (fun y : Fin (d + 1 + 1) → ℝ => y 1) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1 + 1) => ℝ) 1).differentiableAt
  have h1 : coordPartial (0 : Fin (d + 1 + 1))
      (fun y : Fin (d + 1 + 1) → ℝ => y 1) x = 0 := by
    rw [coordPartial_coord]
    simp
  have h0 : coordPartial (0 : Fin (d + 1 + 1))
      (fun y : Fin (d + 1 + 1) → ℝ => α (y 0)) x = deriv α (x 0) :=
    coordPartial_timeLift_zero hαd.hasDerivAt
  show coordPartial 0 (fun y : Fin (d + 1 + 1) → ℝ => α (y 0) + y 1) x = deriv α (x 0)
  rw [coordPartial_add hf hg 0, h0, h1, add_zero]

/-- **The tilted factor is genuinely non-constant along a leaf.** -/
theorem exists_leaf_inhomogeneity {d : ℕ} (α : ℝ → ℝ) :
    ∃ x y : Fin (d + 1 + 1) → ℝ,
      x 0 = y 0 ∧ tiltedFactor (d := d) α x ≠ tiltedFactor (d := d) α y := by
  refine ⟨0, Pi.single 1 1, ?_, ?_⟩
  · simp
  · simp only [tiltedFactor, Pi.single_apply]
    norm_num

/-- **Clock probes in the tilted chart.** -/
theorem exists_tilted_localProbe {d : ℕ} {α : ℝ → ℝ} (hα : ContDiff ℝ ∞ α)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (a : ℝ) :
    ∃ (u : (Fin (d + 1 + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin (d + 1 + 1) → ℝ, x 0 = a → u x = 1) ∧
      (∀ x : Fin (d + 1 + 1) → ℝ, x 0 ∈ Ioo (a - ε) (a + ε) →
        SolvesPotentialWaveAt (inhomChart (contDiff_tiltedFactor (d := d) hα)).dalembert
          (fun y => V (y 0)) u x) :=
  exists_inhom_localProbe (contDiff_tiltedFactor hα)
    (((contDiff_infty_iff_deriv.mp hα).2).of_le (by simp))
    (coordPartial_zero_tiltedFactor hα) hV a

/-- **Determination in the tilted chart, unconditionally.** -/
theorem tilted_potential_eq {d : ℕ} {α : ℝ → ℝ} (hα : ContDiff ℝ ∞ α)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) {other : (Fin (d + 1 + 1) → ℝ) → ℝ}
    (hother : ∀ (b : ℝ) (u : (Fin (d + 1 + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1 + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (inhomChart (contDiff_tiltedFactor (d := d) hα)).dalembert
          (fun y => V (y 0)) u x) →
      (∀ x : Fin (d + 1 + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (inhomChart (contDiff_tiltedFactor (d := d) hα)).dalembert
          other u x)) :
    other = fun y => V (y 0) :=
  inhom_potential_eq (contDiff_tiltedFactor hα)
    (((contDiff_infty_iff_deriv.mp hα).2).of_le (by simp))
    (coordPartial_zero_tiltedFactor hα) hV hother

/-- **The tilted chart lies outside every slicing theorem.** Two points of one leaf carry different
metrics, so its data are not constant on the leaves — yet its potential is determined. -/
theorem tiltedChart_not_leafConstant {d : ℕ} {α : ℝ → ℝ} (hα : ContDiff ℝ ∞ α) :
    ∃ x y : Fin (d + 1 + 1) → ℝ, x 0 = y 0 ∧
      (inhomChart (contDiff_tiltedFactor (d := d) hα)).inverseMetric x 1 1
        ≠ (inhomChart (contDiff_tiltedFactor (d := d) hα)).inverseMetric y 1 1 := by
  obtain ⟨x, y, h0, hne⟩ := exists_leaf_inhomogeneity (d := d) α
  exact ⟨x, y, h0, inhomChart_not_leafConstant _ hne 1 (by simp)⟩

end GaloisForLFunctions.HTGeometry
