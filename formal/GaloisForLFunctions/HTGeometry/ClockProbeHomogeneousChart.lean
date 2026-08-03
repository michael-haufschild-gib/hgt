import GaloisForLFunctions.HTGeometry.ClockProbeSturmLiouville
import GaloisForLFunctions.HTGeometry.ConformalMetricDalembertian

/-!
# Clock probes on a homogeneous chart

A chart is *homogeneous* when its inverse metric and volume density depend only on the zeroth
coordinate. On such a chart a field that likewise depends only on that coordinate has a
d'Alembertian given by a one-dimensional divergence-form expression: with `A t = ρ(t) G⁰⁰(t)`,

`□ (w ∘ x⁰) = ρ⁻¹ (A w')'`.

Combined with local existence for `(A w')' + B w = 0` this produces genuine clock probes in every
dimension, and hence determination of a homogeneous potential from clock data — with no
nondegeneracy hypothesis. The one-dimensional model is thereby lifted to the homogeneous sector of
a chart of arbitrary dimension.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- Lift of a function of one variable to the chart, constant on the level sets of the zeroth
coordinate. -/
def timeLift {d : ℕ} (w : ℝ → ℝ) : (Fin (d + 1) → ℝ) → ℝ := fun x => w (x 0)

/-- **Transverse constancy.** A lifted field has vanishing partial derivative in every direction
other than the zeroth, with no differentiability hypothesis. -/
theorem coordPartial_timeLift_of_ne {d : ℕ} (w : ℝ → ℝ) {i : Fin (d + 1)} (hi : i ≠ 0)
    (x : Fin (d + 1) → ℝ) : coordPartial i (timeLift w) x = 0 := by
  have hi0 : (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ) 0 = 0 := by
    rw [Pi.single_apply]
    simp [Ne.symm hi]
  by_cases hd : DifferentiableAt ℝ (timeLift (d := d) w) x
  · have hline : HasDerivAt (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ))
        (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ))
          ((1 : ℝ) • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ)) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const _
      simpa using h1.const_add x
    have hbase : (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ)) 0 = x := by
      simp
    have hL : HasFDerivAt (timeLift (d := d) w) (fderiv ℝ (timeLift (d := d) w) x)
        ((fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ)) 0) := by
      rw [hbase]
      exact hd.hasFDerivAt
    have hcomp := hL.comp_hasDerivAt 0 hline
    have hconst : (timeLift (d := d) w ∘
        fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ)) = fun _ : ℝ => w (x 0) := by
      funext t
      simp only [Function.comp_apply, timeLift, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hi0]
      norm_num
    rw [hconst] at hcomp
    have hzero : HasDerivAt (fun _ : ℝ => w (x 0)) 0 (0 : ℝ) := hasDerivAt_const _ _
    have hval := hcomp.unique hzero
    rw [coordPartial, hval]
  · rw [coordPartial, fderiv_zero_of_not_differentiableAt hd]
    rfl

/-- **The zeroth partial derivative of a lifted field is the ordinary derivative.** -/
theorem coordPartial_timeLift_zero {d : ℕ} {w : ℝ → ℝ} {c : ℝ} {x : Fin (d + 1) → ℝ}
    (hw : HasDerivAt w c (x 0)) : coordPartial (0 : Fin (d + 1)) (timeLift w) x = c := by
  have hproj : HasFDerivAt (fun y : Fin (d + 1) → ℝ => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0).hasFDerivAt
  have hcomp := hw.comp_hasFDerivAt x hproj
  have hEq : (w ∘ fun y : Fin (d + 1) → ℝ => y 0) = timeLift (d := d) w := rfl
  rw [hEq] at hcomp
  rw [coordPartial, hcomp.fderiv]
  simp

/-- **Flux of a lifted field.** Only the zeroth column of the inverse metric contributes. -/
theorem flux_timeLift {d : ℕ} (M : SmoothMetricChart (d + 1)) {w : ℝ → ℝ} {c : ℝ}
    {x : Fin (d + 1) → ℝ} (hw : HasDerivAt w c (x 0)) (i : Fin (d + 1)) :
    M.flux (timeLift w) i x = M.density x * (M.inverseMetric x i 0 * c) := by
  have hsum : ∑ j, M.inverseMetric x i j * coordPartial j (timeLift (d := d) w) x
      = M.inverseMetric x i 0 * c := by
    rw [Finset.sum_eq_single (0 : Fin (d + 1))]
    · rw [coordPartial_timeLift_zero hw]
    · intro j _ hj
      rw [coordPartial_timeLift_of_ne w hj x, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h
  rw [SmoothMetricChart.flux, hsum]

/-- **Reduction of the chart d'Alembertian on a homogeneous chart.** A field depending only on the
zeroth coordinate has d'Alembertian `ρ⁻¹ (ρ G⁰⁰ w')'`. -/
theorem dalembert_timeLift {d : ℕ} {M : SmoothMetricChart (d + 1)}
    {coeff : ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {dens : ℝ → ℝ}
    (hG : ∀ x : Fin (d + 1) → ℝ, M.inverseMetric x = coeff (x 0))
    (hρ : ∀ x : Fin (d + 1) → ℝ, M.density x = dens (x 0))
    {w dw q : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hw : ∀ t ∈ S, HasDerivAt w (dw t) t)
    (hq : ∀ t ∈ S, HasDerivAt (fun s => dens s * (coeff s 0 0 * dw s)) (q t) t)
    {x : Fin (d + 1) → ℝ} (hx : x 0 ∈ S) :
    M.dalembert (timeLift w) x = (dens (x 0))⁻¹ * q (x 0) := by
  have hslab : IsOpen ((fun y : Fin (d + 1) → ℝ => y 0) ⁻¹' S) :=
    hS.preimage (continuous_apply 0)
  have hnhds : (fun y : Fin (d + 1) → ℝ => y 0) ⁻¹' S ∈ nhds x := hslab.mem_nhds hx
  have hev : ∀ i : Fin (d + 1),
      M.flux (timeLift w) i =ᶠ[nhds x]
        timeLift (fun t => dens t * (coeff t i 0 * dw t)) := by
    intro i
    refine Filter.eventuallyEq_of_mem hnhds ?_
    intro y hy
    have hyS : y 0 ∈ S := hy
    rw [flux_timeLift M (hw (y 0) hyS) i, hG y, hρ y]
    rfl
  have hcp : ∀ i : Fin (d + 1), coordPartial i (M.flux (timeLift w) i) x
      = coordPartial i (timeLift (fun t => dens t * (coeff t i 0 * dw t))) x := by
    intro i
    rw [coordPartial, coordPartial, (hev i).fderiv_eq]
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin (d + 1))), i ≠ 0 →
      coordPartial i (M.flux (timeLift w) i) x = 0 := by
    intro i _ hi
    rw [hcp i, coordPartial_timeLift_of_ne _ hi x]
  have hone : coordPartial (0 : Fin (d + 1)) (M.flux (timeLift w) 0) x = q (x 0) := by
    rw [hcp 0]
    exact coordPartial_timeLift_zero (hq (x 0) hx)
  have hsum : ∑ i, coordPartial i (M.flux (timeLift w) i) x = q (x 0) := by
    rw [Finset.sum_eq_single (0 : Fin (d + 1)) hzero
      (fun h => absurd (Finset.mem_univ (0 : Fin (d + 1))) h)]
    exact hone
  rw [SmoothMetricChart.dalembert, hsum, hρ x]

/-- **Clock probes exist on every homogeneous chart.** For a homogeneous potential the equation
`□u + Vu = 0` has, about every time, a solution constant on the level sets of the zeroth coordinate
and normalized to one on the initial slice. -/
theorem exists_homogeneous_localProbe {d : ℕ} {M : SmoothMetricChart (d + 1)}
    {coeff : ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {dens : ℝ → ℝ}
    (hG : ∀ x : Fin (d + 1) → ℝ, M.inverseMetric x = coeff (x 0))
    (hρ : ∀ x : Fin (d + 1) → ℝ, M.density x = dens (x 0))
    {V : ℝ → ℝ}
    (hA : ContDiff ℝ 1 fun t => dens t * coeff t 0 0)
    (hA0 : ∀ t, dens t * coeff t 0 0 ≠ 0)
    (hB : ContDiff ℝ 1 fun t => dens t * V t)
    (a : ℝ) :
    ∃ (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin (d + 1) → ℝ, x 0 = a → u x = 1) ∧
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (a - ε) (a + ε) →
        SolvesPotentialWaveAt M.dalembert (timeLift V) u x) := by
  obtain ⟨w, dw, ε, hε, hwa, hd1, _hdw, hd2⟩ := exists_localSturmProbe hA hB hA0 a
  have hassoc : (fun s => (dens s * coeff s 0 0) * dw s)
      = fun s => dens s * (coeff s 0 0 * dw s) := by
    funext s
    ring
  rw [hassoc] at hd2
  refine ⟨timeLift w, ε, hε, ?_, ?_⟩
  · intro x hx
    rw [timeLift, hx, hwa]
  · intro x hx
    have hdens : dens (x 0) ≠ 0 := by
      have h := M.density_pos x
      rw [hρ x] at h
      exact ne_of_gt h
    have hred := dalembert_timeLift hG hρ isOpen_Ioo hd1 hd2 hx
    rw [SolvesPotentialWaveAt, hred, timeLift, timeLift]
    field_simp
    ring

/-- **Determination of a homogeneous potential from clock data, unconditionally.** A competing
potential solving the local probes of `V` on their slabs equals `V` everywhere on the chart. -/
theorem chartPotential_eq_of_homogeneous {d : ℕ} {M : SmoothMetricChart (d + 1)}
    {coeff : ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {dens : ℝ → ℝ}
    (hG : ∀ x : Fin (d + 1) → ℝ, M.inverseMetric x = coeff (x 0))
    (hρ : ∀ x : Fin (d + 1) → ℝ, M.density x = dens (x 0))
    {V : ℝ → ℝ} {other : (Fin (d + 1) → ℝ) → ℝ}
    (hA : ContDiff ℝ 1 fun t => dens t * coeff t 0 0)
    (hA0 : ∀ t, dens t * coeff t 0 0 ≠ 0)
    (hB : ContDiff ℝ 1 fun t => dens t * V t)
    (hother : ∀ (b : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert (timeLift V) u x) →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert other u x)) :
    other = timeLift V := by
  funext x
  obtain ⟨u, ε, hε, hu1, hsolve⟩ := exists_homogeneous_localProbe hG hρ hA hA0 hB (x 0)
  have hx : x 0 ∈ Ioo (x 0 - ε) (x 0 + ε) := by constructor <;> linarith
  refine potential_eq_of_solvesPotentialWaveAt
    (hother (x 0) u ε hε hsolve x hx) (hsolve x hx) ?_
  rw [hu1 x rfl]
  exact one_ne_zero

end GaloisForLFunctions.HTGeometry
