import GaloisForLFunctions.HTGeometry.ClockProbeHomogeneousChart

/-!
# Clock probes along an arbitrary non-null slicing

The homogeneous reduction singles out the zeroth coordinate. Nothing in the argument does: what
matters is that the chart data are constant on the level sets of a fixed linear phase `⟪n, x⟫` and
that the covector `n` is non-null for the inverse metric.

For such a slicing a field constant on the level sets satisfies

`□ (w ∘ ⟪n, ·⟫) = ρ⁻¹ (ρ G(n,n) w')'`,

so local existence for the divergence-form equation again produces clock probes and determines the
potential — in every dimension, with no nondegeneracy hypothesis.

Taking `n` to be the zeroth basis covector recovers the homogeneous case; taking `n` spatial covers
the static configurations, where the geometry varies from place to place and the clock potential is
read off along the varying direction.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {d : ℕ}

/-- Linear phase of a covector. -/
noncomputable def covectorPhase (n x : Fin (d + 1) → ℝ) : ℝ := ∑ i, n i * x i

/-- The linear phase as a continuous linear functional. -/
noncomputable def covectorCLM (n : Fin (d + 1) → ℝ) : (Fin (d + 1) → ℝ) →L[ℝ] ℝ :=
  ∑ i, (n i) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) i)

@[simp] theorem covectorCLM_apply (n x : Fin (d + 1) → ℝ) :
    covectorCLM n x = covectorPhase n x := by
  simp [covectorCLM, covectorPhase]

theorem covectorCLM_coe (n : Fin (d + 1) → ℝ) :
    (⇑(covectorCLM n)) = covectorPhase (d := d) n :=
  funext (covectorCLM_apply n)

theorem continuous_covectorPhase (n : Fin (d + 1) → ℝ) :
    Continuous (covectorPhase (d := d) n) := by
  rw [← covectorCLM_coe n]
  exact (covectorCLM n).continuous

theorem covectorPhase_single (n : Fin (d + 1) → ℝ) (i : Fin (d + 1)) :
    covectorPhase n (Pi.single i 1) = n i := by
  rw [covectorPhase, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_apply, if_neg hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem covectorPhase_basis (k : Fin (d + 1)) (x : Fin (d + 1) → ℝ) :
    covectorPhase (Pi.single k 1) x = x k := by
  rw [covectorPhase, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    rw [Pi.single_apply, if_neg hj, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- Lift of a function of one variable along a covector: constant on the level sets of the linear
phase. -/
noncomputable def covectorLift (n : Fin (d + 1) → ℝ) (w : ℝ → ℝ) :
    (Fin (d + 1) → ℝ) → ℝ := fun x => w (covectorPhase n x)

/-- Slicing by the zeroth basis covector is the homogeneous slicing. -/
theorem covectorLift_single_zero (w : ℝ → ℝ) :
    covectorLift (Pi.single (0 : Fin (d + 1)) 1) w = timeLift w := by
  funext x
  rw [covectorLift, timeLift, covectorPhase, Finset.sum_eq_single (0 : Fin (d + 1))]
  · simp
  · intro j _ hj
    rw [Pi.single_apply, if_neg hj, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h

/-- **Partial derivatives of a lifted field.** Each direction contributes the corresponding
component of the covector. -/
theorem coordPartial_covectorLift {n : Fin (d + 1) → ℝ} {w : ℝ → ℝ} {c : ℝ}
    {x : Fin (d + 1) → ℝ} (hw : HasDerivAt w c (covectorPhase n x)) (i : Fin (d + 1)) :
    coordPartial i (covectorLift n w) x = n i * c := by
  have hproj : HasFDerivAt (covectorPhase (d := d) n) (covectorCLM n) x := by
    rw [← covectorCLM_coe n]
    exact (covectorCLM n).hasFDerivAt
  have hcomp := hw.comp_hasFDerivAt x hproj
  have hEq : (w ∘ covectorPhase (d := d) n) = covectorLift n w := rfl
  rw [hEq] at hcomp
  rw [coordPartial, hcomp.fderiv]
  simp [covectorPhase_single, mul_comm]

/-- **Flux of a lifted field.** The inverse metric enters only through its pairing with the
covector. -/
theorem flux_covectorLift (M : SmoothMetricChart (d + 1)) {n : Fin (d + 1) → ℝ}
    {w : ℝ → ℝ} {c : ℝ} {x : Fin (d + 1) → ℝ}
    (hw : HasDerivAt w c (covectorPhase n x)) (i : Fin (d + 1)) :
    M.flux (covectorLift n w) i x
      = M.density x * ((∑ j, M.inverseMetric x i j * n j) * c) := by
  have hsum : ∑ j, M.inverseMetric x i j * coordPartial j (covectorLift n w) x
      = (∑ j, M.inverseMetric x i j * n j) * c := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coordPartial_covectorLift hw j]
    ring
  rw [SmoothMetricChart.flux, hsum]

/-- The norm of a covector for the inverse metric, `G(n,n)`. -/
noncomputable def covectorNorm (coeff : ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (n : Fin (d + 1) → ℝ) (t : ℝ) : ℝ := ∑ i, n i * ∑ j, coeff t i j * n j

/-- Contracting the flux family with the covector produces the divergence-form coefficient. -/
theorem sum_weighted_flux (dens dw : ℝ) (n : Fin (d + 1) → ℝ) (C : Fin (d + 1) → ℝ) :
    ∑ i, n i * (dens * (C i * dw)) = (dens * ∑ i, n i * C i) * dw := by
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- For a basis covector the metric norm is the corresponding diagonal entry. -/
theorem covectorNorm_basis (coeff : ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (k : Fin (d + 1)) (t : ℝ) :
    covectorNorm coeff (Pi.single k 1) t = coeff t k k := by
  rw [covectorNorm, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, one_mul, Finset.sum_eq_single k]
    · rw [Pi.single_eq_same, mul_one]
    · intro j _ hj
      rw [Pi.single_apply, if_neg hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  · intro i _ hi
    rw [Pi.single_apply, if_neg hi, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- **Reduction of the chart d'Alembertian along a slicing.** -/
theorem dalembert_covectorLift {M : SmoothMetricChart (d + 1)}
    {coeff : ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {dens : ℝ → ℝ}
    {n : Fin (d + 1) → ℝ}
    (hG : ∀ x : Fin (d + 1) → ℝ, M.inverseMetric x = coeff (covectorPhase n x))
    (hρ : ∀ x : Fin (d + 1) → ℝ, M.density x = dens (covectorPhase n x))
    {w dw : ℝ → ℝ} {F : Fin (d + 1) → ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hw : ∀ t ∈ S, HasDerivAt w (dw t) t)
    (hF : ∀ i : Fin (d + 1), ∀ t ∈ S,
      HasDerivAt (fun s => dens s * ((∑ j, coeff s i j * n j) * dw s)) (F i t) t)
    {x : Fin (d + 1) → ℝ} (hx : covectorPhase n x ∈ S) :
    M.dalembert (covectorLift n w) x
      = (dens (covectorPhase n x))⁻¹ * ∑ i, n i * F i (covectorPhase n x) := by
  have hnhds : covectorPhase (d := d) n ⁻¹' S ∈ nhds x :=
    (hS.preimage (continuous_covectorPhase n)).mem_nhds hx
  have hev : ∀ i : Fin (d + 1), M.flux (covectorLift n w) i =ᶠ[nhds x]
      covectorLift n (fun t => dens t * ((∑ j, coeff t i j * n j) * dw t)) := by
    intro i
    refine Filter.eventuallyEq_of_mem hnhds ?_
    intro y hy
    have hyS : covectorPhase n y ∈ S := hy
    rw [flux_covectorLift M (hw _ hyS) i, hG y, hρ y]
    rfl
  have hcpEq : ∀ i : Fin (d + 1), coordPartial i (M.flux (covectorLift n w) i) x
      = coordPartial i
          (covectorLift n (fun t => dens t * ((∑ j, coeff t i j * n j) * dw t))) x := by
    intro i
    rw [coordPartial, coordPartial, (hev i).fderiv_eq]
  have hcp : ∀ i : Fin (d + 1), coordPartial i (M.flux (covectorLift n w) i) x
      = n i * F i (covectorPhase n x) := by
    intro i
    rw [hcpEq i]
    exact coordPartial_covectorLift (hF i _ hx) i
  rw [SmoothMetricChart.dalembert, hρ x]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hcp i

/-- **Clock probes along a non-null slicing.** For chart data constant on the level sets of the
phase, with the covector non-null, the equation `□u + Vu = 0` has a solution about every value of
the phase, constant on the level sets and normalized to one on the initial leaf. -/
theorem exists_covector_localProbe {M : SmoothMetricChart (d + 1)}
    {coeff : ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {dens : ℝ → ℝ} {n : Fin (d + 1) → ℝ}
    (hG : ∀ x : Fin (d + 1) → ℝ, M.inverseMetric x = coeff (covectorPhase n x))
    (hρ : ∀ x : Fin (d + 1) → ℝ, M.density x = dens (covectorPhase n x))
    (hdens : ContDiff ℝ 1 dens)
    (hcoeff : ∀ i j, ContDiff ℝ 1 fun t => coeff t i j)
    (hQ : ∀ t, dens t * covectorNorm coeff n t ≠ 0)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (a : ℝ) :
    ∃ (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin (d + 1) → ℝ, covectorPhase n x = a → u x = 1) ∧
      (∀ x : Fin (d + 1) → ℝ, covectorPhase n x ∈ Ioo (a - ε) (a + ε) →
        SolvesPotentialWaveAt M.dalembert (covectorLift n V) u x) := by
  have hCi : ∀ i : Fin (d + 1), ContDiff ℝ 1 fun t => ∑ j, coeff t i j * n j := fun i =>
    ContDiff.sum fun j _ => (hcoeff i j).mul contDiff_const
  have hA : ContDiff ℝ 1 fun t => dens t * covectorNorm coeff n t := by
    refine hdens.mul ?_
    exact ContDiff.sum fun i _ => contDiff_const.mul (hCi i)
  have hB : ContDiff ℝ 1 fun t => dens t * V t := hdens.mul hV
  obtain ⟨w, dw, ε, hε, hwa, hd1, hdw, hd2⟩ := exists_localSturmProbe hA hB hQ a
  obtain ⟨F, hF⟩ : ∃ F : Fin (d + 1) → ℝ → ℝ, ∀ i : Fin (d + 1), ∀ t ∈ Ioo (a - ε) (a + ε),
      HasDerivAt (fun s => dens s * ((∑ j, coeff s i j * n j) * dw s)) (F i t) t := by
    refine ⟨fun i => deriv fun s => dens s * ((∑ j, coeff s i j * n j) * dw s), ?_⟩
    intro i t ht
    refine DifferentiableAt.hasDerivAt ?_
    exact (hdens.differentiable (by simp) t).mul
      (((hCi i).differentiable (by simp) t).mul (hdw t ht))
  have hkey : ∀ t ∈ Ioo (a - ε) (a + ε),
      ∑ i, n i * F i t = -(dens t * V t) * w t := by
    intro t ht
    have hpieces : ∀ i ∈ (Finset.univ : Finset (Fin (d + 1))),
        HasDerivAt (fun s => n i * (dens s * ((∑ j, coeff s i j * n j) * dw s)))
          (n i * F i t) t := fun i _ => (hF i t ht).const_mul (n i)
    have hsum := HasDerivAt.sum hpieces
    have hfun : (∑ i : Fin (d + 1),
        fun s => n i * (dens s * ((∑ j, coeff s i j * n j) * dw s)))
        = fun s => (dens s * covectorNorm coeff n s) * dw s := by
      funext s
      rw [Finset.sum_apply]
      exact sum_weighted_flux (dens s) (dw s) n fun i => ∑ j, coeff s i j * n j
    rw [hfun] at hsum
    exact hsum.unique (hd2 t ht)
  refine ⟨covectorLift n w, ε, hε, ?_, ?_⟩
  · intro x hx
    rw [covectorLift, hx, hwa]
  · intro x hx
    have hdens0 : dens (covectorPhase n x) ≠ 0 := by
      have h := M.density_pos x
      rw [hρ x] at h
      exact ne_of_gt h
    have hred := dalembert_covectorLift hG hρ isOpen_Ioo hd1 hF hx
    rw [SolvesPotentialWaveAt, hred, covectorLift, covectorLift,
      hkey (covectorPhase n x) hx]
    field_simp
    ring

/-- **Determination of the potential along a non-null slicing, unconditionally.** -/
theorem chartPotential_eq_of_covector {M : SmoothMetricChart (d + 1)}
    {coeff : ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {dens : ℝ → ℝ} {n : Fin (d + 1) → ℝ}
    (hG : ∀ x : Fin (d + 1) → ℝ, M.inverseMetric x = coeff (covectorPhase n x))
    (hρ : ∀ x : Fin (d + 1) → ℝ, M.density x = dens (covectorPhase n x))
    (hdens : ContDiff ℝ 1 dens)
    (hcoeff : ∀ i j, ContDiff ℝ 1 fun t => coeff t i j)
    (hQ : ∀ t, dens t * covectorNorm coeff n t ≠ 0)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) {other : (Fin (d + 1) → ℝ) → ℝ}
    (hother : ∀ (b : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ, covectorPhase n x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert (covectorLift n V) u x) →
      (∀ x : Fin (d + 1) → ℝ, covectorPhase n x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert other u x)) :
    other = covectorLift n V := by
  funext x
  obtain ⟨u, ε, hε, hu1, hsolve⟩ :=
    exists_covector_localProbe hG hρ hdens hcoeff hQ hV (covectorPhase n x)
  have hx : covectorPhase n x ∈ Ioo (covectorPhase n x - ε) (covectorPhase n x + ε) := by
    constructor <;> linarith
  refine potential_eq_of_solvesPotentialWaveAt
    (hother (covectorPhase n x) u ε hε hsolve x hx) (hsolve x hx) ?_
  rw [hu1 x rfl]
  exact one_ne_zero

end GaloisForLFunctions.HTGeometry
