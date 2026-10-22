import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonProbeExamples
import GaloisForLFunctions.HTGeometry.ClockLocalTwoSpecies

/-!
# A probe at every event

The construction normalises the field at time zero, so as it stands it produces a probe near one time
slice. Every other event is reached by shifting the potential in time and composing the field with
the inverse shift: coordinate derivatives are translation invariant, so the shifted field solves the
equation for the unshifted potential.

The outcome is the corpus's `OpenProbes` interface — a probe on an open neighbourhood of *every*
event, nonvanishing throughout it — which is what the two-species scale law consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform SchwartzMap ContDiff

/-! ## Translation invariance of the coordinate calculus -/

section Translation

variable {d : ℕ}

theorem hasFDerivAt_comp_add_const {f : (Fin d → ℝ) → ℝ} {f' : (Fin d → ℝ) →L[ℝ] ℝ}
    {y c : Fin d → ℝ} (h : HasFDerivAt f f' (y + c)) :
    HasFDerivAt (fun z : Fin d → ℝ => f (z + c)) f' y := by
  have hshift : HasFDerivAt (fun z : Fin d → ℝ => z + c)
      (ContinuousLinearMap.id ℝ (Fin d → ℝ)) y := (hasFDerivAt_id y).add_const c
  have hcomp := h.comp y hshift
  rw [ContinuousLinearMap.comp_id] at hcomp
  exact hcomp

theorem coordPartial_comp_add_const {f : (Fin d → ℝ) → ℝ} {y c : Fin d → ℝ}
    (hdiff : DifferentiableAt ℝ f (y + c)) (j : Fin d) :
    coordPartial j (fun z : Fin d → ℝ => f (z + c)) y = coordPartial j f (y + c) := by
  rw [coordPartial, coordPartial, (hasFDerivAt_comp_add_const hdiff.hasFDerivAt).fderiv]

theorem coordPartial_comp_add_const_fun {f : (Fin d → ℝ) → ℝ} {c : Fin d → ℝ}
    (hdiff : ∀ z : Fin d → ℝ, DifferentiableAt ℝ f z) (j : Fin d) :
    coordPartial j (fun z : Fin d → ℝ => f (z + c))
      = fun y : Fin d → ℝ => coordPartial j f (y + c) := by
  funext y
  exact coordPartial_comp_add_const (hdiff (y + c)) j

theorem coordPartial_sq_comp_add_const {f : (Fin d → ℝ) → ℝ} {c : Fin d → ℝ}
    (hdiff : ∀ z : Fin d → ℝ, DifferentiableAt ℝ f z)
    (hdiff2 : ∀ (j : Fin d) (z : Fin d → ℝ), DifferentiableAt ℝ (coordPartial j f) z)
    (j : Fin d) (y : Fin d → ℝ) :
    coordPartial j (coordPartial j (fun z : Fin d → ℝ => f (z + c))) y
      = coordPartial j (coordPartial j f) (y + c) := by
  rw [coordPartial_comp_add_const_fun hdiff j]
  exact coordPartial_comp_add_const (hdiff2 j (y + c)) j

end Translation

/-! ## The shifted family -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-- The potential, shifted in time. -/
noncomputable def WienerFamily.timeShift (A : WienerFamily E N) (t₀ : ℝ) : WienerFamily E N where
  density := fun t => A.density (t + t₀)
  bound := A.bound
  norm_le := fun t => A.norm_le (t + t₀)
  lip := A.lip
  lip_nonneg := A.lip_nonneg
  lip_le := by
    intro t t'
    have h := A.lip_le (t + t₀) (t' + t₀)
    have habs : |t + t₀ - (t' + t₀)| = |t - t'| := by
      congr 1
      ring
    rw [habs] at h
    exact h

theorem WienerFamily.timeShift_density (A : WienerFamily E N) (t₀ t : ℝ) :
    (A.timeShift t₀).density t = A.density (t + t₀) := rfl

theorem isRealFamily_timeShift {A : WienerFamily E N} (h : IsRealFamily A) (t₀ : ℝ) :
    IsRealFamily (A.timeShift t₀) := fun t => h (t + t₀)

theorem differentiableAt_comp_add_const {d : ℕ} {f : (Fin d → ℝ) → ℝ} {c : Fin d → ℝ}
    (h : ∀ z : Fin d → ℝ, DifferentiableAt ℝ f z) (y : Fin d → ℝ) :
    DifferentiableAt ℝ (fun z : Fin d → ℝ => f (z + c)) y :=
  (hasFDerivAt_comp_add_const (h (y + c)).hasFDerivAt).differentiableAt

/-! ## The probe at an arbitrary event -/

section Anywhere

variable {d N : ℕ} (A : WienerFamily (EuclideanSpace ℝ (Fin d)) N)

/-- The chart vector of a time shift. -/
noncomputable def kgTimeShiftVec (d : ℕ) (t₀ : ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons (-t₀) (fun _ : Fin d => (0 : ℝ))

theorem add_kgTimeShiftVec_zero (y : Fin (d + 1) → ℝ) (t₀ : ℝ) :
    (y + kgTimeShiftVec d t₀) 0 = y 0 - t₀ := by
  show y 0 + kgTimeShiftVec d t₀ 0 = y 0 - t₀
  rw [kgTimeShiftVec, Fin.cons_zero]
  ring

theorem kgSpatial_add_kgTimeShiftVec (y : Fin (d + 1) → ℝ) (t₀ : ℝ) :
    kgSpatial d (y + kgTimeShiftVec d t₀) = kgSpatial d y := by
  have hcoord : (fun i : Fin d => (y + kgTimeShiftVec d t₀) i.succ)
      = fun i : Fin d => y i.succ := by
    funext i
    show y i.succ + kgTimeShiftVec d t₀ i.succ = y i.succ
    rw [kgTimeShiftVec, Fin.cons_succ]
    ring
  rw [kgSpatial, kgSpatial, hcoord]

theorem kgChartPotential_timeShift (t₀ : ℝ) (y : Fin (d + 1) → ℝ) :
    kgChartPotential (A.timeShift t₀) (y + kgTimeShiftVec d t₀) = kgChartPotential A y := by
  have harg : y 0 - t₀ + t₀ = y 0 := by ring
  rw [kgChartPotential, kgChartPotential, add_kgTimeShiftVec_zero,
    kgSpatial_add_kgTimeShiftVec, WienerFamily.timeShift_density, harg]

/-- **The wave operator commutes with translations of the chart.** -/
theorem kgWaveOp_comp_add_const (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (c : Fin (d + 1) → ℝ) (y : Fin (d + 1) → ℝ) :
    kgWaveOp d (fun z : Fin (d + 1) → ℝ => kgChartField A G₀ (z + c)) y
      = kgWaveOp d (kgChartField A G₀) (y + c) := by
  have hdiff1 : ∀ z : Fin (d + 1) → ℝ, DifferentiableAt ℝ (kgChartField A G₀) z := fun z =>
    (hasFDerivAt_kgChartField A G₀ hN z).differentiableAt
  have hdiff2 : ∀ (j : Fin (d + 1)) (z : Fin (d + 1) → ℝ),
      DifferentiableAt ℝ (coordPartial j (kgChartField A G₀)) z := fun j z =>
    differentiableAt_coordPartial_kgChartField A G₀ hN j z
  have hshiftDiff : ∀ j : Fin (d + 1), ∀ z : Fin (d + 1) → ℝ,
      DifferentiableAt ℝ (coordPartial j (fun w : Fin (d + 1) → ℝ => kgChartField A G₀ (w + c)))
        z := by
    intro j z
    rw [coordPartial_comp_add_const_fun hdiff1 j]
    exact differentiableAt_comp_add_const (hdiff2 j) z
  rw [kgWaveOp, ofSignature_dalembert_of_differentiableAt (kgEps d) (kgEps_ne_zero d)
      (fun j => hshiftDiff j y),
    ofSignature_dalembert_of_differentiableAt (kgEps d) (kgEps_ne_zero d)
      (fun j => hdiff2 j (y + c))]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact coordPartial_sq_comp_add_const hdiff1 hdiff2 j y

/-- **A probe at every event.** For a real admissible family the constructed field, shifted in time,
gives a clock probe on an open neighbourhood of *any* chart point, nonvanishing throughout it: the
corpus's `OpenProbes` interface. -/
theorem openProbes_kgChartPotential
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (hreal : IsRealFamily A) :
    OpenProbes (kgWaveOp d) (kgChartPotential A) := by
  intro y₀
  set t₀ : ℝ := y₀ 0 with ht₀
  set x₀ : EuclideanSpace ℝ (Fin d) := kgSpatial d y₀ with hx₀
  set c : Fin (d + 1) → ℝ := kgTimeShiftVec d t₀ with hc
  set B : WienerFamily (EuclideanSpace ℝ (Fin d)) N := A.timeShift t₀ with hB
  have hshift : Continuous fun z : Fin (d + 1) → ℝ => z + c := continuous_add_const c
  have h1 : (y₀ + c) 0 = 0 := by
    rw [hc, add_kgTimeShiftVec_zero, ht₀]
    ring
  have h2 : kgSpatial d (y₀ + c) = x₀ := by
    rw [hc, kgSpatial_add_kgTimeShiftVec, hx₀]
  have hmap : Filter.Tendsto (fun z : Fin (d + 1) → ℝ =>
      (((z + c) 0, kgSpatial d (z + c)) : ℝ × EuclideanSpace ℝ (Fin d))) (nhds y₀)
      (nhds (0, x₀)) := by
    have hcont : Continuous fun z : Fin (d + 1) → ℝ =>
        (((z + c) 0, kgSpatial d (z + c)) : ℝ × EuclideanSpace ℝ (Fin d)) :=
      ((continuous_apply 0).comp hshift).prodMk ((continuous_kgSpatial d).comp hshift)
    have h : Filter.Tendsto (fun z : Fin (d + 1) → ℝ =>
        (((z + c) 0, kgSpatial d (z + c)) : ℝ × EuclideanSpace ℝ (Fin d))) (nhds y₀)
        (nhds (((y₀ + c) 0, kgSpatial d (y₀ + c)) : ℝ × EuclideanSpace ℝ (Fin d))) :=
      hcont.continuousAt
    rw [h1, h2] at h
    exact h
  have hev : ∀ᶠ z in nhds y₀, kgChartField B (kgConjChar x₀) (z + c) ≠ 0 :=
    hmap.eventually (eventually_kgRealField_ne_zero B hN x₀)
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hev
  refine ⟨W, hWopen, hWmem, fun z : Fin (d + 1) → ℝ => kgChartField B (kgConjChar x₀) (z + c),
    fun z _ => ?_, fun z hz => hWsub hz⟩
  have hwave := kgWaveOp_kgChartField B (kgConjChar x₀) hN (isRealFamily_timeShift hreal t₀)
    (z + c)
  have htrans := kgWaveOp_comp_add_const B hN (kgConjChar x₀) c z
  show kgWaveOp d (fun w : Fin (d + 1) → ℝ => kgChartField B (kgConjChar x₀) (w + c)) z
    + kgChartPotential A z * kgChartField B (kgConjChar x₀) (z + c) = 0
  rw [htrans, ← kgChartPotential_timeShift A t₀ z]
  exact hwave

/-! ## Localisation and determination -/

/-- **Probes are a local matter.** A potential that agrees near every event with the potential of
some admissible family has probes on open regions. -/
theorem openProbes_of_locally_kgChartPotential
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {P : (Fin (d + 1) → ℝ) → ℝ}
    (h : ∀ y₀ : Fin (d + 1) → ℝ, ∃ (B : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
      (W : Set (Fin (d + 1) → ℝ)), IsRealFamily B ∧ IsOpen W ∧ y₀ ∈ W ∧
        Set.EqOn P (kgChartPotential B) W) :
    OpenProbes (kgWaveOp d) P := by
  intro y₀
  obtain ⟨B, W, hBreal, hWopen, hWmem, hWeq⟩ := h y₀
  obtain ⟨W', hW'open, hW'mem, u, hu, hune⟩ := openProbes_kgChartPotential B hN hBreal y₀
  refine ⟨W ∩ W', hWopen.inter hW'open, ⟨hWmem, hW'mem⟩, u, fun z hz => ?_,
    fun z hz => hune z hz.2⟩
  have hzeq : P z = kgChartPotential B z := hWeq hz.1
  have hsolve := hu z hz.2
  show kgWaveOp d u z + P z * u z = 0
  rw [hzeq]
  exact hsolve

/-- **The probe determines the potential.** Any potential for which the constructed probes solve
agrees with the constructed potential everywhere. -/
theorem potential_eq_of_kgOpenProbes
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (hreal : IsRealFamily A)
    {other : (Fin (d + 1) → ℝ) → ℝ}
    (h : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn (kgWaveOp d) (kgChartPotential A) u W →
      SolvesPotentialWaveOn (kgWaveOp d) other u W) :
    other = kgChartPotential A :=
  potential_eq_of_openProbes (openProbes_kgChartPotential A hN hreal) h

end Anywhere

/-! ## Every smooth static potential -/

section StaticSmooth

open SchwartzMap

variable {d N : ℕ}

/-- A cutoff at a point. -/
noncomputable def kgCutoff (x₀ : EuclideanSpace ℝ (Fin d)) : ContDiffBump x₀ :=
  ⟨1, 2, one_pos, one_lt_two⟩

/-- The localised potential: the smooth potential, cut off around a point, as a Schwartz
function. -/
noncomputable def kgLocalPotential {p : EuclideanSpace ℝ (Fin d) → ℝ} (hp : ContDiff ℝ ∞ p)
    (x₀ : EuclideanSpace ℝ (Fin d)) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := by
  refine HasCompactSupport.toSchwartzMap
    (f := fun x : EuclideanSpace ℝ (Fin d) => ((kgCutoff x₀ x * (p x + 1) : ℝ) : ℂ)) ?_ ?_
  · have hbase : HasCompactSupport fun x : EuclideanSpace ℝ (Fin d) =>
        (kgCutoff x₀) x * (p x + 1) :=
      (kgCutoff x₀).hasCompactSupport.mul_right
    exact hbase.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  · refine Complex.ofRealCLM.contDiff.comp ?_
    exact ((kgCutoff x₀).contDiff).mul (hp.add contDiff_const)

theorem kgLocalPotential_apply {p : EuclideanSpace ℝ (Fin d) → ℝ} (hp : ContDiff ℝ ∞ p)
    (x₀ x : EuclideanSpace ℝ (Fin d)) :
    kgLocalPotential hp x₀ x = ((kgCutoff x₀ x * (p x + 1) : ℝ) : ℂ) := rfl

theorem kgLocalPotential_real {p : EuclideanSpace ℝ (Fin d) → ℝ} (hp : ContDiff ℝ ∞ p)
    (x₀ x : EuclideanSpace ℝ (Fin d)) :
    (starRingEnd ℂ) (kgLocalPotential hp x₀ x) = kgLocalPotential hp x₀ x := by
  rw [kgLocalPotential_apply, Complex.conj_ofReal]

theorem kgLocalPotential_eq_of_mem_ball {p : EuclideanSpace ℝ (Fin d) → ℝ} (hp : ContDiff ℝ ∞ p)
    (x₀ : EuclideanSpace ℝ (Fin d)) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Metric.ball x₀ 1) : (kgLocalPotential hp x₀ x).re = p x + 1 := by
  have hone : (kgCutoff x₀) x = 1 :=
    (kgCutoff x₀).one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  rw [kgLocalPotential_apply, Complex.ofReal_re, hone, one_mul]

/-- **Clock probes for every smooth static potential**, with no decay hypothesis: the potential is
cut off near each event, and the probe only has to solve there. -/
theorem openProbes_of_static_smooth
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {p : EuclideanSpace ℝ (Fin d) → ℝ} (hp : ContDiff ℝ ∞ p) :
    OpenProbes (kgWaveOp d) (fun y : Fin (d + 1) → ℝ => p (kgSpatial d y)) := by
  refine openProbes_of_locally_kgChartPotential (N := N) hN fun y₀ => ?_
  set x₀ : EuclideanSpace ℝ (Fin d) := kgSpatial d y₀ with hx₀
  refine ⟨(WienerDensity.ofSchwartz (𝓕 (kgLocalPotential hp x₀)) N).constFamily,
    (kgSpatial d) ⁻¹' Metric.ball x₀ 1,
    isRealFamily_constFamily
      (isRealDensity_ofSchwartz_fourier _ (kgLocalPotential_real hp x₀) N),
    (Metric.isOpen_ball).preimage (continuous_kgSpatial d), ?_, ?_⟩
  · show kgSpatial d y₀ ∈ Metric.ball x₀ 1
    rw [← hx₀]
    exact Metric.mem_ball_self one_pos
  · intro z hz
    have hball : kgSpatial d z ∈ Metric.ball x₀ 1 := hz
    rw [kgChartPotential_ofSchwartz, kgLocalPotential_eq_of_mem_ball hp x₀ hball]
    ring

end StaticSmooth

end GaloisForLFunctions.HTGeometry
