import GaloisForLFunctions.RHTower.SuzukiDonoghueKernelUniformBound

/-!
# The endpoint mass is the linear Nevanlinna coefficient

The Donoghue kernel takes the *same* value `z` at both projective endpoints.  Consequently the
Herglotz transform of a compactified spectral probability splits as

`m(z) = alpha * z + int_interior K_z dnu`,

where `alpha` is the mass the measure puts on the two endpoints together.  That is exactly the
statement that the endpoint mass is the linear coefficient in the Nevanlinna representation of `m`:
the endpoints contribute nothing but a multiple of `z`, and every other feature of `m` comes from
the interior.

The mechanism is a two-set decomposition of the compact projective interval into its interior and
its two endpoints.  On the endpoint set the kernel is constant, so its integral is the endpoint
mass times that constant.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

/-- The two projective endpoints, inside the compact projective interval. -/
def projectiveEndpointSet : Set ↥projectiveInterval :=
  {t | (t : ℝ) = -(Real.pi / 2) ∨ (t : ℝ) = Real.pi / 2}

/-- The projective interior. -/
def projectiveInteriorSet : Set ↥projectiveInterval :=
  {t | (t : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)}

theorem measurableSet_projectiveInteriorSet : MeasurableSet projectiveInteriorSet :=
  measurable_subtype_coe measurableSet_Ioo

theorem measurableSet_projectiveEndpointSet : MeasurableSet projectiveEndpointSet := by
  have hpre : projectiveEndpointSet
      = Subtype.val ⁻¹' ({-(Real.pi / 2), Real.pi / 2} : Set ℝ) := rfl
  rw [hpre]
  exact measurable_subtype_coe ((measurableSet_singleton _).union (measurableSet_singleton _))

/-- The interior and the two endpoints exhaust the compact projective interval. -/
theorem projectiveInteriorSet_union_endpointSet :
    projectiveInteriorSet ∪ projectiveEndpointSet = Set.univ := by
  ext t
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  obtain ⟨x, hx⟩ := t
  rw [projectiveInterval] at hx
  by_cases h1 : x = -(Real.pi / 2)
  · exact Or.inr (Or.inl h1)
  · by_cases h2 : x = Real.pi / 2
    · exact Or.inr (Or.inr h2)
    · exact Or.inl ⟨lt_of_le_of_ne hx.1 (Ne.symm h1), lt_of_le_of_ne hx.2 h2⟩

theorem disjoint_projectiveInteriorSet_endpointSet :
    Disjoint projectiveInteriorSet projectiveEndpointSet := by
  rw [Set.disjoint_left]
  rintro t ht (h | h)
  · exact absurd h (ne_of_gt ht.1)
  · exact absurd h (ne_of_lt ht.2)

/-- The extended kernel is integrable against any finite measure on the compact interval. -/
theorem integrable_extendedProjectiveKernel
    (nu : Measure ↥projectiveInterval) [IsFiniteMeasure nu] {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ↥projectiveInterval => extendedProjectiveKernel (t : ℝ) z) nu := by
  have hcont : Continuous (fun t : ↥projectiveInterval => extendedProjectiveKernel (t : ℝ) z) :=
    (continuousOn_extendedProjectiveKernel hz).restrict
  exact hcont.integrable_of_hasCompactSupport isClosed_closure.isCompact

/-- **The endpoint mass is the linear Nevanlinna coefficient.**  Because the Donoghue kernel takes
the same value `z` at both projective endpoints, the Herglotz transform splits into that value
weighted by the endpoint mass, plus the interior transform. -/
theorem integral_extendedProjectiveKernel_split
    (nu : Measure ↥projectiveInterval) [IsFiniteMeasure nu] {z : ℂ} (hz : 0 < z.im) :
    ∫ t, extendedProjectiveKernel (t : ℝ) z ∂nu
      = nu.real projectiveEndpointSet • z
        + ∫ t in projectiveInteriorSet, extendedProjectiveKernel (t : ℝ) z ∂nu := by
  have hint := integrable_extendedProjectiveKernel nu hz
  have hsplit : ∫ t, extendedProjectiveKernel (t : ℝ) z ∂nu
      = (∫ t in projectiveInteriorSet, extendedProjectiveKernel (t : ℝ) z ∂nu)
        + ∫ t in projectiveEndpointSet, extendedProjectiveKernel (t : ℝ) z ∂nu := by
    rw [← setIntegral_univ, ← projectiveInteriorSet_union_endpointSet,
      setIntegral_union disjoint_projectiveInteriorSet_endpointSet
        measurableSet_projectiveEndpointSet hint.integrableOn hint.integrableOn]
  have heqOn : Set.EqOn (fun t : ↥projectiveInterval => extendedProjectiveKernel (t : ℝ) z)
      (fun _ => z) projectiveEndpointSet := by
    rintro t (h | h)
    · show extendedProjectiveKernel (t : ℝ) z = z
      rw [h]
      exact extendedProjectiveKernel_left z
    · show extendedProjectiveKernel (t : ℝ) z = z
      rw [h]
      exact extendedProjectiveKernel_right z
  have hconst : ∫ t in projectiveEndpointSet, extendedProjectiveKernel (t : ℝ) z ∂nu
      = nu.real projectiveEndpointSet • z := by
    rw [setIntegral_congr_fun measurableSet_projectiveEndpointSet heqOn, setIntegral_const]
  rw [hsplit, hconst, add_comm]

/-- **`(17)` in Nevanlinna form.**  Weak convergence of the compactified spectral probabilities
sends the Herglotz transforms to the limiting transform written with its linear coefficient
displayed: the endpoint mass of the limit times `z`, plus the interior transform. -/
theorem tendsto_integral_extendedProjectiveKernel_nevanlinna
    {ι : Type*} {l : Filter ι} {nu : ι → ProbabilityMeasure ↥projectiveInterval}
    {nu0 : ProbabilityMeasure ↥projectiveInterval}
    (h : Tendsto nu l (nhds nu0)) {z : ℂ} (hz : 0 < z.im) :
    Tendsto
      (fun i => ∫ t, extendedProjectiveKernel (t : ℝ) z ∂(nu i : Measure ↥projectiveInterval)) l
      (nhds ((nu0 : Measure ↥projectiveInterval).real projectiveEndpointSet • z
        + ∫ t in projectiveInteriorSet, extendedProjectiveKernel (t : ℝ) z
            ∂(nu0 : Measure ↥projectiveInterval))) := by
  have hlim := tendsto_integral_extendedProjectiveKernel h hz
  rwa [integral_extendedProjectiveKernel_split (nu0 : Measure ↥projectiveInterval) hz] at hlim

/-- **Zero linear coefficient means no endpoint mass.**  The endpoint contribution to the transform
vanishes for one spectral parameter above the real axis exactly when the measure puts no mass on
the two projective endpoints.  This is the second hypothesis of the closure theorem `(18)`, the one
that rules out endpoint residual. -/
theorem endpointMass_eq_zero_iff_smul_eq_zero
    (nu : Measure ↥projectiveInterval) [IsFiniteMeasure nu] {z : ℂ} (hz : 0 < z.im) :
    nu.real projectiveEndpointSet • z = 0 ↔ nu.real projectiveEndpointSet = 0 := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    exact absurd hz (lt_irrefl _)
  constructor
  · intro h
    rcases smul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' hzne
  · intro h
    rw [h, zero_smul]

/-! ## The two endpoints separately, and the closure theorem -/

/-- The left projective endpoint. -/
noncomputable def projectiveLeft : ↥projectiveInterval :=
  ⟨-(Real.pi / 2), Set.mem_Icc.mpr ⟨le_refl _, by linarith [Real.pi_pos]⟩⟩

/-- The right projective endpoint. -/
noncomputable def projectiveRight : ↥projectiveInterval :=
  ⟨Real.pi / 2, Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos], le_refl _⟩⟩

theorem projectiveLeft_ne_projectiveRight : projectiveLeft ≠ projectiveRight := by
  intro h
  have hval := congrArg Subtype.val h
  have : -(Real.pi / 2) = Real.pi / 2 := hval
  linarith [Real.pi_pos]

theorem projectiveEndpointSet_eq_pair :
    projectiveEndpointSet = {projectiveLeft, projectiveRight} := by
  ext t
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

/-- The endpoint mass is the sum of the two separate endpoint masses. -/
theorem measureReal_projectiveEndpointSet (nu : Measure ↥projectiveInterval)
    [IsFiniteMeasure nu] :
    nu.real projectiveEndpointSet
      = nu.real {projectiveLeft} + nu.real {projectiveRight} := by
  rw [projectiveEndpointSet_eq_pair, Set.insert_eq]
  refine measureReal_union ?_ (measurableSet_singleton _)
  simpa using projectiveLeft_ne_projectiveRight

/-- **Each endpoint carries half the linear coefficient.**  Suzuki symmetry makes the limiting
spectral measure even, and an even measure gives the two projective endpoints equal mass; each is
therefore half of the linear Nevanlinna coefficient. -/
theorem measureReal_endpoint_eq_half (nu : Measure ↥projectiveInterval) [IsFiniteMeasure nu]
    (heven : nu.real {projectiveLeft} = nu.real {projectiveRight}) :
    nu.real {projectiveLeft} = nu.real projectiveEndpointSet / 2 ∧
      nu.real {projectiveRight} = nu.real projectiveEndpointSet / 2 := by
  rw [measureReal_projectiveEndpointSet nu, ← heven]
  constructor <;> ring

/-- The interior mass and the endpoint mass exhaust a probability measure. -/
theorem measureReal_interior_add_endpoint (nu : Measure ↥projectiveInterval)
    [IsProbabilityMeasure nu] :
    nu.real projectiveInteriorSet + nu.real projectiveEndpointSet = 1 := by
  have hunion : nu.real (projectiveInteriorSet ∪ projectiveEndpointSet)
      = nu.real projectiveInteriorSet + nu.real projectiveEndpointSet :=
    measureReal_union disjoint_projectiveInteriorSet_endpointSet
      measurableSet_projectiveEndpointSet
  rw [← hunion, projectiveInteriorSet_union_endpointSet]
  simp

/-- **`(18)`, the closure theorem.**  Entire-pair normality kills the interior residual, so the
labelled mass accounts for all of the interior; a zero linear coefficient of the limiting Herglotz
function kills the endpoint mass.  The two hypotheses address disjoint mechanisms — condensation
inside a bounded physical window, and escape to projective infinity — and together they force the
labelled masses to sum to one, leaving no residual anywhere. -/
theorem suzuki_closure_labelledMass_eq_one (nu : Measure ↥projectiveInterval)
    [IsProbabilityMeasure nu] {labelledMass : ℝ}
    (hinterior : nu.real projectiveInteriorSet = labelledMass)
    (hendpoint : nu.real projectiveEndpointSet = 0) :
    labelledMass = 1 := by
  have h := measureReal_interior_add_endpoint nu
  rw [hinterior, hendpoint, add_zero] at h
  exact h

/-- The closure theorem stated from the vanishing of the linear coefficient itself, which is the
form `(18)` uses: a zero linear coefficient in the Nevanlinna representation is exactly zero
endpoint mass. -/
theorem suzuki_closure_labelledMass_eq_one_of_linearCoefficient
    (nu : Measure ↥projectiveInterval) [IsProbabilityMeasure nu] {labelledMass : ℝ} {z : ℂ}
    (hz : 0 < z.im) (hinterior : nu.real projectiveInteriorSet = labelledMass)
    (hlinear : nu.real projectiveEndpointSet • z = 0) :
    labelledMass = 1 :=
  suzuki_closure_labelledMass_eq_one nu hinterior
    ((endpointMass_eq_zero_iff_smul_eq_zero nu hz).mp hlinear)

end GaloisForLFunctions.RHTower
