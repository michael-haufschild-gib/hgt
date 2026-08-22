import GaloisForLFunctions.HTGeometry.LocalPauliAutonomousObserverLaw
import GaloisForLFunctions.HTGeometry.EuclideanAnalyticNullPreimage
import GaloisForLFunctions.HTGeometry.RealFiniteAnalyticEscape
import GaloisForLFunctions.HTGeometry.SublevelVanishing

/-!
# Fixed-time anti-concentration for one local Hamiltonian draw

A nonzero visible jet of a globally real-analytic endpoint makes every scalar
level Gaussian-null.  Finite-measure continuity then upgrades exact nullity to
simultaneous approximate anti-concentration against every finite target family.

For the complete active fixed-locality Pauli ensemble, the canonical
coefficient reporter has identity derivative at the zero Hamiltonian at every
nonzero laboratory time.  Thus the general law applies without a genericity,
spectral-gap, or independence premise.  Reporter anti-concentration transports
back to the actual matrix exponential in the `L2Operator` norm.  The resulting
radius is positive for each finite circuit dictionary; no dimension- or
depth-uniform lower bound on that radius is claimed.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A globally real-analytic nonconstant scalar observable has no atoms under
the standard Gaussian parameter law. -/
theorem analytic_scalar_level_stdGaussian_zero
    {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : AnalyticOnNhd ℝ f univ)
    (hnc : ∃ x y, f x ≠ f y) (c : ℝ) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {x | f x = c} = 0 := by
  have hlocal : ∀ V : Set (EuclideanSpace ℝ (Fin m)),
      IsOpen V → V.Nonempty → V ⊆ univ →
        ∃ p ∈ V, ∃ q ∈ V, f p ≠ f q := by
    intro V hV hVne hVU
    obtain ⟨q, hqV⟩ := hVne
    have hne : ∃ p ∈ (univ : Set (EuclideanSpace ℝ (Fin m))),
        f p - f q ≠ 0 := by
      obtain ⟨a, b, hab⟩ := hnc
      by_cases ha : f a = f q
      · exact ⟨b, mem_univ _, sub_ne_zero.mpr
          (fun hb => hab (ha.trans hb.symm))⟩
      · exact ⟨a, mem_univ _, sub_ne_zero.mpr ha⟩
    obtain ⟨p, hpV, hpne⟩ := exists_mem_neZero_of_analyticOnNhd_real
      (hf.sub analyticOnNhd_const) isPreconnected_univ hne
      hV ⟨q, hqV⟩ hVU
    exact ⟨p, hpV, q, hqV, sub_ne_zero.mp hpne⟩
  have hvol : volume
      ((univ : Set (EuclideanSpace ℝ (Fin m))) ∩ f ⁻¹' {c}) = 0 :=
    analytic_preimage_volume_eq_zero_isOpen_euclidean
      isOpen_univ hf hlocal {c} (measure_singleton c)
  rw [univ_inter] at hvol
  rw [stdGaussian_eq_withDensity]
  apply withDensity_absolutelyContinuous _ _
  change volume (f ⁻¹' {c}) = 0
  exact hvol

/-- A globally analytic vector endpoint whose coordinates are nonconstant is
simultaneously anti-concentrated against every finite target family at some
positive radius. -/
theorem analytic_vector_finiteTarget_exists_small_stdGaussian_tube
    {m v : ℕ} [Nonempty (Fin v)]
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin v)}
    (hF : AnalyticOnNhd ℝ F univ)
    (hnc : ∀ i : Fin v, ∃ x y, F x i ≠ F y i)
    {K : Type*} [Fintype K]
    (target : K → EuclideanSpace ℝ (Fin v))
    {failure : ℝ} (hfailure : 0 < failure) :
    ∃ radius : ℝ, 0 < radius ∧
      (stdGaussian (EuclideanSpace ℝ (Fin m))).real
        {x | ∃ k, dist (F x) (target k) ≤ radius} < failure := by
  let i₀ : Fin v := Classical.choice inferInstance
  let h : K → EuclideanSpace ℝ (Fin m) → ℝ :=
    fun k x => dist (F x) (target k)
  have hmeas : ∀ k, Measurable (h k) := by
    intro k
    exact (hF.continuous.dist continuous_const).measurable
  have hnull : ∀ k, stdGaussian (EuclideanSpace ℝ (Fin m))
      {x | h k x = 0} = 0 := by
    intro k
    have hcoord : AnalyticOnNhd ℝ (fun x => F x i₀) univ := by
      change AnalyticOnNhd ℝ
        ((EuclideanSpace.proj (𝕜 := ℝ) i₀) ∘ F) univ
      exact (EuclideanSpace.proj (𝕜 := ℝ) i₀).comp_analyticOnNhd hF
    have hsub : {x | h k x = 0} ⊆
        {x | F x i₀ = target k i₀} := by
      intro x hx
      have heq : F x = target k := dist_eq_zero.mp hx
      exact congrArg (fun z : EuclideanSpace ℝ (Fin v) => z i₀) heq
    apply measure_mono_null hsub
    exact analytic_scalar_level_stdGaussian_zero
      hcoord (hnc i₀) (target k i₀)
  obtain ⟨g, hg, hgb⟩ := exists_small_finite_sublevel
    (stdGaussian (EuclideanSpace ℝ (Fin m)))
    hmeas hnull hfailure
  refine ⟨g, hg, ?_⟩
  simpa [h, abs_of_nonneg dist_nonneg] using hgb

/-- Every positive qubit count and positive locality cutoff has at least one
active nonidentity Pauli coefficient. -/
theorem activePauliCoefficientIndex_succ_nonempty (n q : ℕ) :
    Nonempty (ActivePauliCoefficientIndex (n + 1) (q + 1)) := by
  let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let P : PauliTracelessLabel (n + 1) (q + 1) :=
    ⟨pauliXLabel i, by
      constructor
      · rw [pauliWeight_pauliXLabel]
        omega
      · exact pauliXLabel_ne_identity i⟩
  exact Fin.pos_iff_nonempty.mp (Fintype.card_pos_iff.mpr ⟨P⟩)

/-- At every nonzero time, every canonical reported Pauli coordinate of the
ordinary static local-Hamiltonian endpoint is nonconstant. -/
theorem nonzeroTimeActivePauli_coordinate_nonconstant
    (n q : ℕ) (t : ℝˣ) (i : ActivePauliCoefficientIndex n q) :
    ∃ x y, autonomousExponentialEndpoint
        (A := Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
        (nonzeroTimeActivePauliGenerator n q t)
        (nonzeroTimeActivePauliReporter n q t) x i ≠
      autonomousExponentialEndpoint
        (A := Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
        (nonzeroTimeActivePauliGenerator n q t)
        (nonzeroTimeActivePauliReporter n q t) y i := by
  let F := autonomousExponentialEndpoint
    (A := Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (nonzeroTimeActivePauliGenerator n q t)
    (nonzeroTimeActivePauliReporter n q t)
  have hFdiff : DifferentiableAt ℝ F 0 :=
    (autonomousExponentialEndpoint_analyticOnNhd
      (nonzeroTimeActivePauliGenerator n q t)
      (nonzeroTimeActivePauliReporter n q t)
      0 (mem_univ 0)).differentiableAt
  let phi : EuclideanSpace ℝ (ActivePauliCoefficientIndex n q) → ℝ :=
    (EuclideanSpace.proj (𝕜 := ℝ) i) ∘ F
  have hcoordDeriv : HasFDerivAt phi
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ F 0)) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp
      0 hFdiff.hasFDerivAt
  have hder : fderiv ℝ phi 0
      (unitTimeActivePauliDirections n q i) = 1 := by
    rw [hcoordDeriv.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [autonomousExponentialEndpoint_fderiv_zero]
    change nonzeroTimeActivePauliReporter n q t
      (nonzeroTimeActivePauliGenerator n q t
        (unitTimeActivePauliDirections n q i)) i = 1
    rw [nonzeroTimeActivePauliReporter_generator]
    simp [unitTimeActivePauliDirections]
  have hphi : ∃ x y, phi x ≠ phi y := by
    by_contra hcon
    push Not at hcon
    have hconst : phi = fun _ => phi 0 := by
      funext x
      exact hcon x 0
    have hz : fderiv ℝ phi 0
        (unitTimeActivePauliDirections n q i) = 0 := by
      rw [hconst]
      simp
    linarith
  simpa [phi, F, Function.comp_def] using hphi

/-- Fixed-time reporter anti-concentration for one ordinary local-Hamiltonian
draw, uniform over an arbitrary finite target dictionary. -/
theorem nonzeroTimeActivePauli_succ_finiteTarget_exists_small_stdGaussian_tube
    (n q : ℕ) (t : ℝˣ) {K : Type*} [Fintype K]
    (target : K → EuclideanSpace ℝ
      (ActivePauliCoefficientIndex (n + 1) (q + 1)))
    {failure : ℝ} (hfailure : 0 < failure) :
    ∃ radius : ℝ, 0 < radius ∧
      (stdGaussian (EuclideanSpace ℝ
        (ActivePauliCoefficientIndex (n + 1) (q + 1)))).real
        {x | ∃ k, dist
          (autonomousExponentialEndpoint
            (A := Matrix (Fin (n + 1) → Bool) (Fin (n + 1) → Bool) ℂ)
            (nonzeroTimeActivePauliGenerator (n + 1) (q + 1) t)
            (nonzeroTimeActivePauliReporter (n + 1) (q + 1) t) x)
          (target k) ≤ radius} < failure := by
  letI : Nonempty (ActivePauliCoefficientIndex (n + 1) (q + 1)) :=
    activePauliCoefficientIndex_succ_nonempty n q
  exact analytic_vector_finiteTarget_exists_small_stdGaussian_tube
    (autonomousExponentialEndpoint_analyticOnNhd
      (nonzeroTimeActivePauliGenerator (n + 1) (q + 1) t)
      (nonzeroTimeActivePauliReporter (n + 1) (q + 1) t))
    (nonzeroTimeActivePauli_coordinate_nonconstant (n + 1) (q + 1) t)
    target hfailure

/-- **Physical fixed-time finite-circuit anti-concentration.**  For every
positive qubit count, positive fixed-locality cutoff, nonzero laboratory time,
finite matrix target dictionary, and positive failure budget, one positive
`L2Operator`-norm radius makes capture by the complete dictionary less likely
than that budget under one Gaussian draw of the static local Hamiltonian. -/
theorem nonzeroTimeActivePauli_succ_finiteMatrixTarget_exists_small_stdGaussian_tube
    (n q : ℕ) (t : ℝˣ) {K : Type*} [Fintype K]
    (target : K → Matrix (Fin (n + 1) → Bool) (Fin (n + 1) → Bool) ℂ)
    {failure : ℝ} (hfailure : 0 < failure) :
    ∃ radius : ℝ, 0 < radius ∧
      (stdGaussian (EuclideanSpace ℝ
        (ActivePauliCoefficientIndex (n + 1) (q + 1)))).real
        {x | ∃ k, dist
          (NormedSpace.exp
            (nonzeroTimeActivePauliGenerator (n + 1) (q + 1) t x))
          (target k) ≤ radius} < failure := by
  let R := nonzeroTimeActivePauliReporter (n + 1) (q + 1) t
  let reportedTarget : K → EuclideanSpace ℝ
      (ActivePauliCoefficientIndex (n + 1) (q + 1)) :=
    fun k => R (target k)
  obtain ⟨g, hg, hgbound⟩ :=
    nonzeroTimeActivePauli_succ_finiteTarget_exists_small_stdGaussian_tube
      n q t reportedTarget hfailure
  let radius : ℝ := g / (‖R‖ + 1)
  have hden : 0 < ‖R‖ + 1 := by positivity
  have hradius : 0 < radius := div_pos hg hden
  refine ⟨radius, hradius, ?_⟩
  apply lt_of_le_of_lt (measureReal_mono ?_) hgbound
  rintro x ⟨k, hk⟩
  refine ⟨k, ?_⟩
  change dist
      (R (NormedSpace.exp
        (nonzeroTimeActivePauliGenerator (n + 1) (q + 1) t x)))
      (R (target k)) ≤ g
  rw [dist_eq_norm, ← map_sub]
  calc
    ‖R (NormedSpace.exp
          (nonzeroTimeActivePauliGenerator (n + 1) (q + 1) t x) -
        target k)‖ ≤
        ‖R‖ * ‖NormedSpace.exp
          (nonzeroTimeActivePauliGenerator (n + 1) (q + 1) t x) -
        target k‖ := R.le_opNorm _
    _ = ‖R‖ * dist
          (NormedSpace.exp
            (nonzeroTimeActivePauliGenerator (n + 1) (q + 1) t x))
          (target k) := by rw [dist_eq_norm]
    _ ≤ ‖R‖ * radius :=
      mul_le_mul_of_nonneg_left hk (norm_nonneg R)
    _ = (‖R‖ * g) / (‖R‖ + 1) := by
      simp only [radius]
      ring
    _ ≤ g := (div_le_iff₀ hden).2 (by nlinarith [norm_nonneg R])

end

end GaloisForLFunctions.HTGeometry
