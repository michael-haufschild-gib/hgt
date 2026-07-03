/-
# Böttcher tower — Brolin: arbitrary-target limiting Brolin measures

This module is part of the split Brolin/Riesz-measure interface. Import
`GaloisForLFunctions.Bottcher.Brolin` for the full public surface.
-/
import GaloisForLFunctions.Bottcher.Brolin.BoundaryCriteria
import Mathlib.MeasureTheory.Measure.Support

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-! ## Arbitrary-target limiting Brolin measures

The zero-target construction is useful for the exterior identity, but for
`c = 0` it selects the exceptional pullback sequence.  The following block
builds the same compactness/potential package for arbitrary target pullbacks.
-/

/-- A target-dependent escape disk containing every level-`n` pullback atom of
`a`. -/
def targetEscapeDisk (c a : ℂ) : Set ℂ :=
  Metric.closedBall 0 (max (max 2 ‖c‖) ‖a‖)

/-- Every arbitrary-target pullback atom lies in its target-dependent escape
disk. -/
theorem mem_targetEscapeDisk_of_mem_roots_quadraticPolyIterate_sub_C
    {c a z : ℂ} {n : ℕ}
    (hz : z ∈ (quadraticPolyIterate c n - Polynomial.C a).roots) :
    z ∈ targetEscapeDisk c a := by
  rw [targetEscapeDisk, Metric.mem_closedBall, dist_zero_right]
  by_contra hle
  rw [not_le] at hle
  have h2 : 2 < ‖z‖ :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hc : ‖c‖ ≤ ‖z‖ :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hle)
  have ha : ‖a‖ < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hle
  have hzroot : (quadratic c)^[n] z = a := by
    have hp : quadraticPolyIterate c n - Polynomial.C a ≠ 0 :=
      (quadraticPolyIterate_sub_C_monic c a n).ne_zero
    have hisroot : (quadraticPolyIterate c n - Polynomial.C a).IsRoot z :=
      (Polynomial.mem_roots hp).mp hz
    rwa [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
      quadraticPolyIterate_eval, sub_eq_zero] at hisroot
  have horbit := norm_le_orbit hc h2 n
  rw [hzroot] at horbit
  exact not_le_of_gt ha horbit

/-- The unnormalized arbitrary-target counting measure is carried by the
target-dependent escape disk. -/
theorem rootCountingMeasure_roots_sub_C_targetEscapeDisk_compl
    (c a : ℂ) (n : ℕ) :
    rootCountingMeasure (quadraticPolyIterate c n - Polynomial.C a).roots
        (targetEscapeDisk c a)ᶜ = 0 :=
  rootCountingMeasure_compl_eq_zero_of_forall_mem _ _ fun _ hz =>
    mem_targetEscapeDisk_of_mem_roots_quadraticPolyIterate_sub_C hz

/-- Each finite arbitrary-target pre-Brolin measure is carried by the
target-dependent escape disk. -/
theorem preBrolinMeasureAt_targetEscapeDisk_compl (c a : ℂ) (n : ℕ) :
    preBrolinMeasureAt c a n (targetEscapeDisk c a)ᶜ = 0 := by
  rw [preBrolinMeasureAt, Measure.smul_apply,
    rootCountingMeasure_roots_sub_C_targetEscapeDisk_compl]
  simp

/-- The finite arbitrary-target pullback measure, regarded as a measure on its
compact target-dependent escape disk. -/
noncomputable def preBrolinMeasureAtOnTargetEscapeDisk
    (c a : ℂ) (n : ℕ) : Measure (targetEscapeDisk c a) :=
  ((2 ^ n : ENNReal)⁻¹) •
    rootCountingMeasureOn (targetEscapeDisk c a)
      (quadraticPolyIterate c n - Polynomial.C a).roots
      (fun _ hz => mem_targetEscapeDisk_of_mem_roots_quadraticPolyIterate_sub_C hz)

/-- The compact-carrier arbitrary-target measure pushes forward to the plane
finite arbitrary-target pre-Brolin measure. -/
theorem map_preBrolinMeasureAtOnTargetEscapeDisk_subtype_coe
    (c a : ℂ) (n : ℕ) :
    Measure.map (fun z : targetEscapeDisk c a => (z : ℂ))
        (preBrolinMeasureAtOnTargetEscapeDisk c a n) =
      preBrolinMeasureAt c a n := by
  rw [preBrolinMeasureAtOnTargetEscapeDisk, preBrolinMeasureAt, Measure.map_smul,
    map_rootCountingMeasureOn_subtype_coe]

theorem preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk
    (c a : ℂ) (n : ℕ) :
    preBrolinMeasureAt c a n =
      Measure.map (fun z : targetEscapeDisk c a => (z : ℂ))
        (preBrolinMeasureAtOnTargetEscapeDisk c a n) :=
  (map_preBrolinMeasureAtOnTargetEscapeDisk_subtype_coe c a n).symm

/-- Plane compactly supported test integrals against arbitrary-target finite
measures can be computed on the target-dependent escape disk. -/
theorem integral_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a : ℂ) (n : ℕ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂preBrolinMeasureAt c a n =
      ∫ z : targetEscapeDisk c a, φ (z : ℂ)
        ∂preBrolinMeasureAtOnTargetEscapeDisk c a n := by
  rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- Truncated-kernel integrals against arbitrary-target finite measures can be
computed on the target-dependent escape disk. -/
theorem integral_truncatedLogKernel_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, truncatedLogKernel z δ w ∂preBrolinMeasureAt c a n =
      ∫ w : targetEscapeDisk c a, truncatedLogKernel z δ (w : ℂ)
        ∂preBrolinMeasureAtOnTargetEscapeDisk c a n := by
  rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable

/-- Carrier form of finite arbitrary-target Green-sublevel confinement. -/
theorem preBrolinMeasureAtOnTargetEscapeDisk_greenSublevel_preimage_compl_of_scaled_target_le
    (c a : ℂ) (n : ℕ) {ε : ℝ}
    (hε : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a ≤ ε) :
    preBrolinMeasureAtOnTargetEscapeDisk c a n
      ((fun z : targetEscapeDisk c a => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ) = 0 := by
  have hset : MeasurableSet (greenSublevel c ε)ᶜ :=
    (measurableSet_greenSublevel c ε).compl
  have hmap := map_preBrolinMeasureAtOnTargetEscapeDisk_subtype_coe c a n
  have h := congrArg (fun μ : Measure ℂ => μ (greenSublevel c ε)ᶜ) hmap
  change (Measure.map (fun z : targetEscapeDisk c a => (z : ℂ))
      (preBrolinMeasureAtOnTargetEscapeDisk c a n)) (greenSublevel c ε)ᶜ =
        preBrolinMeasureAt c a n (greenSublevel c ε)ᶜ at h
  rw [Measure.map_apply measurable_subtype_coe hset] at h
  rw [h, preBrolinMeasureAt_greenSublevel_compl_of_scaled_target_le c a n hε]

theorem preBrolinMeasureAtOnTargetEscapeDisk_apply_univ
    (c a : ℂ) (n : ℕ) :
    preBrolinMeasureAtOnTargetEscapeDisk c a n Set.univ = 1 := by
  rw [preBrolinMeasureAtOnTargetEscapeDisk, Measure.smul_apply,
    rootCountingMeasureOn_apply_univ, roots_card_quadraticPolyIterate_sub_C]
  rw [smul_eq_mul]
  have hne : (2 ^ n : ENNReal) ≠ 0 := by simp
  have htop : (2 ^ n : ENNReal) ≠ ⊤ := by simp
  simpa using ENNReal.inv_mul_cancel hne htop

instance instIsProbabilityMeasure_preBrolinMeasureAtOnTargetEscapeDisk
    (c a : ℂ) (n : ℕ) :
    IsProbabilityMeasure (preBrolinMeasureAtOnTargetEscapeDisk c a n) where
  measure_univ := preBrolinMeasureAtOnTargetEscapeDisk_apply_univ c a n

noncomputable def preBrolinProbabilityAtOnTargetEscapeDisk
    (c a : ℂ) (n : ℕ) :
    ProbabilityMeasure (targetEscapeDisk c a) :=
  ⟨preBrolinMeasureAtOnTargetEscapeDisk c a n,
    instIsProbabilityMeasure_preBrolinMeasureAtOnTargetEscapeDisk c a n⟩

instance instCompactSpace_targetEscapeDisk (c a : ℂ) :
    CompactSpace (targetEscapeDisk c a) :=
  isCompact_iff_compactSpace.mp (by
    simpa [targetEscapeDisk] using
      (isCompact_closedBall (0 : ℂ) (max (max 2 ‖c‖) ‖a‖)))

/-- A chosen subsequential weak limit of the compact-carrier arbitrary-target
finite Brolin approximants. -/
noncomputable def brolinLimitAtOnTargetEscapeDiskData (c a : ℂ) :
    { μ : ProbabilityMeasure (targetEscapeDisk c a) //
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto
          (fun k => preBrolinProbabilityAtOnTargetEscapeDisk c a (ψ k))
          atTop (𝓝 μ) } := by
  classical
  let h := CompactSpace.tendsto_subseq (preBrolinProbabilityAtOnTargetEscapeDisk c a)
  let μ := Classical.choose h
  have hμ :
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (preBrolinProbabilityAtOnTargetEscapeDisk c a ∘ ψ)
          atTop (𝓝 μ) :=
    Classical.choose_spec h
  let ψ := Classical.choose hμ
  have hψ :
      StrictMono ψ ∧
        Tendsto (preBrolinProbabilityAtOnTargetEscapeDisk c a ∘ ψ)
          atTop (𝓝 μ) :=
    Classical.choose_spec hμ
  exact ⟨μ, ψ, hψ.1, by simpa [Function.comp_def] using hψ.2⟩

noncomputable def brolinLimitAtOnTargetEscapeDisk (c a : ℂ) :
    ProbabilityMeasure (targetEscapeDisk c a) :=
  (brolinLimitAtOnTargetEscapeDiskData c a).1

theorem brolinLimitAtOnTargetEscapeDisk_spec (c a : ℂ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto
        (fun k => preBrolinProbabilityAtOnTargetEscapeDisk c a (ψ k))
        atTop (𝓝 (brolinLimitAtOnTargetEscapeDisk c a)) :=
  (brolinLimitAtOnTargetEscapeDiskData c a).2

noncomputable def brolinLimitAtSubsequence (c a : ℂ) : ℕ → ℕ :=
  Classical.choose (brolinLimitAtOnTargetEscapeDisk_spec c a)

theorem brolinLimitAtSubsequence_strictMono (c a : ℂ) :
    StrictMono (brolinLimitAtSubsequence c a) :=
  (Classical.choose_spec (brolinLimitAtOnTargetEscapeDisk_spec c a)).1

theorem preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto (c a : ℂ) :
    Tendsto
      (fun k =>
        preBrolinProbabilityAtOnTargetEscapeDisk c a
          (brolinLimitAtSubsequence c a k))
      atTop (𝓝 (brolinLimitAtOnTargetEscapeDisk c a)) :=
  (Classical.choose_spec (brolinLimitAtOnTargetEscapeDisk_spec c a)).2

theorem le_brolinLimitAtSubsequence (c a : ℂ) (k : ℕ) :
    k ≤ brolinLimitAtSubsequence c a k := by
  have hψ := brolinLimitAtSubsequence_strictMono c a
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hlt : brolinLimitAtSubsequence c a k <
          brolinLimitAtSubsequence c a (k + 1) :=
        hψ (Nat.lt_succ_self k)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)

theorem brolinLimitAtSubsequence_tendsto_atTop (c a : ℂ) :
    Tendsto (brolinLimitAtSubsequence c a) atTop atTop :=
  (brolinLimitAtSubsequence_strictMono c a).tendsto_atTop

/-- The arbitrary-target limiting Brolin measure on the plane. -/
noncomputable def limitingBrolinMeasureAt (c a : ℂ) : Measure ℂ :=
  Measure.map (fun z : targetEscapeDisk c a => (z : ℂ))
    (brolinLimitAtOnTargetEscapeDisk c a : Measure (targetEscapeDisk c a))

instance instIsProbabilityMeasure_limitingBrolinMeasureAt (c a : ℂ) :
    IsProbabilityMeasure (limitingBrolinMeasureAt c a) := by
  rw [limitingBrolinMeasureAt]
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem integral_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂limitingBrolinMeasureAt c a =
      ∫ z : targetEscapeDisk c a, φ (z : ℂ)
        ∂(brolinLimitAtOnTargetEscapeDisk c a :
          Measure (targetEscapeDisk c a)) := by
  rw [limitingBrolinMeasureAt, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- Restrict a compactly supported plane test function to the target-dependent
escape disk. -/
noncomputable def compactRestrictionOnTargetEscapeDisk
    (c a : ℂ) (φ : C_c(ℂ, ℝ)) :
    BoundedContinuousFunction (targetEscapeDisk c a) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z : targetEscapeDisk c a => φ (z : ℂ),
      φ.continuous.comp continuous_subtype_val⟩

theorem preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
    (c a : ℂ) (φ : C_c(ℂ, ℝ)) :
    Tendsto
      (fun k =>
        ∫ z : targetEscapeDisk c a, φ (z : ℂ)
          ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a
              (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)))
      atTop
      (𝓝 (∫ z : targetEscapeDisk c a, φ (z : ℂ)
          ∂(brolinLimitAtOnTargetEscapeDisk c a :
            Measure (targetEscapeDisk c a)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a))
      (compactRestrictionOnTargetEscapeDisk c a φ)
  simpa [compactRestrictionOnTargetEscapeDisk] using h

/-- Weak convergence of the chosen arbitrary-target subsequence to a plane
measure, in compactly supported test-function form. -/
def IsWeakSubseqLimitOfPreBrolinAt
    (c a : ℂ) (ψ : ℕ → ℕ) (μ : Measure ℂ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    Tendsto (fun k => ∫ z, φ z ∂preBrolinMeasureAt c a (ψ k))
      atTop (𝓝 (∫ z, φ z ∂μ))

theorem limitingBrolinMeasureAt_isWeakSubseqLimitOfPreBrolinAt
    (c a : ℂ) :
    IsWeakSubseqLimitOfPreBrolinAt c a (brolinLimitAtSubsequence c a)
      (limitingBrolinMeasureAt c a) := by
  intro φ
  have h := preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto c a φ
  rw [integral_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_preBrolinMeasureAt_eq_integral_targetEscapeDisk]
  rfl

/-- The Riesz-Markov positive functional represented by the arbitrary-target
limiting Brolin measure.  The remaining GAP-A analytic step is to identify this
functional with `(2π)⁻¹ ΔG_c`; this definition removes the last target-specific
gap in the limiting/Riesz functional construction. -/
noncomputable def limitingBrolinRieszFunctionalAt
    (c a : ℂ) : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := fun φ => ∫ z, φ z ∂limitingBrolinMeasureAt c a
    map_add' := by
      intro φ ψ
      change ∫ z, φ z + ψ z ∂limitingBrolinMeasureAt c a =
        ∫ z, φ z ∂limitingBrolinMeasureAt c a +
          ∫ z, ψ z ∂limitingBrolinMeasureAt c a
      rw [integral_add]
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    map_smul' := by
      intro r φ
      change ∫ z, r • φ z ∂limitingBrolinMeasureAt c a =
        r • ∫ z, φ z ∂limitingBrolinMeasureAt c a
      rw [integral_smul]
    monotone' := by
      intro φ ψ hφψ
      apply integral_mono _ _ hφψ
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport }

theorem limitingBrolinRieszFunctionalAt_apply
    (c a : ℂ) (φ : C_c(ℂ, ℝ)) :
    limitingBrolinRieszFunctionalAt c a φ =
      ∫ z, φ z ∂limitingBrolinMeasureAt c a := by
  rfl

/-- The measure side of the arbitrary-target limiting Riesz functional. -/
noncomputable def limitingBrolinRieszMeasureAt (c a : ℂ) : Measure ℂ :=
  limitingBrolinMeasureAt c a

/-- The limiting Riesz-measure side is exactly the constructed limiting Brolin
measure. -/
theorem limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt
    (c a : ℂ) :
    limitingBrolinRieszMeasureAt c a = limitingBrolinMeasureAt c a := by
  rfl

theorem limitingBrolinRieszMeasureAt_integral_eq_functional
    (c a : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂limitingBrolinRieszMeasureAt c a =
      limitingBrolinRieszFunctionalAt c a φ := by
  rw [limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt,
    limitingBrolinRieszFunctionalAt_apply]

/-- Functional version of arbitrary-target weak convergence. -/
def IsWeakSubseqLimitFunctionalOfPreBrolinAt
    (c a : ℂ) (ψ : ℕ → ℕ) (Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    Tendsto (fun k => preBrolinRieszFunctionalAt c a (ψ k) φ)
      atTop (𝓝 (Λ φ))

/-- The arbitrary-target limiting Riesz functional is represented by the weak
limit of the finite arbitrary-target pre-Brolin Riesz functionals. -/
theorem limitingBrolinRieszFunctionalAt_isWeakSubseqLimitFunctionalOfPreBrolinAt
    (c a : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolinAt c a (brolinLimitAtSubsequence c a)
      (limitingBrolinRieszFunctionalAt c a) := by
  intro φ
  have h := limitingBrolinMeasureAt_isWeakSubseqLimitOfPreBrolinAt c a φ
  simpa [preBrolinRieszFunctionalAt_apply, limitingBrolinRieszFunctionalAt_apply] using h

theorem eventually_preBrolinMeasureAt_subseq_greenSublevel_compl_of_pos
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
        (greenSublevel c ε)ᶜ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_target_le_of_pos c a hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact preBrolinMeasureAt_greenSublevel_compl_of_scaled_target_le
    c a (brolinLimitAtSubsequence c a k)
    (hN (brolinLimitAtSubsequence c a k)
      (le_trans hk (le_brolinLimitAtSubsequence c a k)))

/-- Along the chosen arbitrary-target compactness subsequence, finite Riesz
functionals vanish eventually on every test function that vanishes on a
positive Green sublevel. -/
theorem eventually_preBrolinRieszFunctionalAt_subseq_eq_zero_of_eq_zero_on_greenSublevel
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    ∀ᶠ k in atTop,
      preBrolinRieszFunctionalAt c a (brolinLimitAtSubsequence c a k) φ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_target_le_of_pos c a hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact preBrolinRieszFunctionalAt_eq_zero_of_scaled_target_le_of_eq_zero_on_greenSublevel
    c a (brolinLimitAtSubsequence c a k) φ
    (hN (brolinLimitAtSubsequence c a k)
      (le_trans hk (le_brolinLimitAtSubsequence c a k))) hφ

/-- The arbitrary-target limiting Riesz functional vanishes on every compactly
supported test function that vanishes on a positive Green sublevel. -/
theorem limitingBrolinRieszFunctionalAt_eq_zero_of_eq_zero_on_greenSublevel
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    limitingBrolinRieszFunctionalAt c a φ = 0 := by
  have hlim :=
    limitingBrolinRieszFunctionalAt_isWeakSubseqLimitFunctionalOfPreBrolinAt
      c a φ
  have hzero :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (𝓝 (limitingBrolinRieszFunctionalAt c a φ)) := by
    exact hlim.congr'
      (eventually_preBrolinRieszFunctionalAt_subseq_eq_zero_of_eq_zero_on_greenSublevel
        c a hε φ hφ)
  exact (tendsto_nhds_unique tendsto_const_nhds hzero).symm

theorem eventually_preBrolinMeasureAtOnTargetEscapeDisk_subseq_greenSublevel_preimage_compl_of_pos
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      preBrolinMeasureAtOnTargetEscapeDisk c a
        (brolinLimitAtSubsequence c a k)
        ((fun z : targetEscapeDisk c a => (z : ℂ)) ⁻¹'
          (greenSublevel c ε)ᶜ) = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_target_le_of_pos c a hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact
    preBrolinMeasureAtOnTargetEscapeDisk_greenSublevel_preimage_compl_of_scaled_target_le
      c a (brolinLimitAtSubsequence c a k)
      (hN (brolinLimitAtSubsequence c a k)
        (le_trans hk (le_brolinLimitAtSubsequence c a k)))

/-- The arbitrary-target compact-carrier weak limit is carried by every positive
Green sublevel, pulled back to its target-dependent escape disk. -/
theorem brolinLimitAtOnTargetEscapeDisk_greenSublevel_preimage_compl_of_pos
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (brolinLimitAtOnTargetEscapeDisk c a :
      Measure (targetEscapeDisk c a))
      (((fun z : targetEscapeDisk c a => (z : ℂ)) ⁻¹'
        (greenSublevel c ε)ᶜ)) = 0 := by
  let G : Set (targetEscapeDisk c a) :=
    ((fun z : targetEscapeDisk c a => (z : ℂ)) ⁻¹'
      (greenSublevel c ε)ᶜ)
  have hGopen : IsOpen G := by
    dsimp [G]
    exact ((isClosed_greenSublevel c ε).isOpen_compl).preimage continuous_subtype_val
  have hle :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a) hGopen
  have hevent :
      ∀ᶠ k in atTop,
        (preBrolinProbabilityAtOnTargetEscapeDisk c a
          (brolinLimitAtSubsequence c a k) :
          Measure (targetEscapeDisk c a)) G = 0 := by
    filter_upwards
      [eventually_preBrolinMeasureAtOnTargetEscapeDisk_subseq_greenSublevel_preimage_compl_of_pos
        c a hε] with k hk
    simpa [G, preBrolinProbabilityAtOnTargetEscapeDisk] using hk
  have htend :
      Tendsto
        (fun k =>
          (preBrolinProbabilityAtOnTargetEscapeDisk c a
            (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)) G)
        atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hevent] with k hk
    exact hk.symm
  have hliminf :
      atTop.liminf
        (fun k =>
          (preBrolinProbabilityAtOnTargetEscapeDisk c a
            (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)) G) = 0 :=
    htend.liminf_eq
  have hle_zero :
      (brolinLimitAtOnTargetEscapeDisk c a :
        Measure (targetEscapeDisk c a)) G ≤ 0 := by
    rw [← hliminf]
    exact hle
  have hGzero :
      (brolinLimitAtOnTargetEscapeDisk c a :
        Measure (targetEscapeDisk c a)) G = 0 :=
    le_antisymm hle_zero bot_le
  simpa [G] using hGzero

theorem limitingBrolinMeasureAt_greenSublevel_compl_of_pos
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    limitingBrolinMeasureAt c a (greenSublevel c ε)ᶜ = 0 := by
  have hmeas : MeasurableSet (greenSublevel c ε)ᶜ :=
    (measurableSet_greenSublevel c ε).compl
  rw [limitingBrolinMeasureAt, Measure.map_apply measurable_subtype_coe hmeas]
  exact brolinLimitAtOnTargetEscapeDisk_greenSublevel_preimage_compl_of_pos c a hε

theorem limitingBrolinMeasureAt_filledJulia_compl (c a : ℂ) :
    limitingBrolinMeasureAt c a (filledJulia c)ᶜ = 0 := by
  rw [filledJulia_compl_eq_iUnion_greenSublevel_inv_nat_succ_compl c]
  apply measure_iUnion_null
  intro n
  exact limitingBrolinMeasureAt_greenSublevel_compl_of_pos c a (by positivity)

theorem limitingBrolinMeasureAt_isProbOn_filledJulia (c a : ℂ) :
    IsProbOn (limitingBrolinMeasureAt c a) (filledJulia c) :=
  ⟨instIsProbabilityMeasure_limitingBrolinMeasureAt c a,
    limitingBrolinMeasureAt_filledJulia_compl c a⟩

theorem limitingBrolinRieszMeasureAt_isProbOn_filledJulia (c a : ℂ) :
    IsProbOn (limitingBrolinRieszMeasureAt c a) (filledJulia c) := by
  rw [limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt]
  exact limitingBrolinMeasureAt_isProbOn_filledJulia c a

noncomputable def truncatedLogKernelOnTargetEscapeDisk
    (c a z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (targetEscapeDisk c a) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : targetEscapeDisk c a => truncatedLogKernel z δ (w : ℂ),
      (continuous_truncatedLogKernel (z := z) hδ).comp continuous_subtype_val⟩

theorem integral_truncatedLogKernel_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasureAt c a =
      ∫ w : targetEscapeDisk c a, truncatedLogKernel z δ (w : ℂ)
        ∂(brolinLimitAtOnTargetEscapeDisk c a :
          Measure (targetEscapeDisk c a)) := by
  rw [limitingBrolinMeasureAt, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable

theorem truncatedLogKernel_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : targetEscapeDisk c a, truncatedLogKernel z δ (w : ℂ)
          ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a
              (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)))
      atTop
      (𝓝 (∫ w : targetEscapeDisk c a, truncatedLogKernel z δ (w : ℂ)
          ∂(brolinLimitAtOnTargetEscapeDisk c a :
            Measure (targetEscapeDisk c a)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a))
      (truncatedLogKernelOnTargetEscapeDisk c a z δ hδ)
  simpa [truncatedLogKernelOnTargetEscapeDisk] using h

theorem truncatedLogKernel_preBrolinMeasureAt_subseq_integral_tendsto_limiting
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k))
      atTop
      (𝓝 (∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasureAt c a)) := by
  have h :=
    truncatedLogKernel_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
      c a z hδ
  rw [integral_truncatedLogKernel_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    c a z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedLogKernel_preBrolinMeasureAt_eq_integral_targetEscapeDisk c a z hδ]
  rfl

theorem eventually_logPotential_preBrolinMeasureAt_subseq_eq_integral_truncatedLogKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      logPotential
          (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z =
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) := by
  filter_upwards [eventually_preBrolinMeasureAt_subseq_greenSublevel_compl_of_pos
    c a hε] with k hk
  exact logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support hk hsep

theorem logPotential_limitingBrolinMeasureAt_eq_integral_truncatedLogKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    logPotential (limitingBrolinMeasureAt c a) z =
      ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasureAt c a :=
  logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support
    (limitingBrolinMeasureAt_greenSublevel_compl_of_pos c a hε) hsep

/-- The logarithmic-potential part of weak convergence for arbitrary target
pullbacks along a selected subsequence. -/
def HasSubseqLogPotentialLimitAt
    (c a : ℂ) (ψ : ℕ → ℕ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto (fun k => - logPotential (preBrolinMeasureAt c a (ψ k)) z)
      atTop (𝓝 (- logPotential μ z))

theorem neg_logPotential_preBrolinMeasureAt_limitSubseq_tendsto_greenFunctionDyn_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto
      (fun k =>
        - logPotential
          (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
      atTop (𝓝 (greenFunctionDyn c z)) :=
  (neg_logPotential_preBrolinMeasureAt_tendsto_greenFunctionDyn_basin
    (c := c) (a := a) hz).comp (brolinLimitAtSubsequence_tendsto_atTop c a)

theorem limitingBrolinMeasureAt_hasSubseqLogPotentialLimitAt (c a : ℂ) :
    HasSubseqLogPotentialLimitAt c a (brolinLimitAtSubsequence c a)
      (limitingBrolinMeasureAt c a) := by
  intro z hz
  have hGne : greenFunctionDyn c z ≠ 0 := by
    intro hzero
    exact hz ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
  have hGpos : 0 < greenFunctionDyn c z :=
    lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
  let ε : ℝ := greenFunctionDyn c z / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < greenFunctionDyn c z := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hsep⟩ :=
    exists_pos_le_norm_of_greenSublevel_of_lt_green
      (c := c) (z := z) (ε := ε) hεlt
  have htrunc :=
    truncatedLogKernel_preBrolinMeasureAt_subseq_integral_tendsto_limiting
      c a z hδpos
  have hlim :=
    logPotential_limitingBrolinMeasureAt_eq_integral_truncatedLogKernel
      c a z hεpos hsep
  have hevent :=
    eventually_logPotential_preBrolinMeasureAt_subseq_eq_integral_truncatedLogKernel
      c a z hεpos hsep
  have hlog :
      Tendsto
        (fun k =>
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
        atTop (𝓝 (logPotential (limitingBrolinMeasureAt c a) z)) := by
    rw [hlim]
    exact htrunc.congr' (by
      filter_upwards [hevent] with k hk
      exact hk.symm)
  simpa using hlog.neg

theorem green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z = - logPotential (limitingBrolinMeasureAt c a) z :=
  tendsto_nhds_unique
    (neg_logPotential_preBrolinMeasureAt_limitSubseq_tendsto_greenFunctionDyn_basin
      (c := c) (a := a) hz)
    (limitingBrolinMeasureAt_hasSubseqLogPotentialLimitAt c a hz)

theorem green_eq_neg_logPotential_limitingBrolinRieszMeasureAt_on_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z =
      - logPotential (limitingBrolinRieszMeasureAt c a) z := by
  rw [limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt]
  exact green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin
    (c := c) (a := a) (z := z) hz

/-- Canonical nonzero-target hDisc-side limiting measure.  Choosing target `1`
avoids the zero-target exceptional degeneration at `c = 0`. -/
noncomputable def brolinMuOne (c : ℂ) : Measure ℂ :=
  limitingBrolinMeasureAt c 1

theorem brolinMuOne_hDiscCore (c : ℂ) :
    IsProbOn (brolinMuOne c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolinAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      HasSubseqLogPotentialLimitAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (brolinMuOne c) z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [brolinMuOne] using limitingBrolinMeasureAt_isProbOn_filledJulia c 1
  · simpa [brolinMuOne] using limitingBrolinMeasureAt_isWeakSubseqLimitOfPreBrolinAt c 1
  · simpa [brolinMuOne] using limitingBrolinMeasureAt_hasSubseqLogPotentialLimitAt c 1
  · intro z hz
    simpa [brolinMuOne] using
      green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin
        (c := c) (a := 1) (z := z) hz

/-- The positive Riesz-Markov functional represented by the canonical hDisc
limiting measure `brolinMuOne`. -/
noncomputable def brolinMuOneRieszFunctional
    (c : ℂ) : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  limitingBrolinRieszFunctionalAt c 1

theorem brolinMuOneRieszFunctional_apply
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    brolinMuOneRieszFunctional c φ =
      ∫ z, φ z ∂brolinMuOne c := by
  rfl

/-- The canonical hDisc Riesz-measure side represented by the target-one
limiting functional. -/
noncomputable def brolinMuOneRieszMeasure (c : ℂ) : Measure ℂ :=
  limitingBrolinRieszMeasureAt c 1

theorem brolinMuOneRieszMeasure_eq_brolinMuOne (c : ℂ) :
    brolinMuOneRieszMeasure c = brolinMuOne c := by
  rw [brolinMuOneRieszMeasure,
    limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt, brolinMuOne]

theorem brolinMuOneRieszMeasure_integral_eq_functional
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂brolinMuOneRieszMeasure c =
      brolinMuOneRieszFunctional c φ := by
  rw [brolinMuOneRieszMeasure_eq_brolinMuOne,
    brolinMuOneRieszFunctional_apply]

theorem brolinMuOneRieszMeasure_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (brolinMuOneRieszMeasure c) (filledJulia c) := by
  rw [brolinMuOneRieszMeasure_eq_brolinMuOne]
  exact (brolinMuOne_hDiscCore c).1

theorem brolinMuOneRieszMeasure_hasSubseqLogPotentialLimitAt (c : ℂ) :
    HasSubseqLogPotentialLimitAt c 1 (brolinLimitAtSubsequence c 1)
      (brolinMuOneRieszMeasure c) := by
  rw [brolinMuOneRieszMeasure_eq_brolinMuOne]
  exact (brolinMuOne_hDiscCore c).2.2.1

theorem green_eq_neg_logPotential_brolinMuOneRieszMeasure_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z =
      - logPotential (brolinMuOneRieszMeasure c) z := by
  rw [brolinMuOneRieszMeasure_eq_brolinMuOne]
  exact (brolinMuOne_hDiscCore c).2.2.2 z hz

/-- The canonical hDisc Riesz functional is the weak limit of the finite
`target = 1` pullback Riesz functionals. -/
theorem brolinMuOneRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolinAt
    (c : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolinAt c 1
      (brolinLimitAtSubsequence c 1) (brolinMuOneRieszFunctional c) := by
  simpa [brolinMuOneRieszFunctional] using
    limitingBrolinRieszFunctionalAt_isWeakSubseqLimitFunctionalOfPreBrolinAt c 1

/-- The canonical hDisc Riesz functional is carried, in compact-test form, by
every positive Green sublevel. -/
theorem brolinMuOneRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    brolinMuOneRieszFunctional c φ = 0 := by
  simpa [brolinMuOneRieszFunctional] using
    limitingBrolinRieszFunctionalAt_eq_zero_of_eq_zero_on_greenSublevel
      c 1 hε φ hφ

/-- Riesz-functional core for the constructed hDisc measure.  This is the
functional side of the limiting measure construction, separated from the later
distributional identity `(2π)⁻¹ΔG_c`. -/
theorem brolinMuOne_hDiscRieszFunctionalCore (c : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolinAt c 1
        (brolinLimitAtSubsequence c 1) (brolinMuOneRieszFunctional c) ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ φ : C_c(ℂ, ℝ),
        (∀ z, z ∈ greenSublevel c ε → φ z = 0) →
          brolinMuOneRieszFunctional c φ = 0 := by
  refine ⟨?_, ?_⟩
  · exact brolinMuOneRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolinAt c
  · intro ε hε φ hφ
    exact brolinMuOneRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel c hε φ hφ

/-- Canonical hDisc limiting/Riesz-measure package: the represented measure is
the constructed target-one limiting Brolin measure, it is carried by `K_c`, and
its exterior logarithmic potential is `G_c`. -/
theorem brolinMuOne_hDiscLimitingRieszMeasureCore (c : ℂ) :
    brolinMuOneRieszMeasure c = brolinMuOne c ∧
      IsProbOn (brolinMuOneRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolinAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOneRieszMeasure c) ∧
      HasSubseqLogPotentialLimitAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOneRieszMeasure c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuOneRieszMeasure c) z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact brolinMuOneRieszMeasure_eq_brolinMuOne c
  · exact brolinMuOneRieszMeasure_isProbOn_filledJulia c
  · rw [brolinMuOneRieszMeasure_eq_brolinMuOne]
    exact (brolinMuOne_hDiscCore c).2.1
  · exact brolinMuOneRieszMeasure_hasSubseqLogPotentialLimitAt c
  · intro z hz
    exact green_eq_neg_logPotential_brolinMuOneRieszMeasure_on_basin hz

end Bottcher

namespace Bottcher

noncomputable section

/-- Arbitrary-target hDisc limiting-measure package: the selected limiting
Brolin measure is carried by `K_c`, is the weak subsequential limit of the
finite target-`a` pre-Brolin measures, has the corresponding logarithmic
potential subsequential limit on the basin, and represents `G_c` there. -/
theorem limitingBrolinMeasureAt_hDiscCore (c a : ℂ) :
    IsProbOn (limitingBrolinMeasureAt c a) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolinAt c a (brolinLimitAtSubsequence c a)
        (limitingBrolinMeasureAt c a) ∧
      HasSubseqLogPotentialLimitAt c a (brolinLimitAtSubsequence c a)
        (limitingBrolinMeasureAt c a) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (limitingBrolinMeasureAt c a) z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact limitingBrolinMeasureAt_isProbOn_filledJulia c a
  · exact limitingBrolinMeasureAt_isWeakSubseqLimitOfPreBrolinAt c a
  · exact limitingBrolinMeasureAt_hasSubseqLogPotentialLimitAt c a
  · intro z hz
    exact green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin
      (c := c) (a := a) (z := z) hz

/-- Arbitrary-target Riesz-measure package for the same selected limiting
Brolin measure. -/
theorem limitingBrolinRieszMeasureAt_hDiscCore (c a : ℂ) :
    limitingBrolinRieszMeasureAt c a = limitingBrolinMeasureAt c a ∧
      IsProbOn (limitingBrolinRieszMeasureAt c a) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolinAt c a (brolinLimitAtSubsequence c a)
        (limitingBrolinRieszMeasureAt c a) ∧
      HasSubseqLogPotentialLimitAt c a (brolinLimitAtSubsequence c a)
        (limitingBrolinRieszMeasureAt c a) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (limitingBrolinRieszMeasureAt c a) z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt c a
  · exact limitingBrolinRieszMeasureAt_isProbOn_filledJulia c a
  · rw [limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt]
    exact (limitingBrolinMeasureAt_hDiscCore c a).2.1
  · rw [limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt]
    exact (limitingBrolinMeasureAt_hDiscCore c a).2.2.1
  · intro z hz
    exact green_eq_neg_logPotential_limitingBrolinRieszMeasureAt_on_basin
      (c := c) (a := a) (z := z) hz

end

end Bottcher

namespace Bottcher

noncomputable section

/-- The arbitrary-target limiting Brolin measure has no support outside the
filled Julia set.  This is the easy support inclusion coming from the proven
carrier statement `μ((K_c)ᶜ)=0`; the hard remaining support theorem is the
opposite Julia-frontier inclusion. -/
theorem limitingBrolinMeasureAt_support_subset_filledJulia (c a : ℂ) :
    (limitingBrolinMeasureAt c a).support ⊆ filledJulia c := by
  intro z hz
  by_contra hzK
  have hpos : 0 < limitingBrolinMeasureAt c a (filledJulia c)ᶜ := by
    rw [Measure.mem_support_iff_forall] at hz
    exact hz (filledJulia c)ᶜ ((isClosed_filledJulia c).isOpen_compl.mem_nhds hzK)
  rw [limitingBrolinMeasureAt_filledJulia_compl] at hpos
  exact (lt_irrefl _) hpos

/-- Riesz-measure variant of the same support inclusion. -/
theorem limitingBrolinRieszMeasureAt_support_subset_filledJulia (c a : ℂ) :
    (limitingBrolinRieszMeasureAt c a).support ⊆ filledJulia c := by
  rw [limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt]
  exact limitingBrolinMeasureAt_support_subset_filledJulia c a

/-- The target-one hDisc measure has no support outside the filled Julia set. -/
theorem brolinMuOne_support_subset_filledJulia (c : ℂ) :
    (brolinMuOne c).support ⊆ filledJulia c := by
  simpa [brolinMuOne] using limitingBrolinMeasureAt_support_subset_filledJulia c 1

/-- Riesz target-one hDisc measure support inclusion. -/
theorem brolinMuOneRieszMeasure_support_subset_filledJulia (c : ℂ) :
    (brolinMuOneRieszMeasure c).support ⊆ filledJulia c := by
  rw [brolinMuOneRieszMeasure_eq_brolinMuOne]
  exact brolinMuOne_support_subset_filledJulia c

end

end Bottcher
