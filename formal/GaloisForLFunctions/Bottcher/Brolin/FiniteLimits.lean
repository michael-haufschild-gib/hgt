/-
# Böttcher tower — Brolin: zero-target Riesz functionals and weak limits

This module is part of the split Brolin/Riesz-measure interface. Import
`GaloisForLFunctions.Bottcher.Brolin` for the full public surface.
-/
import GaloisForLFunctions.Bottcher.Brolin.FiniteMeasures

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The finite positive functional represented by the normalized level-`n`
zero-pullback measure. -/
noncomputable def preBrolinRieszFunctional (c : ℂ) (n : ℕ) :
    C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := fun φ => ∫ z, φ z ∂preBrolinMeasure c n
    map_add' := by
      intro φ ψ
      change ∫ z, φ z + ψ z ∂preBrolinMeasure c n =
        ∫ z, φ z ∂preBrolinMeasure c n + ∫ z, ψ z ∂preBrolinMeasure c n
      rw [integral_add]
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    map_smul' := by
      intro a φ
      change ∫ z, a • φ z ∂preBrolinMeasure c n =
        a • ∫ z, φ z ∂preBrolinMeasure c n
      rw [integral_smul]
    monotone' := by
      intro φ ψ hφψ
      apply integral_mono _ _ hφψ
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport }

theorem preBrolinRieszFunctional_apply (c : ℂ) (n : ℕ) (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctional c n φ =
      ∫ z, φ z ∂preBrolinMeasure c n := by
  rfl

/-- Finite Riesz functionals are normalized root averages. -/
theorem preBrolinRieszFunctional_apply_root_average (c : ℂ) (n : ℕ)
    (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctional c n φ =
      (2 ^ n : ℝ)⁻¹ *
        (((quadraticPolyIterate c n).roots.map fun z => φ z).sum) := by
  rw [preBrolinRieszFunctional_apply, integral_preBrolinMeasure_eq_root_average]

/-- Finite Riesz functionals can equivalently be integrated on the compact
escape-disk carrier. -/
theorem preBrolinRieszFunctional_apply_escapeDisk (c : ℂ) (n : ℕ)
    (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctional c n φ =
      ∫ z : escapeDisk c, φ (z : ℂ) ∂preBrolinMeasureOnEscapeDisk c n := by
  rw [preBrolinRieszFunctional_apply, integral_preBrolinMeasure_eq_integral_escapeDisk]

/-- If a test function vanishes on a Green sublevel that contains the level-`n`
zero-pullback atoms, then the level-`n` finite Brolin functional vanishes on it. -/
theorem preBrolinRieszFunctional_eq_zero_of_scaled_critical_le_of_eq_zero_on_greenSublevel
    (c : ℂ) (n : ℕ) {ε : ℝ} (φ : C_c(ℂ, ℝ))
    (hε : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c 0 ≤ ε)
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    preBrolinRieszFunctional c n φ = 0 := by
  rw [preBrolinRieszFunctional_apply_root_average]
  have hsum :
      (((quadraticPolyIterate c n).roots.map fun z => φ z).sum) = 0 := by
    have hmap :
        ((quadraticPolyIterate c n).roots.map fun z => φ z) =
          ((quadraticPolyIterate c n).roots.map fun _ => 0) := by
      apply Multiset.map_congr rfl
      intro z hz
      exact hφ z (by
        have hzsub :=
          mem_greenSublevel_scaled_critical_of_mem_roots_quadraticPolyIterate
            (c := c) (n := n) hz
        rw [mem_greenSublevel_iff] at hzsub ⊢
        exact le_trans hzsub hε)
    rw [hmap]
    simp
  rw [hsum, mul_zero]

/-- The subtype-carried finite pre-Brolin measure is normalized. -/
theorem preBrolinMeasureOnEscapeDisk_apply_univ (c : ℂ) (n : ℕ) :
    preBrolinMeasureOnEscapeDisk c n Set.univ = 1 := by
  rw [preBrolinMeasureOnEscapeDisk, Measure.smul_apply,
    rootCountingMeasureOn_apply_univ, roots_card_quadraticPolyIterate]
  rw [smul_eq_mul]
  have hne : (2 ^ n : ENNReal) ≠ 0 := by simp
  have htop : (2 ^ n : ENNReal) ≠ ⊤ := by simp
  simpa using ENNReal.inv_mul_cancel hne htop

instance instIsProbabilityMeasure_preBrolinMeasureOnEscapeDisk (c : ℂ) (n : ℕ) :
    IsProbabilityMeasure (preBrolinMeasureOnEscapeDisk c n) where
  measure_univ := preBrolinMeasureOnEscapeDisk_apply_univ c n

/-- The compact-carrier probability-measure form of the finite pre-Brolin
approximants. -/
noncomputable def preBrolinProbabilityOnEscapeDisk (c : ℂ) (n : ℕ) :
    ProbabilityMeasure (escapeDisk c) :=
  ⟨preBrolinMeasureOnEscapeDisk c n,
    instIsProbabilityMeasure_preBrolinMeasureOnEscapeDisk c n⟩

instance instCompactSpace_escapeDisk (c : ℂ) : CompactSpace (escapeDisk c) :=
  isCompact_iff_compactSpace.mp (by
    simpa [escapeDisk] using (isCompact_closedBall (0 : ℂ) (max 2 ‖c‖)))

/-- A chosen subsequential weak limit of the compact-carrier finite Brolin
approximants.  This is the first genuine limiting measure object in the
arbitrary-`c` Brolin construction. -/
noncomputable def brolinLimitOnEscapeDiskData (c : ℂ) :
    { μ : ProbabilityMeasure (escapeDisk c) //
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (fun k => preBrolinProbabilityOnEscapeDisk c (ψ k)) atTop (𝓝 μ) } := by
  classical
  let h := CompactSpace.tendsto_subseq (preBrolinProbabilityOnEscapeDisk c)
  let μ := Classical.choose h
  have hμ :
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (preBrolinProbabilityOnEscapeDisk c ∘ ψ) atTop (𝓝 μ) :=
    Classical.choose_spec h
  let ψ := Classical.choose hμ
  have hψ :
      StrictMono ψ ∧ Tendsto (preBrolinProbabilityOnEscapeDisk c ∘ ψ) atTop (𝓝 μ) :=
    Classical.choose_spec hμ
  exact ⟨μ, ψ, hψ.1, by simpa [Function.comp_def] using hψ.2⟩

/-- The compact-carrier limiting Brolin probability measure. -/
noncomputable def brolinLimitOnEscapeDisk (c : ℂ) : ProbabilityMeasure (escapeDisk c) :=
  (brolinLimitOnEscapeDiskData c).1

/-- The defining subsequential convergence of the compact-carrier limiting
Brolin measure. -/
theorem brolinLimitOnEscapeDisk_spec (c : ℂ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun k => preBrolinProbabilityOnEscapeDisk c (ψ k)) atTop
        (𝓝 (brolinLimitOnEscapeDisk c)) :=
  (brolinLimitOnEscapeDiskData c).2

/-- A named extraction subsequence for the compact-carrier finite Brolin
probabilities. -/
noncomputable def brolinLimitSubsequence (c : ℂ) : ℕ → ℕ :=
  Classical.choose (brolinLimitOnEscapeDisk_spec c)

theorem brolinLimitSubsequence_strictMono (c : ℂ) :
    StrictMono (brolinLimitSubsequence c) :=
  (Classical.choose_spec (brolinLimitOnEscapeDisk_spec c)).1

theorem preBrolinProbabilityOnEscapeDisk_subseq_tendsto (c : ℂ) :
    Tendsto
      (fun k => preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k))
      atTop (𝓝 (brolinLimitOnEscapeDisk c)) :=
  (Classical.choose_spec (brolinLimitOnEscapeDisk_spec c)).2

/-- A strictly increasing self-map of `ℕ` eventually dominates the identity;
in this concrete form it is enough for the Brolin extraction sequence. -/
theorem le_brolinLimitSubsequence (c : ℂ) (k : ℕ) :
    k ≤ brolinLimitSubsequence c k := by
  have hψ := brolinLimitSubsequence_strictMono c
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hlt : brolinLimitSubsequence c k <
          brolinLimitSubsequence c (k + 1) :=
        hψ (Nat.lt_succ_self k)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)

/-- Along the chosen compactness subsequence, every positive Green sublevel
eventually carries the finite plane measures. -/
theorem eventually_preBrolinMeasure_subseq_greenSublevel_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      preBrolinMeasure c (brolinLimitSubsequence c k) (greenSublevel c ε)ᶜ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_critical_le_of_pos c hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact preBrolinMeasure_greenSublevel_compl_of_scaled_critical_le
    c (brolinLimitSubsequence c k)
    (hN (brolinLimitSubsequence c k) (le_trans hk (le_brolinLimitSubsequence c k)))

/-- Along the chosen compactness subsequence, every positive Green sublevel
eventually carries the finite compact-carrier measures. -/
theorem eventually_preBrolinMeasureOnEscapeDisk_subseq_greenSublevel_preimage_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      preBrolinMeasureOnEscapeDisk c (brolinLimitSubsequence c k)
        ((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ) = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_critical_le_of_pos c hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact preBrolinMeasureOnEscapeDisk_greenSublevel_preimage_compl_of_scaled_critical_le
    c (brolinLimitSubsequence c k)
    (hN (brolinLimitSubsequence c k) (le_trans hk (le_brolinLimitSubsequence c k)))

/-- Along the chosen compactness subsequence, finite Riesz functionals vanish
eventually on every test function that vanishes on a positive Green sublevel. -/
theorem eventually_preBrolinRieszFunctional_subseq_eq_zero_of_eq_zero_on_greenSublevel
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    ∀ᶠ k in atTop,
      preBrolinRieszFunctional c (brolinLimitSubsequence c k) φ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_critical_le_of_pos c hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact preBrolinRieszFunctional_eq_zero_of_scaled_critical_le_of_eq_zero_on_greenSublevel
    c (brolinLimitSubsequence c k) φ
    (hN (brolinLimitSubsequence c k) (le_trans hk (le_brolinLimitSubsequence c k))) hφ

/-- The chosen compactness extraction still has indices tending to infinity. -/
theorem brolinLimitSubsequence_tendsto_atTop (c : ℂ) :
    Tendsto (brolinLimitSubsequence c) atTop atTop :=
  (brolinLimitSubsequence_strictMono c).tendsto_atTop

/-- The limiting Brolin measure on the plane, obtained by pushing the compact
escape-disk limit forward along the subtype inclusion. -/
noncomputable def limitingBrolinMeasure (c : ℂ) : Measure ℂ :=
  Measure.map (fun z : escapeDisk c => (z : ℂ))
    (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))

instance instIsProbabilityMeasure_limitingBrolinMeasure (c : ℂ) :
    IsProbabilityMeasure (limitingBrolinMeasure c) := by
  rw [limitingBrolinMeasure]
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

/-- The limiting plane measure is still carried by the same compact escape disk. -/
theorem limitingBrolinMeasure_escapeDisk_compl (c : ℂ) :
    limitingBrolinMeasure c (escapeDisk c)ᶜ = 0 := by
  rw [limitingBrolinMeasure]
  rw [Measure.map_apply measurable_subtype_coe]
  · simp
  · have hclosed : IsClosed (escapeDisk c) := by
      exact (by
        simpa [escapeDisk] using
          (isCompact_closedBall (0 : ℂ) (max 2 ‖c‖)).isClosed)
    exact hclosed.measurableSet.compl

/-- The limiting plane measure is a probability measure carried by the compact
escape disk. -/
theorem limitingBrolinMeasure_isProbOn_escapeDisk (c : ℂ) :
    IsProbOn (limitingBrolinMeasure c) (escapeDisk c) :=
  ⟨instIsProbabilityMeasure_limitingBrolinMeasure c,
    limitingBrolinMeasure_escapeDisk_compl c⟩

/-- The Riesz-Markov positive functional represented by the constructed limiting
Brolin measure.  The remaining GAP-A analytic step is to identify this
functional with `(2π)⁻¹ ΔG_c`. -/
noncomputable def limitingBrolinRieszFunctional (c : ℂ) : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := fun φ => ∫ z, φ z ∂limitingBrolinMeasure c
    map_add' := by
      intro φ ψ
      change ∫ z, φ z + ψ z ∂limitingBrolinMeasure c =
        ∫ z, φ z ∂limitingBrolinMeasure c + ∫ z, ψ z ∂limitingBrolinMeasure c
      rw [integral_add]
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    map_smul' := by
      intro a φ
      change ∫ z, a • φ z ∂limitingBrolinMeasure c =
        a • ∫ z, φ z ∂limitingBrolinMeasure c
      rw [integral_smul]
    monotone' := by
      intro φ ψ hφψ
      apply integral_mono _ _ hφψ
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport }

theorem limitingBrolinRieszFunctional_apply (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    limitingBrolinRieszFunctional c φ =
      ∫ z, φ z ∂limitingBrolinMeasure c := by
  rfl

/-- Plane test integrals against the limiting Brolin measure can be computed on
the compact escape-disk carrier where the limit was constructed. -/
theorem integral_limitingBrolinMeasure_eq_integral_escapeDisk (c : ℂ)
    (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂limitingBrolinMeasure c =
      ∫ z : escapeDisk c, φ (z : ℂ) ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [limitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- Carrier form of the limiting positive functional. -/
theorem limitingBrolinRieszFunctional_apply_escapeDisk (c : ℂ)
    (φ : C_c(ℂ, ℝ)) :
    limitingBrolinRieszFunctional c φ =
      ∫ z : escapeDisk c, φ (z : ℂ) ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [limitingBrolinRieszFunctional_apply,
    integral_limitingBrolinMeasure_eq_integral_escapeDisk]

/-- Restrict a compactly supported plane test function to the compact escape
disk as a bounded continuous test function. -/
noncomputable def compactRestrictionOnEscapeDisk (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z : escapeDisk c => φ (z : ℂ), φ.continuous.comp continuous_subtype_val⟩

/-- The defining compact-carrier subsequential convergence, expressed on the
restricted compactly supported tests used by the Riesz interface. -/
theorem preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    Tendsto
      (fun k =>
        ∫ z : escapeDisk c, φ (z : ℂ)
          ∂(preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ z : escapeDisk c, φ (z : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (compactRestrictionOnEscapeDisk c φ)
  simpa [compactRestrictionOnEscapeDisk] using h

/-- Weak convergence of the chosen finite zero-pullback subsequence to a plane
measure, stated only in the compactly supported test-function language used by
the local Riesz-Markov interface. -/
def IsWeakSubseqLimitOfPreBrolin (c : ℂ) (μ : Measure ℂ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    Tendsto
      (fun k => ∫ z, φ z ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop (𝓝 (∫ z, φ z ∂μ))

/-- Functional version of the same weak-limit contract. -/
def IsWeakSubseqLimitFunctionalOfPreBrolin
    (c : ℂ) (Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    Tendsto
      (fun k => preBrolinRieszFunctional c (brolinLimitSubsequence c k) φ)
      atTop (𝓝 (Λ φ))

/-- Measure weak convergence implies weak convergence of the represented
positive functional. -/
theorem isWeakSubseqLimitFunctionalOfPreBrolin_of_measure
    {c : ℂ} {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    (hμ : IsWeakSubseqLimitOfPreBrolin c μ) :
    IsWeakSubseqLimitFunctionalOfPreBrolin c
      { toFun := fun φ => ∫ z, φ z ∂μ
        map_add' := by
          intro φ ψ
          change ∫ z, φ z + ψ z ∂μ = ∫ z, φ z ∂μ + ∫ z, ψ z ∂μ
          rw [integral_add]
          · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
          · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
        map_smul' := by
          intro a φ
          change ∫ z, a • φ z ∂μ = a • ∫ z, φ z ∂μ
          rw [integral_smul]
        monotone' := by
          intro φ ψ hφψ
          apply integral_mono _ _ hφψ
          · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
          · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport } := by
  intro φ
  exact hμ φ

/-- The compactness-selected plane measure is the weak subsequential limit of
the finite zero-pullback Brolin measures. -/
theorem limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin (c : ℂ) :
    IsWeakSubseqLimitOfPreBrolin c (limitingBrolinMeasure c) := by
  intro φ
  have h := preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto c φ
  rw [integral_limitingBrolinMeasure_eq_integral_escapeDisk]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_preBrolinMeasure_eq_integral_escapeDisk]
  rfl

/-- The represented limiting Riesz functional is the weak limit of the finite
pre-Brolin Riesz functionals. -/
theorem limitingBrolinRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolin
    (c : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolin c (limitingBrolinRieszFunctional c) :=
  isWeakSubseqLimitFunctionalOfPreBrolin_of_measure
    (limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin c)

/-- A weak subsequential limit gives zero mass to every compactly supported
test function that vanishes on a positive Green sublevel.  This is the
test-function support form of the future statement `μ((K_c)ᶜ)=0`. -/
theorem weakSubseqLimit_integral_eq_zero_of_eq_zero_on_greenSublevel
    {c : ℂ} {μ : Measure ℂ} (hμ : IsWeakSubseqLimitOfPreBrolin c μ)
    {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    ∫ z, φ z ∂μ = 0 := by
  have hlim := hμ φ
  have hzero :
      Tendsto
        (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (∫ z, φ z ∂μ)) := by
    exact hlim.congr'
      (eventually_preBrolinRieszFunctional_subseq_eq_zero_of_eq_zero_on_greenSublevel
        c hε φ hφ)
  exact (tendsto_nhds_unique tendsto_const_nhds hzero).symm

/-- Functional weak-limit version of the same Green-sublevel vanishing
criterion. -/
theorem weakSubseqLimitFunctional_eq_zero_of_eq_zero_on_greenSublevel
    {c : ℂ} {Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ}
    (hΛ : IsWeakSubseqLimitFunctionalOfPreBrolin c Λ)
    {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    Λ φ = 0 := by
  have hlim := hΛ φ
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (Λ φ)) := by
    exact hlim.congr'
      (eventually_preBrolinRieszFunctional_subseq_eq_zero_of_eq_zero_on_greenSublevel
        c hε φ hφ)
  exact (tendsto_nhds_unique tendsto_const_nhds hzero).symm

/-- Concrete Green-sublevel vanishing for the constructed limiting measure. -/
theorem limitingBrolinMeasure_integral_eq_zero_of_eq_zero_on_greenSublevel
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    ∫ z, φ z ∂limitingBrolinMeasure c = 0 :=
  weakSubseqLimit_integral_eq_zero_of_eq_zero_on_greenSublevel
    (limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin c) hε φ hφ

/-- Concrete Green-sublevel vanishing for the represented limiting positive
functional. -/
theorem limitingBrolinRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    limitingBrolinRieszFunctional c φ = 0 :=
  weakSubseqLimitFunctional_eq_zero_of_eq_zero_on_greenSublevel
    (limitingBrolinRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolin c) hε φ hφ

/-- The compact-carrier weak limit is carried by every positive Green sublevel,
pulled back to the escape disk. -/
theorem brolinLimitOnEscapeDisk_greenSublevel_preimage_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
      (((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ)) = 0 := by
  let G : Set (escapeDisk c) :=
    ((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ)
  have hGopen : IsOpen G := by
    dsimp [G]
    exact ((isClosed_greenSublevel c ε).isOpen_compl).preimage continuous_subtype_val
  have hle :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c) hGopen
  have hevent :
      ∀ᶠ k in atTop,
        (preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
          Measure (escapeDisk c)) G = 0 := by
    filter_upwards
      [eventually_preBrolinMeasureOnEscapeDisk_subseq_greenSublevel_preimage_compl_of_pos
        c hε] with k hk
    simpa [G, preBrolinProbabilityOnEscapeDisk] using hk
  have htend :
      Tendsto
        (fun k =>
          (preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)) G)
        atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hevent] with k hk
    exact hk.symm
  have hliminf :
      atTop.liminf
        (fun k =>
          (preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)) G) = 0 :=
    htend.liminf_eq
  have hle_zero : (brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) G ≤ 0 := by
    rw [← hliminf]
    exact hle
  have hGzero : (brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) G = 0 :=
    le_antisymm hle_zero bot_le
  simpa [G] using hGzero

/-- The limiting plane measure is carried by every positive Green sublevel. -/
theorem limitingBrolinMeasure_greenSublevel_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    limitingBrolinMeasure c (greenSublevel c ε)ᶜ = 0 := by
  have hmeas : MeasurableSet (greenSublevel c ε)ᶜ :=
    (measurableSet_greenSublevel c ε).compl
  rw [limitingBrolinMeasure, Measure.map_apply measurable_subtype_coe hmeas]
  exact brolinLimitOnEscapeDisk_greenSublevel_preimage_compl_of_pos c hε

/-- The complement of `K_c` is the union of complements of the positive Green
sublevels with levels `(n+1)⁻¹`. -/
theorem filledJulia_compl_eq_iUnion_greenSublevel_inv_nat_succ_compl (c : ℂ) :
    (filledJulia c)ᶜ =
      ⋃ n : ℕ, (greenSublevel c (((n + 1 : ℕ) : ℝ)⁻¹))ᶜ := by
  ext z
  constructor
  · intro hz
    have hznot : z ∉ filledJulia c := by
      simpa using hz
    have hGne : greenFunctionDyn c z ≠ 0 := by
      intro hzero
      exact hznot ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
    have hGpos : 0 < greenFunctionDyn c z :=
      lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / greenFunctionDyn c z)
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    rw [Set.mem_compl_iff, mem_greenSublevel_iff]
    have hN' : 1 / greenFunctionDyn c z < ((N + 1 : ℕ) : ℝ) :=
      lt_trans hN (by exact_mod_cast Nat.lt_succ_self N)
    have hden : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
    have hsmall : (((N + 1 : ℕ) : ℝ)⁻¹) < greenFunctionDyn c z := by
      simpa [one_div] using (one_div_lt hden hGpos).2 hN'
    exact not_le_of_gt hsmall
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨N, hN⟩
    rw [Set.mem_compl_iff]
    intro hK
    apply hN
    rw [mem_greenSublevel_iff, (greenFunctionDyn_eq_zero_iff c z).mpr hK]
    positivity

/-- The constructed limiting measure is carried by the filled Julia set. -/
theorem limitingBrolinMeasure_filledJulia_compl (c : ℂ) :
    limitingBrolinMeasure c (filledJulia c)ᶜ = 0 := by
  rw [filledJulia_compl_eq_iUnion_greenSublevel_inv_nat_succ_compl c]
  apply measure_iUnion_null
  intro n
  exact limitingBrolinMeasure_greenSublevel_compl_of_pos c (by positivity)

/-- The constructed limiting measure is a probability measure on `K_c`. -/
theorem limitingBrolinMeasure_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (limitingBrolinMeasure c) (filledJulia c) :=
  ⟨instIsProbabilityMeasure_limitingBrolinMeasure c,
    limitingBrolinMeasure_filledJulia_compl c⟩

/-- A globally continuous truncation of the logarithmic kernel singular at `z`.
For `δ ≤ ‖z - w‖` it agrees with `logKernel z w`. -/
noncomputable def truncatedLogKernel (z : ℂ) (δ : ℝ) (w : ℂ) : ℝ :=
  - Real.log (max δ ‖z - w‖)

theorem continuous_truncatedLogKernel {z : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun w : ℂ => truncatedLogKernel z δ w) := by
  unfold truncatedLogKernel
  have hcont : Continuous fun w : ℂ => max δ ‖z - w‖ :=
    continuous_const.max ((continuous_const.sub continuous_id).norm)
  exact (hcont.log fun w =>
    ne_of_gt (lt_of_lt_of_le hδ (le_max_left δ ‖z - w‖))).neg

theorem truncatedLogKernel_eq_logKernel_of_le_norm
    {z w : ℂ} {δ : ℝ} (hδw : δ ≤ ‖z - w‖) :
    truncatedLogKernel z δ w = logKernel z w := by
  unfold truncatedLogKernel logKernel
  rw [max_eq_right hδw]

/-- Away from its singularity, the truncated logarithmic kernel is below the
true logarithmic kernel. -/
theorem truncatedLogKernel_le_logKernel_of_ne
    {z w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hzw : z ≠ w) :
    truncatedLogKernel z δ w ≤ logKernel z w := by
  unfold truncatedLogKernel logKernel
  have hnorm : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hmax : 0 < max δ ‖z - w‖ := lt_of_lt_of_le hδ (le_max_left _ _)
  have hlog := Real.log_le_log hnorm (le_max_right δ ‖z - w‖)
  exact neg_le_neg hlog

/-- Decreasing the truncation radius increases the truncated logarithmic
kernel. -/
theorem truncatedLogKernel_mono_of_le
    (z w : ℂ) {η δ : ℝ} (hη : 0 < η) (hηδ : η ≤ δ) :
    truncatedLogKernel z δ w ≤ truncatedLogKernel z η w := by
  unfold truncatedLogKernel
  have hmaxη : 0 < max η ‖z - w‖ := lt_of_lt_of_le hη (le_max_left _ _)
  have hmax_le : max η ‖z - w‖ ≤ max δ ‖z - w‖ :=
    max_le_max hηδ le_rfl
  exact neg_le_neg (Real.log_le_log hmaxη hmax_le)

/-- For truncation radii at most one, the truncated kernel is absolutely
dominated by the true kernel away from the singularity. -/
theorem norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
    {z w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) (hzw : z ≠ w) :
    ‖truncatedLogKernel z δ w‖ ≤ ‖logKernel z w‖ := by
  by_cases hle : δ ≤ ‖z - w‖
  · rw [truncatedLogKernel_eq_logKernel_of_le_norm hle]
  · rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hlt : ‖z - w‖ < δ := lt_of_not_ge hle
    have hnormpos : 0 < ‖z - w‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
    have htrunc_nonneg : 0 ≤ truncatedLogKernel z δ w := by
      unfold truncatedLogKernel
      have hmax : max δ ‖z - w‖ = δ := max_eq_left hlt.le
      rw [hmax]
      exact neg_nonneg.mpr (Real.log_nonpos hδ.le hδle)
    have hkernel_nonneg : 0 ≤ logKernel z w := by
      unfold logKernel
      exact neg_nonneg.mpr
        (Real.log_nonpos hnormpos.le (le_trans hlt.le hδle))
    rw [abs_of_nonneg htrunc_nonneg, abs_of_nonneg hkernel_nonneg]
    exact truncatedLogKernel_le_logKernel_of_ne hδ hzw

/-- The standard `1/(n+1)` truncations converge pointwise to the true
logarithmic kernel away from the singularity. -/
theorem truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
    {z w : ℂ} (hzw : z ≠ w) :
    Tendsto
      (fun n : ℕ =>
        truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w)
      atTop (𝓝 (logKernel z w)) := by
  have hnorm : 0 < ‖z - w‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - w‖)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNle : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ n
  have hlarge : 1 / ‖z - w‖ < ((n + 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le hN (le_trans hNle hnle)
  have hdenpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ ‖z - w‖ := by
    rw [inv_eq_one_div]
    exact ((one_div_lt hdenpos hnorm).2 hlarge).le
  exact (truncatedLogKernel_eq_logKernel_of_le_norm hδle).symm

/-- The filled Julia set lies in the same fixed escape disk that carries all
finite zero-pullback measures. -/
theorem mem_escapeDisk_of_mem_filledJulia {c z : ℂ}
    (hz : z ∈ filledJulia c) :
    z ∈ escapeDisk c := by
  simpa [escapeDisk] using filledJulia_subset_closedBall c hz

/-- Two points in the fixed escape disk are separated by at most its diameter. -/
theorem norm_sub_le_escapeDisk_diameter {c z w : ℂ}
    (hz : z ∈ escapeDisk c) (hw : w ∈ escapeDisk c) :
    ‖z - w‖ ≤ 2 * max 2 ‖c‖ := by
  have hzle : ‖z‖ ≤ max 2 ‖c‖ := by
    simpa [escapeDisk, Metric.mem_closedBall, dist_zero_right] using hz
  have hwle : ‖w‖ ≤ max 2 ‖c‖ := by
    simpa [escapeDisk, Metric.mem_closedBall, dist_zero_right] using hw
  calc
    ‖z - w‖ ≤ ‖z‖ + ‖w‖ := by simpa using norm_sub_le z w
    _ ≤ max 2 ‖c‖ + max 2 ‖c‖ := add_le_add hzle hwle
    _ = 2 * max 2 ‖c‖ := by ring

/-- On the fixed escape disk, every positive logarithmic truncation has a
uniform lower bound coming only from the disk diameter. -/
theorem truncatedLogKernel_escapeDisk_lower_bound
    {c z w : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : z ∈ escapeDisk c) (hw : w ∈ escapeDisk c) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤ truncatedLogKernel z δ w := by
  unfold truncatedLogKernel
  have hdist : ‖z - w‖ ≤ 2 * max 2 ‖c‖ :=
    norm_sub_le_escapeDisk_diameter hz hw
  have hmax :
      max δ ‖z - w‖ ≤ max δ (2 * max 2 ‖c‖) :=
    max_le_max le_rfl hdist
  have hpos : 0 < max δ ‖z - w‖ :=
    lt_of_lt_of_le hδ (le_max_left _ _)
  exact neg_le_neg (Real.log_le_log hpos hmax)

/-- On the fixed escape disk, the true logarithmic kernel has the same
diameter lower bound.  At the diagonal the convention `log 0 = 0` is harmless
because the diameter is at least one. -/
theorem logKernel_escapeDisk_lower_bound
    {c z w : ℂ} (hz : z ∈ escapeDisk c) (hw : w ∈ escapeDisk c) :
    - Real.log (2 * max 2 ‖c‖) ≤ logKernel z w := by
  unfold logKernel
  by_cases hzw : z - w = 0
  · rw [hzw, norm_zero, Real.log_zero, neg_zero]
    have hdiam_ge_one : (1 : ℝ) ≤ 2 * max 2 ‖c‖ := by
      have hmax_ge_one : (1 : ℝ) ≤ max 2 ‖c‖ := by
        exact le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_left 2 ‖c‖)
      nlinarith
    have hlog_nonneg : 0 ≤ Real.log (2 * max 2 ‖c‖) :=
      Real.log_nonneg hdiam_ge_one
    linarith
  · have hdist : ‖z - w‖ ≤ 2 * max 2 ‖c‖ :=
      norm_sub_le_escapeDisk_diameter hz hw
    have hdistpos : 0 < ‖z - w‖ := norm_pos_iff.mpr hzw
    exact neg_le_neg (Real.log_le_log hdistpos hdist)

/-- Any probability measure carried by `K_c` has logarithmic potential bounded
below at every evaluation point in the fixed escape disk.  This is the
carrier-only lower half of the boundary potential estimates. -/
theorem logPotential_lower_bound_of_isProbOn_filledJulia_of_mem_escapeDisk
    {c z : ℂ} {μ : Measure ℂ}
    (hμ : IsProbOn μ (filledJulia c)) (hz : z ∈ escapeDisk c) :
    - Real.log (2 * max 2 ‖c‖) ≤ logPotential μ z := by
  let A : ℝ := - Real.log (2 * max 2 ‖c‖)
  haveI : IsProbabilityMeasure μ := hμ.1
  have hCge : (1 : ℝ) ≤ 2 * max 2 ‖c‖ := by
    have hmax_ge_one : (1 : ℝ) ≤ max 2 ‖c‖ := by
      exact le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_left 2 ‖c‖)
    nlinarith
  by_cases hint : Integrable (fun w => logKernel z w) μ
  · have hconst : Integrable (fun _ : ℂ => A) μ := integrable_const A
    have hmem : ∀ᵐ w ∂μ, w ∈ filledJulia c := (mem_ae_iff).2 hμ.2
    have hmono :
        (fun _ : ℂ => A) ≤ᵐ[μ] fun w => logKernel z w := by
      filter_upwards [hmem] with w hwK
      dsimp [A]
      exact logKernel_escapeDisk_lower_bound hz
        (mem_escapeDisk_of_mem_filledJulia hwK)
    have hle := integral_mono_ae hconst hint hmono
    simpa [A, logPotential] using hle
  · have hzero : logPotential μ z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]
    exact neg_nonpos.mpr (Real.log_nonneg hCge)

/-- Finite truncated-kernel integrals are bounded above by the true finite
pre-Brolin potential whenever the evaluation point is not a level-`n` atom. -/
theorem integral_truncatedLogKernel_preBrolinMeasure_le_logPotential_of_iterate_ne_zero
    {c z : ℂ} {δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hz : (quadratic c)^[n] z ≠ 0) :
    ∫ w, truncatedLogKernel z δ w ∂preBrolinMeasure c n ≤
      logPotential (preBrolinMeasure c n) z := by
  rw [integral_preBrolinMeasure_eq_root_average,
    logPotential_preBrolinMeasure_eq_scaled_rootLogKernelSum]
  have hsum :
      (((quadraticPolyIterate c n).roots.map
          (fun w => truncatedLogKernel z δ w)).sum) ≤
        (((quadraticPolyIterate c n).roots.map
          (fun w => logKernel z w)).sum) := by
    suffices hsum' : ∀ s : Multiset ℂ,
        (∀ w ∈ s, truncatedLogKernel z δ w ≤ logKernel z w) →
          (s.map (fun w => truncatedLogKernel z δ w)).sum ≤
            (s.map (fun w => logKernel z w)).sum by
      apply hsum'
      intro w hw
      have hzw : z ≠ w := by
        intro h
        have hwroot : (quadraticPolyIterate c n).IsRoot w :=
          (Polynomial.mem_roots (quadraticPolyIterate_monic c n).ne_zero).mp hw
        have hiter : (quadratic c)^[n] w = 0 := by
          simpa [Polynomial.IsRoot.def, quadraticPolyIterate_eval] using hwroot
        exact hz (by rwa [h])
      exact truncatedLogKernel_le_logKernel_of_ne hδ hzw
    intro s
    induction s using Multiset.induction_on with
    | empty =>
        intro _h
        simp
    | cons a s ih =>
        intro h
        have ha : truncatedLogKernel z δ a ≤ logKernel z a := h a (by simp)
        have hs : ∀ w ∈ s, truncatedLogKernel z δ w ≤ logKernel z w := by
          intro w hw
          exact h w (by simp [hw])
        simpa using add_le_add ha (ih hs)
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The truncated kernel restricted to the compact escape disk, in the bounded
continuous-function form required by weak convergence of probability measures. -/
noncomputable def truncatedLogKernelOnEscapeDisk
    (c z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ),
      (continuous_truncatedLogKernel (z := z) hδ).comp continuous_subtype_val⟩

/-- Finite pre-Brolin integrals of the truncated kernel can be computed on the
compact escape-disk carrier. -/
theorem integral_truncatedLogKernel_preBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, truncatedLogKernel z δ w ∂preBrolinMeasure c n =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
        ∂preBrolinMeasureOnEscapeDisk c n := by
  rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable

/-- Limiting Brolin integrals of the truncated kernel can be computed on the
compact escape-disk carrier. -/
theorem integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
        ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [limitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable

/-- The compact-carrier finite measures converge on the truncated logarithmic
kernel. -/
theorem truncatedLogKernel_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedLogKernelOnEscapeDisk c z δ hδ)
  simpa [truncatedLogKernelOnEscapeDisk] using h

/-- The plane finite measures converge on the truncated logarithmic kernel to
the constructed limiting Brolin measure. -/
theorem truncatedLogKernel_preBrolinMeasure_subseq_integral_tendsto_limiting
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop
      (𝓝 (∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c)) := by
  have h :=
    truncatedLogKernel_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
      c z hδ
  rw [integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedLogKernel_preBrolinMeasure_eq_integral_escapeDisk c z hδ]
  rfl

/-- Limiting truncated-kernel integrals are bounded below by the fixed
escape-disk diameter whenever the evaluation point is in that disk. -/
theorem integral_truncatedLogKernel_limitingBrolinMeasure_escapeDisk_lower_bound
    (c : ℂ) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : z ∈ escapeDisk c) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
      ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c := by
  rw [integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  let A : ℝ := - Real.log (max δ (2 * max 2 ‖c‖))
  let μK : Measure (escapeDisk c) := (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
  haveI : IsProbabilityMeasure μK := by
    dsimp [μK]
    infer_instance
  have hconst : Integrable (fun _ : escapeDisk c => A) μK :=
    integrable_const A
  have hfun :
      Integrable (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) μK := by
    simpa [truncatedLogKernelOnEscapeDisk, μK] using
      (truncatedLogKernelOnEscapeDisk c z δ hδ).integrable μK
  have hmono :
      (fun _ : escapeDisk c => A) ≤
        (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) := by
    intro w
    exact truncatedLogKernel_escapeDisk_lower_bound hδ hz w.2
  have hle := integral_mono hconst hfun hmono
  simpa [A, μK] using hle

/-- Pointwise lower bound that isolates the logarithmic contribution of a
candidate atom at the evaluation point inside the compact escape-disk carrier. -/
theorem truncatedLogKernel_escapeDisk_atom_lower_bound
    (c : ℂ) {z : ℂ} (hz : z ∈ escapeDisk c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (w : escapeDisk c) :
    let zz : escapeDisk c := ⟨z, hz⟩
    let C : ℝ := 2 * max 2 ‖c‖
    let A : ℝ := - Real.log δ
    let B : ℝ := - Real.log C
    B + (A - B) * ({zz} : Set (escapeDisk c)).indicator (fun _ => (1 : ℝ)) w ≤
      truncatedLogKernel z δ (w : ℂ) := by
  intro zz C A B
  have hCge : 1 ≤ C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hδC : δ ≤ C := le_trans hδle hCge
  have hmaxC : max δ C = C := max_eq_right hδC
  by_cases hw : w = zz
  · subst w
    have hzz : (zz : ℂ) = z := rfl
    simp [truncatedLogKernel, A, B, hzz, hδ.le]
  · have hnot : w ∉ ({zz} : Set (escapeDisk c)) := by
      simpa using hw
    have hlower :=
      truncatedLogKernel_escapeDisk_lower_bound (c := c) (z := z) (w := (w : ℂ))
        hδ hz w.2
    rw [hmaxC] at hlower
    simpa [A, B, C, Set.indicator_of_notMem hnot] using hlower

/-- If `ε < G_c(z)`, then the Green sublevel `{G_c ≤ ε}` stays a positive
Euclidean distance from `z`. -/
theorem exists_pos_le_norm_of_greenSublevel_of_lt_green
    {c z : ℂ} {ε : ℝ} (hεz : ε < greenFunctionDyn c z) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖ := by
  have hopen : IsOpen {w : ℂ | ε < greenFunctionDyn c w} :=
    isOpen_lt continuous_const (continuous_greenFunctionDyn c)
  obtain ⟨δ, hδpos, hδsub⟩ := (Metric.isOpen_iff.mp hopen) z hεz
  refine ⟨δ, hδpos, ?_⟩
  intro w hw
  by_contra hnot
  have hlt : ‖z - w‖ < δ := lt_of_not_ge hnot
  have hball : w ∈ Metric.ball z δ := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hlt
  have hgt : ε < greenFunctionDyn c w := hδsub hball
  exact not_lt_of_ge hw hgt

/-- A measure carried by a Green sublevel separated from `z` has true log
potential equal to the truncated-kernel integral at `z`. -/
theorem logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support
    {c z : ℂ} {μ : Measure ℂ} {ε δ : ℝ}
    (hμ : μ (greenSublevel c ε)ᶜ = 0)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    logPotential μ z = ∫ w, truncatedLogKernel z δ w ∂μ := by
  unfold logPotential
  refine integral_congr_ae ?_
  have hmem : ∀ᵐ w ∂μ, w ∈ greenSublevel c ε := by
    exact (mem_ae_iff).2 hμ
  filter_upwards [hmem] with w hw
  exact (truncatedLogKernel_eq_logKernel_of_le_norm (hsep w hw)).symm

/-- Along the selected subsequence, finite log potentials equal the truncated
kernel integral once the finite measures are carried by the separating sublevel. -/
theorem eventually_logPotential_preBrolinMeasure_subseq_eq_integral_truncatedLogKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z =
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasure c (brolinLimitSubsequence c k) := by
  filter_upwards [eventually_preBrolinMeasure_subseq_greenSublevel_compl_of_pos
    c hε] with k hk
  exact logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support hk hsep

/-- The constructed limiting measure has true log potential equal to the
truncated-kernel integral whenever the chosen sublevel separates it from `z`. -/
theorem logPotential_limitingBrolinMeasure_eq_integral_truncatedLogKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    logPotential (limitingBrolinMeasure c) z =
      ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c :=
  logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support
    (limitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hsep

/-- The logarithmic-potential part of weak convergence at points of the basin.
It is stated separately because the kernel has a logarithmic singularity and
needs its own proof, distinct from compactly supported continuous tests. -/
def HasSubseqLogPotentialLimit (c : ℂ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto
      (fun k => - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
      atTop (𝓝 (- logPotential μ z))

/-- The constructed limiting Brolin measure satisfies the logarithmic-potential
weak limit on the whole basin.  The singular logarithmic kernel is removed by
separating the basin point from a positive Green sublevel and using the
truncated-kernel weak convergence proved above. -/
theorem limitingBrolinMeasure_hasSubseqLogPotentialLimit (c : ℂ) :
    HasSubseqLogPotentialLimit c (limitingBrolinMeasure c) := by
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
    truncatedLogKernel_preBrolinMeasure_subseq_integral_tendsto_limiting
      c z hδpos
  have hlim :=
    logPotential_limitingBrolinMeasure_eq_integral_truncatedLogKernel
      c z hεpos hsep
  have hevent :=
    eventually_logPotential_preBrolinMeasure_subseq_eq_integral_truncatedLogKernel
      c z hεpos hsep
  have hlog :
      Tendsto
        (fun k => logPotential
          (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
        atTop (𝓝 (logPotential (limitingBrolinMeasure c) z)) := by
    rw [hlim]
    exact htrunc.congr' (by
      filter_upwards [hevent] with k hk
      exact hk.symm)
  simpa using hlog.neg

end Bottcher
