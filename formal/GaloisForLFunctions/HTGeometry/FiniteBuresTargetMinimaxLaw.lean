import GaloisForLFunctions.HTGeometry.FiniteBuresReporterVariationalLaw
import GaloisForLFunctions.HTGeometry.FiniteBuresTargetMinimaxCore
import GaloisForLFunctions.HTGeometry.BuresPositiveReporterIncidenceLaw

/-!
# Exact finite Bures target minimax law

This module identifies the abstract finite-target Sion exchange with Bures
root fidelity.  Every target law is an actual probability mixture of occupied
rank-one rays, singular source and target matrices are allowed, and the target
maximum is attained on the compact simplex.
-/

open Matrix Set
open MeasureTheory
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem finiteBuresMixtureValue_eq_rootFidelity
    {C : Type*} [Fintype C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) {p : C → ℝ}
    (hp : p ∈ stdSimplex ℝ C) :
    finiteBuresMixtureValue source target p =
      finiteBuresRootFidelity source (finiteBuresTargetMixture p target) := by
  have hsets : finiteBuresReporterValueSet source target p =
      {q : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℂ,
        A.PosDef ∧
          q = finiteBuresReporterHalfSum source
            (finiteBuresTargetMixture p target) A} := by
    ext q
    constructor
    · rintro ⟨A, hA, rfl⟩
      refine ⟨A, hA, ?_⟩
      simpa [finiteBuresReporterHalfSum, finiteBuresSourcePairing,
        finiteBuresTargetPairing] using
        finiteBuresSaddleValue_eq_halfSum_mixture source target p A
    · rintro ⟨A, hA, rfl⟩
      refine ⟨A, hA, ?_⟩
      simpa [finiteBuresReporterHalfSum, finiteBuresSourcePairing,
        finiteBuresTargetPairing] using
        (finiteBuresSaddleValue_eq_halfSum_mixture source target p A).symm
  unfold finiteBuresMixtureValue
  rw [hsets]
  change finiteBuresReporterHalfSumCapacity source
      (finiteBuresTargetMixture p target) = _
  exact finiteBuresReporterHalfSumCapacity_eq_rootFidelity hsource
    (finiteBuresTargetMixture_posSemidef hp target)

theorem continuousOn_finiteBuresMixtureRootFidelity
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    ContinuousOn
      (fun p : C → ℝ =>
        finiteBuresRootFidelity source (finiteBuresTargetMixture p target))
      (stdSimplex ℝ C) := by
  have hroot := continuousOn_finiteBuresRootFidelity_right source
  have hmix := continuous_finiteBuresTargetMixture target
  have hmaps : MapsTo (fun p : C → ℝ => finiteBuresTargetMixture p target)
      (stdSimplex ℝ C)
      {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef} := by
    intro p hp
    exact finiteBuresTargetMixture_posSemidef hp target
  exact hroot.comp hmix.continuousOn hmaps

theorem finiteBuresMixtureValueSet_eq_rootFidelitySet
    {C : Type*} [Fintype C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    finiteBuresMixtureValueSet source target =
      {q : ℝ | ∃ p ∈ stdSimplex ℝ C,
        q = finiteBuresRootFidelity source
          (finiteBuresTargetMixture p target)} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, finiteBuresMixtureValue_eq_rootFidelity hsource target hp⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, (finiteBuresMixtureValue_eq_rootFidelity hsource target hp).symm⟩

/-- The dual Bures optimum is attained by an actual probability mixture of
the occupied rays. -/
theorem exists_finiteBuresDualCapacity_maximizer
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    ∃ p ∈ stdSimplex ℝ C,
      finiteBuresDualCapacity source target =
        finiteBuresRootFidelity source
          (finiteBuresTargetMixture p target) := by
  let objective : (C → ℝ) → ℝ := fun p =>
    finiteBuresRootFidelity source (finiteBuresTargetMixture p target)
  have hcompact : IsCompact (stdSimplex ℝ C) := isCompact_stdSimplex ℝ C
  have hnonempty : (stdSimplex ℝ C).Nonempty := by
    classical
    let c : C := Classical.choice inferInstance
    exact ⟨Pi.single c 1, single_mem_stdSimplex ℝ c⟩
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    (continuousOn_finiteBuresMixtureRootFidelity source target)
  refine ⟨p, hp, ?_⟩
  have hset := finiteBuresMixtureValueSet_eq_rootFidelitySet hsource target
  have hlub : IsLUB (finiteBuresMixtureValueSet source target) (objective p) := by
    rw [hset]
    simpa [objective, eq_comm] using hmax.isLUB hp
  unfold finiteBuresDualCapacity
  exact (isLUB_csSup (finiteBuresMixtureValueSet_nonempty source target)
    (finiteBuresMixtureValueSet_bddAbove hsource target)).unique hlub

/-- **Exact finite Bures target minimax law.**  The best additive reporter
against the complete occupied-target maximum equals the largest Bures root
fidelity against a probability mixture of the occupied rays. -/
theorem finiteBuresHalfSumTargetMinimax
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    sInf {q : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℂ,
      A.PosDef ∧
        q = (finiteBuresSourcePairing source A +
          finiteBuresTargetMaximum A target) / 2} =
      sSup {q : ℝ | ∃ p ∈ stdSimplex ℝ C,
        q = finiteBuresRootFidelity source
          (finiteBuresTargetMixture p target)} := by
  calc
    _ = finiteBuresPrimalCapacity source target :=
      (finiteBuresPrimalCapacity_eq_halfSumMaximumInfimum source target).symm
    _ = finiteBuresDualCapacity source target :=
      finiteBuresPrimalCapacity_eq_dualCapacity hsource target
    _ = _ := by
      unfold finiteBuresDualCapacity
      rw [finiteBuresMixtureValueSet_eq_rootFidelitySet hsource target]

/-- **Exact product-form finite Bures target minimax law.**  The complete
occupied-target reporter product equals the square of the largest Bures root
fidelity over every probability mixture of the occupied target rays. -/
theorem finiteBuresProductTargetMinimax
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    finiteBuresProductCapacity source target =
      sSup {q : ℝ | ∃ p ∈ stdSimplex ℝ C,
        q = finiteBuresRootFidelity source
          (finiteBuresTargetMixture p target)} ^ (2 : ℕ) := by
  rw [finiteBuresProductCapacity_eq_dualCapacity_sq hsource target]
  unfold finiteBuresDualCapacity
  rw [finiteBuresMixtureValueSet_eq_rootFidelitySet hsource target]

/-- The product-form optimum has an actual maximizing probability mixture;
no relaxed or finitely additive target law is introduced. -/
theorem exists_finiteBuresProductCapacity_maximizer
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    ∃ p ∈ stdSimplex ℝ C,
      finiteBuresProductCapacity source target =
        finiteBuresRootFidelity source
          (finiteBuresTargetMixture p target) ^ (2 : ℕ) := by
  obtain ⟨p, hp, hmax⟩ :=
    exists_finiteBuresDualCapacity_maximizer hsource target
  refine ⟨p, hp, ?_⟩
  rw [finiteBuresProductCapacity_eq_dualCapacity_sq hsource target, hmax]

/-- The incidence capacity from the complete-union coarea law is definitionally
the product capacity in the Bures minimax problem, up to commutation of its two
real factors. -/
theorem finitePositiveReporterIncidenceCapacity_eq_finiteBuresProductCapacity
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    finitePositiveReporterIncidenceCapacity source target =
      finiteBuresProductCapacity source target := by
  unfold finitePositiveReporterIncidenceCapacity finiteBuresProductCapacity
    finiteBuresProductMaximumValueSet
  congr 1
  ext q
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨A, hA, ?_⟩
    simp only [finitePositiveReporterTargetMaximum,
      finitePositiveReporterTargetLeverage, finiteBuresTargetMaximum,
      finiteBuresTargetLeverage, finiteBuresSourcePairing]
    rw [mul_comm]
  · rintro ⟨A, hA, rfl⟩
    refine ⟨A, hA, ?_⟩
    simp only [finitePositiveReporterTargetMaximum,
      finitePositiveReporterTargetLeverage, finiteBuresTargetMaximum,
      finiteBuresTargetLeverage, finiteBuresSourcePairing]
    rw [mul_comm]

/-- **Complete-incidence Bures minimax law.**  A complete finite target union
is controlled without a target-count union bound by one compact probability
mixture of the occupied target rays. -/
theorem finiteBures_completeIncidence_minimax_bound
    {X C : Type*} [MeasurableSpace X]
    [Fintype C] [Nonempty C] {n : ℕ}
    (mu : Measure X) [MeasureTheory.IsFiniteMeasure mu]
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu) :
    threshold * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
      sSup {q : ℝ | ∃ p ∈ stdSimplex ℝ C,
        q = finiteBuresRootFidelity
          (finitePositiveReporterSourceCovariance mu state)
          (finiteBuresTargetMixture p target)} ^ (2 : ℕ) := by
  have hsource := finitePositiveReporterSourceCovariance_posSemidef
    mu state hprod
  calc
    threshold * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
        finitePositiveReporterIncidenceCapacity
          (finitePositiveReporterSourceCovariance mu state) target :=
      finitePositiveReporter_completeIncidence_capacity_bound
        mu target state threshold hthreshold hprod
    _ = finiteBuresProductCapacity
        (finitePositiveReporterSourceCovariance mu state) target :=
      finitePositiveReporterIncidenceCapacity_eq_finiteBuresProductCapacity
        (finitePositiveReporterSourceCovariance mu state) target
    _ = _ := finiteBuresProductTargetMinimax hsource target

/-- **Return-excised complete-incidence Bures minimax law.**  Return mass is
paid once.  Every surviving source point retains its restricted-measure weight,
and the residual complete target union is governed by the exact Bures mixture
capacity of the restricted covariance. -/
theorem finiteBures_returnExcisedIncidence_minimax_bound
    {X C : Type*} [MeasurableSpace X]
    [Fintype C] [Nonempty C] {n : ℕ}
    (mu : Measure X) [MeasureTheory.IsFiniteMeasure mu]
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j))
        (mu.restrict returnSetᶜ)) :
    mu.real (finitePositiveReporterCaptureEvent target state threshold) ≤
      mu.real returnSet +
        sSup {q : ℝ | ∃ p ∈ stdSimplex ℝ C,
          q = finiteBuresRootFidelity
            (finitePositiveReporterSourceCovariance
              (mu.restrict returnSetᶜ) state)
            (finiteBuresTargetMixture p target)} ^ (2 : ℕ) / threshold := by
  let nu : Measure X := mu.restrict returnSetᶜ
  let E : Set X := finitePositiveReporterCaptureEvent target state threshold
  have hresidualScaled := finiteBures_completeIncidence_minimax_bound
    nu target state threshold hthreshold hprod
  have hresidual :
      nu.real E ≤
        sSup {q : ℝ | ∃ p ∈ stdSimplex ℝ C,
          q = finiteBuresRootFidelity
            (finitePositiveReporterSourceCovariance nu state)
            (finiteBuresTargetMixture p target)} ^ (2 : ℕ) / threshold := by
    apply (le_div_iff₀' hthreshold).2
    simpa [E, mul_comm] using hresidualScaled
  have hcut := measureReal_le_return_add_restrict_compl
    mu E returnSet hreturn
  exact hcut.trans (by
    simpa [E, nu] using add_le_add_left hresidual (mu.real returnSet))

end

end GaloisForLFunctions.HTGeometry
