import GaloisForLFunctions.RHTower.JointAncestryActualThetaGradeNormEscape
import GaloisForLFunctions.RHTower.DeningerTwoPrimeKummerDenseNonclosedRange
import GaloisForLFunctions.HTGeometry.SourceLinearClosedRelationSplitting

/-!
# JAS actual-theta closed unbounded grade synthesis

The bounded actual-grade synthesis obstruction has an exact positive survivor. Reciprocal actual
theta-grade norms form a bounded, nonzero null sequence. Its diagonal multiplier is injective with
dense nonclosed range. Inverting that multiplier and following the canonical normalized
prime-grade isometry gives a closed densely defined single-valued relation whose value on every
prime coordinate is the literal actual theta-weighted critical prime packet.

The domain is nonclosed and no bounded operator realizes the same coordinate law, so this is a
genuinely unbounded completion. It closes the coefficient-faithful actual-grade synthesis step,
not the still-missing RFHM support-cutting source-linear sewing needed for the Xi endpoint.
-/

open scoped InnerProductSpace
open Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

abbrev JASPrimeEllTwo := HTGeometry.IndexedEllTwo Nat.Primes

abbrev JASActualThetaPacketHilbert (t : ℝ) :=
  L2Amplification ℕ (JASCriticalPrimePoissonL2 t)

def jasActualThetaGradeWeight (p : Nat.Primes) : ℝ :=
  ‖jointAncestryCompletedThetaGradeL2 (natEquivPrimes.symm p)‖

def jasActualThetaClosedSynthesisScale : ℝ :=
  min 1 (Real.sqrt jasActualThetaPositiveIntervalMass)

theorem jasActualThetaClosedSynthesisScale_pos :
    0 < jasActualThetaClosedSynthesisScale := by
  exact lt_min (by norm_num)
    (Real.sqrt_pos.2 jasActualThetaPositiveIntervalMass_pos)

theorem jasActualThetaGradeWeight_pos (p : Nat.Primes) :
    0 < jasActualThetaGradeWeight p := by
  rw [jasActualThetaGradeWeight, norm_pos_iff]
  exact jointAncestryCompletedThetaGradeL2_ne_zero _

theorem jasActualThetaClosedSynthesisScale_le_weight (p : Nat.Primes) :
    jasActualThetaClosedSynthesisScale ≤ jasActualThetaGradeWeight p := by
  let r := natEquivPrimes.symm p
  have hsqrt : jasActualThetaClosedSynthesisScale ≤
      Real.sqrt jasActualThetaPositiveIntervalMass :=
    min_le_right _ _
  have hexp : 1 ≤ Real.exp (r : ℝ) :=
    Real.one_le_exp (by positivity)
  have hsqrtNonneg : 0 ≤ Real.sqrt jasActualThetaPositiveIntervalMass :=
    Real.sqrt_nonneg _
  calc
    jasActualThetaClosedSynthesisScale ≤
        Real.sqrt jasActualThetaPositiveIntervalMass := hsqrt
    _ ≤ Real.exp (r : ℝ) * Real.sqrt jasActualThetaPositiveIntervalMass := by
      nlinarith
    _ ≤ jasActualThetaGradeWeight p := by
      exact exp_mul_sqrt_jasActualThetaPositiveIntervalMass_le_norm r

def jasActualThetaReciprocalMultiplier (p : Nat.Primes) : ℂ :=
  ((jasActualThetaClosedSynthesisScale / jasActualThetaGradeWeight p : ℝ) : ℂ)

theorem norm_jasActualThetaReciprocalMultiplier_le_one (p : Nat.Primes) :
    ‖jasActualThetaReciprocalMultiplier p‖ ≤ 1 := by
  rw [jasActualThetaReciprocalMultiplier, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg jasActualThetaClosedSynthesisScale_pos.le
      (jasActualThetaGradeWeight_pos p).le)]
  exact (div_le_one (jasActualThetaGradeWeight_pos p)).2
    (jasActualThetaClosedSynthesisScale_le_weight p)

theorem jasActualThetaReciprocalMultiplier_ne_zero (p : Nat.Primes) :
    jasActualThetaReciprocalMultiplier p ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr
    (div_ne_zero jasActualThetaClosedSynthesisScale_pos.ne'
      (jasActualThetaGradeWeight_pos p).ne')

def jasActualThetaReciprocalOperator : JASPrimeEllTwo →L[ℂ] JASPrimeEllTwo :=
  deningerMultiplier norm_jasActualThetaReciprocalMultiplier_le_one

theorem jasActualThetaReciprocalOperator_injective :
    Function.Injective jasActualThetaReciprocalOperator :=
  deningerMultiplier_injective norm_jasActualThetaReciprocalMultiplier_le_one
    jasActualThetaReciprocalMultiplier_ne_zero

theorem jasActualThetaReciprocalOperator_denseRange :
    DenseRange jasActualThetaReciprocalOperator :=
  deningerMultiplier_denseRange_of_ne_zero
    norm_jasActualThetaReciprocalMultiplier_le_one
    jasActualThetaReciprocalMultiplier_ne_zero

theorem tendsto_jasActualThetaReciprocalMultiplier_natEquivPrimes :
    Tendsto (fun n : ℕ => jasActualThetaReciprocalMultiplier (natEquivPrimes n))
      atTop (nhds 0) := by
  have hreal : Tendsto (fun n : ℕ =>
      jasActualThetaClosedSynthesisScale /
        ‖jointAncestryCompletedThetaGradeL2 n‖) atTop (nhds 0) :=
    tendsto_norm_jointAncestryCompletedThetaGradeL2_atTop.const_div_atTop _
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  convert hcomplex using 1
  · funext n
    simp [jasActualThetaReciprocalMultiplier, jasActualThetaGradeWeight]
  · simp

theorem jasActualThetaReciprocalOperator_not_isClosed_range :
    ¬ IsClosed (Set.range jasActualThetaReciprocalOperator) := by
  exact deningerMultiplier_not_isClosed_range_of_weights_tendsto_zero
    norm_jasActualThetaReciprocalMultiplier_le_one
    jasActualThetaReciprocalMultiplier_ne_zero natEquivPrimes
    tendsto_jasActualThetaReciprocalMultiplier_natEquivPrimes

def jasActualThetaNormalizedSynthesisIsometry (t : ℝ) :
    JASPrimeEllTwo →ₗᵢ[ℂ] JASActualThetaPacketHilbert t :=
  (orthonormal_jointAncestryCriticalPrimeInjectiveGradePacket t).orthogonalFamily.linearIsometry

theorem jasActualThetaNormalizedSynthesisIsometry_coordinateBasis
    (t : ℝ) (p : Nat.Primes) :
    jasActualThetaNormalizedSynthesisIsometry t
        (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) =
      jointAncestryCriticalPrimeInjectiveGradePacket t p := by
  change jointAncestryCriticalPrimeInjectiveGradeSynthesis t
      (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) =
    jointAncestryCriticalPrimeInjectiveGradePacket t p
  exact jointAncestryCriticalPrimeInjectiveGradeSynthesis_coordinateBasis t p

def jasActualThetaClosedGradeFirstEquation (t : ℝ) :
    HilbertSum JASPrimeEllTwo (JASActualThetaPacketHilbert t) →L[ℂ] JASPrimeEllTwo :=
  (((jasActualThetaClosedSynthesisScale : ℂ) • hilbertSumFst) -
    jasActualThetaReciprocalOperator.comp
      ((jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap.adjoint.comp
        hilbertSumSnd))

def jasActualThetaClosedGradeRangeEquation (t : ℝ) :
    HilbertSum JASPrimeEllTwo (JASActualThetaPacketHilbert t) →L[ℂ]
      JASActualThetaPacketHilbert t :=
  ((jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap.comp
      ((jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap.adjoint.comp
        hilbertSumSnd)) - hilbertSumSnd

def jasActualThetaClosedGradeSynthesisRelation (t : ℝ) :
    Submodule ℂ (HilbertSum JASPrimeEllTwo (JASActualThetaPacketHilbert t)) :=
  LinearMap.ker (jasActualThetaClosedGradeFirstEquation t).toLinearMap ⊓
    LinearMap.ker (jasActualThetaClosedGradeRangeEquation t).toLinearMap

theorem mem_jasActualThetaClosedGradeSynthesisRelation_iff
    (t : ℝ) (z : HilbertSum JASPrimeEllTwo (JASActualThetaPacketHilbert t)) :
    z ∈ jasActualThetaClosedGradeSynthesisRelation t ↔
      (jasActualThetaClosedSynthesisScale : ℂ) • hilbertSumFst z =
        jasActualThetaReciprocalOperator
          ((jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap.adjoint
            (hilbertSumSnd z)) ∧
      (jasActualThetaNormalizedSynthesisIsometry t)
          ((jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap.adjoint
            (hilbertSumSnd z)) = hilbertSumSnd z := by
  simp only [jasActualThetaClosedGradeSynthesisRelation, Submodule.mem_inf,
    LinearMap.mem_ker, jasActualThetaClosedGradeFirstEquation,
    jasActualThetaClosedGradeRangeEquation, ContinuousLinearMap.coe_coe,
    sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, sub_eq_zero]
  rfl

theorem isClosed_jasActualThetaClosedGradeSynthesisRelation (t : ℝ) :
    IsClosed (jasActualThetaClosedGradeSynthesisRelation t :
      Set (HilbertSum JASPrimeEllTwo (JASActualThetaPacketHilbert t))) := by
  exact (ContinuousLinearMap.isClosed_ker
      (jasActualThetaClosedGradeFirstEquation t)).inter
    (ContinuousLinearMap.isClosed_ker (jasActualThetaClosedGradeRangeEquation t))

theorem adjoint_jasActualThetaNormalizedSynthesisIsometry_apply
    (t : ℝ) (x : JASPrimeEllTwo) :
    (jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap.adjoint
        (jasActualThetaNormalizedSynthesisIsometry t x) = x := by
  change (jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap.adjoint
    ((jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap x) = x
  have h := DFunLike.congr_fun
    (jasActualThetaNormalizedSynthesisIsometry t).adjoint_comp_self x
  simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    one_apply_eq_self] using h

theorem jasActualThetaClosedGrade_graph_mem
    (t : ℝ) (x : JASPrimeEllTwo) :
    hilbertSumInl (jasActualThetaReciprocalOperator x) +
        hilbertSumInr
          ((jasActualThetaClosedSynthesisScale : ℂ) •
            jasActualThetaNormalizedSynthesisIsometry t x) ∈
      jasActualThetaClosedGradeSynthesisRelation t := by
  rw [mem_jasActualThetaClosedGradeSynthesisRelation_iff]
  simp only [map_add, hilbertSumFst_inl, hilbertSumFst_inr,
    hilbertSumSnd_inl, hilbertSumSnd_inr, add_zero, zero_add]
  constructor
  · rw [map_smul, adjoint_jasActualThetaNormalizedSynthesisIsometry_apply,
      map_smul]
  · rw [map_smul, adjoint_jasActualThetaNormalizedSynthesisIsometry_apply,
      map_smul]

theorem jasActualThetaReciprocalOperator_map_smul
    (c : ℂ) (x : JASPrimeEllTwo) :
    jasActualThetaReciprocalOperator (c • x) =
      c • jasActualThetaReciprocalOperator x :=
  map_smul jasActualThetaReciprocalOperator c x

theorem jasActualThetaReciprocalOperator_range_subset_relationDomain (t : ℝ) :
    Set.range jasActualThetaReciprocalOperator ⊆
      (hilbertRelationDomain (jasActualThetaClosedGradeSynthesisRelation t) :
        Set JASPrimeEllTwo) := by
  rintro u ⟨x, rfl⟩
  change jasActualThetaReciprocalOperator x ∈
    Submodule.map hilbertSumFst.toLinearMap
      (jasActualThetaClosedGradeSynthesisRelation t)
  refine ⟨hilbertSumInl (jasActualThetaReciprocalOperator x) +
      hilbertSumInr
        ((jasActualThetaClosedSynthesisScale : ℂ) •
          jasActualThetaNormalizedSynthesisIsometry t x),
    jasActualThetaClosedGrade_graph_mem t x, ?_⟩
  change hilbertSumFst
      (hilbertSumInl (jasActualThetaReciprocalOperator x) +
        hilbertSumInr
          ((jasActualThetaClosedSynthesisScale : ℂ) •
            jasActualThetaNormalizedSynthesisIsometry t x)) =
    jasActualThetaReciprocalOperator x
  rw [map_add, hilbertSumFst_inl, hilbertSumFst_inr, add_zero]

theorem dense_jasActualThetaClosedGradeSynthesisRelation_domain (t : ℝ) :
    Dense (hilbertRelationDomain (jasActualThetaClosedGradeSynthesisRelation t) :
      Set JASPrimeEllTwo) :=
  jasActualThetaReciprocalOperator_denseRange.mono
    (jasActualThetaReciprocalOperator_range_subset_relationDomain t)

theorem jasActualThetaClosedGradeSynthesisRelation_domain_eq_range (t : ℝ) :
    (hilbertRelationDomain (jasActualThetaClosedGradeSynthesisRelation t) :
        Set JASPrimeEllTwo) = Set.range jasActualThetaReciprocalOperator := by
  apply Set.Subset.antisymm
  · intro u hu
    change u ∈ Submodule.map hilbertSumFst.toLinearMap
      (jasActualThetaClosedGradeSynthesisRelation t) at hu
    rcases hu with ⟨z, hz, hzu⟩
    have hfirst :=
      (mem_jasActualThetaClosedGradeSynthesisRelation_iff t z).mp hz |>.1
    change hilbertSumFst z = u at hzu
    refine ⟨((jasActualThetaClosedSynthesisScale : ℂ)⁻¹ •
      (jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap.adjoint
        (hilbertSumSnd z)), ?_⟩
    have hc : (jasActualThetaClosedSynthesisScale : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr jasActualThetaClosedSynthesisScale_pos.ne'
    calc
      jasActualThetaReciprocalOperator
          ((jasActualThetaClosedSynthesisScale : ℂ)⁻¹ •
            (jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap.adjoint
              (hilbertSumSnd z)) =
          (jasActualThetaClosedSynthesisScale : ℂ)⁻¹ •
            jasActualThetaReciprocalOperator
              ((jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap.adjoint
                (hilbertSumSnd z)) :=
        jasActualThetaReciprocalOperator_map_smul _ _
      _ = (jasActualThetaClosedSynthesisScale : ℂ)⁻¹ •
          ((jasActualThetaClosedSynthesisScale : ℂ) • hilbertSumFst z) :=
        congrArg (fun v : JASPrimeEllTwo =>
          (jasActualThetaClosedSynthesisScale : ℂ)⁻¹ • v) hfirst.symm
      _ = hilbertSumFst z := inv_smul_smul₀ hc _
      _ = u := hzu
  · exact jasActualThetaReciprocalOperator_range_subset_relationDomain t

theorem not_isClosed_jasActualThetaClosedGradeSynthesisRelation_domain (t : ℝ) :
    ¬ IsClosed (hilbertRelationDomain (jasActualThetaClosedGradeSynthesisRelation t) :
      Set JASPrimeEllTwo) := by
  rw [jasActualThetaClosedGradeSynthesisRelation_domain_eq_range]
  exact jasActualThetaReciprocalOperator_not_isClosed_range

theorem jasActualThetaClosedGradeSynthesisRelation_singleValued (t : ℝ) :
    HilbertRelationSingleValued (jasActualThetaClosedGradeSynthesisRelation t) := by
  intro y hy
  have h := (mem_jasActualThetaClosedGradeSynthesisRelation_iff t
    (hilbertSumInr y)).mp hy
  simp only [hilbertSumFst_inr, hilbertSumSnd_inr, smul_zero] at h
  have hadjZero :
      (jasActualThetaNormalizedSynthesisIsometry t).toContinuousLinearMap.adjoint y = 0 := by
    apply jasActualThetaReciprocalOperator_injective
    simpa using h.1.symm
  have hy := h.2
  rw [hadjZero] at hy
  have hzero : (0 : JASActualThetaPacketHilbert t) = y := by
    simpa using hy
  exact hzero.symm

theorem jasActualThetaReciprocalMultiplier_mul_weight (p : Nat.Primes) :
    jasActualThetaReciprocalMultiplier p * (jasActualThetaGradeWeight p : ℂ) =
      (jasActualThetaClosedSynthesisScale : ℂ) := by
  rw [jasActualThetaReciprocalMultiplier]
  norm_cast
  exact div_mul_cancel₀ _ (jasActualThetaGradeWeight_pos p).ne'

theorem jasActualThetaReciprocalOperator_weight_smul_coordinateBasis
    (p : Nat.Primes) :
    jasActualThetaReciprocalOperator
        ((jasActualThetaGradeWeight p : ℂ) •
          HTGeometry.ellTwoCoordinateBasis Nat.Primes p) =
      (jasActualThetaClosedSynthesisScale : ℂ) •
        HTGeometry.ellTwoCoordinateBasis Nat.Primes p := by
  apply lp.ext
  funext q
  rw [jasActualThetaReciprocalOperator, deningerMultiplier_apply]
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hqp : q = p
  · subst q
    simpa [HTGeometry.ellTwoCoordinateBasis_apply, lp.single_apply] using
      jasActualThetaReciprocalMultiplier_mul_weight p
  · simp [HTGeometry.ellTwoCoordinateBasis_apply, lp.single_apply, hqp]

theorem jointAncestryCriticalPrimeActualThetaInjectiveGradePacket_eq_weight_smul
    (t : ℝ) (p : Nat.Primes) :
    jointAncestryCriticalPrimeActualThetaInjectiveGradePacket t p =
      (jasActualThetaGradeWeight p : ℂ) •
        jasActualThetaNormalizedSynthesisIsometry t
          (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) := by
  rw [jasActualThetaNormalizedSynthesisIsometry_coordinateBasis]
  change l2Single (natEquivPrimes.symm p)
      ((jasActualThetaGradeWeight p : ℂ) • criticalPrimeSingletonCharacterL2 t p) =
    (jasActualThetaGradeWeight p : ℂ) •
      l2Single (natEquivPrimes.symm p) (criticalPrimeSingletonCharacterL2 t p)
  rw [map_smul]

theorem jasActualThetaClosedGradeSynthesisRelation_coordinate_mem
    (t : ℝ) (p : Nat.Primes) :
    hilbertSumInl (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) +
        hilbertSumInr
          (jointAncestryCriticalPrimeActualThetaInjectiveGradePacket t p) ∈
      jasActualThetaClosedGradeSynthesisRelation t := by
  rw [jointAncestryCriticalPrimeActualThetaInjectiveGradePacket_eq_weight_smul,
    mem_jasActualThetaClosedGradeSynthesisRelation_iff]
  simp only [map_add, hilbertSumFst_inl, hilbertSumFst_inr,
    hilbertSumSnd_inl, hilbertSumSnd_inr, add_zero, zero_add]
  rw [map_smul, adjoint_jasActualThetaNormalizedSynthesisIsometry_apply]
  constructor
  · exact (jasActualThetaReciprocalOperator_weight_smul_coordinateBasis p).symm
  · rw [map_smul]

/-- Canonical actual theta weights admit an exact closed densely defined single-valued synthesis
relation, but no bounded synthesis operator. -/
theorem jasActualThetaClosedUnboundedGradeSynthesis (t : ℝ) :
    IsClosed (jasActualThetaClosedGradeSynthesisRelation t :
      Set (HilbertSum JASPrimeEllTwo (JASActualThetaPacketHilbert t))) ∧
    Dense (hilbertRelationDomain (jasActualThetaClosedGradeSynthesisRelation t) :
      Set JASPrimeEllTwo) ∧
    ¬ IsClosed (hilbertRelationDomain (jasActualThetaClosedGradeSynthesisRelation t) :
      Set JASPrimeEllTwo) ∧
    HilbertRelationSingleValued (jasActualThetaClosedGradeSynthesisRelation t) ∧
    (∀ p, hilbertSumInl (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) +
        hilbertSumInr
          (jointAncestryCriticalPrimeActualThetaInjectiveGradePacket t p) ∈
      jasActualThetaClosedGradeSynthesisRelation t) ∧
    ¬ JASCriticalPrimeActualThetaInjectiveGradeSynthesis t := by
  exact ⟨isClosed_jasActualThetaClosedGradeSynthesisRelation t,
    dense_jasActualThetaClosedGradeSynthesisRelation_domain t,
    not_isClosed_jasActualThetaClosedGradeSynthesisRelation_domain t,
    jasActualThetaClosedGradeSynthesisRelation_singleValued t,
    jasActualThetaClosedGradeSynthesisRelation_coordinate_mem t,
    not_JASCriticalPrimeActualThetaInjectiveGradeSynthesis t⟩

end

end RHTower
