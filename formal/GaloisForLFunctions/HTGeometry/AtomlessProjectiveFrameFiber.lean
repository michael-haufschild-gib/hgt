import GaloisForLFunctions.HTGeometry.ProjectiveFiniteConstraintCarrierAperture
import GaloisForLFunctions.HTGeometry.CauchyJetFrame
import GaloisForLFunctions.HTGeometry.CofinalCholeskySelection
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory OnePoint Complex
open scoped ENNReal OnePoint Topology BoundedContinuousFunction
noncomputable section
variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

noncomputable def leafCayleyMomentContinuousMap (n : ℕ) : C(OnePoint ℝ, ℂ) :=
  ⟨fun t => cayleyMoment (F.leaf t : Measure ℝ) n,
    (continuous_cayleyMoment n).comp F.continuous_leaf⟩

noncomputable def leafCayleyMomentReBCF (n : ℕ) : OnePoint ℝ →ᵇ ℝ :=
  ContinuousMap.linearIsometryBoundedOfCompact (OnePoint ℝ) ℝ ℝ
    ⟨fun t => (leafCayleyMomentContinuousMap F n t).re,
      Complex.continuous_re.comp (leafCayleyMomentContinuousMap F n).continuous⟩

noncomputable def leafCayleyMomentImBCF (n : ℕ) : OnePoint ℝ →ᵇ ℝ :=
  ContinuousMap.linearIsometryBoundedOfCompact (OnePoint ℝ) ℝ ℝ
    ⟨fun t => (leafCayleyMomentContinuousMap F n t).im,
      Complex.continuous_im.comp (leafCayleyMomentContinuousMap F n).continuous⟩

@[simp] theorem leafCayleyMomentReBCF_apply (n : ℕ) (t : OnePoint ℝ) :
    leafCayleyMomentReBCF F n t = (cayleyMoment (F.leaf t : Measure ℝ) n).re := rfl

@[simp] theorem leafCayleyMomentImBCF_apply (n : ℕ) (t : OnePoint ℝ) :
    leafCayleyMomentImBCF F n t = (cayleyMoment (F.leaf t : Measure ℝ) n).im := rfl

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory OnePoint Complex
open scoped ENNReal OnePoint Topology BoundedContinuousFunction
noncomputable section
variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]

noncomputable def boundaryCayleyConstraintL1 (N : ℕ) : Fin (N + N) → Lp ℝ 1 eta :=
  Fin.append
    (fun i => BoundedContinuousFunction.toLp 1 eta ℝ (leafCayleyMomentReBCF F (i + 1)))
    (fun i => BoundedContinuousFunction.toLp 1 eta ℝ (leafCayleyMomentImBCF F (i + 1)))

@[simp] theorem boundaryCayleyConstraintL1_castAdd (N : ℕ) (i : Fin N) :
    boundaryCayleyConstraintL1 F eta N (Fin.castAdd N i) =
      BoundedContinuousFunction.toLp 1 eta ℝ (leafCayleyMomentReBCF F (i + 1)) := by
  simp [boundaryCayleyConstraintL1]

@[simp] theorem boundaryCayleyConstraintL1_natAdd (N : ℕ) (i : Fin N) :
    boundaryCayleyConstraintL1 F eta N (Fin.natAdd N i) =
      BoundedContinuousFunction.toLp 1 eta ℝ (leafCayleyMomentImBCF F (i + 1)) := by
  exact Fin.append_right _ _ i

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory OnePoint Complex
open scoped ENNReal OnePoint Topology BoundedContinuousFunction
noncomputable section
variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]

theorem linftyDensityMeasure_linftyOne :
    linftyDensityMeasure eta (linftyOne eta) = eta := by
  rw [linftyDensityMeasure]
  calc
    eta.withDensity (fun x => ENNReal.ofReal (⇑(linftyOne eta) x)) =
        eta.withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [Lp.coeFn_const ⊤ eta (1 : ℝ)] with x hx
      change ENNReal.ofReal (⇑(Lp.const ⊤ eta (1 : ℝ)) x) = 1
      rw [hx]
      norm_num
    _ = eta := withDensity_one

theorem weightedBoundaryCarrier_linftyOne :
    weightedBoundaryCarrier F eta (linftyOne eta) =
      boundaryBarycenter eta (fun t => (F.leaf t : Measure ℝ)) := by
  rw [weightedBoundaryCarrier, linftyDensityMeasure_linftyOne]

theorem linftyOne_strictlyPositive : LinftyStrictlyPositive eta (linftyOne eta) := by
  filter_upwards [Lp.coeFn_const ⊤ eta (1 : ℝ)] with x hx
  change 0 < ⇑(Lp.const ⊤ eta (1 : ℝ)) x
  rw [hx]
  norm_num

noncomputable def boundaryCayleyMomentReCLM (n : ℕ) : (Lp ℝ ⊤ eta) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing eta 1 ⊤)
    (BoundedContinuousFunction.toLp 1 eta ℝ (leafCayleyMomentReBCF F n))

noncomputable def boundaryCayleyMomentImCLM (n : ℕ) : (Lp ℝ ⊤ eta) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing eta 1 ⊤)
    (BoundedContinuousFunction.toLp 1 eta ℝ (leafCayleyMomentImBCF F n))

 theorem boundaryCayleyMomentReCLM_eq_weightedCarrier
    (w : Lp ℝ ⊤ eta) (hw : LinftyStrictlyPositive eta w)
    (hint : ∫ t, w t ∂eta = 1) (n : ℕ) :
    boundaryCayleyMomentReCLM F eta n w =
      (cayleyMoment (weightedBoundaryCarrier F eta w) n).re := by
  letI : IsProbabilityMeasure (linftyDensityMeasure eta w) :=
    linftyDensityMeasure_isProbabilityMeasure eta w hw hint
  letI (t : OnePoint ℝ) : IsProbabilityMeasure (F.leaf t : Measure ℝ) := (F.leaf t).prop
  letI : IsProbabilityMeasure (weightedBoundaryCarrier F eta w) := by
    dsimp only [weightedBoundaryCarrier]
    exact boundaryBarycenter_isProbabilityMeasure (linftyDensityMeasure eta w)
      (fun t => (F.leaf t : Measure ℝ)) F.measurable_leaf (fun t => (F.leaf t).prop)
  rw [boundaryCayleyMomentReCLM, ContinuousLinearMap.lpPairing_eq_integral]
  trans ∫ t, leafCayleyMomentReBCF F n t * w t ∂eta
  · apply integral_congr_ae
    filter_upwards [BoundedContinuousFunction.coeFn_toLp 1 eta ℝ
      (leafCayleyMomentReBCF F n)] with t ht
    rw [ht]
    rfl
  · rw [cayleyMoment]
    have hpow : Integrable (fun x : ℝ => realCayley x ^ n)
        (weightedBoundaryCarrier F eta w) :=
      (cayleyPowerBCF n).integrable (weightedBoundaryCarrier F eta w)
    have hre := integral_re hpow
    change (∫ x, (realCayley x ^ n).re ∂weightedBoundaryCarrier F eta w) =
      (∫ x, realCayley x ^ n ∂weightedBoundaryCarrier F eta w).re at hre
    rw [← hre]
    rw [weightedBoundaryCarrier, boundaryBarycenter, integral_bind_real
      (linftyDensityMeasure eta w) (fun t => (F.leaf t : Measure ℝ))
      (fun x => (realCayley x ^ n).re) F.measurable_leaf
      (cayleyPowerReBCF n).continuous.measurable]
    · rw [linftyDensityMeasure]
      have hmeas : AEMeasurable (fun t => ENNReal.ofReal (w t)) eta :=
        (Lp.memLp w).1.aemeasurable.ennreal_ofReal
      rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [hw] with t ht
      rw [ENNReal.toReal_ofReal ht.le]
      rw [leafCayleyMomentReBCF_apply]
      have hleaf : Integrable (fun x : ℝ => realCayley x ^ n) (F.leaf t : Measure ℝ) :=
        (cayleyPowerBCF n).integrable (F.leaf t : Measure ℝ)
      rw [cayleyMoment]
      have hreleaf := integral_re hleaf
      change (∫ x, (realCayley x ^ n).re ∂(F.leaf t : Measure ℝ)) =
        (∫ x, realCayley x ^ n ∂(F.leaf t : Measure ℝ)).re at hreleaf
      rw [← hreleaf]
      simp [smul_eq_mul, mul_comm]
    · exact (cayleyPowerReBCF n).integrable (weightedBoundaryCarrier F eta w)

theorem boundaryCayleyMomentImCLM_eq_weightedCarrier
    (w : Lp ℝ ⊤ eta) (hw : LinftyStrictlyPositive eta w)
    (hint : ∫ t, w t ∂eta = 1) (n : ℕ) :
    boundaryCayleyMomentImCLM F eta n w =
      (cayleyMoment (weightedBoundaryCarrier F eta w) n).im := by
  letI : IsProbabilityMeasure (linftyDensityMeasure eta w) :=
    linftyDensityMeasure_isProbabilityMeasure eta w hw hint
  letI (t : OnePoint ℝ) : IsProbabilityMeasure (F.leaf t : Measure ℝ) := (F.leaf t).prop
  letI : IsProbabilityMeasure (weightedBoundaryCarrier F eta w) := by
    dsimp only [weightedBoundaryCarrier]
    exact boundaryBarycenter_isProbabilityMeasure (linftyDensityMeasure eta w)
      (fun t => (F.leaf t : Measure ℝ)) F.measurable_leaf (fun t => (F.leaf t).prop)
  rw [boundaryCayleyMomentImCLM, ContinuousLinearMap.lpPairing_eq_integral]
  trans ∫ t, leafCayleyMomentImBCF F n t * w t ∂eta
  · apply integral_congr_ae
    filter_upwards [BoundedContinuousFunction.coeFn_toLp 1 eta ℝ
      (leafCayleyMomentImBCF F n)] with t ht
    rw [ht]
    rfl
  · rw [cayleyMoment]
    have hpow : Integrable (fun x : ℝ => realCayley x ^ n)
        (weightedBoundaryCarrier F eta w) :=
      (cayleyPowerBCF n).integrable (weightedBoundaryCarrier F eta w)
    have him := integral_im hpow
    change (∫ x, (realCayley x ^ n).im ∂weightedBoundaryCarrier F eta w) =
      (∫ x, realCayley x ^ n ∂weightedBoundaryCarrier F eta w).im at him
    rw [← him]
    rw [weightedBoundaryCarrier, boundaryBarycenter, integral_bind_real
      (linftyDensityMeasure eta w) (fun t => (F.leaf t : Measure ℝ))
      (fun x => (realCayley x ^ n).im) F.measurable_leaf
      (cayleyPowerImBCF n).continuous.measurable]
    · rw [linftyDensityMeasure]
      have hmeas : AEMeasurable (fun t => ENNReal.ofReal (w t)) eta :=
        (Lp.memLp w).1.aemeasurable.ennreal_ofReal
      rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [hw] with t ht
      rw [ENNReal.toReal_ofReal ht.le]
      rw [leafCayleyMomentImBCF_apply]
      have hleaf : Integrable (fun x : ℝ => realCayley x ^ n) (F.leaf t : Measure ℝ) :=
        (cayleyPowerBCF n).integrable (F.leaf t : Measure ℝ)
      rw [cayleyMoment]
      have himleaf := integral_im hleaf
      change (∫ x, (realCayley x ^ n).im ∂(F.leaf t : Measure ℝ)) =
        (∫ x, realCayley x ^ n ∂(F.leaf t : Measure ℝ)).im at himleaf
      rw [← himleaf]
      simp [smul_eq_mul, mul_comm]
    · exact (cayleyPowerImBCF n).integrable (weightedBoundaryCarrier F eta w)

theorem normalizedCayleyConstraint_castAdd_succ
    (N : ℕ) (w : Lp ℝ ⊤ eta) (i : Fin N) :
    normalizedLinftyL1ConstraintOperator eta (boundaryCayleyConstraintL1 F eta N) w
        (Fin.castAdd N i).succ = boundaryCayleyMomentReCLM F eta (i + 1) w := by
  simp [normalizedLinftyL1ConstraintOperator, linftyL1ConstraintOperator,
    boundaryCayleyConstraintL1, boundaryCayleyMomentReCLM]

theorem normalizedCayleyConstraint_natAdd_succ
    (N : ℕ) (w : Lp ℝ ⊤ eta) (i : Fin N) :
    normalizedLinftyL1ConstraintOperator eta (boundaryCayleyConstraintL1 F eta N) w
        (Fin.natAdd N i).succ = boundaryCayleyMomentImCLM F eta (i + 1) w := by
  change ((ContinuousLinearMap.mul ℝ ℝ).lpPairing eta 1 ⊤
    (boundaryCayleyConstraintL1 F eta N (Fin.natAdd N i))) w = _
  rw [boundaryCayleyConstraintL1_natAdd]
  rfl

theorem cayleyMoment_prefix_eq_of_normalizedCayleyConstraint_eq
    (N : ℕ) {w u : Lp ℝ ⊤ eta}
    (hw : LinftyStrictlyPositive eta w) (hu : LinftyStrictlyPositive eta u)
    (hwint : ∫ t, w t ∂eta = 1) (huint : ∫ t, u t ∂eta = 1)
    (hconstraint :
      normalizedLinftyL1ConstraintOperator eta (boundaryCayleyConstraintL1 F eta N) w =
        normalizedLinftyL1ConstraintOperator eta (boundaryCayleyConstraintL1 F eta N) u) :
    ∀ n ≤ N, cayleyMoment (weightedBoundaryCarrier F eta w) n =
      cayleyMoment (weightedBoundaryCarrier F eta u) n := by
  intro n hn
  cases n with
  | zero =>
      letI : IsProbabilityMeasure (linftyDensityMeasure eta w) :=
        linftyDensityMeasure_isProbabilityMeasure eta w hw hwint
      letI : IsProbabilityMeasure (linftyDensityMeasure eta u) :=
        linftyDensityMeasure_isProbabilityMeasure eta u hu huint
      letI (t : OnePoint ℝ) : IsProbabilityMeasure (F.leaf t : Measure ℝ) := (F.leaf t).prop
      letI : IsProbabilityMeasure (weightedBoundaryCarrier F eta w) := by
        exact boundaryBarycenter_isProbabilityMeasure _ _ F.measurable_leaf (fun t => (F.leaf t).prop)
      letI : IsProbabilityMeasure (weightedBoundaryCarrier F eta u) := by
        exact boundaryBarycenter_isProbabilityMeasure _ _ F.measurable_leaf (fun t => (F.leaf t).prop)
      simp [cayleyMoment]
  | succ m =>
      have hm : m < N := Nat.lt_of_succ_le hn
      let i : Fin N := ⟨m, hm⟩
      apply Complex.ext
      · have hre := congrFun hconstraint (Fin.castAdd N i).succ
        rw [normalizedCayleyConstraint_castAdd_succ,
          normalizedCayleyConstraint_castAdd_succ,
          boundaryCayleyMomentReCLM_eq_weightedCarrier F eta w hw hwint,
          boundaryCayleyMomentReCLM_eq_weightedCarrier F eta u hu huint] at hre
        simpa [i] using hre
      · have him := congrFun hconstraint (Fin.natAdd N i).succ
        rw [normalizedCayleyConstraint_natAdd_succ,
          normalizedCayleyConstraint_natAdd_succ,
          boundaryCayleyMomentImCLM_eq_weightedCarrier F eta w hw hwint,
          boundaryCayleyMomentImCLM_eq_weightedCarrier F eta u hu huint] at him
        simpa [i] using him

theorem gram_and_cauchyJet_eq_of_normalizedCayleyConstraint_eq
    (N : ℕ) {w u : Lp ℝ ⊤ eta}
    (hw : LinftyStrictlyPositive eta w) (hu : LinftyStrictlyPositive eta u)
    (hwint : ∫ t, w t ∂eta = 1) (huint : ∫ t, u t ∂eta = 1)
    (hconstraint :
      normalizedLinftyL1ConstraintOperator eta (boundaryCayleyConstraintL1 F eta N) w =
        normalizedLinftyL1ConstraintOperator eta (boundaryCayleyConstraintL1 F eta N) u) :
    circleToeplitzGram N (cayleyMomentZ (weightedBoundaryCarrier F eta w)) =
        circleToeplitzGram N (cayleyMomentZ (weightedBoundaryCarrier F eta u)) ∧
      ∀ n < N,
        iteratedDeriv n (resolventTransform (weightedBoundaryCarrier F eta w)) (-I) =
          iteratedDeriv n (resolventTransform (weightedBoundaryCarrier F eta u)) (-I) := by
  letI : IsProbabilityMeasure (linftyDensityMeasure eta w) :=
    linftyDensityMeasure_isProbabilityMeasure eta w hw hwint
  letI : IsProbabilityMeasure (linftyDensityMeasure eta u) :=
    linftyDensityMeasure_isProbabilityMeasure eta u hu huint
  letI (t : OnePoint ℝ) : IsProbabilityMeasure (F.leaf t : Measure ℝ) := (F.leaf t).prop
  letI : IsProbabilityMeasure (weightedBoundaryCarrier F eta w) := by
    exact boundaryBarycenter_isProbabilityMeasure _ _ F.measurable_leaf (fun t => (F.leaf t).prop)
  letI : IsProbabilityMeasure (weightedBoundaryCarrier F eta u) := by
    exact boundaryBarycenter_isProbabilityMeasure _ _ F.measurable_leaf (fun t => (F.leaf t).prop)
  have hpref := cayleyMoment_prefix_eq_of_normalizedCayleyConstraint_eq
    F eta N hw hu hwint huint hconstraint
  exact ⟨(circleToeplitzGram_cayleyMomentZ_eq_iff _ _ N).2 hpref,
    (cayleyMoment_prefix_iff_cauchyJet_prefix _ _ N).1 hpref⟩

/-- **Atomless projective Hilbert-cube frame fiber.** Every finite Cayley--Toeplitz frame fiber
through a Nevanlinna boundary barycenter contains a closed topologically embedded Hilbert cube of
distinct positive carriers.  Every carrier in the cube has the common complete Hamburger moment
sequence and measure class, the same level-`N` Gram section, and the same regular Cauchy jet through
order `N-1`. -/
theorem exists_closedEmbeddedHilbertCube_in_exactCayleyFrameFiber
    [NoAtoms eta] (N : ℕ) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ v : ℕ → Lp ℝ ⊤ eta,
      ∃ carrier : SignedHilbertCube → ProbabilityMeasure ℝ,
      Topology.IsClosedEmbedding
          (affinePositiveHilbertCubeMap (linftyOne eta) delta v) ∧
      Topology.IsClosedEmbedding carrier ∧
      (∀ t, (carrier t : Measure ℝ) = weightedBoundaryCarrier F eta
        (affinePositiveHilbertCubeMap (linftyOne eta) delta v t)) ∧
      ∀ t,
        LinftyStrictlyPositive eta
          (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) ∧
        HasHamburgerMoments s (carrier t : Measure ℝ) ∧
        ((carrier t : Measure ℝ) ≪
            boundaryBarycenter eta (fun q => (F.leaf q : Measure ℝ)) ∧
          boundaryBarycenter eta (fun q => (F.leaf q : Measure ℝ)) ≪
            (carrier t : Measure ℝ)) ∧
        circleToeplitzGram N (cayleyMomentZ (carrier t : Measure ℝ)) =
          circleToeplitzGram N (cayleyMomentZ
            (boundaryBarycenter eta (fun q => (F.leaf q : Measure ℝ)))) ∧
        ∀ n < N,
          iteratedDeriv n (resolventTransform (carrier t : Measure ℝ)) (-I) =
            iteratedDeriv n
              (resolventTransform
                (boundaryBarycenter eta (fun q => (F.leaf q : Measure ℝ)))) (-I) := by
  obtain ⟨v, _ell, _hvnorm, _hbio, hwembed, hall, carrier, hcembed, hcarrier⟩ :=
    exists_positiveHilbertCube_weightedBoundaryCarriers F eta
      (boundaryCayleyConstraintL1 F eta N) hdelta0 hdelta1
  have hbaseint : ∫ x, ⇑(linftyOne eta) x ∂eta = 1 := by
    rw [← linftyIntegralCLM_apply]
    exact linftyIntegralCLM_linftyOne eta
  refine ⟨v, carrier, hwembed, hcembed, hcarrier, ?_⟩
  intro t
  have hframe := gram_and_cauchyJet_eq_of_normalizedCayleyConstraint_eq F eta N
    (hall t).2.1 (linftyOne_strictlyPositive eta)
    (by
      rw [← linftyIntegralCLM_apply]
      have hzero := congrFun (hall t).1 (0 : Fin (N + N + 1))
      rw [normalizedLinftyL1ConstraintOperator_zero,
        normalizedLinftyL1ConstraintOperator_zero, linftyIntegralCLM_linftyOne] at hzero
      exact hzero)
    hbaseint (hall t).1
  have hac := weightedBoundaryCarrier_mutuallyAbsolutelyContinuous F eta (hall t).2.1
  rw [hcarrier t]
  rw [weightedBoundaryCarrier_linftyOne F eta] at hframe
  exact ⟨(hall t).2.1, (hall t).2.2, hac, hframe⟩

/-- **Infinite-support projective Hilbert-cube frame fiber.** Infinite topological support of the
projective parameter law already forces a closed Hilbert cube in every finite Cayley--Toeplitz
frame fiber.  Atomlessness is unnecessary.  All carriers retain the complete Hamburger moment
sequence and measure class, the level-`N` Gram section, and the regular Cauchy jet through order
`N-1`. -/
theorem exists_closedEmbeddedHilbertCube_in_exactCayleyFrameFiber_of_infiniteSupport
    (heta : eta.support.Infinite) (N : ℕ)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ v : ℕ → Lp ℝ ⊤ eta,
      ∃ carrier : SignedHilbertCube → ProbabilityMeasure ℝ,
      Topology.IsClosedEmbedding
          (affinePositiveHilbertCubeMap (linftyOne eta) delta v) ∧
      Topology.IsClosedEmbedding carrier ∧
      (∀ t, (carrier t : Measure ℝ) = weightedBoundaryCarrier F eta
        (affinePositiveHilbertCubeMap (linftyOne eta) delta v t)) ∧
      ∀ t,
        LinftyStrictlyPositive eta
          (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) ∧
        HasHamburgerMoments s (carrier t : Measure ℝ) ∧
        ((carrier t : Measure ℝ) ≪
            boundaryBarycenter eta (fun q => (F.leaf q : Measure ℝ)) ∧
          boundaryBarycenter eta (fun q => (F.leaf q : Measure ℝ)) ≪
            (carrier t : Measure ℝ)) ∧
        circleToeplitzGram N (cayleyMomentZ (carrier t : Measure ℝ)) =
          circleToeplitzGram N (cayleyMomentZ
            (boundaryBarycenter eta (fun q => (F.leaf q : Measure ℝ)))) ∧
        ∀ n < N,
          iteratedDeriv n (resolventTransform (carrier t : Measure ℝ)) (-I) =
            iteratedDeriv n
              (resolventTransform
                (boundaryBarycenter eta (fun q => (F.leaf q : Measure ℝ)))) (-I) := by
  obtain ⟨v, _ell, _hvnorm, _hbio, hwembed, hall, carrier, hcembed, hcarrier⟩ :=
    exists_positiveHilbertCube_weightedBoundaryCarriers_of_infiniteSupport F eta heta
      (boundaryCayleyConstraintL1 F eta N) hdelta0 hdelta1
  have hbaseint : ∫ x, ⇑(linftyOne eta) x ∂eta = 1 := by
    rw [← linftyIntegralCLM_apply]
    exact linftyIntegralCLM_linftyOne eta
  refine ⟨v, carrier, hwembed, hcembed, hcarrier, ?_⟩
  intro t
  have hframe := gram_and_cauchyJet_eq_of_normalizedCayleyConstraint_eq F eta N
    (hall t).2.1 (linftyOne_strictlyPositive eta)
    (by
      rw [← linftyIntegralCLM_apply]
      have hzero := congrFun (hall t).1 (0 : Fin (N + N + 1))
      rw [normalizedLinftyL1ConstraintOperator_zero,
        normalizedLinftyL1ConstraintOperator_zero, linftyIntegralCLM_linftyOne] at hzero
      exact hzero)
    hbaseint (hall t).1
  have hac := weightedBoundaryCarrier_mutuallyAbsolutelyContinuous F eta (hall t).2.1
  rw [hcarrier t]
  rw [weightedBoundaryCarrier_linftyOne F eta] at hframe
  exact ⟨(hall t).2.1, (hall t).2.2, hac, hframe⟩

end
end GaloisForLFunctions.HTGeometry
