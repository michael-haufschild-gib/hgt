import GaloisForLFunctions.RHTower.XiHurwitzOrientationExactBoundaryMultiplicity

open Complex Metric Function Filter Topology
open scoped Topology BigOperators

namespace RHTower

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Common absolute orientation coefficient on one analytic-multiplicity fiber. -/
def xiHurwitzOrientationAbsoluteFiberCoefficient (ρ : XiDivisorSupport) : ℂ :=
  ((‖xiHurwitzOrientationFiberCoefficient ρ‖ : ℝ) : ℂ)

/-- One complete multiplicity fiber of the absolute orientation companion. -/
def xiHurwitzOrientationAbsoluteFiberVector (ρ : XiDivisorSupport) : XiWeilCarrier :=
  xiHurwitzOrientationAbsoluteFiberCoefficient ρ •
    xiWeilFiberIndicatorLp (xiSpectralPointSupport ρ)

theorem xiHurwitzOrientationAbsoluteFiberVector_mem_continuedCauchyHilbertSubspace
    (ρ : XiDivisorSupport) :
    xiHurwitzOrientationAbsoluteFiberVector ρ ∈
      xiWeilContinuedCauchyHilbertSubspace := by
  exact xiWeilContinuedCauchyHilbertSubspace.smul_mem _
    (xiWeilFiberIndicatorLp_mem_continuedCauchyHilbertSubspace
      (xiFirstZeroCopy ρ))

theorem sum_xiHurwitzOrientationAbsoluteCoordinate_single_fiber (ρ : XiDivisorSupport) :
    (∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
      lp.single 2 (⟨ρ, j⟩ : XiZeroCopy)
        (((‖xiHurwitzOrientationCoordinate (⟨ρ, j⟩ : XiZeroCopy)‖ : ℝ) : ℂ))) =
      xiHurwitzOrientationAbsoluteFiberVector ρ := by
  apply Subtype.ext
  funext q
  rcases q with ⟨τ, k⟩
  simp only [lp.coeFn_sum, Finset.sum_apply]
  change
    (∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
      (lp.single (E := fun _ : XiZeroCopy => ℂ) 2 (⟨ρ, j⟩ : XiZeroCopy)
        (((‖xiHurwitzOrientationCoordinate (⟨ρ, j⟩ : XiZeroCopy)‖ : ℝ) : ℂ)))
          (⟨τ, k⟩ : XiZeroCopy)) =
      xiHurwitzOrientationAbsoluteFiberVector ρ (⟨τ, k⟩ : XiZeroCopy)
  by_cases hτρ : τ = ρ
  · subst τ
    have hleft :
        (∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
          (lp.single (E := fun _ : XiZeroCopy => ℂ) 2 (⟨ρ, j⟩ : XiZeroCopy)
            (((‖xiHurwitzOrientationCoordinate (⟨ρ, j⟩ : XiZeroCopy)‖ : ℝ) : ℂ)))
              (⟨ρ, k⟩ : XiZeroCopy)) =
          (((‖xiHurwitzOrientationCoordinate (⟨ρ, k⟩ : XiZeroCopy)‖ : ℝ) : ℂ)) := by
      rw [Fintype.sum_eq_single k]
      · rw [lp.single_apply_self]
      · intro j hj
        rw [lp.single_apply_ne]
        intro heq
        apply hj
        cases heq
        rfl
    rw [hleft]
    simp [xiHurwitzOrientationAbsoluteFiberVector,
      xiHurwitzOrientationAbsoluteFiberCoefficient,
      xiHurwitzOrientationFiberCoefficient,
      xiWeilFiberIndicatorLp_apply, xiSpectralPoint_eq_support,
      xiHurwitzOrientationCoordinate]
  · have hspec : xiSpectralPointSupport τ ≠ xiSpectralPointSupport ρ := by
      intro heq
      exact hτρ (xiSpectralPointSupport_injective heq)
    have hleft :
        (∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
          (lp.single (E := fun _ : XiZeroCopy => ℂ) 2 (⟨ρ, j⟩ : XiZeroCopy)
            (((‖xiHurwitzOrientationCoordinate (⟨ρ, j⟩ : XiZeroCopy)‖ : ℝ) : ℂ)))
              (⟨τ, k⟩ : XiZeroCopy)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _hj
      rw [lp.single_apply_ne]
      intro heq
      have hfst := congrArg Sigma.fst heq
      exact hτρ hfst
    rw [hleft]
    simp only [xiHurwitzOrientationAbsoluteFiberVector, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, xiWeilFiberIndicatorLp_apply,
      xiSpectralPoint_eq_support, hspec,
      ↓reduceIte, mul_zero]

theorem hasSum_xiHurwitzOrientationAbsoluteFiberVector :
    HasSum xiHurwitzOrientationAbsoluteFiberVector
      xiHurwitzOrientationAbsoluteVector := by
  let f : XiZeroCopy → XiWeilCarrier := fun q =>
    lp.single 2 q (xiHurwitzOrientationAbsoluteVector q)
  have hall : HasSum f xiHurwitzOrientationAbsoluteVector :=
    lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤)
      xiHurwitzOrientationAbsoluteVector
  apply hall.sigma
  intro ρ
  rw [← sum_xiHurwitzOrientationAbsoluteCoordinate_single_fiber ρ]
  simpa only [f, xiHurwitzOrientationAbsoluteVector_apply] using
    (hasSum_fintype (fun j : Fin (Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =>
        lp.single (E := fun _ : XiZeroCopy => ℂ) 2 (⟨ρ, j⟩ : XiZeroCopy)
          (((‖xiHurwitzOrientationCoordinate (⟨ρ, j⟩ : XiZeroCopy)‖ : ℝ) : ℂ))))

theorem xiHurwitzOrientationAbsoluteVector_mem_continuedCauchyHilbertSubspace :
    xiHurwitzOrientationAbsoluteVector ∈
      xiWeilContinuedCauchyHilbertSubspace := by
  have hmem :
      (∑' ρ : XiDivisorSupport, xiHurwitzOrientationAbsoluteFiberVector ρ) ∈
        xiWeilContinuedCauchyHilbertSubspace :=
    tsum_mem
      (Submodule.isClosed_topologicalClosure
        xiWeilContinuedCauchyAlgebraicSubspace)
      xiHurwitzOrientationAbsoluteFiberVector_mem_continuedCauchyHilbertSubspace
  rw [hasSum_xiHurwitzOrientationAbsoluteFiberVector.tsum_eq] at hmem
  exact hmem

/-- The entire continued Cauchy Hilbert subspace lies in the closure of actual separated packet
evaluations, not only the signed orientation vector. -/
theorem xiWeilContinuedCauchyHilbertSubspace_le_closure_separatedPacketEvaluations :
    (xiWeilContinuedCauchyHilbertSubspace : Set XiWeilCarrier) ⊆
      closure xiSeparatedContinuedCauchyPacketEvaluationSet := by
  have hclosure :
      closure (xiWeilContinuedCauchyAlgebraicSubspace : Set XiWeilCarrier) ⊆
        closure xiSeparatedContinuedCauchyPacketEvaluationSet :=
    closure_minimal
      continuedCauchyAlgebraicSubspace_le_closure_separatedPacketEvaluations
      isClosed_closure
  exact hclosure

theorem xiHurwitzOrientationBoundaryPlus_mem_continuedCauchyHilbertSubspace :
    xiHurwitzOrientationBoundaryPlus ∈
      xiWeilContinuedCauchyHilbertSubspace := by
  exact xiWeilContinuedCauchyHilbertSubspace.smul_mem _
    (xiWeilContinuedCauchyHilbertSubspace.add_mem
      xiHurwitzOrientationVector_mem_continuedCauchyHilbertSubspace
      xiHurwitzOrientationAbsoluteVector_mem_continuedCauchyHilbertSubspace)

theorem xiHurwitzOrientationBoundaryMinus_mem_continuedCauchyHilbertSubspace :
    xiHurwitzOrientationBoundaryMinus ∈
      xiWeilContinuedCauchyHilbertSubspace := by
  exact xiWeilContinuedCauchyHilbertSubspace.smul_mem _
    (xiWeilContinuedCauchyHilbertSubspace.sub_mem
      xiHurwitzOrientationVector_mem_continuedCauchyHilbertSubspace
      xiHurwitzOrientationAbsoluteVector_mem_continuedCauchyHilbertSubspace)

def xiHurwitzOrientationPositiveTargetPlus (t : ℝ) : XiWeilCarrier :=
  (1 / 2 : ℂ) • xiHurwitzOrientationVector +
    (((1 / 2 + t : ℝ) : ℂ)) • xiHurwitzOrientationAbsoluteVector

def xiHurwitzOrientationPositiveTargetMinus (t : ℝ) : XiWeilCarrier :=
  (1 / 2 : ℂ) • xiHurwitzOrientationVector -
    (((1 / 2 + t : ℝ) : ℂ)) • xiHurwitzOrientationAbsoluteVector

theorem xiHurwitzOrientationPositiveTargetPlus_mem_continuedCauchyHilbertSubspace
    (t : ℝ) :
    xiHurwitzOrientationPositiveTargetPlus t ∈
      xiWeilContinuedCauchyHilbertSubspace := by
  exact xiWeilContinuedCauchyHilbertSubspace.add_mem
    (xiWeilContinuedCauchyHilbertSubspace.smul_mem _
      xiHurwitzOrientationVector_mem_continuedCauchyHilbertSubspace)
    (xiWeilContinuedCauchyHilbertSubspace.smul_mem _
      xiHurwitzOrientationAbsoluteVector_mem_continuedCauchyHilbertSubspace)

theorem xiHurwitzOrientationPositiveTargetMinus_mem_continuedCauchyHilbertSubspace
    (t : ℝ) :
    xiHurwitzOrientationPositiveTargetMinus t ∈
      xiWeilContinuedCauchyHilbertSubspace := by
  exact xiWeilContinuedCauchyHilbertSubspace.sub_mem
    (xiWeilContinuedCauchyHilbertSubspace.smul_mem _
      xiHurwitzOrientationVector_mem_continuedCauchyHilbertSubspace)
    (xiWeilContinuedCauchyHilbertSubspace.smul_mem _
      xiHurwitzOrientationAbsoluteVector_mem_continuedCauchyHilbertSubspace)

theorem xiWeilHilbertQuadratic_positiveTargetPlus (t : ℝ) (ht : 0 < t) :
    xiWeilHilbertQuadratic (xiHurwitzOrientationPositiveTargetPlus t) =
      (t + t ^ 2) * xiHurwitzOrientationEnergy := by
  let u := xiHurwitzOrientationPositiveTargetPlus t
  have huplus : u + xiWeilLineConjLinearIsometry u =
      (((1 + 2 * t : ℝ) : ℂ)) • xiHurwitzOrientationAbsoluteVector := by
    change xiHurwitzOrientationPositiveTargetPlus t +
      xiWeilLineConjLinearIsometry (xiHurwitzOrientationPositiveTargetPlus t) = _
    rw [xiHurwitzOrientationPositiveTargetPlus, map_add, map_smul, map_smul,
      xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationVector,
      xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector]
    module
  have huminus : u - xiWeilLineConjLinearIsometry u =
      xiHurwitzOrientationVector := by
    change xiHurwitzOrientationPositiveTargetPlus t -
      xiWeilLineConjLinearIsometry (xiHurwitzOrientationPositiveTargetPlus t) = _
    rw [xiHurwitzOrientationPositiveTargetPlus, map_add, map_smul, map_smul,
      xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationVector,
      xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector]
    module
  have hbalance := CliffordWeil.four_mul_quadratic_eq_even_sub_odd
    xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive u
  rw [huplus, huminus, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < 1 + 2 * t),
    norm_xiHurwitzOrientationAbsoluteVector_eq_orientationVector] at hbalance
  change 4 * xiWeilHilbertQuadratic u = _ at hbalance
  rw [← norm_sq_xiHurwitzOrientationVector]
  change xiWeilHilbertQuadratic u = _
  nlinarith [sq_nonneg ‖xiHurwitzOrientationVector‖]

theorem xiWeilHilbertQuadratic_positiveTargetMinus (t : ℝ) (ht : 0 < t) :
    xiWeilHilbertQuadratic (xiHurwitzOrientationPositiveTargetMinus t) =
      (t + t ^ 2) * xiHurwitzOrientationEnergy := by
  let u := xiHurwitzOrientationPositiveTargetMinus t
  have huplus : u + xiWeilLineConjLinearIsometry u =
      -((((1 + 2 * t : ℝ) : ℂ)) • xiHurwitzOrientationAbsoluteVector) := by
    change xiHurwitzOrientationPositiveTargetMinus t +
      xiWeilLineConjLinearIsometry (xiHurwitzOrientationPositiveTargetMinus t) = _
    rw [xiHurwitzOrientationPositiveTargetMinus, map_sub, map_smul, map_smul,
      xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationVector,
      xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector]
    module
  have huminus : u - xiWeilLineConjLinearIsometry u =
      xiHurwitzOrientationVector := by
    change xiHurwitzOrientationPositiveTargetMinus t -
      xiWeilLineConjLinearIsometry (xiHurwitzOrientationPositiveTargetMinus t) = _
    rw [xiHurwitzOrientationPositiveTargetMinus, map_sub, map_smul, map_smul,
      xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationVector,
      xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector]
    module
  have hbalance := CliffordWeil.four_mul_quadratic_eq_even_sub_odd
    xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive u
  rw [huplus, huminus, norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < 1 + 2 * t),
    norm_xiHurwitzOrientationAbsoluteVector_eq_orientationVector] at hbalance
  change 4 * xiWeilHilbertQuadratic u = _ at hbalance
  rw [← norm_sq_xiHurwitzOrientationVector]
  change xiWeilHilbertQuadratic u = _
  nlinarith [sq_nonneg ‖xiHurwitzOrientationVector‖]

/-- A positive point in separated-packet closure can be approximated by an actual separated
packet without leaving the open positive-energy region. -/
theorem exists_separatedContinuedCauchyPacket_sourceEnergy_pos_near
    {u : XiWeilCarrier}
    (hu : u ∈ closure xiSeparatedContinuedCauchyPacketEvaluationSet)
    (hQ : 0 < xiWeilHilbertQuadratic u) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : XiSeparatedContinuedCauchyPacket,
      0 < P.sourceEnergy ∧ dist P.evaluation u < ε := by
  have hopen : IsOpen {v : XiWeilCarrier | 0 < xiWeilHilbertQuadratic v} :=
    isOpen_Ioi.preimage continuous_xiWeilHilbertQuadratic
  have hnhds : {v : XiWeilCarrier | 0 < xiWeilHilbertQuadratic v} ∈ 𝓝 u :=
    hopen.mem_nhds hQ
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hr : 0 < min δ ε := lt_min hδ hε
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp hu (min δ ε) hr
  obtain ⟨P, rfl⟩ := hv
  refine ⟨P, ?_, ?_⟩
  rw [P.sourceEnergy_eq_hilbertQuadratic]
  apply hball
  rw [Metric.mem_ball, dist_comm]
  exact huv.trans_le (min_le_left _ _)
  rw [dist_comm]
  exact huv.trans_le (min_le_right _ _)

theorem tendsto_xiHurwitzOrientationPositiveTargetPlus_boundaryPlus :
    Tendsto
      (fun n : ℕ => xiHurwitzOrientationPositiveTargetPlus
        (1 / ((n : ℝ) + 1))) atTop
      (𝓝 xiHurwitzOrientationBoundaryPlus) := by
  have ht : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Continuous xiHurwitzOrientationPositiveTargetPlus := by
    unfold xiHurwitzOrientationPositiveTargetPlus
    fun_prop
  have h := hc.continuousAt.tendsto.comp ht
  have hzero : xiHurwitzOrientationPositiveTargetPlus 0 =
      xiHurwitzOrientationBoundaryPlus := by
    unfold xiHurwitzOrientationPositiveTargetPlus
      xiHurwitzOrientationBoundaryPlus
    module
  rw [← hzero]
  change Tendsto (fun n : ℕ => xiHurwitzOrientationPositiveTargetPlus
    (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (xiHurwitzOrientationPositiveTargetPlus 0)) at h
  exact h

theorem tendsto_xiHurwitzOrientationPositiveTargetMinus_boundaryMinus :
    Tendsto
      (fun n : ℕ => xiHurwitzOrientationPositiveTargetMinus
        (1 / ((n : ℝ) + 1))) atTop
      (𝓝 xiHurwitzOrientationBoundaryMinus) := by
  have ht : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Continuous xiHurwitzOrientationPositiveTargetMinus := by
    unfold xiHurwitzOrientationPositiveTargetMinus
    fun_prop
  have h := hc.continuousAt.tendsto.comp ht
  have hzero : xiHurwitzOrientationPositiveTargetMinus 0 =
      xiHurwitzOrientationBoundaryMinus := by
    unfold xiHurwitzOrientationPositiveTargetMinus
      xiHurwitzOrientationBoundaryMinus
    module
  rw [← hzero]
  change Tendsto (fun n : ℕ => xiHurwitzOrientationPositiveTargetMinus
    (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (xiHurwitzOrientationPositiveTargetMinus 0)) at h
  exact h

/-- Positive orientation energy gives strictly positive genuine source packets approaching both
exact null-boundary witnesses, with exact source energies tending to zero. -/
theorem exists_positiveSeparatedPackets_tendsto_both_orientationBoundaries_of_energy_pos
    (hE : 0 < xiHurwitzOrientationEnergy) :
    ∃ Pplus Pminus : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (Pplus n).evaluation) atTop
        (𝓝 xiHurwitzOrientationBoundaryPlus) ∧
      Tendsto (fun n => (Pplus n).sourceEnergy) atTop (𝓝 0) ∧
      (∀ n, 0 < (Pplus n).sourceEnergy) ∧
      Tendsto (fun n => (Pminus n).evaluation) atTop
        (𝓝 xiHurwitzOrientationBoundaryMinus) ∧
      Tendsto (fun n => (Pminus n).sourceEnergy) atTop (𝓝 0) ∧
      (∀ n, 0 < (Pminus n).sourceEnergy) := by
  have hplusClosure : ∀ n : ℕ,
      xiHurwitzOrientationPositiveTargetPlus (1 / ((n : ℝ) + 1)) ∈
        closure xiSeparatedContinuedCauchyPacketEvaluationSet := fun n =>
    xiWeilContinuedCauchyHilbertSubspace_le_closure_separatedPacketEvaluations
      (xiHurwitzOrientationPositiveTargetPlus_mem_continuedCauchyHilbertSubspace _)
  have hminusClosure : ∀ n : ℕ,
      xiHurwitzOrientationPositiveTargetMinus (1 / ((n : ℝ) + 1)) ∈
        closure xiSeparatedContinuedCauchyPacketEvaluationSet := fun n =>
    xiWeilContinuedCauchyHilbertSubspace_le_closure_separatedPacketEvaluations
      (xiHurwitzOrientationPositiveTargetMinus_mem_continuedCauchyHilbertSubspace _)
  have hplusQ : ∀ n : ℕ, 0 < xiWeilHilbertQuadratic
      (xiHurwitzOrientationPositiveTargetPlus (1 / ((n : ℝ) + 1))) := by
    intro n
    rw [xiWeilHilbertQuadratic_positiveTargetPlus _ (by positivity)]
    positivity
  have hminusQ : ∀ n : ℕ, 0 < xiWeilHilbertQuadratic
      (xiHurwitzOrientationPositiveTargetMinus (1 / ((n : ℝ) + 1))) := by
    intro n
    rw [xiWeilHilbertQuadratic_positiveTargetMinus _ (by positivity)]
    positivity
  have hplusExists : ∀ n : ℕ, ∃ P : XiSeparatedContinuedCauchyPacket,
      0 < P.sourceEnergy ∧
      dist P.evaluation
        (xiHurwitzOrientationPositiveTargetPlus (1 / ((n : ℝ) + 1))) <
          1 / ((n : ℝ) + 1) := fun n =>
    exists_separatedContinuedCauchyPacket_sourceEnergy_pos_near
      (hplusClosure n) (hplusQ n) (by positivity)
  have hminusExists : ∀ n : ℕ, ∃ P : XiSeparatedContinuedCauchyPacket,
      0 < P.sourceEnergy ∧
      dist P.evaluation
        (xiHurwitzOrientationPositiveTargetMinus (1 / ((n : ℝ) + 1))) <
          1 / ((n : ℝ) + 1) := fun n =>
    exists_separatedContinuedCauchyPacket_sourceEnergy_pos_near
      (hminusClosure n) (hminusQ n) (by positivity)
  choose Pplus hPplusPos hPplusDist using hplusExists
  choose Pminus hPminusPos hPminusDist using hminusExists
  have herrorPlus : Tendsto (fun n => dist (Pplus n).evaluation
      (xiHurwitzOrientationPositiveTargetPlus (1 / ((n : ℝ) + 1))))
      atTop (𝓝 0) := by
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => (hPplusDist n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have herrorMinus : Tendsto (fun n => dist (Pminus n).evaluation
      (xiHurwitzOrientationPositiveTargetMinus (1 / ((n : ℝ) + 1))))
      atTop (𝓝 0) := by
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => (hPminusDist n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have htargetPlusDist := tendsto_iff_dist_tendsto_zero.mp
    tendsto_xiHurwitzOrientationPositiveTargetPlus_boundaryPlus
  have htargetMinusDist := tendsto_iff_dist_tendsto_zero.mp
    tendsto_xiHurwitzOrientationPositiveTargetMinus_boundaryMinus
  have hPplus : Tendsto (fun n => (Pplus n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryPlus) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => dist_triangle _
        (xiHurwitzOrientationPositiveTargetPlus (1 / ((n : ℝ) + 1))) _)
      (by simpa only [zero_add] using herrorPlus.add htargetPlusDist)
  have hPminus : Tendsto (fun n => (Pminus n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryMinus) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => dist_triangle _
        (xiHurwitzOrientationPositiveTargetMinus (1 / ((n : ℝ) + 1))) _)
      (by simpa only [zero_add] using herrorMinus.add htargetMinusDist)
  have hEnergyPlus :=
    continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hPplus
  have hEnergyMinus :=
    continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hPminus
  rw [xiHurwitzOrientationBoundaryPlus_exact.1] at hEnergyPlus
  rw [xiHurwitzOrientationBoundaryMinus_exact.1] at hEnergyMinus
  refine ⟨Pplus, Pminus, hPplus, ?_, hPplusPos, hPminus, ?_, hPminusPos⟩
  · apply hEnergyPlus.congr'
    exact Eventually.of_forall fun n =>
      (Pplus n).sourceEnergy_eq_hilbertQuadratic.symm
  · apply hEnergyMinus.congr'
    exact Eventually.of_forall fun n =>
      (Pminus n).sourceEnergy_eq_hilbertQuadratic.symm

/-- Empty separated packet used when orientation energy and both boundary targets collapse. -/
def xiOrientationBoundaryEmptySeparatedPacket :
    XiSeparatedContinuedCauchyPacket where
  index := Fin 0
  fintypeIndex := inferInstance
  coeff := Fin.elim0
  pole := Fin.elim0
  separated i := Fin.elim0 i

@[simp] theorem xiOrientationBoundaryEmptySeparatedPacket_evaluation :
    xiOrientationBoundaryEmptySeparatedPacket.evaluation = 0 := by
  rw [XiSeparatedContinuedCauchyPacket.evaluation]
  unfold xiWeilContinuedCauchyPacketLp
  change (∑ _i : Fin 0, _) = 0
  rw [Fintype.sum_empty]

@[simp] theorem xiOrientationBoundaryEmptySeparatedPacket_sourceEnergy :
    xiOrientationBoundaryEmptySeparatedPacket.sourceEnergy = 0 := by
  rw [XiSeparatedContinuedCauchyPacket.sourceEnergy_eq_hilbertQuadratic,
    xiOrientationBoundaryEmptySeparatedPacket_evaluation]
  simp [xiWeilHilbertQuadratic, xiWeilLineConjLinearIsometry]

/-- **Unconditional positive-side source saturation of both exact Route-Q boundaries.**
There are actual finite pairwise-separated continued prime--Gamma packets converging to both
canonical exact null-boundary witnesses. Their exact source energies are nonnegative and tend to
zero. If orientation energy is positive, every packet in both sequences has strictly positive
source energy. -/
theorem exists_nonnegativeSeparatedPackets_tendsto_both_orientationBoundaries :
    ∃ Pplus Pminus : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (Pplus n).evaluation) atTop
        (𝓝 xiHurwitzOrientationBoundaryPlus) ∧
      Tendsto (fun n => (Pplus n).sourceEnergy) atTop (𝓝 0) ∧
      (∀ n, 0 ≤ (Pplus n).sourceEnergy) ∧
      Tendsto (fun n => (Pminus n).evaluation) atTop
        (𝓝 xiHurwitzOrientationBoundaryMinus) ∧
      Tendsto (fun n => (Pminus n).sourceEnergy) atTop (𝓝 0) ∧
      (∀ n, 0 ≤ (Pminus n).sourceEnergy) ∧
      (0 < xiHurwitzOrientationEnergy →
        (∀ n, 0 < (Pplus n).sourceEnergy) ∧
        (∀ n, 0 < (Pminus n).sourceEnergy)) := by
  by_cases hzero : xiHurwitzOrientationEnergy = 0
  · have hw : xiHurwitzOrientationVector = 0 :=
      xiHurwitzOrientationVector_eq_zero_iff_energy_eq_zero.2 hzero
    have he : xiHurwitzOrientationAbsoluteVector = 0 := by
      apply norm_eq_zero.mp
      have hsq : ‖xiHurwitzOrientationAbsoluteVector‖ ^ 2 = 0 := by
        rw [norm_sq_xiHurwitzOrientationAbsoluteVector, hzero]
      nlinarith [norm_nonneg xiHurwitzOrientationAbsoluteVector]
    have hbplus : xiHurwitzOrientationBoundaryPlus = 0 := by
      unfold xiHurwitzOrientationBoundaryPlus
      rw [hw, he]
      module
    have hbminus : xiHurwitzOrientationBoundaryMinus = 0 := by
      unfold xiHurwitzOrientationBoundaryMinus
      rw [hw, he]
      module
    let P : ℕ → XiSeparatedContinuedCauchyPacket := fun _ =>
      xiOrientationBoundaryEmptySeparatedPacket
    have hPevalPlus : Tendsto (fun n => (P n).evaluation) atTop
        (𝓝 xiHurwitzOrientationBoundaryPlus) := by
      rw [hbplus]
      simpa only [P, xiOrientationBoundaryEmptySeparatedPacket_evaluation] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : XiWeilCarrier))
          atTop (𝓝 0))
    have hPevalMinus : Tendsto (fun n => (P n).evaluation) atTop
        (𝓝 xiHurwitzOrientationBoundaryMinus) := by
      rw [hbminus]
      simpa only [P, xiOrientationBoundaryEmptySeparatedPacket_evaluation] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : XiWeilCarrier))
          atTop (𝓝 0))
    have hPenergy : Tendsto (fun n => (P n).sourceEnergy) atTop (𝓝 0) := by
      simpa only [P, xiOrientationBoundaryEmptySeparatedPacket_sourceEnergy] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    refine ⟨P, P, hPevalPlus, hPenergy, ?_, hPevalMinus, hPenergy, ?_, ?_⟩
    · intro n
      simp [P]
    · intro n
      simp [P]
    · intro hpos
      exact (hpos.ne' hzero).elim
  · have hpos : 0 < xiHurwitzOrientationEnergy :=
      lt_of_le_of_ne xiHurwitzOrientationEnergy_nonneg (Ne.symm hzero)
    obtain ⟨Pplus, Pminus, hPplus, hEplus, hplusPos,
        hPminus, hEminus, hminusPos⟩ :=
      exists_positiveSeparatedPackets_tendsto_both_orientationBoundaries_of_energy_pos hpos
    refine ⟨Pplus, Pminus, hPplus, hEplus, fun n => (hplusPos n).le,
      hPminus, hEminus, fun n => (hminusPos n).le, ?_⟩
    intro _
    exact ⟨hplusPos, hminusPos⟩

end

end RHTower

