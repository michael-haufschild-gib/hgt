import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePActiveQuantileCellPort
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePFullCrossCurrentHistory
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePStrictCrossNonpositive
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolGramModularFaithfulness
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaSignedBivariateStability
import GaloisForLFunctions.RHTower.LoewnerCongruenceNormalization

/-!
# Full active-head P packet and survival of signed source current

Each finite physical head is reduced to exactly its active prime-power labels.
Those labels admit distinct literal zero-clock P-G186 Burnol columns. Their
five-profile source-current matrix agrees entrywise with the physical strict
cross kernel, and its all-ones quadratic is the original source current.

Cofinal negative source excursions therefore produce cofinal non-PSD finite
source packets. P-G186's prime-log Gram is invertible and Hermitian on these
packets, so the actual forward two-Julia `H * C * H` coefficient remains
non-PSD. This is a finite ordered-incidence obstruction, not a cofinal
graph-norm estimate or an Xi divisor landing.
-/

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

private def activeSet (K : ℕ) : Finset (Fin (K + 1)) := by
  classical
  exact Finset.univ.filter (fun i => IsPrimePow (i.val + 2))

private def activeEquiv (K : ℕ) :
    ↥(activeSet K) ≃ Fin (activeSet K).card :=
  (activeSet K).equivFin

private theorem active_prime (K : ℕ) (j : Fin (activeSet K).card) :
    IsPrimePow (((activeEquiv K).symm j).1.val + 2) := by
  have h := ((activeEquiv K).symm j).2
  simpa only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and] using h

private def packet (K : ℕ) (j : Fin (activeSet K).card) :
    Nat.Primes × ℕ :=
  Classical.choose (isPrimePow_exists_routePPrimitiveBurnolZeroClockRay
    (((activeEquiv K).symm j).1.val + 2) (active_prime K j))

private theorem packet_val (K : ℕ) (j : Fin (activeSet K).card) :
    xiGammaEulerValuationNat (packet K j) =
      ((activeEquiv K).symm j).1.val + 2 :=
  (Classical.choose_spec (isPrimePow_exists_routePPrimitiveBurnolZeroClockRay
    (((activeEquiv K).symm j).1.val + 2) (active_prime K j))).1

private theorem packet_injective (K : ℕ) : Function.Injective (packet K) := by
  intro i j hij
  have hv := congrArg xiGammaEulerValuationNat hij
  rw [packet_val, packet_val] at hv
  have hfin : ((activeEquiv K).symm i).1 = ((activeEquiv K).symm j).1 := by
    apply Fin.ext
    omega
  have hsub : (activeEquiv K).symm i = (activeEquiv K).symm j :=
    Subtype.ext hfin
  exact (activeEquiv K).symm.injective hsub

private theorem cross_symm (m n : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue m n =
      ccmActualHeadMatchedQuantileParabolicCrossKernelValue n m := by
  unfold ccmActualHeadMatchedQuantileParabolicCrossKernelValue ccmParabolicPairing
  ring

private theorem cross_zero_left (m n : ℕ) (hm : ¬ IsPrimePow m) :
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue m n = 0 := by
  rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_orientation_sub_debt]
  unfold ccmActualHeadMatchedQuantileParabolicOrientationLedger
    ccmActualHeadMatchedQuantileParabolicOrientationCoefficient
    ccmActualHeadMatchedQuantileParabolicDisplacementDebt
  rw [criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hm]
  ring

private theorem cross_zero_right (m n : ℕ) (hn : ¬ IsPrimePow n) :
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue m n = 0 := by
  rw [cross_symm]
  exact cross_zero_left n m hn

private theorem sum_active (K : ℕ) (f : Fin (K + 1) → ℂ)
    (hf : ∀ i, ¬ IsPrimePow (i.val + 2) → f i = 0) :
    (∑ i : Fin (K + 1), f i) = ∑ a : ↥(activeSet K), f a.1 := by
  classical
  calc
    (∑ i : Fin (K + 1), f i) =
        ∑ i : Fin (K + 1), if IsPrimePow (i.val + 2) then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : IsPrimePow (i.val + 2)
      · simp [hi]
      · simp [hi, hf i hi]
    _ = ∑ i ∈ activeSet K, f i := by
      simp [activeSet, Finset.sum_filter]
    _ = ∑ a : ↥(activeSet K), f a.1 := by
      exact (Finset.sum_coe_sort (activeSet K) f).symm

private theorem sum_active_equiv (K : ℕ) (f : ↥(activeSet K) → ℂ) :
    (∑ a : ↥(activeSet K), f a) =
      ∑ i : Fin (activeSet K).card, f ((activeEquiv K).symm i) := by
  exact Fintype.sum_equiv (activeEquiv K) f _ (fun a => by simp)

private theorem packet_cross_apply (K : ℕ)
    (i j : Fin (activeSet K).card) :
    routePPrimitiveBurnolSourceCrossCurrent (packet K) i j =
      (ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix K
        ((activeEquiv K).symm i).1 ((activeEquiv K).symm j).1 : ℂ) := by
  rw [routePPrimitiveBurnolSourceCrossCurrent,
    speQuantileRieszAtomCrossCurrent_apply]
  simp only [packet_val, ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix]

private theorem packet_cross_sum_eq_source (K : ℕ) :
    (∑ i : Fin (activeSet K).card,
      ∑ j : Fin (activeSet K).card,
        routePPrimitiveBurnolSourceCrossCurrent (packet K) i j) =
      (ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) : ℂ) := by
  rw [← routeP_crossKernel_ones_quadratic_eq_sourceCurrent]
  simp only [dotProduct, Matrix.mulVec, mul_one, one_mul,
    ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix]
  push_cast
  have hsum :
      (∑ i : Fin (K + 1), ∑ j : Fin (K + 1),
        (ccmActualHeadMatchedQuantileParabolicCrossKernelValue
          (i.val + 2) (j.val + 2) : ℂ)) =
      ∑ a : ↥(activeSet K), ∑ b : ↥(activeSet K),
        (ccmActualHeadMatchedQuantileParabolicCrossKernelValue
          (a.1.val + 2) (b.1.val + 2) : ℂ) := by
    rw [sum_active]
    · apply Finset.sum_congr rfl
      intro a _
      apply sum_active
      intro j hj
      rw [cross_zero_right _ _ hj]
      rfl
    · intro i hi
      simp_rw [cross_zero_left _ _ hi]
      simp
  rw [hsum]
  rw [sum_active_equiv K]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_active_equiv K]
  apply Finset.sum_congr rfl
  intro j _
  exact packet_cross_apply K i j

private theorem packet_cross_hermitian (K : ℕ) :
    (routePPrimitiveBurnolSourceCrossCurrent (packet K)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  rw [packet_cross_apply, packet_cross_apply]
  change star ((ccmActualHeadMatchedQuantileParabolicCrossKernelValue
      (((activeEquiv K).symm j).1.val + 2)
      (((activeEquiv K).symm i).1.val + 2) : ℝ) : ℂ) =
    (ccmActualHeadMatchedQuantileParabolicCrossKernelValue
      (((activeEquiv K).symm i).1.val + 2)
      (((activeEquiv K).symm j).1.val + 2) : ℂ)
  rw [← starRingEnd_apply, Complex.conj_ofReal, cross_symm]

private theorem source_negative_cofinal (M : ℕ) :
    ∃ K : ℕ, M ≤ K ∧
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) < 0 := by
  obtain ⟨K, hKM, hnegative⟩ :=
    routeP_normalized_history_cofinally_unbounded_below 0 M
  refine ⟨K, hKM, ?_⟩
  have hmass : 0 < ccmActualHeadParabolicMass K :=
    ccmActualHeadParabolicMass_pos K
  rw [ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect_eq_sourceCurrent]
    at hnegative
  have h := (div_lt_iff₀ hmass).mp hnegative
  simpa using h

private theorem cofinal_packet_history_not_posSemidef (M : ℕ) :
    ∃ K : ℕ, M ≤ K ∧
      ¬ (let pe := packet K
        let H := routePPrimitiveJointDepthPrimeLogConjugate pe
          (routePPrimitiveBurnolWindowGramMatrix pe (fun _ => 0))
        H * routePPrimitiveBurnolSourceCrossCurrent pe * H).PosSemidef := by
  obtain ⟨K, hKM, hsource⟩ := source_negative_cofinal M
  refine ⟨K, hKM, ?_⟩
  let pe := packet K
  let C := routePPrimitiveBurnolSourceCrossCurrent pe
  let H := routePPrimitiveJointDepthPrimeLogConjugate pe
    (routePPrimitiveBurnolWindowGramMatrix pe (fun _ => 0))
  have hCneg : ¬ C.PosSemidef := by
    intro hC
    have hquad := hC.dotProduct_mulVec_nonneg
      (fun _ : Fin (activeSet K).card => (1 : ℂ))
    have hsum : (0 : ℂ) ≤ ∑ i : Fin (activeSet K).card,
        ∑ j : Fin (activeSet K).card, C i j := by
      simpa [dotProduct, Matrix.mulVec] using hquad
    rw [show (∑ i : Fin (activeSet K).card,
        ∑ j : Fin (activeSet K).card, C i j) =
        (ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) : ℂ) from
        packet_cross_sum_eq_source K] at hsum
    have hreal : 0 ≤
        ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) := by
      exact (Complex.le_def.mp hsum).1
    exact (not_lt_of_ge hreal) hsource
  have hHpos : H.PosSemidef :=
    routePPrimitiveBurnolPrimeLogConjugate_posSemidef pe (fun _ => 0)
  have hHdet : IsUnit H.det :=
    (Matrix.isUnit_iff_isUnit_det H).mp
      (routePPrimitiveJointDepthPrimeLogConjugate_burnol_isUnit
        pe (packet_injective K) (fun _ => 0))
  intro hword
  apply hCneg
  have hcong : (H * C * Hᴴ).PosSemidef := by
    simpa [hHpos.isHermitian.eq] using hword
  exact (posSemidef_congruence_iff (packet_cross_hermitian K) hHdet).mp hcong

/-- Cofinal physical heads admit an injective literal prime-power P packet
whose complete five-profile matrix has exactly the physical source-current
sum, while the actual forward P-G186 two-Julia middle coefficient is not
positive semidefinite. No sign or graph hypothesis is assumed. -/
theorem routeP_cofinal_activeHead_sourceHistory_not_posSemidef (M : ℕ) :
    ∃ (K N : ℕ) (pe : Fin N → Nat.Primes × ℕ),
      M ≤ K ∧ Function.Injective pe ∧
      (∑ i : Fin N, ∑ j : Fin N,
        routePPrimitiveBurnolSourceCrossCurrent pe i j) =
        (ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) : ℂ) ∧
      ¬ (let H := routePPrimitiveJointDepthPrimeLogConjugate pe
          (routePPrimitiveBurnolWindowGramMatrix pe (fun _ => 0))
        H * routePPrimitiveBurnolSourceCrossCurrent pe * H).PosSemidef := by
  obtain ⟨K, hKM, hword⟩ := cofinal_packet_history_not_posSemidef M
  exact ⟨K, (activeSet K).card, packet K, hKM,
    packet_injective K, packet_cross_sum_eq_source K, hword⟩

end
end RHTower
