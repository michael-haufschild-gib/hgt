import GaloisForLFunctions.RHTower.GammaSewnPluckerNuclearRootTransportNoGo
import GaloisForLFunctions.RHTower.SoninRegularizedMomentWeldNoGo
import GaloisForLFunctions.RHTower.PrimeArchExplicitCircleStateReflection

open Filter Topology ContinuousLinearMap
open scoped BigOperators
noncomputable section
namespace RHTower

private theorem positive_power_sums_hankel
    {a : ℕ → ℝ} (ha : Summable a) (ha0 : ∀ n, 0 ≤ a n) (haa : Antitone a) :
    CompleteHankelCone (fun r => ∑' n, a n ^ (r + 1)) := by
  intro N v
  have hs (i j : Fin N) : Summable (fun k => v i * v j * a k ^ ((i : ℕ) + j + 1)) :=
    (GaloisForLFunctions.HTGeometry.summable_pow_succ_of_nonneg_antitone
      ha ha0 haa ((i : ℕ) + j)).mul_left _
  have hsrow (i : Fin N) : Summable (fun k => ∑ j : Fin N,
      v i * v j * a k ^ ((i : ℕ) + j + 1)) :=
    summable_sum fun j _ => hs i j
  have heq : (∑ i : Fin N, ∑ j : Fin N,
      v i * v j * ∑' k, a k ^ ((i : ℕ) + j + 1)) =
      ∑' k, a k * (∑ i : Fin N, v i * a k ^ (i : ℕ)) ^ 2 := by
    simp_rw [← tsum_mul_left]
    simp_rw [← Summable.tsum_finsetSum (fun j _ => hs _ j)]
    rw [← Summable.tsum_finsetSum (fun i _ => hsrow i)]
    apply tsum_congr
    intro k
    rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add, pow_succ]
    ring
  rw [heq]
  exact tsum_nonneg fun k => mul_nonneg (ha0 k) (sq_nonneg _)

theorem repeatTwo_summable {a : ℕ → ℝ} (ha : Summable a) (ha0 : ∀ n, 0 ≤ a n) :
    Summable (fun n : ℕ => a (n / 2)) := by
  have hp : Summable (fun ni : ℕ × Fin 2 => a ni.1) := by
    rw [summable_prod_of_nonneg (fun ni => ha0 ni.1)]
    exact ⟨fun _ => (hasSum_fintype _).summable, by simpa [mul_comm] using ha.mul_right 2⟩
  exact (Nat.divModEquiv 2).summable_iff.mpr hp

theorem repeatTwo_tsum {a : ℕ → ℝ} (ha : Summable a) (ha0 : ∀ n, 0 ≤ a n) :
    (∑' n : ℕ, a (n / 2)) = 2 * ∑' n, a n := by
  have hp : Summable (fun ni : ℕ × Fin 2 => a ni.1) := by
    rw [summable_prod_of_nonneg (fun ni => ha0 ni.1)]
    exact ⟨fun _ => (hasSum_fintype _).summable, by simpa [mul_comm] using ha.mul_right 2⟩
  have heq := (Nat.divModEquiv 2).tsum_eq (fun ni : ℕ × Fin 2 => a ni.1)
  rw [hp.tsum_prod] at heq
  simpa [tsum_mul_right, mul_comm] using heq

/-- No decreasing nonnegative summable sequence has the full completed Xi square moments.
All Xi multiplicities and both reflection copies occur in the existing ordered enumeration. -/
theorem not_summable_nonneg_primeArch_square_moments
    {b : ℕ → ℝ} (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hba : Antitone b) :
    ¬ (∀ r : ℕ, (∑' n, (b n ^ 2) ^ (r + 1)) = normalizedPrimeArchMoment r) := by
  intro hm
  have hbsq : Summable (fun n => b n ^ 2) := by
    simpa using GaloisForLFunctions.HTGeometry.summable_pow_succ_of_nonneg_antitone
      hb hb0 hba 1
  have hRH : RiemannHypothesis := by
    apply completeHankelCone_normalizedPrimeArchMoment_iff_riemannHypothesis.mp
    have hcone := positive_power_sums_hankel hbsq (fun n => sq_nonneg (b n))
      (fun _ _ h => pow_le_pow_left₀ (hb0 _) (hba h) 2)
    have heq : (fun r => ∑' n, (b n ^ 2) ^ (r + 1)) = normalizedPrimeArchMoment :=
      funext hm
    rwa [heq] at hcone
  have hxisq : Summable (fun n => approxNumber xiOrderedSignedPrimeOperator n ^ 2) := by
    simpa [MemSchattenClass, Real.rpow_two] using xiOrderedSignedPrimeOperator_memSchattenClass_two
  have heq : b = approxNumber xiOrderedSignedPrimeOperator := by
    apply nonneg_sequence_eq_of_summable_square_moments hbsq hxisq hb0
      (approxNumber_nonneg _) hba (approxNumber_antitone _)
    intro r
    have hbmom := congrArg (fun x : ℝ => (x : ℂ)) (hm r)
    rw [Complex.ofReal_tsum] at hbmom
    simpa only [Complex.ofReal_pow] using
      hbmom.trans (normalizedPrimeArchMoment_eq_orderedXi_approxNumber_moments_of_rh hRH r)
  apply xiOrderedSignedPrimeOperator_not_memSchattenClass_one
  exact (heq ▸ hb).congr fun _ => (Real.rpow_one _).symm

/-- A nuclear amplitude cannot realize the half-normalized completed Xi energy moments.
The duplicate enumeration keeps both reflection copies and every multiplicity. -/
theorem not_nuclear_half_normalized_primeArch_energy_moments
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : H →L[ℂ] H} (hA : MemSchattenClass 1 A) :
    ¬ (∀ r : ℕ, 2 * opTrace (energyOp A ^ (r + 1)) = (normalizedPrimeArchMoment r : ℂ)) := by
  intro hm
  have hA2 : MemSchattenClass 2 A := hA.mono one_pos (by norm_num)
  have hAHS := (memSchattenClass_two_iff_isHilbertSchmidt A).mp hA2
  let a := approxNumber A
  let b : ℕ → ℝ := fun n => a (n / 2)
  have ha : Summable a := hA.one_summable_approxNumber
  have ha0 : ∀ n, 0 ≤ a n := approxNumber_nonneg A
  have haa : Antitone a := approxNumber_antitone A
  have hb : Summable b := repeatTwo_summable ha ha0
  have hb0 : ∀ n, 0 ≤ b n := fun n => ha0 _
  have hba : Antitone b := fun _ _ h => haa (Nat.div_le_div_right h)
  have hasq : Summable (fun n => a n ^ 2) := by simpa [MemSchattenClass, Real.rpow_two] using hA2
  have hbsq : Summable (fun n => b n ^ 2) := by
    exact repeatTwo_summable hasq (fun n => sq_nonneg _)
  have hapow (r : ℕ) : Summable (fun n => (a n ^ 2) ^ (r + 1)) :=
    GaloisForLFunctions.HTGeometry.summable_pow_succ_of_nonneg_antitone
      hasq (fun _ => sq_nonneg _) (fun _ _ h => pow_le_pow_left₀ (ha0 _) (haa h) 2) r
  have hrepeated (r : ℕ) :
      (∑' n, (b n ^ 2) ^ (r + 1)) = 2 * ∑' n, (a n ^ 2) ^ (r + 1) :=
    repeatTwo_tsum (hapow r) (fun n => pow_nonneg (sq_nonneg _) _)
  have hbmom (r : ℕ) :
      ((∑' n, (b n ^ 2) ^ (r + 1) : ℝ) : ℂ) = (normalizedPrimeArchMoment r : ℂ) := by
    rw [hrepeated, Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [Complex.ofReal_tsum]
    simp_rw [Complex.ofReal_pow]
    simpa only [Complex.ofReal_pow] using
      (show 2 * (∑' n : ℕ, (((approxNumber A n ^ 2 : ℝ) : ℂ) ^ (r + 1))) =
        (normalizedPrimeArchMoment r : ℂ) from
          (congrArg (fun z : ℂ => 2 * z)
            (opTrace_energyOp_pow_eq_approxNumber_moments hAHS r)).symm.trans (hm r))
  exact not_summable_nonneg_primeArch_square_moments hb hb0 hba
    (fun r => Complex.ofReal_injective (hbmom r))

namespace HedenmalmThetaSource

local instance : ContinuousFunctionalCalculus ℝ
    (GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert)
      IsSelfAdjoint := IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Exact C1 all-moment landing is impossible even after the global mean correction.
This is the literal factor-two Xi normalization, not an undoubled surrogate. -/
theorem not_gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_exact_primeArch_moments :
    ¬ (∀ r : ℕ, 2 * opTrace
      (gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator ^ (r + 1)) =
        (normalizedPrimeArchMoment r : ℂ)) := by
  let T := gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator
  let A := CFC.sqrt T
  have hA : MemSchattenClass 1 A :=
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_sqrt_memSchattenClass_one
  have hstar : adjoint A = A := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)
  have henergy : energyOp A = T := by
    change adjoint A ∘L A = T
    rw [hstar]
    exact CFC.sqrt_mul_sqrt_self T
      ((ContinuousLinearMap.nonneg_iff_isPositive _).2
        gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_isPositive)
  simpa only [henergy, T] using not_nuclear_half_normalized_primeArch_energy_moments hA

end HedenmalmThetaSource
end RHTower
