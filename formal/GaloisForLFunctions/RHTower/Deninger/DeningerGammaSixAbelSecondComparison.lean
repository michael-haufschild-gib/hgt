import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixCriticalAbelReader
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Second Abel boundary comparison and complete correction recovery

The complete integral source has reciprocal principal diagonal plus a
summable arithmetic correction. Its second normalized discrepancy from
the existing physical BV boundary is the correction's divisibility sum
multiplied by log(n). All nontrivial ordinary boundary coefficients and
the scalar first variation jointly recover every diagonal correction.

For the actual source, full second-order agreement is equivalent to a
zero retained Xi coefficient. At multiplicity-top order the complete
arithmetic tail remains detectable after every finite diagonal repair.
These are actual source and boundary limits before divisor specialization;
no reader-agreement or RH premise is introduced. They do not identify a
Sonin transport or the reader at a divisor's original horizontal position.
-/

open Complex Real Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem deningerOrdinaryIntegerGibbsDiagonal_abel
    (ε : ℝ) (T : DeningerOrdinaryIntegerEnd) (k : PNat) :
    deningerOrdinaryIntegerGibbsDiagonal ((1 + ε) / 2) k T =
      ((((k : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) * deningerOrdinaryIntegerDiagonalCoefficient k T := by
  change ((deningerOrdinaryIntegerGibbsMass ((1 + ε) / 2) k : ℂ) * ((k : ℕ) : ℂ)) * _ = _
  have hw := congrArg Complex.ofReal (deningerOrdinaryIntegerGibbsWeight_abel ε k)
  push_cast at hw
  rw [hw]

theorem tendsto_deningerOrdinaryIntegerGibbsTrace_summable_abel
    (T : DeningerOrdinaryIntegerEnd)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k T)) :
    Tendsto (fun ε : ℝ => ∑' k : PNat, deningerOrdinaryIntegerGibbsDiagonal ((1 + ε) / 2) k T)
      (𝓝[>] 0) (𝓝 (∑' k : PNat, deningerOrdinaryIntegerDiagonalCoefficient k T)) := by
  apply tendsto_tsum_of_dominated_convergence hs.norm
  · intro k
    have hc : ContinuousAt (fun ε : ℝ =>
        ((((k : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) * deningerOrdinaryIntegerDiagonalCoefficient k T) 0 := by
      fun_prop (disch := positivity)
    simpa only [deningerOrdinaryIntegerGibbsDiagonal_abel, neg_zero, Real.rpow_zero,
      Complex.ofReal_one, one_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact norm_deningerOrdinaryIntegerGibbsDiagonal_le (by change 0 < ε at hε; linarith) T

/-- The first normalized variation recovers the total, complete correction. -/
theorem tendsto_deningerOrdinaryIntegerAbelReader_summable_slope
    (T : DeningerOrdinaryIntegerEnd)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k T)) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelReader ε T / (ε : ℂ)) (𝓝[>] 0)
      (𝓝 (∑' k : PNat, deningerOrdinaryIntegerDiagonalCoefficient k T)) := by
  have hz := (Complex.continuous_ofReal.continuousAt.tendsto.comp
    tendsto_deningerOrdinaryIntegerGibbsPartition_abel_residue).inv₀
      (by norm_num : ((1 : ℝ) : ℂ) ≠ 0)
  have ht := hz.mul (tendsto_deningerOrdinaryIntegerGibbsTrace_summable_abel T hs)
  simp only [Complex.ofReal_one, inv_one, one_mul] at ht
  convert ht using 1
  funext ε
  simp only [deningerOrdinaryIntegerAbelReader, Function.comp_apply, Complex.ofReal_mul,
    mul_inv_rev, div_eq_mul_inv]
  ring

theorem deningerOrdinaryIntegerSummableDiagonal_rightProjection
    (T : DeningerOrdinaryIntegerEnd)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k T)) (n : PNat) :
    Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T * deningerOrdinaryIntegerDivisibilityProjection n)) := by
  simpa only [deningerOrdinaryIntegerDiagonalCoefficient_rightProjection,
    Set.indicator_apply, Set.mem_setOf_eq] using! hs.indicator {k : PNat | n ∣ k}

theorem tendsto_deningerOrdinaryIntegerAbelReader_summable_projection_slope
    (T : DeningerOrdinaryIntegerEnd)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k T)) (n : PNat) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelReader ε
      (T * deningerOrdinaryIntegerDivisibilityProjection n) / (ε : ℂ)) (𝓝[>] 0)
      (𝓝 (∑' k : PNat, if n ∣ k then deningerOrdinaryIntegerDiagonalCoefficient k T else 0)) := by
  simpa only [deningerOrdinaryIntegerDiagonalCoefficient_rightProjection] using
    tendsto_deningerOrdinaryIntegerAbelReader_summable_slope _
      (deningerOrdinaryIntegerSummableDiagonal_rightProjection T hs n)

theorem deningerOrdinaryIntegerAbelDefect_green_physical
    {ε : ℝ} (hε : 0 < ε) (n : PNat) :
    deningerOrdinaryIntegerAbelDefect ε n deningerOrdinaryIntegerReciprocalGreen =
      (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (((1 + ε) / 2 : ℝ) : ℂ) : ℂ) := by
  have hσ : 1 / 2 < (1 + ε) / 2 := by linarith
  have hp : deningerOrdinaryIntegerAbelReader ε
      (deningerOrdinaryIntegerDivisibilityProjection n * deningerOrdinaryIntegerReciprocalGreen) =
      (deningerOrdinaryIntegerGibbsMass ((1 + ε) / 2) n : ℂ) :=
    deningerOrdinaryIntegerGibbsReader_projectionGreen hσ n
  rw [deningerOrdinaryIntegerAbelDefect,
    deningerOrdinaryIntegerWoldBackward_reciprocalGreen_WoldShift,
    deningerOrdinaryIntegerAbelReader_smul, deningerOrdinaryIntegerAbelReader_green hε, mul_one,
    ← deningerOrdinaryIntegerDivisibilityProjection_commutes_reciprocalGreen, hp]
  have hx := deningerOrdinaryIntegerGibbsReader_eq_physicalBV n (((1 + ε) / 2 : ℝ) : ℂ) hσ
  simp only [Complex.ofReal_re] at hx
  rw [deningerOrdinaryIntegerGibbsReader_boundary hσ n] at hx
  exact hx

theorem deningerOrdinaryIntegerAbelDefect_smul
    (ε : ℝ) (n : PNat) (c : ℂ) (T : DeningerOrdinaryIntegerEnd) :
    deningerOrdinaryIntegerAbelDefect ε n (c • T) =
      c * deningerOrdinaryIntegerAbelDefect ε n T := by
  simp only [deningerOrdinaryIntegerAbelDefect, smul_mul_assoc, mul_smul_comm,
    deningerOrdinaryIntegerAbelReader_smul]
  ring

theorem deningerOrdinaryIntegerAbelDefect_sub
    {ε : ℝ} (T U : deningerOrdinaryIntegerGibbsDomain ((1 + ε) / 2)) (n : PNat) :
    deningerOrdinaryIntegerAbelDefect ε n (T.val - U.val) =
      deningerOrdinaryIntegerAbelDefect ε n T.val - deningerOrdinaryIntegerAbelDefect ε n U.val := by
  have hc := deningerOrdinaryIntegerAbelReader_sub
    ⟨_, deningerOrdinaryIntegerGibbsDomain_compression T n⟩
    ⟨_, deningerOrdinaryIntegerGibbsDomain_compression U n⟩
  have hp := deningerOrdinaryIntegerAbelReader_sub
    ⟨_, deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩
    ⟨_, deningerOrdinaryIntegerGibbsDomain_rightProjection U n⟩
  simp only [deningerOrdinaryIntegerAbelDefect, sub_mul, mul_sub, hc, hp]
  ring

/-- The complete correction measured by the second physical boundary discrepancy. -/
def deningerOrdinaryIntegerAbelSecondCoefficient (n : PNat) (T : DeningerOrdinaryIntegerEnd) (c : ℂ) : ℂ :=
  (Real.log ((n : ℕ) : ℝ) : ℂ) *
    ∑' k : PNat, if n ∣ k then deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen) else 0

theorem deningerOrdinaryIntegerAbelDefect_sub_physical_eq_correction
    {ε : ℝ} (hε : 0 < ε) (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) (n : PNat) :
    deningerOrdinaryIntegerAbelDefect ε n T -
      c * (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (((1 + ε) / 2 : ℝ) : ℂ) : ℂ) =
        deningerOrdinaryIntegerAbelDefect ε n (T - c • deningerOrdinaryIntegerReciprocalGreen) := by
  have hσ : 1 / 2 < (1 + ε) / 2 := by linarith
  have hT := deningerOrdinaryIntegerPrincipalClass_mem_gibbsDomain hσ T c hs
  have hQ := (deningerOrdinaryIntegerGibbsDomain ((1 + ε) / 2)).smul_mem c
    ((deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff _).2 hσ)
  rw [deningerOrdinaryIntegerAbelDefect_sub ⟨T, hT⟩ ⟨_, hQ⟩ n,
    deningerOrdinaryIntegerAbelDefect_smul, deningerOrdinaryIntegerAbelDefect_green_physical hε]

/-- The second physical discrepancy is the full arithmetic correction's divisibility readout. -/
theorem tendsto_deningerOrdinaryIntegerAbelDefect_second
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) (n : PNat) :
    Tendsto (fun ε : ℝ => (deningerOrdinaryIntegerAbelDefect ε n T -
      c * (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (((1 + ε) / 2 : ℝ) : ℂ) : ℂ)) /
        (ε : ℂ)^(2 : ℕ)) (𝓝[>] 0) (𝓝 (deningerOrdinaryIntegerAbelSecondCoefficient n T c)) := by
  have hg := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_deningerOrdinaryIntegerAbelGain_slope n)
  have ht := hg.mul (tendsto_deningerOrdinaryIntegerAbelReader_summable_projection_slope _ hs n)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hσ : 1 / 2 < (1 + ε) / 2 := by change 0 < ε at hε; linarith
  have hR := deningerOrdinaryIntegerSummableDiagonal_mem_gibbsDomain hσ.le _ hs
  rw [deningerOrdinaryIntegerAbelDefect_sub_physical_eq_correction hε T c hs n,
    deningerOrdinaryIntegerAbelDefect_eq ⟨_, hR⟩ n]
  simp only [Function.comp_apply, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- The total complete correction, measured by the scalar first variation. -/
def deningerOrdinaryIntegerAbelCorrectionMass (T : DeningerOrdinaryIntegerEnd) (c : ℂ) : ℂ :=
  ∑' k : PNat, deningerOrdinaryIntegerDiagonalCoefficient k
    (T - c • deningerOrdinaryIntegerReciprocalGreen)

theorem tendsto_deningerOrdinaryIntegerAbelReader_principal_slope
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) :
    Tendsto (fun ε : ℝ => (deningerOrdinaryIntegerAbelReader ε T - c) / (ε : ℂ))
      (𝓝[>] 0) (𝓝 (deningerOrdinaryIntegerAbelCorrectionMass T c)) := by
  apply (tendsto_deningerOrdinaryIntegerAbelReader_summable_slope _ hs).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [deningerOrdinaryIntegerAbelReader_principal_decomposition hε T c hs]
  ring

theorem deningerOrdinaryIntegerAbelSecondCoefficient_eq_iff
    (n : PNat) (hn : n ≠ 1) (T U : DeningerOrdinaryIntegerEnd) (c d : ℂ) :
    deningerOrdinaryIntegerAbelSecondCoefficient n T c =
      deningerOrdinaryIntegerAbelSecondCoefficient n U d ↔
    (∑' k : PNat, if n ∣ k then deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen) else 0) =
    (∑' k : PNat, if n ∣ k then deningerOrdinaryIntegerDiagonalCoefficient k
      (U - d • deningerOrdinaryIntegerReciprocalGreen) else 0) := by
  have hnNat : 1 < (n : ℕ) := by
    have hp := n.pos
    have hne : (n : ℕ) ≠ 1 := fun h => hn (Subtype.ext h)
    omega
  have hlog : (Real.log ((n : ℕ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hnNat)).ne'
  constructor
  · exact mul_left_cancel₀ hlog
  · intro heq
    unfold deningerOrdinaryIntegerAbelSecondCoefficient
    rw [heq]

theorem deningerOrdinaryIntegerAbelSecondCoefficient_zero_iff
    (n : PNat) (hn : n ≠ 1) (T : DeningerOrdinaryIntegerEnd) (c : ℂ) :
    deningerOrdinaryIntegerAbelSecondCoefficient n T c = 0 ↔
      (∑' k : PNat, if n ∣ k then deningerOrdinaryIntegerDiagonalCoefficient k
        (T - c • deningerOrdinaryIntegerReciprocalGreen) else 0) = 0 := by
  have hx := deningerOrdinaryIntegerAbelSecondCoefficient_eq_iff n hn T 0 c 0
  simpa only [deningerOrdinaryIntegerAbelSecondCoefficient, zero_smul, sub_zero,
    map_zero, ite_self, tsum_zero, mul_zero] using hx

/-- Boundary second coefficients recover the entire nonunit correction. -/
theorem deningerOrdinaryIntegerAbelSecondCoefficient_zero_iff_unit
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) :
    (∀ n : PNat, n ≠ 1 → deningerOrdinaryIntegerAbelSecondCoefficient n T c = 0) ↔
      ∀ k : PNat, k ≠ 1 → deningerOrdinaryIntegerDiagonalCoefficient k
        (T - c • deningerOrdinaryIntegerReciprocalGreen) = 0 := by
  constructor
  · intro hz
    exact pnatDivisibility_summable_supported_unit _ hs
      (fun n hn => (deningerOrdinaryIntegerAbelSecondCoefficient_zero_iff n hn T c).1 (hz n hn))
  · intro hz n hn
    apply (deningerOrdinaryIntegerAbelSecondCoefficient_zero_iff n hn T c).2
    apply (tsum_congr (g := fun _ : PNat => (0 : ℂ)) ?_).trans tsum_zero
    intro k
    split_ifs with hnk
    · apply hz k
      intro hk
      subst k
      exact hn (PNat.dvd_antisymm hnk (one_dvd n))
    · rfl

/-- The scalar first variation and every nontrivial boundary second coefficient
jointly determine every correction coefficient, including the unit. -/
theorem deningerOrdinaryIntegerAbelJet_correction_injective
    (T U : DeningerOrdinaryIntegerEnd) (c d : ℂ)
    (hT : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen)))
    (hU : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (U - d • deningerOrdinaryIntegerReciprocalGreen)))
    (hm : deningerOrdinaryIntegerAbelCorrectionMass T c = deningerOrdinaryIntegerAbelCorrectionMass U d)
    (hj : ∀ n : PNat, n ≠ 1 → deningerOrdinaryIntegerAbelSecondCoefficient n T c =
      deningerOrdinaryIntegerAbelSecondCoefficient n U d) :
    (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen)) =
    (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (U - d • deningerOrdinaryIntegerReciprocalGreen)) := by
  apply pnatDivisibility_summable_injective _ _ hT hU
  intro n
  by_cases hn : n = 1
  · subst n
    simpa only [deningerOrdinaryIntegerAbelCorrectionMass, one_dvd, if_true] using! hm
  · exact (deningerOrdinaryIntegerAbelSecondCoefficient_eq_iff n hn T U c d).1 (hj n hn)

theorem deningerOrdinaryIntegerAbelSecondCoefficient_ne_zero_of_nonunit
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen)))
    (k : PNat) (hk : k ≠ 1)
    (hc : deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen) ≠ 0) :
    ∃ n : PNat, n ≠ 1 ∧ deningerOrdinaryIntegerAbelSecondCoefficient n T c ≠ 0 := by
  by_contra h
  push Not at h
  exact hc ((deningerOrdinaryIntegerAbelSecondCoefficient_zero_iff_unit T c hs).1 h k hk)

theorem tendsto_deningerGammaSixIntegral_abel_second
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) (n : PNat) :
    Tendsto (fun ε : ℝ => (deningerOrdinaryIntegerAbelDefect ε n
      (deningerGammaSixIntegralOperator k l w z) -
      (iteratedDeriv k XiC w * iteratedDeriv l XiC z) *
        (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (((1 + ε) / 2 : ℝ) : ℂ) : ℂ)) /
          (ε : ℂ)^(2 : ℕ)) (𝓝[>] 0)
      (𝓝 (deningerOrdinaryIntegerAbelSecondCoefficient n
        (deningerGammaSixIntegralOperator k l w z) (iteratedDeriv k XiC w * iteratedDeriv l XiC z))) :=
  tendsto_deningerOrdinaryIntegerAbelDefect_second _ _
    (deningerGammaSixIntegralOperator_principal_class k l hw hz hrw hrz) n

/-- The coefficient is the literal complete remainder beyond the exact finite placement. -/
theorem deningerGammaSixIntegralCorrection_tail
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) (n : ℕ) :
    deningerOrdinaryIntegerDiagonalCoefficient ⟨n + 216, by omega⟩
      (deningerGammaSixIntegralOperator k l w z -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC z) • deningerOrdinaryIntegerReciprocalGreen) =
      deningerGammaSixIntegralRemainder k l w z n := by
  simp only [map_sub, map_smul, smul_eq_mul,
    deningerOrdinaryIntegerDiagonalCoefficient_integralOperator,
    deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen]
  change deningerGammaSixIntegralNatColumn k l w z (n + 216) -
    (iteratedDeriv k XiC w * iteratedDeriv l XiC z) * (((n + 216 : ℕ) : ℂ))⁻¹ = _
  rw [deningerGammaSixIntegralNatColumn, if_pos (by omega : 216 ≤ n + 216), Nat.add_sub_cancel,
    deningerGammaSixIntegralColumn_decomposition k l hw hz hrw hrz]
  push_cast
  ring

theorem deningerGammaSixIntegralRemainder_ne_zero
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0) (n : ℕ)
    (hM : deningerGammaSixTensorRemainderMultiplier (deningerGammaSixShellDepth n) w w ≠ 0) :
    deningerGammaSixIntegralRemainder k l w w n ≠ 0 := by
  have ha := deningerGammaSixIntegral_every_depth_admitted (deningerGammaSixShellHonestDepth n) hrw
  rw [deningerGammaSixIntegralRemainder,
    (deningerGammaSixInternalJetTensorRemainder_fourierLaplace_data k l _ hw hw ha ha).2]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (deningerGammaSixShellFlattening_pos n).ne')
    (mul_ne_zero (mul_ne_zero
      (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (deningerGammaSixHalfWeight_pos _).ne')) hM) hc)

/-- The exact source correction has nonzero coefficients arbitrarily far out.
This statement survives removal or replacement of every finite initial head. -/
theorem deningerGammaSixIntegralCorrection_nonzero_above
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0) (N : ℕ) :
    ∃ a : PNat, N < (a : ℕ) ∧ deningerOrdinaryIntegerDiagonalCoefficient a
      (deningerGammaSixIntegralOperator k l w w -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) ≠ 0 := by
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (eventually_deningerGammaSixTensorRemainderMultiplier_diagonal_ne_zero (by linarith))
  let m := N + M + 3
  have hm3 : 3 ≤ m := by omega
  have hMm : M ≤ m := by omega
  have hmN : N ≤ m := by omega
  have hpow : m < 6 ^ m := Nat.lt_pow_self (by norm_num)
  refine ⟨⟨6 ^ m + 216, by omega⟩, by change N < 6 ^ m + 216; omega, ?_⟩
  rw [deningerGammaSixIntegralCorrection_tail k l hw hw hrw hrw]
  apply deningerGammaSixIntegralRemainder_ne_zero k l hw hrw hc
  simpa only [deningerGammaSixShellDepth_pow m hm3] using hM m hMm

/-- No finite diagonal counterterm eliminates the surviving arithmetic tail. -/
theorem deningerGammaSixIntegralCorrection_finite_repair_nonzero
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0)
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    ∃ a : PNat, a ≠ 1 ∧ deningerOrdinaryIntegerDiagonalCoefficient a
      ((deningerGammaSixIntegralOperator k l w w + F) -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) ≠ 0 := by
  obtain ⟨N, hN⟩ := hF.bddAbove
  obtain ⟨a, ha, hra⟩ := deningerGammaSixIntegralCorrection_nonzero_above k l hw hrw hc (N : ℕ)
  have haF : deningerOrdinaryIntegerDiagonalCoefficient a F = 0 := by
    by_contra hne
    have hle : a ≤ N := hN hne
    change (a : ℕ) ≤ (N : ℕ) at hle
    omega
  have ha1 : a ≠ 1 := by
    intro heq
    subst a
    have hp := N.pos
    change (N : ℕ) < 1 at ha
    omega
  refine ⟨a, ha1, ?_⟩
  simpa only [map_sub, map_add, haF, add_zero] using hra


theorem deningerOrdinaryIntegerAbelDefect_second_zero_iff
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) (n : PNat) :
    Tendsto (fun ε : ℝ => (deningerOrdinaryIntegerAbelDefect ε n T -
      c * (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (((1 + ε) / 2 : ℝ) : ℂ) : ℂ)) /
        (ε : ℂ)^(2 : ℕ)) (𝓝[>] 0) (𝓝 0) ↔ deningerOrdinaryIntegerAbelSecondCoefficient n T c = 0 := by
  constructor
  · intro h
    exact tendsto_nhds_unique (tendsto_deningerOrdinaryIntegerAbelDefect_second T c hs n) h
  · intro h
    simpa only [h] using tendsto_deningerOrdinaryIntegerAbelDefect_second T c hs n

theorem deningerGammaSixIntegral_finite_repair_principal_class
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re)
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    Summable (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a
      ((deningerGammaSixIntegralOperator k l w z + F) -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC z) • deningerOrdinaryIntegerReciprocalGreen)) := by
  have hsF : Summable (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F) :=
    summable_of_hasFiniteSupport hF
  apply ((deningerGammaSixIntegralOperator_principal_class k l hw hz hrw hrz).add hsF).congr
  intro a
  simp only [map_sub, map_add]
  ring

theorem deningerGammaSixIntegral_finite_repair_second_nonzero
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0)
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    ∃ n : PNat, n ≠ 1 ∧ deningerOrdinaryIntegerAbelSecondCoefficient n
      (deningerGammaSixIntegralOperator k l w w + F) (iteratedDeriv k XiC w * iteratedDeriv l XiC w) ≠ 0 := by
  obtain ⟨a, ha, hca⟩ := deningerGammaSixIntegralCorrection_finite_repair_nonzero k l hw hrw hc F hF
  exact deningerOrdinaryIntegerAbelSecondCoefficient_ne_zero_of_nonunit _ _
    (deningerGammaSixIntegral_finite_repair_principal_class k l hw hw hrw hrw F hF) a ha hca

/-- Full second-order agreement is sharp for the actual every-depth integral source. -/
theorem deningerGammaSixIntegral_second_coefficients_zero_iff
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) :
    (∀ n : PNat, n ≠ 1 → deningerOrdinaryIntegerAbelSecondCoefficient n
      (deningerGammaSixIntegralOperator k l w z) (iteratedDeriv k XiC w * iteratedDeriv l XiC z) = 0) ↔
      iteratedDeriv k XiC w * iteratedDeriv l XiC z = 0 := by
  constructor
  · intro h
    have hunit := (deningerOrdinaryIntegerAbelSecondCoefficient_zero_iff_unit _ _
      (deningerGammaSixIntegralOperator_principal_class k l hw hz hrw hrz)).1 h
    have htwo := hunit (2 : PNat) (by norm_num)
    simp only [map_sub, map_smul, smul_eq_mul,
      deningerOrdinaryIntegerDiagonalCoefficient_integralOperator,
      deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen] at htwo
    norm_num [deningerGammaSixIntegralDiagonal, deningerGammaSixIntegralNatColumn] at htwo
    exact mul_eq_zero.mpr htwo
  · intro hc n _
    rw [deningerGammaSixIntegralOperator_eq_zero k l hw hz hrw hrz hc, hc]
    simp only [deningerOrdinaryIntegerAbelSecondCoefficient, zero_smul, sub_zero,
      map_zero, ite_self, tsum_zero, mul_zero]

theorem deningerGammaSixIntegral_second_order_agreement_iff
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) :
    (∀ n : PNat, n ≠ 1 → Tendsto (fun ε : ℝ =>
      (deningerOrdinaryIntegerAbelDefect ε n (deningerGammaSixIntegralOperator k l w z) -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC z) *
          (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (((1 + ε) / 2 : ℝ) : ℂ) : ℂ)) /
            (ε : ℂ)^(2 : ℕ)) (𝓝[>] 0) (𝓝 0)) ↔ iteratedDeriv k XiC w * iteratedDeriv l XiC z = 0 := by
  have hlim := fun n => deningerOrdinaryIntegerAbelDefect_second_zero_iff _ _
    (deningerGammaSixIntegralOperator_principal_class k l hw hz hrw hrz) n
  simp_rw [hlim]
  exact deningerGammaSixIntegral_second_coefficients_zero_iff k l hw hz hrw hrz

/-- Every finite diagonal repair of an admitted multiplicity-top source still
fails second-order comparison at some ordinary dilation. No RH premise is used. -/
theorem deningerGammaSixIntegral_top_finite_repair_second_obstruction
    (rho : XiDivisorSupport) (hrho : (1 / 3 : ℝ) < (rho : ℂ).re)
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    ∃ n : PNat, n ≠ 1 ∧ ¬ Tendsto (fun ε : ℝ =>
      (deningerOrdinaryIntegerAbelDefect ε n
        (deningerGammaSixIntegralOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho)
          (xiSpectralPointSupport rho) (xiSpectralPointSupport rho) + F) -
        (iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho) *
          iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho)) *
            (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (((1 + ε) / 2 : ℝ) : ℂ) : ℂ)) /
              (ε : ℂ)^(2 : ℕ)) (𝓝[>] 0) (𝓝 0) := by
  have hw := abs_im_xiSpectralPointSupport_lt_one rho
  have hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    simpa only [mobiusThetaCenteredParameter_xiSpectralPointSupport] using hrho
  have hc := mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
    (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
  obtain ⟨n, hn, hcn⟩ := deningerGammaSixIntegral_finite_repair_second_nonzero _ _ hw hrw hc F hF
  refine ⟨n, hn, ?_⟩
  intro hz
  exact hcn ((deningerOrdinaryIntegerAbelDefect_second_zero_iff _ _
    (deningerGammaSixIntegral_finite_repair_principal_class _ _ hw hw hrw hrw F hF) n).1 hz)

end
end RHTower
