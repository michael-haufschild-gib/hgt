import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExponentialBarrierPrimeComparison
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExponentialBarrierPoleComparison
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExponentialBarrierPotential
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExponentialBarrierGammaComparison

/-!
# Exponential comparison for confining half-line minimizers

The confining potential and divergent cutoff Gamma row absorb the complete
prime and polar terms. The weak equation forces a high exponential positive
level to vanish. Both signs give exponential envelopes and square moments
of every order below fifteen.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory HTGeometry

/-- Negation preserves the normalized minimizing line. -/
theorem IsHalfLineEnergyMinimizer.neg {R : ℝ} {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) :
    IsHalfLineEnergyMinimizer R (fun u => -F u) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [neg_one_mul] using hF.1.const_mul (-1)
  · simpa only [neg_sq] using hF.2.1
  · have he := criticalHalfLineFullEnergy_const_mul R F (-1)
    have hsq : (-1 : ℝ) ^ 2 = 1 := by norm_num
    simp only [neg_one_mul, hsq, one_mul] at he
    exact he.trans hF.2.2

/-- Terminal support turns the weak equation into a full-line diagonal row identity. -/
theorem IsHalfLineEnergyMinimizer.weakEquation_rows {R : ℝ} (hR : 0 < R)
    {F G : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F)
    (hG : CriticalHalfLineEnergyDomain G) :
    gammaMixedForm F G +
      (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G) +
      criticalAliasCoefficient R * (∫ u, F u * G u * Real.exp (-(8 * u))) =
      criticalHalfLineGroundEnergy R * (∫ u, F u * G u) + primeMixedForm F G := by
  have hsupport : (∫ u in Iio 0, F u * G u * Real.exp (-(8 * u))) =
      ∫ u, F u * G u * Real.exp (-(8 * u)) := by
    rw [← integral_indicator measurableSet_Iio]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      dsimp only
      by_cases hu : u ∈ Iio (0 : ℝ)
      · rw [indicator_of_mem hu]
      · rw [indicator_of_notMem hu, hF.1.support u (le_of_not_gt hu), zero_mul, zero_mul]
  have he := hF.weakEquation hR hG
  unfold criticalHalfLineMixedEnergy at he
  rw [primeMixedForm_symm G F, hsupport] at he
  linarith only [he]

/-- The full weak equation forces a sufficiently high exponential positive level to vanish. -/
theorem IsHalfLineEnergyMinimizer.exists_exponential_upper_bound {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) {β : ℝ}
    (hβ : 1 / 2 < β) (hβupper : β < 15 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ u ∂volume, F u ≤ C * Real.exp (β * u) := by
  have hβ0 : 0 < β := by linarith only [hβ]
  obtain ⟨B, _hB, hcoercive⟩ := exists_exponentialBarrier_diagonalCoercivity
    (criticalAliasCoefficient_positive hR) hβ hβupper (halfLineExponentialPrimeTail β)
  -- The cutoff fixes a coercive diagonal independently of the positive level.
  obtain ⟨δ, hδ, hδ1, hmass⟩ := exists_halfLineGamma_cutoffMass_gt
    (B + halfLineBarrierSmallJumpConstant β + 2 * |gammaHardyPhaseRate 0| +
      criticalHalfLineGroundEnergy R)
  let k : ℝ := (2 * ∫ h in Ioi δ, archLevyDensity h) -
    halfLineBarrierSmallJumpConstant β - 2 * |gammaHardyPhaseRate 0| -
      criticalHalfLineGroundEnergy R
  have hk : B ≤ k := by dsimp only [k]; linarith only [hmass]
  let D : ℝ := 2 * Real.sqrt ((∫ h in Ioi δ, archLevyDensity h ^ 2) * ∫ u, F u ^ 2)
  let P : ℝ := halfLinePoleReadoutSize F
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hP : 0 ≤ P := halfLinePoleReadoutSize_nonneg F
  let t : ℝ := D + P
  have ht : 0 ≤ t := add_nonneg hD hP
  have hDt : D ≤ t := le_add_of_nonneg_right hP
  have hPt : P ≤ t := le_add_of_nonneg_left hD
  let G := exponentialBarrierPositiveLevel β t F
  have hG : CriticalHalfLineEnergyDomain G := hF.1.exponentialBarrierPositiveLevel_mem hβ0 ht
  have hG0 (u : ℝ) : 0 ≤ G u := (exponentialBarrierPositiveLevel_le_abs ht β F u).1
  let A : ℝ → ℝ := fun u => criticalAliasCoefficient R * Real.exp (-(8 * u)) + k -
    (6 * Real.exp (-((β + 1 / 2) * u)) + halfLineExponentialPrimeTail β)
  have hpair : Integrable (fun u => F u * G u) := hF.1.memLp_real.integrable_mul hG.memLp_real
  have hpot : Integrable (fun u => F u * G u * Real.exp (-(8 * u))) :=
    hF.1.integrable_mul_exponentialBarrierPositiveLevel ht le_rfl β
  have hrow : Integrable (fun u =>
      (6 * Real.exp (-((β + 1 / 2) * u)) + halfLineExponentialPrimeTail β) * (F u * G u)) :=
    hF.1.integrable_exponentialBarrier_primeRow (by linarith only [hβupper]) ht
  have hA : Integrable (fun u => A u * (F u * G u)) := by
    apply (((hpot.const_mul (criticalAliasCoefficient R)).add (hpair.const_mul k)).sub hrow).congr
    exact Eventually.of_forall fun u => by dsimp only [A]; ring
  have hAint : (∫ u, A u * (F u * G u)) =
      criticalAliasCoefficient R * (∫ u, F u * G u * Real.exp (-(8 * u))) +
        k * (∫ u, F u * G u) -
        ∫ u, (6 * Real.exp (-((β + 1 / 2) * u)) + halfLineExponentialPrimeTail β) * (F u * G u) := by
    calc
      _ = ∫ u, (criticalAliasCoefficient R * (F u * G u * Real.exp (-(8 * u))) +
          k * (F u * G u)) -
          (6 * Real.exp (-((β + 1 / 2) * u)) + halfLineExponentialPrimeTail β) * (F u * G u) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun u => by dsimp only [A]; ring
      _ = (∫ u, criticalAliasCoefficient R * (F u * G u * Real.exp (-(8 * u))) +
          k * (F u * G u)) -
          ∫ u, (6 * Real.exp (-((β + 1 / 2) * u)) + halfLineExponentialPrimeTail β) * (F u * G u) :=
        integral_sub ((hpot.const_mul (criticalAliasCoefficient R)).add (hpair.const_mul k)) hrow
      _ = _ := by
        rw [integral_add (hpot.const_mul (criticalAliasCoefficient R)) (hpair.const_mul k),
          integral_const_mul, integral_const_mul]
  have hforce : Integrable (fun u => (D + P * Real.exp (-(u / 2))) * G u) := by
    apply ((hG.integrable.const_mul D).add (hG.integrable_polarExponential.const_mul P)).congr
    exact Eventually.of_forall fun u => by dsimp only; ring
  have hforceint : (∫ u, (D + P * Real.exp (-(u / 2))) * G u) =
      D * (∫ u, G u) + P * (∫ u, G u * Real.exp (-(u / 2))) := by
    calc
      _ = ∫ u, D * G u + P * (G u * Real.exp (-(u / 2))) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun u => by dsimp only; ring
      _ = _ := by
        rw [integral_add (hG.integrable.const_mul D) (hG.integrable_polarExponential.const_mul P),
          integral_const_mul, integral_const_mul]
  let J : ℝ → ℝ := fun u => A u * (F u * G u) - (D + P * Real.exp (-(u / 2))) * G u
  have hJ : Integrable J := hA.sub hforce
  -- The weak equation bounds the absorbed pairing above by zero.
  have hupper : (∫ u, J u) ≤ 0 := by
    have hgamma := hF.1.exponentialBarrier_gammaMixed_lower hβ0 ht hδ hδ1.le
    have hprime := hF.1.primeMixedForm_exponentialBarrier_le hβ hβupper ht
    have hpole := halfLine_polarMixedForm_lower F hG hG0
    have heq := hF.weakEquation_rows hR hG
    change ((2 * ∫ h in Ioi δ, archLevyDensity h) -
      halfLineBarrierSmallJumpConstant β - 2 * |gammaHardyPhaseRate 0|) *
      (∫ u, F u * G u) - D * (∫ u, G u) ≤ gammaMixedForm F G at hgamma
    change primeMixedForm F G ≤
      ∫ u, (6 * Real.exp (-((β + 1 / 2) * u)) + halfLineExponentialPrimeTail β) *
        (F u * G u) at hprime
    change -P * (∫ u, G u * Real.exp (-(u / 2))) ≤ _ at hpole
    change (∫ u, A u * (F u * G u) - (D + P * Real.exp (-(u / 2))) * G u) ≤ 0
    rw [integral_sub hA hforce, hAint, hforceint]
    dsimp only [k]
    linarith only [hgamma, hprime, hpole, heq]
  -- Diagonal coercivity makes that same pairing dominate the test's square mass.
  have hlower : (∫ u, G u ^ 2) ≤ ∫ u, J u := by
    apply integral_mono hG.sq hJ
    intro u
    by_cases hu : u ≤ 0
    · obtain ⟨hA1, hAp⟩ := hcoercive k hk u hu
      have hh := weighted_positiveLevel_coercivity hA1 hAp
        (Real.exp_pos (-(u / 2))).le ht hDt hPt (F u)
      change max (F u - t * Real.exp (β * u)) 0 ^ 2 ≤
        A u * (F u * max (F u - t * Real.exp (β * u)) 0) -
          (D + P * Real.exp (-(u / 2))) * max (F u - t * Real.exp (β * u)) 0 at hh
      simpa only [G, J, hF.1.exponentialBarrierPositiveLevel_eq ht] using hh
    · have hz := hG.support u (lt_of_not_ge hu).le
      change G u ^ 2 ≤ A u * (F u * G u) - (D + P * Real.exp (-(u / 2))) * G u
      rw [hz, zero_pow two_ne_zero, mul_zero, mul_zero, mul_zero, sub_self]
  have hsquare : (∫ u, G u ^ 2) = 0 :=
    le_antisymm (hlower.trans hupper) (integral_nonneg fun u => sq_nonneg (G u))
  have hzero : G =ᵐ[volume] 0 := by
    have hh := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg (G u)) hG.sq).mp hsquare
    filter_upwards [hh] with u hu
    exact sq_eq_zero_iff.mp hu
  refine ⟨t, ht, ?_⟩
  filter_upwards [hzero] with u hu
  have hh := le_max_left (F u - t * Real.exp (β * u)) 0
  rw [← hF.1.exponentialBarrierPositiveLevel_eq ht β u] at hh
  have hu0 : G u = 0 := hu
  exact sub_nonpos.mp (hh.trans_eq hu0)

/-- Every confining minimizer has exponential envelopes for rates between one half and fifteen halves. -/
theorem IsHalfLineEnergyMinimizer.exists_exponential_barrier {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) {β : ℝ}
    (hβ : 1 / 2 < β) (hβupper : β < 15 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ u ∂volume, |F u| ≤ C * Real.exp (β * u) := by
  obtain ⟨C, hC, hc⟩ := hF.exists_exponential_upper_bound hR hβ hβupper
  obtain ⟨D, hD, hd⟩ := hF.neg.exists_exponential_upper_bound hR hβ hβupper
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  filter_upwards [hc, hd] with u hcu hdu
  have hce := mul_nonneg hC (Real.exp_pos (β * u)).le
  have hde := mul_nonneg hD (Real.exp_pos (β * u)).le
  dsimp only at hdu
  exact abs_le.mpr ⟨by nlinarith only [hdu, hce], by nlinarith only [hcu, hde]⟩

/-- Every confining minimizer has finite exponential square moments of all orders below fifteen. -/
theorem IsHalfLineEnergyMinimizer.integrable_exponential_square {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) {b : ℝ} (hb : b < 15) :
    Integrable (fun u => F u ^ 2 * Real.exp (-(b * u))) := by
  obtain ⟨β, hβ, hβupper, hbβ⟩ :
      ∃ β : ℝ, 1 / 2 < β ∧ β < 15 / 2 ∧ b < 2 * β := by
    by_cases hb1 : b ≤ 1
    · exact ⟨1, by norm_num, by norm_num, by linarith only [hb1]⟩
    · refine ⟨(b + 15) / 4, ?_, ?_, ?_⟩ <;> linarith only [hb, lt_of_not_ge hb1]
  obtain ⟨C, _hC, hc⟩ := hF.exists_exponential_barrier hR hβ hβupper
  have hr : 0 < 2 * β - b := sub_pos.mpr hbβ
  apply ((integrable_negativeHalfLineExponentialBarrier hr).const_mul (C ^ 2)).mono'
    ((hF.1.meas.pow_const 2).mul (by fun_prop)).aestronglyMeasurable
  filter_upwards [hc] with u hu
  change ‖F u ^ 2 * Real.exp (-(b * u))‖ ≤
    C ^ 2 * negativeHalfLineExponentialBarrier (2 * β - b) u
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg (F u)) (Real.exp_pos _).le)]
  by_cases hu0 : u ≤ 0
  · rw [negativeHalfLineExponentialBarrier, indicator_of_mem hu0]
    have hs := pow_le_pow_left₀ (abs_nonneg (F u)) hu 2
    rw [sq_abs, mul_pow] at hs
    have hh := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-(b * u))).le
    have he : Real.exp (β * u) ^ 2 * Real.exp (-(b * u)) =
        Real.exp ((2 * β - b) * u) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rwa [mul_assoc, he] at hh
  · rw [hF.1.support u (lt_of_not_ge hu0).le, zero_pow two_ne_zero, zero_mul,
      negativeHalfLineExponentialBarrier, indicator_of_notMem hu0, mul_zero]

/-- Every positive confinement has an actual normalized minimizer with all sub-fifteen square moments. -/
theorem exists_exponentially_bounded_halfLineEnergyMinimizer {R : ℝ} (hR : 0 < R) :
    ∃ F : ℝ → ℝ, IsHalfLineEnergyMinimizer R F ∧
      (∀ β : ℝ, 1 / 2 < β → β < 15 / 2 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ u ∂volume, |F u| ≤ C * Real.exp (β * u)) ∧
      ∀ b : ℝ, b < 15 → Integrable (fun u => F u ^ 2 * Real.exp (-(b * u))) := by
  obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
  exact ⟨F, hF, fun _ hβ hβupper => hF.exists_exponential_barrier hR hβ hβupper,
    fun _ hb => hF.integrable_exponential_square hR hb⟩

#print axioms IsHalfLineEnergyMinimizer.neg
#print axioms IsHalfLineEnergyMinimizer.weakEquation_rows
#print axioms IsHalfLineEnergyMinimizer.exists_exponential_upper_bound
#print axioms IsHalfLineEnergyMinimizer.exists_exponential_barrier
#print axioms IsHalfLineEnergyMinimizer.integrable_exponential_square
#print axioms exists_exponentially_bounded_halfLineEnergyMinimizer
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
