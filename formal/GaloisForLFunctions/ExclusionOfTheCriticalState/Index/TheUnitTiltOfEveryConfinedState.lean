import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheNullVectorsOfTheConfinedForm
import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheHeatedZeroPairingOfTwoProfilesIsWeilsForm
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTiltedStateLiesInTheEnergyDomainUpToTheRateOfTheZeros

/-!
# Absolute zero traces of every confined state

Testing the null equation with the square of a truncated exponential weight
bounds the jump energy and the confinement mass at the same time. The resulting
unit tilt controls square sampling at all zero copies, including an infinite
off-line divisor.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23 Complex
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations CriticalArithmeticCorrelationTheory
  ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

private def cutMass (F : ℝ → ℝ) (c N : ℝ) : ℝ :=
  ∫ u in Iio (0:ℝ), F u * (truncatedTilt (2*c) N u * F u) * Real.exp (-(8*u))

private def cutJump (F : ℝ → ℝ) (c N : ℝ) : ℝ :=
  ∫ x in Ioi (0:ℝ), archLevyDensity x *
    ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u+x) * F (u+x))^2

private theorem gamma_add_confinement_le {R : ℝ} {F : ℝ → ℝ} (hF : IsConfinedNullVector R F)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (N : ℝ) :
    gammaMixedForm F (fun u => truncatedTilt (2*c) N u * F u) +
        criticalAliasCoefficient R * cutMass F c N ≤
      2 * vonMangoldtThreeHalvesMass * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) +
        4 * (∫ u, |F u| * Real.exp (-(5 / 2) * u)) ^ 2 := by
  have hd := hF.1
  have h2c0 : (0 : ℝ) ≤ 2*c := by positivity
  have h2c2 : 2*c ≤ 2 := by linarith only [hc1]
  have h2c3 : 2*c ≤ 3 := by linarith only [hc1]
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hd h2c0 N
  have hw := hF.2.2 _ hG
  rw [criticalHalfLineMixedEnergy_eq_bare_add] at hw
  unfold bareMixedEnergy at hw
  unfold cutMass
  -- The ordinary weighted form controls both orientations of the prime pairing.
  have hE0 : 0 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hs1 := Real.sqrt_le_sqrt (exponentialSourceMass_le_exponential hd)
  have hs2 := Real.sqrt_le_sqrt (exponentialSourceMass_truncatedTilt_mul_le hd h2c0 h2c3 N)
  have hss : Real.sqrt (exponentialSourceMass F) *
      Real.sqrt (exponentialSourceMass fun u => truncatedTilt (2 * c) N u * F u) ≤
        ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    (mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
      (Real.mul_self_sqrt hE0)
  have hv : (0 : ℝ) ≤ 2 * vonMangoldtThreeHalvesMass :=
    mul_nonneg two_pos.le vonMangoldtThreeHalvesMass_nonneg
  have hp1 := (abs_primeMixedForm_le hd.weighted hG.weighted).trans
    (mul_le_mul_of_nonneg_left hss hv)
  have hp2 := (abs_primeMixedForm_le hG.weighted hd.weighted).trans
    (mul_le_mul_of_nonneg_left ((mul_comm _ _).trans_le hss) hv)
  -- The two real pole moments obey the same absolute bound.
  have hP0 : 0 ≤ ∫ u, |F u| * Real.exp (-(5 / 2) * u) :=
    integral_nonneg fun u => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hCC := mul_le_mul (abs_coshHalfMoment_le_of_domain hd)
    (abs_coshHalfMoment_truncatedTilt_mul_le hd h2c0 h2c2 N) (abs_nonneg _) hP0
  have hSS := mul_le_mul (abs_sinhHalfMoment_le_of_domain hd)
    (abs_sinhHalfMoment_truncatedTilt_mul_le hd h2c0 h2c2 N) (abs_nonneg _) hP0
  rw [← abs_mul] at hCC hSS
  have hCC' := (neg_le_abs _).trans hCC
  have hSS' := (le_abs_self _).trans hSS
  linarith only [hw,hCC',hSS',hp1,hp2,le_abs_self (primeMixedForm F fun u => truncatedTilt (2 * c) N u * F u),
    le_abs_self (primeMixedForm (fun u => truncatedTilt (2 * c) N u * F u) F)]

private theorem truncated_energy_bound {R : ℝ} {F : ℝ → ℝ} (hF : IsConfinedNullVector R F)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ K : ℝ, ∀ N : ℝ, cutJump F c N + criticalAliasCoefficient R * cutMass F c N ≤ K := by
  have hd := hF.1
  unfold cutJump
  refine ⟨(2 * vonMangoldtThreeHalvesMass + 2 * |gammaHardyPhaseRate 0| +
    (3 * c ^ 2 + 2) * ∫ x in Ioi (0 : ℝ), Real.exp (-(x / 2))) *
      (∫ u, F u ^ 2 * Real.exp (-(8 * u))) +
        4 * (∫ u, |F u| * Real.exp (-(5 / 2) * u)) ^ 2, fun N => ?_⟩
  have h2c : (0 : ℝ) ≤ 2 * c := by positivity
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hd h2c N
  have hB := levyEnergy_truncatedTilt_sub_levyMixed_le hd hc0 hc1 N
  have hC := gamma_add_confinement_le hF hc0 hc1 N
  have hL := gammaMixedForm_eq_levy hd hG
  have hI := integral_mul_truncatedTilt_mul_nonneg_le hd h2c (by linarith : 2 * c ≤ 3) N
  have h1 : -(gammaHardyPhaseRate 0) * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) ≤
      |gammaHardyPhaseRate 0| * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) :=
    mul_le_mul_of_nonneg_right (neg_le_abs _) hI.1
  have h2 : |gammaHardyPhaseRate 0| * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) ≤
      |gammaHardyPhaseRate 0| * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    mul_le_mul_of_nonneg_left hI.2 (abs_nonneg _)
  linarith only [hB,hC,hL,h1,h2]

/-- At any critical ratio, all tilts through the unit tilt belong to the full
energy domain. The confinement mass follows from the same estimate as the jump energy. -/
theorem IsConfinedNullVector.tilt_domain {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c*u)) * F u) := by
  obtain ⟨K,hK⟩ := truncated_energy_bound hF hc0 hc1
  let a := criticalAliasCoefficient R
  have ha : 0 < a := criticalAliasCoefficient_positive hr
  let m := fun (N : ℝ) (u : ℝ) => F u * (truncatedTilt (2*c) N u * F u) * Real.exp (-(8*u))
  have hm (N u : ℝ) : 0 ≤ m N u := by
    change 0 ≤ F u * (truncatedTilt (2*c) N u * F u) * Real.exp (-(8*u))
    rw [mul_left_comm (F u), ← sq]
    exact mul_nonneg (mul_nonneg (truncatedTilt_pos _ _ _).le (sq_nonneg _)) (Real.exp_pos _).le
  have hj (N : ℝ) : 0 ≤ cutJump F c N := setIntegral_nonneg measurableSet_Ioi fun x hx =>
    mul_nonneg (archLevyDensity_pos hx).le (integral_nonneg fun _ => sq_nonneg _)
  have hmEq (N : ℝ) : cutMass F c N = ∫ u, m N u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    simp only [hF.1.support u (not_lt.mp hu),zero_mul]
  have hi (N : ℝ) : Integrable (m N) :=
    hF.1.integrable_exponentialCross
      (criticalHalfLineEnergyDomain_truncatedTilt_mul hF.1 (mul_nonneg (by norm_num) hc0) N)
  have hbound (N : ℝ) : ∫ u, m N u ≤ K/a := by
    rw [le_div_iff₀ ha, mul_comm, ← hmEq]
    exact (le_add_of_nonneg_left (hj N)).trans (hK N)
  have hlim (u : ℝ) : Tendsto (fun N : ℕ => m N u) atTop
      (𝓝 (F u ^ 2 * Real.exp (-((8+2*c)*u)))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌈-u⌉₊] with N hN
    dsimp only [m]
    rw [truncatedTilt_eq_exp_neg (by linarith only [Nat.ceil_le.mp hN])]
    rw [show -((8+2*c)*u) = -((2*c)*u) + -(8*u) by ring,Real.exp_add]
    ring
  have hmass : Integrable fun u => F u ^ 2 * Real.exp (-((8+2*c)*u)) := by
    apply integrable_of_tendsto (Eventually.of_forall hlim) (fun n => (hi n).1)
    apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := K/a))
    apply liminf_le_of_frequently_le'
    apply Frequently.of_forall
    intro n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    simp_rw [Real.norm_of_nonneg (hm n _)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  apply criticalHalfLineEnergyDomain_exp_mul_of_levyEnergy_truncatedTilt_le hF.1 hc0 hmass
  intro N
  have hnn : 0 ≤ cutMass F c N := by rw [hmEq]; exact integral_nonneg (hm N)
  exact (le_add_of_nonneg_right (mul_nonneg ha.le hnn)).trans (hK N)

/-- Both reflected sampling maps of every confined null state are square-summable
on all the zero copies. -/
theorem IsConfinedNullVector.summable_zero_traces {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) :
    (Summable fun q : XiZeroCopy => ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ ^ 2) ∧
    (Summable fun q : XiZeroCopy => ‖negativeHalfLineLaplace (cx F) (-centredZero q)‖ ^ 2) := by
  have h := hF.tilt_domain hr zero_le_one le_rfl
  exact ⟨summable_norm_sq_laplace_centredZero h,summable_norm_sq_laplace_neg_centredZero h⟩

/-- The full bare pairing of two rungs is an absolutely convergent sum, with no
restriction on the number of off-line zero copies. -/
theorem IsConfinedNullVector.hasSum_bare_pair {R S : ℝ} (hr : 0 < R) (hs : 0 < S)
    {F G : ℝ → ℝ} (hF : IsConfinedNullVector R F) (hG : IsConfinedNullVector S G) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx G) (-centredZero q)) (bareMixedEnergy F G : ℂ) :=
  hasSum_mul_of_tendsto_gaussian (hF.summable_zero_traces hr).1 (hG.summable_zero_traces hs).2
    (tendsto_heatedZeroPairing hF.1 hG.1)

#print axioms IsConfinedNullVector.tilt_domain
#print axioms IsConfinedNullVector.summable_zero_traces
#print axioms IsConfinedNullVector.hasSum_bare_pair
end GaloisForLFunctions.ExclusionOfTheCriticalState
