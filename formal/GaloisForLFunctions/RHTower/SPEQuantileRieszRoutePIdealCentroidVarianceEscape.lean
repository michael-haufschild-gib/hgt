import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePIdealCentroidVarianceCorrection
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import GaloisForLFunctions.RHTower.SuzukiTransitionCoreGrowingRankCartanFission

/-!
# Route P barycentric escape of matched centroid variance

The literal matched centroid differs from the ideal arithmetic centroid by a
summable positive excess. Its finite cubic-width contribution stays bounded,
but its first-moment shift is amplified by the escaping Chebyshev-to-critical
mass ratio. Consequently the matched-minus-ideal normalized variance tends to
negative infinity. This is a geometric correction law, not a sign theorem for
the full matched-minus-quantile strict-cross defect.
-/

open scoped BigOperators Chebyshev
open ArithmeticFunction Filter Topology

namespace RHTower

theorem tendsto_criticalMellinAtomWeight_zero :
    Tendsto criticalMellinAtomWeight atTop (𝓝 0) := by
  have hlog : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop
      (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
    have hn := h.comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using hn
  refine squeeze_zero' (f := criticalMellinAtomWeight)
    (g := fun n : ℕ => Real.log (n : ℝ) / Real.sqrt (n : ℝ)) ?_ ?_ hlog
  · exact Eventually.of_forall
      criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [criticalMellinAtomWeight_eq_div_sqrt]
    exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
      (Real.sqrt_nonneg _)

theorem tendsto_routeP_mass_div_linear_zero :
    Tendsto (fun K : ℕ => ccmActualHeadParabolicMass K / ((K + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hw := tendsto_criticalMellinAtomWeight_zero.comp (tendsto_add_atTop_nat 2)
  have hc := hw.cesaro
  have heq (K : ℕ) :
      (((K + 1 : ℕ) : ℝ)⁻¹) *
        ∑ n ∈ Finset.range (K + 1), criticalMellinAtomWeight (n + 2) =
        ccmActualHeadParabolicMass K / ((K + 1 : ℕ) : ℝ) := by
    simp only [ccmActualHeadParabolicMass, div_eq_mul_inv]
    ring
  exact (hc.comp (tendsto_add_atTop_nat 1)).congr' (Eventually.of_forall heq)

theorem tendsto_routeP_psi_div_linear_one :
    Tendsto
      (fun K : ℕ => Chebyshev.psi ((K + 2 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ))
      atTop (𝓝 1) := by
  have hfactor : Tendsto
      (fun K : ℕ => ((K + 2 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      (2 : ℝ) 1 1 (show (1 : ℝ) ≠ 0 by norm_num)
    convert h using 1
    · ext K
      push_cast
      ring
    · norm_num
  have hbase := tendsto_psi_natCast_div.comp (tendsto_add_atTop_nat 2)
  have hprod := hbase.mul hfactor
  have heq (K : ℕ) :
      Chebyshev.psi ((K + 2 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) =
        (Chebyshev.psi ((K + 2 : ℕ) : ℝ) / ((K + 2 : ℕ) : ℝ)) *
          (((K + 2 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ)) := by
    have h2 : (((K + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
  simpa only [one_mul] using hprod.congr'
    (Eventually.of_forall (fun K => (heq K).symm))

theorem tendsto_routeP_mass_div_psi_zero :
    Tendsto
      (fun K : ℕ => ccmActualHeadParabolicMass K /
        Chebyshev.psi ((K + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_routeP_mass_div_linear_zero.div
    tendsto_routeP_psi_div_linear_one (by norm_num : (1 : ℝ) ≠ 0)
  have heq (K : ℕ) :
      (ccmActualHeadParabolicMass K / ((K + 1 : ℕ) : ℝ)) /
          (Chebyshev.psi ((K + 2 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ)) =
        ccmActualHeadParabolicMass K /
          Chebyshev.psi ((K + 2 : ℕ) : ℝ) := by
    have hk : (((K + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    by_cases hp : Chebyshev.psi ((K + 2 : ℕ) : ℝ) = 0
    · rw [hp]
      simp
    · field_simp
  simpa only [zero_div] using h.congr' (Eventually.of_forall heq)

theorem tendsto_routeP_psi_div_mass_atTop :
    Tendsto
      (fun K : ℕ => Chebyshev.psi ((K + 2 : ℕ) : ℝ) /
        ccmActualHeadParabolicMass K) atTop atTop := by
  have hpsipos : ∀ᶠ K : ℕ in atTop,
      0 < Chebyshev.psi ((K + 2 : ℕ) : ℝ) := by
    filter_upwards [tendsto_routeP_psi_div_linear_one.eventually
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))] with K hK
    have hk : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
    exact (div_pos_iff_of_pos_right hk).mp hK
  have hratio : Tendsto
      (fun K : ℕ => ccmActualHeadParabolicMass K /
        Chebyshev.psi ((K + 2 : ℕ) : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact tendsto_routeP_mass_div_psi_zero
    · filter_upwards [hpsipos] with K hK
      exact div_pos (ccmActualHeadParabolicMass_pos K) hK
  have h := tendsto_inv_nhdsGT_zero.comp hratio
  simpa only [Function.comp_def, inv_div] using h

noncomputable def routePWidthCubeAtom (n : ℕ) : ℝ :=
  criticalMellinAtomWeight n ^ (3 : ℕ) / 4

theorem summable_routePWidthCubeAtom : Summable routePWidthCubeAtom := by
  have h := GaloisForLFunctions.RHTower.summable_criticalMellinAtomWeight_cube
  refine (h.mul_left (1 / 4 : ℝ)).congr (fun n => ?_)
  unfold routePWidthCubeAtom
  ring

theorem routePWidthCubePrefix_eq_atomPrefix (K : ℕ) :
    routePWidthCubePrefix K =
      ∑ n ∈ Finset.range (K + 3), routePWidthCubeAtom n := by
  have hzero : routePWidthCubeAtom 0 = 0 := by
    simp [routePWidthCubeAtom, criticalMellinAtomWeight]
  have hone : routePWidthCubeAtom 1 = 0 := by
    simp [routePWidthCubeAtom, criticalMellinAtomWeight]
  rw [centroid_sum_range_shift_two routePWidthCubeAtom hzero hone K]
  rfl

theorem routePWidthCubePrefix_le_tsum (K : ℕ) :
    routePWidthCubePrefix K ≤ ∑' n : ℕ, routePWidthCubeAtom n := by
  rw [routePWidthCubePrefix_eq_atomPrefix]
  exact summable_routePWidthCubeAtom.sum_le_tsum (Finset.range (K + 3))
    (fun n _ => by
      unfold routePWidthCubeAtom
      exact div_nonneg
        (pow_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n) 3)
        (by norm_num))

theorem centroidAtomExcess_two_pos : 0 < centroidAtomExcess 2 := by
  have hw : 0 < criticalMellinAtomWeight 2 :=
    criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
  have hc : 0 < ccmActualHeadMatchedPolarCentroid 2 :=
    ccmActualHeadMatchedPolarCentroid_pos 2
  have hr : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hrsq : Real.sqrt (2 : ℝ) ^ (2 : ℕ) = 2 := by norm_num
  have hsq := ccmActualHeadMatchedPolarCentroid_sq 2 (by norm_num)
  have hstrict : 2 * Real.sqrt (2 : ℝ) < ccmActualHeadMatchedPolarCentroid 2 := by
    nlinarith [sq_pos_of_pos hw]
  unfold centroidAtomExcess
  exact mul_pos hw (sub_pos.mpr hstrict)

theorem routeP_centroid_excess_pos (K : ℕ) :
    0 < ccmActualHeadMatchedCentroidChebyshevExcess K := by
  rw [ccmActualHeadMatchedCentroidChebyshevExcess_eq_atomPrefix]
  have hmem : 2 ∈ Finset.range (K + 3) := by simp
  exact lt_of_lt_of_le centroidAtomExcess_two_pos
    (Finset.single_le_sum (fun n _ => centroidAtomExcess_nonneg_all n) hmem)

theorem routeP_matched_variance_correction_atBot :
    Tendsto
      (fun K : ℕ =>
        ccmActualHeadParabolicNormalizedCentroidVariance K ccmActualHeadMatchedPolarCentroid -
          ccmActualHeadParabolicNormalizedCentroidVariance K routePIdealCentroid)
      atTop atBot := by
  let C : ℝ := ∑' n : ℕ, routePWidthCubeAtom n
  let E : ℝ := centroidAtomExcess 2
  have hE : 0 < E := centroidAtomExcess_two_pos
  have hcoeff : -4 * E < 0 := by linarith
  have hupper : Tendsto
      (fun K : ℕ => C +
        (Chebyshev.psi ((K + 2 : ℕ) : ℝ) / ccmActualHeadParabolicMass K) *
          (-4 * E)) atTop atBot := by
    apply tendsto_atBot_add_const_left
    exact tendsto_routeP_psi_div_mass_atTop.atTop_mul_const_of_neg' hcoeff
  apply tendsto_atBot_mono (f := fun K : ℕ => C +
    (Chebyshev.psi ((K + 2 : ℕ) : ℝ) / ccmActualHeadParabolicMass K) *
      (-4 * E))
  · intro K
    rw [routeP_matched_variance_correction]
    let m := ccmActualHeadParabolicMass K
    let p := Chebyshev.psi ((K + 2 : ℕ) : ℝ)
    let e := ccmActualHeadMatchedCentroidChebyshevExcess K
    let q := routePWidthCubePrefix K
    have hm : 0 < m := ccmActualHeadParabolicMass_pos K
    have hp : 0 ≤ p := by
      unfold p
      rw [← centroidAtomExcess_vonMangoldt_shift_two K]
      exact Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hq : q ≤ C := routePWidthCubePrefix_le_tsum K
    have he : E ≤ e := by
      unfold e
      rw [ccmActualHeadMatchedCentroidChebyshevExcess_eq_atomPrefix]
      exact Finset.single_le_sum
        (fun n _ => centroidAtomExcess_nonneg_all n)
        (by simp : 2 ∈ Finset.range (K + 3))
    have hbridge : (4 * p * e + e ^ (2 : ℕ)) / m =
        4 * (p / m) * e + e ^ (2 : ℕ) / m := by
      field_simp
    change q - (4 * p * e + e ^ (2 : ℕ)) / m ≤ C + (p / m) * (-4 * E)
    rw [hbridge]
    have hdebt : 0 ≤ e ^ (2 : ℕ) / m :=
      div_nonneg (sq_nonneg e) hm.le
    have hcredit : 0 ≤ 4 * (p / m) * (e - E) := by positivity
    nlinarith only [hq, hdebt, hcredit]
  · exact hupper

end RHTower
