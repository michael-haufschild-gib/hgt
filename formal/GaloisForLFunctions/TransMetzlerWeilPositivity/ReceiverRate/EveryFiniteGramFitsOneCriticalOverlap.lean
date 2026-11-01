import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.ABoundedOverlapRateSeesASemilocalWindow
import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.AProfileAtEveryLogarithmicType

/-!
# One critical overlap realizes every finite rational Weil Gram

The fixed Beurling profile admits every positive derivative type. For each
finite family, choose that type small enough for the synthesis threshold.
The overlap remains `2 · dcScale N`, independently of the family.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ContDiff RealInnerProductSpace
namespace GaloisForLFunctions.TransMetzlerWeilPositivity
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics ArithmeticCastelnuovoSeveri EffectiveArithmeticHodgeTheory
  ArithmeticPositiveDuality
open BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)

/-- The unit-mass Beurling profile on `[0,1]`. -/
def beurlingUnitProfile (u : ℝ) : ℝ := 2 * beurlingDCProfile (2 * u - 1)

theorem beurlingUnitProfile_nonneg (u : ℝ) : 0 ≤ beurlingUnitProfile u :=
  mul_nonneg two_pos.le (beurlingDCProfile_nonneg _)

theorem contDiff_beurlingUnitProfile : ContDiff ℝ ∞ beurlingUnitProfile :=
  contDiff_const.mul (contDiff_beurlingDCProfile.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem beurlingUnitProfile_eq_zero (u : ℝ) (hu : u ∉ Set.Icc 0 1) :
    beurlingUnitProfile u = 0 := by
  unfold beurlingUnitProfile
  rw [beurlingDCProfile_vanishesOff, mul_zero]
  by_contra h
  have h' := abs_le.mp (not_lt.mp h)
  exact hu ⟨by linarith [h'.1], by linarith [h'.2]⟩

theorem integral_beurlingUnitProfile : ∫ u, beurlingUnitProfile u = 1 := by
  unfold beurlingUnitProfile
  rw [integral_const_mul]
  have h : (fun u => beurlingDCProfile (2 * u - 1)) =
      fun u => (fun t => beurlingDCProfile (t - 1)) (u / (1 / 2)) := by
    funext u
    congr 1
    ring
  rw [h, Measure.integral_comp_div (fun t : ℝ => beurlingDCProfile (t - 1)) (1 / 2 : ℝ)]
  simp only [sub_eq_add_neg, integral_add_right_eq_self, integral_beurlingDCProfile]
  norm_num

theorem recentred_beurlingUnitProfile : recentredProfile beurlingUnitProfile =
    beurlingDCProfile := by
  funext u
  rw [recentredProfile, integral_beurlingUnitProfile]
  unfold beurlingUnitProfile
  rw [show 2 * ((u + 1) / 2) - 1 = u by ring]
  ring

private theorem integral_sq_pos {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hint : (∫ u, φ u) ≠ 0) :
    0 < ∫ u, φ u ^ 2 := by
  have hcont : Continuous (fun u : ℝ => φ u ^ 2) := hφ.pow 2
  have hsupp : HasCompactSupport (fun u : ℝ => φ u ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (zero_pow (by decide))
  have hi : Integrable (fun u : ℝ => φ u ^ 2) :=
    hcont.integrable_of_hasCompactSupport hsupp
  refine lt_of_le_of_ne (integral_nonneg fun u => sq_nonneg _) ?_
  intro he
  have hae := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg (φ u)) hi).mp he.symm
  apply hint
  calc
    (∫ u, φ u) = ∫ _ : ℝ, (0 : ℝ) := integral_congr_ae (hae.mono fun u hu => sq_eq_zero_iff.mp hu)
    _ = 0 := integral_zero _ _

theorem integral_beurlingUnitProfile_sq_pos : 0 < ∫ u, beurlingUnitProfile u ^ 2 :=
  integral_sq_pos contDiff_beurlingUnitProfile.continuous
    (HasCompactSupport.intro isCompact_Icc beurlingUnitProfile_eq_zero)
    (by rw [integral_beurlingUnitProfile]; norm_num)

/-- Each finite rational correlation Gram is approximated by complete Beurling
packet Grams at the universal critical overlap, independent of the family. -/
theorem exists_ratCorr_gram_approximation_at_universal_critical_overlap
    {ι : Type*} [Fintype ι] (q : ι → posUnits) :
    ∃ B : ℕ, 1 ≤ B ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ x : ι → ℕ → ℝ, ∀ i j,
        ‖weilGram vonMangoldtWeight
            (fun a => cx (atomicTest (n * B) (x a)
              (dilate (((n * B : ℕ) : ℝ) / dcScale (n * B)) beurlingDCProfile))) i j -
          ratCorr ((q i)⁻¹ * q j)‖ < ε := by
  classical
  let F : ι → ℝ → ℝ := fun i u => cubicSpline (u - logPos (q i))
  have hF : ∀ i, ContDiff ℝ 2 (F i) :=
    fun i => contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const)
  have hFc : ∀ i, HasCompactSupport (F i) :=
    fun i => hasCompactSupport_cubicSpline.comp_homeomorph (Homeomorph.subRight _)
  choose Ri Mi Li hRi hRiF hMi hLi using fun i => exists_test_bounds (hF i) (hFc i)
  let R := ∑ i, Ri i
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => hRi i
  have hFR : ∀ i, SupportedIn R (F i) := fun i =>
    EffectiveArithmeticHodgeTheory.supportedIn_mono (hRiF i)
      (Finset.single_le_sum (fun j _ => hRi j) (Finset.mem_univ i))
  let B := blockSize (R + 1)
  have hB : 1 ≤ B := one_le_blockSize (R + 1)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (zero_lt_one.trans_le hB)
  let b : ℝ := 1 / (48 * B * Real.exp 1)
  have hb : 0 < b := by dsimp only [b]; positivity
  obtain ⟨A, _, hA⟩ := exists_beurlingDCProfile_bound hb
  let κ : ℕ → ℝ := fun N => (N : ℝ) / dcScale N
  have hk : Tendsto κ atTop atTop := by
    simpa only [one_mul] using tendsto_div_const_mul_dcScale (by norm_num : (0 : ℝ) < 1)
  have hrate : ∀ᶠ N : ℕ in atTop, 1 ≤ dcRate κ N := by
    filter_upwards [eventually_div_dcScale_le_dcRate hk
      (dcScale_atTop.eventually_ge_atTop 1), dcScale_atTop.eventually_gt_atTop 0]
      with N hN hS
    simpa only [div_self hS.ne'] using hN
  have hRK : 24 * b * blockSize (R + 1) * Real.exp 1 < 1 := by
    have he : 24 * b * blockSize (R + 1) * Real.exp 1 = 1 / 2 := by
      dsimp only [b, B]
      field_simp
      ring
    rw [he]
    norm_num
  have hgram (i j : ι) : weilGram vonMangoldtWeight (fun a => cx (F a)) i j =
      ratCorr ((q i)⁻¹ * q j) := by
    change weilGram vonMangoldtWeight
      (fun a => ArithmeticCastelnuovoSeveri.translate (logPos (q a)) (cx cubicSpline)) i j = _
    rw [weilGram_translate_cubicSpline, ratCorr, logPos_inv_mul, neg_sub]
  refine ⟨B, hB, fun ε hε => ?_⟩
  have happrox := eventually_exists_family_gram_approximation_of_rate
    contDiff_beurlingDCProfile beurlingDCProfile_vanishesOff integral_beurlingDCProfile
    hb.le hA
    hk le_rfl hrate hR hF hFR hRK ε hε
  filter_upwards [happrox] with n hn
  obtain ⟨x, hx⟩ := hn
  refine ⟨x, fun i j => ?_⟩
  simpa only [← hgram i j] using hx i j

/-- Every finite rational correlation Gram is an entrywise limit of full Weil
packet Grams on the same Beurling critical schedule. -/
theorem exists_ratCorr_gram_limit_at_universal_critical_overlap
    {ι : Type*} [Fintype ι] (q : ι → posUnits) :
    ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧
      ∃ x : ℕ → ι → ℕ → ℝ, ∀ i j,
        Tendsto (fun m => weilGram vonMangoldtWeight
          (fun a => cx (atomicTest (N m) (x m a)
            (dilate ((N m : ℝ) / dcScale (N m)) beurlingDCProfile))) i j)
          atTop (𝓝 (ratCorr ((q i)⁻¹ * q j))) := by
  classical
  obtain ⟨B, hB, happ⟩ := exists_ratCorr_gram_approximation_at_universal_critical_overlap q
  have hex : ∀ m : ℕ, ∃ n : ℕ, m ≤ n ∧ ∃ x : ι → ℕ → ℝ, ∀ i j,
      ‖weilGram vonMangoldtWeight
          (fun a => cx (atomicTest (n * B) (x a)
            (dilate (((n * B : ℕ) : ℝ) / dcScale (n * B)) beurlingDCProfile))) i j -
        ratCorr ((q i)⁻¹ * q j)‖ < 1 / ((m : ℝ) + 1) := by
    intro m
    exact ((eventually_ge_atTop m).and (happ (1 / ((m : ℝ) + 1)) (by positivity))).exists
  choose n hn x hx using hex
  refine ⟨fun m => n m * B,
    tendsto_atTop_mono (fun m => (hn m).trans (Nat.le_mul_of_pos_right (n m) hB)) tendsto_id,
    x, fun i j => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun m => norm_nonneg _) (fun m => (hx m i j).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Every finite rational correlation Gram is an entrywise limit of compressions
of the smooth complete Weil matrix at the universal overlap `2 · dcScale N`. -/
theorem exists_ratCorr_completeWeil_gram_limit_at_universal_critical_overlap {ι : Type*} [Fintype ι]
    (q : ι → posUnits) :
    ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧
      ∃ v : (m : ℕ) → ι → EuclideanSpace ℝ (PrimeHorizonIndex (N m)), ∀ i j,
        Tendsto (fun m => (((∫ u, atomDilate beurlingUnitProfile
          (2 * dcScale (N m) / N m) u ^ 2) *
          ⟪(completeWeilMatrix beurlingUnitProfile (2 * dcScale (N m)) (N m)).toEuclideanLin
            (v m i), v m j⟫ : ℝ) : ℂ)) atTop (𝓝 (ratCorr ((q i)⁻¹ * q j))) := by
  obtain ⟨N, hN, x, hx⟩ := exists_ratCorr_gram_limit_at_universal_critical_overlap q
  refine ⟨N, hN, fun m i =>
    completePacketVector beurlingUnitProfile (2 * dcScale (N m)) (N m) (x m i), fun i j => ?_⟩
  refine (hx i j).congr' ?_
  filter_upwards [hN.eventually (dcScale_atTop.eventually_gt_atTop 0),
    hN.eventually (eventually_ge_atTop 1)] with m hm h1
  have hc : 0 < 2 * dcScale (N m) := by
    positivity
  have heq : 2 / (2 * dcScale (N m) / N m) =
      (N m : ℝ) / dcScale (N m) := by
    rw [div_div_eq_mul_div, mul_div_mul_left _ _ two_ne_zero]
  symm
  simpa only [recentred_beurlingUnitProfile, heq] using
    completePacketVector_gram (x m) (contDiff_beurlingUnitProfile.of_le (natCast_le_infty 2))
      beurlingUnitProfile_eq_zero integral_beurlingUnitProfile_sq_pos hc h1 i j

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.exists_ratCorr_completeWeil_gram_limit_at_universal_critical_overlap
