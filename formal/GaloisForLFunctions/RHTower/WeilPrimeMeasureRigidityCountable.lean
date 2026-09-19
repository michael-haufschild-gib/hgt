import GaloisForLFunctions.RHTower.WeilCountablePerturbationFamily
import GaloisForLFunctions.RHTower.WeilPrimeMeasureRigidityFinite
import GaloisForLFunctions.HTGeometry.CosineSeriesNonposZero

/-!
# Prime-measure rigidity for countable summable perturbations

Change countably many prime weights, with summable budget `∑ |w n| · 2/√(x n)` and summable
logarithmic moment, at distinct scales `x n > 1`.  The resulting restricted Weil operator has
nonnegative ground energy at every aperture if and only if the Riemann hypothesis holds and every
weight vanishes.

The argument is that of the finite case with two additions.  Scales invisible at the wide-bump
aperture (`log x n > 2a ≥ 2L`) contribute nothing to the block term, and their share of the
profile is dominated by the logarithmic moment: `|κ n| · L ≤ |κ n| · log(x n)/2`.  The frequency
profile `∑' n, w n (2/√x n) cos(ζ log x n)` is a continuous absolutely convergent cosine series,
nonpositive at every gap frequency, hence everywhere; an absolutely convergent cosine series with
distinct positive frequencies that is nonpositive everywhere has zero coefficients.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilDeletion

/-- The frequency profile of a countable perturbation. -/
def countableProfile (P : CountablePrimePerturbation) (ζ : ℝ) : ℝ :=
  ∑' n, P.w n * (2 / Real.sqrt (P.x n)) * Real.cos (ζ * Real.log (P.x n))

theorem two_div_sqrt_pos (P : CountablePrimePerturbation) (n : ℕ) :
    0 < 2 / Real.sqrt (P.x n) := by
  have : 0 < Real.sqrt (P.x n) := Real.sqrt_pos.mpr (by linarith [P.one_lt n])
  positivity

theorem countableProfile_term_abs_le (P : CountablePrimePerturbation) (ζ : ℝ) (n : ℕ) :
    |P.w n * (2 / Real.sqrt (P.x n)) * Real.cos (ζ * Real.log (P.x n))| ≤
      |P.w n| * (2 / Real.sqrt (P.x n)) := by
  rw [abs_mul, abs_mul, abs_of_pos (two_div_sqrt_pos P n)]
  exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (two_div_sqrt_pos P n).le)
    (Real.abs_cos_le_one _)

theorem summable_countableProfile_term (P : CountablePrimePerturbation) (ζ : ℝ) :
    Summable fun n => P.w n * (2 / Real.sqrt (P.x n)) * Real.cos (ζ * Real.log (P.x n)) :=
  Summable.of_norm_bounded P.budget_summable fun n => by
    rw [Real.norm_eq_abs]; exact countableProfile_term_abs_le P ζ n

theorem continuous_countableProfile (P : CountablePrimePerturbation) :
    Continuous (countableProfile P) := by
  unfold countableProfile
  refine continuous_tsum (fun n => ?_) P.budget_summable fun n ζ => ?_
  · exact continuous_const.mul (Real.continuous_cos.comp (continuous_id.mul continuous_const))
  · rw [Real.norm_eq_abs]; exact countableProfile_term_abs_le P ζ n

/-- The logarithmic moment of the profile terms is summable. -/
theorem summable_countableProfile_term_abs_mul_log (P : CountablePrimePerturbation) (ζ : ℝ) :
    Summable fun n => |P.w n * (2 / Real.sqrt (P.x n)) * Real.cos (ζ * Real.log (P.x n))| *
      Real.log (P.x n) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (Real.log_pos (P.one_lt n)).le)
    (fun n => mul_le_mul_of_nonneg_right (countableProfile_term_abs_le P ζ n)
      (Real.log_pos (P.one_lt n)).le) P.logMoment_summable

/-- At a gap frequency, nonnegative ground energy at every aperture forces the profile to be
nonpositive. -/
theorem countableProfile_nonpos_of_gap (hreal : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0)
    (P : CountablePrimePerturbation)
    (hpos : ∀ a : SuzukiPositiveAperture, 0 ≤ (countableFamily P).energy a)
    {ζ d : ℝ} (hd : 0 < d) (hgap : ∀ q : XiZeroCopy, d ≤ |ζ - (xiSpectralPoint q).re|) :
    countableProfile P ζ ≤ 0 := by
  obtain ⟨M, hM0, hM⟩ := exists_lipschitz_phiTwo
  set c₂ : ℝ := ∫ v, phiN 2 v ^ 2 with hc₂
  have hc₂pos : 0 < c₂ := by
    have := integral_phiN_sq_ge 2
    have := sN_pos 2
    have h0 : 0 < 1 / (2 * sN 2) := by positivity
    linarith
  set C : ℝ := gapZeroSideConstant ζ d with hC
  have hCpos : 0 < C := gapZeroSideConstant_pos ζ d
  set κ : ℕ → ℝ := fun n => P.w n * (2 / Real.sqrt (P.x n)) * Real.cos (ζ * Real.log (P.x n))
    with hκ
  have hκsum : Summable κ := summable_countableProfile_term P ζ
  have hκlog : Summable fun n => |κ n| * Real.log (P.x n) :=
    summable_countableProfile_term_abs_mul_log P ζ
  set K : ℝ := ∑' n, |κ n| * Real.log (P.x n) with hK
  have hlogpos : ∀ n, 0 < Real.log (P.x n) := fun n => Real.log_pos (P.one_lt n)
  have hKnn : 0 ≤ K := tsum_nonneg fun n => mul_nonneg (abs_nonneg _) (hlogpos n).le
  have key : ∀ L : ℝ, 1 ≤ L → countableProfile P ζ * (c₂ * L) ≤ C + (M + c₂ / 2) * K := by
    intro L hL1
    have hLpos : 0 < L := by linarith
    have hfloor := countableFamily_energy_mul_le P (wideBumpAperture L hL1)
      (modulatedBumpSource L hL1 ζ).toCCMFormVector
    have hQ : ccmRestrictedWeilSourceQuadratic (wideBumpAperture L hL1)
        (modulatedBumpSource L hL1 ζ).toCCMFormVector ≤ C / L ^ 4 := by
      rw [ccmRestrictedWeilSourceQuadratic_eq_tsum_normSq_of_real hreal]
      exact tsum_normSq_paperFT_modulatedBump_le_of_gap hreal hL1 hd hgap
    have hE : 0 ≤ (countableFamily P).energy (wideBumpAperture L hL1) *
        ‖ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL1 ζ).toCCMFormVector‖ ^ 2 :=
      mul_nonneg (hpos _) (by positivity)
    have hCL : C / L ^ 4 ≤ C := div_le_self hCpos.le (one_le_pow₀ hL1)
    have h2L : 2 * L ≤ 2 * (wideBumpAperture L hL1).1 := by
      show 2 * L ≤ 2 * (L * sTwo + 1)
      have := sTwo_pos
      have hs : 1 ≤ sTwo := by rw [sTwo_val]; norm_num
      nlinarith
    -- termwise lower bound for the block pairing
    have hterm : ∀ n, κ n * (c₂ * L) - |κ n| * Real.log (P.x n) * (M + c₂ / 2) ≤
        (inner ℂ (ccmInsertedBlock (wideBumpAperture L hL1) (P.x n) (P.w n)
          (ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL1 ζ).toCCMFormVector))
          (ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL1 ζ).toCCMFormVector)).re := by
      intro n
      rw [re_inner_insertedBlock_modulatedBump' hL1 ζ (P.x n) (P.w n)]
      have hMl : 0 ≤ |κ n| * Real.log (P.x n) * (M + c₂ / 2) :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (hlogpos n).le) (by linarith)
      split_ifs with hvis
      · have hlo : c₂ * L - M * Real.log (P.x n) ≤ bumpOverlap L (Real.log (P.x n)) := by
          have := bumpOverlap_ge hLpos (Real.log (P.x n)) hM
          rw [abs_of_pos (hlogpos n)] at this
          linarith [mul_comm L c₂]
        have hhi : bumpOverlap L (Real.log (P.x n)) ≤ c₂ * L := by
          have := bumpOverlap_le hLpos (Real.log (P.x n))
          linarith [mul_comm L c₂]
        have heq : P.w n * (1 / Real.sqrt (P.x n)) *
            (2 * Real.cos (ζ * Real.log (P.x n)) * bumpOverlap L (Real.log (P.x n))) =
            κ n * bumpOverlap L (Real.log (P.x n)) := by
          rw [hκ]
          ring
        rw [heq]
        have hMl' : 0 ≤ |κ n| * Real.log (P.x n) * (c₂ / 2) :=
          mul_nonneg (mul_nonneg (abs_nonneg _) (hlogpos n).le) (by linarith)
        rcases le_or_gt 0 (κ n) with hk | hk
        · rw [abs_of_nonneg hk] at hMl' ⊢
          nlinarith [mul_le_mul_of_nonneg_left hlo hk]
        · rw [abs_of_neg hk] at hMl' ⊢
          nlinarith [mul_le_mul_of_nonpos_left hhi hk.le]
      · -- invisible: log x n > 2 a ≥ 2 L
        have hlog : 2 * L < Real.log (P.x n) := by
          have hx : Real.exp (2 * (wideBumpAperture L hL1).1) < P.x n := lt_of_not_ge hvis
          have := (Real.lt_log_iff_exp_lt (by linarith [P.one_lt n])).mpr hx
          linarith
        have h1 : κ n * (c₂ * L) ≤ |κ n| * (c₂ * L) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        have h2 : |κ n| * (c₂ * L) ≤ |κ n| * Real.log (P.x n) * (c₂ / 2) := by
          have : c₂ * L ≤ Real.log (P.x n) * (c₂ / 2) := by nlinarith
          calc |κ n| * (c₂ * L) ≤ |κ n| * (Real.log (P.x n) * (c₂ / 2)) :=
                mul_le_mul_of_nonneg_left this (abs_nonneg _)
            _ = |κ n| * Real.log (P.x n) * (c₂ / 2) := by ring
        have h3 : 0 ≤ |κ n| * Real.log (P.x n) * M :=
          mul_nonneg (mul_nonneg (abs_nonneg _) (hlogpos n).le) hM0
        nlinarith
    -- sum the termwise bound
    have hsum1 : Summable fun n => κ n * (c₂ * L) := hκsum.mul_right _
    have hsum2 : Summable fun n => |κ n| * Real.log (P.x n) * (M + c₂ / 2) := hκlog.mul_right _
    have hsumR := summable_re_inner_insertedBlock (wideBumpAperture L hL1) P
      (ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL1 ζ).toCCMFormVector)
    have hle := Summable.tsum_le_tsum hterm (hsum1.sub hsum2) hsumR
    rw [Summable.tsum_sub hsum1 hsum2, hκsum.tsum_mul_right, hκlog.tsum_mul_right] at hle
    have hprof : countableProfile P ζ = ∑' n, κ n := rfl
    rw [hprof]
    linarith
  by_contra hcon
  push Not at hcon
  set S : ℝ := countableProfile P ζ with hS
  have hcS : 0 < c₂ * S := mul_pos hc₂pos hcon
  set L : ℝ := max 1 ((C + (M + c₂ / 2) * K) / (c₂ * S) + 1) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLbig : (C + (M + c₂ / 2) * K) / (c₂ * S) + 1 ≤ L := le_max_right _ _
  have hkey := key L hL1
  have hlt : (C + (M + c₂ / 2) * K) / (c₂ * S) < L := by linarith
  rw [div_lt_iff₀ hcS] at hlt
  nlinarith [hkey, hlt]

/-- Zero weights give the literal family. -/
theorem countableFamily_energy_eq_of_weights_zero (P : CountablePrimePerturbation)
    (hw : ∀ n, P.w n = 0) (a : SuzukiPositiveAperture) :
    (countableFamily P).energy a = ccmRestrictedWeilGroundEnergy a := by
  have hblock : ccmCountableBlock a P = 0 := by
    unfold ccmCountableBlock
    have : ∀ n, ccmInsertedBlock a (P.x n) (P.w n) = 0 := fun n => by
      unfold ccmInsertedBlock
      rw [hw n, Complex.ofReal_zero]
      split_ifs
      · exact zero_smul ℂ (ccmScaleTransportOperator a (P.x n))
      · rfl
    simp only [this, tsum_zero]
  have hrem : ccmCountableRemainder a P = ccmRestrictedWeilBoundedRemainder a := by
    unfold ccmCountableRemainder
    rw [hblock, sub_zero]
  show ‖boundedPerturbedFormCovariance (ccmArchimedeanFormToAperture a) (ccmCountableRemainder a P)
      (ccmCountableRemainder_isSelfAdjoint a P)‖⁻¹ -
      boundedPerturbedFormShift (ccmCountableRemainder a P) = _
  unfold ccmRestrictedWeilGroundEnergy ccmRestrictedWeilCovariance
  rw [boundedPerturbedFormCovariance_congr (ccmArchimedeanFormToAperture a) hrem _
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a), hrem]

/-- **Prime-measure rigidity for countable summable perturbations.** -/
theorem riemannHypothesis_and_weights_zero_of_countableFamily_nonneg
    (P : CountablePrimePerturbation) (hinj : Function.Injective P.x)
    (hpos : ∀ a : SuzukiPositiveAperture, 0 ≤ (countableFamily P).energy a) :
    RiemannHypothesis ∧ ∀ n, P.w n = 0 := by
  have hRH : RiemannHypothesis := by
    by_contra h
    obtain ⟨a, ha⟩ := exists_countableFamily_energy_neg_of_not_riemannHypothesis P h
    linarith [hpos a]
  refine ⟨hRH, ?_⟩
  have hreal := xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH
  have hprof : ∀ ζ : ℝ, countableProfile P ζ ≤ 0 := by
    intro ζ₀
    by_contra hcon
    push Not at hcon
    have hev : ∀ᶠ ζ in 𝓝 ζ₀, 0 < countableProfile P ζ :=
      ((continuous_countableProfile P).tendsto ζ₀).eventually (lt_mem_nhds hcon)
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨ζ, d, hζ, hd, hgap⟩ := exists_gap_frequency hreal ζ₀ hη
    have h1 := countableProfile_nonpos_of_gap hreal P hpos hd hgap
    have h2 := hball (by rwa [Real.dist_eq])
    linarith
  have hc : Summable fun n => |P.w n * (2 / Real.sqrt (P.x n))| := by
    refine P.budget_summable.congr fun n => ?_
    rw [abs_mul, abs_of_pos (two_div_sqrt_pos P n)]
  have hzero := cosineSeries_coeff_eq_zero_of_nonpos
    (fun n => P.w n * (2 / Real.sqrt (P.x n))) (fun n => Real.log (P.x n))
    (fun n => Real.log_pos (P.one_lt n))
    (fun i j h => hinj (Real.log_injOn_pos (Set.mem_Ioi.mpr (by linarith [P.one_lt i]))
      (Set.mem_Ioi.mpr (by linarith [P.one_lt j])) h))
    hc
    (fun t => by
      have := hprof t
      unfold countableProfile at this
      simp only [mul_comm t] at this
      exact this)
  intro n
  have h := hzero n
  have hsx : 0 < 2 / Real.sqrt (P.x n) := by
    have : 0 < Real.sqrt (P.x n) := Real.sqrt_pos.mpr (by linarith [P.one_lt n])
    positivity
  exact (mul_eq_zero.mp h).resolve_right hsx.ne'

/-- **Prime-measure rigidity for countable summable perturbations, both directions.** -/
theorem countableFamily_nonneg_iff (P : CountablePrimePerturbation)
    (hinj : Function.Injective P.x) :
    (∀ a : SuzukiPositiveAperture, 0 ≤ (countableFamily P).energy a) ↔
      RiemannHypothesis ∧ ∀ n, P.w n = 0 := by
  constructor
  · exact riemannHypothesis_and_weights_zero_of_countableFamily_nonneg P hinj
  · rintro ⟨hRH, hw⟩ a
    rw [countableFamily_energy_eq_of_weights_zero P hw]
    exact ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis hRH a

end RHTower.WeilDeletion

end
