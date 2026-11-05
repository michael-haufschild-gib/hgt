import GaloisForLFunctions.SignedWindowCriticality.CollectiveSliverPaymentAndSignedThetaGauges
import GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry.TheWindowEdgeCarriesTheNewestPrime
import GaloisForLFunctions.SignedWindowCriticality.BelowLogFour.TwoProfileRefutationBelowLogFour
import GaloisForLFunctions.ArithmeticIncidencePositivity.MultiPrimeDilationModulusAndIteratedWeilFloors

/-!
# Neutral Signed Theta-Gauge Optimization, Deficit Conservation, and the `{2, 3, 4}` Sliver Frontier up to `log 5`

On any compact window `[-c, c]` (`c > 0`), the window-adapted neutral signed theta-gauge pair
`(signedEvenThetaGauge b (neutralEvenThetaParam b c), shiftedGroundState a)` eliminates the even
outside cosh deficit at every finite pocket location `b` while retaining positive sinh slack in the
odd sector. Joint analysis of `(b, a)` with the prime-`3` and prime-`4` endpoint slivers establishes
four unconditional laws:

1. **Finite-`b` neutral decomposition, pole-neutral `(b, α₀)`-invariance, and odd variance necessity**
   (`neutralEvenTheta_signedJump_and_variance_eq`, `neutralEvenTheta_poleNeutral_invariance`,
   `odd_shiftedGroundState_variance_retention_necessary`). At `α₀ = neutralEvenThetaParam b c`,
   both `signedJumpEnergy` and `2 · chargeVariance` share the identical `(b, c)`-dependent weight
   `α₀^*(b, c) ∫ (F² / M_reg) cosh(x/2)`. On the codimension-one pole-neutral hyperplane
   `evenPoleMoment F = 0`, this weight cancels identically, leaving `markovEnergy F = archForm F -
   primeSum F` invariant under `b`; in the odd sector, dropping retained variance fails for every
   `a > 0` above `c = 273 / 400`. Optimizing `(b, a)` is therefore necessarily joint with retained
   variance and the endpoint slivers.

2. **Asymptotic `b → ∞` rescaling and outside-deficit conservation**
   (`tendsto_neutralEvenThetaParam_div_two_cosh_atTop`,
   `tendsto_signedEvenThetaProfile_neutral_div_two_cosh_atTop`,
   `tendsto_neutralEvenTheta_signedJump_and_variance_atTop`). As the negative pockets `±b → ±∞`,
   `M_{b, α₀^*(b,c)}^+ / (2 cosh(b/2))` converges to `((1/2) / Δ_Φ(c)) Φ`, `2 · chargeVariance`
   converges to the ground-state window variance `2 V_{Φ cosh}^{(-c, c)}(F / Φ)`, and the exterior
   prime-power jumps into the receding pockets retain the exact negative mass
   `-2 Δ_Φ(c) ∫ (F² / Φ) cosh(x/2)`, conserving the ground-state outside cosh deficit.

3. **Exact `{2, 3, 4}` reflection truncation, half-window `n = 2`-only sliver law, and sub-unit
   collective outward Lévy edge-carry up to `2c = log 5`**
   (`orderedCoupling_collarReflect_eq_two_three_four_of_lt_half_log_five`,
   `primeSum_eq_two_sliver_of_collarWindow_lt_log_three`,
   `twoThreeFour_collarKicks_le_levyEnergy`). Across the entire `{2, 3, 4}` reflection band
   `0 < c < (log 5) / 2` (`2c < log 5`, crossing both `2c = log 3` and `2c = log 4`), `c < log 3`
   holds automatically so primes `3` and `4` do not enter the diagonal `primeSum f` on `[m - c, m]`
   at all (`primeSum f = 2 w₂ autocorr f (log 2)`), while in the reflected coupling `{2, 3, 4}`
   together consume at most `(3 log 2 / 8 + log 3 / 6) √5 < 991 / 1000 < 1` of `levyEnergy f`.

4. **Infinite-tower super-`enlargedWeilFloorAperture` reflection-pair sliver floors and joint
   `{2, 3, 4}` frontier equivalence**
   (`weilQuad_sub_abs_orderedCoupling_ge_of_le_weilFloorApertureTower`,
   `joint_neutralThetaGauge_and_twoThreeFour_sliver_equivalence`). Along the infinite strictly
   increasing tower `weilFloorApertureTower k` (`k : ℕ`, with `enlargedWeilFloorAperture <
   successorWeilFloorAperture = weilFloorApertureTower 0 < weilFloorApertureTower (k + 1)`), every
   collar test on `[m - c, m]` (`0 < c ≤ weilFloorApertureTower k`) satisfies
   `W(f) - |𝒞_m(f)| ≥ weilFloorTowerConst k · ∫ f²`.
-/

open MeasureTheory Set Filter Topology
open scoped Real BigOperators

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open _root_.Zeta23 _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.WeilMarkovPole
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry
open GaloisForLFunctions.SignedWindowCriticality.BelowLogFour

private lemma fullZeroForm_eq_weilQuad_of_cont {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) : fullZeroForm F = weilQuad F :=
  GaloisForLFunctions.ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional hF hFc

/-! ### 1. Finite-`b` neutral decomposition, pole-neutral `(b, α₀)`-invariance, and odd variance necessity -/

/-- Test coordinate `u_{b, c}(x) = F(x) / regularizedEvenThetaProfile c b (neutralEvenThetaParam b c) x`
associated to a compactly supported test `F` on `[-c, c]`. -/
def neutralEvenThetaTestCoord (c b : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  F x / regularizedEvenThetaProfile c b (neutralEvenThetaParam b c) x

/-- Exact decomposition of `signedJumpEnergy` in `signedEvenThetaGauge b α₀` into `markovEnergy`
plus the cosh source integral with weight `α₀`. -/
theorem signedJumpEnergy_signedEvenTheta_eq (b α₀ : ℝ) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    signedJumpEnergy (signedEvenThetaProfile b α₀) u =
      markovEnergy (fun x => (phiDoobTest (fun y => signedEvenThetaGauge b α₀ y * u y) x : ℂ)) +
        α₀ * ∫ x, u x ^ 2 * (signedEvenThetaProfile b α₀ x * Real.cosh (x / 2)) := by
  have hm := markovEnergy_thetaGauge Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) hu huc
  have hsrc : (∫ x, u x ^ 2 *
        (riemannKernelReal x *
          translateSpan Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) x) *
        translateSource Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) x) =
      -(α₀ * ∫ x, u x ^ 2 * (signedEvenThetaProfile b α₀ x * Real.cosh (x / 2))) := by
    have hpt : (fun x => u x ^ 2 *
          (riemannKernelReal x *
            translateSpan Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) x) *
          translateSource Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) x) =
        fun x => (-α₀) * (u x ^ 2 * (signedEvenThetaProfile b α₀ x * Real.cosh (x / 2))) := by
      funext x
      simp only [translateSource, translateCoshCoefficient_signedEvenTheta,
        translateSinhCoefficient_signedEvenTheta, signedEvenThetaProfile, signedEvenThetaGauge]
      ring
    rw [hpt, integral_const_mul]
    ring
  rw [hsrc] at hm
  unfold signedEvenThetaProfile signedEvenThetaGauge at hm ⊢
  linarith

/-- **Exact finite-`b` neutral decomposition.** For `c > 0`, `b : ℝ` with
`M_{b, α₀^*(b, c)}^+ > 0` on `[-(c + 1), c + 1]`, and `F ∈ C²_c(ℝ)` supported in `[-c, c]`,
both `signedJumpEnergy` and `2 · chargeVariance` share the exact `(b, c)`-dependent integral
`α₀^*(b, c) ∫ (F² / M_reg) cosh(x/2)`. -/
theorem neutralEvenTheta_signedJump_and_variance_eq {c b : ℝ} (hc : 0 < c)
    (hpos : ∀ x ∈ Icc (-(c + 1)) (c + 1),
      0 < signedEvenThetaProfile b (neutralEvenThetaParam b c) x)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : SupportedIn c F) :
    signedJumpEnergy (signedEvenThetaProfile b (neutralEvenThetaParam b c))
        (neutralEvenThetaTestCoord c b F) =
      markovEnergy (fun x => (F x : ℂ)) +
        neutralEvenThetaParam b c *
          ∫ x, (F x ^ 2 /
            regularizedEvenThetaProfile c b (neutralEvenThetaParam b c) x) * Real.cosh (x / 2) ∧
    2 * chargeVariance
        (fun x => signedEvenThetaProfile b (neutralEvenThetaParam b c) x * Real.cosh (x / 2))
        (Ioo (-c) c) (neutralEvenThetaTestCoord c b F) =
      neutralEvenThetaParam b c *
          (∫ x, (F x ^ 2 /
            regularizedEvenThetaProfile c b (neutralEvenThetaParam b c) x) * Real.cosh (x / 2)) -
        2 * evenPoleMoment F ^ 2 := by
  set α₀ := neutralEvenThetaParam b c
  set u := neutralEvenThetaTestCoord c b F
  have hu_diff : ContDiff ℝ 2 u :=
    hF.div (contDiff_regularizedEvenThetaProfile c b α₀)
      fun x => (regularizedEvenThetaProfile_pos hpos x).ne'
  have hu_supp : SupportedIn c u := fun x hx => by
    dsimp only [u, neutralEvenThetaTestCoord]; rw [hFc x hx, zero_div]
  have hu_cs := hasCompactSupport_of_supportedIn hu_supp
  have hphi : (phiDoobTest fun y => signedEvenThetaGauge b α₀ y * u y) = F := funext fun x => by
    simp only [phiDoobTest, u, neutralEvenThetaTestCoord, ← mul_assoc]
    change signedEvenThetaProfile b α₀ x * (F x / regularizedEvenThetaProfile c b α₀ x) = F x
    by_cases hx : |x| ≤ c
    · rw [regularizedEvenThetaProfile_eq_of_abs_le hx]
      exact mul_div_cancel₀ (F x) (hpos x (abs_le.mp (hx.trans (by linarith)))).ne'
    · rw [hFc x (not_le.mp hx), zero_div, mul_zero]
  have hquad_pt : (fun x => u x ^ 2 * (signedEvenThetaProfile b α₀ x * Real.cosh (x / 2))) =
      fun x => (F x ^ 2 / regularizedEvenThetaProfile c b α₀ x) * Real.cosh (x / 2) := by
    funext x
    dsimp only [u, neutralEvenThetaTestCoord]
    by_cases hx : |x| ≤ c
    · rw [regularizedEvenThetaProfile_eq_of_abs_le hx]
      have hne := (hpos x (abs_le.mp (hx.trans (by linarith)))).ne'
      dsimp only [α₀] at hne ⊢
      field_simp [hne]
    · rw [hFc x (not_le.mp hx)]
      simp
  have hj := signedJumpEnergy_signedEvenTheta_eq b α₀ hu_diff hu_cs
  rw [hphi, hquad_pt] at hj
  have hden := groundState_outsideCoshDeficit_pos hc.le
  have hcc : (∫ x in Ioo (-c) c, signedEvenThetaProfile b α₀ x * Real.cosh (x / 2)) = α₀ / 2 := by
    have hz : coshCharge (signedEvenThetaGauge b α₀) (Ioo (-c) c) - α₀ / 2 = 0 := by
      rw [coshCharge_signedEvenTheta_sub_half]
      dsimp only [α₀, neutralEvenThetaParam]
      rw [div_mul_cancel₀ _ hden.ne', sub_self]
    unfold coshCharge at hz
    unfold signedEvenThetaProfile
    linarith
  have hlin : (∫ x, u x * (signedEvenThetaProfile b α₀ x * Real.cosh (x / 2))) =
      evenPoleMoment F := by
    have hev := evenPoleMoment_phiDoob_mul (signedEvenThetaGauge b α₀) u
    rw [hphi] at hev
    exact hev.symm
  refine ⟨hj, ?_⟩
  unfold chargeVariance
  rw [hcc, hquad_pt, hlin]
  ring

/-- **Pole-neutral hyperplane `(b, α₀)`-invariance.** On the codimension-one subspace
`evenPoleMoment F = 0`, the `(b, c)`-dependent weight cancels identically between
`signedJumpEnergy` and `2 · chargeVariance`, leaving `archForm F - primeSum F` independent of `b`. -/
theorem neutralEvenTheta_poleNeutral_invariance {c b : ℝ} (hc : 0 < c)
    (hpos : ∀ x ∈ Icc (-(c + 1)) (c + 1),
      0 < signedEvenThetaProfile b (neutralEvenThetaParam b c) x)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : SupportedIn c F)
    (hpole : evenPoleMoment F = 0) :
    signedJumpEnergy (signedEvenThetaProfile b (neutralEvenThetaParam b c))
        (neutralEvenThetaTestCoord c b F) -
      2 * chargeVariance
        (fun x => signedEvenThetaProfile b (neutralEvenThetaParam b c) x * Real.cosh (x / 2))
        (Ioo (-c) c) (neutralEvenThetaTestCoord c b F) =
      archForm F - primeSum F := by
  obtain ⟨hj, hv⟩ := neutralEvenTheta_signedJump_and_variance_eq hc hpos hF hFc
  have hFc_cs := hasCompactSupport_of_supportedIn hFc
  have hm := markovEnergy_ofReal_eq_archForm_sub_primeSum hF hFc_cs
  rw [hj, hv, hpole, hm]
  ring

/-- **Odd-sector variance-retention necessity.** Above `c = 273 / 400`, no choice of shift `a > 0`
in `shiftedGroundState a` can make the variance-dropped odd window lower bound nonnegative; hence
optimizing `(b, a)` across the `{2, 3, 4}` frontier necessarily retains the variance terms. -/
theorem odd_shiftedGroundState_variance_retention_necessary {a c : ℝ}
    (ha : 0 < a) (hc : 273 / 400 < c) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧
      (∀ x, u (-x) = u x) ∧ SupportedIn c u ∧
      2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u +
        8 * outsideCharge a c *
          (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) < 0 := by
  obtain ⟨u, hu, huc, hue, huoff, hneg⟩ :=
    exists_shiftedGroundState_windowLower_neg_below_log_four ha hc
  refine ⟨u, hu, huc, hue, fun x hx => huoff x fun hm => ?_, hneg⟩
  have hle : |x| ≤ c := abs_le.mpr ⟨hm.1.le, hm.2.le⟩
  linarith

/-! ### 2. Quantitative `O(1 / cosh(b / 2))` rescaling and asymptotic `b → ∞` deficit conservation -/

/-- Uniform `O(1 / cosh(b / 2))` convergence of `signedEvenThetaProfile b 0 / (2 cosh(b/2))` to `Φ`
on all of `ℝ`. -/
theorem abs_signedEvenThetaProfile_div_two_cosh_sub_le (b x : ℝ) :
    |signedEvenThetaProfile b 0 x / (2 * Real.cosh (b / 2)) - riemannKernelReal x| ≤
      riemannKernelReal 0 / Real.cosh (b / 2) := by
  have hcpos : 0 < Real.cosh (b / 2) := Real.cosh_pos _
  have h2c : 0 < 2 * Real.cosh (b / 2) := by positivity
  have hdiff : signedEvenThetaProfile b 0 x / (2 * Real.cosh (b / 2)) - riemannKernelReal x =
      -(riemannKernelReal (x - b) + riemannKernelReal (x + b)) / (2 * Real.cosh (b / 2)) := by
    rw [signedEvenThetaProfile_eq]
    field_simp [hcpos.ne']
    ring
  rw [hdiff, abs_div, abs_neg, abs_of_pos h2c]
  have hsum_pos : 0 ≤ riemannKernelReal (x - b) + riemannKernelReal (x + b) :=
    add_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le
  rw [abs_of_nonneg hsum_pos, div_le_div_iff₀ h2c hcpos]
  have h1 := riemannKernelReal_le_zero_point (x - b)
  have h2 := riemannKernelReal_le_zero_point (x + b)
  nlinarith

private theorem tendsto_inv_cosh_half_atTop :
    Tendsto (fun b : ℝ => (Real.cosh (b / 2))⁻¹) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_
    (tendsto_inv_atTop_zero.comp (tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2)))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.cosh_pos _)), Function.comp_apply]
  have hsh := Real.self_le_sinh_iff.mpr (show (0 : ℝ) ≤ b / 2 by positivity)
  have hch : b * (1 / 2) ≤ Real.cosh (b / 2) := by linarith [(Real.sinh_lt_cosh (b / 2)).le]
  exact inv_anti₀ (by positivity) hch

/-- As `b → ∞`, `neutralEvenThetaParam b c / (2 cosh(b/2))` converges to the ratio
`I_Φ(c) / (1/2 - I_Φ(c))` of inside to outside ground-state cosh charge. -/
theorem tendsto_neutralEvenThetaParam_div_two_cosh_atTop {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun b : ℝ => neutralEvenThetaParam b c / (2 * Real.cosh (b / 2))) atTop
      (𝓝 ((∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2)) /
        (1 / 2 - ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2)))) := by
  set I_Φ := ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2)
  set Δ_Φ := 1 / 2 - I_Φ
  have hΔ : 0 < Δ_Φ := groundState_outsideCoshDeficit_pos hc
  have hc_int : IntegrableOn (fun x => Real.cosh (x / 2)) (Ioo (-c) c) :=
    integrableOn_Ioo_of_continuous (Real.continuous_cosh.comp (continuous_id.div_const 2))
  have hnum : Tendsto (fun b : ℝ => coshCharge (signedEvenThetaGauge b 0) (Ioo (-c) c) /
      (2 * Real.cosh (b / 2))) atTop (𝓝 I_Φ) := by
    rw [Metric.tendsto_nhds]
    refine fun ε hε => ?_
    set C := riemannKernelReal 0 * ∫ x in Ioo (-c) c, Real.cosh (x / 2)
    have hlim0 : Tendsto (fun b : ℝ => C * (Real.cosh (b / 2))⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_cosh_half_atTop.const_mul C
    filter_upwards [hlim0.eventually (gt_mem_nhds hε)] with b hb
    rw [Real.dist_eq]
    have h2c : (2 * Real.cosh (b / 2)) ≠ 0 := by positivity
    have hi0 : IntegrableOn (fun x => signedEvenThetaProfile b 0 x * Real.cosh (x / 2)) (Ioo (-c) c) :=
      integrableOn_Ioo_of_continuous
        ((continuous_riemannKernelReal.mul
          (contDiff_translateSpan Finset.univ (signedEvenThetaCoeff b 0) (evenNullShift b)).continuous).mul
          (Real.continuous_cosh.comp (continuous_id.div_const 2)))
    have hiΦ : IntegrableOn (fun x => riemannKernelReal x * Real.cosh (x / 2)) (Ioo (-c) c) :=
      integrableOn_Ioo_of_continuous
        (continuous_riemannKernelReal.mul (Real.continuous_cosh.comp (continuous_id.div_const 2)))
    have hdiff_eq : coshCharge (signedEvenThetaGauge b 0) (Ioo (-c) c) / (2 * Real.cosh (b / 2)) - I_Φ =
        ∫ x in Ioo (-c) c,
          (signedEvenThetaProfile b 0 x / (2 * Real.cosh (b / 2)) - riemannKernelReal x) *
            Real.cosh (x / 2) := by
      unfold coshCharge
      change (∫ x in Ioo (-c) c, signedEvenThetaProfile b 0 x * Real.cosh (x / 2)) /
          (2 * Real.cosh (b / 2)) - I_Φ = _
      rw [← integral_div, ← integral_sub (hi0.div_const _) hiΦ]
      exact setIntegral_congr_fun measurableSet_Ioo fun x _ => by field_simp [h2c]
    rw [hdiff_eq]
    have habs_le : |∫ x in Ioo (-c) c,
          (signedEvenThetaProfile b 0 x / (2 * Real.cosh (b / 2)) - riemannKernelReal x) *
            Real.cosh (x / 2)| ≤ C * (Real.cosh (b / 2))⁻¹ := by
      refine abs_integral_le_integral_abs.trans ?_
      have hdom : IntegrableOn (fun x => (riemannKernelReal 0 / Real.cosh (b / 2)) *
          Real.cosh (x / 2)) (Ioo (-c) c) := hc_int.const_mul _
      have hdiff_int : IntegrableOn (fun x =>
          (signedEvenThetaProfile b 0 x / (2 * Real.cosh (b / 2)) - riemannKernelReal x) *
            Real.cosh (x / 2)) (Ioo (-c) c) :=
        integrableOn_Ioo_of_continuous
          ((((continuous_riemannKernelReal.mul
            (contDiff_translateSpan Finset.univ (signedEvenThetaCoeff b 0) (evenNullShift b)).continuous).div_const _).sub
            continuous_riemannKernelReal).mul (Real.continuous_cosh.comp (continuous_id.div_const 2)))
      refine (setIntegral_mono_on hdiff_int.abs hdom measurableSet_Ioo fun x _ => ?_).trans_eq ?_
      · rw [abs_mul, abs_of_pos (Real.cosh_pos _)]
        exact mul_le_mul_of_nonneg_right (abs_signedEvenThetaProfile_div_two_cosh_sub_le b x)
          (Real.cosh_pos _).le
      · rw [integral_const_mul]; dsimp only [C]; ring
    exact habs_le.trans_lt hb
  have heq : (fun b : ℝ => neutralEvenThetaParam b c / (2 * Real.cosh (b / 2))) =
      fun b : ℝ => (coshCharge (signedEvenThetaGauge b 0) (Ioo (-c) c) /
        (2 * Real.cosh (b / 2))) / Δ_Φ := by
    funext b; unfold neutralEvenThetaParam; dsimp only [Δ_Φ, I_Φ]; rw [div_right_comm]
  rw [heq]
  exact hnum.div_const Δ_Φ

/-- As `b → ∞`, the rescaled neutral signed theta profile converges pointwise to the positive
ground-state multiple `((1/2) / (1/2 - I_Φ(c))) Φ(x)`. -/
theorem tendsto_signedEvenThetaProfile_neutral_div_two_cosh_atTop {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    Tendsto (fun b : ℝ =>
        signedEvenThetaProfile b (neutralEvenThetaParam b c) x / (2 * Real.cosh (b / 2))) atTop
      (𝓝 (((1 / 2) / (1 / 2 - ∫ t in Ioo (-c) c, riemannKernelReal t * Real.cosh (t / 2))) *
        riemannKernelReal x)) := by
  set I_Φ := ∫ t in Ioo (-c) c, riemannKernelReal t * Real.cosh (t / 2)
  set Δ_Φ := 1 / 2 - I_Φ
  have hΔ : 0 < Δ_Φ := groundState_outsideCoshDeficit_pos hc
  have h0 : Tendsto (fun b : ℝ => signedEvenThetaProfile b 0 x / (2 * Real.cosh (b / 2)))
      atTop (𝓝 (riemannKernelReal x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_
      (by simpa using tendsto_inv_cosh_half_atTop.const_mul (riemannKernelReal 0))
    filter_upwards with b
    rw [Real.norm_eq_abs, div_eq_mul_inv]
    simpa [div_eq_mul_inv] using abs_signedEvenThetaProfile_div_two_cosh_sub_le b x
  have hα := (tendsto_neutralEvenThetaParam_div_two_cosh_atTop hc).mul_const (riemannKernelReal x)
  have heq : (fun b : ℝ =>
        signedEvenThetaProfile b (neutralEvenThetaParam b c) x / (2 * Real.cosh (b / 2))) =
      fun b : ℝ => signedEvenThetaProfile b 0 x / (2 * Real.cosh (b / 2)) +
        (neutralEvenThetaParam b c / (2 * Real.cosh (b / 2))) * riemannKernelReal x := by
    funext b; rw [signedEvenThetaProfile_eq_add_mul]; ring
  rw [heq]
  convert h0.add hα using 2
  change ((1 / 2) / Δ_Φ) * riemannKernelReal x =
    riemannKernelReal x + (I_Φ / Δ_Φ) * riemannKernelReal x
  have hhalf : (1 / 2 : ℝ) = Δ_Φ + I_Φ := by dsimp only [Δ_Φ]; ring
  rw [hhalf, add_div, div_self hΔ.ne']
  ring

private lemma markovEnergy_eq_groundState_jump_sub_cosh {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    markovEnergy (fun x => (F x : ℂ)) =
      signedJumpEnergy riemannKernelReal (fun x => F x / riemannKernelReal x) -
        ∫ x, (F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2) := by
  set u₀ : ℝ → ℝ := fun x => F x / riemannKernelReal x
  have hu₀ : ContDiff ℝ 2 u₀ :=
    hF.div contDiff_riemannKernelReal fun x => (riemannKernelReal_pos x).ne'
  have hu₀c : HasCompactSupport u₀ :=
    hFc.mono fun x hx => fun hFx => hx (by dsimp only [u₀]; rw [hFx, zero_div])
  let s₀ : Finset (Fin 1) := {0}
  let α₀ : Fin 1 → ℝ := fun _ => 1
  let b₀ : Fin 1 → ℝ := fun _ => 0
  have hspan : ∀ x, translateSpan s₀ α₀ b₀ x = 1 := fun x => by
    simp [translateSpan, translateGroundState, s₀, α₀, b₀,
      div_self (riemannKernelReal_pos x).ne']
  have hphi : (phiDoobTest fun y => translateSpan s₀ α₀ b₀ y * u₀ y) = F := funext fun x => by
    simp only [phiDoobTest, hspan, one_mul, u₀, mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']
  have hM : (fun y => riemannKernelReal y * translateSpan s₀ α₀ b₀ y) = riemannKernelReal :=
    funext fun y => by rw [hspan, mul_one]
  have hm := markovEnergy_thetaGauge s₀ α₀ b₀ hu₀ hu₀c
  rw [hphi, hM] at hm
  simp only [hspan, mul_one] at hm
  have hsrc : (∫ x, u₀ x ^ 2 * riemannKernelReal x * translateSource s₀ α₀ b₀ x) =
      -∫ x, (F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2) := by
    have hpt : (fun x => u₀ x ^ 2 * riemannKernelReal x * translateSource s₀ α₀ b₀ x) =
        fun x => -((F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2)) := funext fun x => by
      simp only [translateSource, translateCoshCoefficient, translateSinhCoefficient,
        s₀, α₀, b₀, Finset.sum_singleton, zero_div, Real.cosh_zero, Real.sinh_zero, u₀]
      have hne := (riemannKernelReal_pos x).ne'
      field_simp [hne]
      ring
    rw [hpt, integral_neg]
  rw [hsrc] at hm
  linarith

/-- **Asymptotic `b → ∞` deficit conservation law.** As the negative pockets `±b → ±∞`,
`2 · chargeVariance` in the neutral signed theta gauge converges to the ground-state window
variance `2 V_{Φ cosh}^{(-c, c)}(F / Φ)`, while `signedJumpEnergy` converges to
`J_Φ(F / Φ) - 2 Δ_Φ(c) ∫ (F² / Φ) cosh(x/2)`: the exterior prime-power jumps into `±b` conserve
the exact ground-state outside cosh deficit `Δ_Φ(c) = 1/2 - ∫_{(-c, c)} Φ cosh`. -/
theorem tendsto_neutralEvenTheta_signedJump_and_variance_atTop {c : ℝ} (hc : 0 < c)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : SupportedIn c F) :
    Tendsto (fun b : ℝ =>
        signedJumpEnergy (signedEvenThetaProfile b (neutralEvenThetaParam b c))
          (neutralEvenThetaTestCoord c b F)) atTop
      (𝓝 (signedJumpEnergy riemannKernelReal (fun x => F x / riemannKernelReal x) -
        2 * (1 / 2 - ∫ t in Ioo (-c) c, riemannKernelReal t * Real.cosh (t / 2)) *
          ∫ x, (F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2))) ∧
    Tendsto (fun b : ℝ =>
        2 * chargeVariance
          (fun x => signedEvenThetaProfile b (neutralEvenThetaParam b c) x * Real.cosh (x / 2))
          (Ioo (-c) c) (neutralEvenThetaTestCoord c b F)) atTop
      (𝓝 (2 * chargeVariance (fun x => riemannKernelReal x * Real.cosh (x / 2))
        (Ioo (-c) c) (fun x => F x / riemannKernelReal x))) := by
  set I_Φ := ∫ t in Ioo (-c) c, riemannKernelReal t * Real.cosh (t / 2)
  set Δ_Φ := 1 / 2 - I_Φ
  have hΔ : 0 < Δ_Φ := groundState_outsideCoshDeficit_pos hc.le
  have hFc_cs := hasCompactSupport_of_supportedIn hFc
  -- Uniform lower bound on `Φ` over `[-(c + 1), c + 1]`
  obtain ⟨x₀, _, hx₀min⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by linarith : -(c + 1) ≤ c + 1)) continuous_riemannKernelReal.continuousOn
  set m_Φ := riemannKernelReal x₀
  have hm_pos : 0 < m_Φ := riemannKernelReal_pos x₀
  -- Eventual positivity on `[-(c + 1), c + 1]` for all large `b`
  have hev_pos : ∀ᶠ b : ℝ in atTop,
      ∀ x ∈ Icc (-(c + 1)) (c + 1), 0 < signedEvenThetaProfile b (neutralEvenThetaParam b c) x := by
    filter_upwards [eventually_gt_atTop (max 0 (4 * riemannKernelReal 0 / m_Φ))] with b hb x hx
    have hb0 : 0 < b := (le_max_left _ _).trans_lt hb
    have hb_gt : 4 * riemannKernelReal 0 / m_Φ < b := (le_max_right _ _).trans_lt hb
    have hmul : 4 * riemannKernelReal 0 < b * m_Φ := (div_lt_iff₀ hm_pos).mp hb_gt
    have hsh := Real.self_le_sinh_iff.mpr (show (0 : ℝ) ≤ b / 2 by positivity)
    have hcosh : b / 2 ≤ Real.cosh (b / 2) := by linarith [(Real.sinh_lt_cosh (b / 2)).le]
    have h1 := riemannKernelReal_le_zero_point (x - b)
    have h2 := riemannKernelReal_le_zero_point (x + b)
    have hΦx : m_Φ ≤ riemannKernelReal x := hx₀min hx
    have hnum0 : 0 ≤ coshCharge (signedEvenThetaGauge b 0) (Ioo (-c) c) := by
      unfold coshCharge
      refine setIntegral_nonneg measurableSet_Ioo fun y hy => mul_nonneg ?_ (Real.cosh_pos _).le
      have hyI : y ∈ Icc (-(c + 1)) (c + 1) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hyΦ : m_Φ ≤ riemannKernelReal y := hx₀min hyI
      have hy1 := riemannKernelReal_le_zero_point (y - b)
      have hy2 := riemannKernelReal_le_zero_point (y + b)
      change 0 ≤ signedEvenThetaProfile b 0 y
      rw [signedEvenThetaProfile_eq]
      nlinarith [mul_le_mul_of_nonneg_right hcosh (riemannKernelReal_pos y).le]
    have hα_nn : 0 ≤ neutralEvenThetaParam b c := div_nonneg hnum0 hΔ.le
    rw [signedEvenThetaProfile_eq]
    nlinarith [mul_le_mul_of_nonneg_right hcosh (riemannKernelReal_pos x).le,
      mul_nonneg hα_nn (riemannKernelReal_pos x).le]
  -- Key scalar-controlled convergence of the weighted integral
  have hint_lim : Tendsto (fun b : ℝ =>
        neutralEvenThetaParam b c *
          ∫ x, (F x ^ 2 /
            regularizedEvenThetaProfile c b (neutralEvenThetaParam b c) x) * Real.cosh (x / 2))
      atTop (𝓝 (2 * I_Φ * ∫ x, (F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2))) := by
    set α_sc : ℝ → ℝ := fun b => neutralEvenThetaParam b c / (2 * Real.cosh (b / 2))
    set q_lim : ℝ := (1 / 2) / Δ_Φ
    have hq_pos : 0 < q_lim := by dsimp only [q_lim]; positivity
    have hα_lim : Tendsto α_sc atTop (𝓝 (I_Φ / Δ_Φ)) :=
      tendsto_neutralEvenThetaParam_div_two_cosh_atTop hc.le
    have h1pα_lim : Tendsto (fun b => 1 + α_sc b) atTop (𝓝 q_lim) := by
      convert tendsto_const_nhds.add hα_lim using 2
      have hhalf : (1 / 2 : ℝ) = Δ_Φ + I_Φ := by dsimp only [Δ_Φ]; ring
      dsimp only [q_lim]
      rw [hhalf, add_div, div_self hΔ.ne']
    set γ : ℝ → ℝ := fun b =>
      |1 + α_sc b - q_lim| * riemannKernelReal 0 + riemannKernelReal 0 * (Real.cosh (b / 2))⁻¹
    have hγ_lim : Tendsto γ atTop (𝓝 0) := by
      have t1 : Tendsto (fun b => |1 + α_sc b - q_lim| * riemannKernelReal 0) atTop (𝓝 0) := by
        simpa using (tendsto_iff_norm_sub_tendsto_zero.mp h1pα_lim).mul_const (riemannKernelReal 0)
      have t2 : Tendsto (fun b => riemannKernelReal 0 * (Real.cosh (b / 2))⁻¹) atTop (𝓝 0) := by
        simpa using tendsto_inv_cosh_half_atTop.const_mul (riemannKernelReal 0)
      simpa using t1.add t2
    set η : ℝ → ℝ := fun b =>
      (|α_sc b - I_Φ / Δ_Φ| * riemannKernelReal 0 + 2 * |I_Φ| * γ b) /
        ((q_lim / 2 * m_Φ) * m_Φ)
    have hη_lim : Tendsto η atTop (𝓝 0) := by
      have t1 : Tendsto (fun b => |α_sc b - I_Φ / Δ_Φ| * riemannKernelReal 0) atTop (𝓝 0) := by
        simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hα_lim).mul_const (riemannKernelReal 0)
      have t2 : Tendsto (fun b => 2 * |I_Φ| * γ b) atTop (𝓝 0) := by
        simpa using hγ_lim.const_mul (2 * |I_Φ|)
      simpa using (t1.add t2).div_const ((q_lim / 2 * m_Φ) * m_Φ)
    have hc_supp : ∀ x, x ∉ Icc (-c) c → F x = 0 := fun x hx =>
      hFc x (not_le.mp fun hle => hx (abs_le.mp hle))
    set M_F := ∫ x, F x ^ 2 * Real.cosh (x / 2)
    have hi_MF : Integrable fun x => F x ^ 2 * Real.cosh (x / 2) :=
      ((hF.continuous.pow 2).mul
        (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
        (HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c))
          fun x hx => by simp [hc_supp x hx])
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using hη_lim.mul_const M_F)
    filter_upwards [hev_pos, hγ_lim.eventually (gt_mem_nhds (by positivity : 0 < q_lim / 2 * m_Φ))]
      with b hbpos hγ_small
    rw [Real.norm_eq_abs]
    have hi1 : Integrable fun x => neutralEvenThetaParam b c *
        ((F x ^ 2 / regularizedEvenThetaProfile c b (neutralEvenThetaParam b c) x) *
          Real.cosh (x / 2)) := by
      have hc_reg : Continuous fun x =>
          neutralEvenThetaParam b c *
            ((F x ^ 2 / regularizedEvenThetaProfile c b (neutralEvenThetaParam b c) x) *
              Real.cosh (x / 2)) :=
        continuous_const.mul
          (((hF.continuous.pow 2).div (contDiff_regularizedEvenThetaProfile _ _ _).continuous
            fun x => (regularizedEvenThetaProfile_pos hbpos x).ne').mul
            (Real.continuous_cosh.comp (continuous_id.div_const 2)))
      exact hc_reg.integrable_of_hasCompactSupport
        (HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c))
          fun x hx => by simp [hc_supp x hx])
    have hi2 : Integrable fun x => (2 * I_Φ) *
        ((F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2)) := by
      have hc_Φ : Continuous fun x =>
          (2 * I_Φ) * ((F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2)) :=
        continuous_const.mul
          (((hF.continuous.pow 2).div continuous_riemannKernelReal
            fun x => (riemannKernelReal_pos x).ne').mul
            (Real.continuous_cosh.comp (continuous_id.div_const 2)))
      exact hc_Φ.integrable_of_hasCompactSupport
        (HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c))
          fun x hx => by simp [hc_supp x hx])
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub hi1 hi2]
    refine abs_integral_le_integral_abs.trans ?_
    refine (integral_mono (hi1.sub hi2).abs (hi_MF.const_mul (η b)) fun x => ?_).trans_eq
      (integral_const_mul (η b) _)
    change |neutralEvenThetaParam b c *
        ((F x ^ 2 / regularizedEvenThetaProfile c b (neutralEvenThetaParam b c) x) *
          Real.cosh (x / 2)) -
        2 * I_Φ * ((F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2))| ≤
      η b * (F x ^ 2 * Real.cosh (x / 2))
    by_cases hx : |x| ≤ c
    · rw [regularizedEvenThetaProfile_eq_of_abs_le hx]
      set M_sc := signedEvenThetaProfile b (neutralEvenThetaParam b c) x / (2 * Real.cosh (b / 2))
      have h2c : 0 < 2 * Real.cosh (b / 2) := by positivity
      have hΦx_pos := riemannKernelReal_pos x
      have hxI : x ∈ Icc (-(c + 1)) (c + 1) := abs_le.mp (hx.trans (by linarith))
      have hΦx_ge : m_Φ ≤ riemannKernelReal x := hx₀min hxI
      have hM_pos : 0 < signedEvenThetaProfile b (neutralEvenThetaParam b c) x := hbpos x hxI
      have hMsc_pos : 0 < M_sc := div_pos hM_pos h2c
      have hratio : neutralEvenThetaParam b c /
          signedEvenThetaProfile b (neutralEvenThetaParam b c) x = α_sc b / M_sc := by
        dsimp only [α_sc, M_sc]; rw [div_div_div_cancel_right₀ h2c.ne']
      have hMsc_diff : |M_sc - q_lim * riemannKernelReal x| ≤ γ b := by
        have hsplit : M_sc - q_lim * riemannKernelReal x =
            (1 + α_sc b - q_lim) * riemannKernelReal x +
              (signedEvenThetaProfile b 0 x / (2 * Real.cosh (b / 2)) - riemannKernelReal x) := by
          dsimp only [M_sc, α_sc]
          rw [signedEvenThetaProfile_eq_add_mul]
          field_simp [h2c.ne']
          ring
        rw [hsplit]
        refine (abs_add_le _ _).trans (add_le_add ?_
          (by simpa [div_eq_mul_inv] using abs_signedEvenThetaProfile_div_two_cosh_sub_le b x))
        rw [abs_mul, abs_of_pos hΦx_pos]
        exact mul_le_mul_of_nonneg_left (riemannKernelReal_le_zero_point x) (abs_nonneg _)
      have hMsc_lower : q_lim / 2 * m_Φ ≤ M_sc := by
        have hqΦ : q_lim * m_Φ ≤ q_lim * riemannKernelReal x :=
          mul_le_mul_of_nonneg_left hΦx_ge hq_pos.le
        have hl := (abs_le.mp hMsc_diff).1
        linarith
      have hnum_bound : |α_sc b * riemannKernelReal x - 2 * I_Φ * M_sc| ≤
          |α_sc b - I_Φ / Δ_Φ| * riemannKernelReal 0 + 2 * |I_Φ| * γ b := by
        have h2Iq : 2 * I_Φ * q_lim = I_Φ / Δ_Φ := by
          dsimp only [q_lim]; field_simp [hΔ.ne']
        have hsplit : α_sc b * riemannKernelReal x - 2 * I_Φ * M_sc =
            (α_sc b - I_Φ / Δ_Φ) * riemannKernelReal x -
              2 * I_Φ * (M_sc - q_lim * riemannKernelReal x) := by
          linear_combination -riemannKernelReal x * h2Iq
        rw [hsplit]
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos hΦx_pos]
          exact mul_le_mul_of_nonneg_left (riemannKernelReal_le_zero_point x) (abs_nonneg _)
        · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact mul_le_mul_of_nonneg_left hMsc_diff (by positivity)
      have hden_ge : (q_lim / 2 * m_Φ) * m_Φ ≤ M_sc * riemannKernelReal x :=
        mul_le_mul hMsc_lower hΦx_ge hm_pos.le (by positivity)
      have hrat_diff : |α_sc b / M_sc - 2 * I_Φ / riemannKernelReal x| ≤ η b := by
        rw [div_sub_div _ _ hMsc_pos.ne' hΦx_pos.ne', abs_div,
          abs_of_pos (mul_pos hMsc_pos hΦx_pos), mul_comm M_sc (2 * I_Φ)]
        exact (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden_ge).trans
          (div_le_div_of_nonneg_right hnum_bound (by positivity))
      have hfactor : neutralEvenThetaParam b c *
            ((F x ^ 2 / signedEvenThetaProfile b (neutralEvenThetaParam b c) x) *
              Real.cosh (x / 2)) -
          2 * I_Φ * ((F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2)) =
          (α_sc b / M_sc - 2 * I_Φ / riemannKernelReal x) * (F x ^ 2 * Real.cosh (x / 2)) := by
        have : neutralEvenThetaParam b c *
            ((F x ^ 2 / signedEvenThetaProfile b (neutralEvenThetaParam b c) x) *
              Real.cosh (x / 2)) =
            (neutralEvenThetaParam b c /
              signedEvenThetaProfile b (neutralEvenThetaParam b c) x) *
              (F x ^ 2 * Real.cosh (x / 2)) := by ring
        rw [this, hratio]; ring
      rw [hfactor, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.cosh_pos _).le)]
      exact mul_le_mul_of_nonneg_right hrat_diff (mul_nonneg (sq_nonneg _) (Real.cosh_pos _).le)
    · rw [hFc x (not_le.mp hx)]
      simp
  -- Assemble the two limits from the finite-`b` decomposition and `markovEnergy_eq_groundState_jump_sub_cosh`
  have hm_eq := markovEnergy_eq_groundState_jump_sub_cosh hF hFc_cs
  have hvar_Φ : 2 * chargeVariance (fun x => riemannKernelReal x * Real.cosh (x / 2))
        (Ioo (-c) c) (fun x => F x / riemannKernelReal x) =
      2 * I_Φ * (∫ x, (F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2)) -
        2 * evenPoleMoment F ^ 2 := by
    unfold chargeVariance evenPoleMoment
    have h1 : (fun x => (F x / riemannKernelReal x) ^ 2 *
          (riemannKernelReal x * Real.cosh (x / 2))) =
        fun x => (F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2) := funext fun x => by
      have hne := (riemannKernelReal_pos x).ne'; field_simp [hne]
    have h2 : (fun x => (F x / riemannKernelReal x) *
          (riemannKernelReal x * Real.cosh (x / 2))) =
        fun x => F x * Real.cosh (x / 2) := funext fun x => by
      have hne := (riemannKernelReal_pos x).ne'; field_simp [hne]
    rw [h1, h2]
    dsimp only [I_Φ]
    ring
  refine ⟨?_, ?_⟩
  · have hlim1 : Tendsto (fun b => markovEnergy (fun x => (F x : ℂ)) +
        neutralEvenThetaParam b c *
          ∫ x, (F x ^ 2 /
            regularizedEvenThetaProfile c b (neutralEvenThetaParam b c) x) * Real.cosh (x / 2))
        atTop (𝓝 (signedJumpEnergy riemannKernelReal (fun x => F x / riemannKernelReal x) -
          2 * Δ_Φ * ∫ x, (F x ^ 2 / riemannKernelReal x) * Real.cosh (x / 2))) := by
      convert tendsto_const_nhds.add hint_lim using 2
      rw [hm_eq]
      dsimp only [Δ_Φ, I_Φ]
      ring
    refine hlim1.congr' ?_
    filter_upwards [hev_pos] with b hbpos
    exact ((neutralEvenTheta_signedJump_and_variance_eq hc hbpos hF hFc).1).symm
  · rw [hvar_Φ]
    refine (hint_lim.sub_const (2 * evenPoleMoment F ^ 2)).congr' ?_
    filter_upwards [hev_pos] with b hbpos
    exact ((neutralEvenTheta_signedJump_and_variance_eq hc hbpos hF hFc).2).symm

/-! ### 3. `{2, 3, 4}` endpoint-sliver structure and sub-unit outward Lévy edge-carry up to `2c = log 5` -/

/-- `log 5 / 2 < log 3` (`5 < 3² = 9`), so throughout the entire `{2, 3, 4}` reflection band
`2c ≤ log 5`, the half-window width `c` stays strictly below `log 3`. -/
theorem half_log_five_lt_log_three : Real.log 5 / 2 < Real.log 3 := by
  have h59 : Real.log 5 < Real.log ((3 : ℝ) ^ 2) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h59
  push_cast at h59
  linarith

/-- Explicit elementary upper bound `log 3 < 10987 / 10000` (`log(3/4) = log 3 - 2 log 2`). -/
private theorem log_three_lt_rational : Real.log 3 < 10987 / 10000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 4 : ℝ)| < 1 by norm_num) 8
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, abs_le] at h
  have e : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [e] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith [h.2, Real.log_two_lt_d9]

/-- **Exact `{2, 3, 4}` reflection truncation below `2c = log 5`.** For `0 ≤ c` with `2c < log 5`
(crossing both `2c = log 3` and `2c = log 4`) and `f ∈ C²_c(ℝ)` supported in `[m - c, m]`,
`orderedCoupling f (collarReflect m f)` truncates identically to the three prime powers `2, 3, 4`. -/
theorem orderedCoupling_collarReflect_eq_two_three_four_of_lt_half_log_five {m c : ℝ}
    (hc : 0 ≤ c) (hc5 : 2 * c < Real.log 5) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hm : ∀ u, m < u → f u = 0) (hleft : ∀ u, u < m - c → f u = 0) :
    orderedCoupling f (collarReflect m f) =
      collarHankel m f -
        vonMangoldtAtom 2 * selfConv f (2 * m - Real.log 2) -
        vonMangoldtAtom 3 * selfConv f (2 * m - Real.log 3) -
        vonMangoldtAtom 4 * selfConv f (2 * m - Real.log 4) := by
  rw [orderedCoupling_collarReflect_eq_finsetSum hc hf hm hleft]
  have hfl : ⌊Real.exp (2 * c)⌋₊ ≤ 4 := by
    have hexp5 : Real.exp (2 * c) < 5 := by
      calc Real.exp (2 * c) < Real.exp (Real.log 5) := Real.exp_lt_exp.mpr hc5
        _ = 5 := Real.exp_log (by norm_num)
    by_contra hgt
    have h5 : (5 : ℝ) ≤ Real.exp (2 * c) := by
      exact_mod_cast (Nat.le_floor_iff (Real.exp_pos _).le).mp (by omega : 5 ≤ ⌊Real.exp (2 * c)⌋₊)
    linarith
  have hsub : Finset.Icc 2 ⌊Real.exp (2 * c)⌋₊ ⊆ ({2, 3, 4} : Finset ℕ) := fun n hn => by
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hn ⊢
    omega
  have hsum : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * c)⌋₊,
        vonMangoldtAtom n * selfConv f (2 * m - Real.log n)) =
      ∑ n ∈ ({2, 3, 4} : Finset ℕ),
        vonMangoldtAtom n * selfConv f (2 * m - Real.log n) := by
    refine Finset.sum_subset hsub fun n _ hn => ?_
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn2 | hgt
    · simp [vonMangoldtAtom, hn2]
    · have hexp : Real.exp (2 * c) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hgt
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      rw [selfConv_eq_zero_of_two_mul_lt hc hleft ((Real.lt_log_iff_exp_lt hn0).mpr hexp), mul_zero]
  rw [hsum]
  simp only [Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ ({4} : Finset ℕ)), Finset.sum_singleton]
  ring

/-- **Half-window `n = 2`-only diagonal sliver law across the entire `{2, 3, 4}` band.** For any
`0 ≤ c < log 3` (in particular every `0 ≤ c ≤ (log 5) / 2`) and `f` vanishing outside `[m - c, m]`,
primes `3` and `4` do not act in `primeSum f` at all: `primeSum f = 2 w₂ autocorr f (log 2)`, which
moreover vanishes identically for `c ≤ log 2` (`2c ≤ log 4`). -/
theorem primeSum_eq_two_sliver_of_collarWindow_lt_log_three {m c : ℝ}
    (hc : 0 ≤ c) (hc3 : c < Real.log 3) {f : ℝ → ℝ}
    (hm : ∀ u, m < u → f u = 0) (hleft : ∀ u, u < m - c → f u = 0) :
    primeSum f = 2 * vonMangoldtAtom 2 * autocorr f (Real.log 2) ∧
      (c ≤ Real.log 2 → primeSum f = 0) := by
  set g : ℝ → ℝ := fun v => f (v + (m - c / 2))
  have hgs : ∀ v, c / 2 < |v| → g v = 0 := fun v hv => by
    dsimp only [g]
    rcases lt_abs.mp hv with hpos | hneg
    · exact hm _ (by linarith)
    · exact hleft _ (by linarith)
  have hauto_eq : ∀ t : ℝ, autocorr g t = autocorr f t := fun t => by
    unfold autocorr
    dsimp only [g]
    have hshift : (fun u => f (u + (m - c / 2)) * f (u + t + (m - c / 2))) =
        fun u => f (u + (m - c / 2)) * f ((u + (m - c / 2)) + t) :=
      funext fun u => by congr 2; ring
    rw [hshift, integral_add_right_eq_self (fun w => f w * f (w + t)) (m - c / 2)]
  have hps_eq : primeSum f = primeSum g := by
    have hterm : ∀ (h : ℝ → ℝ) (n : ℕ),
        (∫ u, h u * h (u - Real.log n)) + (∫ u, h u * h (u + Real.log n)) =
          2 * autocorr h (Real.log n) := fun h n => by
      change autocorr h (-Real.log n) + autocorr h (Real.log n) = _
      rw [autocorr_neg]; ring
    unfold primeSum
    simp_rw [hterm, hauto_eq]
  have hfl : ⌊Real.exp (2 * (c / 2))⌋₊ ≤ 2 := by
    rw [show 2 * (c / 2) = c by ring]
    have hexp3 : Real.exp c < 3 := by
      calc Real.exp c < Real.exp (Real.log 3) := Real.exp_lt_exp.mpr hc3
        _ = 3 := Real.exp_log (by norm_num)
    by_contra hgt
    have h3 : (3 : ℝ) ≤ Real.exp c := by
      exact_mod_cast (Nat.le_floor_iff (Real.exp_pos _).le).mp (by omega : 3 ≤ ⌊Real.exp c⌋₊)
    linarith
  have hp_g := primeSum_eq_finsetSum_of_radius hgs
  have hsum2 : primeSum f = 2 * vonMangoldtAtom 2 * autocorr f (Real.log 2) := by
    rw [hps_eq, hp_g]
    have hsub : Finset.Icc 2 ⌊Real.exp (2 * (c / 2))⌋₊ ⊆ ({2} : Finset ℕ) := fun n hn => by
      simp only [Finset.mem_Icc, Finset.mem_singleton] at hn ⊢
      omega
    rw [Finset.sum_subset hsub]
    · simp [hauto_eq]
    · intro n _ hn
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      rcases hn with hn2 | hgt
      · simp [vonMangoldtAtom, hn2]
      · have hexp : Real.exp (2 * (c / 2)) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hgt
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hlog : 2 * (c / 2) < |Real.log n| := by
          rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))]
          exact (Real.lt_log_iff_exp_lt hn0).mpr hexp
        rw [autocorr_zero_of_radius hgs hlog, mul_zero]
  refine ⟨hsum2, fun hc2 => ?_⟩
  rw [hsum2, ← hauto_eq]
  rcases lt_or_eq_of_le hc2 with hlt | rfl
  · rw [autocorr_zero_of_radius hgs (by
      rw [abs_of_pos (Real.log_pos (by norm_num))]
      linarith), mul_zero]
  · -- At `c = log 2`, the overlap is the single point `v = -(log 2)/2`, of measure zero
    have hae : ∀ᵐ v : ℝ, g v * g (v + Real.log 2) = 0 := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (-(Real.log 2 / 2)))] with v hv
      simp only [mem_compl_iff, mem_singleton_iff] at hv
      rcases lt_trichotomy v (-(Real.log 2 / 2)) with hlt | heq | hgt
      · rw [hgs v (lt_abs.mpr (Or.inr (by linarith))), zero_mul]
      · exact absurd heq hv
      · rw [hgs (v + Real.log 2) (lt_abs.mpr (Or.inl (by linarith))), mul_zero]
    have hz : autocorr g (Real.log 2) = 0 := integral_eq_zero_of_ae hae
    rw [hz, mul_zero]

/-- **Sub-unit collective `{2, 3, 4}` outward Lévy edge-carry up to `2c = log 5`.** Throughout
`c ≤ (log 5) / 2` (`2c ≤ log 5`, across both `2c = log 3` and `2c = log 4`), the three reflection
prime-power kicks `{2, 3, 4}` together consume strictly less than `991 / 1000 < 1` of `levyEnergy f`,
leaving at least `(9 / 1000) · levyEnergy f` spare on every collar `[m - c, m]`. -/
theorem twoThreeFour_collarKicks_le_levyEnergy {m c : ℝ} (hc : c ≤ Real.log 5 / 2)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hleft : ∀ u, u < m - c → f u = 0) :
    vonMangoldtAtom 2 * |selfConv f (2 * m - Real.log 2)| +
        vonMangoldtAtom 3 * |selfConv f (2 * m - Real.log 3)| +
        vonMangoldtAtom 4 * |selfConv f (2 * m - Real.log 4)| ≤
      (3 * Real.log 2 / 8 + Real.log 3 / 6) * Real.sqrt 5 * levyEnergy f ∧
    (3 * Real.log 2 / 8 + Real.log 3 / 6) * Real.sqrt 5 < 991 / 1000 := by
  set f₀ : ℝ → ℝ := fun u => f (u + m)
  have hf₀ : ContDiff ℝ 2 f₀ := hf.comp (contDiff_id.add contDiff_const)
  have hf₀c : HasCompactSupport f₀ := hfc.comp_homeomorph (Homeomorph.addRight m)
  have hf₀L : ∀ u, u < -c → f₀ u = 0 := fun u hu => hleft (u + m) (by linarith)
  have hlevy_eq : levyEnergy f₀ = levyEnergy f := by
    unfold levyEnergy
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => congrArg (archLevyDensity x * ·) ?_
    dsimp only [f₀]
    have hsh : (fun u => (f (u + m) - f (u + x + m)) ^ 2) =
        fun u => (f (u + m) - f ((u + m) + x)) ^ 2 := funext fun u => by congr 2; ring
    rw [hsh, integral_add_right_eq_self (fun w => (f w - f (w + x)) ^ 2) m]
  have hL := SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' f
  have h2 := vonMangoldtAtom_mul_abs_selfConv_le hf₀ hf₀c hf₀L 2
  have h3 := vonMangoldtAtom_mul_abs_selfConv_le hf₀ hf₀c hf₀L 3
  have h4 := vonMangoldtAtom_mul_abs_selfConv_le hf₀ hf₀c hf₀L 4
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h2
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three] at h3
  have hΛ4 : (ArithmeticFunction.vonMangoldt 4 : ℝ) = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    push_cast; rfl
  rw [hΛ4] at h4
  rw [← selfConv_shift_centre m, hlevy_eq] at h2 h3 h4
  have hec : Real.exp c ≤ Real.sqrt 5 := by
    calc Real.exp c ≤ Real.exp (Real.log 5 / 2) := Real.exp_le_exp.mpr hc
      _ = Real.exp (Real.log (Real.sqrt 5)) := by rw [Real.log_sqrt (by norm_num)]
      _ = Real.sqrt 5 := Real.exp_log (Real.sqrt_pos.mpr (by norm_num))
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  push_cast at h2 h3 h4
  have hsum : vonMangoldtAtom 2 * |selfConv f (2 * m - Real.log 2)| +
        vonMangoldtAtom 3 * |selfConv f (2 * m - Real.log 3)| +
        vonMangoldtAtom 4 * |selfConv f (2 * m - Real.log 4)| ≤
      (3 * Real.log 2 / 8 + Real.log 3 / 6) * Real.sqrt 5 * levyEnergy f := by
    have hcoeff : Real.log 2 * Real.exp c / (2 * 2) +
          Real.log 3 * Real.exp c / (2 * 3) +
          Real.log 2 * Real.exp c / (2 * 4) ≤
        (3 * Real.log 2 / 8 + Real.log 3 / 6) * Real.sqrt 5 := by
      have : Real.log 2 * Real.exp c / (2 * 2) + Real.log 3 * Real.exp c / (2 * 3) +
            Real.log 2 * Real.exp c / (2 * 4) =
          (3 * Real.log 2 / 8 + Real.log 3 / 6) * Real.exp c := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hec (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hL]
  refine ⟨hsum, ?_⟩
  have h2_lt : Real.log 2 < 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have h3_lt : Real.log 3 < 10987 / 10000 := log_three_lt_rational
  have h5_lt : Real.sqrt 5 < 22361 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hlin : 3 * Real.log 2 / 8 + Real.log 3 / 6 < 4431 / 10000 := by linarith
  have h5_nn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

/-! ### 4. Infinite-tower super-`enlargedWeilFloorAperture` sliver floors & joint `{2, 3, 4}` equivalence -/

/-- **Unconditional infinite-tower collective sliver floor.** For every `k : ℕ`, every centre
`m ∈ ℝ`, every `0 < c ≤ weilFloorApertureTower k` (strictly exceeding both
`enlargedWeilFloorAperture` and `successorWeilFloorAperture` for `k ≥ 1`), and every `f ∈ C²_c(ℝ)`
supported in `[m - c, m]`, `weilFloorTowerConst k * ∫ f² ≤ W(f) - |𝒞_m(f)|`. -/
theorem weilQuad_sub_abs_orderedCoupling_ge_of_le_weilFloorApertureTower (k : ℕ) {m c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ weilFloorApertureTower k) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hm : ∀ u, m < u → f u = 0) (hleft : ∀ u, u < m - c → f u = 0) :
    weilFloorTowerConst k * (∫ u, f u ^ 2) ≤
      weilQuad f - |orderedCoupling f (collarReflect m f)| := by
  have hfc := hasCompactSupport_of_collarWindow hm hleft
  rw [weilQuad_sub_abs_orderedCoupling_eq_half_min hf hfc hm]
  have hGp_diff := contDiff_reflectionEvenProfile (m := m) hf
  have hGm_diff := contDiff_reflectionOddProfile (m := m) hf
  have hGp_supp := supportedIn_reflectionEvenProfile hc0.le hm hleft
  have hGm_supp := supportedIn_reflectionOddProfile hc0.le hm hleft
  have hGp_cs := hasCompactSupport_of_supportedIn hGp_supp
  have hGm_cs := hasCompactSupport_of_supportedIn hGm_supp
  have hGp_floor := fullZeroForm_ge_of_support_le_weilFloorApertureTower k hGp_diff hGp_cs
    fun u hu => hGp_supp u (hc.trans_lt hu)
  have hGm_floor := fullZeroForm_ge_of_support_le_weilFloorApertureTower k hGm_diff hGm_cs
    fun u hu => hGm_supp u (hc.trans_lt hu)
  rw [fullZeroForm_eq_weilQuad_of_cont hGp_diff.continuous hGp_cs] at hGp_floor
  rw [fullZeroForm_eq_weilQuad_of_cont hGm_diff.continuous hGm_cs] at hGm_floor
  obtain ⟨hGp_L2, hGm_L2⟩ := integral_reflectionProfile_sq hc0.le hf.continuous hm hleft
  rw [hGp_L2] at hGp_floor
  rw [hGm_L2] at hGm_floor
  have hmin : weilFloorTowerConst k * (2 * ∫ u, f u ^ 2) ≤
      min (weilQuad (reflectionEvenProfile m f)) (weilQuad (reflectionOddProfile m f)) :=
    le_min hGp_floor hGm_floor
  linarith only [hmin]

/-- **Joint neutral signed theta-gauge & `{2, 3, 4}` endpoint-sliver equivalence up to `2c = log 5`.**
Across the entire `{2, 3, 4}` band `0 < c < (log 5) / 2` (`2c < log 5`, crossing both `2c = log 3`
and `2c = log 4`), for every odd shift `a > 0`, `ZetaWindowPositive c` is unconditionally equivalent
both to the `{2, 3, 4}` half-window endpoint-sliver band inequality (with `primeSum` reduced to the
single `n = 2` sliver) and to the joint `(signedEvenThetaGauge b (neutralEvenThetaParam b c),
shiftedGroundState a)` retained-variance certificate. -/
theorem joint_neutralThetaGauge_and_twoThreeFour_sliver_equivalence {c a : ℝ}
    (hc0 : 0 < c) (hc5 : 2 * c < Real.log 5) (ha : 0 < a) :
    (ZetaWindowPositive c ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
        |collarHankel 0 f -
            vonMangoldtAtom 2 * selfConv f (-Real.log 2) -
            vonMangoldtAtom 3 * selfConv f (-Real.log 3) -
            vonMangoldtAtom 4 * selfConv f (-Real.log 4)| ≤
          archForm f - 2 * vonMangoldtAtom 2 * autocorr f (Real.log 2) + realPoleForm f) ∧
    (ZetaWindowPositive c ↔
      ∃ b : ℝ, 0 < b ∧ 0 < neutralEvenThetaParam b c ∧
        (∀ α₀ : ℝ, 0 ≤ α₀ → ∀ x ∈ Icc (-(c + 1)) (c + 1), 0 < signedEvenThetaProfile b α₀ x) ∧
        (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
          2 * chargeVariance
            (fun x => signedEvenThetaProfile b (neutralEvenThetaParam b c) x * Real.cosh (x / 2))
            (Ioo (-c) c) u ≤
            signedJumpEnergy (signedEvenThetaProfile b (neutralEvenThetaParam b c)) u) ∧
        (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
          0 ≤ 2 * sameSideEnergy (shiftedGroundState a) u -
              reflectedDifferenceEnergy (shiftedGroundState a) u +
            8 * ((∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2)) *
                (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
              (∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2)) ^ 2) +
            8 * outsideCharge a c *
              ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2))) := by
  have hc3 : c < Real.log 3 := (by linarith : c < Real.log 5 / 2).trans half_log_five_lt_log_three
  refine ⟨?_, ?_⟩
  · rw [zetaWindowPositive_iff_abs_centreCoupling_le hc0]
    refine forall_congr' fun f => imp_congr_right fun hf => imp_congr_right fun h0 =>
      imp_congr_right fun hleft => ?_
    have hleft0 : ∀ u, u < 0 - c → f u = 0 := fun u hu => hleft u (by linarith)
    have hfc := hasCompactSupport_of_collarWindow h0 hleft0
    have hcc : centreCoupling f =
        collarHankel 0 f -
          vonMangoldtAtom 2 * selfConv f (-Real.log 2) -
          vonMangoldtAtom 3 * selfConv f (-Real.log 3) -
          vonMangoldtAtom 4 * selfConv f (-Real.log 4) := by
      have ho := orderedCoupling_collarReflect_eq_two_three_four_of_lt_half_log_five
        hc0.le hc5 hf h0 hleft0
      rw [orderedCoupling_collarReflect hf hfc h0] at ho
      simpa only [centreCoupling, mul_zero, zero_sub] using ho
    have hw : weilQuad f =
        archForm f - 2 * vonMangoldtAtom 2 * autocorr f (Real.log 2) + realPoleForm f := by
      rw [← fullZeroForm_eq_weilQuad_of_cont hf.continuous hfc,
        fullZeroForm_eq_arch_prime_pole hf hfc,
        (primeSum_eq_two_sliver_of_collarWindow_lt_log_three hc0.le hc3 h0 hleft0).1]
    rw [hcc, hw]
  · rw [zetaWindowPositive_iff_even_and_odd_sectors c,
      odd_nonneg_iff_retainedVariance_shiftedGroundState ha hc0]
    constructor
    · rintro ⟨hev, hod⟩
      obtain ⟨b, hb0, hα0, hbpos, _, _⟩ := exists_signedEvenThetaGauge_pos_and_nonneg_poleCharge hc0
      exact ⟨b, hb0, hα0, hbpos,
        (even_nonneg_iff_neutralSignedEvenThetaGauge hc0 hbpos).mp hev, hod⟩
    · rintro ⟨b, _, _, hbpos, hev, hod⟩
      exact ⟨(even_nonneg_iff_neutralSignedEvenThetaGauge hc0 hbpos).mpr hev, hod⟩

#print axioms neutralEvenTheta_signedJump_and_variance_eq
#print axioms neutralEvenTheta_poleNeutral_invariance
#print axioms odd_shiftedGroundState_variance_retention_necessary
#print axioms tendsto_neutralEvenThetaParam_div_two_cosh_atTop
#print axioms tendsto_signedEvenThetaProfile_neutral_div_two_cosh_atTop
#print axioms tendsto_neutralEvenTheta_signedJump_and_variance_atTop
#print axioms orderedCoupling_collarReflect_eq_two_three_four_of_lt_half_log_five
#print axioms primeSum_eq_two_sliver_of_collarWindow_lt_log_three
#print axioms twoThreeFour_collarKicks_le_levyEnergy
#print axioms weilQuad_sub_abs_orderedCoupling_ge_of_le_weilFloorApertureTower
#print axioms joint_neutralThetaGauge_and_twoThreeFour_sliver_equivalence

end GaloisForLFunctions.SignedWindowCriticality

end
