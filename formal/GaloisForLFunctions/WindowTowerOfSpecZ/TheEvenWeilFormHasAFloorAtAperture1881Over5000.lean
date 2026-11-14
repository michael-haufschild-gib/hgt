import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstThreeEvenMomentsArePaidAtAperture1881Over5000
import GaloisForLFunctions.WindowTowerOfSpecZ.SevenGammaModesBoundTheMassAtAperture1881Over5000
import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaComparisonRetainsTheMeanAndTheCorrelationMoments
import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderPaysForTheDisjointHalfWindows
import GaloisForLFunctions.WindowTowerOfSpecZ.TwoEvenMomentsRetainTheCoshPoleAtAperture1881Over5000
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.EvenCenteredPrimitiveMass
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.EvenCorrelationMoments
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicChargedGaps
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicBoundaryIdentity

/-!
# The even Weil floor at aperture `1881/5000`

The Gamma lag decomposition retains its mean, primitive and quadratic
correlation charges. The sixth regional gap and the first three even moment
capacities absorb these charges and the first prime reflection.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilMarkovPole _root_.RHTower.WeilLevyPoleGauss
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory SpacingScaleHarmonicAnalysis SelectivePositivityAndThresholdLaws
open ArithmeticIncidencePositivity ArithmeticCriticalityTheory BiScaleUncertainty ArithmeticPositivityTheory

private abbrev aperture : ℝ := 1881 / 5000

private theorem dilated_outside {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-aperture) aperture) {x : ℝ}
    (hx : x ∉ Icc (-1 : ℝ) 1) : F (aperture * x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  have hi := hs ht
  apply hx
  dsimp [aperture] at hi
  exact ⟨by linarith only [hi.1], by linarith only [hi.2]⟩

private theorem dilated_support {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-aperture) aperture) :
    tsupport (fun x => F (aperture * x)) ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  exact hx (dilated_outside hs hn)

private theorem even_integral_unit {H : ℝ → ℝ} (hH : Continuous H)
    (he : ∀ x, H (-x) = H x) :
    (∫ x in Icc (-1 : ℝ) 1, H x) = 2 * ∫ x in (0 : ℝ)..1, H x := by
  have hn := intervalIntegral.integral_comp_neg (f := H) (a := (0 : ℝ)) (b := 1)
  simp only [he, neg_zero] at hn
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hH.intervalIntegrable (-1) 0) (hH.intervalIntegrable 0 1)
  rw [← hn, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  linarith only [h]

private theorem dilated_mass {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-aperture) aperture) (heven : ∀ x, F (-x) = F x) :
    (∫ x, F x ^ 2) = 2 * aperture * ∫ u in (0 : ℝ)..1, F (aperture * u) ^ 2 := by
  have hc : Continuous (fun u => F (aperture * u)) :=
    hF.comp (continuous_const.mul continuous_id)
  have hcut : (∫ u in Icc (-1 : ℝ) 1, F (aperture * u) ^ 2) =
      ∫ u, F (aperture * u) ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      rw [dilated_outside hs hu, zero_pow two_ne_zero])
  have he := even_integral_unit (H := fun u => F (aperture * u) ^ 2)
    (hc.pow 2) (fun u => by rw [mul_neg, heven])
  have hscale := Measure.integral_comp_mul_left (fun x => F x ^ 2) aperture
  norm_num [aperture, smul_eq_mul] at hscale
  rw [hcut, hscale] at he
  dsimp [aperture]
  linarith only [he]

private theorem dilated_autocorr (F : ℝ → ℝ) (t : ℝ) :
    autocorr (fun x => F (aperture * x)) t = aperture⁻¹ * autocorr F (aperture * t) := by
  unfold autocorr
  have h := Measure.integral_comp_mul_left (fun x => F x * F (x + aperture * t)) aperture
  rw [abs_of_pos (by norm_num [aperture] : 0 < aperture⁻¹), smul_eq_mul] at h
  simpa only [mul_add] using h

private theorem dilated_lag (F : ℝ → ℝ) :
    (∫ t in Ioc (0 : ℝ) 2,
      (autocorr (fun x => F (aperture * x)) 0 - autocorr (fun x => F (aperture * x)) t) / t) =
      aperture⁻¹ * ∫ t in Ioc (0 : ℝ) (2 * aperture), (autocorr F 0 - autocorr F t) / t := by
  have he (t : ℝ) :
      (autocorr (fun x => F (aperture * x)) 0 - autocorr (fun x => F (aperture * x)) t) / t =
        (autocorr F 0 - autocorr F (aperture * t)) / (aperture * t) := by
    rw [dilated_autocorr F 0, dilated_autocorr F t, mul_zero]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc (fun t _ => he t),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  have h := intervalIntegral.integral_comp_mul_left
    (fun t => (autocorr F 0 - autocorr F t) / t) (a := 0) (b := 2)
    (by norm_num [aperture] : aperture ≠ 0)
  rw [smul_eq_mul, mul_zero, mul_comm aperture 2,
    intervalIntegral.integral_of_le (by norm_num [aperture] : (0 : ℝ) ≤ 2 * aperture)] at h
  exact h

private theorem even_supported_half_integral {G W : ℝ → ℝ} (hG : Continuous G)
    (hW : Continuous W) (hs : tsupport G ⊆ Icc (-1 : ℝ) 1)
    (he : ∀ x, G (-x) = G x) (hWe : ∀ x, W (-x) = W x) :
    (∫ x, W x * G x) = 2 * ∫ x in (0 : ℝ)..1, W x * G x := by
  have hcut : (∫ x in Icc (-1 : ℝ) 1, W x * G x) = ∫ x, W x * G x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero]
  have h := even_integral_unit (H := fun x => W x * G x) (hW.mul hG)
    (fun x => by rw [hWe, he])
  rw [hcut] at h
  exact h

private theorem weighted_dilation (F W : ℝ → ℝ) :
    (∫ x, W x * F x) = aperture * ∫ u, W (aperture * u) * F (aperture * u) := by
  have h := Measure.integral_comp_mul_left (fun x => W x * F x) aperture
  norm_num [aperture, smul_eq_mul] at h ⊢
  linarith only [h]

private theorem dilated_correlation_moment (F : ℝ → ℝ) (n : ℕ) :
    (∫ t in Ioc (0 : ℝ) (2 * aperture), t ^ n * autocorr F t) =
      aperture ^ (n + 2) * ∫ t in Ioc (0 : ℝ) 2,
        t ^ n * autocorr (fun x => F (aperture * x)) t := by
  have hc (t : ℝ) : autocorr F (aperture * t) =
      aperture * autocorr (fun x => F (aperture * x)) t := by
    rw [dilated_autocorr]
    norm_num [aperture]
    ring
  have he (t : ℝ) : (aperture * t) ^ n * autocorr F (aperture * t) =
      aperture ^ (n + 1) * (t ^ n * autocorr (fun x => F (aperture * x)) t) := by
    rw [hc, mul_pow, pow_succ]
    ring
  have h := intervalIntegral.mul_integral_comp_add_mul
    (f := fun t => t ^ n * autocorr F t) (a := (0 : ℝ)) (b := 2) (c := aperture) (d := 0)
  simp only [zero_add, mul_zero] at h
  simp_rw [he] at h
  rw [intervalIntegral.integral_const_mul, ← mul_assoc,
    show aperture * aperture ^ (n + 1) = aperture ^ (n + 2) by simp only [pow_add, pow_one, pow_two]; ring,
    show aperture * 2 = 2 * aperture by ring,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
    intervalIntegral.integral_of_le (by norm_num [aperture] : (0 : ℝ) ≤ 2 * aperture)] at h
  exact h.symm

private theorem legP_two_eq (x : ℝ) : legP 2 x = (3 * x ^ 2 - 1) / 2 := by
  norm_num [legP]
  ring

private theorem legP_four_eq (x : ℝ) : legP 4 x = (35 * x ^ 4 - 30 * x ^ 2 + 3) / 8 := by
  norm_num [legP]
  ring

private theorem even_regional_moment {G : ℝ → ℝ} (hG : Continuous G)
    (he : ∀ x, G (-x) = G x) (n : ℕ) :
    regionalLegendreMoment G (2 * n) = 2 * ∫ x in (0 : ℝ)..1, G x * legP (2 * n) x := by
  apply even_integral_unit (H := fun x => G x * legP (2 * n) x)
    (hG.mul (continuous_legP (2 * n)))
  intro x
  rw [he, legP_neg, pow_mul]
  norm_num

private theorem even_primitive_mass_fold {G : ℝ → ℝ} (hG : Continuous G)
    (he : ∀ x, G (-x) = G x) :
    (∫ x in (-1 : ℝ)..1, (∫ y in (0 : ℝ)..x, G y) ^ 2) =
      2 * ∫ x in (0 : ℝ)..1, (∫ y in (0 : ℝ)..x, G y) ^ 2 := by
  let H := fun x => ∫ y in (0 : ℝ)..x, G y
  have hD (x : ℝ) : HasDerivAt H (G x) x := (hG.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  have hHo (x : ℝ) : H (-x) = -H x := by
    have h := intervalIntegral.integral_comp_neg (f := G) (a := (0 : ℝ)) (b := x)
    simp only [he, neg_zero] at h
    dsimp [H]
    rw [intervalIntegral.integral_symm, ← h]
  have h := even_integral_unit (H := fun x => H x ^ 2) (hH.pow 2)
    (fun x => by rw [hHo, neg_sq])
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  exact h

private theorem even_second_position {G : ℝ → ℝ} (hG : Continuous G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) (he : ∀ x, G (-x) = G x) :
    (∫ x, x ^ 2 * G x) = (2 / 3) *
      ((∫ x in (0 : ℝ)..1, G x) + 2 * (∫ x in (0 : ℝ)..1, G x * ((3 * x ^ 2 - 1) / 2))) := by
  have h := even_supported_half_integral hG (continuous_pow 2) hs he (fun x => neg_sq x)
  have hi2 : IntervalIntegrable (fun x => x ^ 2 * G x) volume 0 1 :=
    ((continuous_pow 2).mul hG).intervalIntegrable 0 1
  have hm : (∫ x in (0 : ℝ)..1, G x * ((3 * x ^ 2 - 1) / 2)) =
      (3 * (∫ x in (0 : ℝ)..1, x ^ 2 * G x) - (∫ x in (0 : ℝ)..1, G x)) / 2 := by
    have heq : (fun x => G x * ((3 * x ^ 2 - 1) / 2)) =
        fun x => (3 * (x ^ 2 * G x) - G x) / 2 := by funext x; ring
    rw [heq, intervalIntegral.integral_div, intervalIntegral.integral_sub (μ := volume)
      (f := fun x => 3 * (x ^ 2 * G x)) (g := G) (hi2.const_mul 3) (hG.intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul]
  linarith only [h, hm]

private theorem dilated_mean {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-aperture) aperture) (he : ∀ x, F (-x) = F x) :
    (∫ x, F x) = 2 * aperture * ∫ u in (0 : ℝ)..1, F (aperture * u) := by
  let G := fun u => F (aperture * u)
  have hGc : Continuous G := hF.comp (continuous_const.mul continuous_id)
  have hGe (u : ℝ) : G (-u) = G u := by dsimp [G]; rw [mul_neg, he]
  have h := even_supported_half_integral (G := G) (W := fun _ => (1 : ℝ)) hGc
    continuous_const (dilated_support hs) hGe (fun _ => rfl)
  have hscale := weighted_dilation F (fun _ => (1 : ℝ))
  simp only [one_mul] at h hscale
  change (∫ x, F x) = 2 * aperture * ∫ u in (0 : ℝ)..1, G u
  change (∫ x, F x) = aperture * ∫ u, G u at hscale
  rw [hscale, h]
  ring

private theorem dilated_cosh_pairing {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-aperture) aperture) (he : ∀ x, F (-x) = F x) :
    coshPairing F = 4 * aperture *
      ∫ u in (0 : ℝ)..1, F (aperture * u) * Real.cosh (aperture * u / 2) := by
  let G := fun u => F (aperture * u)
  have hGc : Continuous G := hF.comp (continuous_const.mul continuous_id)
  have hGe (u : ℝ) : G (-u) = G u := by dsimp [G]; rw [mul_neg, he]
  have h := even_supported_half_integral (G := G) (W := fun u => Real.cosh (aperture * u / 2))
    hGc (by fun_prop) (dilated_support hs) hGe (fun u => by rw [mul_neg, neg_div, Real.cosh_neg])
  have hscale := weighted_dilation F (fun x => Real.cosh (x / 2))
  have hpair : coshPairing F = 2 * ∫ x, Real.cosh (x / 2) * F x := by
    unfold coshPairing
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hpair, hscale]
  change 2 * (aperture * ∫ u, Real.cosh (aperture * u / 2) * G u) = _
  rw [h]
  calc
    _ = 4 * aperture * ∫ u in (0 : ℝ)..1, Real.cosh (aperture * u / 2) * G u := by ring
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only [G]
      ring

private theorem dilated_prime_correlation {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-aperture) aperture) (he : ∀ x, F (-x) = F x) :
    autocorr F (Real.log 2) = aperture *
      ∫ u in (Real.log 2 / aperture - 1)..1,
        F (aperture * u) * F (aperture * (Real.log 2 / aperture - u)) := by
  let G := fun u => F (aperture * u)
  let d := Real.log 2 / aperture
  have hGe (x : ℝ) : G (-x) = G x := by dsimp [G]; rw [mul_neg, he]
  have hcut : (∫ u in Icc (d - 1) 1, G u * G (d - u)) = ∫ u, G u * G (d - u) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    by_cases hright : 1 < u
    · have hz : G u = 0 := dilated_outside hs (fun h => not_lt_of_ge h.2 hright)
      rw [hz, zero_mul]
    · have hleft : u < d - 1 := lt_of_not_ge (fun h => hu ⟨h, le_of_not_gt hright⟩)
      have hz : G (d - u) = 0 := dilated_outside hs (fun h => by linarith only [h.2, hleft])
      rw [hz, mul_zero]
  have hn := integral_neg_eq_self (fun u => G u * G (u + d)) volume
  have hfun : (fun u => G (-u) * G (-u + d)) = fun u => G u * G (d - u) := by
    funext u
    rw [hGe, show -u + d = d - u by ring]
  rw [hfun, ← hcut] at hn
  change (∫ u in Icc (d - 1) 1, G u * G (d - u)) = autocorr G d at hn
  have hscale := dilated_autocorr F d
  change autocorr G d = aperture⁻¹ * autocorr F (aperture * d) at hscale
  rw [show aperture * d = Real.log 2 by dsimp [d, aperture]; ring] at hscale
  rw [hscale] at hn
  have hb : Real.log 2 / aperture - 1 ≤ 1 := by
    dsimp [aperture]
    linarith only [Real.log_two_lt_d9]
  rw [intervalIntegral.integral_of_le hb, ← integral_Icc_eq_integral_Ioc]
  change autocorr F (Real.log 2) = aperture * ∫ u in Icc (d - 1) 1, G u * G (d - u)
  dsimp [aperture] at hn ⊢
  linarith only [hn]

private theorem even_weil_decomposition {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-aperture) aperture) (he : ∀ x, F (-x) = F x) :
    weilQuad F = EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F -
      2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2) + coshPairing F ^ 2 / 2 := by
  have hcs : HasCompactSupport F :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hs
  have hN : ∀ n : ℕ, 2 < n → ∀ u, F u * F (u + Real.log n) = 0 := by
    intro n hn u
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
    have hlog : 2 * aperture < Real.log n :=
      lt_of_lt_of_le (by dsimp [aperture]; linarith only [Real.log_three_gt_d9])
        (Real.log_le_log (by norm_num) hn3)
    by_cases hu : F u = 0
    · rw [hu, zero_mul]
    · have huI : u ∈ Icc (-aperture) aperture := by
        by_contra hnot
        exact hu (image_eq_zero_of_notMem_tsupport fun h => hnot (hs h))
      have hz : F (u + Real.log n) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
        have hbound := (hs h).2
        linarith only [huI.1, hlog, hbound]
      rw [hz, mul_zero]
  have hW := weil_eq_markovForm_add_pole hF hcs hN
  change weilQuad F = markovForm 2 F + coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2 at hW
  have hM1 : markovForm 1 F = EF.gammaBracket 0 * (∫ x, F x ^ 2) + levyJump F := by
    norm_num [markovForm, creationPotential, primeJump]
  have hM2 : markovForm 2 F = EF.gammaBracket 0 * (∫ x, F x ^ 2) + levyJump F -
      2 * primeJumpWeight 2 * autocorr F (Real.log 2) := by
    have h := markovForm_succ hF.continuous hcs (N := 1) le_rfl
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at h
    unfold autocorr
    linarith only [h, hM1]
  have hw : primeJumpWeight 2 = Real.log 2 / Real.sqrt 2 := by
    unfold primeJumpWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
  rw [hM2, levyJump_eq_biScale hF hcs, hw, sinhPairing_eq_zero_of_even he] at hW
  simpa only [zero_pow two_ne_zero, zero_div, sub_zero] using hW

private theorem even_potential_integral_bound {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) (he : ∀ x, G (-x) = G x) :
    (∫ u in (0 : ℝ)..1, firstOverlapEvenPotential u * G u ^ 2) ≤
      (3029 / 3000 - Real.log 2) * (∫ u in (0 : ℝ)..1, G u ^ 2) +
      ∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2) := by
  have hExt := (even_logarithmic_lag_and_exterior hG hs he).1
  have hiM : IntegrableOn (fun u => G u ^ 2) (Ioo (0 : ℝ) 1) :=
    (hG.continuous.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hP : Continuous firstOverlapEvenPotential := by unfold firstOverlapEvenPotential; fun_prop
  have hiP : IntegrableOn (fun u => firstOverlapEvenPotential u * G u ^ 2) (Ioo (0 : ℝ) 1) :=
    (hP.mul (hG.continuous.pow 2)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  let c := 3029 / 3000 - Real.log 2
  have hiR : IntegrableOn (fun u => c * G u ^ 2 +
      G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2)) (Ioo (0 : ℝ) 1) :=
    (hiM.const_mul c).add hExt
  have hcomp : (∫ u in Ioo (0 : ℝ) 1, firstOverlapEvenPotential u * G u ^ 2) ≤
      ∫ u in Ioo (0 : ℝ) 1, c * G u ^ 2 + G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2) := by
    apply setIntegral_mono_on hiP hiR measurableSet_Ioo
    intro u hu
    have hp := mul_le_mul_of_nonneg_right (firstOverlapEvenPotential_le_log hu.1.le hu.2) (sq_nonneg (G u))
    dsimp only [c]
    nlinarith only [hp]
  rw [integral_add (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (f := fun u => c * G u ^ 2) (g := fun u => G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2))
    (hiM.const_mul c) hExt, integral_const_mul] at hcomp
  simpa only [c, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] using hcomp


/-- Even tests at aperture `1881/5000` have a uniform positive Weil floor. -/
theorem weilQuad_ge_even_at_aperture_1881_over_5000 {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1881 / 5000 : ℝ)) (1881 / 5000))
    (he : ∀ x, F (-x) = F x) : (1 / 50000 : ℝ) * (∫ x, F x ^ 2) ≤ weilQuad F := by
  let G := fun u => F (aperture * u)
  let M := ∫ u in (0 : ℝ)..1, G u ^ 2
  let m0 := ∫ u in (0 : ℝ)..1, G u
  let m2 := ∫ u in (0 : ℝ)..1, G u * ((3 * u ^ 2 - 1) / 2)
  let m4 := ∫ u in (0 : ℝ)..1, G u * ((35 * u ^ 4 - 30 * u ^ 2 + 3) / 8)
  let H := ∫ u in (0 : ℝ)..1, (∫ v in (0 : ℝ)..u, G v) ^ 2
  let C := ∫ u in (Real.log 2 / aperture - 1)..1, G u * G (Real.log 2 / aperture - u)
  let P := ∫ u in (0 : ℝ)..1, G u * Real.cosh (aperture * u / 2)
  let U := ∫ u in (0 : ℝ)..1, firstOverlapEvenPotential u * G u ^ 2
  let X := ∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2)
  let L := ∫ t in Ioc (0 : ℝ) (2 * aperture), (autocorr F 0 - autocorr F t) / t
  let R := ∫ t in Ioc (0 : ℝ) (2 * aperture), retainedGammaRemainderWeight t *
    (autocorr F 0 - autocorr F t)
  let c := EF.gammaBracket 0 + (2 * aperture) / 2 - (2 * aperture) ^ 2 / 48 -
    (2 * aperture) ^ 3 / 48 + 2 * archLevyAntideriv (2 * aperture)
  have hG : ContDiff ℝ 2 G := hF.comp (contDiff_const.mul contDiff_id)
  have hGs : tsupport G ⊆ Icc (-1 : ℝ) 1 := dilated_support hs
  have hGe (u : ℝ) : G (-u) = G u := by dsimp [G]; rw [mul_neg, he]
  have hcs : HasCompactSupport F :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hs
  have hMass : (∫ x, F x ^ 2) = 2 * aperture * M := dilated_mass hF.continuous hs he
  have hMean : (∫ x, F x) = 2 * aperture * m0 := dilated_mean hF.continuous hs he
  have hMeanG : (∫ x, G x) = 2 * m0 := by
    simpa only [one_mul] using even_supported_half_integral hG.continuous
      (G := G) (W := fun _ => (1 : ℝ)) continuous_const hGs hGe (fun _ => rfl)
  have hPosition : (∫ x, x ^ 2 * G x) = (2 / 3) * (m0 + 2 * m2) :=
    even_second_position hG.continuous hGs hGe
  have hC1G := even_autocorr_first_moment hG.continuous (a := 1) (by norm_num) hGs hGe
  rw [hMeanG, even_primitive_mass_fold hG.continuous hGe] at hC1G
  change (∫ t in Ioc (0 : ℝ) (2 * 1), t * autocorr G t) = 1 * (2 * m0) ^ 2 / 2 - 2 * H at hC1G
  norm_num only [mul_one, one_mul] at hC1G
  have hC2G := even_autocorr_second_moment hG.continuous hGs hGe
  rw [hMeanG, hPosition] at hC2G
  norm_num only [mul_one] at hC2G
  have hC1 : (∫ t in Ioc (0 : ℝ) (2 * aperture), t * autocorr F t) =
      aperture ^ 3 * (2 * m0 ^ 2 - 2 * H) := by
    have h := dilated_correlation_moment F 1
    simp only [pow_one] at h
    change (∫ t in Ioc (0 : ℝ) (2 * aperture), t * autocorr F t) =
      aperture ^ (1 + 2) * ∫ t in Ioc (0 : ℝ) 2, t * autocorr G t at h
    rw [hC1G] at h
    rw [h]
    ring
  have hC2 : (∫ t in Ioc (0 : ℝ) (2 * aperture), t ^ 2 * autocorr F t) =
      aperture ^ 4 * ((4 / 3) * m0 * (m0 + 2 * m2)) := by
    have h := dilated_correlation_moment F 2
    change (∫ t in Ioc (0 : ℝ) (2 * aperture), t ^ 2 * autocorr F t) =
      aperture ^ (2 + 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 2 * autocorr G t at h
    rw [hC2G] at h
    rw [h]
    ring
  have hPrime : autocorr F (Real.log 2) = aperture * C := dilated_prime_correlation hs he
  have hPole : coshPairing F = 4 * aperture * P := dilated_cosh_pairing hF.continuous hs he
  have hGamma := gamma_eq_logarithmic_lag_correlation_moments_and_remainder hF hcs
    (r := 2 * aperture) (by norm_num [aperture]) (by norm_num [aperture])
    (by convert hs using 1 <;> norm_num [aperture])
  change L + c * (∫ x, F x ^ 2) - (∫ x, F x) ^ 2 / 4 +
    (∫ t in Ioc (0 : ℝ) (2 * aperture), t * autocorr F t) / 24 +
    (∫ t in Ioc (0 : ℝ) (2 * aperture), t ^ 2 * autocorr F t) / 16 + R = _ at hGamma
  rw [hMass, hMean, hC1, hC2] at hGamma
  have hWeil := even_weil_decomposition hF hs he
  rw [hMass, ← hGamma, hPrime, hPole] at hWeil
  have hNormalized : weilQuad F / (2 * aperture) = L / (2 * aperture) + c * M -
      aperture * m0 ^ 2 / 2 + aperture ^ 2 / 24 * (m0 ^ 2 - H) +
      aperture ^ 3 / 24 * m0 ^ 2 + aperture ^ 3 / 12 * m0 * m2 +
      R / (2 * aperture) - (Real.log 2 / Real.sqrt 2) * C + 4 * aperture * P ^ 2 := by
    rw [hWeil]
    dsimp only [aperture]
    ring
  have hLag := (even_logarithmic_lag_and_exterior hG hGs hGe).2
  have hScale := dilated_lag F
  change (∫ t in Ioc (0 : ℝ) 2, (autocorr G 0 - autocorr G t) / t) = aperture⁻¹ * L at hScale
  rw [hScale] at hLag
  have hBoundary : L / (2 * aperture) = regionalLogEnergy G / 4 + X := by
    change aperture⁻¹ * L / 2 = regionalLogEnergy G / 4 + X at hLag
    calc
      _ = aperture⁻¹ * L / 2 := by dsimp only [aperture]; ring
      _ = _ := hLag
  rw [hBoundary] at hNormalized
  have hM : (∫ x in Icc (-1 : ℝ) 1, G x ^ 2) = 2 * M :=
    even_integral_unit (hG.continuous.pow 2) (fun x => by rw [hGe])
  have hm0 : regionalLegendreMoment G 0 = 2 * m0 := by
    simpa only [Nat.mul_zero, legP_zero, mul_one] using even_regional_moment hG.continuous hGe 0
  have hm2 : regionalLegendreMoment G 2 = 2 * m2 := by
    simpa only [Nat.mul_one, legP_two_eq] using even_regional_moment hG.continuous hGe 1
  have hm4 : regionalLegendreMoment G 4 = 2 * m4 := by
    simpa only [show (2 : ℕ) * 2 = 4 by norm_num, legP_four_eq] using even_regional_moment hG.continuous hGe 2
  have hGap := regionalLogEnergy_ge_sixth_gap_sub_low_even_moments (hG.of_le (by norm_num)) hGe
  have hBessel := regionalMass_ge_three_even_moments hG.continuous hGe
  rw [hM, hm0, hm2, hm4] at hGap hBessel
  have hPrimitive := primitive_mass_le_rational_variance_and_two_moments hG.continuous
  change H ≤ (5 / 49) * M + (1 / 3 - 5 / 49) * m0 ^ 2 - (2 / 3) * m0 * m2 at hPrimitive
  have hCosh := even_cosh_pole_ge_two_moments hG.continuous
  change 4 * aperture * ((1 + aperture ^ 2 / 24 + aperture ^ 4 / 1920) * m0 +
    (aperture ^ 2 / 12 + aperture ^ 4 / 672) * m2) ^ 2 - (1 / 50000) * M ≤
    4 * aperture * P ^ 2 at hCosh
  have hPotential := even_potential_integral_bound hG hGs hGe
  change U ≤ (3029 / 3000 - Real.log 2) * M + X at hPotential
  have hRem := local_gamma_remainder_ge_at_aperture_1881_over_5000 hF hcs hs
  have hRadius : (1881 / 2500 : ℝ) = 2 * aperture := by norm_num [aperture]
  rw [hRadius, hMass] at hRem
  change (1 / 6250 : ℝ) * (2 * aperture * M) ≤ R at hRem
  have hNonneg : 0 ≤ M := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg (G x))
  have hGammaMass := mul_le_mul_of_nonneg_right gamma_mass_constant_at_aperture_1881_over_5000 hNonneg
  rw [hRadius] at hGammaMass
  have hc : EF.gammaBracket 0 + Real.log 2 + (2 * aperture) / 2 -
      (2 * aperture) ^ 2 / 48 - (2 * aperture) ^ 3 / 48 +
      2 * archLevyAntideriv (2 * aperture) = c + Real.log 2 := by dsimp only [c]; ring
  rw [hc] at hGammaMass
  have hCapacity := firstOverlapEvenCharge_le_energy hG.continuous
  change firstOverlapEvenCharge m0 m2 m4 ≤ U - (Real.log 2 / Real.sqrt 2) * C +
    (1 / 1000000) * M at hCapacity
  unfold firstOverlapEvenCharge at hCapacity
  rw [hMass]
  norm_num [aperture] at hNormalized hCosh hRem hCapacity ⊢
  nlinarith only [hNormalized, hGap, hBessel, hPrimitive, hCosh, hPotential,
    hRem, hGammaMass, hCapacity, hNonneg]

#print axioms weilQuad_ge_even_at_aperture_1881_over_5000

end GaloisForLFunctions.WindowTowerOfSpecZ
