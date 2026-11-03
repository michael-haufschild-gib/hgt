import GaloisForLFunctions.WindowTowerOfSpecZ.ThePrimitiveVarianceRetainsTheOddMoment
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicExteriorIdentity
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicLowOddMoments

/-!
# The explicit two-moment lower form at the first fold

The primitive variance, sinh remainder and exterior logarithmic potential
give a concrete lower form with the signed prime reflection retained. The
only spectral charges removed from the regional energy are its first and
third Legendre moments. The lower form's sign remains a separate inequality.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory SpacingScaleHarmonicAnalysis SelectivePositivityAndThresholdLaws

/-- The mass cost after retaining primitive mean and bounding the sinh remainder. -/
def firstFoldMomentMassCost : ℝ :=
  Real.eulerMascheroniConstant + Real.log Real.pi + 1 / 192 +
    1 / (96 * Real.pi ^ 2) + 97 / 483840

/-- The explicit first-fold lower form; `legP 3 u = (5u³−3u)/2`. -/
def firstFoldTwoMomentForm (G : ℝ → ℝ) : ℝ :=
  (∫ u in Ioo (0 : ℝ) 1,
    (137 / 60 - firstFoldMomentMassCost - Real.log (1 - u ^ 2) / 2) * G u ^ 2) +
  (Real.log 2 / Real.sqrt 2) *
    (∫ u in Icc (2 * Real.log 2 - 1) 1, G u * G (2 * Real.log 2 - u)) -
  (77 / 20 + 39 / 256) * (∫ u in Ioo (0 : ℝ) 1, u * G u) ^ 2 -
  (63 / 20 : ℝ) * (∫ u in Ioo (0 : ℝ) 1, G u * legP 3 u) ^ 2

private theorem even_integral_unit {H : ℝ → ℝ} (hH : Continuous H)
    (he : ∀ x, H (-x) = H x) :
    (∫ x in Icc (-1 : ℝ) 1, H x) = 2 * ∫ x in Ioo (0 : ℝ) 1, H x := by
  have hn := intervalIntegral.integral_comp_neg (f := H) (a := (0 : ℝ)) (b := 1)
  simp only [he, neg_zero] at hn
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hH.intervalIntegrable (-1) 0) (hH.intervalIntegrable 0 1)
  have hwhole : (∫ x in Icc (-1 : ℝ) 1, H x) = ∫ x in Ioc (-1 : ℝ) 1, H x :=
    integral_Icc_eq_integral_Ioc
  rw [← hn] at h
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), ← hwhole] at h
  simp only [integral_Ioc_eq_integral_Ioo] at h
  linarith only [h]

private theorem dilation_outside {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) {x : ℝ}
    (hx : x ∉ Icc (-1 : ℝ) 1) : F ((1 / 2) * x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  have hi := hs ht
  exact hx ⟨by linarith only [hi.1], by linarith only [hi.2]⟩

private theorem dilation_odd {F : ℝ → ℝ} (ho : ∀ x, F (-x) = -F x) (x : ℝ) :
    F ((1 / 2) * (-x)) = -F ((1 / 2) * x) := by rw [mul_neg, ho]

private theorem dilation_half_mass {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ u in Ioo (0 : ℝ) 1, F ((1 / 2) * u) ^ 2) = ∫ x, F x ^ 2 := by
  have hc : Continuous (fun u => F ((1 / 2 : ℝ) * u)) :=
    hF.comp (continuous_const.mul continuous_id)
  have hcut : (∫ u in Icc (-1 : ℝ) 1, F ((1 / 2) * u) ^ 2) =
      ∫ u, F ((1 / 2) * u) ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      rw [dilation_outside hs hu, zero_pow two_ne_zero])
  have he := even_integral_unit (H := fun u => F ((1 / 2) * u) ^ 2) (hc.pow 2)
    (fun x => by rw [dilation_odd ho, neg_sq])
  have hscale := Measure.integral_comp_mul_left (fun x => F x ^ 2) (1 / 2 : ℝ)
  norm_num [smul_eq_mul] at hscale
  rw [hcut, hscale] at he
  linarith only [he]

private theorem dilation_half_position {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ x, x * F x) = (∫ u in Ioo (0 : ℝ) 1, u * F ((1 / 2) * u)) / 2 := by
  have hc : Continuous (fun u => F ((1 / 2 : ℝ) * u)) :=
    hF.comp (continuous_const.mul continuous_id)
  have hcut : (∫ u in Icc (-1 : ℝ) 1, u * F ((1 / 2) * u)) =
      ∫ u, u * F ((1 / 2) * u) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      rw [dilation_outside hs hu, mul_zero])
  have he := even_integral_unit (H := fun u => u * F ((1 / 2) * u)) (continuous_id.mul hc)
    (fun x => by rw [dilation_odd ho, neg_mul_neg])
  have hscale := Measure.integral_comp_mul_left (fun x => x * F x) (1 / 2 : ℝ)
  norm_num [smul_eq_mul] at hscale
  have hfun : (fun x : ℝ => ((1 / 2) * x) * F ((1 / 2) * x)) =
      fun x => (1 / 2 : ℝ) * (x * F ((1 / 2) * x)) := by funext x; ring
  rw [hfun, integral_const_mul] at hscale
  rw [hcut] at he
  linarith only [he, hscale]

private theorem odd_legendre_half {G : ℝ → ℝ} (hG : Continuous G)
    (ho : ∀ x, G (-x) = -G x) {n : ℕ} (hn : (-1 : ℝ) ^ n = -1) :
    regionalLegendreMoment G n = 2 * ∫ u in Ioo (0 : ℝ) 1, G u * legP n u := by
  apply even_integral_unit (H := fun u => G u * legP n u) (hG.mul (continuous_legP n))
  intro x
  rw [ho, legP_neg, hn, neg_one_mul, neg_mul_neg]

private theorem dilation_autocorr (F : ℝ → ℝ) (t : ℝ) :
    autocorr (fun x => F ((1 / 2) * x)) t = 2 * autocorr F ((1 / 2) * t) := by
  unfold autocorr
  have h := Measure.integral_comp_mul_left (fun x => F x * F (x + (1 / 2) * t)) (1 / 2 : ℝ)
  norm_num [smul_eq_mul] at h
  simpa only [mul_add] using h

private theorem dilation_prime_reflection {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    -2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2) =
      (Real.log 2 / Real.sqrt 2) *
        ∫ u in Icc (2 * Real.log 2 - 1) 1,
          F ((1 / 2) * u) * F ((1 / 2) * (2 * Real.log 2 - u)) := by
  let G : ℝ → ℝ := fun u => F ((1 / 2) * u)
  let d : ℝ := 2 * Real.log 2
  have hGo : ∀ x, G (-x) = -G x := dilation_odd ho
  have hcut : (∫ u in Icc (d - 1) 1, G u * G (d - u)) = ∫ u, G u * G (d - u) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    by_cases hright : 1 < u
    · have hz : G u = 0 := dilation_outside hs (fun h => not_lt_of_ge h.2 hright)
      rw [hz, zero_mul]
    · have hleft : u < d - 1 := lt_of_not_ge (fun h => hu ⟨h, le_of_not_gt hright⟩)
      have hz : G (d - u) = 0 := dilation_outside hs (fun h => by linarith only [h.2, hleft])
      rw [hz, mul_zero]
  have hn := integral_neg_eq_self (fun u => G u * G (u + d)) volume
  have hfun : (fun u => G (-u) * G (-u + d)) = fun u => -(G u * G (d - u)) := by
    funext u
    rw [hGo, show -u + d = d - u by ring]
    ring
  rw [hfun, integral_neg, ← hcut] at hn
  change -(∫ u in Icc (d - 1) 1, G u * G (d - u)) = autocorr G d at hn
  have hscale := dilation_autocorr F d
  change autocorr G d = 2 * autocorr F ((1 / 2) * d) at hscale
  rw [show (1 / 2 : ℝ) * d = Real.log 2 by dsimp [d]; ring] at hscale
  rw [hscale] at hn
  have hw := congrArg (fun z : ℝ => (Real.log 2 / Real.sqrt 2) * z) hn
  dsimp [G, d] at hw
  linarith only [hw]

private theorem retained_first_moment_lower {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, ((∫ x, F x ^ 2) - autocorr F t) / t) -
      (firstFoldMomentMassCost + Real.log 2) * (∫ x, F x ^ 2) -
      (39 / 64 : ℝ) * (∫ x, x * F x) ^ 2 -
      2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2) ≤
        retainedOddGammaLowerForm F + (∫ x, F x ^ 2) / 64 := by
  have hv := unit_odd_primitive_variance_le hF hs ho
  have hp := unit_sinhPairing_square_le_position hF hs
  have hM := unit_odd_jump_first_moment hF hs ho
  simp only [autocorr_zero_eq] at hM
  have he : (∫ x, F x ^ 2) / (4 * Real.pi ^ 2) / 24 =
      (1 / (96 * Real.pi ^ 2)) * (∫ x, F x ^ 2) := by ring
  unfold retainedOddGammaLowerForm firstFoldMomentMassCost
  rw [hM]
  linarith only [hv, hp, he]

/-- The reserved Gamma lower form retains exactly two low moments and the signed reflection. -/
theorem retainedOddGamma_add_reserve_ge_firstFoldTwoMomentForm {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    firstFoldTwoMomentForm (fun u => F ((1 / 2) * u)) ≤
      retainedOddGammaLowerForm F + (∫ x, F x ^ 2) / 64 := by
  let G : ℝ → ℝ := fun u => F ((1 / 2) * u)
  have hG : ContDiff ℝ 1 G := (hF.of_le (by norm_num)).comp (contDiff_const.mul contDiff_id)
  have hGo : ∀ x, G (-x) = -G x := dilation_odd ho
  obtain ⟨hExt, hLag⟩ := unit_odd_logarithmic_lag_and_exterior hF hs ho
  change IntegrableOn (fun u => G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2))
    (Ioo (0 : ℝ) 1) at hExt
  have hMass := dilation_half_mass hF.continuous hs ho
  change (∫ u in Ioo (0 : ℝ) 1, G u ^ 2) = ∫ x, F x ^ 2 at hMass
  have hFull := even_integral_unit (H := fun u => G u ^ 2)
    (hG.continuous.pow 2) (fun u => by rw [hGo, neg_sq])
  have hM1 : regionalLegendreMoment G 1 = 2 * ∫ u in Ioo (0 : ℝ) 1, u * G u := by
    simpa only [legP_one, mul_comm] using
      odd_legendre_half hG.continuous hGo (n := 1) (by norm_num)
  have hM3 := odd_legendre_half hG.continuous hGo (n := 3) (by norm_num)
  have hPos := dilation_half_position hF.continuous hs ho
  change (∫ x, x * F x) = (∫ u in Ioo (0 : ℝ) 1, u * G u) / 2 at hPos
  have hGap := regionalLogEnergy_ge_fifth_gap_sub_low_odd_moments hG hGo
  rw [hFull, hMass, hM1, hM3] at hGap
  have hPrime := dilation_prime_reflection hs ho
  have hRet := retained_first_moment_lower hF.continuous hs ho
  simp only [autocorr_zero_eq] at hLag
  rw [hLag, hPos] at hRet
  have hRewrite : -2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2) =
      (Real.log 2 / Real.sqrt 2) *
        ∫ u in Icc (2 * Real.log 2 - 1) 1, G u * G (2 * Real.log 2 - u) := hPrime
  have hiMass : IntegrableOn (fun u => G u ^ 2) (Ioo (0 : ℝ) 1) :=
    (hG.continuous.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hPotential : (∫ u in Ioo (0 : ℝ) 1,
      (137 / 60 - firstFoldMomentMassCost - Real.log (1 - u ^ 2) / 2) * G u ^ 2) =
      (137 / 60 - firstFoldMomentMassCost - Real.log 2) * (∫ x, F x ^ 2) +
      ∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2) := by
    have he : (fun u => (137 / 60 - firstFoldMomentMassCost - Real.log (1 - u ^ 2) / 2) * G u ^ 2) =
        fun u => (137 / 60 - firstFoldMomentMassCost - Real.log 2) * G u ^ 2 +
          G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2) := by funext u; ring
    rw [he, integral_add (hiMass.const_mul _) hExt, integral_const_mul, hMass]
  change firstFoldTwoMomentForm G ≤ retainedOddGammaLowerForm F + (∫ x, F x ^ 2) / 64
  rw [firstFoldTwoMomentForm, hPotential]
  unfold firstFoldMomentMassCost at hRet ⊢
  dsimp only [G] at hRet hGap hRewrite ⊢
  nlinarith only [hRet, hGap, hRewrite]

/-- The complete Weil form dominates the explicit two-moment reflection form on the unit window. -/
theorem weilQuad_ge_firstFoldTwoMomentForm {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    firstFoldTwoMomentForm (fun u => F ((1 / 2) * u)) ≤ weilQuad F :=
  (retainedOddGamma_add_reserve_ge_firstFoldTwoMomentForm hF hs ho).trans
    (weilQuad_ge_retainedOddGamma_add_reserve hF hs ho)

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_ge_firstFoldTwoMomentForm
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedOddGamma_add_reserve_ge_firstFoldTwoMomentForm
