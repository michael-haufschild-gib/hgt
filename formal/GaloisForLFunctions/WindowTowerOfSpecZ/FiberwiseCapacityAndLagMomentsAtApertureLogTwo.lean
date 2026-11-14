import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaComparisonThroughApertureLogTwo
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicChargedGaps
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicBoundaryIdentity
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.EvenCorrelationMoments
import GaloisForLFunctions.HTGeometry.DirichletWirtinger
import GaloisForLFunctions.RHTower.VonMangoldtGammaFactorialBetaReflection

/-!
# Fiberwise capacity, lag moments, and SDP algebraic calculus at aperture `log 2`

This module develops the shared analytic and algebraic machinery used by both
parity sectors (`TheOddWeilFormHasAFloorAtApertureLogTwo` and
`TheEvenWeilFormHasAFloorAtApertureLogTwo`) to certify a uniform positive floor
on `weilQuad` at aperture `A = log 2`:

1. Dilation to the unit window `[-1, 1]`, mass and correlation scaling, positive
   half-window folding of the logarithmic lag and exterior boundary potential,
   and exact prime-two / prime-three autocorrelation folding.
2. Retention of all polynomial Gamma remainder charges up to degree 22.
3. Exact binomial expansion of all even lag moments `∫ t^(2q) autocorr G t` for
   even and odd sources, and exact Cauchy repeated-integral / integration-by-parts
   decomposition of odd lag moments `∫ t^(2q+1) autocorr G t` with Dirichlet–Wirtinger
   damping on the high-Legendre residual and Bessel–Cauchy–Schwarz control of
   the finite mode-spillover cross terms.
4. Polynomial Taylor comparisons for the `cosh` and `sinh` pole pairings.
5. Six-interval folding of `(0, 1)` onto `(0, (1 - a) / 2)` (four coupled branches)
   and `(1 - a, 1 / 2)` (two coupled branches), exact `4 × 4` and `2 × 2`
   tridiagonal `LDLᵀ` pivot lower bounds (`≥ 17 / 16`), Bernstein–Jensen `L²[0, 1]`
   polynomial residual bounds, and exact `LDLᵀ` plus strict diagonal-dominance
   certification of symmetric matrices.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Finset Zeta23
open scoped BigOperators
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open _root_.RHTower.WeilMarkovPole _root_.RHTower.WeilLevyPoleGauss
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory ArithmeticIncidencePositivity ArithmeticCriticalityTheory
open BiScaleUncertainty SpacingScaleHarmonicAnalysis SelectivePositivityAndThresholdLaws

/-! ### 1. Dilation to `[-1, 1]` and half-window folding at `A = log 2` -/

/-- The critical two-prime aperture `log 2` (`e^{2A} = 4`). -/
def apertureLogTwo : ℝ := Real.log 2

theorem apertureLogTwo_pos : 0 < apertureLogTwo :=
  Real.log_pos (by norm_num)

theorem apertureLogTwo_ne_zero : apertureLogTwo ≠ 0 :=
  apertureLogTwo_pos.ne'

/-- Unit-window rescaling `G(u) = F(u * log 2)` of a test `F` supported in `[-log 2, log 2]`. -/
def dilateLogTwo (F : ℝ → ℝ) (u : ℝ) : ℝ := F (apertureLogTwo * u)

theorem contDiff_dilateLogTwo {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (dilateLogTwo F) :=
  hF.comp (contDiff_const.mul contDiff_id)

theorem dilateLogTwo_outside {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo) {u : ℝ}
    (hu : u ∉ Icc (-1 : ℝ) 1) : dilateLogTwo F u = 0 := by
  unfold dilateLogTwo
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  have hi := hs ht
  have hA := apertureLogTwo_pos
  apply hu
  exact ⟨by nlinarith [hi.1], by nlinarith [hi.2]⟩

theorem tsupport_dilateLogTwo {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo) :
    tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  by_contra hn
  exact hu (dilateLogTwo_outside hs hn)

theorem even_integral_Icc_unit {H : ℝ → ℝ} (hH : Continuous H) (he : ∀ x, H (-x) = H x) :
    (∫ x in Icc (-1 : ℝ) 1, H x) = 2 * ∫ x in (0 : ℝ)..1, H x := by
  have hn := intervalIntegral.integral_comp_neg (f := H) (a := (0 : ℝ)) (b := 1)
  simp only [he, neg_zero] at hn
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hH.intervalIntegrable (-1) 0) (hH.intervalIntegrable 0 1)
  rw [← hn, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  linarith only [h]

theorem even_intervalIntegral_unit {H : ℝ → ℝ} (hH : Continuous H) (he : ∀ x, H (-x) = H x) :
    (∫ x in (-1 : ℝ)..1, H x) = 2 * ∫ x in (0 : ℝ)..1, H x := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  exact even_integral_Icc_unit hH he

theorem odd_integral_Icc_unit_zero {H : ℝ → ℝ} (ho : ∀ x, H (-x) = -H x) :
    (∫ x in Icc (-1 : ℝ) 1, H x) = 0 := by
  have h := intervalIntegral.integral_comp_neg (f := H) (a := (-1 : ℝ)) (b := 1)
  simp only [ho, intervalIntegral.integral_neg, neg_neg] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  linarith only [h]

theorem odd_whole_integral_zero {H : ℝ → ℝ} (ho : ∀ x, H (-x) = -H x) :
    (∫ x, H x) = 0 := by
  have h := integral_neg_eq_self H volume
  have hf : (fun x => H (-x)) = fun x => -H x := funext ho
  rw [hf, integral_neg] at h
  linarith only [h]

theorem dilated_mass_of_sq_even {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (hsq : ∀ u, dilateLogTwo F (-u) ^ 2 = dilateLogTwo F u ^ 2) :
    (∫ x, F x ^ 2) = 2 * apertureLogTwo * ∫ u in (0 : ℝ)..1, dilateLogTwo F u ^ 2 := by
  have hc : Continuous (dilateLogTwo F) := hF.comp (continuous_const.mul continuous_id)
  have hcut : (∫ u in Icc (-1 : ℝ) 1, dilateLogTwo F u ^ 2) = ∫ u, dilateLogTwo F u ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      rw [dilateLogTwo_outside hs hu, zero_pow two_ne_zero]
  have he := even_integral_Icc_unit (H := fun u => dilateLogTwo F u ^ 2) (hc.pow 2) hsq
  have hA := apertureLogTwo_pos
  have hscale := Measure.integral_comp_mul_left (fun x => F x ^ 2) apertureLogTwo
  rw [abs_of_pos (inv_pos.mpr hA), smul_eq_mul] at hscale
  change (∫ u, dilateLogTwo F u ^ 2) = apertureLogTwo⁻¹ * ∫ x, F x ^ 2 at hscale
  rw [hcut, hscale] at he
  field_simp [hA.ne'] at he ⊢
  linarith

theorem dilated_autocorr_log_two (F : ℝ → ℝ) (t : ℝ) :
    autocorr (dilateLogTwo F) t = apertureLogTwo⁻¹ * autocorr F (apertureLogTwo * t) := by
  unfold autocorr dilateLogTwo
  have hA := apertureLogTwo_pos
  have h := Measure.integral_comp_mul_left (fun x => F x * F (x + apertureLogTwo * t)) apertureLogTwo
  rw [abs_of_pos (inv_pos.mpr hA), smul_eq_mul] at h
  simpa only [mul_add] using h

theorem dilated_lag_log_two (F : ℝ → ℝ) :
    (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), (autocorr F 0 - autocorr F t) / t) =
      apertureLogTwo * ∫ t in Ioc (0 : ℝ) 2,
        (autocorr (dilateLogTwo F) 0 - autocorr (dilateLogTwo F) t) / t := by
  have hA := apertureLogTwo_pos
  have he (t : ℝ) :
      (autocorr (dilateLogTwo F) 0 - autocorr (dilateLogTwo F) t) / t =
        (autocorr F 0 - autocorr F (apertureLogTwo * t)) / (apertureLogTwo * t) := by
    rw [dilated_autocorr_log_two F 0, dilated_autocorr_log_two F t, mul_zero]
    field_simp [hA.ne']
  rw [setIntegral_congr_fun measurableSet_Ioc fun t _ => he t,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  have h := intervalIntegral.integral_comp_mul_left
    (fun t => (autocorr F 0 - autocorr F t) / t) (a := 0) (b := 2) hA.ne'
  rw [smul_eq_mul, mul_zero, mul_comm apertureLogTwo 2,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * apertureLogTwo)] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]

theorem dilated_correlation_moment_log_two (F : ℝ → ℝ) (n : ℕ) :
    (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ n * autocorr F t) =
      apertureLogTwo ^ (n + 2) * ∫ t in Ioc (0 : ℝ) 2,
        t ^ n * autocorr (dilateLogTwo F) t := by
  have hA := apertureLogTwo_pos
  have hc (t : ℝ) : autocorr F (apertureLogTwo * t) =
      apertureLogTwo * autocorr (dilateLogTwo F) t := by
    rw [dilated_autocorr_log_two, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]
  have he (t : ℝ) : (apertureLogTwo * t) ^ n * autocorr F (apertureLogTwo * t) =
      apertureLogTwo ^ (n + 1) * (t ^ n * autocorr (dilateLogTwo F) t) := by
    rw [hc, mul_pow, pow_succ]
    ring
  have h := intervalIntegral.mul_integral_comp_add_mul
    (f := fun t => t ^ n * autocorr F t) (a := (0 : ℝ)) (b := 2) (c := apertureLogTwo) (d := 0)
  simp only [zero_add, mul_zero] at h
  simp_rw [he] at h
  rw [intervalIntegral.integral_const_mul, ← mul_assoc,
    show apertureLogTwo * apertureLogTwo ^ (n + 1) = apertureLogTwo ^ (n + 2) by ring,
    show apertureLogTwo * 2 = 2 * apertureLogTwo by ring,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * apertureLogTwo)] at h
  exact h.symm

/-- Both even and odd tests satisfy `G(-u)² = G(u)²`, so the exterior logarithmic boundary
potential folds identically onto `(0, 1)` in both parity sectors. -/
theorem logarithmic_lag_half_of_sq_even {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) (hsq : ∀ u, G (-u) ^ 2 = G u ^ 2) :
    IntegrableOn (fun u => G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2)) (Ioo (0 : ℝ) 1) ∧
    (∫ t in Ioc (0 : ℝ) 2, (autocorr G 0 - autocorr G t) / t) / 2 =
      regionalLogEnergy G / 4 +
        ∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2) := by
  obtain ⟨hi, h⟩ := logarithmic_lag_and_boundary hG hs
  let f := (Icc (-1 : ℝ) 1).indicator (fun u => G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2))
  have hn (u : ℝ) : f (-u) = f u := by
    have hSu : -u ∈ Icc (-1 : ℝ) 1 ↔ u ∈ Icc (-1 : ℝ) 1 := by
      simp only [Set.mem_Icc]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    simp only [f, Set.indicator_apply, hSu, hsq, neg_sq]
  have ha (u : ℝ) : f |u| = f u := by
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu, hn]
  have hf_abs := integral_comp_abs (f := f)
  rw [integral_congr_ae (Eventually.of_forall ha)] at hf_abs
  dsimp only [f] at hf_abs
  rw [integral_indicator measurableSet_Icc, setIntegral_indicator measurableSet_Icc] at hf_abs
  have hset : Ioi (0 : ℝ) ∩ Icc (-1 : ℝ) 1 = Ioc (0 : ℝ) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨h0, _, h1⟩ => ⟨h0, h1⟩, fun ⟨h0, h1⟩ => ⟨h0, by linarith, h1⟩⟩
  rw [hset, integral_Icc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at hf_abs
  rw [hf_abs] at h
  refine ⟨hi.mono_set fun u hu => ⟨by linarith [hu.1], hu.2⟩, ?_⟩
  linarith only [h]

/-! ### 2. Prime-2 and Prime-3 autocorrelation folding on `[0, 1]` -/

/-- Normalized prime-3 offset `a = log 3 / log 2 - 1 ∈ (0, 1)` (`log 3 = (1 + a) * log 2`). -/
def primeThreeOffset : ℝ := Real.log 3 / Real.log 2 - 1

theorem primeThreeOffset_bounds :
    1 / 2 < primeThreeOffset ∧ primeThreeOffset < 3 / 5 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  obtain ⟨h3l, h3u⟩ := log_three_bounds_d26
  have h2p : 0 < Real.log 2 := apertureLogTwo_pos
  unfold primeThreeOffset
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ h2p]
    have hc : (1 / 2 + 1 : ℝ) * logTwoHi < logThreeLo := by norm_num [logTwoHi, logThreeLo]
    linarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ h2p]
    have hc : logThreeHi < (3 / 5 + 1 : ℝ) * logTwoLo := by norm_num [logTwoLo, logThreeHi]
    linarith

theorem autocorr_shift_unit_support {G : ℝ → ℝ} (hG : Continuous G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) {τ : ℝ} (_ : 0 ≤ τ) (hτ2 : τ ≤ 2) :
    autocorr G τ = ∫ u in (-1 : ℝ)..(1 - τ), G u * G (u + τ) := by
  have hvan := supported_vanish_at_aperture hG hs
  unfold autocorr
  have hcut : (∫ u, G u * G (u + τ)) = ∫ u in Icc (-1 : ℝ) (1 - τ), G u * G (u + τ) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    by_cases hu1 : u < -1
    · rw [hvan u (by rw [abs_of_neg (by linarith)]; linarith), zero_mul]
    · have hu2 : 1 - τ < u := lt_of_not_ge fun hle => hu ⟨le_of_not_gt hu1, hle⟩
      rw [hvan (u + τ) (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  rw [hcut, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -1 ≤ 1 - τ)]

theorem autocorr_one_of_parity {G : ℝ → ℝ} (hG : Continuous G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) {s : ℝ} (hp : ∀ u, G (-u) = s * G u) :
    autocorr G 1 = 2 * s * ∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u) := by
  rw [autocorr_shift_unit_support hG hs (by norm_num) (by norm_num), sub_self]
  have hneg := intervalIntegral.integral_comp_neg (f := fun u => G u * G (u + 1)) (a := (0 : ℝ)) (b := 1)
  simp only [neg_zero] at hneg
  rw [← hneg]
  have hcongr : (∫ u in (0 : ℝ)..1, G (-u) * G (-u + 1)) =
      s * ∫ u in (0 : ℝ)..1, G u * G (1 - u) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [hp u, show -u + 1 = 1 - u by ring]
    ring
  rw [hcongr]
  have hc1 : Continuous (fun u => G u * G (1 - u)) := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := (0 : ℝ)) (b := 1 / 2) (c := 1)
    (hc1.intervalIntegrable _ _) (hc1.intervalIntegrable _ _)
  have hsub := intervalIntegral.integral_comp_sub_left
    (f := fun u => G u * G (1 - u)) (d := 1) (a := (1 / 2 : ℝ)) (b := 1)
  norm_num at hsub
  have hsym : (∫ u in (0 : ℝ)..(1 / 2), G (1 - u) * G (1 - (1 - u))) =
      ∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring
  rw [hsym] at hsub
  rw [← hsplit, hsub]
  ring

theorem autocorr_primeThree_of_parity {G : ℝ → ℝ} (hG : Continuous G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) {sgn : ℝ} (hp : ∀ u, G (-u) = sgn * G u) :
    autocorr G (1 + primeThreeOffset) =
      2 * sgn * ∫ t in (0 : ℝ)..((1 - primeThreeOffset) / 2),
        G (1 - t) * G (primeThreeOffset + t) := by
  set a := primeThreeOffset
  obtain ⟨ha_lo, ha_hi⟩ := primeThreeOffset_bounds
  rw [autocorr_shift_unit_support hG hs (by linarith) (by linarith)]
  have h1 : 1 - (1 + a) = -a := by ring
  rw [h1]
  have hshift := intervalIntegral.integral_comp_sub_right
    (f := fun u => G u * G (u + (1 + a))) (d := 1) (a := (0 : ℝ)) (b := 1 - a)
  rw [show (0 : ℝ) - 1 = -1 by ring, show 1 - a - 1 = -a by ring] at hshift
  rw [← hshift]
  have hcongr : (∫ t in (0 : ℝ)..(1 - a), G (t - 1) * G (t - 1 + (1 + a))) =
      sgn * ∫ t in (0 : ℝ)..(1 - a), G (1 - t) * G (a + t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [show t - 1 = -(1 - t) by ring, hp (1 - t),
      show -(1 - t) + (1 + a) = a + t by ring]
    ring
  rw [hcongr]
  set L4 := (1 - a) / 2
  have hc : Continuous (fun t => G (1 - t) * G (a + t)) := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := (0 : ℝ)) (b := L4) (c := 1 - a) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hsub := intervalIntegral.integral_comp_sub_left
    (f := fun t => G (1 - t) * G (a + t)) (d := 1 - a) (a := L4) (b := 1 - a)
  have hL : 1 - a - L4 = L4 := by dsimp [L4]; ring
  rw [sub_self, hL] at hsub
  have hsym : (∫ t in (0 : ℝ)..L4, G (1 - (1 - a - t)) * G (a + (1 - a - t))) =
      ∫ t in (0 : ℝ)..L4, G (1 - t) * G (a + t) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have he1 : 1 - (1 - a - t) = a + t := by ring
    have he2 : a + (1 - a - t) = 1 - t := by ring
    rw [he1, he2, mul_comm]
  rw [hsym] at hsub
  rw [← hsplit, hsub]
  ring

/-! ### 3. Retained Gamma remainder moments at `A = log 2` -/

/-- Exact archimedean mass coefficient after retaining all Gamma polynomial remainder moments up to
degree 22 on `(0, 2 * log 2]`. -/
def twoPrimeGammaMassExact : ℝ :=
  let r := 2 * apertureLogTwo
  Zeta23.EF.gammaBracket 0 + r / 2 - r ^ 2 / 48 - r ^ 3 / 48 + 2 * archLevyAntideriv r +
    7 * r ^ 4 / (4 * 5760) - 31 * r ^ 6 / (6 * 967680) + 127 * r ^ 8 / (8 * 154828800) +
    ∑ q ∈ Finset.range 12, gammaAlphaEven q * r ^ (2 * q + 1) / (2 * (q : ℝ) + 1)

theorem weilQuad_ge_retained_gamma_moments {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo) :
    (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), (autocorr F 0 - autocorr F t) / t) +
      twoPrimeGammaMassExact * (∫ x, F x ^ 2) - (∫ x, F x) ^ 2 / 4 +
      (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t * autocorr F t) / 24 -
      7 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 3 * autocorr F t) / 5760 +
      31 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 5 * autocorr F t) / 967680 -
      127 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 7 * autocorr F t) / 154828800 +
      (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 2 * autocorr F t) / 16 -
      (∑ q ∈ Finset.range 12, gammaAlphaEven q *
        ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ (2 * q) * autocorr F t) -
      2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2) -
      2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3) +
      coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2 ≤ weilQuad F := by
  have hcs : HasCompactSupport F :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hs
  set r := 2 * apertureLogTwo
  have hr_pos : 0 < r := by positivity [apertureLogTwo_pos]
  have hr_lt : r < 7 / 5 := two_mul_log_two_lt_seven_fifths
  have hr2 : r ≤ 2 := by linarith
  have hs_r : tsupport F ⊆ Icc (-(r / 2)) (r / 2) := by simpa [r] using hs
  have hgam := gamma_eq_logarithmic_lag_correlation_moments_and_remainder_to_two
    hF hcs hr_pos hr2 hs_r
  have hw := weilQuad_two_prime_decomposition hF hs
  set M := autocorr F 0
  set D := fun t => M - autocorr F t
  have hc : Continuous (autocorr F) := continuous_autocorr hF hcs
  have hdc : Continuous D := continuous_const.sub hc
  have hd_nn : ∀ t, 0 ≤ D t := fun t =>
    sub_nonneg.mpr ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF.continuous t))
  have hiR : IntegrableOn (fun t => retainedGammaRemainderWeight t * D t) (Ioc (0 : ℝ) r) :=
    (local_gamma_terms_integrable_to_two hF hcs).2.mono_set fun _ ht => ⟨ht.1, ht.2.trans hr2⟩
  have hcP : Continuous (fun t => retainedGammaPolyRem t * D t) := by
    unfold retainedGammaPolyRem
    fun_prop
  have hiP : IntegrableOn (fun t => retainedGammaPolyRem t * D t) (Ioc (0 : ℝ) r) :=
    hcP.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmono : (∫ t in Ioc (0 : ℝ) r, retainedGammaPolyRem t * D t) ≤
      ∫ t in Ioc (0 : ℝ) r, retainedGammaRemainderWeight t * D t := by
    refine setIntegral_mono_on hiP hiR measurableSet_Ioc fun t ht => ?_
    exact mul_le_mul_of_nonneg_right
      (retainedGammaPolyRem_le_retainedGammaRemainderWeight ⟨ht.1, ht.2.trans hr_lt.le⟩) (hd_nn t)
  have hpow_D (n : ℕ) : (∫ t in Ioc (0 : ℝ) r, t ^ n * D t) =
      M * r ^ (n + 1) / ((n : ℝ) + 1) - ∫ t in Ioc (0 : ℝ) r, t ^ n * autocorr F t := by
    have he : (fun t => t ^ n * D t) = fun t => M * t ^ n - t ^ n * autocorr F t := by
      funext t; dsimp [D]; ring
    have hi1 : IntegrableOn (fun t => M * t ^ n) (Ioc (0 : ℝ) r) :=
      (continuous_const.mul (continuous_pow n)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hi2 : IntegrableOn (fun t => t ^ n * autocorr F t) (Ioc (0 : ℝ) r) :=
      ((continuous_pow n).mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [he, integral_sub hi1 hi2,
      integral_const_mul, ← intervalIntegral.integral_of_le hr_pos.le, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero n), sub_zero]
    ring
  have hsum_even : (∫ t in Ioc (0 : ℝ) r,
      (∑ q ∈ Finset.range 12, gammaAlphaEven q * t ^ (2 * q)) * D t) =
      (∑ q ∈ Finset.range 12, gammaAlphaEven q * r ^ (2 * q + 1) / (2 * (q : ℝ) + 1)) * M -
        ∑ q ∈ Finset.range 12, gammaAlphaEven q * ∫ t in Ioc (0 : ℝ) r, t ^ (2 * q) * autocorr F t := by
    have hiq (q : ℕ) : IntegrableOn (fun t => gammaAlphaEven q * (t ^ (2 * q) * D t)) (Ioc (0 : ℝ) r) :=
      (continuous_const.mul ((continuous_pow (2 * q)).mul hdc)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ fun q _ => hiq q]
    simp_rw [integral_const_mul, hpow_D, mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    push_cast
    ring
  have hpoly_int : (∫ t in Ioc (0 : ℝ) r, retainedGammaPolyRem t * D t) =
      (7 * r ^ 4 / (4 * 5760) - 31 * r ^ 6 / (6 * 967680) + 127 * r ^ 8 / (8 * 154828800) +
        ∑ q ∈ Finset.range 12, gammaAlphaEven q * r ^ (2 * q + 1) / (2 * (q : ℝ) + 1)) * M -
      7 * (∫ t in Ioc (0 : ℝ) r, t ^ 3 * autocorr F t) / 5760 +
      31 * (∫ t in Ioc (0 : ℝ) r, t ^ 5 * autocorr F t) / 967680 -
      127 * (∫ t in Ioc (0 : ℝ) r, t ^ 7 * autocorr F t) / 154828800 -
      ∑ q ∈ Finset.range 12, gammaAlphaEven q * ∫ t in Ioc (0 : ℝ) r, t ^ (2 * q) * autocorr F t := by
    have hsplit_fn : (fun t => retainedGammaPolyRem t * D t) =
        fun t => ((7 / 5760 : ℝ) * (t ^ 3 * D t) - (31 / 967680 : ℝ) * (t ^ 5 * D t) +
          (127 / 154828800 : ℝ) * (t ^ 7 * D t)) +
          (∑ q ∈ Finset.range 12, gammaAlphaEven q * t ^ (2 * q)) * D t := by
      funext t; unfold retainedGammaPolyRem; ring
    have hi_odd (n : ℕ) : IntegrableOn (fun t => t ^ n * D t) (Ioc (0 : ℝ) r) :=
      ((continuous_pow n).mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hi_o1 : IntegrableOn (fun t => (7 / 5760 : ℝ) * (t ^ 3 * D t) - (31 / 967680 : ℝ) * (t ^ 5 * D t)) (Ioc (0 : ℝ) r) :=
      ((hi_odd 3).const_mul _).sub ((hi_odd 5).const_mul _)
    have hi_o2 : IntegrableOn (fun t => ((7 / 5760 : ℝ) * (t ^ 3 * D t) - (31 / 967680 : ℝ) * (t ^ 5 * D t)) +
        (127 / 154828800 : ℝ) * (t ^ 7 * D t)) (Ioc (0 : ℝ) r) :=
      hi_o1.add ((hi_odd 7).const_mul _)
    have hi_ev : IntegrableOn (fun t => (∑ q ∈ Finset.range 12, gammaAlphaEven q * t ^ (2 * q)) * D t) (Ioc (0 : ℝ) r) := by
      refine Continuous.integrableOn_Icc ?_ |>.mono_set Ioc_subset_Icc_self
      fun_prop
    rw [hsplit_fn, integral_add hi_o2 hi_ev, integral_add hi_o1 ((hi_odd 7).const_mul _),
      integral_sub ((hi_odd 3).const_mul _) ((hi_odd 5).const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul,
      hpow_D 3, hpow_D 5, hpow_D 7, hsum_even]
    norm_num
    ring
  rw [hpoly_int] at hmono
  have hM : M = ∫ x, F x ^ 2 := autocorr_zero_eq F
  rw [hM] at hmono
  unfold twoPrimeGammaMassExact
  dsimp only
  linarith [hw, hgam, hmono]

/-! ### 4. General even lag moments `∫ t^(2q) autocorr G t` for even and odd sources -/

private theorem weighted_autocorr_prod_integrable {G : ℝ → ℝ} (hG : Continuous G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) (n : ℕ) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ n * G p.2 * G (p.2 + p.1)) (volume.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ => p.1 ^ n * G p.2 * G (p.2 + p.1)) := by fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (-2 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1)
    (isCompact_Icc.prod isCompact_Icc)
  intro p hp
  by_cases hx : G p.2 = 0
  · simp only [hx, mul_zero, zero_mul]
  by_cases hy : G (p.2 + p.1) = 0
  · simp only [hy, mul_zero]
  have hxi : p.2 ∈ Icc (-1 : ℝ) 1 := by
    by_contra h; exact hx (image_eq_zero_of_notMem_tsupport fun ht => h (hs ht))
  have hyi : p.2 + p.1 ∈ Icc (-1 : ℝ) 1 := by
    by_contra h; exact hy (image_eq_zero_of_notMem_tsupport fun ht => h (hs ht))
  exact False.elim (hp ⟨⟨by linarith [hxi.2, hyi.1], by linarith [hxi.1, hyi.2]⟩, hxi⟩)

private theorem sum_range_even_odd_split (f : ℕ → ℝ) (q : ℕ) :
    (∑ j ∈ Finset.range (2 * q + 1), f j) =
      (∑ r ∈ Finset.range (q + 1), f (2 * r)) + ∑ r ∈ Finset.range q, f (2 * r + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [show 2 * (q + 1) + 1 = (2 * q + 1) + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

private theorem whole_even_lag_moment {G : ℝ → ℝ} (hG : Continuous G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) (q : ℕ) :
    (∫ t, t ^ (2 * q) * autocorr G t) =
      ∑ j ∈ Finset.range (2 * q + 1),
        ((-1 : ℝ) ^ j * ((2 * q).choose j : ℝ)) *
          (∫ x, x ^ j * G x) * (∫ y, y ^ (2 * q - j) * G y) := by
  have hcs : HasCompactSupport G := isCompact_Icc.of_isClosed_subset (isClosed_tsupport G) hs
  have hip (m : ℕ) : Integrable (fun x : ℝ => x ^ m * G x) :=
    ((continuous_pow m).mul hG).integrable_of_hasCompactSupport hcs.mul_left
  have hl (t : ℝ) : t ^ (2 * q) * autocorr G t = ∫ x, t ^ (2 * q) * G x * G (x + t) := by
    unfold autocorr
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  simp_rw [hl]
  rw [integral_integral_swap (weighted_autocorr_prod_integrable hG hs (2 * q))]
  have hrow (x : ℝ) : (∫ t, t ^ (2 * q) * G x * G (x + t)) =
      ∑ j ∈ Finset.range (2 * q + 1),
        ((-1 : ℝ) ^ j * ((2 * q).choose j : ℝ)) * (x ^ j * G x) * (∫ y, y ^ (2 * q - j) * G y) := by
    have hshift : (∫ t, t ^ (2 * q) * G x * G (x + t)) =
        ∫ y, (y - x) ^ (2 * q) * G x * G y := by
      calc
        _ = ∫ t, (x + t - x) ^ (2 * q) * G x * G (x + t) :=
          integral_congr_ae (Eventually.of_forall fun t => by ring)
        _ = _ := integral_add_left_eq_self (fun y : ℝ => (y - x) ^ (2 * q) * G x * G y) x
    have hbin (y : ℝ) : (y - x) ^ (2 * q) * G x * G y =
        ∑ j ∈ Finset.range (2 * q + 1),
          (((-1 : ℝ) ^ j * ((2 * q).choose j : ℝ)) * (x ^ j * G x)) * (y ^ (2 * q - j) * G y) := by
      rw [sub_eq_add_neg, add_comm y (-x), add_pow, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [neg_pow]
      ring
    rw [hshift]
    simp_rw [hbin]
    rw [integral_finsetSum _ fun j _ => (hip (2 * q - j)).const_mul _]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul]
  simp_rw [hrow]
  rw [integral_finsetSum _ fun j _ => ((hip j).const_mul _).mul_const _]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const, integral_const_mul]

private theorem half_even_lag_moment_eq_half_whole {G : ℝ → ℝ}
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) (q : ℕ) :
    (∫ t in Ioc (0 : ℝ) 2, t ^ (2 * q) * autocorr G t) =
      (1 / 2 : ℝ) * ∫ t, t ^ (2 * q) * autocorr G t := by
  have hev : (fun t : ℝ => |t| ^ (2 * q) * autocorr G |t|) =
      fun t => t ^ (2 * q) * autocorr G t := by
    funext t
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, pow_mul, neg_sq, ← pow_mul, autocorr_neg]
  have hhalf := integral_comp_abs (f := fun t => t ^ (2 * q) * autocorr G t)
  rw [hev] at hhalf
  have hcut : (∫ t in Ioi (0 : ℝ), t ^ (2 * q) * autocorr G t) =
      ∫ t in Ioc (0 : ℝ) 2, t ^ (2 * q) * autocorr G t := by
    have he : ∀ t ∈ Ioi (0 : ℝ), t ^ (2 * q) * autocorr G t =
        (Iic (2 : ℝ)).indicator (fun t => t ^ (2 * q) * autocorr G t) t := by
      intro t _
      by_cases ht : t ≤ 2
      · exact (Set.indicator_of_mem (s := Iic (2 : ℝ)) ht _).symm
      · rw [Set.indicator_of_notMem (s := Iic (2 : ℝ)) ht,
          autocorr_eq_zero_of_support (r := 2) (by simpa using hs) (lt_of_not_ge ht), mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic]
    have hset : Ioi (0 : ℝ) ∩ Iic 2 = Ioc (0 : ℝ) 2 := Ioi_inter_Iic
    rw [hset]
  linarith [hhalf, hcut]

theorem even_lag_moment_of_even {G : ℝ → ℝ} (hG : Continuous G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) (he : ∀ u, G (-u) = G u) (q : ℕ) :
    (∫ t in Ioc (0 : ℝ) 2, t ^ (2 * q) * autocorr G t) =
      2 * ∑ r ∈ Finset.range (q + 1), ((2 * q).choose (2 * r) : ℝ) *
        (∫ u in (0 : ℝ)..1, u ^ (2 * (q - r)) * G u) *
        (∫ u in (0 : ℝ)..1, u ^ (2 * r) * G u) := by
  rw [half_even_lag_moment_eq_half_whole hs q, whole_even_lag_moment hG hs q,
    sum_range_even_odd_split]
  have hodd_zero : (∑ r ∈ Finset.range q,
      ((-1 : ℝ) ^ (2 * r + 1) * ((2 * q).choose (2 * r + 1) : ℝ)) *
        (∫ x, x ^ (2 * r + 1) * G x) * (∫ y, y ^ (2 * q - (2 * r + 1)) * G y)) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    have hz : (∫ x, x ^ (2 * r + 1) * G x) = 0 := by
      apply odd_whole_integral_zero
      intro x
      rw [he, pow_succ, pow_mul, neg_sq]
      ring
    rw [hz, mul_zero, zero_mul]
  rw [hodd_zero, add_zero]
  have hev_moment (m : ℕ) : (∫ x, x ^ (2 * m) * G x) =
      2 * ∫ u in (0 : ℝ)..1, u ^ (2 * m) * G u := by
    have hcut : (∫ x in Icc (-1 : ℝ) 1, x ^ (2 * m) * G x) = ∫ x, x ^ (2 * m) * G x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun ht => hx (hs ht), mul_zero]
    rw [← hcut]
    exact even_integral_Icc_unit (H := fun x => x ^ (2 * m) * G x) ((continuous_pow _).mul hG) fun x => by
      rw [he, pow_mul, neg_sq, ← pow_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr_le : r ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hsub : 2 * q - 2 * r = 2 * (q - r) := by omega
  rw [hsub, hev_moment r, hev_moment (q - r), pow_mul, neg_one_sq, one_pow]
  ring

theorem even_lag_moment_of_odd {G : ℝ → ℝ} (hG : Continuous G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) (ho : ∀ u, G (-u) = -G u) (q : ℕ) :
    (∫ t in Ioc (0 : ℝ) 2, t ^ (2 * q) * autocorr G t) =
      -2 * ∑ r ∈ Finset.range q, ((2 * q).choose (2 * r + 1) : ℝ) *
        (∫ u in (0 : ℝ)..1, u ^ (2 * (q - 1 - r) + 1) * G u) *
        (∫ u in (0 : ℝ)..1, u ^ (2 * r + 1) * G u) := by
  rw [half_even_lag_moment_eq_half_whole hs q, whole_even_lag_moment hG hs q,
    sum_range_even_odd_split]
  have hev_zero : (∑ r ∈ Finset.range (q + 1),
      ((-1 : ℝ) ^ (2 * r) * ((2 * q).choose (2 * r) : ℝ)) *
        (∫ x, x ^ (2 * r) * G x) * (∫ y, y ^ (2 * q - 2 * r) * G y)) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    have hz : (∫ x, x ^ (2 * r) * G x) = 0 := by
      apply odd_whole_integral_zero
      intro x
      rw [ho, pow_mul, neg_sq, ← pow_mul, mul_neg]
    rw [hz, mul_zero, zero_mul]
  rw [hev_zero, zero_add]
  have hodd_moment (m : ℕ) : (∫ x, x ^ (2 * m + 1) * G x) =
      2 * ∫ u in (0 : ℝ)..1, u ^ (2 * m + 1) * G u := by
    have hcut : (∫ x in Icc (-1 : ℝ) 1, x ^ (2 * m + 1) * G x) = ∫ x, x ^ (2 * m + 1) * G x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun ht => hx (hs ht), mul_zero]
    rw [← hcut]
    exact even_integral_Icc_unit (H := fun x => x ^ (2 * m + 1) * G x) ((continuous_pow _).mul hG) fun x => by
      rw [ho, pow_succ, pow_mul, neg_sq, ← pow_mul]
      ring
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr_lt : r < q := Finset.mem_range.mp hr
  have hsub : 2 * q - (2 * r + 1) = 2 * (q - 1 - r) + 1 := by omega
  have hsign : (-1 : ℝ) ^ (2 * r + 1) = -1 := by rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [hsub, hsign, hodd_moment r, hodd_moment (q - 1 - r)]
  ring

/-! ### 5. Legendre projection, iterated primitives, odd lag moments, and Wirtinger bounds -/

/-- Normalized Legendre projection coefficient `((2n + 1) / 2) * ∫_{-1}^1 G(x) P_n(x) dx`. -/
def projCoeff (G : ℝ → ℝ) (n : ℕ) : ℝ :=
  ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment G n

/-- Truncated Legendre projection `P_m G = ∑_{n < m} projCoeff G n * legP n` on `[-1, 1]`. -/
def lowProj (G : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  regionalLegendreSum (Finset.range m) (projCoeff G)

theorem contDiff_legP_all (n : ℕ) {k : WithTop ℕ∞} : ContDiff ℝ k (legP n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · have he : legP 0 = fun _ => (1 : ℝ) := funext legP_zero
      rw [he]; exact contDiff_const
    · have he : legP 1 = fun x => x := funext legP_one
      rw [he]; exact contDiff_id
    · have he : legP (n + 2) = fun x =>
          ((2 * (n : ℝ) + 3) * x * legP (n + 1) x - ((n : ℝ) + 1) * legP n x) / ((n : ℝ) + 2) :=
        funext (legP_succ_succ n)
      rw [he]
      exact (((contDiff_const.mul contDiff_id).mul (ih (n + 1) (by omega))).sub
        (contDiff_const.mul (ih n (by omega)))).div_const _

theorem contDiff_lowProj (G : ℝ → ℝ) (m : ℕ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (lowProj G m) := by
  unfold lowProj regionalLegendreSum
  exact ContDiff.sum fun n _ => contDiff_const.mul (contDiff_legP_all n)

theorem lowProj_moment_lt (G : ℝ → ℝ) {m n : ℕ} (hn : n < m) :
    regionalLegendreMoment (lowProj G m) n = regionalLegendreMoment G n := by
  rw [lowProj, regionalLegendreMoment_sum, if_pos (Finset.mem_range.mpr hn), projCoeff]
  field_simp [show (2 * (n : ℝ) + 1) ≠ 0 by positivity]

theorem lowProj_moment_ge (G : ℝ → ℝ) {m n : ℕ} (hn : m ≤ n) :
    regionalLegendreMoment (lowProj G m) n = 0 := by
  rw [lowProj, regionalLegendreMoment_sum, if_neg (by simp [hn])]

theorem sub_lowProj_moment_lt {G : ℝ → ℝ} (hG : Continuous G) {m n : ℕ} (hn : n < m) :
    regionalLegendreMoment (fun x => G x - lowProj G m x) n = 0 := by
  have hP : Continuous (lowProj G m) := (contDiff_lowProj G m (k := 0)).continuous
  have hi1 : IntegrableOn (fun x => G x * legP n x) (Icc (-1 : ℝ) 1) :=
    (hG.mul (continuous_legP n)).integrableOn_Icc
  have hi2 : IntegrableOn (fun x => lowProj G m x * legP n x) (Icc (-1 : ℝ) 1) :=
    (hP.mul (continuous_legP n)).integrableOn_Icc
  unfold regionalLegendreMoment
  simp_rw [sub_mul]
  rw [integral_sub hi1 hi2]
  change regionalLegendreMoment G n - regionalLegendreMoment (lowProj G m) n = 0
  rw [lowProj_moment_lt G hn, sub_self]

theorem sub_lowProj_moment_ge {G : ℝ → ℝ} (hG : Continuous G) {m n : ℕ} (hn : m ≤ n) :
    regionalLegendreMoment (fun x => G x - lowProj G m x) n = regionalLegendreMoment G n := by
  have hP : Continuous (lowProj G m) := (contDiff_lowProj G m (k := 0)).continuous
  have hi1 : IntegrableOn (fun x => G x * legP n x) (Icc (-1 : ℝ) 1) :=
    (hG.mul (continuous_legP n)).integrableOn_Icc
  have hi2 : IntegrableOn (fun x => lowProj G m x * legP n x) (Icc (-1 : ℝ) 1) :=
    (hP.mul (continuous_legP n)).integrableOn_Icc
  unfold regionalLegendreMoment
  simp_rw [sub_mul]
  rw [integral_sub hi1 hi2]
  change regionalLegendreMoment G n - regionalLegendreMoment (lowProj G m) n = _
  rw [lowProj_moment_ge G hn, sub_zero]

theorem projection_residual_mass_pub {G : ℝ → ℝ} (hG : Continuous G) (m : ℕ) :
    (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G m x) ^ 2) =
      (∫ x in Icc (-1 : ℝ) 1, G x ^ 2) -
        ∑ n ∈ Finset.range m, ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment G n ^ 2 := by
  let P := lowProj G m
  let B := ∑ n ∈ Finset.range m, ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment G n ^ 2
  have hP : Continuous P := (contDiff_lowProj G m (k := 0)).continuous
  have hmul (H : ℝ → ℝ) (hH : Continuous H) :
      (∫ x in Icc (-1 : ℝ) 1, H x * P x) =
        ∑ n ∈ Finset.range m, projCoeff G n * regionalLegendreMoment H n := by
    have hin (n : ℕ) : IntegrableOn (fun x => projCoeff G n * (H x * legP n x)) (Icc (-1 : ℝ) 1) :=
      (continuous_const.mul (hH.mul (continuous_legP n))).integrableOn_Icc
    unfold P lowProj regionalLegendreSum regionalLegendreMoment
    simp_rw [Finset.mul_sum, show ∀ n x, H x * (projCoeff G n * legP n x) =
      projCoeff G n * (H x * legP n x) by intros; ring]
    rw [integral_finsetSum _ fun n _ => hin n]
    simp_rw [integral_const_mul]
  have hGP : (∫ x in Icc (-1 : ℝ) 1, G x * P x) = B := by
    rw [hmul G hG]
    apply Finset.sum_congr rfl; intro n _; dsimp [projCoeff]; ring
  have hPP : (∫ x in Icc (-1 : ℝ) 1, P x ^ 2) = B := by
    have h := hmul P hP
    simp_rw [pow_two]
    rw [h]
    apply Finset.sum_congr rfl; intro n hn
    rw [lowProj_moment_lt G (Finset.mem_range.mp hn)]; dsimp [projCoeff]; ring
  have hiGG : IntegrableOn (fun x => G x ^ 2) (Icc (-1 : ℝ) 1) := (hG.pow 2).integrableOn_Icc
  have hiPP : IntegrableOn (fun x => P x ^ 2) (Icc (-1 : ℝ) 1) := (hP.pow 2).integrableOn_Icc
  have hiGP : IntegrableOn (fun x => G x * P x) (Icc (-1 : ℝ) 1) := (hG.mul hP).integrableOn_Icc
  have he : (fun x => (G x - lowProj G m x) ^ 2) =
      fun x => (G x ^ 2 + P x ^ 2) - 2 * (G x * P x) := by
    funext x; dsimp [P]; ring
  rw [he, integral_sub (hiGG.add hiPP) (hiGP.const_mul 2), integral_add hiGG hiPP,
    integral_const_mul, hGP, hPP]
  dsimp [B]
  ring

theorem regionalLogEnergy_ge_low_add_gap_residual {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (m : ℕ) :
    (∑ n ∈ Finset.range m, regionalLogEigenvalue n *
        ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment G n ^ 2) +
      regionalLogEigenvalue m * (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G m x) ^ 2) ≤
      regionalLogEnergy G := by
  have hgap := regionalLogEnergy_ge_gap_sub_low_moments hG m
  rw [projection_residual_mass_pub hG.continuous m]
  have halg : (∑ n ∈ Finset.range m, regionalLogEigenvalue n *
        ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment G n ^ 2) +
      regionalLogEigenvalue m * ((∫ x in Icc (-1 : ℝ) 1, G x ^ 2) -
        ∑ n ∈ Finset.range m, ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment G n ^ 2) =
      regionalLogEigenvalue m * (∫ x in Icc (-1 : ℝ) 1, G x ^ 2) -
        ∑ n ∈ Finset.range m, (regionalLogEigenvalue m - regionalLogEigenvalue n) *
          ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment G n ^ 2 := by
    rw [mul_sub, Finset.mul_sum]
    have hsub : ∀ a b c : ℝ, a + (b - c) = b - (c - a) := by intros; ring
    rw [hsub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro n _; ring
  rw [halg]
  exact hgap

/-- Polynomials of degree strictly less than `d`, represented on `ℝ` in the monomial basis. -/
def isPolyDeg (d : ℕ) (P : ℝ → ℝ) : Prop :=
  ∃ a : ℕ → ℝ, ∀ x, P x = ∑ k ∈ Finset.range d, a k * x ^ k

/-- Functions in the span of `legP 0, ..., legP (N - 1)`. -/
def inLegSpan (N : ℕ) (P : ℝ → ℝ) : Prop :=
  ∃ c : ℕ → ℝ, ∀ x, P x = ∑ n ∈ Finset.range N, c n * legP n x

theorem inLegSpan_mono {M N : ℕ} (hMN : M ≤ N) {P : ℝ → ℝ} (h : inLegSpan M P) :
    inLegSpan N P := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun n => if n < M then c n else 0, fun x => ?_⟩
  dsimp only
  rw [hc x, ← Finset.sum_subset (Finset.range_mono hMN)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos (Finset.mem_range.mp hn)]
  · intro n _ hnM
    rw [if_neg (by simp at hnM; omega), zero_mul]

theorem inLegSpan_zero (N : ℕ) : inLegSpan N (fun _ => 0) :=
  ⟨fun _ => 0, fun _ => by simp⟩

theorem inLegSpan_add {N : ℕ} {P Q : ℝ → ℝ} (hP : inLegSpan N P) (hQ : inLegSpan N Q) :
    inLegSpan N (fun x => P x + Q x) := by
  obtain ⟨cP, hcP⟩ := hP
  obtain ⟨cQ, hcQ⟩ := hQ
  refine ⟨fun n => cP n + cQ n, fun x => ?_⟩
  dsimp only
  rw [hcP x, hcQ x, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro n _; ring

theorem inLegSpan_smul {N : ℕ} (α : ℝ) {P : ℝ → ℝ} (hP : inLegSpan N P) :
    inLegSpan N (fun x => α * P x) := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨fun n => α * c n, fun x => ?_⟩
  dsimp only
  rw [hc x, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n _; ring

theorem inLegSpan_legP {n N : ℕ} (hn : n < N) : inLegSpan N (legP n) := by
  refine ⟨fun k => if k = n then 1 else 0, fun x => ?_⟩
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hn)]

theorem inLegSpan_mul_id : ∀ {N : ℕ} {P : ℝ → ℝ}, inLegSpan N P →
    inLegSpan (N + 1) (fun x => x * P x) := by
  intro N P ⟨c, hc⟩
  have hterm : ∀ n < N, inLegSpan (N + 1) (fun x => c n * (x * legP n x)) := by
    intro n hn
    apply inLegSpan_smul (c n)
    rcases n with _ | m
    · have he : (fun x => x * legP 0 x) = legP 1 := by
        funext x; rw [legP_zero, legP_one, mul_one]
      rw [he]; exact inLegSpan_legP (by omega)
    · have hb : ∀ x, x * legP (m + 1) x =
          (((m : ℝ) + 2) / (2 * (m : ℝ) + 3)) * legP (m + 2) x +
          (((m : ℝ) + 1) / (2 * (m : ℝ) + 3)) * legP m x := by
        intro x
        have hrec := legP_succ_succ m x
        have hpos : (0 : ℝ) < 2 * (m : ℝ) + 3 := by positivity
        have hpos2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
        field_simp [hpos.ne']
        have hrec' : ((m : ℝ) + 2) * legP (m + 2) x =
            (2 * (m : ℝ) + 3) * x * legP (m + 1) x - ((m : ℝ) + 1) * legP m x := by
          rw [hrec, mul_div_cancel₀ _ hpos2.ne']
        linarith
      have he : (fun x => x * legP (m + 1) x) = fun x =>
          (((m : ℝ) + 2) / (2 * (m : ℝ) + 3)) * legP (m + 2) x +
          (((m : ℝ) + 1) / (2 * (m : ℝ) + 3)) * legP m x := funext hb
      rw [he]
      exact inLegSpan_add
        (inLegSpan_smul _ (inLegSpan_legP (by omega)))
        (inLegSpan_smul _ (inLegSpan_legP (by omega)))
  have hsum : ∀ k ≤ N, inLegSpan (N + 1) (fun x => ∑ n ∈ Finset.range k, c n * (x * legP n x)) := by
    intro k hk
    induction k with
    | zero => simpa using inLegSpan_zero (N + 1)
    | succ k ih =>
      simp_rw [Finset.sum_range_succ]
      exact inLegSpan_add (ih (by omega)) (hterm k (by omega))
  obtain ⟨d, hd⟩ := hsum N le_rfl
  refine ⟨d, fun x => ?_⟩
  dsimp only
  rw [hc x, Finset.mul_sum]
  simp_rw [show ∀ n, x * (c n * legP n x) = c n * (x * legP n x) by intro n; ring]
  exact hd x

theorem inLegSpan_pow (k : ℕ) : inLegSpan (k + 1) (fun x => x ^ k) := by
  induction k with
  | zero =>
    have he : (fun _ : ℝ => (1 : ℝ)) = legP 0 := funext fun x => (legP_zero x).symm
    simpa [pow_zero, he] using inLegSpan_legP (n := 0) (N := 1) (by omega)
  | succ k ih =>
    have he : (fun x : ℝ => x ^ (k + 1)) = fun x => x * x ^ k := funext fun x => by ring
    rw [he]
    exact inLegSpan_mul_id ih

theorem isPolyDeg_imp_inLegSpan {d : ℕ} {P : ℝ → ℝ} (h : isPolyDeg d P) :
    inLegSpan d P := by
  obtain ⟨a, ha⟩ := h
  have hsum : ∀ k ≤ d, inLegSpan d (fun x => ∑ j ∈ Finset.range k, a j * x ^ j) := by
    intro k hk
    induction k with
    | zero => simpa using inLegSpan_zero d
    | succ k ih =>
      simp_rw [Finset.sum_range_succ]
      exact inLegSpan_add (ih (by omega))
        (inLegSpan_smul (a k) (inLegSpan_mono (by omega) (inLegSpan_pow k)))
  obtain ⟨c, hc⟩ := hsum d le_rfl
  exact ⟨c, fun x => (ha x).trans (hc x)⟩

theorem isPolyDeg_legP (n : ℕ) : isPolyDeg (n + 1) (legP n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · exact ⟨fun _ => 1, fun x => by simp [legP_zero]⟩
    · exact ⟨fun k => if k = 1 then 1 else 0, fun x => by simp [legP_one]⟩
    · obtain ⟨a1, ha1⟩ := ih (n + 1) (by omega)
      obtain ⟨a0, ha0⟩ := ih n (by omega)
      refine ⟨fun k =>
        ((if 0 < k then (2 * (n : ℝ) + 3) * a1 (k - 1) else 0) -
          (if k < n + 1 then ((n : ℝ) + 1) * a0 k else 0)) / ((n : ℝ) + 2), fun x => ?_⟩
      dsimp only
      rw [legP_succ_succ n x, ha1 x, ha0 x]
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have h1 : (2 * (n : ℝ) + 3) * x * (∑ k ∈ Finset.range (n + 2), a1 k * x ^ k) =
          ∑ k ∈ Finset.range (n + 3),
            (if 0 < k then (2 * (n : ℝ) + 3) * a1 (k - 1) else 0) * x ^ k := by
        rw [Finset.sum_range_succ' _ (n + 2)]
        simp only [lt_self_iff_false, ↓reduceIte, zero_mul, add_zero, Nat.succ_pos',
          Nat.add_sub_cancel]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring
      have h0 : ((n : ℝ) + 1) * (∑ k ∈ Finset.range (n + 1), a0 k * x ^ k) =
          ∑ k ∈ Finset.range (n + 3),
            (if k < n + 1 then ((n : ℝ) + 1) * a0 k else 0) * x ^ k := by
        rw [Finset.sum_range_succ _ (n + 2), Finset.sum_range_succ _ (n + 1)]
        simp only [show ¬(n + 1 < n + 1) by omega, show ¬(n + 2 < n + 1) by omega,
          ↓reduceIte, zero_mul, add_zero, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k hk
        rw [if_pos (Finset.mem_range.mp hk)]; ring
      rw [h1, h0, ← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl; intro k _; ring

theorem isPolyDeg_lowProj (G : ℝ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    isPolyDeg m (lowProj G m) := by
  have hterm : ∀ n < m, isPolyDeg m (fun x => projCoeff G n * legP n x) := by
    intro n hn
    obtain ⟨a, ha⟩ := isPolyDeg_legP n
    refine ⟨fun k => if k < n + 1 then projCoeff G n * a k else 0, fun x => ?_⟩
    dsimp only
    rw [ha x, Finset.mul_sum, ← Finset.sum_subset (Finset.range_mono (by omega : n + 1 ≤ m))]
    · apply Finset.sum_congr rfl; intro k hk
      rw [if_pos (Finset.mem_range.mp hk)]; ring
    · intro k _ hkn
      rw [if_neg (by simp at hkn; omega), zero_mul]
  have hsum : ∀ r ≤ m, isPolyDeg m (fun x => ∑ n ∈ Finset.range r, projCoeff G n * legP n x) := by
    intro r hr
    induction r with
    | zero => exact ⟨fun _ => 0, fun _ => by simp⟩
    | succ r ih =>
      obtain ⟨b1, hb1⟩ := ih (by omega)
      obtain ⟨b2, hb2⟩ := hterm r (by omega)
      refine ⟨fun k => b1 k + b2 k, fun x => ?_⟩
      dsimp only
      rw [Finset.sum_range_succ, hb1 x, hb2 x, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
  exact hsum m le_rfl

/-- Iterated primitive anchored at `-1`: `iterPrim 0 f = f` and
`iterPrim (k + 1) f x = ∫ u in (-1)..x, iterPrim k f u`. -/
def iterPrim : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, x => f x
  | k + 1, f, x => ∫ u in (-1 : ℝ)..x, iterPrim k f u

theorem iterPrim_neg_one (k : ℕ) (f : ℝ → ℝ) : iterPrim (k + 1) f (-1) = 0 := by
  simp [iterPrim]

theorem hasDerivAt_iterPrim {f : ℝ → ℝ} (hf : Continuous f) :
    ∀ k : ℕ, Continuous (iterPrim k f) ∧ ∀ x, HasDerivAt (iterPrim (k + 1) f) (iterPrim k f x) x
  | 0 => ⟨hf, fun x => (hf.integral_hasStrictDerivAt (-1) x).hasDerivAt⟩
  | k + 1 =>
    let ⟨_, hd⟩ := hasDerivAt_iterPrim hf k
    have hc : Continuous (iterPrim (k + 1) f) :=
      continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
    ⟨hc, fun x => (hc.integral_hasStrictDerivAt (-1) x).hasDerivAt⟩

theorem iterPrim_linear_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∀ k x, iterPrim k (fun u => f u + g u) x = iterPrim k f x + iterPrim k g x
  | 0, _ => rfl
  | k + 1, x => by
    have hc1 := (hasDerivAt_iterPrim hf k).1
    have hc2 := (hasDerivAt_iterPrim hg k).1
    simp only [iterPrim]
    simp_rw [iterPrim_linear_add hf hg k]
    exact intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)

/-- Cauchy's repeated integral identity `(∫ u in (-1)..x, (x - u)^n * f u) = n! * iterPrim (n + 1) f x`. -/
theorem cauchy_repeated_integral {f : ℝ → ℝ} (hf : Continuous f) :
    ∀ (n : ℕ) (x : ℝ),
      (∫ u in (-1 : ℝ)..x, (x - u) ^ n * f u) = (n.factorial : ℝ) * iterPrim (n + 1) f x
  | 0, x => by simp [iterPrim]
  | n + 1, x => by
    let L := fun z : ℝ => ∫ u in (-1 : ℝ)..z, (z - u) ^ (n + 1) * f u
    let R := fun z : ℝ => ((n + 1).factorial : ℝ) * iterPrim (n + 2) f z
    have hL_eq : ∀ z : ℝ, L z = ∑ k ∈ Finset.range (n + 2),
        (((n + 1).choose k : ℝ) * z ^ k) * ∫ u in (-1 : ℝ)..z, (-u) ^ (n + 1 - k) * f u := by
      intro z
      dsimp [L]
      have hbin (u : ℝ) : (z - u) ^ (n + 1) * f u =
          ∑ k ∈ Finset.range (n + 2),
            (((n + 1).choose k : ℝ) * z ^ k) * ((-u) ^ (n + 1 - k) * f u) := by
        rw [sub_eq_add_neg, add_pow, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro k _; ring
      have hik (k : ℕ) : IntervalIntegrable
          (fun u => (((n + 1).choose k : ℝ) * z ^ k) * ((-u) ^ (n + 1 - k) * f u)) volume (-1) z :=
        ((continuous_const.mul ((continuous_neg.pow _).mul hf))).intervalIntegrable _ _
      simp_rw [hbin]
      rw [intervalIntegral.integral_finsetSum fun k _ => hik k]
      apply Finset.sum_congr rfl; intro k _
      rw [intervalIntegral.integral_const_mul]
    have hL_deriv : ∀ z : ℝ, HasDerivAt L
        (((n + 1 : ℕ) : ℝ) * ∫ u in (-1 : ℝ)..z, (z - u) ^ n * f u) z := by
      intro z
      let term := fun (k : ℕ) (w : ℝ) =>
        (((n + 1).choose k : ℝ) * w ^ k) * ∫ u in (-1 : ℝ)..w, (-u) ^ (n + 1 - k) * f u
      have ht_deriv : ∀ k ∈ Finset.range (n + 2), HasDerivAt (term k)
          ((((n + 1).choose k : ℝ) * ((k : ℝ) * z ^ (k - 1))) *
              (∫ u in (-1 : ℝ)..z, (-u) ^ (n + 1 - k) * f u) +
            (((n + 1).choose k : ℝ) * z ^ k) * ((-z) ^ (n + 1 - k) * f z)) z := by
        intro k _
        have hd1 : HasDerivAt (fun w : ℝ => ((n + 1).choose k : ℝ) * w ^ k)
            (((n + 1).choose k : ℝ) * ((k : ℝ) * z ^ (k - 1))) z :=
          (hasDerivAt_pow k z).const_mul _
        have hcont_u : Continuous (fun u : ℝ => (-u) ^ (n + 1 - k) * f u) :=
          (continuous_neg.pow _).mul hf
        have hd2 : HasDerivAt (fun w : ℝ => ∫ u in (-1 : ℝ)..w, (-u) ^ (n + 1 - k) * f u)
            ((-z) ^ (n + 1 - k) * f z) z :=
          (hcont_u.integral_hasStrictDerivAt (-1) z).hasDerivAt
        exact hd1.mul hd2
      have hsum_d := HasDerivAt.sum ht_deriv
      have hfun_eq : (∑ i ∈ Finset.range (n + 2), term i) = L :=
        funext fun w => by simp only [Finset.sum_apply, hL_eq w, term]
      rw [hfun_eq] at hsum_d
      refine hsum_d.congr_deriv ?_
      rw [Finset.sum_add_distrib]
      have hbdry : (∑ k ∈ Finset.range (n + 2),
          (((n + 1).choose k : ℝ) * z ^ k) * ((-z) ^ (n + 1 - k) * f z)) = 0 := by
        have hfac : (∑ k ∈ Finset.range (n + 2),
            (((n + 1).choose k : ℝ) * z ^ k) * ((-z) ^ (n + 1 - k) * f z)) =
            (z + -z) ^ (n + 1) * f z := by
          rw [add_pow, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro k _; ring
        rw [hfac, add_neg_cancel, zero_pow (Nat.succ_ne_zero n), zero_mul]
      rw [hbdry, add_zero]
      rw [Finset.sum_range_succ' _ (n + 1)]
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
      have hcomb : ∀ k ∈ Finset.range (n + 1),
          (((n + 1).choose (k + 1) : ℝ) * (((k + 1 : ℕ) : ℝ) * z ^ k)) =
            ((n + 1 : ℕ) : ℝ) * ((n.choose k : ℝ) * z ^ k) := by
        intro k _
        have hch : (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by
          have h := Nat.add_one_mul_choose_eq n k
          linarith
        have hchR : ((k + 1 : ℕ) : ℝ) * ((n + 1).choose (k + 1) : ℝ) =
            ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ) := by exact_mod_cast hch
        calc
          (((n + 1).choose (k + 1) : ℝ) * (((k + 1 : ℕ) : ℝ) * z ^ k))
            = (((k + 1 : ℕ) : ℝ) * ((n + 1).choose (k + 1) : ℝ)) * z ^ k := by ring
          _ = ((n + 1 : ℕ) : ℝ) * ((n.choose k : ℝ) * z ^ k) := by rw [hchR]; ring
      have hsum_rw : (∑ k ∈ Finset.range (n + 1),
          (((n + 1).choose (k + 1) : ℝ) * (((k + 1 : ℕ) : ℝ) * z ^ k)) *
            ∫ u in (-1 : ℝ)..z, (-u) ^ (n + 1 - (k + 1)) * f u) =
          ((n + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.range (n + 1),
            ((n.choose k : ℝ) * z ^ k) * ∫ u in (-1 : ℝ)..z, (-u) ^ (n - k) * f u := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k hk
        rw [hcomb k hk, show n + 1 - (k + 1) = n - k by omega]
        ring
      rw [hsum_rw]
      congr 1
      have hbin_n (u : ℝ) : (z - u) ^ n * f u =
          ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * z ^ k) * ((-u) ^ (n - k) * f u) := by
        rw [sub_eq_add_neg, add_pow, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro k _; ring
      have hik_n (k : ℕ) : IntervalIntegrable
          (fun u => ((n.choose k : ℝ) * z ^ k) * ((-u) ^ (n - k) * f u)) volume (-1) z :=
        ((continuous_const.mul ((continuous_neg.pow _).mul hf))).intervalIntegrable _ _
      simp_rw [hbin_n]
      rw [intervalIntegral.integral_finsetSum fun k _ => hik_n k]
      apply Finset.sum_congr rfl; intro k _
      rw [intervalIntegral.integral_const_mul]
    have hR_deriv : ∀ z : ℝ, HasDerivAt R
        (((n + 1 : ℕ) : ℝ) * ((n.factorial : ℝ) * iterPrim (n + 1) f z)) z := by
      intro z
      have hd := ((hasDerivAt_iterPrim hf (n + 1)).2 z).const_mul ((n + 1).factorial : ℝ)
      refine hd.congr_deriv ?_
      rw [Nat.factorial_succ]
      push_cast; ring
    have hdiff_deriv : ∀ z : ℝ, HasDerivAt (fun w => L w - R w) 0 z := by
      intro z
      have hd := (hL_deriv z).sub (hR_deriv z)
      rw [cauchy_repeated_integral hf n z, sub_self] at hd
      exact hd
    have hconst := is_const_of_deriv_eq_zero
      (fun z => (hdiff_deriv z).differentiableAt)
      (fun z => (hdiff_deriv z).deriv) x (-1)
    have h0 : L (-1) - R (-1) = 0 := by simp [L, R, iterPrim]
    linarith

theorem isPolyDeg_iterPrim {d : ℕ} (hd : 1 ≤ d) {P : ℝ → ℝ} (hP : isPolyDeg d P) :
    ∀ r : ℕ, isPolyDeg (d + r) (iterPrim r P)
  | 0 => hP
  | r + 1 => by
    obtain ⟨a, ha⟩ := isPolyDeg_iterPrim hd hP r
    refine ⟨fun k => if k = 0 then
        -(∑ j ∈ Finset.range (d + r), a j * (-1 : ℝ) ^ (j + 1) / ((j : ℝ) + 1))
      else a (k - 1) / (k : ℝ), fun x => ?_⟩
    have hij (j : ℕ) : IntervalIntegrable (fun u => a j * u ^ j) volume (-1) x :=
      (continuous_const.mul (continuous_pow j)).intervalIntegrable _ _
    simp only [iterPrim]
    simp_rw [ha]
    rw [intervalIntegral.integral_finsetSum fun j _ => hij j]
    simp_rw [intervalIntegral.integral_const_mul, integral_pow]
    rw [show d + (r + 1) = (d + r) + 1 by omega, Finset.sum_range_succ' _ (d + r)]
    simp only [↓reduceIte, pow_zero, mul_one, Nat.succ_ne_zero, Nat.add_sub_cancel]
    have hsum_eq : (∑ j ∈ Finset.range (d + r),
        a j * ((x ^ (j + 1) - (-1 : ℝ) ^ (j + 1)) / ((j : ℝ) + 1))) =
        (∑ j ∈ Finset.range (d + r), a j / ((j + 1 : ℕ) : ℝ) * x ^ (j + 1)) -
          ∑ j ∈ Finset.range (d + r), a j * (-1 : ℝ) ^ (j + 1) / ((j : ℝ) + 1) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; push_cast; ring
    rw [hsum_eq]
    ring

theorem iterPrim_one_eq_zero_of_moments_zero {R : ℝ → ℝ} (hR : Continuous R) {m : ℕ}
    (hm : ∀ n < m, regionalLegendreMoment R n = 0) :
    ∀ k : ℕ, 1 ≤ k → k ≤ m → iterPrim k R 1 = 0 := by
  intro k hk1 hkm
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn_lt : n < m := by omega
  have hcauchy := cauchy_repeated_integral hR n 1
  have hpoly : isPolyDeg (n + 1) (fun u : ℝ => (1 - u) ^ n) := by
    refine ⟨fun j => ((n.choose j : ℝ) * (-1 : ℝ) ^ j), fun u => ?_⟩
    dsimp only
    rw [sub_eq_add_neg, add_comm 1 (-u), add_pow]
    apply Finset.sum_congr rfl; intro j _; rw [neg_pow, one_pow]; ring
  obtain ⟨c, hc⟩ := isPolyDeg_imp_inLegSpan hpoly
  have hint_zero : (∫ u in (-1 : ℝ)..1, (1 - u) ^ n * R u) = 0 := by
    have hij (j : ℕ) : IntegrableOn (fun u => c j * (R u * legP j u)) (Icc (-1 : ℝ) 1) :=
      (continuous_const.mul (hR.mul (continuous_legP j))).integrableOn_Icc
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
    simp_rw [hc, Finset.sum_mul, show ∀ j u, c j * legP j u * R u = c j * (R u * legP j u) by intros; ring]
    rw [integral_finsetSum _ fun j _ => hij j]
    apply Finset.sum_eq_zero
    intro j hj
    rw [integral_const_mul]
    change c j * regionalLegendreMoment R j = 0
    rw [hm j (lt_of_lt_of_le (Finset.mem_range.mp hj) (by omega)), mul_zero]
  rw [hint_zero] at hcauchy
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  nlinarith

/-- Exact representation of positive lag moments on `[-1, 1]` via `iterPrim`. -/
theorem lag_moment_eq_iterPrim {G : ℝ → ℝ} (hG : Continuous G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) (n : ℕ) :
    (∫ t in Ioc (0 : ℝ) 2, t ^ n * autocorr G t) =
      (n.factorial : ℝ) * ∫ y in (-1 : ℝ)..1, G y * iterPrim (n + 1) G y := by
  have hvan := supported_vanish_at_aperture hG hs
  have hl (t : ℝ) : t ^ n * autocorr G t = ∫ y, G y * (t ^ n * G (y - t)) := by
    unfold autocorr
    have hshift := integral_add_right_eq_self (μ := volume) (fun y : ℝ => G (y - t) * G y) t
    dsimp only at hshift
    simp_rw [add_sub_cancel_right] at hshift
    rw [← hshift, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  simp_rw [hl]
  have hcut_y (t : ℝ) : (∫ y, G y * (t ^ n * G (y - t))) =
      ∫ y in Icc (-1 : ℝ) 1, G y * (t ^ n * G (y - t)) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hy (hs ht)), zero_mul]
  simp_rw [hcut_y]
  have hprod_int : Integrable (fun p : ℝ × ℝ => G p.2 * (p.1 ^ n * G (p.2 - p.1)))
      ((volume.restrict (Ioc (0 : ℝ) 2)).prod (volume.restrict (Icc (-1 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hc : Continuous (fun p : ℝ × ℝ => G p.2 * (p.1 ^ n * G (p.2 - p.1))) := by fun_prop
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) |>.mono_set
      (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)
  rw [integral_integral_swap hprod_int]
  have hinner : ∀ y ∈ Icc (-1 : ℝ) 1,
      (∫ t in Ioc (0 : ℝ) 2, G y * (t ^ n * G (y - t))) =
        G y * ((n.factorial : ℝ) * iterPrim (n + 1) G y) := by
    intro y hy
    rw [integral_const_mul]
    congr 1
    have hy0 : 0 ≤ y + 1 := by linarith [hy.1]
    have hy2 : y + 1 ≤ 2 := by linarith [hy.2]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (a := (0 : ℝ)) (b := y + 1) (c := 2)
      (((continuous_pow n).mul (hG.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _)
      (((continuous_pow n).mul (hG.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _)
    have htail_zero : (∫ t in (y + 1)..2, t ^ n * G (y - t)) = 0 := by
      rw [intervalIntegral.integral_of_le hy2]
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      have ht_gt : y + 1 < t := ht.1
      rw [hvan (y - t) (by rw [abs_of_neg (by linarith)]; linarith), mul_zero]
    rw [htail_zero, add_zero] at hsplit
    rw [← hsplit]
    have hsub' : (∫ t in (0 : ℝ)..(y + 1), (y - (y - t)) ^ n * G (y - t)) =
        ∫ u in (-1 : ℝ)..y, (y - u) ^ n * G u := by
      rw [intervalIntegral.integral_comp_sub_left (fun u => (y - u) ^ n * G u) y,
        sub_zero, show y - (y + 1) = -1 by ring, intervalIntegral.integral_symm, neg_neg]
    simp_rw [sub_sub_cancel] at hsub'
    rw [hsub', cauchy_repeated_integral hG n y]
  rw [setIntegral_congr_fun measurableSet_Icc hinner,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [show ∀ y, G y * ((n.factorial : ℝ) * iterPrim (n + 1) G y) =
    (n.factorial : ℝ) * (G y * iterPrim (n + 1) G y) by intro y; ring]
  rw [intervalIntegral.integral_const_mul]

private theorem ibp_iterPrim_step {A B : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B)
    (a b : ℕ) (hB1 : iterPrim (b + 1) B 1 = 0) :
    (∫ y in (-1 : ℝ)..1, iterPrim a A y * iterPrim (b + 1) B y) =
      -∫ y in (-1 : ℝ)..1, iterPrim (a + 1) A y * iterPrim b B y := by
  obtain ⟨hcA, hdA⟩ := hasDerivAt_iterPrim hA a
  obtain ⟨hcB, hdB⟩ := hasDerivAt_iterPrim hB b
  have hcA1 := (hasDerivAt_iterPrim hA (a + 1)).1
  have hcB1 := (hasDerivAt_iterPrim hB (b + 1)).1
  have hprod : ∀ y ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun z => iterPrim (a + 1) A z * iterPrim (b + 1) B z)
        (iterPrim a A y * iterPrim (b + 1) B y + iterPrim (a + 1) A y * iterPrim b B y) y :=
    fun y _ => (hdA y).mul (hdB y)
  have i1 : IntervalIntegrable (fun y => iterPrim a A y * iterPrim (b + 1) B y) volume (-1) 1 :=
    (hcA.mul hcB1).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun y => iterPrim (a + 1) A y * iterPrim b B y) volume (-1) 1 :=
    (hcA1.mul hcB).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod (i1.add i2)
  rw [hB1, mul_zero, iterPrim_neg_one, zero_mul, sub_zero,
    intervalIntegral.integral_add i1 i2] at hftc
  linarith

/-- Decomposition of odd lag moments across `G = lowProj G m + R` on `[-1, 1]` when `2q + 2 ≤ m`. -/
theorem odd_lag_moment_lowProj_decomp {G : ℝ → ℝ} (hG : Continuous G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) {m q : ℕ} (hqm : 2 * q + 2 ≤ m) :
    let P := lowProj G m
    let R := fun x => G x - P x
    (∫ t in Ioc (0 : ℝ) 2, t ^ (2 * q + 1) * autocorr G t) =
      ((2 * q + 1).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, P y * iterPrim (2 * q + 2) P y) +
        2 * ((2 * q + 1).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, R y * iterPrim (2 * q + 2) P y) +
        (-1 : ℝ) ^ (q + 1) * ((2 * q + 1).factorial : ℝ) *
          (∫ y in (-1 : ℝ)..1, iterPrim (q + 1) R y ^ 2) := by
  intro P R
  have hP : Continuous P := (contDiff_lowProj G m (k := 0)).continuous
  have hR : Continuous R := hG.sub hP
  have hR_zero : ∀ k, 1 ≤ k → k ≤ m → iterPrim k R 1 = 0 :=
    iterPrim_one_eq_zero_of_moments_zero hR (fun n hn => sub_lowProj_moment_lt hG hn)
  have hG_eq : G = fun u => P u + R u := funext fun u => by dsimp [R]; ring
  rw [lag_moment_eq_iterPrim hG hs (2 * q + 1)]
  have hlin : ∀ y, iterPrim (2 * q + 2) G y =
      iterPrim (2 * q + 2) P y + iterPrim (2 * q + 2) R y := by
    intro y
    conv_lhs => rw [hG_eq]
    exact iterPrim_linear_add hP hR (2 * q + 2) y
  simp_rw [hlin]
  have hcIP := (hasDerivAt_iterPrim hP (2 * q + 2)).1
  have hcIR := (hasDerivAt_iterPrim hR (2 * q + 2)).1
  have hexpand : (∫ y in (-1 : ℝ)..1, G y * (iterPrim (2 * q + 2) P y + iterPrim (2 * q + 2) R y)) =
      (∫ y in (-1 : ℝ)..1, P y * iterPrim (2 * q + 2) P y) +
        (∫ y in (-1 : ℝ)..1, R y * iterPrim (2 * q + 2) P y) +
        (∫ y in (-1 : ℝ)..1, P y * iterPrim (2 * q + 2) R y) +
        (∫ y in (-1 : ℝ)..1, R y * iterPrim (2 * q + 2) R y) := by
    have hfn : ∀ y, G y * (iterPrim (2 * q + 2) P y + iterPrim (2 * q + 2) R y) =
        ((P y * iterPrim (2 * q + 2) P y + R y * iterPrim (2 * q + 2) P y) +
          P y * iterPrim (2 * q + 2) R y) + R y * iterPrim (2 * q + 2) R y := by
      intro y; dsimp [R]; ring
    simp_rw [hfn]
    have i1 : IntervalIntegrable (fun y => P y * iterPrim (2 * q + 2) P y) volume (-1) 1 :=
      (hP.mul hcIP).intervalIntegrable (-1) 1
    have i2 : IntervalIntegrable (fun y => R y * iterPrim (2 * q + 2) P y) volume (-1) 1 :=
      (hR.mul hcIP).intervalIntegrable (-1) 1
    have i3 : IntervalIntegrable (fun y => P y * iterPrim (2 * q + 2) R y) volume (-1) 1 :=
      (hP.mul hcIR).intervalIntegrable (-1) 1
    have i4 : IntervalIntegrable (fun y => R y * iterPrim (2 * q + 2) R y) volume (-1) 1 :=
      (hR.mul hcIR).intervalIntegrable (-1) 1
    rw [intervalIntegral.integral_add ((i1.add i2).add i3) i4,
      intervalIntegral.integral_add (i1.add i2) i3,
      intervalIntegral.integral_add i1 i2]
  rw [hexpand]
  have hibp_PR : ∀ s ≤ 2 * q + 2,
      (∫ y in (-1 : ℝ)..1, P y * iterPrim (2 * q + 2) R y) =
        (-1 : ℝ) ^ s * ∫ y in (-1 : ℝ)..1, iterPrim s P y * iterPrim (2 * q + 2 - s) R y := by
    intro s hs_le
    induction s with
    | zero => simp [iterPrim]
    | succ s ih =>
      rw [ih (by omega)]
      have hsub : 2 * q + 2 - s = (2 * q + 2 - (s + 1)) + 1 := by omega
      rw [hsub, ibp_iterPrim_step hP hR s (2 * q + 2 - (s + 1))
        (hR_zero _ (by omega) (by omega)), pow_succ]
      ring
  have hPR := hibp_PR (2 * q + 2) le_rfl
  have hsign_ev : (-1 : ℝ) ^ (2 * q + 2) = 1 := by
    rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [Nat.sub_self, hsign_ev, one_mul] at hPR
  change (∫ y in (-1 : ℝ)..1, P y * iterPrim (2 * q + 2) R y) =
    ∫ y in (-1 : ℝ)..1, iterPrim (2 * q + 2) P y * R y at hPR
  have hPR' : (∫ y in (-1 : ℝ)..1, P y * iterPrim (2 * q + 2) R y) =
      ∫ y in (-1 : ℝ)..1, R y * iterPrim (2 * q + 2) P y := by
    rw [hPR]; exact intervalIntegral.integral_congr fun y _ => mul_comm _ _
  have hibp_RR : ∀ s ≤ q + 1,
      (∫ y in (-1 : ℝ)..1, R y * iterPrim (2 * q + 2) R y) =
        (-1 : ℝ) ^ s * ∫ y in (-1 : ℝ)..1, iterPrim s R y * iterPrim (2 * q + 2 - s) R y := by
    intro s hs_le
    induction s with
    | zero => simp [iterPrim]
    | succ s ih =>
      rw [ih (by omega)]
      have hsub : 2 * q + 2 - s = (2 * q + 2 - (s + 1)) + 1 := by omega
      rw [hsub, ibp_iterPrim_step hR hR s (2 * q + 2 - (s + 1))
        (hR_zero _ (by omega) (by omega)), pow_succ]
      ring
  have hRR := hibp_RR (q + 1) le_rfl
  rw [show 2 * q + 2 - (q + 1) = q + 1 by omega] at hRR
  simp_rw [← pow_two] at hRR
  rw [hPR', hRR]
  ring

/-- Iterated Dirichlet–Wirtinger inequality on `[-1, 1]` for residual primitives vanishing at `±1`. -/
theorem iterPrim_sq_le_wirtinger {R : ℝ → ℝ} (hR : Continuous R) {m : ℕ}
    (hm : ∀ n < m, regionalLegendreMoment R n = 0) :
    ∀ k : ℕ, k ≤ m →
      (∫ y in (-1 : ℝ)..1, iterPrim k R y ^ 2) ≤
        (4 / Real.pi ^ 2) ^ k * ∫ y in Icc (-1 : ℝ) 1, R y ^ 2 := by
  intro k hk
  induction k with
  | zero =>
    simp only [iterPrim, pow_zero, one_mul,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc, le_rfl]
  | succ k ih =>
    obtain ⟨hc, hd⟩ := hasDerivAt_iterPrim hR k
    let fC : ℝ → ℂ := fun y => (iterPrim (k + 1) R y : ℂ)
    let fC' : ℝ → ℂ := fun y => (iterPrim k R y : ℂ)
    have hdw := HTGeometry.dirichlet_wirtinger_intervalIntegral
      (a := (-1 : ℝ)) (b := 1) (by norm_num) (f := fC) (f' := fC')
      (fun y _ => (hd y).ofReal_comp)
      (Complex.continuous_ofReal.comp hc).continuousOn
      (by simp [fC, iterPrim_neg_one])
      (by simp [fC, iterPrim_one_eq_zero_of_moments_zero hR hm (k + 1) (by omega) hk])
    have hn1 (y : ℝ) : ‖fC y‖ ^ 2 = iterPrim (k + 1) R y ^ 2 := by
      simp [fC, Complex.norm_real, sq_abs]
    have hn2 (y : ℝ) : ‖fC' y‖ ^ 2 = iterPrim k R y ^ 2 := by
      simp [fC', Complex.norm_real, sq_abs]
    simp_rw [hn1, hn2] at hdw
    have hscale : ((1 - (-1 : ℝ)) / Real.pi) ^ 2 = 4 / Real.pi ^ 2 := by ring
    rw [hscale] at hdw
    have hprev := ih (by omega)
    have hpos : 0 ≤ 4 / Real.pi ^ 2 := by positivity
    calc
      (∫ y in (-1 : ℝ)..1, iterPrim (k + 1) R y ^ 2)
        ≤ (4 / Real.pi ^ 2) * ∫ y in (-1 : ℝ)..1, iterPrim k R y ^ 2 := hdw
      _ ≤ (4 / Real.pi ^ 2) * ((4 / Real.pi ^ 2) ^ k * ∫ y in Icc (-1 : ℝ) 1, R y ^ 2) :=
          mul_le_mul_of_nonneg_left hprev hpos
      _ = (4 / Real.pi ^ 2) ^ (k + 1) * ∫ y in Icc (-1 : ℝ) 1, R y ^ 2 := by ring

private theorem weighted_cauchy_schwarz_finset {ι : Type*} (s : Finset ι)
    (w a b : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * a i * b i) ^ 2 ≤
      (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) := by
  have hid : 2 * ((∑ i ∈ s, w i * a i ^ 2) * (∑ j ∈ s, w j * b j ^ 2) -
      (∑ i ∈ s, w i * a i * b i) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2 := by
    have hdiff : ∀ i j, w i * w j * (a i * b j - a j * b i) ^ 2 =
        (w i * a i ^ 2) * (w j * b j ^ 2) + (w j * a j ^ 2) * (w i * b i ^ 2) -
          2 * (w i * a i * b i) * (w j * a j * b j) := fun i j => by ring
    simp_rw [hdiff, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h1 : (∑ i ∈ s, ∑ j ∈ s, (w i * a i ^ 2) * (w j * b j ^ 2)) =
        (∑ i ∈ s, w i * a i ^ 2) * (∑ j ∈ s, w j * b j ^ 2) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    have h2 : (∑ i ∈ s, ∑ j ∈ s, (w j * a j ^ 2) * (w i * b i ^ 2)) =
        (∑ j ∈ s, w j * a j ^ 2) * (∑ i ∈ s, w i * b i ^ 2) := by
      rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    have h3 : (∑ i ∈ s, ∑ j ∈ s, 2 * (w i * a i * b i) * (w j * a j * b j)) =
        2 * (∑ i ∈ s, w i * a i * b i) ^ 2 := by
      rw [pow_two, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [h1, h2, h3]; ring
  have hnn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2 :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)
  linarith

/-- Bessel–Cauchy–Schwarz bound for the finite spillover cross term `∫_{-1}^1 R * iterPrim (2q+2) P`:
works identically for `m = 23` (odd `G`) and `m = 24` (even `G`) whenever opposite-parity moments
`m + (2r + 1)` of `G` vanish. -/
theorem high_mode_cross_sq_le {G : ℝ → ℝ} (hG : Continuous G)
    {m q : ℕ} (hm1 : 1 ≤ m)
    (hopp : ∀ r, regionalLegendreMoment G (m + (2 * r + 1)) = 0) :
    let P := lowProj G m
    let R := fun x => G x - P x
    (∫ y in (-1 : ℝ)..1, R y * iterPrim (2 * q + 2) P y) ^ 2 ≤
      (∑ r ∈ Finset.range (q + 1), ((2 * ↑(m + 2 * r) + 1) / 2) *
          regionalLegendreMoment (iterPrim (2 * q + 2) P) (m + 2 * r) ^ 2) *
        (∫ y in Icc (-1 : ℝ) 1, R y ^ 2) := by
  intro P R
  have hP : Continuous P := (contDiff_lowProj G m (k := 0)).continuous
  have hR : Continuous R := hG.sub hP
  let H := iterPrim (2 * q + 2) P
  have hH_poly : isPolyDeg (m + (2 * q + 2)) H :=
    isPolyDeg_iterPrim hm1 (isPolyDeg_lowProj G hm1) (2 * q + 2)
  obtain ⟨c, hc⟩ := isPolyDeg_imp_inLegSpan hH_poly
  have hc_val : ∀ n < m + (2 * q + 2), c n = ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment H n := by
    intro n hn
    have hmom : regionalLegendreMoment H n =
        regionalLegendreMoment (regionalLegendreSum (Finset.range (m + (2 * q + 2))) c) n := by
      unfold regionalLegendreMoment regionalLegendreSum
      simp_rw [hc]
    rw [hmom, regionalLegendreMoment_sum, if_pos (Finset.mem_range.mpr hn)]
    field_simp [show (2 * (n : ℝ) + 1) ≠ 0 by positivity]
  have hint : (∫ y in (-1 : ℝ)..1, R y * H y) =
      ∑ r ∈ Finset.range (q + 1),
        ((2 * ↑(m + 2 * r) + 1) / 2) * regionalLegendreMoment H (m + 2 * r) *
          regionalLegendreMoment R (m + 2 * r) := by
    have hin (n : ℕ) : IntegrableOn (fun y => c n * (R y * legP n y)) (Icc (-1 : ℝ) 1) :=
      (continuous_const.mul (hR.mul (continuous_legP n))).integrableOn_Icc
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
    simp_rw [hc, Finset.mul_sum, show ∀ n y, R y * (c n * legP n y) = c n * (R y * legP n y) by intros; ring]
    rw [integral_finsetSum _ fun n _ => hin n]
    simp_rw [integral_const_mul]
    change (∑ n ∈ Finset.range (m + (2 * q + 2)), c n * regionalLegendreMoment R n) = _
    rw [Finset.sum_range_add]
    have hlow : (∑ n ∈ Finset.range m, c n * regionalLegendreMoment R n) = 0 :=
      Finset.sum_eq_zero fun n hn => by
        rw [sub_lowProj_moment_lt hG (Finset.mem_range.mp hn), mul_zero]
    rw [hlow, zero_add]
    have hsplit2 : 2 * q + 2 = 2 * q + 1 + 1 := rfl
    rw [hsplit2, Finset.sum_range_succ, sum_range_even_odd_split]
    have hlast : c (m + (2 * q + 1)) * regionalLegendreMoment R (m + (2 * q + 1)) = 0 := by
      rw [sub_lowProj_moment_ge hG (by omega), hopp q, mul_zero]
    have hodd_sum : (∑ r ∈ Finset.range q,
        c (m + (2 * r + 1)) * regionalLegendreMoment R (m + (2 * r + 1))) = 0 :=
      Finset.sum_eq_zero fun r _ => by
        rw [sub_lowProj_moment_ge hG (by omega), hopp r, mul_zero]
    rw [hlast, hodd_sum, add_zero, add_zero]
    apply Finset.sum_congr rfl; intro r hr
    have hr_le : r ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [hc_val (m + 2 * r) (by omega)]
  rw [hint]
  have hcs := weighted_cauchy_schwarz_finset (Finset.range (q + 1))
    (fun r => (2 * ↑(m + 2 * r) + 1) / 2)
    (fun r => regionalLegendreMoment H (m + 2 * r))
    (fun r => regionalLegendreMoment R (m + 2 * r))
    (fun r _ => by positivity)
  have hbessel : (∑ r ∈ Finset.range (q + 1),
      ((2 * ↑(m + 2 * r) + 1) / 2) * regionalLegendreMoment R (m + 2 * r) ^ 2) ≤
      ∫ y in Icc (-1 : ℝ) 1, R y ^ 2 := by
    have hinj : (∑ r ∈ Finset.range (q + 1),
        ((2 * ↑(m + 2 * r) + 1) / 2) * regionalLegendreMoment R (m + 2 * r) ^ 2) ≤
        ∑ n ∈ Finset.range (m + 2 * q + 2),
          ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment R n ^ 2 := by
      let emb : ℕ ↪ ℕ := ⟨fun r => m + 2 * r, fun a b h => by dsimp at h; omega⟩
      have hmap : (∑ r ∈ Finset.range (q + 1),
          ((2 * ↑(m + 2 * r) + 1) / 2) * regionalLegendreMoment R (m + 2 * r) ^ 2) =
          ∑ n ∈ (Finset.range (q + 1)).map emb,
            ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment R n ^ 2 := by
        rw [Finset.sum_map]
        rfl
      rw [hmap]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ =>
        mul_nonneg (by positivity) (sq_nonneg _)
      intro n hn
      rcases Finset.mem_map.mp hn with ⟨r, hr, rfl⟩
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; dsimp [emb]; omega)
    exact hinj.trans (regionalMass_ge_low_moments hR (m + 2 * q + 2))
  exact hcs.trans (mul_le_mul_of_nonneg_left hbessel
    (Finset.sum_nonneg fun r _ => mul_nonneg (by positivity) (sq_nonneg _)))

/-! ### 6. Hyperbolic pole Taylor bounds on `[0, 1]` -/

private theorem exp_even_odd_sum (z : ℝ) :
    ∀ M : ℕ,
      (∑ m ∈ Finset.range (2 * M), z ^ m / (m.factorial : ℝ)) +
          (∑ m ∈ Finset.range (2 * M), (-z) ^ m / (m.factorial : ℝ)) =
        2 * ∑ j ∈ Finset.range M, z ^ (2 * j) / ((2 * j).factorial : ℝ) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ (f := fun j => z ^ (2 * j) / ((2 * j).factorial : ℝ))]
    have hev : (-z) ^ (2 * M) = z ^ (2 * M) := by rw [pow_mul, neg_sq, ← pow_mul]
    have hodd : (-z) ^ (2 * M + 1) = -(z ^ (2 * M + 1)) := by
      rw [pow_succ, hev]; ring
    rw [hev, hodd, neg_div]
    linarith [ih]

private theorem exp_odd_diff_sum (z : ℝ) :
    ∀ M : ℕ,
      (∑ m ∈ Finset.range (2 * M + 1), z ^ m / (m.factorial : ℝ)) -
          (∑ m ∈ Finset.range (2 * M + 1), (-z) ^ m / (m.factorial : ℝ)) =
        2 * ∑ j ∈ Finset.range M, z ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show 2 * (M + 1) + 1 = (2 * M + 1) + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ]
    have hev : (-z) ^ ((2 * M + 1) + 1) = z ^ ((2 * M + 1) + 1) := by
      rw [show (2 * M + 1) + 1 = 2 * (M + 1) by omega, pow_mul, neg_sq, ← pow_mul]
    have hodd : (-z) ^ (2 * M + 1) = -(z ^ (2 * M + 1)) := by
      rw [pow_succ, pow_mul, neg_sq, ← pow_mul]; ring
    rw [hev, hodd, neg_div]
    linarith [ih]

private theorem abs_pow_sub_le_half {z z0 : ℝ} (hz : z ∈ Icc (0 : ℝ) (1 / 2))
    (hz0 : z0 ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ m : ℕ, |z ^ (m + 1) - z0 ^ (m + 1)| ≤ ((m + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ m * |z - z0| := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hid : z ^ (m + 2) - z0 ^ (m + 2) =
        z * (z ^ (m + 1) - z0 ^ (m + 1)) + (z - z0) * z0 ^ (m + 1) := by ring
    rw [hid]
    have h1 : |z * (z ^ (m + 1) - z0 ^ (m + 1))| ≤
        (1 / 2 : ℝ) * (((m + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ m * |z - z0|) := by
      rw [abs_mul, abs_of_nonneg hz.1]
      exact mul_le_mul hz.2 ih (abs_nonneg _) (by norm_num)
    have h2 : |(z - z0) * z0 ^ (m + 1)| ≤ |z - z0| * (1 / 2 : ℝ) ^ (m + 1) := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hz0.1 _)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0.1 hz0.2 _) (abs_nonneg _)
    have htri := abs_add_le (z * (z ^ (m + 1) - z0 ^ (m + 1))) ((z - z0) * z0 ^ (m + 1))
    push_cast at h1 ⊢
    calc
      |z * (z ^ (m + 1) - z0 ^ (m + 1)) + (z - z0) * z0 ^ (m + 1)|
        ≤ (1 / 2 : ℝ) * (((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m * |z - z0|) +
            |z - z0| * (1 / 2 : ℝ) ^ (m + 1) := htri.trans (add_le_add h1 h2)
      _ = ((m : ℝ) + 1 + 1) * (1 / 2 : ℝ) ^ (m + 1) * |z - z0| := by ring

private theorem interval_cauchy_schwarz_unit {G E : ℝ → ℝ} (hG : Continuous G) (hE : Continuous E)
    {ε : ℝ} (hε : 0 ≤ ε) (hb : ∀ u ∈ Icc (0 : ℝ) 1, |E u| ≤ ε) :
    (∫ u in (0 : ℝ)..1, G u * E u) ^ 2 ≤ ε ^ 2 * ∫ u in (0 : ℝ)..1, G u ^ 2 := by
  by_cases hε0 : ε = 0
  · subst hε0
    have hz : ∀ u ∈ uIcc (0 : ℝ) 1, G u * E u = 0 := by
      intro u hu
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      rw [abs_nonpos_iff.mp (hb u hu), mul_zero]
    rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
    norm_num
  · have hε_pos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hε0)
    have hquad : ∀ s : ℝ, 0 ≤ ∫ u in (0 : ℝ)..1, (E u - s * G u) ^ 2 := by
      intro s
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact setIntegral_nonneg measurableSet_Ioc fun u _ => sq_nonneg _
    have hE2 : (∫ u in (0 : ℝ)..1, E u ^ 2) ≤ ε ^ 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      calc
        (∫ u in Ioc (0 : ℝ) 1, E u ^ 2)
          ≤ ∫ _ in Ioc (0 : ℝ) 1, ε ^ 2 := by
            refine setIntegral_mono_on ((hE.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
              (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
              measurableSet_Ioc fun u hu => ?_
            have h := pow_le_pow_left₀ (abs_nonneg _) (hb u ⟨hu.1.le, hu.2⟩) 2
            simpa only [sq_abs] using h
        _ = ε ^ 2 := by simp [Measure.real, Real.volume_Ioc]
    set IGE := ∫ u in (0 : ℝ)..1, G u * E u
    set IGG := ∫ u in (0 : ℝ)..1, G u ^ 2
    have hexp : ∀ s : ℝ, (∫ u in (0 : ℝ)..1, (E u - s * G u) ^ 2) =
        (∫ u in (0 : ℝ)..1, E u ^ 2) - 2 * s * IGE + s ^ 2 * IGG := by
      intro s
      have hfn : (fun u => (E u - s * G u) ^ 2) =
          fun u => (E u ^ 2 - (2 * s) * (G u * E u)) + s ^ 2 * G u ^ 2 := funext fun u => by ring
      simp_rw [hfn]
      have i1 : IntervalIntegrable (fun u => E u ^ 2) volume 0 1 := (hE.pow 2).intervalIntegrable 0 1
      have i2 : IntervalIntegrable (fun u => (2 * s) * (G u * E u)) volume 0 1 :=
        ((hG.mul hE).const_mul (2 * s)).intervalIntegrable 0 1
      have i3 : IntervalIntegrable (fun u => s ^ 2 * G u ^ 2) volume 0 1 :=
        ((hG.pow 2).const_mul (s ^ 2)).intervalIntegrable 0 1
      rw [intervalIntegral.integral_add (i1.sub i2) i3,
        intervalIntegral.integral_sub i1 i2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    by_cases hIGG : IGG = 0
    · by_contra hlt
      push Not at hlt
      have hne : IGE ≠ 0 := fun h0 => by rw [h0, hIGG] at hlt; norm_num at hlt
      have hq := hquad (((∫ u in (0 : ℝ)..1, E u ^ 2) + 1) / (2 * IGE))
      rw [hexp, hIGG, mul_zero, add_zero] at hq
      have hsimp : 2 * (((∫ u in (0 : ℝ)..1, E u ^ 2) + 1) / (2 * IGE)) * IGE =
          (∫ u in (0 : ℝ)..1, E u ^ 2) + 1 := by field_simp [hne]
      rw [hsimp] at hq
      linarith
    · have hIGG_nn : 0 ≤ IGG := by
        dsimp [IGG]
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact setIntegral_nonneg measurableSet_Ioc fun u _ => sq_nonneg _
      have hIGG_pos : 0 < IGG := lt_of_le_of_ne hIGG_nn (Ne.symm hIGG)
      have hq := hquad (IGE / IGG)
      rw [hexp] at hq
      have hmul := mul_le_mul_of_nonneg_right hq hIGG_pos.le
      have halg : ((∫ u in (0 : ℝ)..1, E u ^ 2) - 2 * (IGE / IGG) * IGE + (IGE / IGG) ^ 2 * IGG) * IGG =
          (∫ u in (0 : ℝ)..1, E u ^ 2) * IGG - IGE ^ 2 := by field_simp [hIGG]; ring
      rw [halg, zero_mul] at hmul
      nlinarith [mul_le_mul_of_nonneg_right hE2 hIGG_pos.le]

/-- Degree-22 even Taylor polynomial for `cosh (A0 * u / 2)`. -/
def evenPolePoly (A0 u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 12, (A0 * u / 2) ^ (2 * j) / ((2 * j).factorial : ℝ)

/-- Degree-21 odd Taylor polynomial for `sinh (A0 * u / 2)`. -/
def oddPolePoly (A0 u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 11, (A0 * u / 2) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)

theorem even_cosh_pole_ge {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (he : ∀ x, F (-x) = F x) {A0 : ℝ}
    (hA0_pos : 0 ≤ A0) (hA0_hi : A0 ≤ 4 / 5)
    (hdA : |apertureLogTwo - A0| ≤ 2 / 10 ^ 25) :
    let G := dilateLogTwo F;
    4 * logTwoLo * (1 - 1 / 10 ^ 20) * (∫ u in (0 : ℝ)..1, G u * evenPolePoly A0 u) ^ 2 -
      (1 / 10 ^ 24) * (∫ u in (0 : ℝ)..1, G u ^ 2) ≤
      (coshPairing F ^ 2 / 2) / (2 * apertureLogTwo) := by
  intro G
  have hG : Continuous G := hF.comp (continuous_const.mul continuous_id)
  have hGe : ∀ u, G (-u) = G u := fun u => by unfold G dilateLogTwo; rw [mul_neg, he]
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  have hA_pos := apertureLogTwo_pos
  have hpair : coshPairing F = 4 * apertureLogTwo * ∫ u in (0 : ℝ)..1, G u * Real.cosh (apertureLogTwo * u / 2) := by
    unfold coshPairing
    have hscale := Measure.integral_comp_mul_left (fun x => 2 * Real.cosh (x / 2) * F x) apertureLogTwo
    rw [abs_of_pos (inv_pos.mpr hA_pos), smul_eq_mul] at hscale
    have hcut : (∫ u in Icc (-1 : ℝ) 1, 2 * Real.cosh (apertureLogTwo * u / 2) * G u) =
        ∫ u, 2 * Real.cosh (apertureLogTwo * u / 2) * G u :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
        dsimp [G]
        rw [dilateLogTwo_outside hs hu, mul_zero]
    have hev := even_integral_Icc_unit
      (H := fun u => 2 * Real.cosh (apertureLogTwo * u / 2) * G u)
      (by fun_prop)
      fun u => by rw [mul_neg, neg_div, Real.cosh_neg, hGe]
    rw [hcut] at hev
    change (∫ u, 2 * Real.cosh (apertureLogTwo * u / 2) * G u) =
      apertureLogTwo⁻¹ * ∫ x, 2 * Real.cosh (x / 2) * F x at hscale
    have h2int : (∫ u in (0 : ℝ)..1, 2 * Real.cosh (apertureLogTwo * u / 2) * G u) =
        2 * ∫ u in (0 : ℝ)..1, G u * Real.cosh (apertureLogTwo * u / 2) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun u _ => by ring
    rw [h2int] at hev
    field_simp [hA_pos.ne'] at hscale
    linarith
  have hquot : (coshPairing F ^ 2 / 2) / (2 * apertureLogTwo) =
      4 * apertureLogTwo * (∫ u in (0 : ℝ)..1, G u * Real.cosh (apertureLogTwo * u / 2)) ^ 2 := by
    rw [hpair]; field_simp [hA_pos.ne']; ring
  rw [hquot]
  set P_true := ∫ u in (0 : ℝ)..1, G u * Real.cosh (apertureLogTwo * u / 2)
  set P_0 := ∫ u in (0 : ℝ)..1, G u * evenPolePoly A0 u
  have herr_pt : ∀ u ∈ Icc (0 : ℝ) 1,
      |Real.cosh (apertureLogTwo * u / 2) - evenPolePoly A0 u| ≤ 3 / 10 ^ 25 := by
    intro u hu
    set z := apertureLogTwo * u / 2
    set z0 := A0 * u / 2
    have hz_mem : z ∈ Icc (0 : ℝ) (1 / 2) := by
      have hAu : apertureLogTwo ≤ 7 / 10 := by
        unfold apertureLogTwo; norm_num [logTwoHi] at h2u; linarith
      refine ⟨div_nonneg (mul_nonneg hA_pos.le hu.1) (by norm_num), ?_⟩
      dsimp [z]; nlinarith [hu.2, hA_pos, hAu]
    have hz0_mem : z0 ∈ Icc (0 : ℝ) (1 / 2) := by
      refine ⟨div_nonneg (mul_nonneg hA0_pos hu.1) (by norm_num), ?_⟩
      dsimp [z0]; nlinarith [hu.2, hA0_pos, hA0_hi]
    have hz1 : |z| ≤ 1 := by rw [abs_of_nonneg hz_mem.1]; linarith [hz_mem.2]
    have hnz1 : |-z| ≤ 1 := by simpa only [abs_neg] using hz1
    have hp := Real.exp_bound hz1 (n := 24) (by norm_num)
    have hm := Real.exp_bound hnz1 (n := 24) (by norm_num)
    have hcosh_trunc : |Real.cosh z - evenPolePoly apertureLogTwo u| ≤ 1 / 10 ^ 26 := by
      have heq_sum := exp_even_odd_sum z 12
      unfold evenPolePoly
      change |Real.cosh z - ∑ j ∈ Finset.range 12, z ^ (2 * j) / ((2 * j).factorial : ℝ)| ≤ _
      rw [Real.cosh_eq]
      have hdiff : (Real.exp z + Real.exp (-z)) / 2 -
          (∑ j ∈ Finset.range 12, z ^ (2 * j) / ((2 * j).factorial : ℝ)) =
          ((Real.exp z - ∑ m ∈ Finset.range 24, z ^ m / (m.factorial : ℝ)) +
            (Real.exp (-z) - ∑ m ∈ Finset.range 24, (-z) ^ m / (m.factorial : ℝ))) / 2 := by
        linarith [heq_sum]
      rw [hdiff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have htri := (abs_add_le _ _).trans (add_le_add hp hm)
      rw [abs_neg, abs_of_nonneg hz_mem.1] at htri
      have hz24 : z ^ 24 ≤ (1 / 2 : ℝ) ^ 24 := pow_le_pow_left₀ hz_mem.1 hz_mem.2 24
      have hnum : (1 / 2 : ℝ) ^ 24 * ((24 : ℝ) + 1) / ((24 : ℕ).factorial * (24 : ℝ)) ≤ 1 / 10 ^ 26 := by
        norm_num [Nat.factorial]
      nlinarith
    have hshift : |evenPolePoly apertureLogTwo u - evenPolePoly A0 u| ≤ 2 / 10 ^ 25 := by
      unfold evenPolePoly
      change |(∑ j ∈ Finset.range 12, z ^ (2 * j) / ((2 * j).factorial : ℝ)) -
        ∑ j ∈ Finset.range 12, z0 ^ (2 * j) / ((2 * j).factorial : ℝ)| ≤ _
      rw [← Finset.sum_sub_distrib, Finset.sum_range_succ' _ 11]
      simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, sub_self, add_zero]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ k ∈ Finset.range 11,
          |z ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ) -
            z0 ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ)| ≤
          ((2 * (k + 1) : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (2 * k + 1) / ((2 * (k + 1)).factorial : ℝ) * |z - z0| := by
        intro k _
        have hpos_f : (0 : ℝ) < ((2 * (k + 1)).factorial : ℝ) :=
          Nat.cast_pos.mpr (Nat.factorial_pos _)
        rw [← sub_div, abs_div, abs_of_pos hpos_f]
        have hp_sub := abs_pow_sub_le_half hz_mem hz0_mem (2 * k + 1)
        have hdiv := div_le_div_of_nonneg_right hp_sub hpos_f.le
        rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega] at hdiv
        refine hdiv.trans (le_of_eq ?_)
        push_cast; ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have hsum_num : (∑ k ∈ Finset.range 11,
          ((2 * (k + 1) : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (2 * k + 1) / ((2 * (k + 1)).factorial : ℝ)) ≤ 2 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      have hdz : |z - z0| ≤ 1 / 10 ^ 25 := by
        have : z - z0 = (apertureLogTwo - A0) * (u / 2) := by dsimp [z, z0]; ring
        rw [this, abs_mul, abs_of_nonneg (div_nonneg hu.1 (by norm_num))]
        have hu2 : u / 2 ≤ 1 / 2 := by linarith [hu.2]
        nlinarith [abs_nonneg (apertureLogTwo - A0)]
      nlinarith [abs_nonneg (z - z0)]
    calc
      |Real.cosh z - evenPolePoly A0 u|
        = |(Real.cosh z - evenPolePoly apertureLogTwo u) + (evenPolePoly apertureLogTwo u - evenPolePoly A0 u)| := by ring_nf
      _ ≤ |Real.cosh z - evenPolePoly apertureLogTwo u| + |evenPolePoly apertureLogTwo u - evenPolePoly A0 u| := abs_add_le _ _
      _ ≤ 3 / 10 ^ 25 := by linarith
  let E_fn := fun u => Real.cosh (apertureLogTwo * u / 2) - evenPolePoly A0 u
  have hEc : Continuous E_fn := by unfold E_fn evenPolePoly; fun_prop
  have i_c1 : IntervalIntegrable (fun u => G u * Real.cosh (apertureLogTwo * u / 2)) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable 0 1
  have i_c2 : IntervalIntegrable (fun u => G u * evenPolePoly A0 u) volume 0 1 :=
    (by unfold evenPolePoly; fun_prop : Continuous _).intervalIntegrable 0 1
  have hdiff_int : P_true - P_0 = ∫ u in (0 : ℝ)..1, G u * E_fn u := by
    dsimp [P_true, P_0, E_fn]
    rw [← intervalIntegral.integral_sub i_c1 i_c2]
    exact intervalIntegral.integral_congr fun u _ => by ring
  have hcs := interval_cauchy_schwarz_unit hG hEc (by norm_num : (0 : ℝ) ≤ 3 / 10 ^ 25) herr_pt
  rw [← hdiff_int] at hcs
  set δ := P_true - P_0
  have hyoung : (1 - 1 / 10 ^ 20 : ℝ) * P_0 ^ 2 - 10 ^ 20 * δ ^ 2 ≤ P_true ^ 2 := by
    have hPt : P_true = P_0 + δ := by dsimp [δ]; ring
    rw [hPt]
    have hsq : 0 ≤ ((1 / 10 ^ 10 : ℝ) * P_0 + 10 ^ 10 * δ) ^ 2 := sq_nonneg _
    nlinarith
  have hA_lo : logTwoLo ≤ apertureLogTwo := h2l
  have hA_hi : apertureLogTwo ≤ logTwoHi := h2u
  have hMG_nn : 0 ≤ ∫ u in (0 : ℝ)..1, G u ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_nonneg measurableSet_Ioc fun u _ => sq_nonneg _
  have h1 : 4 * logTwoLo * P_true ^ 2 ≤ 4 * apertureLogTwo * P_true ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h2 : 4 * logTwoLo * ((1 - 1 / 10 ^ 20) * P_0 ^ 2 - 10 ^ 20 * δ ^ 2) ≤ 4 * logTwoLo * P_true ^ 2 :=
    mul_le_mul_of_nonneg_left hyoung (by norm_num [logTwoLo])
  have h3 : 4 * logTwoLo * 10 ^ 20 * (3 / 10 ^ 25 : ℝ) ^ 2 ≤ 1 / 10 ^ 24 := by norm_num [logTwoLo]
  nlinarith [mul_le_mul_of_nonneg_left hcs (show 0 ≤ 4 * logTwoLo * (10 ^ 20 : ℝ) by norm_num [logTwoLo]),
    mul_le_mul_of_nonneg_right h3 hMG_nn]

theorem odd_sinh_pole_ge {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (ho : ∀ x, F (-x) = -F x) {A0 : ℝ}
    (hA0_pos : 0 ≤ A0) (hA0_hi : A0 ≤ 4 / 5)
    (hdA : |apertureLogTwo - A0| ≤ 2 / 10 ^ 25) :
    let G := dilateLogTwo F;
    -4 * logTwoHi * (1 + 1 / 10 ^ 20) * (∫ u in (0 : ℝ)..1, G u * oddPolePoly A0 u) ^ 2 -
      (1 / 10 ^ 24) * (∫ u in (0 : ℝ)..1, G u ^ 2) ≤
      -(sinhPairing F ^ 2 / 2) / (2 * apertureLogTwo) := by
  intro G
  have hG : Continuous G := hF.comp (continuous_const.mul continuous_id)
  have hGo : ∀ u, G (-u) = -G u := fun u => by unfold G dilateLogTwo; rw [mul_neg, ho]
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  have hA_pos := apertureLogTwo_pos
  have hpair : sinhPairing F = 4 * apertureLogTwo * ∫ u in (0 : ℝ)..1, G u * Real.sinh (apertureLogTwo * u / 2) := by
    unfold sinhPairing
    have hscale := Measure.integral_comp_mul_left (fun x => 2 * Real.sinh (x / 2) * F x) apertureLogTwo
    rw [abs_of_pos (inv_pos.mpr hA_pos), smul_eq_mul] at hscale
    have hcut : (∫ u in Icc (-1 : ℝ) 1, 2 * Real.sinh (apertureLogTwo * u / 2) * G u) =
        ∫ u, 2 * Real.sinh (apertureLogTwo * u / 2) * G u :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
        dsimp [G]
        rw [dilateLogTwo_outside hs hu, mul_zero]
    have hev := even_integral_Icc_unit
      (H := fun u => 2 * Real.sinh (apertureLogTwo * u / 2) * G u)
      (by fun_prop)
      fun u => by rw [mul_neg, neg_div, Real.sinh_neg, hGo]; ring
    rw [hcut] at hev
    change (∫ u, 2 * Real.sinh (apertureLogTwo * u / 2) * G u) =
      apertureLogTwo⁻¹ * ∫ x, 2 * Real.sinh (x / 2) * F x at hscale
    have h2int : (∫ u in (0 : ℝ)..1, 2 * Real.sinh (apertureLogTwo * u / 2) * G u) =
        2 * ∫ u in (0 : ℝ)..1, G u * Real.sinh (apertureLogTwo * u / 2) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun u _ => by ring
    rw [h2int] at hev
    field_simp [hA_pos.ne'] at hscale
    linarith
  have hquot : -(sinhPairing F ^ 2 / 2) / (2 * apertureLogTwo) =
      -4 * apertureLogTwo * (∫ u in (0 : ℝ)..1, G u * Real.sinh (apertureLogTwo * u / 2)) ^ 2 := by
    rw [hpair]; field_simp [hA_pos.ne']; ring
  rw [hquot]
  set S_true := ∫ u in (0 : ℝ)..1, G u * Real.sinh (apertureLogTwo * u / 2)
  set S_0 := ∫ u in (0 : ℝ)..1, G u * oddPolePoly A0 u
  have herr_pt : ∀ u ∈ Icc (0 : ℝ) 1,
      |Real.sinh (apertureLogTwo * u / 2) - oddPolePoly A0 u| ≤ 3 / 10 ^ 25 := by
    intro u hu
    set z := apertureLogTwo * u / 2
    set z0 := A0 * u / 2
    have hz_mem : z ∈ Icc (0 : ℝ) (1 / 2) := by
      have hAu : apertureLogTwo ≤ 7 / 10 := by
        unfold apertureLogTwo; norm_num [logTwoHi] at h2u; linarith
      refine ⟨div_nonneg (mul_nonneg hA_pos.le hu.1) (by norm_num), ?_⟩
      dsimp [z]; nlinarith [hu.2, hA_pos, hAu]
    have hz0_mem : z0 ∈ Icc (0 : ℝ) (1 / 2) := by
      refine ⟨div_nonneg (mul_nonneg hA0_pos hu.1) (by norm_num), ?_⟩
      dsimp [z0]; nlinarith [hu.2, hA0_pos, hA0_hi]
    have hz1 : |z| ≤ 1 := by rw [abs_of_nonneg hz_mem.1]; linarith [hz_mem.2]
    have hnz1 : |-z| ≤ 1 := by simpa only [abs_neg] using hz1
    have hp := Real.exp_bound hz1 (n := 23) (by norm_num)
    have hm := Real.exp_bound hnz1 (n := 23) (by norm_num)
    have hsinh_trunc : |Real.sinh z - oddPolePoly apertureLogTwo u| ≤ 1 / 10 ^ 26 := by
      have heq_sum := exp_odd_diff_sum z 11
      unfold oddPolePoly
      change |Real.sinh z - ∑ j ∈ Finset.range 11, z ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)| ≤ _
      rw [Real.sinh_eq]
      have hdiff : (Real.exp z - Real.exp (-z)) / 2 -
          (∑ j ∈ Finset.range 11, z ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) =
          ((Real.exp z - ∑ m ∈ Finset.range 23, z ^ m / (m.factorial : ℝ)) -
            (Real.exp (-z) - ∑ m ∈ Finset.range 23, (-z) ^ m / (m.factorial : ℝ))) / 2 := by
        linarith [heq_sum]
      rw [hdiff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have htri := (abs_sub _ _).trans (add_le_add hp hm)
      rw [abs_neg, abs_of_nonneg hz_mem.1] at htri
      have hz23 : z ^ 23 ≤ (1 / 2 : ℝ) ^ 23 := pow_le_pow_left₀ hz_mem.1 hz_mem.2 23
      have hnum : (1 / 2 : ℝ) ^ 23 * ((23 : ℝ) + 1) / ((23 : ℕ).factorial * (23 : ℝ)) ≤ 1 / 10 ^ 26 := by
        norm_num [Nat.factorial]
      nlinarith
    have hshift : |oddPolePoly apertureLogTwo u - oddPolePoly A0 u| ≤ 2 / 10 ^ 25 := by
      unfold oddPolePoly
      change |(∑ j ∈ Finset.range 11, z ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) -
        ∑ j ∈ Finset.range 11, z0 ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)| ≤ _
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ k ∈ Finset.range 11,
          |z ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) -
            z0 ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)| ≤
          ((2 * k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (2 * k) / ((2 * k + 1).factorial : ℝ) * |z - z0| := by
        intro k _
        have hpos_f : (0 : ℝ) < ((2 * k + 1).factorial : ℝ) :=
          Nat.cast_pos.mpr (Nat.factorial_pos _)
        rw [← sub_div, abs_div, abs_of_pos hpos_f]
        have hp_sub := abs_pow_sub_le_half hz_mem hz0_mem (2 * k)
        have hdiv := div_le_div_of_nonneg_right hp_sub hpos_f.le
        refine hdiv.trans (le_of_eq ?_)
        push_cast; ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have hsum_num : (∑ k ∈ Finset.range 11,
          ((2 * k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (2 * k) / ((2 * k + 1).factorial : ℝ)) ≤ 2 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      have hdz : |z - z0| ≤ 1 / 10 ^ 25 := by
        have : z - z0 = (apertureLogTwo - A0) * (u / 2) := by dsimp [z, z0]; ring
        rw [this, abs_mul, abs_of_nonneg (div_nonneg hu.1 (by norm_num))]
        have hu2 : u / 2 ≤ 1 / 2 := by linarith [hu.2]
        nlinarith [abs_nonneg (apertureLogTwo - A0)]
      nlinarith [abs_nonneg (z - z0)]
    calc
      |Real.sinh z - oddPolePoly A0 u|
        = |(Real.sinh z - oddPolePoly apertureLogTwo u) + (oddPolePoly apertureLogTwo u - oddPolePoly A0 u)| := by ring_nf
      _ ≤ |Real.sinh z - oddPolePoly apertureLogTwo u| + |oddPolePoly apertureLogTwo u - oddPolePoly A0 u| := abs_add_le _ _
      _ ≤ 3 / 10 ^ 25 := by linarith
  let E_fn := fun u => Real.sinh (apertureLogTwo * u / 2) - oddPolePoly A0 u
  have hEc : Continuous E_fn := by unfold E_fn oddPolePoly; fun_prop
  have i_s1 : IntervalIntegrable (fun u => G u * Real.sinh (apertureLogTwo * u / 2)) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable 0 1
  have i_s2 : IntervalIntegrable (fun u => G u * oddPolePoly A0 u) volume 0 1 :=
    (by unfold oddPolePoly; fun_prop : Continuous _).intervalIntegrable 0 1
  have hdiff_int : S_true - S_0 = ∫ u in (0 : ℝ)..1, G u * E_fn u := by
    dsimp [S_true, S_0, E_fn]
    rw [← intervalIntegral.integral_sub i_s1 i_s2]
    exact intervalIntegral.integral_congr fun u _ => by ring
  have hcs := interval_cauchy_schwarz_unit hG hEc (by norm_num : (0 : ℝ) ≤ 3 / 10 ^ 25) herr_pt
  rw [← hdiff_int] at hcs
  set δ := S_true - S_0
  have hyoung : S_true ^ 2 ≤ (1 + 1 / 10 ^ 20 : ℝ) * S_0 ^ 2 + (1 + 10 ^ 20) * δ ^ 2 := by
    have hSt : S_true = S_0 + δ := by dsimp [δ]; ring
    rw [hSt]
    have hsq : 0 ≤ ((1 / 10 ^ 10 : ℝ) * S_0 - 10 ^ 10 * δ) ^ 2 := sq_nonneg _
    nlinarith
  have hA_hi : apertureLogTwo ≤ logTwoHi := h2u
  have hMG_nn : 0 ≤ ∫ u in (0 : ℝ)..1, G u ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_nonneg measurableSet_Ioc fun u _ => sq_nonneg _
  have h1 : -4 * logTwoHi * S_true ^ 2 ≤ -4 * apertureLogTwo * S_true ^ 2 := by
    have := mul_le_mul_of_nonneg_right (show 4 * apertureLogTwo ≤ 4 * logTwoHi by linarith) (sq_nonneg S_true)
    linarith
  have h2 : -4 * logTwoHi * ((1 + 1 / 10 ^ 20) * S_0 ^ 2 + (1 + 10 ^ 20) * δ ^ 2) ≤
      -4 * logTwoHi * S_true ^ 2 := by
    have := mul_le_mul_of_nonneg_left hyoung (show 0 ≤ 4 * logTwoHi by norm_num [logTwoHi])
    linarith
  have h3 : 4 * logTwoHi * (1 + 10 ^ 20) * (3 / 10 ^ 25 : ℝ) ^ 2 ≤ 1 / 10 ^ 24 := by
    norm_num [logTwoHi]
  nlinarith [mul_le_mul_of_nonneg_left hcs (show 0 ≤ 4 * logTwoHi * (1 + 10 ^ 20 : ℝ) by norm_num [logTwoHi]),
    mul_le_mul_of_nonneg_right h3 hMG_nn]

/-! ### 7. Six-interval folding on `(0, 1)`, tridiagonal `LDLᵀ` pivots, and SDP algebra -/

/-- Partition of `(0, 1)` into four branches over `(0, (1 - a) / 2)` and two branches over
`(1 - a, 1 / 2)` for any integrable function `H` on `(0, 1)`. -/
theorem six_interval_folding_diag {H : ℝ → ℝ} (hH : IntegrableOn H (Ioo (0 : ℝ) 1)) :
    let a := primeThreeOffset
    let L4 := (1 - a) / 2
    (∫ u in Ioo (0 : ℝ) 1, H u) =
      (∫ s in (0 : ℝ)..L4, H s + H (1 - s) + H (a + s) + H (1 - a - s)) +
        ∫ u in (1 - a)..(1 / 2), H u + H (1 - u) := by
  intro a L4
  obtain ⟨ha_lo, ha_hi⟩ := primeThreeOffset_bounds
  have hH_Icc : IntegrableOn H (Icc (0 : ℝ) 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioo).mpr hH
  have hii : ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 1 → IntervalIntegrable H volume α β := fun α β h0 hαβ h1 =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le hαβ).mpr
      (hH_Icc.mono_set fun x hx => ⟨h0.trans hx.1, hx.2.trans h1⟩)
  have h01 : (∫ u in Ioo (0 : ℝ) 1, H u) = ∫ u in (0 : ℝ)..1, H u := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  rw [h01]
  have p1 := intervalIntegral.integral_add_adjacent_intervals
    (hii 0 L4 le_rfl (by dsimp [L4]; linarith) (by dsimp [L4]; linarith))
    (hii L4 1 (by dsimp [L4]; linarith) (by dsimp [L4]; linarith) le_rfl)
  have p2 := intervalIntegral.integral_add_adjacent_intervals
    (hii L4 (1 - a) (by dsimp [L4]; linarith) (by dsimp [L4]; linarith) (by linarith))
    (hii (1 - a) 1 (by linarith) (by linarith) le_rfl)
  have p3 := intervalIntegral.integral_add_adjacent_intervals
    (hii (1 - a) (1 / 2) (by linarith) (by linarith) (by norm_num))
    (hii (1 / 2) 1 (by norm_num) (by norm_num) le_rfl)
  have p4 := intervalIntegral.integral_add_adjacent_intervals
    (hii (1 / 2) a (by norm_num) (by linarith) (by linarith))
    (hii a 1 (by linarith) (by linarith) le_rfl)
  have p5 := intervalIntegral.integral_add_adjacent_intervals
    (hii a (1 - L4) (by linarith) (by dsimp [L4]; linarith) (by dsimp [L4]; linarith))
    (hii (1 - L4) 1 (by dsimp [L4]; linarith) (by dsimp [L4]; linarith) le_rfl)
  have s2 : (∫ u in L4..(1 - a), H u) = ∫ s in (0 : ℝ)..L4, H (1 - a - s) := by
    have h := (intervalIntegral.integral_comp_sub_left H (1 - a) (a := (0 : ℝ)) (b := L4)).symm
    rw [sub_zero, show 1 - a - L4 = L4 by dsimp [L4]; ring] at h
    exact h
  have s4 : (∫ u in (1 / 2)..a, H u) = ∫ u in (1 - a)..(1 / 2), H (1 - u) := by
    have h := (intervalIntegral.integral_comp_sub_left H 1 (a := 1 - a) (b := 1 / 2)).symm
    rw [show 1 - (1 - a) = a by ring, show (1 : ℝ) - (1 / 2) = 1 / 2 by norm_num] at h
    exact h
  have s5 : (∫ u in a..(1 - L4), H u) = ∫ s in (0 : ℝ)..L4, H (a + s) := by
    have h := intervalIntegral.integral_comp_add_left H a (a := (0 : ℝ)) (b := L4)
    rw [add_zero, show a + L4 = 1 - L4 by dsimp [L4]; ring] at h
    exact h.symm
  have s6 : (∫ u in (1 - L4)..1, H u) = ∫ s in (0 : ℝ)..L4, H (1 - s) := by
    have h := (intervalIntegral.integral_comp_sub_left H 1 (a := (0 : ℝ)) (b := L4)).symm
    rw [sub_zero] at h
    exact h
  have i_s0 : IntervalIntegrable H volume 0 L4 :=
    hii 0 L4 le_rfl (by dsimp [L4]; linarith) (by dsimp [L4]; linarith)
  have i_s1 : IntervalIntegrable (fun s => H (1 - s)) volume 0 L4 := by
    have h := ((hii (1 - L4) 1 (by dsimp [L4]; linarith) (by dsimp [L4]; linarith) le_rfl).comp_sub_left 1).symm
    rwa [sub_self, show 1 - (1 - L4) = L4 by ring] at h
  have i_s2 : IntervalIntegrable (fun s => H (a + s)) volume 0 L4 := by
    have h := (hii a (1 - L4) (by linarith) (by dsimp [L4]; linarith) (by dsimp [L4]; linarith)).comp_add_left a
    rwa [sub_self, show 1 - L4 - a = L4 by dsimp [L4]; ring] at h
  have i_s3 : IntervalIntegrable (fun s => H (1 - a - s)) volume 0 L4 := by
    have h := ((hii L4 (1 - a) (by dsimp [L4]; linarith) (by dsimp [L4]; linarith) (by linarith)).comp_sub_left (1 - a)).symm
    rwa [sub_self, show 1 - a - L4 = L4 by dsimp [L4]; ring] at h
  have i_u0 : IntervalIntegrable H volume (1 - a) (1 / 2) :=
    hii (1 - a) (1 / 2) (by linarith) (by linarith) (by norm_num)
  have i_u1 : IntervalIntegrable (fun u => H (1 - u)) volume (1 - a) (1 / 2) := by
    have h := ((hii (1 / 2) a (by norm_num) (by linarith) (by linarith)).comp_sub_left 1).symm
    rwa [show (1 : ℝ) - (1 / 2) = 1 / 2 by norm_num] at h
  rw [intervalIntegral.integral_add ((i_s0.add i_s1).add i_s2) i_s3,
    intervalIntegral.integral_add (i_s0.add i_s1) i_s2,
    intervalIntegral.integral_add i_s0 i_s1,
    intervalIntegral.integral_add i_u0 i_u1]
  linarith [p1, p2, p3, p4, p5, s2, s4, s5, s6]

theorem six_interval_folding_primeTwo {G : ℝ → ℝ} (hG : Continuous G) :
    let a := primeThreeOffset
    let L4 := (1 - a) / 2
    (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) =
      (∫ s in (0 : ℝ)..L4, G s * G (1 - s) + G (a + s) * G (1 - a - s)) +
        ∫ u in (1 - a)..(1 / 2), G u * G (1 - u) := by
  intro a L4
  obtain ⟨ha_lo, ha_hi⟩ := primeThreeOffset_bounds
  let H := fun u => G u * G (1 - u)
  have hHc : Continuous H := by fun_prop
  have p1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := (0 : ℝ)) (b := L4) (c := 1 / 2) (hHc.intervalIntegrable _ _) (hHc.intervalIntegrable _ _)
  have p2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := L4) (b := 1 - a) (c := 1 / 2) (hHc.intervalIntegrable _ _) (hHc.intervalIntegrable _ _)
  have s2 : (∫ u in L4..(1 - a), H u) = ∫ s in (0 : ℝ)..L4, G (a + s) * G (1 - a - s) := by
    have h := (intervalIntegral.integral_comp_sub_left H (1 - a) (a := (0 : ℝ)) (b := L4)).symm
    rw [sub_zero, show 1 - a - L4 = L4 by dsimp [L4]; ring] at h
    exact h.trans (intervalIntegral.integral_congr fun s _ => by
      dsimp [H]; rw [show 1 - (1 - a - s) = a + s by ring, mul_comm])
  have i1 : IntervalIntegrable (fun s => G s * G (1 - s)) volume 0 L4 := hHc.intervalIntegrable 0 L4
  have i2 : IntervalIntegrable (fun s => G (a + s) * G (1 - a - s)) volume 0 L4 :=
    (by fun_prop : Continuous _).intervalIntegrable 0 L4
  rw [intervalIntegral.integral_add i1 i2]
  dsimp [H] at p1 p2 s2
  linarith

/-- `4 × 4` symmetric tridiagonal quadratic form on a fiber. -/
def tridiag4Form (d0 d1 d2 d3 e2 e3 g0 g1 g2 g3 : ℝ) : ℝ :=
  d0 * g0 ^ 2 + d1 * g1 ^ 2 + d2 * g2 ^ 2 + d3 * g3 ^ 2 +
    2 * e2 * g0 * g1 + 2 * e3 * g1 * g2 + 2 * e2 * g2 * g3

/-- `2 × 2` symmetric tridiagonal quadratic form on a fiber. -/
def tridiag2Form (d0 d1 e2 g0 g1 : ℝ) : ℝ :=
  d0 * g0 ^ 2 + d1 * g1 ^ 2 + 2 * e2 * g0 * g1

theorem tridiag4_ge_seventeen_sixteenths
    {b0 b1 b2 b3 d0 d1 d2 d3 e2 e3 p0 p1 p2 p3 : ℝ}
    (hd0 : b0 ≤ d0) (hd1 : b1 ≤ d1) (hd2 : b2 ≤ d2) (hd3 : b3 ≤ d3)
    (hp0_eq : p0 = b0 - 17 / 16) (hp0 : 0 < p0)
    (hp1_eq : p1 = (b1 - 17 / 16) - e2 ^ 2 / p0) (hp1 : 0 < p1)
    (hp2_eq : p2 = (b2 - 17 / 16) - e3 ^ 2 / p1) (hp2 : 0 < p2)
    (hp3_eq : p3 = (b3 - 17 / 16) - e2 ^ 2 / p2) (hp3 : 0 < p3)
    (g0 g1 g2 g3 : ℝ) :
    (17 / 16 : ℝ) * (g0 ^ 2 + g1 ^ 2 + g2 ^ 2 + g3 ^ 2) ≤
      tridiag4Form d0 d1 d2 d3 e2 e3 g0 g1 g2 g3 := by
  have hmono : tridiag4Form b0 b1 b2 b3 e2 e3 g0 g1 g2 g3 ≤
      tridiag4Form d0 d1 d2 d3 e2 e3 g0 g1 g2 g3 := by
    unfold tridiag4Form
    nlinarith [sq_nonneg g0, sq_nonneg g1, sq_nonneg g2, sq_nonneg g3]
  have hb0 : b0 = p0 + 17 / 16 := by linarith [hp0_eq]
  have hb1 : b1 = p1 + 17 / 16 + e2 ^ 2 / p0 := by linarith [hp1_eq]
  have hb2 : b2 = p2 + 17 / 16 + e3 ^ 2 / p1 := by linarith [hp2_eq]
  have hb3 : b3 = p3 + 17 / 16 + e2 ^ 2 / p2 := by linarith [hp3_eq]
  have hsos : tridiag4Form b0 b1 b2 b3 e2 e3 g0 g1 g2 g3 -
      (17 / 16 : ℝ) * (g0 ^ 2 + g1 ^ 2 + g2 ^ 2 + g3 ^ 2) =
      p0 * (g0 + (e2 / p0) * g1) ^ 2 +
        p1 * (g1 + (e3 / p1) * g2) ^ 2 +
        p2 * (g2 + (e2 / p2) * g3) ^ 2 +
        p3 * g3 ^ 2 := by
    unfold tridiag4Form
    rw [hb0, hb1, hb2, hb3]
    field_simp [hp0.ne', hp1.ne', hp2.ne']
    ring
  have hnn : 0 ≤ p0 * (g0 + (e2 / p0) * g1) ^ 2 +
      p1 * (g1 + (e3 / p1) * g2) ^ 2 +
      p2 * (g2 + (e2 / p2) * g3) ^ 2 +
      p3 * g3 ^ 2 := by positivity
  linarith

theorem tridiag4_complete_sq_pert
    {d0 d1 d2 d3 e2 e3 : ℝ}
    (hcoerc : ∀ u0 u1 u2 u3,
      (17 / 16 : ℝ) * (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2) ≤
        tridiag4Form d0 d1 d2 d3 e2 e3 u0 u1 u2 u3)
    (g0 g1 g2 g3 w0 w1 w2 w3 v0 v1 v20 v30 dv2 dv3 : ℝ) :
    -(2 * (w0 * v0 + w1 * v1 + w2 * v20 + w3 * v30) -
        tridiag4Form d0 d1 d2 d3 e2 e3 w0 w1 w2 w3) -
      ((d0 * w0 + e2 * w1 - v0) ^ 2 + (e2 * w0 + d1 * w1 + e3 * w2 - v1) ^ 2 +
        (e3 * w1 + d2 * w2 + e2 * w3 - v20) ^ 2 + (e2 * w2 + d3 * w3 - v30) ^ 2) -
      (1 / 10 ^ 22 : ℝ) * (w2 ^ 2 + w3 ^ 2) -
      (16 + 10 ^ 22 : ℝ) * (dv2 ^ 2 + dv3 ^ 2) ≤
      tridiag4Form d0 d1 d2 d3 e2 e3 g0 g1 g2 g3 -
        2 * (g0 * v0 + g1 * v1 + g2 * (v20 + dv2) + g3 * (v30 + dv3)) := by
  set u0 := g0 - w0
  set u1 := g1 - w1
  set u2 := g2 - w2
  set u3 := g3 - w3
  have hg0 : g0 = w0 + u0 := by dsimp [u0]; ring
  have hg1 : g1 = w1 + u1 := by dsimp [u1]; ring
  have hg2 : g2 = w2 + u2 := by dsimp [u2]; ring
  have hg3 : g3 = w3 + u3 := by dsimp [u3]; ring
  have hQ := hcoerc u0 u1 u2 u3
  have hexp : tridiag4Form d0 d1 d2 d3 e2 e3 (w0 + u0) (w1 + u1) (w2 + u2) (w3 + u3) -
      2 * ((w0 + u0) * v0 + (w1 + u1) * v1 + (w2 + u2) * (v20 + dv2) + (w3 + u3) * (v30 + dv3)) =
      -(2 * (w0 * v0 + w1 * v1 + w2 * v20 + w3 * v30) -
          tridiag4Form d0 d1 d2 d3 e2 e3 w0 w1 w2 w3) +
        tridiag4Form d0 d1 d2 d3 e2 e3 u0 u1 u2 u3 +
        2 * (u0 * (d0 * w0 + e2 * w1 - v0) + u1 * (e2 * w0 + d1 * w1 + e3 * w2 - v1) +
          u2 * (e3 * w1 + d2 * w2 + e2 * w3 - v20) + u3 * (e2 * w2 + d3 * w3 - v30)) -
        2 * (u2 * dv2 + u3 * dv3) - 2 * (w2 * dv2 + w3 * dv3) := by
    unfold tridiag4Form; ring
  rw [hg0, hg1, hg2, hg3, hexp]
  have hs0 : 0 ≤ (u0 + (d0 * w0 + e2 * w1 - v0)) ^ 2 := sq_nonneg _
  have hs1 : 0 ≤ (u1 + (e2 * w0 + d1 * w1 + e3 * w2 - v1)) ^ 2 := sq_nonneg _
  have hs2 : 0 ≤ (u2 + (e3 * w1 + d2 * w2 + e2 * w3 - v20)) ^ 2 := sq_nonneg _
  have hs3 : 0 ≤ (u3 + (e2 * w2 + d3 * w3 - v30)) ^ 2 := sq_nonneg _
  have hu2 : 0 ≤ ((1 / 4 : ℝ) * u2 - 4 * dv2) ^ 2 := sq_nonneg _
  have hu3 : 0 ≤ ((1 / 4 : ℝ) * u3 - 4 * dv3) ^ 2 := sq_nonneg _
  have hw2 : 0 ≤ ((1 / 10 ^ 11 : ℝ) * w2 + 10 ^ 11 * dv2) ^ 2 := sq_nonneg _
  have hw3 : 0 ≤ ((1 / 10 ^ 11 : ℝ) * w3 + 10 ^ 11 * dv3) ^ 2 := sq_nonneg _
  have hnonneg01 : 0 ≤ (1 / 16 : ℝ) * (u0 ^ 2 + u1 ^ 2) := by positivity
  linarith

theorem tridiag4_sliver_ge
    {d0 d1 d2 d3 e2 e3 : ℝ}
    (hcoerc : ∀ g0 g1 g2 g3,
      (17 / 16 : ℝ) * (g0 ^ 2 + g1 ^ 2 + g2 ^ 2 + g3 ^ 2) ≤
        tridiag4Form d0 d1 d2 d3 e2 e3 g0 g1 g2 g3)
    (g0 g1 g2 g3 v0 v1 v2 v3 : ℝ) :
    -(v0 ^ 2 + v1 ^ 2 + v2 ^ 2 + v3 ^ 2) ≤
      tridiag4Form d0 d1 d2 d3 e2 e3 g0 g1 g2 g3 -
        2 * (g0 * v0 + g1 * v1 + g2 * v2 + g3 * v3) := by
  have hQ := hcoerc g0 g1 g2 g3
  have hs0 : 0 ≤ (g0 - v0) ^ 2 := sq_nonneg _
  have hs1 : 0 ≤ (g1 - v1) ^ 2 := sq_nonneg _
  have hs2 : 0 ≤ (g2 - v2) ^ 2 := sq_nonneg _
  have hs3 : 0 ≤ (g3 - v3) ^ 2 := sq_nonneg _
  have hrem : 0 ≤ (1 / 16 : ℝ) * (g0 ^ 2 + g1 ^ 2 + g2 ^ 2 + g3 ^ 2) := by positivity
  linarith

theorem tridiag2_ge_seventeen_sixteenths
    {b0 b1 d0 d1 e2 p0 p1 : ℝ}
    (hd0 : b0 ≤ d0) (hd1 : b1 ≤ d1)
    (hp0_eq : p0 = b0 - 17 / 16) (hp0 : 0 < p0)
    (hp1_eq : p1 = (b1 - 17 / 16) - e2 ^ 2 / p0) (hp1 : 0 < p1)
    (g0 g1 : ℝ) :
    (17 / 16 : ℝ) * (g0 ^ 2 + g1 ^ 2) ≤ tridiag2Form d0 d1 e2 g0 g1 := by
  have hmono : tridiag2Form b0 b1 e2 g0 g1 ≤ tridiag2Form d0 d1 e2 g0 g1 := by
    unfold tridiag2Form; nlinarith [sq_nonneg g0, sq_nonneg g1]
  have hb0 : b0 = p0 + 17 / 16 := by linarith [hp0_eq]
  have hb1 : b1 = p1 + 17 / 16 + e2 ^ 2 / p0 := by linarith [hp1_eq]
  have hsos : tridiag2Form b0 b1 e2 g0 g1 - (17 / 16 : ℝ) * (g0 ^ 2 + g1 ^ 2) =
      p0 * (g0 + (e2 / p0) * g1) ^ 2 + p1 * g1 ^ 2 := by
    unfold tridiag2Form
    rw [hb0, hb1]
    field_simp [hp0.ne']
    ring
  have hnn : 0 ≤ p0 * (g0 + (e2 / p0) * g1) ^ 2 + p1 * g1 ^ 2 := by positivity
  linarith

theorem tridiag2_complete_sq
    {d0 d1 e2 : ℝ}
    (hcoerc : ∀ u0 u1, (17 / 16 : ℝ) * (u0 ^ 2 + u1 ^ 2) ≤ tridiag2Form d0 d1 e2 u0 u1)
    (g0 g1 w0 w1 v0 v1 : ℝ) :
    -(2 * (w0 * v0 + w1 * v1) - tridiag2Form d0 d1 e2 w0 w1) -
      ((d0 * w0 + e2 * w1 - v0) ^ 2 + (e2 * w0 + d1 * w1 - v1) ^ 2) ≤
      tridiag2Form d0 d1 e2 g0 g1 - 2 * (g0 * v0 + g1 * v1) := by
  set u0 := g0 - w0
  set u1 := g1 - w1
  have hg0 : g0 = w0 + u0 := by dsimp [u0]; ring
  have hg1 : g1 = w1 + u1 := by dsimp [u1]; ring
  have hQ := hcoerc u0 u1
  have hexp : tridiag2Form d0 d1 e2 (w0 + u0) (w1 + u1) - 2 * ((w0 + u0) * v0 + (w1 + u1) * v1) =
      -(2 * (w0 * v0 + w1 * v1) - tridiag2Form d0 d1 e2 w0 w1) +
        tridiag2Form d0 d1 e2 u0 u1 +
        2 * (u0 * (d0 * w0 + e2 * w1 - v0) + u1 * (e2 * w0 + d1 * w1 - v1)) := by
    unfold tridiag2Form; ring
  rw [hg0, hg1, hexp]
  have hs0 : 0 ≤ (u0 + (d0 * w0 + e2 * w1 - v0)) ^ 2 := sq_nonneg _
  have hs1 : 0 ≤ (u1 + (e2 * w0 + d1 * w1 - v1)) ^ 2 := sq_nonneg _
  have hrem : 0 ≤ (1 / 16 : ℝ) * (u0 ^ 2 + u1 ^ 2) := by positivity
  linarith

theorem tridiag2_sliver_ge
    {d0 d1 e2 : ℝ}
    (hcoerc : ∀ g0 g1, (17 / 16 : ℝ) * (g0 ^ 2 + g1 ^ 2) ≤ tridiag2Form d0 d1 e2 g0 g1)
    (g0 g1 v0 v1 : ℝ) :
    -(v0 ^ 2 + v1 ^ 2) ≤ tridiag2Form d0 d1 e2 g0 g1 - 2 * (g0 * v0 + g1 * v1) := by
  have hQ := hcoerc g0 g1
  have hs0 : 0 ≤ (g0 - v0) ^ 2 := sq_nonneg _
  have hs1 : 0 ≤ (g1 - v1) ^ 2 := sq_nonneg _
  have hrem : 0 ≤ (1 / 16 : ℝ) * (g0 ^ 2 + g1 ^ 2) := by positivity
  linarith

/-- Bernstein–Jensen `L²[0, 1]` bound: if `P(ξ) = ∑_{k=0}^N β_k C(N, k) ξ^k (1 - ξ)^{N - k}`, then
`∫_0^1 P(ξ)^2 dξ ≤ (1 / (N + 1)) ∑_{k=0}^N β_k^2`. -/
theorem bernstein_l2_unit_le (N : ℕ) (β : ℕ → ℝ) {P : ℝ → ℝ} (hPc : Continuous P)
    (hP : ∀ ξ, P ξ = ∑ k ∈ Finset.range (N + 1),
      β k * ((N.choose k : ℝ) * ξ ^ k * (1 - ξ) ^ (N - k))) :
    (∫ ξ in (0 : ℝ)..1, P ξ ^ 2) ≤
      (1 / ((N : ℝ) + 1)) * ∑ k ∈ Finset.range (N + 1), β k ^ 2 := by
  have hpt : ∀ ξ ∈ Icc (0 : ℝ) 1,
      P ξ ^ 2 ≤ ∑ k ∈ Finset.range (N + 1),
        β k ^ 2 * ((N.choose k : ℝ) * ξ ^ k * (1 - ξ) ^ (N - k)) := by
    intro ξ hξ
    let w := fun k => (N.choose k : ℝ) * ξ ^ k * (1 - ξ) ^ (N - k)
    have hw_nn : ∀ k ∈ Finset.range (N + 1), 0 ≤ w k := fun k _ =>
      mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hξ.1 _)) (pow_nonneg (by linarith [hξ.2]) _)
    have hw_sum : (∑ k ∈ Finset.range (N + 1), w k) = 1 := by
      have hb := add_pow ξ (1 - ξ) N
      rw [add_sub_cancel, one_pow] at hb
      rw [hb]
      apply Finset.sum_congr rfl; intro k _; dsimp [w]; ring
    have hcs := weighted_cauchy_schwarz_finset (Finset.range (N + 1)) w β (fun _ => 1) hw_nn
    simp only [mul_one, one_pow, hw_sum] at hcs
    have hP_eq : P ξ = ∑ k ∈ Finset.range (N + 1), w k * β k := by
      rw [hP ξ]; apply Finset.sum_congr rfl; intro k _; dsimp [w]; ring
    rw [hP_eq]
    refine hcs.trans ?_
    apply le_of_eq
    apply Finset.sum_congr rfl; intro k _; dsimp [w]; ring
  have hmono : (∫ ξ in (0 : ℝ)..1, P ξ ^ 2) ≤
      ∫ ξ in (0 : ℝ)..1, ∑ k ∈ Finset.range (N + 1),
        β k ^ 2 * ((N.choose k : ℝ) * ξ ^ k * (1 - ξ) ^ (N - k)) := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((hPc.pow 2).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun ξ => _).intervalIntegrable 0 1) hpt
  refine hmono.trans (le_of_eq ?_)
  have hik (k : ℕ) : IntervalIntegrable
      (fun ξ : ℝ => β k ^ 2 * ((N.choose k : ℝ) * ξ ^ k * (1 - ξ) ^ (N - k))) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable 0 1
  rw [intervalIntegral.integral_finsetSum fun k _ => hik k]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have heq_fn : (fun ξ : ℝ => β k ^ 2 * ((N.choose k : ℝ) * ξ ^ k * (1 - ξ) ^ (N - k))) =
      fun ξ => (β k ^ 2 * (N.choose k : ℝ)) * (ξ ^ k * (1 - ξ) ^ (N - k)) := funext fun ξ => by ring
  rw [intervalIntegral.integral_congr fun ξ _ => congrFun heq_fn ξ,
    intervalIntegral.integral_const_mul,
    RHTower.integral_pow_mul_one_sub_pow_eq_factorial_ratio k (N - k)]
  have hch := Nat.choose_mul_factorial_mul_factorial hk_le
  have hchR : (N.choose k : ℝ) * (k.factorial : ℝ) * ((N - k).factorial : ℝ) = (N.factorial : ℝ) := by
    exact_mod_cast hch
  have hsub : k + (N - k) + 1 = N + 1 := by omega
  rw [hsub, Nat.factorial_succ N]
  push_cast
  have hpos_f : (0 : ℝ) < (N.factorial : ℝ) := by positivity
  have hpos_n : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  field_simp [hpos_f.ne', hpos_n.ne']
  nlinarith [hchR]

/-- Markov–Legendre Lipschitz bound on `[-1, 1]` deduced from `abs_legP'_le`. -/
theorem abs_legP_sub_le {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) (n : ℕ) :
    |legP n x - legP n y| ≤ ((n : ℝ) * ((n : ℝ) + 1) / 2) * |x - y| := by
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Icc (-1 : ℝ) 1) (f := legP n) (f' := legP' n)
    (fun z _ => (hasDerivAt_legP n z).hasDerivWithinAt)
    (fun z hz => by rw [Real.norm_eq_abs]; exact abs_legP'_le (abs_le.mpr hz) n)
    (convex_Icc (-1 : ℝ) 1) hy hx
  simpa only [Real.norm_eq_abs] using hmvt

/-- Perturbation bound for replacing `A^p` by `A0^p` in a symmetric `K × K` quadratic form. -/
theorem symm_quad_scale_pert {K : ℕ} (Q : Fin K → Fin K → ℝ) (hSym : ∀ i j, Q i j = Q j i)
    {s s0 δ : ℝ} (hs : |s - s0| ≤ δ) (m : Fin K → ℝ) :
    s0 * (∑ i, ∑ j, Q i j * m i * m j) -
      ∑ i, (δ * ∑ j, |Q i j|) * m i ^ 2 ≤
      s * (∑ i, ∑ j, Q i j * m i * m j) := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hs
  have hdiff : |(s - s0) * ∑ i, ∑ j, Q i j * m i * m j| ≤
      ∑ i, (δ * ∑ j, |Q i j|) * m i ^ 2 := by
    rw [abs_mul]
    have h1 : |∑ i, ∑ j, Q i j * m i * m j| ≤ ∑ i, ∑ j, |Q i j| * |m i| * |m j| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_mul]
    have h2 : (∑ i, ∑ j, |Q i j| * |m i| * |m j|) ≤ ∑ i, (∑ j, |Q i j|) * m i ^ 2 := by
      have hsq : ∀ i j, 2 * (|Q i j| * |m i| * |m j|) ≤ |Q i j| * m i ^ 2 + |Q i j| * m j ^ 2 := by
        intro i j
        have h := mul_nonneg (abs_nonneg (Q i j)) (sq_nonneg (|m i| - |m j|))
        have hexp_sq : |Q i j| * (|m i| - |m j|) ^ 2 =
            |Q i j| * |m i| ^ 2 + |Q i j| * |m j| ^ 2 - 2 * (|Q i j| * |m i| * |m j|) := by ring
        rw [sq_abs, sq_abs] at hexp_sq
        linarith
      have hsum_le : 2 * (∑ i, ∑ j, |Q i j| * |m i| * |m j|) ≤
          ∑ i, ∑ j, (|Q i j| * m i ^ 2 + |Q i j| * m j ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => hsq i j
      have hsym_sum : (∑ i, ∑ j, |Q i j| * m j ^ 2) = ∑ i, ∑ j, |Q i j| * m i ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hSym j i]
      have hrhs : (∑ i, ∑ j, (|Q i j| * m i ^ 2 + |Q i j| * m j ^ 2)) =
          2 * ∑ i, (∑ j, |Q i j|) * m i ^ 2 := by
        simp_rw [Finset.sum_add_distrib]
        rw [hsym_sum]
        simp_rw [← Finset.sum_mul]
        ring
      linarith
    have hm1 := mul_le_mul hs h1 (abs_nonneg _) hδ
    have hm2 := mul_le_mul_of_nonneg_left h2 hδ
    have heq_r : δ * (∑ i, (∑ j, |Q i j|) * m i ^ 2) = ∑ i, (δ * ∑ j, |Q i j|) * m i ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    linarith
  have hlo := (neg_abs_le ((s - s0) * ∑ i, ∑ j, Q i j * m i * m j))
  have halg : s * (∑ i, ∑ j, Q i j * m i * m j) =
      s0 * (∑ i, ∑ j, Q i j * m i * m j) + (s - s0) * (∑ i, ∑ j, Q i j * m i * m j) := by ring
  linarith [abs_le.mp hdiff]

/-- Symmetric matrix entry-rounding bound: if `B_clean` is symmetric and
`B i i + ∑_{j ≠ i} |B i j - B_clean i j| ≤ B_clean i i`, then `mᵀ B m ≤ mᵀ B_clean m`. -/
theorem symm_quad_round_le {K : ℕ} (B B_clean : Fin K → Fin K → ℝ)
    (hSym : ∀ i j, B i j - B_clean i j = B j i - B_clean j i)
    (hDiag : ∀ i, B i i + (∑ j ∈ Finset.univ.erase i, |B i j - B_clean i j|) ≤ B_clean i i)
    (m : Fin K → ℝ) :
    (∑ i, ∑ j, B i j * m i * m j) ≤ ∑ i, ∑ j, B_clean i j * m i * m j := by
  let D := fun i j => B_clean i j - B i j
  suffices h : 0 ≤ ∑ i, ∑ j, D i j * m i * m j by
    have heq : (∑ i, ∑ j, B_clean i j * m i * m j) - (∑ i, ∑ j, B i j * m i * m j) =
        ∑ i, ∑ j, D i j * m i * m j := by
      simp_rw [← Finset.sum_sub_distrib, D]; apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    linarith
  have hDsym : ∀ i j, D i j = D j i := fun i j => by dsimp [D]; linarith [hSym i j]
  have hDdiag : ∀ i, (∑ j ∈ Finset.univ.erase i, |D i j|) ≤ D i i := fun i => by
    have h := hDiag i
    have he : ∀ j, |B i j - B_clean i j| = |D i j| := fun j => by
      dsimp [D]; rw [abs_sub_comm]
    simp_rw [he] at h
    dsimp [D]; linarith
  have hsplit : (∑ i, ∑ j, D i j * m i * m j) =
      (∑ i, D i i * m i ^ 2) + ∑ i, ∑ j ∈ Finset.univ.erase i, D i j * m i * m j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    have h := Finset.add_sum_erase Finset.univ (fun j => D i j * m i * m j) (Finset.mem_univ i)
    rw [← h]; ring
  have hoff : -(∑ i, (∑ j ∈ Finset.univ.erase i, |D i j|) * m i ^ 2) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, D i j * m i * m j := by
    have hpt : ∀ i (j : Fin K),
        -(|D i j| * m i ^ 2 + |D i j| * m j ^ 2) ≤ 2 * (D i j * m i * m j) := by
      intro i j
      have h1 : -( |D i j| * |m i| * |m j| ) ≤ D i j * m i * m j := by
        have := neg_abs_le (D i j * m i * m j)
        rwa [abs_mul, abs_mul] at this
      have h2 := mul_nonneg (abs_nonneg (D i j)) (sq_nonneg (|m i| - |m j|))
      have hexp_sq : |D i j| * (|m i| - |m j|) ^ 2 =
          |D i j| * |m i| ^ 2 + |D i j| * |m j| ^ 2 - 2 * (|D i j| * |m i| * |m j|) := by ring
      rw [sq_abs, sq_abs] at hexp_sq
      linarith
    have hsum2 : -(∑ i, ∑ j ∈ Finset.univ.erase i, (|D i j| * m i ^ 2 + |D i j| * m j ^ 2)) ≤
        2 * ∑ i, ∑ j ∈ Finset.univ.erase i, D i j * m i * m j := by
      rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hpt i j
    have hsym_er : (∑ i, ∑ j ∈ Finset.univ.erase i, |D i j| * m j ^ 2) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, |D i j| * m i ^ 2 := by
      have hfull1 : ∀ f : Fin K → Fin K → ℝ,
          (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) = (∑ i, ∑ j, f i j) - ∑ i, f i i := by
        intro f
        have h : ∀ i, f i i + (∑ j ∈ Finset.univ.erase i, f i j) = ∑ j, f i j := fun i =>
          Finset.add_sum_erase Finset.univ (f i) (Finset.mem_univ i)
        linarith [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h i,
          Finset.sum_add_distrib (s := Finset.univ) (f := fun i => f i i)
            (g := fun i => ∑ j ∈ Finset.univ.erase i, f i j)]
      rw [hfull1 (fun i j => |D i j| * m j ^ 2), hfull1 (fun i j => |D i j| * m i ^ 2)]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [hDsym j i]
    have hlhs : (∑ i, ∑ j ∈ Finset.univ.erase i, (|D i j| * m i ^ 2 + |D i j| * m j ^ 2)) =
        2 * ∑ i, (∑ j ∈ Finset.univ.erase i, |D i j|) * m i ^ 2 := by
      simp_rw [Finset.sum_add_distrib]
      rw [hsym_er]
      simp_rw [← Finset.sum_mul]
      ring
    linarith
  have hdiag_dom : (∑ i, (∑ j ∈ Finset.univ.erase i, |D i j|) * m i ^ 2) ≤
      ∑ i, D i i * m i ^ 2 :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hDdiag i) (sq_nonneg _)
  linarith

/-- Finite unweighted Cauchy–Schwarz `(∑_{k : Fin K} c_k m_k)^2 ≤ K * ∑_k c_k^2 m_k^2`. -/
theorem fin_sum_mul_sq_le (K : ℕ) (c m : Fin K → ℝ) :
    (∑ k, c k * m k) ^ 2 ≤ (K : ℝ) * ∑ k, c k ^ 2 * m k ^ 2 := by
  have h := weighted_cauchy_schwarz_finset Finset.univ (fun _ : Fin K => (1 : ℝ))
    (fun k => c k * m k) (fun _ => 1) (fun _ _ => zero_le_one)
  simp only [one_mul, mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_pow] at h
  linarith

/-- Exact `LDLᵀ` plus strict diagonal-dominance certificate for positive semidefiniteness of a
symmetric `K × K` matrix `C`. -/
theorem psd_of_ldlt_add_diag_dom {K : ℕ} (C L E : Fin K → Fin K → ℝ) (d : Fin K → ℝ)
    (hd : ∀ r, 0 ≤ d r)
    (hE_sym : ∀ i j, E i j = E j i)
    (hE_dom : ∀ i, (∑ j ∈ Finset.univ.erase i, |E i j|) ≤ E i i)
    (hDecomp : ∀ i j, C i j = (∑ r, L i r * d r * L j r) + E i j)
    (m : Fin K → ℝ) :
    0 ≤ ∑ i, ∑ j, C i j * m i * m j := by
  simp_rw [hDecomp, add_mul, Finset.sum_add_distrib]
  have hldlt : 0 ≤ ∑ i, ∑ j, (∑ r, L i r * d r * L j r) * m i * m j := by
    have heq : (∑ i, ∑ j, (∑ r, L i r * d r * L j r) * m i * m j) =
        ∑ r, d r * (∑ i, L i r * m i) ^ 2 := by
      simp_rw [Finset.sum_mul]
      conv_lhs =>
        enter [2, i]
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro r _
      rw [pow_two, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      ring
    rw [heq]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hd r) (sq_nonneg _)
  have hE_nn : 0 ≤ ∑ i, ∑ j, E i j * m i * m j := by
    have h := symm_quad_round_le (fun _ _ => 0) E
      (fun i j => by simp [hE_sym i j])
      (fun i => by simpa [abs_neg] using hE_dom i) m
    simpa using h
  linarith

end GaloisForLFunctions.WindowTowerOfSpecZ
