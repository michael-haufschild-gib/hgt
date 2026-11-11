import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTwistedMomentErrorKeepsItsDerivatives
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheLinearDetectorHasSmallTaperError

/-!
# Uniform remainder for the actual three-moment detector

Quadratic homogeneity admits the residual coefficients of size two.
The common-taper remainder controls all three moments and both derivatives;
the actual edge integrals supply the remaining sublinear error.
-/

open Complex Filter MeasureTheory Set Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem field_scale (N : ℕ) (w : ℕ → ℝ) (c : ℝ) (z : ℂ) (t : ℝ) :
    twistedMomentField N (fun n => c * w n) z t = (c : ℂ) * twistedMomentField N w z t := by
  unfold twistedMomentField edPoly
  simp only [Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum]
  ring

private theorem iteratedDeriv_scale (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => c * f z) = fun z => c * iteratedDeriv n f z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext z
    exact deriv_const_mul_field c

private theorem holomorphicMoment_scale (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) (c : ℝ) :
    holomorphicTwistedMoment p q η N (fun n => c * w n) =
      fun z => (c : ℂ) ^ 2 * holomorphicTwistedMoment p q η N w z := by
  funext z
  unfold holomorphicTwistedMoment
  simp_rw [field_scale]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

private theorem holomorphicGcdSum_scale (a b : ℂ) (N : ℕ) (w : ℕ → ℝ) (c : ℝ) :
    holomorphicGcdSum a b N (fun n => c * w n) = (c : ℂ) ^ 2 * holomorphicGcdSum a b N w := by
  unfold holomorphicGcdSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  ring

private theorem holomorphicMain_scale (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) (c : ℝ) :
    holomorphicTwistedMomentMain p q η N (fun n => c * w n) =
      fun z => (c : ℂ) ^ 2 * holomorphicTwistedMomentMain p q η N w z := by
  funext z
  unfold holomorphicTwistedMomentMain
  rw [holomorphicGcdSum_scale, holomorphicGcdSum_scale]
  ring

/-- Every literal remainder jet is quadratic in a common real coefficient scale. -/
theorem twistedMomentErrorJet_scale (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) (c : ℝ)
    (n : ℕ) (d : ℝ) :
    twistedMomentErrorJet p q η N (fun k => c * w k) n d =
      c ^ 2 * twistedMomentErrorJet p q η N w n d := by
  unfold twistedMomentErrorJet realTwistedMomentJet realTwistedMomentMainJet
  rw [holomorphicMoment_scale, holomorphicMain_scale, iteratedDeriv_scale, iteratedDeriv_scale]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- One taper controls the first three remainder jets for coefficients bounded by two. -/
theorem exists_twistedMoment_three_jet_error_bound_two {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) :
    ∃ a C : ℝ, 0 < a ∧ a < 1 ∧ 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (d q : ℝ) (N : ℕ) (w : ℕ → ℝ),
        T ≤ q → q ≤ 2 * T → 1 / T ≤ d → d ≤ 1 / 40 → (N : ℝ) ≤ T ^ θ →
        (∀ n ∈ Finset.Icc 1 N, |w n| ≤ 2) →
        |twistedMomentErrorJet T q (T ^ a) N w 0 d| ≤ C ∧
        |twistedMomentErrorJet T q (T ^ a) N w 1 d| ≤ C ∧
        |twistedMomentErrorJet T q (T ^ a) N w 2 d| ≤ C := by
  obtain ⟨a, C, ha, ha1, hC, he⟩ :=
    exists_twistedMoment_first_three_jet_power_saving hθ0 hθ 0 le_rfl
  refine ⟨a, 4 * C, ha, ha1, by positivity, ?_⟩
  filter_upwards [he] with T hT
  intro d q N w hq hq2 hd hd40 hN hw
  have hv : ∀ n ∈ Finset.Icc 1 N, |w n / 2| ≤ 1 := by
    intro n hn
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_one (by norm_num)).mpr (hw n hn)
  have hh := hT d q N (fun n => w n / 2) hq hq2 hd hd40 hN hv
  simp only [neg_zero, Real.rpow_zero, mul_one] at hh
  have hscale (j : ℕ) : |twistedMomentErrorJet T q (T ^ a) N w j d| =
      4 * |twistedMomentErrorJet T q (T ^ a) N (fun n => w n / 2) j d| := by
    have hw' : (fun n => 2 * (w n / 2)) = w := by funext n; ring
    have hs := twistedMomentErrorJet_scale T q (T ^ a) N (fun n => w n / 2) 2 j d
    rw [hw'] at hs
    rw [hs, abs_mul]
    norm_num
  exact ⟨(hscale 0).trans_le (mul_le_mul_of_nonneg_left hh.1 (by norm_num)),
    (hscale 1).trans_le (mul_le_mul_of_nonneg_left hh.2.1 (by norm_num)),
    (hscale 2).trans_le (mul_le_mul_of_nonneg_left hh.2.2 (by norm_num))⟩

/-- The exact direct and reflected gcd expression selected by the detector.
The coefficients remain fixed while taking each displacement derivative. -/
def detectorThreeMomentMain (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) (d lam : ℝ) : ℝ :=
  realTwistedMomentMainJet p q η N (detectorResidualWeights lam w) 0 d - lam / 2 *
    (realTwistedMomentMainJet p q η N w 1 d -
      realTwistedMomentMainJet p q η N (detectorCorrectionWeights lam w) 1 d +
      realTwistedMomentMainJet p q η N (detectorResidualWeights lam w) 1 d) +
    lam ^ 2 / 4 * realTwistedMomentMainJet p q η N w 2 d

/-- Uniform sublinear error reduces the literal linear detector to its explicit gcd main terms. -/
theorem exists_linearDetector_main_remainder_bound {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) :
    ∃ a r C : ℝ, 0 < a ∧ a < 1 ∧ 0 < r ∧ 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (q d lam : ℝ) (N : ℕ),
        T ≤ q → q ≤ 2 * T → 1 / T ≤ d → d ≤ min r (1 / 40) →
        1 < N → (N : ℝ) ≤ T ^ θ → 0 ≤ lam → lam ≤ 1 → lam * Real.log N ≤ 1 →
        |(∫ t, blockWindow T q (T ^ a) t *
          ‖(riemannZeta (displacedLinePt d t) + (lam : ℂ) * deriv riemannZeta (displacedLinePt d t)) *
            edPoly (fun n => (linearDetectorWeights N d n : ℂ)) (Finset.Icc 1 N)
              (displacedLinePt d t)‖ ^ 2) -
          detectorThreeMomentMain T q (T ^ a) N (linearDetectorWeights N d) d lam| ≤
          C * T ^ (7 / 8 : ℝ) := by
  obtain ⟨a, E, ha, ha1, hE, he⟩ := exists_twistedMoment_three_jet_error_bound_two hθ0 hθ
  obtain ⟨r, C, hr, hrhalf, hC, htaper⟩ := exists_linearDetector_taper_error_bound
  refine ⟨a, r, 11 * E / 4 + C, ha, ha1, hr, by positivity, ?_⟩
  filter_upwards [he, eventually_ge_atTop (16 : ℝ), eventually_rpow_le_quarter ha1]
    with T herror hT hηT
  intro q d lam N hq hq2 hdT hd hN hNT hlam hlam1 hlog
  have hT0 : 0 < T := by linarith only [hT]
  have hT1 : 1 ≤ T := by linarith only [hT]
  have hd0 : 0 < d := (one_div_pos.mpr hT0).trans_le hdT
  have hd40 : d ≤ 1 / 40 := hd.trans (min_le_right _ _)
  have hdr : |d| ≤ r := by rw [abs_of_pos hd0]; exact hd.trans (min_le_left _ _)
  have hd4 : |d| < 1 / 4 := by rw [abs_of_pos hd0]; linarith only [hd40]
  have hη : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  have hη1 : 1 ≤ T ^ a := Real.one_le_rpow hT1 ha.le
  have hNsqrt : (N : ℝ) ≤ T ^ (1 / 2 : ℝ) :=
    hNT.trans (Real.rpow_le_rpow_of_exponent_le hT1 hθ.le)
  have hw : ∀ n ∈ Finset.Icc 1 N, |linearDetectorWeights N d n| ≤ (n : ℝ) ^ (-d) :=
    fun n hn => abs_linearDetectorWeights_le hN d (Finset.mem_Icc.mp hn).1
  have hnscale (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : (n : ℝ) ^ (-d) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (Finset.mem_Icc.mp hn).1) (neg_nonpos.mpr hd0.le)
  have hw2 : ∀ n ∈ Finset.Icc 1 N, |linearDetectorWeights N d n| ≤ 2 := by
    intro n hn
    exact ((hw n hn).trans (hnscale n hn)).trans (by norm_num)
  have hc2 : ∀ n ∈ Finset.Icc 1 N,
      |detectorCorrectionWeights lam (linearDetectorWeights N d) n| ≤ 2 := by
    intro n hn
    exact ((abs_detectorCorrectionWeights_le hlam hlog hw n hn).trans
      (hnscale n hn)).trans (by norm_num)
  have hr2 : ∀ n ∈ Finset.Icc 1 N,
      |detectorResidualWeights lam (linearDetectorWeights N d) n| ≤ 2 := by
    intro n hn
    have hh := (abs_half_detectorResidualWeights_le hlam hlog hw n hn).trans (hnscale n hn)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    linarith only [hh]
  have eF := herror d q N (linearDetectorWeights N d) hq hq2 hdT hd40 hNT hw2
  have eG := herror d q N (detectorCorrectionWeights lam (linearDetectorWeights N d))
    hq hq2 hdT hd40 hNT hc2
  have eH := herror d q N (detectorResidualWeights lam (linearDetectorWeights N d))
    hq hq2 hdT hd40 hNT hr2
  have hte := htaper T q (T ^ a) d lam N hT hq hq2 hη1
    (by linarith only [hηT, hT]) hdr hN hNsqrt hlam hlam1 hlog
  let e (j : ℕ) (w : ℕ → ℝ) := twistedMomentErrorJet T q (T ^ a) N w j d
  let w := linearDetectorWeights N d
  let g := detectorCorrectionWeights lam w
  let v := detectorResidualWeights lam w
  change |e 0 w| ≤ E ∧ |e 1 w| ≤ E ∧ |e 2 w| ≤ E at eF
  change |e 0 g| ≤ E ∧ |e 1 g| ≤ E ∧ |e 2 g| ≤ E at eG
  change |e 0 v| ≤ E ∧ |e 1 v| ≤ E ∧ |e 2 v| ≤ E at eH
  have hcomb : |e 1 w - e 1 g + e 1 v| ≤ 3 * E := by
    exact ((abs_add_le _ _).trans (add_le_add_right (abs_sub _ _) _)).trans
      (by change _ ≤ _; linarith only [eF.2.1, eG.2.1, eH.2.1])
  have hlam2 : lam ^ 2 ≤ 1 := by nlinarith only [hlam, hlam1]
  have herrors : |e 0 v - lam / 2 * (e 1 w - e 1 g + e 1 v) + lam ^ 2 / 4 * e 2 w| ≤
      11 * E / 4 := by
    refine ((abs_add_le _ _).trans (add_le_add_right (abs_sub _ _) _)).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ lam / 2),
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ lam ^ 2 / 4)]
    calc
      _ ≤ E + lam / 2 * (3 * E) + lam ^ 2 / 4 * E :=
        add_le_add (add_le_add eH.1 (mul_le_mul_of_nonneg_left hcomb (by positivity)))
          (mul_le_mul_of_nonneg_left eF.2.2 (by positivity))
      _ ≤ E + 1 / 2 * (3 * E) + 1 / 4 * E := by gcongr
      _ = _ := by ring
  have hpow : 1 ≤ T ^ (7 / 8 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  have hi := integral_mollifiedDetector_three_moments (p := T) (q := q) hη N w hd4 lam
  rw [← realTwistedMomentJet_zero hd0 (by linarith only [hd40]) T q (T ^ a) N v] at hi
  have hid : (∫ t, blockWindow T q (T ^ a) t *
      ‖(riemannZeta (displacedLinePt d t) + (lam : ℂ) * deriv riemannZeta (displacedLinePt d t)) *
        edPoly (fun n => (w n : ℂ)) (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2) -
      detectorThreeMomentMain T q (T ^ a) N w d lam =
      (e 0 v - lam / 2 * (e 1 w - e 1 g + e 1 v) + lam ^ 2 / 4 * e 2 w) +
      (lam * (∫ t, iteratedDeriv 1 (blockWindow T q (T ^ a)) t *
        (mollifiedLineJet N w 0 (d : ℂ) t * conj (mollifiedLineJet N g 0 (d : ℂ) t)).im) +
        lam ^ 2 / 4 * (∫ t, iteratedDeriv 2 (blockWindow T q (T ^ a)) t *
          ‖mollifiedLineJet N w 0 (d : ℂ) t‖ ^ 2)) := by
    rw [hi]
    dsimp only [detectorThreeMomentMain, e, twistedMomentErrorJet, v, g]
    ring
  rw [hid]
  refine ((abs_add_le _ _).trans (add_le_add herrors hte)).trans ?_
  calc
    _ ≤ (11 * E / 4) * T ^ (7 / 8 : ℝ) + C * T ^ (7 / 8 : ℝ) := by
      gcongr
      exact le_mul_of_one_le_right (by positivity) hpow
    _ = _ := by ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
