import GaloisForLFunctions.RHTower.PrimeIndexedRVMSchattenInfrastructure
import GaloisForLFunctions.RHTower.XiHorizontalBound
import GaloisForLFunctions.RHTower.XiHorizontalRatioSelection
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.HTGeometry.DigammaAsymptotic
import GaloisForLFunctions.HTGeometry.GammaShiftRatioTube

/-!
# Quantitative Riemann--von Mangoldt remainder

The existing quarter-path formula, Backlund horizontal estimate, and quantitative vertical
digamma bound give the classical `O(log T)` remainder in the exact smooth normalization used by
the prime-indexed RVM skeleton.  A good-height squeeze transfers the estimate from zero-free
horizontal contours to every sufficiently large height.
-/

open Complex Filter Topology intervalIntegral MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem abs_re_digamma_one_add_vertical_sub_log_le {t : ℝ} (ht : 1 ≤ t) :
    |(Complex.digamma ((1 : ℂ) + (t : ℂ) * I)).re - Real.log t|
      ≤ (2 + Real.pi) / t := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hnorm0 : 0 < ‖(1 : ℂ) + (t : ℂ) * I‖ := by
    rw [norm_pos_iff]
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hsq : ‖(1 : ℂ) + (t : ℂ) * I‖ ^ 2 = 1 ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hlognorm : (1 / 2 : ℝ) * Real.log (1 ^ 2 + t ^ 2) =
      Real.log ‖(1 : ℂ) + (t : ℂ) * I‖ := by
    rw [← hsq, Real.log_pow]
    ring
  have hdig := re_digamma_vertical_bound_uncond (σ := 1) (t := t) (by norm_num) ht0
  rw [hlognorm] at hdig
  have hnorm := abs_log_norm_vertical_sub_le (M := 1) (σ := 1) (t := t)
    (by norm_num) (by norm_num) ht
  have htri : |(Complex.digamma ((1 : ℂ) + (t : ℂ) * I)).re - Real.log t|
      ≤ |(Complex.digamma ((1 : ℂ) + (t : ℂ) * I)).re
            - Real.log ‖(1 : ℂ) + (t : ℂ) * I‖|
        + |Real.log ‖(1 : ℂ) + (t : ℂ) * I‖ - Real.log t| := by
    set A : ℝ := (Complex.digamma ((1 : ℂ) + (t : ℂ) * I)).re
    set B : ℝ := Real.log ‖(1 : ℂ) + (t : ℂ) * I‖
    set C : ℝ := Real.log t
    calc
      |A - C| = |(A - B) + (B - C)| := by congr 1; ring
      _ ≤ |A - B| + |B - C| := abs_add_le _ _
  refine htri.trans ?_
  have hinv2 : 1 / t ^ 2 ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) ht0]
    nlinarith
  have hpi : 0 < Real.pi := Real.pi_pos
  calc
    |(Complex.digamma ((1 : ℂ) + (t : ℂ) * I)).re
          - Real.log ‖(1 : ℂ) + (t : ℂ) * I‖|
        + |Real.log ‖(1 : ℂ) + (t : ℂ) * I‖ - Real.log t|
      ≤ (1 / t ^ 2 + Real.pi / (2 * t)) + 1 ^ 2 / t := add_le_add hdig hnorm
    _ ≤ (2 + Real.pi) / t := by
      rw [one_pow]
      have hhalf : Real.pi / (2 * t) ≤ Real.pi / t := by
        rw [div_le_div_iff₀ (by positivity) ht0]
        nlinarith
      calc
        1 / t ^ 2 + Real.pi / (2 * t) + 1 / t
            ≤ 1 / t + Real.pi / t + 1 / t := by linarith
        _ = (2 + Real.pi) / t := by field_simp; ring

theorem exists_abs_gammaVerticalPhase_one_sub_main_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |gammaVerticalPhase 1 T - (T * Real.log T - T)| ≤ C * Real.log T := by
  set f : ℝ → ℝ := fun t =>
    (Complex.digamma ((1 : ℂ) + (t : ℂ) * I)).re with hf
  set A : ℝ := |(∫ t in (0 : ℝ)..1, f t) + 1| with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := A / Real.log 2 + (2 + Real.pi) with hC
  have hC0 : 0 < C := by
    rw [hC]
    have : 0 ≤ A / Real.log 2 := div_nonneg hA0 hlog2.le
    nlinarith [Real.pi_pos]
  refine ⟨C, hC0, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog2T : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlogT0 : 0 < Real.log T := lt_of_lt_of_le hlog2 hlog2T
  have hcf : Continuous f := by
    rw [hf]
    exact continuous_digammaVerticalRe (by norm_num)
  have hclog : ContinuousOn Real.log (Set.uIcc (1 : ℝ) T) :=
    Real.continuousOn_log.mono fun t htmem => by
      rw [Set.uIcc_of_le hT1, Set.mem_Icc] at htmem
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
  have hlogint : IntervalIntegrable Real.log volume (1 : ℝ) T :=
    hclog.intervalIntegrable
  have hdiffint : IntervalIntegrable (fun t => f t - Real.log t) volume (1 : ℝ) T :=
    (hcf.intervalIntegrable _ _).sub hlogint
  have hmajorint : IntervalIntegrable (fun t : ℝ => (2 + Real.pi) / t) volume 1 T := by
    refine (ContinuousOn.intervalIntegrable ?_)
    exact continuousOn_const.div continuousOn_id (fun t htmem hzero => by
      rw [Set.uIcc_of_le hT1, Set.mem_Icc] at htmem
      linarith)
  have htail : |∫ t in (1 : ℝ)..T, (f t - Real.log t)|
      ≤ (2 + Real.pi) * Real.log T := by
    rw [← Real.norm_eq_abs]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le hT1 ?_ hmajorint) ?_
    · filter_upwards [] with t htmem
      rw [Real.norm_eq_abs]
      simpa [hf] using abs_re_digamma_one_add_vertical_sub_log_le htmem.1.le
    · have hnot : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) T := by
        rw [Set.uIcc_of_le hT1, Set.mem_Icc]
        simp
      have hone := integral_one_div (a := (1 : ℝ)) (b := T) hnot
      have hratio : T / (1 : ℝ) = T := by ring
      have hmajorEq : (∫ t in (1 : ℝ)..T, (2 + Real.pi) / t)
          = (2 + Real.pi) * ∫ t in (1 : ℝ)..T, 1 / t := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun t _ => ?_
        ring
      rw [hmajorEq, hone, hratio]
  have hsplit : gammaVerticalPhase 1 T
      = (∫ t in (0 : ℝ)..1, f t) + ∫ t in (1 : ℝ)..T, f t := by
    rw [gammaVerticalPhase, ← hf]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hcf.intervalIntegrable 0 1) (hcf.intervalIntegrable 1 T)).symm
  have hlog : ∫ t in (1 : ℝ)..T, Real.log t = T * Real.log T - T + 1 := by
    rw [integral_log]
    simp
  have htailSplit : ∫ t in (1 : ℝ)..T, f t
      = (∫ t in (1 : ℝ)..T, (f t - Real.log t))
        + (T * Real.log T - T + 1) := by
    have hsub := intervalIntegral.integral_sub (hcf.intervalIntegrable 1 T) hlogint
    rw [hlog] at hsub
    linarith
  rw [hsplit, htailSplit]
  have heq : (∫ t in (0 : ℝ)..1, f t) +
        ((∫ t in (1 : ℝ)..T, f t - Real.log t) + (T * Real.log T - T + 1))
        - (T * Real.log T - T)
      = ((∫ t in (0 : ℝ)..1, f t) + 1)
        + (∫ t in (1 : ℝ)..T, f t - Real.log t) := by ring
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  have hAhead : A ≤ (A / Real.log 2) * Real.log T := by
    calc
      A = (A / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (A / Real.log 2) * Real.log T :=
        mul_le_mul_of_nonneg_left hlog2T (div_nonneg hA0 hlog2.le)
  rw [← hA]
  rw [hC]
  nlinarith

theorem gammaVerticalPhase_routeKRVM_main_identity {T : ℝ} (hT : 0 < T) :
    (T / 2 * Real.log (T / 2) - T / 2) - T * Real.log Real.pi / 2
      = Real.pi * (routeKSmoothRVMCount T - 7 / 8) := by
  have hT2 : 0 < T / 2 := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have harg : T / routeKRVMBase = ((T / 2) / Real.pi) / Real.exp 1 := by
    rw [routeKRVMBase]
    field_simp
  have hlog : Real.log (T / routeKRVMBase)
      = Real.log (T / 2) - Real.log Real.pi - 1 := by
    rw [harg, Real.log_div (div_pos hT2 hpi).ne' he.ne',
      Real.log_div hT2.ne' hpi.ne', Real.log_exp]
  rw [routeKSmoothRVMCount, hlog]
  field_simp [Real.pi_ne_zero]
  ring

theorem exists_abs_vertical_xi_sub_routeKRVM_main_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 4 ≤ T →
      |(∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re)
          - Real.pi * (routeKSmoothRVMCount T - 7 / 8)| ≤ C * Real.log T := by
  obtain ⟨Cγ, hCγ, hγ⟩ := exists_abs_gammaVerticalPhase_one_sub_main_le
  refine ⟨Cγ + 2 * Real.pi, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hhalf : (2 : ℝ) ≤ T / 2 := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hloghalf : Real.log (T / 2) ≤ Real.log T :=
    Real.log_le_log (by positivity) (by linarith)
  have hphase := hγ (T / 2) hhalf
  have hphase' : |gammaVerticalPhase 1 (T / 2)
      - (T / 2 * Real.log (T / 2) - T / 2)| ≤ Cγ * Real.log T := by
    exact hphase.trans (mul_le_mul_of_nonneg_left hloghalf hCγ.le)
  have hrat := abs_integral_rational_head_le T
  have hzeta := abs_integral_re_logDeriv_zeta_two_le T
  have hsplit := integral_re_logDeriv_xi_two T
  have hmain := gammaVerticalPhase_routeKRVM_main_identity hT0
  rw [hsplit]
  have heq :
      (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2)))
          - T * Real.log Real.pi / 2 + gammaVerticalPhase 1 (T / 2)
          + (∫ y in (0 : ℝ)..T,
              (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re)
          - Real.pi * (routeKSmoothRVMCount T - 7 / 8)
        = (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2)))
          + (gammaVerticalPhase 1 (T / 2)
              - (T / 2 * Real.log (T / 2) - T / 2))
          + (∫ y in (0 : ℝ)..T,
              (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re) := by
    rw [← hmain]
    ring
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) hzeta).trans ?_
  nlinarith [Real.pi_pos]

theorem exists_abs_xiZeroCount_sub_routeKSmoothRVMCount_admissible_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 4 ≤ T →
      (∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |(xiZeroCount T : ℝ) - routeKSmoothRVMCount T| ≤ C * Real.log T := by
  obtain ⟨Cv, hCv, hv⟩ := exists_abs_vertical_xi_sub_routeKRVM_main_le
  obtain ⟨Ch, hCh, hh⟩ := exists_horizontal_xi_bound
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨(Cv + Ch + Real.pi) / Real.pi, by positivity, fun T hT hne => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    linarith [Real.exp_one_lt_d9]
  set V : ℝ := ∫ y in (0 : ℝ)..T,
    (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re with hV
  set H : ℝ := ∫ x in (1 / 2 : ℝ)..2,
    (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im with hH
  have hvb : |V - Real.pi * (routeKSmoothRVMCount T - 7 / 8)|
      ≤ Cv * Real.log T := by simpa [hV] using hv T hT
  have hhb : |H| ≤ Ch * Real.log T := by simpa [hH] using hh T hT hne
  have hmass := two_pi_mul_xiSymmetricMass hT0 hne
  have hsym := xiSymmetricMass_eq_two_mul_xiZeroCount hT0
  have hsymR : (xiSymmetricMass T : ℝ) = 2 * (xiZeroCount T : ℝ) := by
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) hsym
  rw [hsymR, ← hV, ← hH] at hmass
  have hscaledEq : Real.pi * ((xiZeroCount T : ℝ) - routeKSmoothRVMCount T)
      = (V - Real.pi * (routeKSmoothRVMCount T - 7 / 8)) - H
        - Real.pi * (7 / 8) := by
    nlinarith [hmass]
  have hscaled : |Real.pi * ((xiZeroCount T : ℝ) - routeKSmoothRVMCount T)|
      ≤ (Cv + Ch + Real.pi) * Real.log T := by
    rw [hscaledEq]
    calc
      |(V - Real.pi * (routeKSmoothRVMCount T - 7 / 8)) - H - Real.pi * (7 / 8)|
          ≤ |(V - Real.pi * (routeKSmoothRVMCount T - 7 / 8)) - H|
              + |Real.pi * (7 / 8)| := by
            simpa using abs_sub_le
              ((V - Real.pi * (routeKSmoothRVMCount T - 7 / 8)) - H) 0
              (Real.pi * (7 / 8))
      _ ≤ (|V - Real.pi * (routeKSmoothRVMCount T - 7 / 8)| + |H|)
              + Real.pi * (7 / 8) := by
            gcongr
            · simpa using abs_sub_le
                (V - Real.pi * (routeKSmoothRVMCount T - 7 / 8)) 0 H
            · rw [abs_of_nonneg]
              positivity
      _ ≤ (Cv + Ch + Real.pi) * Real.log T := by
            nlinarith [hvb, hhb, hCv, hCh, hpi]
  rw [abs_mul, abs_of_pos hpi] at hscaled
  rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
  nlinarith

theorem routeKSmoothRVMCount_sub_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    routeKSmoothRVMCount b - routeKSmoothRVMCount a
      = ((b * Real.log b - a * Real.log a)
          - (b - a) * Real.log routeKRVMBase) / (2 * Real.pi) := by
  rw [routeKSmoothRVMCount, routeKSmoothRVMCount,
    Real.log_div hb.ne' routeKRVMBase_pos.ne',
    Real.log_div ha.ne' routeKRVMBase_pos.ne']
  field_simp [Real.pi_ne_zero]
  ring

theorem routeKSmoothRVMCount_sub_le_log_of_mem_unitAbove
    {T U : ℝ} (hT : 4 ≤ T) (hTU : T ≤ U) (hUT : U ≤ T + 1) :
    routeKSmoothRVMCount U - routeKSmoothRVMCount T ≤ Real.log T := by
  have hT0 : 0 < T := by linarith
  have hU0 : 0 < U := lt_of_lt_of_le hT0 hTU
  have hlogbase : 0 ≤ Real.log routeKRVMBase :=
    Real.log_nonneg one_lt_routeKRVMBase.le
  have hsub := routeKSmoothRVMCount_sub_eq hT0 hU0
  have hUlog : U * Real.log U ≤ (T + 1) * Real.log (T + 1) :=
    mul_log_mono (by linarith) hUT
  have hsucc := succ_mul_log_le (by linarith : (1 : ℝ) ≤ T)
  have hpi : 3 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  rw [hsub, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hnonneg : 0 ≤ (U - T) * Real.log routeKRVMBase :=
    mul_nonneg (sub_nonneg.mpr hTU) hlogbase
  nlinarith

theorem routeKSmoothRVMCount_sub_le_log_of_mem_unitBelow
    {L T : ℝ} (hT : 4 ≤ T) (hLT : T - 1 ≤ L) (hTL : L ≤ T) :
    routeKSmoothRVMCount T - routeKSmoothRVMCount L ≤ Real.log T := by
  have hT0 : 0 < T := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hlogbase : 0 ≤ Real.log routeKRVMBase :=
    Real.log_nonneg one_lt_routeKRVMBase.le
  have hsub := routeKSmoothRVMCount_sub_eq hL0 hT0
  have hpred := pred_mul_log_ge (by linarith : (2 : ℝ) ≤ T)
  have hLlog : (T - 1) * Real.log (T - 1) ≤ L * Real.log L :=
    mul_log_mono (by linarith) hLT
  have hpi : 3 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  rw [hsub, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hnonneg : 0 ≤ (T - L) * Real.log routeKRVMBase :=
    mul_nonneg (sub_nonneg.mpr hTL) hlogbase
  nlinarith

/-- The classical Riemann--von Mangoldt remainder in the card's exact smooth normalization. -/
theorem exists_xiZeroCount_routeKSmoothRVMCount_log_remainder :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      |(xiZeroCount T : ℝ) - routeKSmoothRVMCount T| ≤ C * Real.log T := by
  obtain ⟨Cadm, hCadm, hadm⟩ :=
    exists_abs_xiZeroCount_sub_routeKSmoothRVMCount_admissible_le
  obtain ⟨_Cgood, _hCgood, n₀, hgood⟩ := exists_good_height
  set T₀ : ℝ := max (max (n₀ + 1) 8) (routeKRVMBase + 2) with hT₀
  refine ⟨2 * Cadm + 1, by positivity, T₀, ?_, fun T hT => ?_⟩
  · rw [hT₀]
    exact le_trans (by norm_num) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hT8 : (8 : ℝ) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hT₀ ▸ hT)
  have hn₀pred : n₀ ≤ T - 1 := by
    have : n₀ + 1 ≤ T :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hT₀ ▸ hT)
    linarith
  have hn₀T : n₀ ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlogT0 : 0 < Real.log T := Real.log_pos (by linarith)
  obtain ⟨Tplus, hTplusL, hTplusU, hminusPlus, _hplusPlus, _hsumPlus⟩ :=
    hgood T hn₀T
  obtain ⟨Tminus, hTminusL, hTminusU, hminusMinus, _hplusMinus, _hsumMinus⟩ :=
    hgood (T - 1) hn₀pred
  have hTminusU' : Tminus ≤ T := by linarith
  have hTplus4 : (4 : ℝ) ≤ Tplus := by linarith
  have hTminus4 : (4 : ℝ) ≤ Tminus := by linarith
  have hnePlus : ∀ x : ℝ, xi ((x : ℂ) + (Tplus : ℂ) * I) ≠ 0 :=
    xi_ne_zero_horizontal_of_avoids_zero_ordinates hminusPlus
  have hneMinus : ∀ x : ℝ, xi ((x : ℂ) + (Tminus : ℂ) * I) ≠ 0 :=
    xi_ne_zero_horizontal_of_avoids_zero_ordinates hminusMinus
  have hplus := hadm Tplus hTplus4 hnePlus
  have hminus := hadm Tminus hTminus4 hneMinus
  rw [abs_le] at hplus hminus
  have hcountPlus : (xiZeroCount T : ℝ) ≤ (xiZeroCount Tplus : ℝ) := by
    exact_mod_cast xiZeroCount_mono hTplusL
  have hcountMinus : (xiZeroCount Tminus : ℝ) ≤ (xiZeroCount T : ℝ) := by
    exact_mod_cast xiZeroCount_mono hTminusU'
  have hMplus : routeKSmoothRVMCount Tplus - routeKSmoothRVMCount T ≤ Real.log T :=
    routeKSmoothRVMCount_sub_le_log_of_mem_unitAbove (by linarith) hTplusL hTplusU
  have hMminus : routeKSmoothRVMCount T - routeKSmoothRVMCount Tminus ≤ Real.log T :=
    routeKSmoothRVMCount_sub_le_log_of_mem_unitBelow (by linarith) hTminusL hTminusU'
  have hTplus0 : 0 < Tplus := by linarith
  have hTminus0 : 0 < Tminus := by linarith
  have hlogPlus : Real.log Tplus ≤ 2 * Real.log T := by
    have hsq : Tplus ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
    calc
      Real.log Tplus ≤ Real.log (T ^ 2) := Real.log_le_log hTplus0 hsq
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have hlogMinus : Real.log Tminus ≤ Real.log T :=
    Real.log_le_log hTminus0 hTminusU'
  have hCadmPlus : Cadm * Real.log Tplus ≤ 2 * Cadm * Real.log T := by
    nlinarith [mul_le_mul_of_nonneg_left hlogPlus hCadm.le]
  have hCadmMinus : Cadm * Real.log Tminus ≤ Cadm * Real.log T :=
    mul_le_mul_of_nonneg_left hlogMinus hCadm.le
  rw [abs_le]
  constructor
  · nlinarith [hminus.1, hcountMinus, hMminus, hCadmMinus]
  · nlinarith [hplus.2, hcountPlus, hMplus, hCadmPlus]

end RHTower
