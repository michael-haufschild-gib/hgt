import GaloisForLFunctions.HTGeometry.GammaShiftLadder
import GaloisForLFunctions.HTGeometry.DigammaVerticalUniformLog
import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# Summable archimedean tail for vertical HCF differences

The HCF cross-height source must take a vertical difference before it is
continued to the divisor.  `logDeriv Γℝ` itself grows like `log |t|`; this
module proves that the height-two difference has the summable `O(1/|t|)`
tail.  Height two is forced by the `s / 2` argument of `Γℝ`.

This resolves only the archimedean tail obligation.  It supplies neither the
required finite quadratic source trace nor its continuation estimate.
-/

open Complex

namespace RHTower

noncomputable section

/-- A height-two difference cancels the logarithmic archimedean growth. -/
theorem exists_norm_logDeriv_GammaR_vertical_two_shift_le :
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧ ∀ s : ℂ, 0 < s.re → R ≤ ‖s‖ →
      ‖logDeriv Gammaℝ (s + 2 * I) - logDeriv Gammaℝ s‖ ≤ K / ‖s‖ := by
  obtain ⟨K, R, hK, hR, htail⟩ :=
    GaloisForLFunctions.HTGeometry.exists_norm_digamma_vertical_unit_shift_le
  refine ⟨K, 2 * R, hK, ?_, ?_⟩
  · linarith
  · intro s hs hsize
    have hsHalf : 0 < (s / 2).re := by
      rw [Complex.div_re]
      norm_num
      linarith
    have hsizeHalf : R ≤ ‖s / 2‖ := by
      rw [Complex.norm_div]
      norm_num
      linarith
    have htail' := htail (s / 2) hsHalf hsizeHalf
    have hshift : (s + 2 * I) / 2 = s / 2 + I := by ring
    rw [logDeriv_Gammaℝ_digamma (by simpa using hs),
      logDeriv_Gammaℝ_digamma hs, hshift]
    have hrewrite :
        (Complex.digamma (s / 2 + I) / 2 - (Real.log Real.pi : ℂ) / 2) -
            (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) =
          (Complex.digamma (s / 2 + I) - Complex.digamma (s / 2)) / 2 := by
      ring
    rw [hrewrite, Complex.norm_div]
    norm_num
    rw [show ‖s / 2‖ = ‖s‖ / 2 by rw [Complex.norm_div]; norm_num] at htail'
    have hnorm : 0 < ‖s‖ := by
      have : 0 < 2 * R := by nlinarith
      exact this.trans_le hsize
    calc
      ‖(s / 2 + I).digamma - (s / 2).digamma‖ / 2 ≤
          (K / (‖s‖ / 2)) / 2 :=
        div_le_div_of_nonneg_right htail' (by norm_num)
      _ = K / ‖s‖ := by
        field_simp

/-- On the safe vertical line, every short positive height shift has a
uniformly bounded archimedean increment.  Unlike the height-two tail, this is
an interval family and is therefore compatible with a noncancelling positive
cross-height trace. -/
theorem exists_norm_logDeriv_GammaR_vertical_unit_interval_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t h : ℝ, 2 ≤ t → 0 ≤ h → h ≤ 1 →
      ‖logDeriv Gammaℝ ((3 / 2 : ℂ) + ((t + h : ℝ) : ℂ) * I) -
          logDeriv Gammaℝ ((3 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  obtain ⟨C, hC, hdigamma⟩ :=
    GaloisForLFunctions.HTGeometry.exists_uniform_bound_digamma_sub_vertLog
      (M := 1) (by norm_num)
  refine ⟨C + 1 / 2, by positivity, ?_⟩
  intro t h ht hh0 hh1
  have ht0 : 0 < t := by linarith
  have hu : 1 ≤ t / 2 := by linarith
  have hv : 1 ≤ (t + h) / 2 := by linarith
  have hσ0 : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have hσ1 : (3 / 4 : ℝ) ≤ 1 := by norm_num
  have hψu := hdigamma (3 / 4) (t / 2) hσ0 hσ1 hu
  have hψv := hdigamma (3 / 4) ((t + h) / 2) hσ0 hσ1 hv
  have hψu' :
      ‖Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) -
          GaloisForLFunctions.vertLog (t / 2)‖ ≤ C := by
    calc
      _ ≤ C / (t / 2) := hψu
      _ ≤ C := by
        rw [div_le_iff₀ (by positivity : 0 < t / 2)]
        nlinarith
  have hψv' :
      ‖Complex.digamma (((3 / 4 : ℝ) : ℂ) + (((t + h) / 2 : ℝ) : ℂ) * I) -
          GaloisForLFunctions.vertLog ((t + h) / 2)‖ ≤ C := by
    calc
      _ ≤ C / ((t + h) / 2) := hψv
      _ ≤ C := by
        rw [div_le_iff₀ (by positivity : 0 < (t + h) / 2)]
        nlinarith
  have huv : t / 2 ≤ (t + h) / 2 := by linarith
  have hvle : (t + h) / 2 ≤ 2 * (t / 2) := by linarith
  have hlog0 : 0 ≤ Real.log ((t + h) / 2) - Real.log (t / 2) := by
    exact sub_nonneg.mpr (Real.log_le_log (by positivity) huv)
  have hlog1 : Real.log ((t + h) / 2) - Real.log (t / 2) ≤ 1 := by
    have hlog : Real.log ((t + h) / 2) ≤ Real.log (2 * (t / 2)) :=
      Real.log_le_log (by positivity) hvle
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by positivity : t / 2 ≠ 0)] at hlog
    linarith [Real.log_two_lt_d9]
  have hvert :
      ‖GaloisForLFunctions.vertLog ((t + h) / 2) -
          GaloisForLFunctions.vertLog (t / 2)‖ ≤ 1 := by
    rw [GaloisForLFunctions.vertLog, GaloisForLFunctions.vertLog]
    have hrewrite :
        ((Real.log ((t + h) / 2) : ℂ) + (Real.pi / 2 : ℂ) * I) -
            ((Real.log (t / 2) : ℂ) + (Real.pi / 2 : ℂ) * I) =
          ((Real.log ((t + h) / 2) - Real.log (t / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hrewrite, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
    exact hlog1
  have hdigammaDiff :
      ‖Complex.digamma (((3 / 4 : ℝ) : ℂ) + (((t + h) / 2 : ℝ) : ℂ) * I) -
          Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ ≤ 2 * C + 1 := by
    let a : ℂ := Complex.digamma (((3 / 4 : ℝ) : ℂ) + (((t + h) / 2 : ℝ) : ℂ) * I) -
      GaloisForLFunctions.vertLog ((t + h) / 2)
    let b : ℂ := GaloisForLFunctions.vertLog ((t + h) / 2) -
      GaloisForLFunctions.vertLog (t / 2)
    let c : ℂ := GaloisForLFunctions.vertLog (t / 2) -
      Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)
    have hsplit :
        Complex.digamma (((3 / 4 : ℝ) : ℂ) + (((t + h) / 2 : ℝ) : ℂ) * I) -
            Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) = a + b + c := by
      simp [a, b, c]
    rw [hsplit]
    have ha : ‖a‖ ≤ C := hψv'
    have hb : ‖b‖ ≤ 1 := hvert
    have hcEq : c = -(Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) -
          GaloisForLFunctions.vertLog (t / 2)) := by
      simp [c]
    have hc : ‖c‖ ≤ C := by
      rw [hcEq, norm_neg]
      exact hψu'
    calc
      ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
      _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by gcongr; exact norm_add_le _ _
      _ ≤ C + 1 + C := by gcongr
      _ = 2 * C + 1 := by ring
  have hfirst : 0 < (((3 / 2 : ℂ) + ((t + h : ℝ) : ℂ) * I)).re := by
    simp
  have hsecond : 0 < (((3 / 2 : ℂ) + (t : ℂ) * I)).re := by
    simp
  rw [logDeriv_Gammaℝ_digamma hfirst, logDeriv_Gammaℝ_digamma hsecond]
  have hcoordv : ((3 / 2 : ℂ) + ((t + h : ℝ) : ℂ) * I) / 2 =
      ((3 / 4 : ℝ) : ℂ) + (((t + h) / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hcoordu : ((3 / 2 : ℂ) + (t : ℂ) * I) / 2 =
      ((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hcoordv, hcoordu]
  have hrewrite :
      (Complex.digamma (((3 / 4 : ℝ) : ℂ) + (((t + h) / 2 : ℝ) : ℂ) * I) / 2 -
          (Real.log Real.pi : ℂ) / 2) -
        (Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) / 2 -
          (Real.log Real.pi : ℂ) / 2) =
        (Complex.digamma (((3 / 4 : ℝ) : ℂ) + (((t + h) / 2 : ℝ) : ℂ) * I) -
          Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)) / 2 := by
    ring
  rw [hrewrite]
  calc
    _ = ‖Complex.digamma (((3 / 4 : ℝ) : ℂ) + (((t + h) / 2 : ℝ) : ℂ) * I) -
        Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ / 2 := by
      rw [Complex.norm_div]
      norm_num
    _ ≤ (2 * C + 1) / 2 := div_le_div_of_nonneg_right hdigammaDiff (by norm_num)
    _ = C + 1 / 2 := by ring

end

end RHTower
