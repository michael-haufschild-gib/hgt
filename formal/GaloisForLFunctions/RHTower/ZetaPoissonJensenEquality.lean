import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenEquality
import GaloisForLFunctions.RHTower.ZetaPoissonJensenInequality
import GaloisForLFunctions.RHTower.Deninger.DeningerZetaLowerBound


/-!
# The Poisson–Jensen equality for `ζ`

For `Re s₀ > ½`, `s₀ ≠ 1`, `ζ(s₀) ≠ 0`, let `T` be the half-plane automorphism with `T(1) = s₀` and
`G_{s₀}(w) = (T(s) − 1) ζ(T(s))` at `s = 1/(1 − w)` (`shiftedZetaDisc`).  The Jensen zero sums of
`G_{s₀}` converge to

`∫ log |ζ(½ + iτ)| P_{s₀}(τ) dτ − log |ζ(s₀)| + log(|s₀|/|s₀ − 1|)`

(`tendsto_jensenSum_shiftedZetaDisc`), so the inequality of `ZetaPoissonJensenInequality` is an
equality: `log |ζ|` on `Re s > ½` is the Poisson extension of its critical-line values plus
`log |s/(s − 1)|`, minus the Green potential of the zeros off the critical line.

The proof applies the boundary Jensen equality of `ZetaCriticalLineJensenEquality` to `G_{s₀}`;
near `w = 1`, `Re T(s) ≥ 2` and `|G_{s₀}| ≥ 1/4` (`exists_quarter_le_norm_shiftedZetaDisc`).
-/

open Complex MeasureTheory Set Filter Topology ComplexConjugate Metric
open scoped Real

namespace RHTower

noncomputable section

/-- Far to the right of the shifted disc, `|G_{s₀}| ≥ 1/4`. -/
theorem exists_quarter_le_norm_shiftedZetaDisc {s0 : ℂ} (hs0 : 1 / 2 < s0.re) :
    ∃ x₀ : ℝ, 1 / 2 ≤ x₀ ∧ x₀ < 1 ∧ ∀ x : ℝ, x₀ ≤ x → x < 1 →
      1 / 4 ≤ ‖shiftedZetaDisc s0 x‖ := by
  set lam : ℝ := 2 * s0.re - 1 with hlam
  have hlam0 : 0 < lam := by rw [hlam]; linarith
  set σ₀ : ℝ := max 2 (1 / 2 + 3 / (2 * lam)) with hσ₀
  have hσ₀2 : 2 ≤ σ₀ := le_max_left _ _
  refine ⟨1 - 1 / σ₀, ?_, ?_, fun x hx hx1 => ?_⟩
  · have : 1 / σ₀ ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  · have : 0 < 1 / σ₀ := by positivity
    linarith
  have h1x : 0 < 1 - x := by linarith
  set σ : ℝ := (1 - x)⁻¹ with hσ
  have hσσ₀ : σ₀ ≤ σ := by
    rw [hσ, le_inv_comm₀ (by linarith) h1x]
    have : 1 - x ≤ 1 / σ₀ := by linarith
    rwa [one_div] at this
  have hs : halfPlaneOfDisc (x : ℂ) = (σ : ℂ) := by
    simp only [halfPlaneOfDisc, hσ]; push_cast; rfl
  set T := halfPlaneShift s0 (σ : ℂ) with hT
  have hTre : 2 ≤ T.re := by
    rw [hT, re_halfPlaneShift, Complex.ofReal_re]
    have h3 : 1 / 2 + 3 / (2 * lam) ≤ σ := (le_max_right _ _).trans hσσ₀
    have h4 : 3 / 2 ≤ lam * (σ - 1 / 2) := by
      have : 3 / (2 * lam) ≤ σ - 1 / 2 := by linarith
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    rw [← hlam]
    linarith
  have hT1 : T ≠ 1 := by
    intro h; rw [h] at hTre; norm_num at hTre
  rw [shiftedZetaDisc, hs, ← hT, zetaEntire_eq hT1, norm_mul]
  have hsub : 1 ≤ ‖T - 1‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, Complex.one_re, abs_of_pos (by linarith)]
    linarith
  have hζ := norm_riemannZeta_ge_of_two_le_re hTre
  nlinarith [norm_nonneg (riemannZeta T)]

/-- The boundary circle average of `log |G_{s₀}|` is the Poisson average of `log |ζ|` on the
critical line plus `log |s₀|`. -/
theorem circleAverage_log_norm_shiftedZetaDisc_one_eq {s0 : ℂ} (hs0 : 1 / 2 < s0.re)
    (hs01 : s0 ≠ 1) (hz0 : riemannZeta s0 ≠ 0) :
    Real.circleAverage (fun w => Real.log ‖shiftedZetaDisc s0 w‖) 0 1 =
      (∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ) +
        Real.log ‖s0‖ := by
  have hs00 : s0 ≠ 0 := by rintro rfl; simp at hs0; linarith
  have hG0 : zetaEntire s0 ≠ 0 := by
    rw [zetaEntire_eq hs01]; exact mul_ne_zero (sub_ne_zero.mpr hs01) hz0
  obtain ⟨hci, -⟩ := circleIntegrable_and_sum_log_add_le_circleAverage
    (differentiableOn_shiftedZetaDisc s0) (measurable_shiftedZetaDisc s0)
    (by rw [shiftedZetaDisc_zero]; exact hG0) (exists_log_norm_shiftedZetaDisc_le hs0)
    (U := ∅) (by simp)
  set F1 : ℝ → ℝ := fun τ => Real.log ‖zetaEntire (1 / 2 + τ * I)‖ with hF1
  set F2 : ℝ → ℝ := fun τ => Real.log ‖(1 / 2 + τ * I : ℂ) - 1‖ with hF2
  have hcrit : ∀ t : ℝ, halfPlaneShift s0 (halfPlaneOfDisc (circleMap 0 1 (criticalLineAngle t)))
      = 1 / 2 + (((2 * s0.re - 1) * t + s0.im : ℝ) : ℂ) * I := by
    intro t
    rw [halfPlaneOfDisc_circleMap_criticalLineAngle, halfPlaneShift_criticalLine]
  obtain ⟨hiff1, heq1⟩ := circleAverage_shift_eq_poisson hs0 F1
    (fun w => Real.log ‖shiftedZetaDisc s0 w‖) (fun t => by
      simp only [hF1, shiftedZetaDisc, hcrit])
  have hF1int := hiff1.mp hci
  obtain ⟨hpci, hpavg⟩ := circleIntegrable_and_circleAverage_poleFactor hs0
  have hw1 : ∀ t : ℝ, circleMap 0 1 (criticalLineAngle t) ≠ 1 := by
    intro t h
    have := halfPlaneOfDisc_circleMap_criticalLineAngle t
    rw [h, halfPlaneOfDisc, sub_self, inv_zero] at this
    have h2 := congrArg Complex.re this
    norm_num at h2
  obtain ⟨hiff2, heq2⟩ := circleAverage_shift_eq_poisson hs0 F2
    (fun w : ℂ => Real.log ‖s0 - 1 + (starRingEnd ℂ) s0 * w‖ - Real.log ‖1 - w‖) (fun t => by
      have hwt := hw1 t
      set w := circleMap 0 1 (criticalLineAngle t) with hwdef
      have hwn : ‖w‖ = 1 := by rw [hwdef]; simp
      have hnum : s0 - 1 + (starRingEnd ℂ) s0 * w ≠ 0 := by
        intro h
        have hw' : w = -(s0 - 1) / (starRingEnd ℂ) s0 := by
          have hcs0 : (starRingEnd ℂ) s0 ≠ 0 := by simpa using hs00
          field_simp; linear_combination h
        have hlt : ‖s0 - 1‖ < ‖s0‖ := by
          have h1 : ‖s0 - 1‖ ^ 2 < ‖s0‖ ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
              Complex.normSq_apply]
            simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
            nlinarith
          exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
        rw [hw', norm_div, norm_neg, Complex.norm_conj,
          div_eq_one_iff_eq (norm_ne_zero_iff.mpr hs00)] at hwn
        linarith
      have hden : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hwt)
      simp only [hF2]
      rw [← hcrit t, halfPlaneShift_halfPlaneOfDisc_sub_one s0 hwt, norm_div,
        Real.log_div (norm_ne_zero_iff.mpr hnum) (norm_ne_zero_iff.mpr hden)])
  have hF2int := hiff2.mp hpci
  rw [hpavg] at heq2
  have hne1 : ∀ τ : ℝ, (1 / 2 : ℂ) + τ * I ≠ 1 := by
    intro τ h; have := congrArg Complex.re h; norm_num at this
  have hcount : {τ : ℝ | riemannZeta (1 / 2 + τ * I) = 0}.Countable := by
    have hinj : Function.Injective (fun τ : ℝ => (1 / 2 : ℂ) + τ * I) := by
      intro a b hab
      have := congrArg Complex.im hab
      simpa using this
    refine (countable_setOf_zetaEntire_eq_zero.preimage hinj).mono fun τ hτ => ?_
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hτ ⊢
    rw [zetaEntire_eq (hne1 τ), hτ, mul_zero]
  have hae : ∀ᵐ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ
      = F1 τ * halfPlanePoissonKernel s0 τ - F2 τ * halfPlanePoissonKernel s0 τ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hcount.measure_zero _)] with τ hτ
    have hsub : (1 / 2 : ℂ) + τ * I - 1 ≠ 0 := sub_ne_zero.mpr (hne1 τ)
    simp only [hF1, hF2]
    rw [zetaEntire_eq (hne1 τ), norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hsub)
      (norm_ne_zero_iff.mpr hτ)]
    ring
  rw [integral_congr_ae hae, integral_sub hF1int hF2int, ← heq1, ← heq2]
  ring

/-- **The Poisson–Jensen equality for `ζ`.**  For `Re s₀ > ½`, `s₀ ≠ 1`, `ζ(s₀) ≠ 0`, the Jensen
zero sums of `G_{s₀}(w) = (T(s) − 1)ζ(T(s))` (`T` the half-plane automorphism sending `1` to
`s₀`) converge to `∫ log |ζ(½ + iτ)| P_{s₀}(τ) dτ − log |ζ(s₀)| + log(|s₀|/|s₀ − 1|)`.  The zeros
of `G_{s₀}` are `(ρ − s₀)/(ρ + s̄₀ − 1)` over the zeros `ρ` of `ζ` with `Re ρ > ½`, so this is the
exact Riesz decomposition: `log |ζ(s₀)|` is the Poisson extension of `log |ζ|` on the critical line
plus `log(|s₀|/|s₀ − 1|)`, minus the Green potential `Σ m_ρ log |(ρ + s̄₀ − 1)/(ρ − s₀)|` of the
zeros off the line. -/
theorem tendsto_jensenSum_shiftedZetaDisc {s0 : ℂ} (hs0 : 1 / 2 < s0.re) (hs01 : s0 ≠ 1)
    (hz0 : riemannZeta s0 ≠ 0) :
    Tendsto (fun r : ℝ => ∑ᶠ u, (MeromorphicOn.divisor (shiftedZetaDisc s0)
        (closedBall (0 : ℂ) |r|) u : ℝ) * Real.log (r * ‖0 - u‖⁻¹)) (𝓝[<] 1)
      (𝓝 ((∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ) -
        Real.log ‖riemannZeta s0‖ + Real.log (‖s0‖ / ‖s0 - 1‖))) := by
  have hs00 : s0 ≠ 0 := by rintro rfl; simp at hs0; linarith
  have hG0 : zetaEntire s0 ≠ 0 := by
    rw [zetaEntire_eq hs01]; exact mul_ne_zero (sub_ne_zero.mpr hs01) hz0
  obtain ⟨A, hA⟩ := exists_log_norm_shiftedZetaDisc_le hs0
  obtain ⟨x₀, hx₀, hx₀1, hlow⟩ := exists_quarter_le_norm_shiftedZetaDisc hs0
  have h := tendsto_integral_log_norm_circleMap_nhdsLT_one (differentiableOn_shiftedZetaDisc s0)
    (measurable_shiftedZetaDisc s0) (by rw [shiftedZetaDisc_zero]; exact hG0) hA
    (by norm_num : (0 : ℝ) < 1 / 4) hx₀ hx₀1 hlow
  have hcirc : Tendsto (fun r => Real.circleAverage (fun w => Real.log ‖shiftedZetaDisc s0 w‖) 0 r)
      (𝓝[<] 1) (𝓝 (Real.circleAverage (fun w => Real.log ‖shiftedZetaDisc s0 w‖) 0 1)) := by
    simp only [Real.circleAverage_def, smul_eq_mul]
    exact h.const_mul _
  rw [circleAverage_log_norm_shiftedZetaDisc_one_eq hs0 hs01 hz0] at hcirc
  have hlim : (∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ) -
      Real.log ‖riemannZeta s0‖ + Real.log (‖s0‖ / ‖s0 - 1‖) =
      (∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ) +
        Real.log ‖s0‖ - Real.log ‖zetaEntire s0‖ := by
    rw [zetaEntire_eq hs01, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs01))
      (norm_ne_zero_iff.mpr hz0), Real.log_div (norm_ne_zero_iff.mpr hs00)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs01))]
    ring
  rw [hlim]
  refine (hcirc.sub_const (Real.log ‖zetaEntire s0‖)).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have han : AnalyticOnNhd ℂ (shiftedZetaDisc s0) (closedBall 0 |r|) := by
    intro w hw
    rw [abs_of_pos hr.1, mem_closedBall, dist_zero_right] at hw
    have hw1 : w ≠ 1 := fun h => by rw [h, norm_one] at hw; linarith [hr.2]
    exact (differentiableOn_shiftedZetaDisc s0).analyticAt
      (isOpen_compl_singleton.mem_nhds hw1)
  rw [han.circleAverage_log_norm hr.1.ne' (by rw [shiftedZetaDisc_zero]; exact hG0),
    shiftedZetaDisc_zero]
  ring

end

end RHTower
