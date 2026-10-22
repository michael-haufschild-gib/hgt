import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaMollifiedEquation

/-!
# The scale majorant for pairing the Gamma jump against a test function

Transposing `R_σ` onto a test function needs a Fubini interchange in which the test function sits
*inside* the second difference.  The corpus majorant `gammaPairingMajorant` dominates the difference
pointwise and is then paired against an `L¹` factor; here the roles are reversed, so what is needed
is a bound on the *base-point integral* of the difference, uniform in the scale.

Both regimes are elementary once the test function's compact support is used.  At small scale the
difference is `O(s)` pointwise and lives on a fixed interval, so its integral is `O(s)` and `s·k(s)`
is bounded.  At large scale the support is useless — the translates have moved far — but
translation invariance of the `L¹` norm gives `4e^{σs}‖φ‖₁`, and the kernel's exponential decay
beats `e^{σs}` for every `σ < 1`.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- Outside the enlarged support every translate has left the support. -/
theorem shiftedSecondDifference_eq_zero_of_support {φ : ℝ → ℝ} {R : ℝ}
    (hsupp : ∀ x : ℝ, R < |x| → φ x = 0) (σ : ℝ) {L s : ℝ} (hs : 0 ≤ s)
    (hL : R + s < |L|) : shiftedSecondDifference σ φ L s = 0 := by
  have h0 : φ L = 0 := hsupp L (by linarith)
  have h1 : φ (L + s) = 0 := by
    refine hsupp _ ?_
    rcases le_or_gt 0 L with hLpos | hLneg
    · rw [abs_of_nonneg hLpos] at hL
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ L + s)]
      linarith
    · rw [abs_of_neg hLneg] at hL
      rcases le_or_gt 0 (L + s) with h | h
      · rw [abs_of_nonneg h]
        linarith
      · rw [abs_of_neg h]
        linarith
  have h2 : φ (L - s) = 0 := by
    refine hsupp _ ?_
    rcases le_or_gt 0 L with hLpos | hLneg
    · rw [abs_of_nonneg hLpos] at hL
      rcases le_or_gt 0 (L - s) with h | h
      · rw [abs_of_nonneg h]
        linarith
      · rw [abs_of_neg h]
        linarith
    · rw [abs_of_neg hLneg] at hL
      rw [abs_of_neg (by linarith : L - s < 0)]
      linarith
  rw [shiftedSecondDifference, h0, h1, h2]
  ring

/-- The scale majorant for the transposed pairing. -/
def gammaTransposeMajorant (K B N R σ : ℝ) (s : ℝ) : ℝ :=
  if s ≤ 1 then (2 * R + 2) * (2 * K + 2 * B * σ * Real.exp σ) * s * gammaTransportKernel s
  else 4 * N * Real.exp (σ * s) * gammaTransportKernel s


theorem gammaTransposeMajorant_nonneg {K B N R σ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hR : 0 ≤ R) (hσ0 : 0 ≤ σ) {s : ℝ} (hs : 0 < s) :
    0 ≤ gammaTransposeMajorant K B N R σ s := by
  have hk : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs
  rw [gammaTransposeMajorant]
  split
  · positivity
  · positivity

theorem integrableOn_gammaTransposeMajorant {K B N R σ : ℝ} (hσ1 : σ < 1) :
    IntegrableOn (gammaTransposeMajorant K B N R σ) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  have hnear : IntegrableOn (gammaTransposeMajorant K B N R σ) (Ioc 0 1) := by
    have hbase : IntegrableOn (fun s : ℝ => s * gammaTransportKernel s) (Ioc 0 1) :=
      integrableOn_id_mul_gammaTransportKernel_Ioi_zero.mono_set Ioc_subset_Ioi_self
    have hscaled : IntegrableOn
        (fun s : ℝ => ((2 * R + 2) * (2 * K + 2 * B * σ * Real.exp σ))
          * (s * gammaTransportKernel s)) (Ioc 0 1) := hbase.const_mul _
    refine hscaled.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [gammaTransposeMajorant, if_pos hs.2]
    ring
  have hfar : IntegrableOn (gammaTransposeMajorant K B N R σ) (Ioi 1) := by
    have hdom : IntegrableOn (fun s : ℝ => 8 * |N| * Real.exp (-(1 - σ) * s)) (Ioi 1) := by
      have h : IntegrableOn (fun x : ℝ => Real.exp (-(1 - σ) * x)) (Ioi 1) :=
        exp_neg_integrableOn_Ioi (1 : ℝ) (by linarith : (0:ℝ) < 1 - σ)
      exact h.const_mul (8 * |N|)
    refine Integrable.mono' hdom ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_
      · exact ((((measurable_const.mul measurable_const).mul measurable_id)).mul
          measurable_gammaTransportKernel)
      · exact ((measurable_const.mul
          (Real.measurable_exp.comp (measurable_const.mul measurable_id))).mul
          measurable_gammaTransportKernel)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs' : (1 : ℝ) < s := hs
      have hs1 : (1 : ℝ) ≤ s := le_of_lt hs'
      have hnot : ¬ s ≤ 1 := by linarith
      rw [gammaTransposeMajorant, if_neg hnot, Real.norm_eq_abs]
      have hk : gammaTransportKernel s ≤ 2 * Real.exp (-s) :=
        gammaTransportKernel_le_two_mul_exp_neg hs1
      have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos (by linarith)
      have habs : |4 * N * Real.exp (σ * s) * gammaTransportKernel s|
          = 4 * |N| * Real.exp (σ * s) * gammaTransportKernel s := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hkpos, abs_of_pos (Real.exp_pos _)]
        norm_num
      rw [habs]
      calc 4 * |N| * Real.exp (σ * s) * gammaTransportKernel s
          ≤ 4 * |N| * Real.exp (σ * s) * (2 * Real.exp (-s)) := by
            refine mul_le_mul_of_nonneg_left hk (by positivity)
        _ = 8 * |N| * Real.exp (-(1 - σ) * s) := by
            rw [show (8 : ℝ) * |N| * Real.exp (-(1 - σ) * s)
              = 4 * |N| * (Real.exp (σ * s) * Real.exp (-s)) * 2 by
                rw [← Real.exp_add]
                ring_nf]
            ring
  rw [hsplit]
  exact hnear.union hfar


/-- The base-point integral of the shifted second difference, in the two scale regimes. -/
theorem integral_abs_shiftedSecondDifference_mul_kernel_le {φ : ℝ → ℝ} {K B N R σ : ℝ}
    (hφc : Continuous φ)
    (hφK : ∀ x y : ℝ, |φ x - φ y| ≤ K * |x - y|) (hφB : ∀ x, |φ x| ≤ B)
    (hsupp : ∀ x : ℝ, R < |x| → φ x = 0) (hR : 0 ≤ R)
    (hφint : Integrable φ) (hN : (∫ x, |φ x|) = N)
    (hσ0 : 0 ≤ σ) {s : ℝ} (hs : 0 < s) :
    (∫ L, |shiftedSecondDifference σ φ L s| * gammaTransportKernel s)
      ≤ gammaTransposeMajorant K B N R σ s := by
  have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs
  have hcont : Continuous fun L : ℝ => shiftedSecondDifference σ φ L s := by
    have : Continuous fun L : ℝ => 2 * φ L - Real.exp (-(σ * s)) * φ (L + s)
        - Real.exp (σ * s) * φ (L - s) :=
      ((continuous_const.mul hφc).sub
        (continuous_const.mul (hφc.comp (continuous_id.add continuous_const)))).sub
        (continuous_const.mul (hφc.comp (continuous_id.sub continuous_const)))
    exact this
  rw [integral_mul_const]
  by_cases hcase : s ≤ 1
  · -- small scale: the difference is `O(s)` and lives on a fixed interval
    have hzero : ∀ L : ℝ, L ∉ Icc (-(R + 1)) (R + 1) → shiftedSecondDifference σ φ L s = 0 := by
      intro L hL
      refine shiftedSecondDifference_eq_zero_of_support hsupp σ hs.le ?_
      rw [mem_Icc, not_and_or] at hL
      rcases hL with h | h
      · rw [not_le] at h
        rw [abs_of_neg (by linarith : L < 0)]
        linarith
      · rw [not_le] at h
        rw [abs_of_pos (by linarith : 0 < L)]
        linarith
    have hbound : ∀ L : ℝ, |shiftedSecondDifference σ φ L s|
        ≤ (2 * K + 2 * B * σ * Real.exp σ) * s := by
      intro L
      refine le_trans (abs_shiftedSecondDifference_le_mul hφK hφB hσ0 hs.le L) ?_
      have hexp : Real.exp (σ * s) ≤ Real.exp σ :=
        Real.exp_le_exp.mpr (by nlinarith [hσ0, hs.le, hcase])
      have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hφB 0)
      have hstep : 2 * B * σ * Real.exp (σ * s) ≤ 2 * B * σ * Real.exp σ :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) hs.le
    have hint : IntegrableOn (fun L : ℝ => |shiftedSecondDifference σ φ L s|)
        (Icc (-(R + 1)) (R + 1)) := (hcont.abs).integrableOn_Icc
    have heq : (∫ L, |shiftedSecondDifference σ φ L s|)
        = ∫ L in Icc (-(R + 1)) (R + 1), |shiftedSecondDifference σ φ L s| := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun L hL => ?_).symm
      rw [hzero L hL, abs_zero]
    have hle : (∫ L in Icc (-(R + 1)) (R + 1), |shiftedSecondDifference σ φ L s|)
        ≤ (2 * R + 2) * ((2 * K + 2 * B * σ * Real.exp σ) * s) := by
      have hnorm := MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (C := (2 * K + 2 * B * σ * Real.exp σ) * s) (s := Icc (-(R + 1)) (R + 1))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
        (fun L _ => by rw [Real.norm_eq_abs, abs_abs]; exact hbound L)
      have hmeasure : (volume : Measure ℝ).real (Icc (-(R + 1)) ((R : ℝ) + 1)) = 2 * R + 2 := by
        rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring
      rw [hmeasure] at hnorm
      rw [mul_comm] at hnorm
      calc (∫ L in Icc (-(R + 1)) (R + 1), |shiftedSecondDifference σ φ L s|)
          ≤ ‖∫ L in Icc (-(R + 1)) (R + 1), |shiftedSecondDifference σ φ L s|‖ :=
            le_abs_self _
        _ ≤ (2 * R + 2) * ((2 * K + 2 * B * σ * Real.exp σ) * s) := hnorm
    rw [gammaTransposeMajorant, if_pos hcase, heq]
    calc (∫ L in Icc (-(R + 1)) (R + 1), |shiftedSecondDifference σ φ L s|)
          * gammaTransportKernel s
        ≤ ((2 * R + 2) * ((2 * K + 2 * B * σ * Real.exp σ) * s)) * gammaTransportKernel s :=
          mul_le_mul_of_nonneg_right hle hkpos.le
      _ = (2 * R + 2) * (2 * K + 2 * B * σ * Real.exp σ) * s * gammaTransportKernel s := by ring
  · -- large scale: translation invariance of the `L¹` norm
    have hs1 : (1 : ℝ) ≤ s := by linarith [not_le.mp hcase]
    have hexp1 : (1 : ℝ) ≤ Real.exp (σ * s) := Real.one_le_exp (by positivity)
    have habs1 : Integrable fun L : ℝ => |φ L| := hφint.abs
    have habs2 : (∫ L, |φ (L + s)|) = N := by
      rw [← hN]
      exact integral_add_right_eq_self (fun L => |φ L|) s
    have habs3 : (∫ L, |φ (L - s)|) = N := by
      rw [← hN]
      exact integral_sub_right_eq_self (fun L => |φ L|) s
    have hptw : ∀ L : ℝ, |shiftedSecondDifference σ φ L s|
        ≤ 2 * |φ L| + Real.exp (σ * s) * |φ (L + s)| + Real.exp (σ * s) * |φ (L - s)| := by
      intro L
      rw [shiftedSecondDifference]
      have h1 : |2 * φ L - Real.exp (-(σ * s)) * φ (L + s) - Real.exp (σ * s) * φ (L - s)|
          ≤ |2 * φ L| + |Real.exp (-(σ * s)) * φ (L + s)| + |Real.exp (σ * s) * φ (L - s)| := by
        calc |2 * φ L - Real.exp (-(σ * s)) * φ (L + s) - Real.exp (σ * s) * φ (L - s)|
            ≤ |2 * φ L - Real.exp (-(σ * s)) * φ (L + s)|
              + |Real.exp (σ * s) * φ (L - s)| := abs_sub _ _
          _ ≤ (|2 * φ L| + |Real.exp (-(σ * s)) * φ (L + s)|)
              + |Real.exp (σ * s) * φ (L - s)| := add_le_add (abs_sub _ _) le_rfl
      refine le_trans h1 ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      have hle : Real.exp (-(σ * s)) ≤ Real.exp (σ * s) :=
        Real.exp_le_exp.mpr (by nlinarith [hσ0, hs1])
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2]
      nlinarith [abs_nonneg (φ (L + s)), hle]
    have hsum : Integrable fun L : ℝ =>
        2 * |φ L| + Real.exp (σ * s) * |φ (L + s)| + Real.exp (σ * s) * |φ (L - s)| := by
      refine ((habs1.const_mul 2).add ?_).add ?_
      · exact (habs1.comp_add_right s).const_mul _
      · exact (habs1.comp_sub_right s).const_mul _
    have hle := MeasureTheory.integral_mono
      ((hcont.abs).integrable_of_hasCompactSupport (by
        refine HasCompactSupport.intro (isCompact_Icc (a := -(R + s)) (b := R + s)) fun L hL => ?_
        rw [mem_Icc, not_and_or] at hL
        refine abs_eq_zero.mpr (shiftedSecondDifference_eq_zero_of_support hsupp σ hs.le ?_)
        rcases hL with h | h
        · rw [not_le] at h
          rw [abs_of_neg (by linarith : L < 0)]
          linarith
        · rw [not_le] at h
          rw [abs_of_pos (by linarith : 0 < L)]
          linarith)) hsum hptw
    have hIA : Integrable fun L : ℝ => 2 * |φ L| := habs1.const_mul 2
    have hIB : Integrable fun L : ℝ => Real.exp (σ * s) * |φ (L + s)| :=
      (habs1.comp_add_right s).const_mul _
    have hIC : Integrable fun L : ℝ => Real.exp (σ * s) * |φ (L - s)| :=
      (habs1.comp_sub_right s).const_mul _
    have hval : (∫ L, 2 * |φ L| + Real.exp (σ * s) * |φ (L + s)|
        + Real.exp (σ * s) * |φ (L - s)|) = 2 * N + 2 * Real.exp (σ * s) * N := by
      have h1 : (∫ L, (2 * |φ L| + Real.exp (σ * s) * |φ (L + s)|)
          + Real.exp (σ * s) * |φ (L - s)|)
          = (∫ L, 2 * |φ L| + Real.exp (σ * s) * |φ (L + s)|)
            + ∫ L, Real.exp (σ * s) * |φ (L - s)| := integral_add (hIA.add hIB) hIC
      have h2 : (∫ L, 2 * |φ L| + Real.exp (σ * s) * |φ (L + s)|)
          = (∫ L, 2 * |φ L|) + ∫ L, Real.exp (σ * s) * |φ (L + s)| := integral_add hIA hIB
      rw [h1, h2, integral_const_mul, integral_const_mul, integral_const_mul, hN, habs2, habs3]
      ring
    rw [hval] at hle
    rw [gammaTransposeMajorant, if_neg hcase]
    have hNnn : 0 ≤ N := by
      rw [← hN]
      exact integral_nonneg fun x => abs_nonneg _
    calc (∫ L, |shiftedSecondDifference σ φ L s|) * gammaTransportKernel s
        ≤ (2 * N + 2 * Real.exp (σ * s) * N) * gammaTransportKernel s :=
          mul_le_mul_of_nonneg_right hle hkpos.le
      _ ≤ (4 * N * Real.exp (σ * s)) * gammaTransportKernel s := by
          refine mul_le_mul_of_nonneg_right ?_ hkpos.le
          nlinarith [hexp1, hNnn]
      _ = 4 * N * Real.exp (σ * s) * gammaTransportKernel s := by ring

end GaloisForLFunctions.RHTower
