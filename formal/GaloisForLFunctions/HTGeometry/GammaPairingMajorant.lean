import GaloisForLFunctions.HTGeometry.ShiftedSecondDifferenceBounds

/-!
# The scale majorant of the Gamma pairing

Multiplying the two scale bounds by the Gamma kernel produces a majorant that no longer depends on
the base point: constant on `(0,1]`, and exponentially decaying beyond.  It is integrable on the
ray exactly when `σ < 1`, and it is the dominating function that lets the base-point and scale
integrations of the Gamma pairing be exchanged.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The scale majorant: constant near zero, exponentially decaying far out. -/
noncomputable def gammaPairingMajorant (K B σ : ℝ) (s : ℝ) : ℝ :=
  if s ≤ 1 then 2 * K + 2 * B * σ * Real.exp σ else 8 * B * Real.exp (-(1 - σ) * s)

/-- **The pointwise domination.**  The Gamma pairing integrand is dominated in scale, uniformly in
the base point. -/
theorem abs_shiftedSecondDifference_mul_kernel_le {F : ℝ → ℝ} {K B σ : ℝ}
    (hK : ∀ x y : ℝ, |F x - F y| ≤ K * |x - y|) (hB : ∀ x, |F x| ≤ B)
    (hσ0 : 0 ≤ σ) {s : ℝ} (hs : 0 < s) (L : ℝ) :
    |shiftedSecondDifference σ F L s * gammaTransportKernel s|
      ≤ gammaPairingMajorant K B σ s := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hker : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs
  rw [abs_mul, abs_of_pos hker, gammaPairingMajorant]
  by_cases hs1 : s ≤ 1
  · rw [if_pos hs1]
    have hbound := abs_shiftedSecondDifference_le_mul hK hB hσ0 hs.le L
    have hexp : Real.exp (σ * s) ≤ Real.exp σ := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hstep : |shiftedSecondDifference σ F L s| ≤ (2 * K + 2 * B * σ * Real.exp σ) * s := by
      refine le_trans hbound ?_
      have : 2 * B * σ * Real.exp (σ * s) ≤ 2 * B * σ * Real.exp σ := by
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
      nlinarith [hs.le]
    have hinv : gammaTransportKernel s ≤ 1 / s := gammaTransportKernel_le_inv hs
    have hCnn : 0 ≤ 2 * K + 2 * B * σ * Real.exp σ := by
      have h0 : (0 : ℝ) ≤ |shiftedSecondDifference σ F L s| := abs_nonneg _
      nlinarith [hstep, hs]
    calc |shiftedSecondDifference σ F L s| * gammaTransportKernel s
        ≤ ((2 * K + 2 * B * σ * Real.exp σ) * s) * (1 / s) := by
          exact mul_le_mul hstep hinv hker.le (by positivity)
      _ = 2 * K + 2 * B * σ * Real.exp σ := by field_simp
  · rw [if_neg hs1]
    push_neg at hs1
    have hbound := abs_shiftedSecondDifference_le_exp hB hσ0 hs.le L
    have hinv : gammaTransportKernel s ≤ 2 * Real.exp (-s) :=
      gammaTransportKernel_le_two_mul_exp_neg hs1.le
    calc |shiftedSecondDifference σ F L s| * gammaTransportKernel s
        ≤ (4 * B * Real.exp (σ * s)) * (2 * Real.exp (-s)) := by
          exact mul_le_mul hbound hinv hker.le (by positivity)
      _ = 8 * B * (Real.exp (σ * s) * Real.exp (-s)) := by ring
      _ = 8 * B * Real.exp (-(1 - σ) * s) := by
          rw [← Real.exp_add]
          congr 2
          ring

/-- The majorant is integrable on the ray precisely because `σ < 1`. -/
theorem integrableOn_gammaPairingMajorant {K B σ : ℝ} (hσ1 : σ < 1) :
    IntegrableOn (gammaPairingMajorant K B σ) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  have hnear : IntegrableOn (gammaPairingMajorant K B σ) (Ioc 0 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => 2 * K + 2 * B * σ * Real.exp σ) (Ioc 0 1) := by
      have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
        constructor
        simp
      exact integrable_const _
    refine hconst.congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    rw [gammaPairingMajorant, if_pos hs.2]
  have hfar : IntegrableOn (gammaPairingMajorant K B σ) (Ioi 1) := by
    have hpos : 0 < 1 - σ := by linarith
    have hexp : IntegrableOn (fun s : ℝ => 8 * B * Real.exp (-(1 - σ) * s)) (Ioi 1) := by
      have hbase : IntegrableOn (fun s : ℝ => Real.exp ((σ - 1) * s)) (Ioi 1) := by
        simpa using exp_neg_integrableOn_Ioi (1 : ℝ) hpos
      have := hbase.const_mul (8 * B)
      refine this.congr ?_
      filter_upwards with s
      congr 1
      ring
    refine hexp.congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [gammaPairingMajorant, if_neg (by exact not_le.mpr hs)]
  rw [hsplit]
  exact hnear.union hfar

end GaloisForLFunctions.HTGeometry
