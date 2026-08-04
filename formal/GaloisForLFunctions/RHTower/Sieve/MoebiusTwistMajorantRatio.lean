import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistContourBoundRatio
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistCombinedBound
import GaloisForLFunctions.RHTower.Sieve.MoebiusMajorantRatio

/-!
# The twisted ratio bound against the majorant

Collapsing the twisted contour terms and majorising the coefficient gives the twisted analogue of
the majorant bound: the trivial size `N+H+1` times a polynomial coefficient times the decay
`exp(-c₀ t / 8192)` with `t = (log(N+H))^{1/10}`, at the cost of a single factor `2` for the
shortened truncation height.

The twist is constrained only by `5 + 4|τ| ≤ contourParam(N+H)`; that condition already places `τ`
inside half the truncation height, so nothing further is assumed.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- **The twisted smoothed Möbius sum at arbitrary smoothing width, against the majorant.** -/
theorem exists_norm_tsum_moebiusTwist_smoothWeight_le_majorant_ratio :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ N H L : ℝ, 0 < N → 1 ≤ H → N / H ≤ L → 0 ≤ L →
      1 ≤ Real.log (N + H) → 2 ≤ (Real.log (N + H)) ^ ((1 : ℝ) / 10) →
      K₀ ≤ contourParam (N + H) →
      ∀ τ : ℝ, 5 + 4 * |τ| ≤ ((contourParam (N + H) : ℕ) : ℝ) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          moebiusTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * ((N + H + 1)
            * coeffMajorant (C * (L + 2) ^ 2) (C' * (L + 2)) M₀ (1024 / zeroFreeConst)
                ((Real.log (N + H)) ^ ((1 : ℝ) / 10))
            * Real.exp (-(zeroFreeConst * (Real.log (N + H)) ^ ((1 : ℝ) / 10) / 8192))) := by
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_moebiusTwist_smoothWeight_le_ratio
  refine ⟨C, C', M₀, K₀, hC, hC', hM₀,
    fun N H L hN hH1 hL hL0 hlog1 hlog2 hK τ hKτ => ?_⟩
  have hH : (0 : ℝ) < H := by linarith
  set x : ℝ := N + H with hxdef
  have hx0 : (0 : ℝ) < x := by rw [hxdef]; linarith
  have hL2 : (0 : ℝ) ≤ L + 2 := by linarith
  have hĈ : (0 : ℝ) ≤ C * (L + 2) ^ 2 := by positivity
  have hĈ' : (0 : ℝ) ≤ C' * (L + 2) := by positivity
  have ht : (2 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 10) := hlog2
  have ht1 : (1 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 10) := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (contourParam x) := le_trans ht1 (le_log_contourParam x)
  have hgap : rightAbscissa (contourParam x) - leftAbscissa (contourParam x) ≤ 1 :=
    gap_le_one hL1
  -- positivity of the abscissa and of the gap
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  have hL9 : (1 : ℝ) ≤ (Real.log (contourParam x)) ^ 9 := one_le_pow₀ hL1
  have h16 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log (contourParam x)) ^ 9) := by positivity
  have h2p : (0 : ℝ) < zeroFreeConst / (2 * (Real.log (contourParam x)) ^ 9) := by positivity
  have h16le : zeroFreeConst / (16 * (Real.log (contourParam x)) ^ 9) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  have hcpos : 0 < leftAbscissa (contourParam x) := by rw [leftAbscissa]; linarith
  have hgapnn : 0 ≤ rightAbscissa (contourParam x) - leftAbscissa (contourParam x) := by
    rw [rightAbscissa, leftAbscissa]; linarith
  -- the two logarithmic comparisons between `x` and `x + 1`
  have hxe : (2 : ℝ) ≤ x := by
    have h := Real.exp_le_exp.2 hlog1
    rw [Real.exp_log hx0] at h
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    linarith
  have hx1le : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
  have hsq : x + 1 ≤ x ^ 2 := by nlinarith [hxe]
  have hy : Real.log (x + 1) ≤ 2 * Real.log x := by
    have h := Real.log_le_log (by linarith) hsq
    rwa [Real.log_pow] at h
  have hbase := hmain N H L hN hH1 hL τ (contourParam x) hK hKτ
  have hcomb := combined_terms_twist_le (x := x) (C := C * (L + 2) ^ 2) (C' := C' * (L + 2))
    (R := invZetaRightBound (contourParam x)) (E := invZetaEdgeBound (contourParam x))
    (M₀ := M₀) (τ := τ) hlog1 ht hx0 hy hx1le hĈ hĈ'
    (invZetaRightBound_nonneg _) (invZetaEdgeBound_nonneg _) hM₀ hgap hgapnn hcpos
    (abs_le_half_truncHeight hKτ)
  have hcoeff := coeff_le_coeffMajorant (x := x) (C := C * (L + 2) ^ 2) (C' := C' * (L + 2))
    hlog1 hĈ hĈ' hM₀
  have hSpos : (0 : ℝ) < Real.exp (-(zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192)) :=
    Real.exp_pos _
  have hfinal : (x + 1)
      * (8 * invZetaRightBound (contourParam x) * (C * (L + 2) ^ 2)
          + 8 * invZetaEdgeBound (contourParam x) * (C' * (L + 2))
          + max M₀ (invZetaEdgeBound (contourParam x)) * (4 + 2 * (C * (L + 2) ^ 2)))
      * Real.exp (-(zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192))
      ≤ (x + 1)
          * coeffMajorant (C * (L + 2) ^ 2) (C' * (L + 2)) M₀ (1024 / zeroFreeConst)
              ((Real.log x) ^ ((1 : ℝ) / 10))
          * Real.exp (-(zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192)) := by
    have hx10 : (0 : ℝ) ≤ x + 1 := by linarith
    gcongr
  refine le_trans hbase (le_trans hcomb ?_)
  linarith

end RHTower.Sieve
