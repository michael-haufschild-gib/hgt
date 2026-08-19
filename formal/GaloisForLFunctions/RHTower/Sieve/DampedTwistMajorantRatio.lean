import GaloisForLFunctions.RHTower.Sieve.DampedTwistContourBoundRatio
import GaloisForLFunctions.RHTower.Sieve.DampedFactoredBound
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistMajorantRatio

/-!
# The twisted damped ratio bound against the majorant

Every one of the four twisted contour terms carries exactly one edge constant, and each of those is
the `invZeta` constant multiplied by the *same* factor `dampedCorrBound P (leftAbscissa K)`.  So the
whole twisted damped bound factors as that constant times the expression appearing in
`Sieve/MoebiusTwistContourBoundRatio`, and the collapse of the twisted Möbius argument — the
doubling for the shortened truncation height and the majorisation of the coefficient — applies to
the second factor unchanged.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The twisted damped contour bound, factored.** -/
theorem exists_norm_tsum_dampedTwist_smoothWeight_le_ratio_factored {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∀ N H L : ℝ, 0 < N → 1 ≤ H → N / H ≤ L → ∀ (τ : ℝ) (K : ℕ), K₀ ≤ K →
        5 + 4 * |τ| ≤ (K : ℝ) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P t τ n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ dampedCorrBound P (leftAbscissa K)
          * (2 * (invZetaRightBound K
                * (C * (L + 2) ^ 2 * (N + H + 1) ^ rightAbscissa K)) / twistHeight K τ
            + invZetaEdgeBound K * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
                / (twistHeight K τ) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
            + invZetaEdgeBound K * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
                / (twistHeight K τ) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
            + max M₀ (invZetaEdgeBound K)
                * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K)
                    + 2 * (C * (L + 2) ^ 2 * (N + H + 1) ^ leftAbscissa K))) := by
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_dampedTwist_smoothWeight_le_ratio hPprime
  refine ⟨C, C', M₀, K₀, hC, hC', hM₀, fun t ht0 ht1 N H L hN hH1 hL τ K hKle hKτ => ?_⟩
  refine le_trans (hmain t ht0 ht1 N H L hN hH1 hL τ K hKle hKτ) (le_of_eq ?_)
  ring

/-- **The twisted damped smoothed sum at arbitrary smoothing width, against the majorant.** -/
theorem exists_norm_tsum_dampedTwist_smoothWeight_le_majorant_ratio {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∀ N H L : ℝ, 0 < N → 1 ≤ H → N / H ≤ L → 0 ≤ L →
      1 ≤ Real.log (N + H) → 2 ≤ (Real.log (N + H)) ^ ((1 : ℝ) / 10) →
      K₀ ≤ contourParam (N + H) →
      ∀ τ : ℝ, 5 + 4 * |τ| ≤ ((contourParam (N + H) : ℕ) : ℝ) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P t τ n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ dampedCorrBound P (leftAbscissa (contourParam (N + H)))
          * (2 * ((N + H + 1)
              * coeffMajorant (C * (L + 2) ^ 2) (C' * (L + 2)) M₀ (1024 / zeroFreeConst)
                  ((Real.log (N + H)) ^ ((1 : ℝ) / 10))
              * Real.exp (-(zeroFreeConst * (Real.log (N + H)) ^ ((1 : ℝ) / 10) / 8192)))) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_dampedTwist_smoothWeight_le_ratio_factored hPprime
  refine ⟨C, C', M₀, K₀, hC, hC', hM₀,
    fun t ht0 ht1 N H L hN hH1 hL hL0 hlog1 hlog2 hK τ hKτ => ?_⟩
  have hH : (0 : ℝ) < H := by linarith
  set x : ℝ := N + H with hxdef
  have hx0 : (0 : ℝ) < x := by rw [hxdef]; linarith
  have hL2 : (0 : ℝ) ≤ L + 2 := by linarith
  have hĈ : (0 : ℝ) ≤ C * (L + 2) ^ 2 := by positivity
  have hĈ' : (0 : ℝ) ≤ C' * (L + 2) := by positivity
  have ht : (2 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 10) := hlog2
  have ht1' : (1 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 10) := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (contourParam x) := le_trans ht1' (le_log_contourParam x)
  have hgap : rightAbscissa (contourParam x) - leftAbscissa (contourParam x) ≤ 1 :=
    gap_le_one hL1
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  have hL9 : (1 : ℝ) ≤ (Real.log (contourParam x)) ^ 9 := one_le_pow₀ hL1
  have h16 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log (contourParam x)) ^ 9) := by positivity
  have h2p : (0 : ℝ) < zeroFreeConst / (2 * (Real.log (contourParam x)) ^ 9) := by positivity
  have h16le : zeroFreeConst / (16 * (Real.log (contourParam x)) ^ 9) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  have hcpos : 0 < leftAbscissa (contourParam x) := by rw [leftAbscissa]; linarith
  have hchalf : (1 : ℝ) / 2 ≤ leftAbscissa (contourParam x) := by
    rw [leftAbscissa]; linarith
  have hgapnn : 0 ≤ rightAbscissa (contourParam x) - leftAbscissa (contourParam x) := by
    rw [rightAbscissa, leftAbscissa]; linarith
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
  have hbase := hmain t ht0 ht1 N H L hN hH1 hL τ (contourParam x) hK hKτ
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
  exact norm_tsum_damped_le_of_moebius_shape hP2 hchalf hbase
    (le_trans hcomb (by linarith))

end

end RHTower.Sieve
