import GaloisForLFunctions.RHTower.Sieve.MoebiusContourBoundRatio
import GaloisForLFunctions.RHTower.Sieve.MoebiusMajorantBound

/-!
# The ratio bound against the majorant

The collapse lemmas take the contour bound's constants as parameters, so the price `(L+2)²` of
narrow smoothing needs no separate treatment: substituting `C·(L+2)²` and `C'·(L+2)` for the two
constants makes the ratio bound an instance of the same chain that produced the diagonal one.

The result is the trivial size `N+H+1` times a majorant in which `L` appears only inside the
polynomial coefficient.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- **The smoothed Möbius sum at arbitrary smoothing width, against the majorant.** -/
theorem exists_norm_tsum_moebius_smoothWeight_le_majorant_ratio :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ N H L : ℝ, 0 < N → 1 ≤ H → N / H ≤ L → 0 ≤ L →
      1 ≤ Real.log (N + H) → 2 ≤ (Real.log (N + H)) ^ ((1 : ℝ) / 10) →
      K₀ ≤ contourParam (N + H) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ (N + H + 1)
            * coeffMajorant (C * (L + 2) ^ 2) (C' * (L + 2)) M₀ (1024 / zeroFreeConst)
                ((Real.log (N + H)) ^ ((1 : ℝ) / 10))
            * Real.exp (-(zeroFreeConst * (Real.log (N + H)) ^ ((1 : ℝ) / 10) / 8192)) := by
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_moebius_smoothWeight_le_ratio
  refine ⟨C, C', M₀, K₀, hC, hC', hM₀, fun N H L hN hH1 hL hL0 hlog1 hlog2 hK => ?_⟩
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
  have hbase := hmain N H L hN hH1 hL (contourParam x) hK
  have hcomb := combined_terms_le (x := x) (C := C * (L + 2) ^ 2) (C' := C' * (L + 2))
    (R := invZetaRightBound (contourParam x)) (E := invZetaEdgeBound (contourParam x))
    (M₀ := M₀) hlog1 ht hx0 hy hx1le hĈ hĈ'
    (invZetaRightBound_nonneg _) (invZetaEdgeBound_nonneg _) hM₀ hgap
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
  exact le_trans hbase (le_trans hcomb hfinal)

end RHTower.Sieve
