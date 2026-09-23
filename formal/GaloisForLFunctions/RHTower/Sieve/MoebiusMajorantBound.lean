import GaloisForLFunctions.RHTower.Sieve.CoeffMajorant
import GaloisForLFunctions.RHTower.Sieve.MoebiusContourBoundDiag

/-!
# The smoothed Möbius sum against the majorant

The contour bound at the balanced parameter, with every term collapsed and the coefficient
majorised:

    ‖ 2π ∑ₙ μ(n)·w(n) ‖  ≤  (2N+1) · coeffMajorant(t) · exp(-c₀ t / 8192),   t = (log 2N)^{1/10}.

The second and third factors together tend to zero, so the smoothed sum is `o(N)`.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- **The smoothed Möbius sum against the majorant.** -/
theorem exists_norm_tsum_moebius_smoothWeight_le_majorant :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧ ∀ N : ℝ, 1 ≤ N →
      1 ≤ Real.log (N + N) → 2 ≤ (Real.log (N + N)) ^ ((1 : ℝ) / 10) →
      K₀ ≤ contourParam (N + N) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N N (n : ℝ) : ℝ) : ℂ))‖
        ≤ (N + N + 1)
            * coeffMajorant C C' M₀ (1024 / zeroFreeConst)
                ((Real.log (N + N)) ^ ((1 : ℝ) / 10))
            * Real.exp (-(zeroFreeConst * (Real.log (N + N)) ^ ((1 : ℝ) / 10) / 8192)) := by
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_moebius_smoothWeight_le_diag 0
  refine ⟨C, C', M₀, K₀, hC, hC', hM₀, fun N hN hlog1 hlog2 hK => ?_⟩
  set x : ℝ := N + N with hxdef
  have hx0 : (0 : ℝ) < x := by rw [hxdef]; linarith
  have hx1 : (1 : ℝ) ≤ x := by rw [hxdef]; linarith
  have ht : (2 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 10) := hlog2
  have ht1 : (1 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 10) := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (contourParam x) := le_trans ht1 (le_log_contourParam x)
  have hgap : rightAbscissa (contourParam x) - leftAbscissa (contourParam x) ≤ 1 :=
    gap_le_one hL1
  -- the two logarithmic comparisons between `x` and `x + 1`
  have hx1le : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
  have hsq : x + 1 ≤ x ^ (2 : ℕ) := by nlinarith [hx1]
  have hy : Real.log (x + 1) ≤ 2 * Real.log x := by
    have h := Real.log_le_log (by linarith) hsq
    rwa [Real.log_pow] at h
  -- the contour bound
  have hbase := hmain N hN (contourParam x) hK
  have hcomb := combined_terms_le (x := x) (C := C) (C' := C')
    (R := invZetaRightBound (contourParam x)) (E := invZetaEdgeBound (contourParam x))
    (M₀ := M₀) hlog1 ht hx0 hy hx1le hC hC'
    (invZetaRightBound_nonneg _) (invZetaEdgeBound_nonneg _) hM₀ hgap
  have hcoeff := coeff_le_coeffMajorant (x := x) hlog1 hC hC' hM₀
  have hSpos : (0 : ℝ) < Real.exp (-(zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192)) :=
    Real.exp_pos _
  have hfinal : (x + 1)
      * (8 * invZetaRightBound (contourParam x) * C
          + 8 * invZetaEdgeBound (contourParam x) * C'
          + max M₀ (invZetaEdgeBound (contourParam x)) * (4 + 2 * C))
      * Real.exp (-(zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192))
      ≤ (x + 1)
          * coeffMajorant C C' M₀ (1024 / zeroFreeConst) ((Real.log x) ^ ((1 : ℝ) / 10))
          * Real.exp (-(zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192)) := by
    have hx10 : (0 : ℝ) ≤ x + 1 := by linarith
    gcongr
  exact le_trans hbase (le_trans hcomb hfinal)

end RHTower.Sieve
