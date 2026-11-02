import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheLinearMomentRemovesTheOverlapLogarithm

/-!
# Linear overlap bounds control both packet arguments

The overlap matrix is symmetric. Polarization and a balanced rescaling turn
its linear quadratic bound into a bilinear bound on each conductor space.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis

private theorem overlapMatrix_hermitian (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    (overlapMatrix φ c N).IsHermitian := by
  change Matrix.conjTranspose (overlapMatrix φ c N) = overlapMatrix φ c N
  ext i j
  change overlapMatrix φ c N j i = overlapMatrix φ c N i j
  dsimp only [overlapMatrix]
  have hcond : ((j : ℕ) ≠ i ∧ |Real.log (i : ℕ) - Real.log (j : ℕ)| ≤ 2 * (c / N)) ↔
      ((i : ℕ) ≠ j ∧ |Real.log (j : ℕ) - Real.log (i : ℕ)| ≤ 2 * (c / N)) := by
    rw [ne_comm, abs_sub_comm]
  rw [hcond]
  split_ifs
  · rw [atomArchPair_comm _ (j : ℕ) (i : ℕ), archimedeanCenterKernel_comm (j : ℕ) (i : ℕ)]
  · rfl

/-- Linear overlap control is bilinear on the whole conductor space. -/
theorem exists_overlapMatrix_inner_le_linear {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R N : ℕ} {c : ℝ},
      2 ≤ R → R ^ 4 ≤ N → 18 * (1 + Real.log R) ≤ Real.log N →
      1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
      ∀ {u v : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R N → v ∈ conductorSubspace R N →
        |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, v⟫| ≤ C * c * ‖u‖ * ‖v‖ := by
  obtain ⟨C, hC, hquad⟩ := exists_overlapMatrix_self_inner_le_linear hφ hsupp hM
  refine ⟨C, hC, ?_⟩
  intro R N c hR hR4 hlog hc hcL hw u v hu hv
  let A := Matrix.toEuclideanLin (overlapMatrix φ c N)
  let V := conductorSubspace R N
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr (overlapMatrix_hermitian φ c N)
  have hsumBound (x y : EuclideanSpace ℝ (PrimeHorizonIndex N))
      (hx : x ∈ V) (hy : y ∈ V) :
      |⟪A x, y⟫| ≤ C * c / 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have hplus := hquad hR hR4 hlog hc hcL hw (V.add_mem hx hy)
    have hminus := hquad hR hR4 hlog hc hcL hw (V.sub_mem hx hy)
    have hswap : ⟪A y, x⟫ = ⟪A x, y⟫ := by
      rw [hsym y x, real_inner_comm y (A x)]
    have hpolar : ⟪A (x + y), x + y⟫ - ⟪A (x - y), x - y⟫ = 4 * ⟪A x, y⟫ := by
      simp only [map_add, map_sub, inner_add_left, inner_sub_left, inner_add_right, inner_sub_right]
      rw [hswap]
      ring
    have hpar : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      rw [← real_inner_self_eq_norm_sq (x + y), ← real_inner_self_eq_norm_sq (x - y)]
      simp only [inner_add_left, inner_sub_left, inner_add_right, inner_sub_right,
        real_inner_self_eq_norm_sq]
      ring
    have hh := (abs_sub ⟪A (x + y), x + y⟫ ⟪A (x - y), x - y⟫).trans
      (add_le_add hplus hminus)
    rw [hpolar, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hh
    rw [← mul_add, hpar] at hh
    linarith only [hh]
  by_cases hu0 : u = 0
  · simp only [hu0, map_zero, inner_zero_left, abs_zero, norm_zero, mul_zero, zero_mul, le_refl]
  by_cases hv0 : v = 0
  · simp only [hv0, inner_zero_right, abs_zero, norm_zero, mul_zero, le_refl]
  have huPos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hvPos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hh := hsumBound (‖v‖ • u) (‖u‖ • v) (V.smul_mem _ hu) (V.smul_mem _ hv)
  rw [map_smul, real_inner_smul_left, real_inner_smul_right, abs_mul, abs_mul,
    abs_of_pos hvPos, abs_of_pos huPos, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hvPos, abs_of_pos huPos] at hh
  apply (mul_le_mul_iff_right₀ (mul_pos huPos hvPos)).mp
  convert hh using 1 <;> ring

#print axioms exists_overlapMatrix_inner_le_linear

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
