import GaloisForLFunctions.HTGeometry.CaratheodoryFejerRankCorankOne

/-!
# Connes--van Suijlekom: exact Toeplitz corank-one corollary

This file closes the scale mismatch between the normalized finite
Carathéodory--Fejér factorization and Corollary 1.1 of
Connes--van Suijlekom, arXiv:2511.23257v1.  The published statement allows
an arbitrary positive semidefinite Toeplitz scale; normalization is justified
inside the proof because positive rank forces the zeroth Toeplitz moment to be
strictly positive.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A positive semidefinite Toeplitz section with zero zeroth moment is zero.
This is the scale-degenerate branch excluded by a positive corank-one rank. -/
theorem circleToeplitzGram_eq_zero_of_zero_moment
    {N : ℕ} {c : ℤ → ℂ} (hc : IsHermitianMoment c) (hc0 : c 0 = 0)
    (hG : (circleToeplitzGram N c).PosSemidef) :
    circleToeplitzGram N c = 0 := by
  let e0 : Fin (N + 1) → ℂ := Pi.single 0 1
  have hquad : star e0 ⬝ᵥ (circleToeplitzGram N c *ᵥ e0) = 0 := by
    simp [e0, Pi.single_apply, circleToeplitzGram, dotProduct, Matrix.mulVec, hc0]
  have hmul : circleToeplitzGram N c *ᵥ e0 = 0 :=
    (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hG e0).mp hquad
  ext i j
  have hcol : ∀ k : Fin (N + 1), c (k : ℤ) = 0 := by
    intro k
    have hk := congrFun hmul k
    simpa [e0, circleToeplitzGram, Matrix.mulVec] using hk
  change c (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) = 0
  by_cases hij : i ≤ j
  · have hdiff : (j : ℕ) - (i : ℕ) ≤ N := by omega
    have hpos : c (((j : ℕ) - (i : ℕ) : ℕ) : ℤ) = 0 :=
      hcol ⟨j - i, by omega⟩
    rw [show ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) =
      -(((j : ℕ) - (i : ℕ) : ℕ) : ℤ) by omega, hc (j - i)]
    simpa [hpos]
  · have hdiff : (i : ℕ) - (j : ℕ) ≤ N := by omega
    have hpos : c (((i : ℕ) - (j : ℕ) : ℕ) : ℤ) = 0 :=
      hcol ⟨i - j, by omega⟩
    have hji : (j : ℕ) < (i : ℕ) := Nat.lt_of_not_ge hij
    rw [show ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) =
      (((i : ℕ) - (j : ℕ) : ℕ) : ℤ) by omega]
    exact hpos

/-- Positive zeroth moment forced by PSD and positive Toeplitz rank. -/
theorem circleToeplitzGram_mass_pos_of_rank_eq
    {N : ℕ} (hN : 0 < N) {c : ℤ → ℂ} (hc : IsHermitianMoment c)
    (hG : (circleToeplitzGram N c).PosSemidef)
    (hRank : (circleToeplitzGram N c).rank = N) :
    0 < (c 0).re := by
  have hc0ne : c 0 ≠ 0 := by
    intro hc0
    have hz := circleToeplitzGram_eq_zero_of_zero_moment hc hc0 hG
    rw [hz, Matrix.rank_zero] at hRank
    omega
  have hdiag : 0 ≤ c 0 := by
    simpa [circleToeplitzGram] using
      (hG.diag_nonneg (i := (0 : Fin (N + 1))))
  have hdiagRe : 0 ≤ (c 0).re := (Complex.nonneg_iff.mp hdiag).1
  have hreal : c 0 = ((c 0).re : ℂ) := by
    apply Complex.ext
    · simp
    · have him := congrArg Complex.im (hc 0)
      have him' : (c 0).im = -(c 0).im := by simpa using him
      have himzero : (c 0).im = 0 := by linarith
      exact himzero
  exact lt_of_le_of_ne hdiagRe (by
    intro hm
    apply hc0ne
    have hm' : (c 0).re = 0 := hm.symm
    rw [hreal, hm']
    simp)

/-- Nonzero scalar multiplication preserves finite matrix rank. -/
theorem rank_smul_matrix_of_ne_zero
    {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} {a : ℂ}
    (ha : a ≠ 0) :
    (a • A).rank = A.rank := by
  have hdet : IsUnit ((a • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)).det) := by
    rw [Matrix.det_smul, Matrix.det_one]
    apply (isUnit_iff_ne_zero).2
    simpa using (pow_ne_zero (Fintype.card (Fin (N + 1))) ha)
  have hmul : A * (a • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) = a • A := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
    ring
  rw [← hmul]
  exact Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet

/-- **Connes--van Suijlekom, Corollary 1.1.**

For a Hermitian positive semidefinite Toeplitz section of rank `N`, every
zero of the polynomial attached to a kernel vector lies on the unit circle.
The moment encoding is the corpus's exact finite Toeplitz encoding of the
source matrix; no normalization or extra analytic hypothesis is assumed. -/
theorem connesVanSuijlekom_corollary_1_1
    {N : ℕ} (c : ℤ → ℂ) (hc : IsHermitianMoment c)
    (hG : (circleToeplitzGram N c).PosSemidef)
    (hRank : (circleToeplitzGram N c).rank = N)
    (xi : Fin (N + 1) → ℂ)
    (hker : circleToeplitzGram N c *ᵥ xi = 0) :
    ∀ {w : ℂ}, w ∈ (finiteToeplitzKernelPolynomial xi).roots → ‖w‖ = 1 := by
  intro w hw
  by_cases hxi : finiteToeplitzKernelPolynomial xi = 0
  · simp [hxi] at hw
  · cases N with
    | zero =>
        have hdegree : (finiteToeplitzKernelPolynomial xi).natDegree ≤ 0 := by
          simpa using natDegree_finiteToeplitzKernelPolynomial_le xi
        have hcard : (finiteToeplitzKernelPolynomial xi).roots.card = 0 := by
          apply Nat.eq_zero_of_le_zero
          exact (Polynomial.card_roots' _).trans hdegree
        rw [Multiset.card_eq_zero.mp hcard] at hw
        simpa using hw
    | succ N =>
        let m : ℝ := (c 0).re
        have hmpos : 0 < m := by
          dsimp [m]
          exact circleToeplitzGram_mass_pos_of_rank_eq (N := N + 1) (by omega) hc hG hRank
        let cn : ℤ → ℂ := fun q => ((m⁻¹ : ℝ) : ℂ) * c q
        have hcn : IsHermitianMoment cn := by
          intro r
          simp only [cn, starRingEnd_apply, star_mul]
          rw [hc r]
          simp [mul_comm]
        have hc0real : c 0 = (m : ℂ) := by
          dsimp [m]
          apply Complex.ext
          · simp
          · have him := congrArg Complex.im (hc 0)
            have him' : (c 0).im = -(c 0).im := by simpa using him
            have himzero : (c 0).im = 0 := by linarith
            exact himzero
        have hcn0 : cn 0 = 1 := by
          dsimp [cn]
          rw [hc0real]
          simp [hmpos.ne']
        have hscale : circleToeplitzGram (N + 1) cn =
            ((m⁻¹ : ℝ) : ℂ) • circleToeplitzGram (N + 1) c := by
          ext i j
          simp [cn, circleToeplitzGram, Matrix.smul_apply]
        have hGnorm : (circleToeplitzGram (N + 1) cn).PosSemidef := by
          rw [hscale]
          exact hG.smul (by positivity)
        have hRanknorm : (circleToeplitzGram (N + 1) cn).rank = N + 1 := by
          rw [hscale, rank_smul_matrix_of_ne_zero (A := circleToeplitzGram (N + 1) c)
            (by exact_mod_cast (inv_ne_zero hmpos.ne'))]
          exact hRank
        have hkernorm : circleToeplitzGram (N + 1) cn *ᵥ xi = 0 := by
          rw [hscale, Matrix.smul_mulVec, hker]
          simp
        exact circleToeplitzGram_kernel_polynomial_roots_on_unitCircle_of_rank_eq
          cn hcn hcn0 hGnorm hRanknorm xi hkernorm hxi hw

end

end GaloisForLFunctions.HTGeometry
