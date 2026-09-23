import GaloisForLFunctions.HTGeometry.HermitianTraceNorm

/-!
# Guth–Maynard, Lemma 4.1: the singular-value bound

For a rectangular matrix `M : Matrix W N ℂ` and a vector `b`,
`‖M b‖² ≤ λ_max(M Mᴴ) ‖b‖²`.  This is the first inequality of Guth–Maynard's Lemma 4.1
(arXiv 2405.20552): `Σ_{t ∈ W} |D_N(t)|² = ‖M_W b‖² ≤ s₁(M_W)² ‖b‖²`, with the squared top singular
value read as the top eigenvalue of the Hermitian matrix `M Mᴴ` on the *row* side, which is the side
on which the cubic-trace argument (Lemma 4.2) is normalized.

The proof avoids identifying the nonzero spectra of `Mᴴ M` and `M Mᴴ`: with `u = M b`,
`‖u‖² = Re ⟨Mᴴ u, b⟩ ≤ ‖Mᴴ u‖ ‖b‖` and `‖Mᴴ u‖² = Re ⟨(M Mᴴ) u, u⟩ ≤ λ_max ‖u‖²` (Rayleigh), so
`‖u‖ ≤ √λ_max ‖b‖`.
-/

open Matrix Finset

namespace RHTower.GuthMaynard

/-- `Σ_i ‖x_i‖²` is the real part of `star x ⬝ᵥ x`. -/
theorem re_star_dotProduct_self {n : Type*} [Fintype n] (x : n → ℂ) :
    (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ (2 : ℕ) := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- `Re (conj z · (r z)) = r ‖z‖²` for real `r`. -/
theorem re_conj_mul_real_mul (z : ℂ) (r : ℝ) :
    ((starRingEnd ℂ) z * ((r : ℂ) * z)).re = r * ‖z‖ ^ (2 : ℕ) := by
  rw [show (starRingEnd ℂ) z * ((r : ℂ) * z) = (r : ℂ) * (z * (starRingEnd ℂ) z) by ring,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Rayleigh bound.** For a Hermitian matrix whose eigenvalues are all `≤ μ`,
`Re (star v ⬝ᵥ A v) ≤ μ Σ ‖v_i‖²`. -/
theorem re_star_dotProduct_mulVec_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {μ : ℝ} (hμ : ∀ i, hA.eigenvalues i ≤ μ) (v : n → ℂ) :
    (star v ⬝ᵥ (A *ᵥ v)).re ≤ μ * ∑ i, ‖v i‖ ^ (2 : ℕ) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hUU : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at this
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef
  have hdiag : A = U * D * Uᴴ := GaloisForLFunctions.HTGeometry.hermitian_eq_conj_diagonal hA
  set w : n → ℂ := Uᴴ *ᵥ v with hwdef
  -- `star v ᵥ* U = star w`
  have hsw : star w = star v ᵥ* U := by
    rw [hwdef, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  -- the quadratic form in the eigenbasis
  have key : star v ⬝ᵥ (A *ᵥ v) = star w ⬝ᵥ (D *ᵥ w) := by
    conv_lhs => rw [hdiag]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← hsw]
  -- the norm is preserved
  have hnorm : star w ⬝ᵥ w = star v ⬝ᵥ v := by
    rw [hsw, ← dotProduct_mulVec, hwdef, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hnorm' : ∑ i, ‖w i‖ ^ (2 : ℕ) = ∑ i, ‖v i‖ ^ (2 : ℕ) := by
    rw [← re_star_dotProduct_self, ← re_star_dotProduct_self, hnorm]
  -- evaluate the diagonal form
  have hform : (star w ⬝ᵥ (D *ᵥ w)).re = ∑ i, hA.eigenvalues i * ‖w i‖ ^ (2 : ℕ) := by
    simp only [dotProduct, Complex.re_sum, Pi.star_apply, hDdef, Matrix.mulVec_diagonal,
      Function.comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := re_conj_mul_real_mul (w i) (hA.eigenvalues i)
    simpa [Complex.star_def] using this
  rw [key, hform, ← hnorm', Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hμ i) (by positivity)

/-- Cauchy–Schwarz for the dot product: `Re (star x ⬝ᵥ y) ≤ √(Σ‖x‖²) √(Σ‖y‖²)`. -/
theorem re_star_dotProduct_le_sqrt_mul_sqrt {n : Type*} [Fintype n] (x y : n → ℂ) :
    (star x ⬝ᵥ y).re ≤ Real.sqrt (∑ i, ‖x i‖ ^ (2 : ℕ)) * Real.sqrt (∑ i, ‖y i‖ ^ (2 : ℕ)) := by
  set X : EuclideanSpace ℂ n := WithLp.toLp 2 x
  set Y : EuclideanSpace ℂ n := WithLp.toLp 2 y
  have hinner : inner ℂ X Y = star x ⬝ᵥ y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hX : ‖X‖ = Real.sqrt (∑ i, ‖x i‖ ^ (2 : ℕ)) := EuclideanSpace.norm_eq X
  have hY : ‖Y‖ = Real.sqrt (∑ i, ‖y i‖ ^ (2 : ℕ)) := EuclideanSpace.norm_eq Y
  calc (star x ⬝ᵥ y).re ≤ ‖star x ⬝ᵥ y‖ := Complex.re_le_norm _
    _ = ‖inner ℂ X Y‖ := by rw [hinner]
    _ ≤ ‖X‖ * ‖Y‖ := norm_inner_le_norm X Y
    _ = _ := by rw [hX, hY]

/-- **Guth–Maynard Lemma 4.1.** If every eigenvalue of `M Mᴴ` is at most `μ ≥ 0`, then
`Σ_t ‖(M b)_t‖² ≤ μ Σ_n ‖b_n‖²`. -/
theorem sum_normSq_mulVec_le {W N : Type*} [Fintype W] [Fintype N] [DecidableEq W]
    (M : Matrix W N ℂ) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ i, (Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues i ≤ μ) (b : N → ℂ) :
    ∑ t, ‖(M *ᵥ b) t‖ ^ (2 : ℕ) ≤ μ * ∑ j, ‖b j‖ ^ (2 : ℕ) := by
  obtain ⟨u, hu⟩ : ∃ u : W → ℂ, u = M *ᵥ b := ⟨_, rfl⟩
  rw [← hu]
  have hSu0 : 0 ≤ ∑ t, ‖u t‖ ^ (2 : ℕ) := Finset.sum_nonneg fun _ _ => by positivity
  have hSb0 : 0 ≤ ∑ j, ‖b j‖ ^ (2 : ℕ) := Finset.sum_nonneg fun _ _ => by positivity
  -- `Σ‖u‖² = Re (star (Mᴴ u) ⬝ᵥ b)`
  have e1 : star (Mᴴ *ᵥ u) ⬝ᵥ b = star u ⬝ᵥ u := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← dotProduct_mulVec, ← hu]
  have h1 : ∑ t, ‖u t‖ ^ (2 : ℕ) = (star (Mᴴ *ᵥ u) ⬝ᵥ b).re := by
    rw [e1, re_star_dotProduct_self]
  -- `Σ ‖Mᴴ u‖² ≤ μ Σ‖u‖²` by Rayleigh for `M Mᴴ`
  have e2 : star (Mᴴ *ᵥ u) ⬝ᵥ (Mᴴ *ᵥ u) = star u ⬝ᵥ ((M * Mᴴ) *ᵥ u) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← dotProduct_mulVec,
      Matrix.mulVec_mulVec]
  have h2 : ∑ j, ‖(Mᴴ *ᵥ u) j‖ ^ (2 : ℕ) ≤ μ * ∑ t, ‖u t‖ ^ (2 : ℕ) := by
    rw [← re_star_dotProduct_self, e2]
    exact re_star_dotProduct_mulVec_le (Matrix.isHermitian_mul_conjTranspose_self M) hμ u
  -- Cauchy–Schwarz
  have h3 : ∑ t, ‖u t‖ ^ (2 : ℕ) ≤ Real.sqrt (μ * ∑ t, ‖u t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j, ‖b j‖ ^ (2 : ℕ)) := by
    calc ∑ t, ‖u t‖ ^ (2 : ℕ) = (star (Mᴴ *ᵥ u) ⬝ᵥ b).re := h1
      _ ≤ Real.sqrt (∑ j, ‖(Mᴴ *ᵥ u) j‖ ^ (2 : ℕ)) * Real.sqrt (∑ j, ‖b j‖ ^ (2 : ℕ)) :=
          re_star_dotProduct_le_sqrt_mul_sqrt _ _
      _ ≤ Real.sqrt (μ * ∑ t, ‖u t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j, ‖b j‖ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
  -- conclude: `S ≤ √(μ S) √Sb` gives `S ≤ μ Sb`
  rcases eq_or_lt_of_le hSu0 with h0 | hpos
  · rw [← h0]; positivity
  · have hsq : (∑ t, ‖u t‖ ^ (2 : ℕ)) * (∑ t, ‖u t‖ ^ (2 : ℕ))
        ≤ (μ * ∑ t, ‖u t‖ ^ (2 : ℕ)) * ∑ j, ‖b j‖ ^ (2 : ℕ) := by
      have hm := mul_le_mul h3 h3 hSu0 (by positivity)
      calc (∑ t, ‖u t‖ ^ (2 : ℕ)) * (∑ t, ‖u t‖ ^ (2 : ℕ))
          ≤ (Real.sqrt (μ * ∑ t, ‖u t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j, ‖b j‖ ^ (2 : ℕ))) *
              (Real.sqrt (μ * ∑ t, ‖u t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j, ‖b j‖ ^ (2 : ℕ))) := hm
        _ = (Real.sqrt (μ * ∑ t, ‖u t‖ ^ (2 : ℕ)) * Real.sqrt (μ * ∑ t, ‖u t‖ ^ (2 : ℕ))) *
              (Real.sqrt (∑ j, ‖b j‖ ^ (2 : ℕ)) * Real.sqrt (∑ j, ‖b j‖ ^ (2 : ℕ))) := by ring
        _ = (μ * ∑ t, ‖u t‖ ^ (2 : ℕ)) * ∑ j, ‖b j‖ ^ (2 : ℕ) := by
            rw [Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt hSb0]
    have : (∑ t, ‖u t‖ ^ (2 : ℕ)) * (∑ t, ‖u t‖ ^ (2 : ℕ))
        ≤ (∑ t, ‖u t‖ ^ (2 : ℕ)) * (μ * ∑ j, ‖b j‖ ^ (2 : ℕ)) := by linarith [hsq]
    exact le_of_mul_le_mul_left this hpos

end RHTower.GuthMaynard
