/-
# Quantitative inverse bound for four-dimensional phase matrices

For the coordinate changes in Bourgain's argument we use the sup norm on
`Fin 4 → ℝ`.  A `4 × 4` matrix whose entries are bounded by `B` and whose
determinant has absolute value at least `d > 0` has inverse operator bound
`24 B³ / d`.  This is the elementary adjugate estimate, proved here so the
later normalized-curve distortion bound is fully explicit.
-/
import GaloisForLFunctions.RHTower.BourgainNormalizedTwoBaseJet

namespace RHTower

noncomputable section

/-- Six-term determinant bound for a `3 × 3` real matrix. -/
theorem abs_det_fin_three_le
    {A : Matrix (Fin 3) (Fin 3) ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B) :
    |A.det| ≤ 6 * B ^ (3 : ℕ) := by
  have hterm (i₁ j₁ i₂ j₂ i₃ j₃ : Fin 3) :
      |A i₁ j₁ * A i₂ j₂ * A i₃ j₃| ≤ B ^ (3 : ℕ) := by
    rw [abs_mul, abs_mul]
    calc
      |A i₁ j₁| * |A i₂ j₂| * |A i₃ j₃| ≤
          B * B * B := by
        gcongr <;> exact hA _ _
      _ = B ^ (3 : ℕ) := by ring
  rw [Matrix.det_fin_three]
  let t₁ := A 0 0 * A 1 1 * A 2 2
  let t₂ := A 0 0 * A 1 2 * A 2 1
  let t₃ := A 0 1 * A 1 0 * A 2 2
  let t₄ := A 0 1 * A 1 2 * A 2 0
  let t₅ := A 0 2 * A 1 0 * A 2 1
  let t₆ := A 0 2 * A 1 1 * A 2 0
  have htri :
      |t₁ - t₂ - t₃ + t₄ + t₅ - t₆| ≤
        |t₁| + |t₂| + |t₃| + |t₄| + |t₅| + |t₆| := by
    calc
      |t₁ - t₂ - t₃ + t₄ + t₅ - t₆| ≤
          |t₁ - t₂ - t₃ + t₄ + t₅| + |t₆| := abs_sub _ _
      _ ≤ (|t₁ - t₂ - t₃ + t₄| + |t₅|) + |t₆| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((|t₁ - t₂ - t₃| + |t₄|) + |t₅|) + |t₆| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (((|t₁ - t₂| + |t₃|) + |t₄|) + |t₅|) + |t₆| := by
        gcongr
        exact abs_sub _ _
      _ ≤ ((((|t₁| + |t₂|) + |t₃|) + |t₄|) + |t₅|) + |t₆| := by
        gcongr
        exact abs_sub _ _
      _ = |t₁| + |t₂| + |t₃| + |t₄| + |t₅| + |t₆| := by ring
  have ht₁ : |t₁| ≤ B ^ (3 : ℕ) := hterm 0 0 1 1 2 2
  have ht₂ : |t₂| ≤ B ^ (3 : ℕ) := hterm 0 0 1 2 2 1
  have ht₃ : |t₃| ≤ B ^ (3 : ℕ) := hterm 0 1 1 0 2 2
  have ht₄ : |t₄| ≤ B ^ (3 : ℕ) := hterm 0 1 1 2 2 0
  have ht₅ : |t₅| ≤ B ^ (3 : ℕ) := hterm 0 2 1 0 2 1
  have ht₆ : |t₆| ≤ B ^ (3 : ℕ) := hterm 0 2 1 1 2 0
  change |t₁ - t₂ - t₃ + t₄ + t₅ - t₆| ≤ _
  linarith

/-- Every cofactor of a `4 × 4` matrix with entries bounded by `B` is
bounded by `6B³`. -/
theorem abs_adjugate_fin_four_apply_le
    {A : Matrix (Fin 4) (Fin 4) ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B)
    (i j : Fin 4) :
    |A.adjugate i j| ≤ 6 * B ^ (3 : ℕ) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [abs_mul]
  have hsign : |((-1 : ℝ) ^ (↑j + ↑i : ℕ))| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [hsign, one_mul]
  apply abs_det_fin_three_le hB
  intro k l
  exact hA _ _

/-- Entrywise inverse bound obtained from the adjugate formula. -/
theorem abs_nonsing_inv_apply_le
    {A : Matrix (Fin 4) (Fin 4) ℝ} {B d : ℝ}
    (hB : 0 ≤ B) (hd : 0 < d)
    (hA : ∀ i j, |A i j| ≤ B)
    (hdet : d ≤ |A.det|)
    (i j : Fin 4) :
    |A⁻¹ i j| ≤ 6 * B ^ (3 : ℕ) / d := by
  have hdet0 : 0 < |A.det| := hd.trans_le hdet
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  change |A.det⁻¹ * A.adjugate i j| ≤ _
  rw [abs_mul, abs_inv]
  have hinv : |A.det|⁻¹ ≤ d⁻¹ :=
    (inv_le_inv₀ hdet0 hd).2 hdet
  have hadj :=
    abs_adjugate_fin_four_apply_le hB hA i j
  calc
    |A.det|⁻¹ * |A.adjugate i j| ≤
        d⁻¹ * (6 * B ^ (3 : ℕ)) :=
      mul_le_mul hinv hadj (abs_nonneg _) (inv_nonneg.mpr hd.le)
    _ = 6 * B ^ (3 : ℕ) / d := by field_simp

/-- Sup-norm bound for the inverse matrix acting on phase space. -/
theorem norm_nonsing_inv_mulVec_le
    {A : Matrix (Fin 4) (Fin 4) ℝ} {B d : ℝ}
    (hB : 0 ≤ B) (hd : 0 < d)
    (hA : ∀ i j, |A i j| ≤ B)
    (hdet : d ≤ |A.det|)
    (x : Fin 4 → ℝ) :
    ‖A⁻¹.mulVec x‖ ≤ (24 * B ^ (3 : ℕ) / d) * ‖x‖ := by
  have hC0 : 0 ≤ 24 * B ^ (3 : ℕ) / d := by positivity
  rw [pi_norm_le_iff_of_nonneg
    (mul_nonneg hC0 (norm_nonneg x))]
  intro i
  change ‖∑ j, A⁻¹ i j * x j‖ ≤ _
  rw [Fin.sum_univ_four]
  have hx (j : Fin 4) : ‖x j‖ ≤ ‖x‖ :=
    norm_apply_le_norm_bourgainPhaseSpace x j
  have hterm (j : Fin 4) :
      ‖A⁻¹ i j * x j‖ ≤
        (6 * B ^ (3 : ℕ) / d) * ‖x‖ := by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul
      (abs_nonsing_inv_apply_le hB hd hA hdet i j)
      (hx j) (norm_nonneg _) (by positivity)
  calc
    ‖A⁻¹ i 0 * x 0 + A⁻¹ i 1 * x 1 +
        A⁻¹ i 2 * x 2 + A⁻¹ i 3 * x 3‖ ≤
      ‖A⁻¹ i 0 * x 0‖ + ‖A⁻¹ i 1 * x 1‖ +
        ‖A⁻¹ i 2 * x 2‖ + ‖A⁻¹ i 3 * x 3‖ := norm_add₄_le
    _ ≤ (24 * B ^ (3 : ℕ) / d) * ‖x‖ := by
      have h0 := hterm 0
      have h1 := hterm 1
      have h2 := hterm 2
      have h3 := hterm 3
      calc
        ‖A⁻¹ i 0 * x 0‖ + ‖A⁻¹ i 1 * x 1‖ +
            ‖A⁻¹ i 2 * x 2‖ + ‖A⁻¹ i 3 * x 3‖ ≤
            4 * ((6 * B ^ (3 : ℕ) / d) * ‖x‖) := by
          linarith
        _ = (24 * B ^ (3 : ℕ) / d) * ‖x‖ := by ring

end

end RHTower
