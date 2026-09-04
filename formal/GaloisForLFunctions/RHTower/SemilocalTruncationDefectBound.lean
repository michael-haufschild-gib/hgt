import GaloisForLFunctions.RHTower.SemilocalBoostEntryBound
import GaloisForLFunctions.RHTower.SemilocalTwoModeRadiusResponse

/-!
# The truncation defect `tr(T(δ₁) T(δ₂))` under the boost bound

`T(δ)_{ij} = 2 Re M_{ij}(δ)`, so the boost bound controls every entry of the cosine tangent:
`|T(δ)_{ij}| ≤ 2 (cosh δ)^{-1/2} c_i c_j exp(2ij/sinh² δ)`.  Consequences:

* `|tr(T(δ₁)T(δ₂))| ≤ 4 Σ_{i,j≤n} E₁(i,j) E₂(i,j)` (determinant level, `O(εn)`);
* the row increment `tr_{n+1} − tr_n = 2 Σ_{i≤n} T₁(i,n+1) T₂(i,n+1) + T₁(n+1,n+1) T₂(n+1,n+1)`
  is bounded by `8 Σ_{i≤n+1} E₁(i,n+1) E₂(i,n+1)` (radius level, `O(ε)`);
* **the two-prime cross term at the squared-radius level is the beat-mode jet up to an explicit
  `O((cosh δ₁ cosh δ₂)^{-1/2})` error** (`abs_bilinearSquaredRadiusJet_sub_beat_le`).
-/

open Matrix Real MeasureTheory Filter Topology Finset
open scoped BigOperators

namespace RHTower
namespace CosineModeResponse

open MeixnerPollaczek FirstEulerCriticalJet

/-! ## Tangent entries as real parts of boost entries -/

theorem cosineModeTangent_apply_eq (δ : ℝ) (n : ℕ) (i j : Fin (n + 1)) :
    cosineModeTangent δ n i j = 2 * (boostMatrixEntry δ i j).re := by
  show 2 * (∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s * Real.cos (δ * s)
    ∂semilocalArchimedeanGammaMeasure) = 2 * (boostMatrixEntry δ i j).re
  congr 1
  unfold boostMatrixEntry
  have h := Complex.reCLM.integral_comp_comm (integrable_eval_mul_eval_mul_cexp i j δ)
  simp only [Complex.reCLM_apply] at h
  rw [← h]
  congr 1
  funext s
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp [Complex.mul_re, Complex.mul_im]

theorem cosineModeTangent_symm (δ : ℝ) (n : ℕ) (i j : Fin (n + 1)) :
    cosineModeTangent δ n i j = cosineModeTangent δ n j i := by
  show 2 * (∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s * Real.cos (δ * s)
    ∂semilocalArchimedeanGammaMeasure) = 2 * (∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial j).eval s *
    (semilocalArchimedeanJacobiPolynomial i).eval s * Real.cos (δ * s)
    ∂semilocalArchimedeanGammaMeasure)
  congr 2
  funext s
  ring

theorem cosineModeTangent_castSucc (δ : ℝ) (n : ℕ) (i j : Fin (n + 1)) :
    cosineModeTangent δ (n + 1) (Fin.castSucc i) (Fin.castSucc j) = cosineModeTangent δ n i j := rfl

/-- The entry bound `E(δ; i, j) = (cosh δ)^{-1/2} c_i c_j exp(2ij/sinh² δ)`. -/
noncomputable def entryBound (δ : ℝ) (i j : ℕ) : ℝ :=
  Real.cosh δ ^ (-(1 / 2 : ℝ)) * semilocalArchimedeanJacobiNormalization i *
    semilocalArchimedeanJacobiNormalization j * Real.exp (2 * i * j / Real.sinh δ ^ 2)

theorem entryBound_nonneg (δ : ℝ) (i j : ℕ) : 0 ≤ entryBound δ i j := by
  unfold entryBound
  have := normalization_pos' i
  have := normalization_pos' j
  have := Real.rpow_nonneg (Real.cosh_pos δ).le (-(1 / 2 : ℝ))
  positivity

theorem entryBound_symm (δ : ℝ) (i j : ℕ) : entryBound δ i j = entryBound δ j i := by
  unfold entryBound
  rw [show (2 : ℝ) * i * j = 2 * j * i by ring]
  ring

theorem norm_boostMatrixEntry_le_entryBound {δ : ℝ} (hδ : 0 < δ) (i j : ℕ) :
    ‖boostMatrixEntry δ i j‖ ≤ entryBound δ i j := by
  have h := norm_boostMatrixEntry_le hδ i j
  have hτ : Real.tanh δ ^ (i + j) ≤ 1 := pow_le_one₀ (tanh_nonneg' hδ.le) (Real.tanh_lt_one δ).le
  have hpos : 0 ≤ Real.cosh δ ^ (-(1 / 2 : ℝ)) * semilocalArchimedeanJacobiNormalization i *
      semilocalArchimedeanJacobiNormalization j * Real.exp (2 * i * j / Real.sinh δ ^ 2) :=
    entryBound_nonneg δ i j
  unfold entryBound
  calc ‖boostMatrixEntry δ i j‖ ≤ _ := h
    _ = (Real.cosh δ ^ (-(1 / 2 : ℝ)) * semilocalArchimedeanJacobiNormalization i *
          semilocalArchimedeanJacobiNormalization j * Real.exp (2 * i * j / Real.sinh δ ^ 2)) *
          Real.tanh δ ^ (i + j) := by ring
    _ ≤ (Real.cosh δ ^ (-(1 / 2 : ℝ)) * semilocalArchimedeanJacobiNormalization i *
          semilocalArchimedeanJacobiNormalization j * Real.exp (2 * i * j / Real.sinh δ ^ 2)) * 1 :=
        mul_le_mul_of_nonneg_left hτ hpos
    _ = _ := by ring

/-- `|T(δ)_{ij}| ≤ 2 E(δ; i, j)`. -/
theorem abs_cosineModeTangent_le {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (i j : Fin (n + 1)) :
    |cosineModeTangent δ n i j| ≤ 2 * entryBound δ i j := by
  rw [cosineModeTangent_apply_eq, abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left
    ((Complex.abs_re_le_norm _).trans (norm_boostMatrixEntry_le_entryBound hδ i j)) (by norm_num)

/-- `|m_j(δ)| ≤ E(δ; j, j)`. -/
theorem abs_cosineDiagonalMoment_le {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    |cosineDiagonalMoment δ j| ≤ entryBound δ j j := by
  rw [cosineDiagonalMoment_eq_re_boostMatrixEntry]
  exact (Complex.abs_re_le_norm _).trans (norm_boostMatrixEntry_le_entryBound hδ j j)

/-! ## The truncation defect -/

/-- `D_n = tr(T(δ₁) T(δ₂))` on indices `0..n`. -/
noncomputable def truncationDefect (δ₁ δ₂ : ℝ) (n : ℕ) : ℝ :=
  Matrix.trace (cosineModeTangent δ₁ n * cosineModeTangent δ₂ n)

theorem truncationDefect_eq_sum (δ₁ δ₂ : ℝ) (n : ℕ) :
    truncationDefect δ₁ δ₂ n =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), cosineModeTangent δ₁ n i j * cosineModeTangent δ₂ n j i := by
  unfold truncationDefect
  simp [Matrix.trace, Matrix.mul_apply]

/-- Determinant-level bound: `|D_n| ≤ 4 Σ_{i,j} E₁(i,j) E₂(i,j)`. -/
theorem abs_truncationDefect_le {δ₁ δ₂ : ℝ} (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (n : ℕ) :
    |truncationDefect δ₁ δ₂ n| ≤
      4 * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), entryBound δ₁ i j * entryBound δ₂ i j := by
  rw [truncationDefect_eq_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, cosineModeTangent_symm δ₂ n j i]
  have ha := abs_cosineModeTangent_le h₁ n i j
  have hb := abs_cosineModeTangent_le h₂ n i j
  calc |cosineModeTangent δ₁ n i j| * |cosineModeTangent δ₂ n i j|
      ≤ (2 * entryBound δ₁ i j) * (2 * entryBound δ₂ i j) :=
        mul_le_mul ha hb (abs_nonneg _) (by have := entryBound_nonneg δ₁ i j; positivity)
    _ = 4 * (entryBound δ₁ i j * entryBound δ₂ i j) := by ring

/-- **The row increment of the defect.** -/
theorem truncationDefect_succ_sub (δ₁ δ₂ : ℝ) (n : ℕ) :
    truncationDefect δ₁ δ₂ (n + 1) - truncationDefect δ₁ δ₂ n =
      2 * ∑ i : Fin (n + 1), cosineModeTangent δ₁ (n + 1) (Fin.castSucc i) (Fin.last (n + 1)) *
          cosineModeTangent δ₂ (n + 1) (Fin.castSucc i) (Fin.last (n + 1)) +
        cosineModeTangent δ₁ (n + 1) (Fin.last (n + 1)) (Fin.last (n + 1)) *
          cosineModeTangent δ₂ (n + 1) (Fin.last (n + 1)) (Fin.last (n + 1)) := by
  rw [truncationDefect_eq_sum, truncationDefect_eq_sum]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc (n := n + 1)]
  simp only [cosineModeTangent_castSucc]
  have hsym : ∀ i : Fin (n + 1), cosineModeTangent δ₂ (n + 1) (Fin.last (n + 1)) (Fin.castSucc i) =
      cosineModeTangent δ₂ (n + 1) (Fin.castSucc i) (Fin.last (n + 1)) := fun i =>
    cosineModeTangent_symm δ₂ (n + 1) _ _
  have hsym₁ : ∀ i : Fin (n + 1), cosineModeTangent δ₁ (n + 1) (Fin.last (n + 1)) (Fin.castSucc i) =
      cosineModeTangent δ₁ (n + 1) (Fin.castSucc i) (Fin.last (n + 1)) := fun i =>
    cosineModeTangent_symm δ₁ (n + 1) _ _
  simp only [hsym, hsym₁, Finset.sum_add_distrib]
  ring

/-- Radius-level bound: `|D_{n+1} − D_n| ≤ 8 Σ_{i ≤ n+1} E₁(i, n+1) E₂(i, n+1)`. -/
theorem abs_truncationDefect_succ_sub_le {δ₁ δ₂ : ℝ} (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (n : ℕ) :
    |truncationDefect δ₁ δ₂ (n + 1) - truncationDefect δ₁ δ₂ n| ≤
      8 * ∑ i : Fin (n + 2), entryBound δ₁ i (n + 1) * entryBound δ₂ i (n + 1) := by
  rw [truncationDefect_succ_sub]
  have hterm : ∀ i : Fin (n + 2), |cosineModeTangent δ₁ (n + 1) i (Fin.last (n + 1)) *
      cosineModeTangent δ₂ (n + 1) i (Fin.last (n + 1))| ≤
      4 * (entryBound δ₁ i (n + 1) * entryBound δ₂ i (n + 1)) := by
    intro i
    rw [abs_mul]
    have ha := abs_cosineModeTangent_le h₁ (n + 1) i (Fin.last (n + 1))
    have hb := abs_cosineModeTangent_le h₂ (n + 1) i (Fin.last (n + 1))
    rw [Fin.val_last] at ha hb
    calc |cosineModeTangent δ₁ (n + 1) i (Fin.last (n + 1))| *
          |cosineModeTangent δ₂ (n + 1) i (Fin.last (n + 1))|
        ≤ (2 * entryBound δ₁ i (n + 1)) * (2 * entryBound δ₂ i (n + 1)) :=
          mul_le_mul ha hb (abs_nonneg _) (by have := entryBound_nonneg δ₁ i (n + 1); positivity)
      _ = 4 * (entryBound δ₁ i (n + 1) * entryBound δ₂ i (n + 1)) := by ring
  have hE : ∀ i : Fin (n + 2), 0 ≤ entryBound δ₁ i (n + 1) * entryBound δ₂ i (n + 1) := fun i =>
    mul_nonneg (entryBound_nonneg _ _ _) (entryBound_nonneg _ _ _)
  rw [Fin.sum_univ_castSucc (n := n + 1)]
  have hsum : |2 * ∑ i : Fin (n + 1), cosineModeTangent δ₁ (n + 1) (Fin.castSucc i) (Fin.last (n + 1)) *
      cosineModeTangent δ₂ (n + 1) (Fin.castSucc i) (Fin.last (n + 1))| ≤
      8 * ∑ i : Fin (n + 1), entryBound δ₁ (Fin.castSucc i) (n + 1) * entryBound δ₂ (Fin.castSucc i) (n + 1) := by
    rw [abs_mul, abs_two, Finset.mul_sum]
    have := Finset.abs_sum_le_sum_abs (fun i : Fin (n + 1) =>
      cosineModeTangent δ₁ (n + 1) (Fin.castSucc i) (Fin.last (n + 1)) *
        cosineModeTangent δ₂ (n + 1) (Fin.castSucc i) (Fin.last (n + 1))) Finset.univ
    calc 2 * |∑ i : Fin (n + 1), cosineModeTangent δ₁ (n + 1) (Fin.castSucc i) (Fin.last (n + 1)) *
          cosineModeTangent δ₂ (n + 1) (Fin.castSucc i) (Fin.last (n + 1))|
        ≤ 2 * ∑ i : Fin (n + 1), |cosineModeTangent δ₁ (n + 1) (Fin.castSucc i) (Fin.last (n + 1)) *
          cosineModeTangent δ₂ (n + 1) (Fin.castSucc i) (Fin.last (n + 1))| :=
          mul_le_mul_of_nonneg_left this (by norm_num)
      _ ≤ 2 * ∑ i : Fin (n + 1), 4 * (entryBound δ₁ (Fin.castSucc i) (n + 1) * entryBound δ₂ (Fin.castSucc i) (n + 1)) := by
          gcongr with i
          exact hterm (Fin.castSucc i)
      _ = ∑ i : Fin (n + 1), 8 * (entryBound δ₁ (Fin.castSucc i) (n + 1) * entryBound δ₂ (Fin.castSucc i) (n + 1)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  have hlast := hterm (Fin.last (n + 1))
  rw [Fin.val_last] at hlast
  calc |2 * ∑ i : Fin (n + 1), cosineModeTangent δ₁ (n + 1) (Fin.castSucc i) (Fin.last (n + 1)) *
        cosineModeTangent δ₂ (n + 1) (Fin.castSucc i) (Fin.last (n + 1)) +
        cosineModeTangent δ₁ (n + 1) (Fin.last (n + 1)) (Fin.last (n + 1)) *
          cosineModeTangent δ₂ (n + 1) (Fin.last (n + 1)) (Fin.last (n + 1))|
      ≤ |2 * ∑ i : Fin (n + 1), cosineModeTangent δ₁ (n + 1) (Fin.castSucc i) (Fin.last (n + 1)) *
        cosineModeTangent δ₂ (n + 1) (Fin.castSucc i) (Fin.last (n + 1))| +
        |cosineModeTangent δ₁ (n + 1) (Fin.last (n + 1)) (Fin.last (n + 1)) *
          cosineModeTangent δ₂ (n + 1) (Fin.last (n + 1)) (Fin.last (n + 1))| := abs_add_le _ _
    _ ≤ 8 * ∑ i : Fin (n + 1), entryBound δ₁ (Fin.castSucc i) (n + 1) * entryBound δ₂ (Fin.castSucc i) (n + 1) +
        4 * (entryBound δ₁ (n + 1) (n + 1) * entryBound δ₂ (n + 1) (n + 1)) := add_le_add hsum hlast
    _ ≤ 8 * (∑ i : Fin (n + 1), entryBound δ₁ (Fin.castSucc i) (n + 1) * entryBound δ₂ (Fin.castSucc i) (n + 1) +
        entryBound δ₁ (Fin.last (n + 1)) (n + 1) * entryBound δ₂ (Fin.last (n + 1)) (n + 1)) := by
        rw [Fin.val_last]
        have := hE (Fin.last (n + 1))
        rw [Fin.val_last] at this
        nlinarith

/-! ## The two-prime cross term at the squared-radius level -/

theorem prevJet_add (J K : ℕ → ℝ) (n : ℕ) :
    prevJet (fun m => J m + K m) n = prevJet J n + prevJet K n := by
  cases n <;> simp [prevJet]

theorem prevJet_sub (J K : ℕ → ℝ) (n : ℕ) :
    prevJet (fun m => J m - K m) n = prevJet J n - prevJet K n := by
  cases n <;> simp [prevJet]

theorem bilinearDeterminantJet_eq (δ₁ δ₂ : ℝ) :
    bilinearDeterminantJet δ₁ δ₂ = fun m => (cosineModeDeterminantJet (δ₁ + δ₂) m +
      cosineModeDeterminantJet (δ₁ - δ₂) m) - truncationDefect δ₁ δ₂ m := rfl

/-- Decomposition of the bilinear squared-radius jet minus the beat-mode jet. -/
theorem bilinearSquaredRadiusJet_sub_beat_eq (δ₁ δ₂ : ℝ) (m : ℕ) :
    bilinearSquaredRadiusJet δ₁ δ₂ (m + 1) -
        squaredRadiusJetOf (cosineModeDeterminantJet (δ₁ - δ₂)) (m + 1) =
      squaredRadiusJetOf (cosineModeDeterminantJet (δ₁ + δ₂)) (m + 1) -
        archimedeanSquaredRadius (m + 1) *
          ((truncationDefect δ₁ δ₂ (m + 2) - truncationDefect δ₁ δ₂ (m + 1)) -
            (truncationDefect δ₁ δ₂ (m + 1) - truncationDefect δ₁ δ₂ m)) +
        squaredRadiusJetOf (cosineModeDeterminantJet δ₁) (m + 1) *
          squaredRadiusJetOf (cosineModeDeterminantJet δ₂) (m + 1) / archimedeanSquaredRadius (m + 1) := by
  unfold bilinearSquaredRadiusJet
  rw [bilinearDeterminantJet_eq]
  unfold squaredRadiusJetOf
  simp only [prevJet]
  ring

theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  exact (abs_add_le a (-b)).trans (by rw [abs_neg])

/-- **The two-prime cross term is the beat-mode radius jet up to an explicit error.**  For
`δ₁, δ₂ > 0` and every degree `m + 1`,

`|∂₁∂₂ a² − [beat-mode jet]| ≤ r² · (2(E₊(m+2) + E₊(m+1)) + 8 Σ E₁E₂(·, m+2) + 8 Σ E₁E₂(·, m+1)
    + 4 (E₁(m+2) + E₁(m+1)) (E₂(m+2) + E₂(m+1)))`,

every `E` carrying the factor `(cosh δ)^{-1/2}`. -/
theorem abs_bilinearSquaredRadiusJet_sub_beat_le {δ₁ δ₂ : ℝ} (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (m : ℕ) :
    |bilinearSquaredRadiusJet δ₁ δ₂ (m + 1) -
        squaredRadiusJetOf (cosineModeDeterminantJet (δ₁ - δ₂)) (m + 1)| ≤
      archimedeanSquaredRadius (m + 1) *
        (2 * (entryBound (δ₁ + δ₂) (m + 2) (m + 2) + entryBound (δ₁ + δ₂) (m + 1) (m + 1)) +
          8 * ∑ i : Fin (m + 3), entryBound δ₁ i (m + 2) * entryBound δ₂ i (m + 2) +
          8 * ∑ i : Fin (m + 2), entryBound δ₁ i (m + 1) * entryBound δ₂ i (m + 1) +
          4 * (entryBound δ₁ (m + 2) (m + 2) + entryBound δ₁ (m + 1) (m + 1)) *
            (entryBound δ₂ (m + 2) (m + 2) + entryBound δ₂ (m + 1) (m + 1))) := by
  have hr := archimedeanSquaredRadius_pos (m + 1)
  have hsum : 0 < δ₁ + δ₂ := by linarith
  set r2 := archimedeanSquaredRadius (m + 1) with hr2
  rw [bilinearSquaredRadiusJet_sub_beat_eq]
  -- the three pieces
  have hA : |squaredRadiusJetOf (cosineModeDeterminantJet (δ₁ + δ₂)) (m + 1)| ≤
      r2 * (2 * (entryBound (δ₁ + δ₂) (m + 2) (m + 2) + entryBound (δ₁ + δ₂) (m + 1) (m + 1))) := by
    rw [squaredRadiusJetOf_cosineMode, abs_mul, abs_of_pos hr, abs_mul, abs_two]
    have h1 := abs_cosineDiagonalMoment_le hsum (m + 2)
    have h2 := abs_cosineDiagonalMoment_le hsum (m + 1)
    have h3 := abs_sub_le_abs_add_abs (cosineDiagonalMoment (δ₁ + δ₂) (m + 1 + 1))
      (cosineDiagonalMoment (δ₁ + δ₂) (m + 1))
    have hm : (m + 1 + 1) = m + 2 := rfl
    rw [hm] at h3
    apply mul_le_mul_of_nonneg_left _ hr.le
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [hm]
    linarith
  have hB : |r2 * ((truncationDefect δ₁ δ₂ (m + 2) - truncationDefect δ₁ δ₂ (m + 1)) -
      (truncationDefect δ₁ δ₂ (m + 1) - truncationDefect δ₁ δ₂ m))| ≤
      r2 * (8 * ∑ i : Fin (m + 3), entryBound δ₁ i (m + 2) * entryBound δ₂ i (m + 2) +
        8 * ∑ i : Fin (m + 2), entryBound δ₁ i (m + 1) * entryBound δ₂ i (m + 1)) := by
    rw [abs_mul, abs_of_pos hr]
    apply mul_le_mul_of_nonneg_left _ hr.le
    have i1 : |truncationDefect δ₁ δ₂ (m + 2) - truncationDefect δ₁ δ₂ (m + 1)| ≤
        8 * ∑ i : Fin (m + 3), entryBound δ₁ i (m + 2) * entryBound δ₂ i (m + 2) :=
      abs_truncationDefect_succ_sub_le h₁ h₂ (m + 1)
    have i0 := abs_truncationDefect_succ_sub_le h₁ h₂ m
    have h3 := abs_sub_le_abs_add_abs (truncationDefect δ₁ δ₂ (m + 2) - truncationDefect δ₁ δ₂ (m + 1))
      (truncationDefect δ₁ δ₂ (m + 1) - truncationDefect δ₁ δ₂ m)
    linarith
  have hC : |squaredRadiusJetOf (cosineModeDeterminantJet δ₁) (m + 1) *
      squaredRadiusJetOf (cosineModeDeterminantJet δ₂) (m + 1) / r2| ≤
      r2 * (4 * (entryBound δ₁ (m + 2) (m + 2) + entryBound δ₁ (m + 1) (m + 1)) *
        (entryBound δ₂ (m + 2) (m + 2) + entryBound δ₂ (m + 1) (m + 1))) := by
    rw [squaredRadiusJetOf_cosineMode, squaredRadiusJetOf_cosineMode]
    have hm : (m + 1 + 1) = m + 2 := rfl
    rw [hm]
    have e1 := abs_cosineDiagonalMoment_le h₁ (m + 2)
    have e2 := abs_cosineDiagonalMoment_le h₁ (m + 1)
    have e3 := abs_cosineDiagonalMoment_le h₂ (m + 2)
    have e4 := abs_cosineDiagonalMoment_le h₂ (m + 1)
    have d1 := abs_sub_le_abs_add_abs (cosineDiagonalMoment δ₁ (m + 2)) (cosineDiagonalMoment δ₁ (m + 1))
    have d2 := abs_sub_le_abs_add_abs (cosineDiagonalMoment δ₂ (m + 2)) (cosineDiagonalMoment δ₂ (m + 1))
    have hid : archimedeanSquaredRadius (m + 1) * (2 * (cosineDiagonalMoment δ₁ (m + 2) - cosineDiagonalMoment δ₁ (m + 1))) *
        (archimedeanSquaredRadius (m + 1) * (2 * (cosineDiagonalMoment δ₂ (m + 2) - cosineDiagonalMoment δ₂ (m + 1)))) / r2 =
        r2 * (4 * ((cosineDiagonalMoment δ₁ (m + 2) - cosineDiagonalMoment δ₁ (m + 1)) *
          (cosineDiagonalMoment δ₂ (m + 2) - cosineDiagonalMoment δ₂ (m + 1)))) := by
      rw [hr2]
      field_simp
      ring
    rw [hid, abs_mul, abs_of_pos hr, abs_mul, abs_mul]
    rw [show |(4 : ℝ)| = 4 by norm_num]
    apply mul_le_mul_of_nonneg_left _ hr.le
    have hn1 : 0 ≤ entryBound δ₁ (m + 2) (m + 2) + entryBound δ₁ (m + 1) (m + 1) :=
      add_nonneg (entryBound_nonneg _ _ _) (entryBound_nonneg _ _ _)
    have hn2 : 0 ≤ entryBound δ₂ (m + 2) (m + 2) + entryBound δ₂ (m + 1) (m + 1) :=
      add_nonneg (entryBound_nonneg _ _ _) (entryBound_nonneg _ _ _)
    have hb1 : |cosineDiagonalMoment δ₁ (m + 2) - cosineDiagonalMoment δ₁ (m + 1)| ≤
        entryBound δ₁ (m + 2) (m + 2) + entryBound δ₁ (m + 1) (m + 1) := by linarith
    have hb2 : |cosineDiagonalMoment δ₂ (m + 2) - cosineDiagonalMoment δ₂ (m + 1)| ≤
        entryBound δ₂ (m + 2) (m + 2) + entryBound δ₂ (m + 1) (m + 1) := by linarith
    calc 4 * (|cosineDiagonalMoment δ₁ (m + 2) - cosineDiagonalMoment δ₁ (m + 1)| *
          |cosineDiagonalMoment δ₂ (m + 2) - cosineDiagonalMoment δ₂ (m + 1)|)
        ≤ 4 * ((entryBound δ₁ (m + 2) (m + 2) + entryBound δ₁ (m + 1) (m + 1)) *
          (entryBound δ₂ (m + 2) (m + 2) + entryBound δ₂ (m + 1) (m + 1))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hb1 hb2 (abs_nonneg _) hn1
      _ = _ := by ring
  have htri : |squaredRadiusJetOf (cosineModeDeterminantJet (δ₁ + δ₂)) (m + 1) -
      r2 * ((truncationDefect δ₁ δ₂ (m + 2) - truncationDefect δ₁ δ₂ (m + 1)) -
        (truncationDefect δ₁ δ₂ (m + 1) - truncationDefect δ₁ δ₂ m)) +
      squaredRadiusJetOf (cosineModeDeterminantJet δ₁) (m + 1) *
        squaredRadiusJetOf (cosineModeDeterminantJet δ₂) (m + 1) / r2| ≤
      |squaredRadiusJetOf (cosineModeDeterminantJet (δ₁ + δ₂)) (m + 1)| +
      |r2 * ((truncationDefect δ₁ δ₂ (m + 2) - truncationDefect δ₁ δ₂ (m + 1)) -
        (truncationDefect δ₁ δ₂ (m + 1) - truncationDefect δ₁ δ₂ m))| +
      |squaredRadiusJetOf (cosineModeDeterminantJet δ₁) (m + 1) *
        squaredRadiusJetOf (cosineModeDeterminantJet δ₂) (m + 1) / r2| := by
    have := abs_add_le (squaredRadiusJetOf (cosineModeDeterminantJet (δ₁ + δ₂)) (m + 1) -
      r2 * ((truncationDefect δ₁ δ₂ (m + 2) - truncationDefect δ₁ δ₂ (m + 1)) -
        (truncationDefect δ₁ δ₂ (m + 1) - truncationDefect δ₁ δ₂ m)))
      (squaredRadiusJetOf (cosineModeDeterminantJet δ₁) (m + 1) *
        squaredRadiusJetOf (cosineModeDeterminantJet δ₂) (m + 1) / r2)
    have := abs_sub_le_abs_add_abs (squaredRadiusJetOf (cosineModeDeterminantJet (δ₁ + δ₂)) (m + 1))
      (r2 * ((truncationDefect δ₁ δ₂ (m + 2) - truncationDefect δ₁ δ₂ (m + 1)) -
        (truncationDefect δ₁ δ₂ (m + 1) - truncationDefect δ₁ δ₂ m)))
    linarith
  calc _ ≤ _ := htri
    _ ≤ _ := add_le_add (add_le_add hA hB) hC
    _ = _ := by ring

end CosineModeResponse
end RHTower
