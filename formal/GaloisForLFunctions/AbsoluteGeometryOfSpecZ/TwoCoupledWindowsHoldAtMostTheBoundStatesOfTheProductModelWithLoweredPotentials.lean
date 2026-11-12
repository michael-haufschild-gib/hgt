import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TwoWindowsCoupledThroughTheirChargesHoldOneBoundStateIffTheirSusceptibilitiesMultiplyToAtLeastOne
import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex
import GaloisForLFunctions.HTGeometry.ExponentialKernelAlternatingInertia
import GaloisForLFunctions.HTGeometry.HaynsworthInertia

/-!
# Two coupled windows hold at most the bound states of the product model with lowered potentials

Two real symmetric forms `A`, `B` coupled by a matrix `K` give the form
`A(x) + B(y) − 2 Σ K_ij x_i y_j` (`coupled`). The neutral part of the union of two adjacent
windows is of this shape, with `K` the couplings between the blocks of the two windows
(`neutralWindow_add_submatrix`).

Let `u`, `v` be charges with `u_i v_j ≤ K_ij`, and `F = K − u ⊗ v ≥ 0` the excess of the
couplings over the product of the charges. Since

  `−2 Σ F_ij x_i y_j = Σ F_ij (x_i − y_j)² − Σ_i (F 1)_i x_i² − Σ_j (Fᵀ 1)_j y_j²`,

the coupled form is at least the form glued through the product of the charges, of the two
forms with potentials lowered by the excess (`bilin_glued_le_coupled`). Hence:

* the coupled form has at most as many negative squares as that product model
  (`hermNegIndex_coupled_le_glued`); if the lowered forms satisfy the hypotheses of the gluing
  lemma with `αβ ≥ 1`, the coupled form has at most one (`hermNegIndex_coupled_le_one`);
* with `u = v = 0`: two forms coupled by `K ≥ 0` have together at most the negative squares of
  the two forms with potentials lowered by their couplings (`hermNegIndex_coupled_le_add`).

For two adjacent windows these are `hermNegIndex_neutralWindow_add_le_glued` and
`hermNegIndex_neutralWindow_add_le_add`.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Lowering a potential -/

section Diagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Subtracting a diagonal matrix lowers the potential of the form. -/
theorem bilin_sub_diagonal (A : Matrix ι ι ℝ) (d x : ι → ℝ) :
    bilin (A - diagonal d) x x = bilin A x x - ∑ i, d i * x i ^ 2 := by
  simp only [bilin, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
    ring
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hji), mul_zero]
  · exact fun h => absurd (Finset.mem_univ i) h

omit [Fintype ι] in
theorem sub_diagonal_symm {A : Matrix ι ι ℝ} (hA : ∀ i j, A i j = A j i) (d : ι → ℝ) (i j : ι) :
    (A - diagonal d) i j = (A - diagonal d) j i := by
  rw [Matrix.sub_apply, Matrix.sub_apply, hA i j]
  by_cases h : i = j
  · rw [h]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

end Diagonal

/-! ### Two forms coupled by a matrix -/

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- Two forms coupled by a matrix: `A(x) + B(y) − 2 Σ K_ij x_i y_j`. -/
def coupled (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ) (K : ι₁ → ι₂ → ℝ) :
    Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ :=
  Matrix.of (Sum.elim (fun i => Sum.elim (A i) fun j => -K i j)
    fun j => Sum.elim (fun i => -K i j) (B j))

theorem bilin_coupled (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ) (K : ι₁ → ι₂ → ℝ)
    (w : ι₁ ⊕ ι₂ → ℝ) :
    bilin (coupled A B K) w w =
      bilin A (fun i => w (Sum.inl i)) (fun i => w (Sum.inl i)) +
        bilin B (fun j => w (Sum.inr j)) (fun j => w (Sum.inr j)) -
        2 * ∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * K i j := by
  have hcross : ∑ j, ∑ i, w (Sum.inr j) * w (Sum.inl i) * K i j =
      ∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * K i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [bilin, coupled, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    mul_neg, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [hcross]
  ring

/-- The excess of the couplings of a block of the first form over the product of the
charges. -/
def excessLeft (K : ι₁ → ι₂ → ℝ) (u : ι₁ → ℝ) (v : ι₂ → ℝ) (i : ι₁) : ℝ :=
  ∑ j, (K i j - u i * v j)

/-- The excess of the couplings of a block of the second form over the product of the
charges. -/
def excessRight (K : ι₁ → ι₂ → ℝ) (u : ι₁ → ℝ) (v : ι₂ → ℝ) (j : ι₂) : ℝ :=
  ∑ i, (K i j - u i * v j)

variable [DecidableEq ι₁] [DecidableEq ι₂]

/-- **The coupled form is at least the product model with lowered potentials**, when the
couplings are at least the product of the charges. -/
theorem bilin_glued_le_coupled (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ) (K : ι₁ → ι₂ → ℝ)
    (u : ι₁ → ℝ) (v : ι₂ → ℝ) (hK : ∀ i j, u i * v j ≤ K i j) (w : ι₁ ⊕ ι₂ → ℝ) :
    bilin (glued (A - diagonal (excessLeft K u v)) (B - diagonal (excessRight K u v)) u v) w w ≤
      bilin (coupled A B K) w w := by
  -- the excess couplings, as a sum of squares
  have hsq : 0 ≤ ∑ i, ∑ j, (K i j - u i * v j) * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hK i j)) (sq_nonneg _)
  have hterm : ∀ i j, (K i j - u i * v j) * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 =
      (K i j - u i * v j) * w (Sum.inl i) ^ 2 + (K i j - u i * v j) * w (Sum.inr j) ^ 2 -
        2 * (w (Sum.inl i) * w (Sum.inr j) * K i j) +
          2 * (w (Sum.inl i) * w (Sum.inr j) * (u i * v j)) := fun i j => by ring
  have hexp : ∑ i, ∑ j, (K i j - u i * v j) * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 =
      (∑ i, ∑ j, (K i j - u i * v j) * w (Sum.inl i) ^ 2) +
        (∑ i, ∑ j, (K i j - u i * v j) * w (Sum.inr j) ^ 2) -
        2 * (∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * K i j) +
          2 * (∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * (u i * v j)) := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ i, excessLeft K u v i * w (Sum.inl i) ^ 2 =
      ∑ i, ∑ j, (K i j - u i * v j) * w (Sum.inl i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [excessLeft, Finset.sum_mul]
  have h2 : ∑ j, excessRight K u v j * w (Sum.inr j) ^ 2 =
      ∑ i, ∑ j, (K i j - u i * v j) * w (Sum.inr j) ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [excessRight, Finset.sum_mul]
  have h3 : chargeOf u (fun i => w (Sum.inl i)) * chargeOf v (fun j => w (Sum.inr j)) =
      ∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * (u i * v j) := by
    rw [chargeOf, chargeOf, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [bilin_glued, bilin_coupled, bilin_sub_diagonal, bilin_sub_diagonal, h1, h2, h3]
  linarith

/-- **The coupled form has at most the negative squares of the product model with lowered
potentials.** -/
theorem hermNegIndex_coupled_le_glued (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (K : ι₁ → ι₂ → ℝ) (u : ι₁ → ℝ) (v : ι₂ → ℝ) (hK : ∀ i j, u i * v j ≤ K i j) :
    hermNegIndex ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) ≤
      hermNegIndex ((glued (A - diagonal (excessLeft K u v))
        (B - diagonal (excessRight K u v)) u v).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) :=
  HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_le _ _ fun c => by
    rw [hermQuad_map_eq_bilin, hermQuad_map_eq_bilin]
    exact add_le_add (bilin_glued_le_coupled A B K u v hK _)
      (bilin_glued_le_coupled A B K u v hK _)

/-- **Gluing with couplings above the product of the charges.** If the two forms with
potentials lowered by the excess couplings satisfy the hypotheses of the gluing lemma, with
`αβ ≥ 1`, the coupled form has at most one negative square. -/
theorem hermNegIndex_coupled_le_one {A : Matrix ι₁ ι₁ ℝ} {B : Matrix ι₂ ι₂ ℝ}
    {K : ι₁ → ι₂ → ℝ} {u a : ι₁ → ℝ} {v b : ι₂ → ℝ} (hA : ∀ i j, A i j = A j i)
    (hB : ∀ i j, B i j = B j i) (hK : ∀ i j, u i * v j ≤ K i j)
    (hAa : ∀ i, ∑ j, (A - diagonal (excessLeft K u v)) i j * a j = u i)
    (hBb : ∀ i, ∑ j, (B - diagonal (excessRight K u v)) i j * b j = v i)
    (hApos : ∀ x, chargeOf u x = 0 → 0 ≤ bilin (A - diagonal (excessLeft K u v)) x x)
    (hBpos : ∀ y, chargeOf v y = 0 → 0 ≤ bilin (B - diagonal (excessRight K u v)) y y)
    (hβ : chargeOf v b < 0) (hαβ : 1 ≤ chargeOf u a * chargeOf v b) :
    hermNegIndex ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) ≤ 1 := by
  have h := hermNegIndex_coupled_le_glued A B K u v hK
  rwa [hermNegIndex_glued_eq_one (sub_diagonal_symm hA _) (sub_diagonal_symm hB _) hAa hBb hApos
    hBpos hβ hαβ] at h

/-- **Two forms coupled by nonnegative couplings have together at most the negative squares of
the two forms with potentials lowered by their couplings.** -/
theorem hermNegIndex_coupled_le_add {A : Matrix ι₁ ι₁ ℝ} {B : Matrix ι₂ ι₂ ℝ}
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i) (K : ι₁ → ι₂ → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) :
    hermNegIndex ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) ≤
      hermNegIndex ((A - diagonal fun i => ∑ j, K i j).map (↑) : Matrix ι₁ ι₁ ℂ) +
        hermNegIndex ((B - diagonal fun j => ∑ i, K i j).map (↑) : Matrix ι₂ ι₂ ℂ) := by
  have h := hermNegIndex_coupled_le_glued A B K (fun _ => 0) (fun _ => 0) fun i j => by
    rw [zero_mul]
    exact hK i j
  have eL : excessLeft K (fun _ => 0) (fun _ => 0) = fun i => ∑ j, K i j :=
    funext fun i => Finset.sum_congr rfl fun j _ => by rw [zero_mul, sub_zero]
  have eR : excessRight K (fun _ => 0) (fun _ => 0) = fun j => ∑ i, K i j :=
    funext fun j => Finset.sum_congr rfl fun i _ => by rw [zero_mul, sub_zero]
  rw [eL, eR] at h
  -- without charges the product model is the direct sum
  have hblocks : ((glued (A - diagonal fun i => ∑ j, K i j) (B - diagonal fun j => ∑ i, K i j)
      (fun _ => 0) (fun _ => 0)).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) =
        fromBlocks ((A - diagonal fun i => ∑ j, K i j).map (↑)) 0 0
          ((B - diagonal fun j => ∑ i, K i j).map (↑)) := by
    ext (i | i) (j | j) <;> simp [glued]
  rw [hblocks, negIndex_fromBlocks_zero (isHermitian_map_ofReal (sub_diagonal_symm hA _))
    (isHermitian_map_ofReal (sub_diagonal_symm hB _))] at h
  exact h

/-! ### Two adjacent windows -/

/-- **The neutral part of the union of two adjacent windows is the two neutral parts coupled by
the weights between their blocks.** -/
theorem neutralWindow_add_submatrix (Q R J₁ J₂ : ℕ) :
    (neutralWindow Q R (J₁ + J₂)).submatrix finSumFinEquiv finSumFinEquiv =
      coupled (neutralWindow Q R J₁) (neutralWindow Q (R + J₁) J₂)
        fun (i : Fin J₁) (j : Fin J₂) => blockWeight Q (R + i) (R + J₁ + j) := by
  ext (i | i) (j | j)
  · rfl
  · show neutralBlock Q (R + (i : ℕ)) (R + (J₁ + (j : ℕ))) = -blockWeight Q (R + i) (R + J₁ + j)
    rw [blockWeight, neg_neg, add_assoc]
  · show neutralBlock Q (R + (J₁ + (i : ℕ))) (R + (j : ℕ)) = -blockWeight Q (R + j) (R + J₁ + i)
    rw [blockWeight, neg_neg, neutralBlock_comm, add_assoc]
  · show neutralBlock Q (R + (J₁ + (i : ℕ))) (R + (J₁ + (j : ℕ))) =
      neutralBlock Q (R + J₁ + i) (R + J₁ + j)
    rw [add_assoc, add_assoc]

theorem hermNegIndex_neutralWindow_add (Q R J₁ J₂ : ℕ) :
    hermNegIndex ((neutralWindow Q R (J₁ + J₂)).map (↑) : Matrix (Fin (J₁ + J₂)) _ ℂ) =
      hermNegIndex ((coupled (neutralWindow Q R J₁) (neutralWindow Q (R + J₁) J₂)
        fun (i : Fin J₁) (j : Fin J₂) => blockWeight Q (R + i) (R + J₁ + j)).map (↑) :
          Matrix (Fin J₁ ⊕ Fin J₂) (Fin J₁ ⊕ Fin J₂) ℂ) := by
  rw [← neutralWindow_add_submatrix, ← hermNegIndex_submatrix_equiv
    ((neutralWindow Q R (J₁ + J₂)).map (↑) : Matrix (Fin (J₁ + J₂)) _ ℂ) finSumFinEquiv]
  rfl

/-- **The gluing of two adjacent windows.** For charges with `u_i v_j` at most the coupling of
the blocks `R + i` and `R + J₁ + j`, the union holds at most the bound states of the two
windows, with potentials lowered by the excess couplings, glued through the product of the
charges. -/
theorem hermNegIndex_neutralWindow_add_le_glued (Q R J₁ J₂ : ℕ) (u : Fin J₁ → ℝ)
    (v : Fin J₂ → ℝ) (huv : ∀ i j, u i * v j ≤ blockWeight Q (R + i) (R + J₁ + j)) :
    hermNegIndex ((neutralWindow Q R (J₁ + J₂)).map (↑) : Matrix (Fin (J₁ + J₂)) _ ℂ) ≤
      hermNegIndex ((glued
        (neutralWindow Q R J₁ -
          diagonal (excessLeft
            (fun (i : Fin J₁) (j : Fin J₂) => blockWeight Q (R + i) (R + J₁ + j)) u v))
        (neutralWindow Q (R + J₁) J₂ -
          diagonal (excessRight
            (fun (i : Fin J₁) (j : Fin J₂) => blockWeight Q (R + i) (R + J₁ + j)) u v))
        u v).map (↑) : Matrix (Fin J₁ ⊕ Fin J₂) (Fin J₁ ⊕ Fin J₂) ℂ) := by
  rw [hermNegIndex_neutralWindow_add]
  exact hermNegIndex_coupled_le_glued _ _ _ u v huv

/-- **Two adjacent windows hold together at most the bound states of the two windows with
potentials lowered by their couplings to each other.** -/
theorem hermNegIndex_neutralWindow_add_le_add (Q R J₁ J₂ : ℕ) :
    hermNegIndex ((neutralWindow Q R (J₁ + J₂)).map (↑) : Matrix (Fin (J₁ + J₂)) _ ℂ) ≤
      hermNegIndex ((neutralWindow Q R J₁ -
        diagonal fun i : Fin J₁ => ∑ j : Fin J₂, blockWeight Q (R + i) (R + J₁ + j)).map (↑) :
          Matrix (Fin J₁) (Fin J₁) ℂ) +
        hermNegIndex ((neutralWindow Q (R + J₁) J₂ -
          diagonal fun j : Fin J₂ => ∑ i : Fin J₁, blockWeight Q (R + i) (R + J₁ + j)).map (↑) :
            Matrix (Fin J₂) (Fin J₂) ℂ) := by
  rw [hermNegIndex_neutralWindow_add]
  exact hermNegIndex_coupled_le_add (fun i j => neutralBlock_comm Q _ _)
    (fun i j => neutralBlock_comm Q _ _) _ fun i j =>
      (blockWeight_pos (by have := i.2; omega) Q).le

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
