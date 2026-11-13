import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TwoCoupledWindowsHoldAtMostTheBoundStatesOfTheProductModelWithLoweredPotentials

/-!
# Two coupled windows are bracketed by lowered and raised potentials and glued through response matrices

For symmetric forms `A`, `B` coupled by `K` (`coupled A B K`) and charges `u`, `v` with
`u_i v_j ≤ K_ij`, the excess `F_ij = K_ij − u_i v_j ≥ 0` satisfies both
`−2 F_ij x_i y_j ≥ −F_ij (x_i² + y_j²)` and `−2 F_ij x_i y_j ≤ F_ij (x_i² + y_j²)`.
Lowering the potentials by the row and column sums of `F` bounds the negative index from above
(`hermNegIndex_coupled_le_glued`), and raising the potentials by the same excess bounds the
negative index from below (`hermNegIndex_glued_le_coupled`).

* **Sign elimination and exact single-block maximum.** When `A` and `B` each take a negative value,
  nonnegativity on `ker u` and `ker v` together with `1 ≤ (u·a)(v·b)` automatically forces both
  susceptibilities to be negative (`hermNegIndex_glued_eq_one_of_exists_neg`). When the first
  window is a single block (`Fin 1`) with `A_00 < 0` and `B b₀ = K_0` has `b₀ ≤ 0` and
  `1 ≤ A_00⁻¹ (K_0 · b₀)`, the zero-excess choice `(1, K_0)` achieves the global maximum of
  `(u·a)(v·b)` over all admissible charge pairs (`susceptibility_mul_le_of_fin_one`).
* **Multi-charge response matrices.** Replacing rank-one charges by `r`-tuples of charges
  `U : Matrix ι₁ ρ ℝ`, `V : Matrix ι₂ ρ ℝ` (`gluedMatrix`) gives two-sided potential brackets at
  rank `r` (`hermNegIndex_coupled_le_gluedMatrix`, `hermNegIndex_gluedMatrix_le_coupled`) and, by
  Haynsworth inertia additivity, the response-matrix gluing law (`hermNegIndex_gluedMatrix_response`):
  for `𝒜 = Uᵀ A⁻¹ U` and `ℬ = Vᵀ B⁻¹ V`,
  `hermNegIndex (gluedMatrix A B U V) + hermNegIndex 𝒜 = hermNegIndex A + hermNegIndex B + hermNegIndex (𝒜⁻¹ − ℬ)`.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open Finset Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Raising a potential and the lowered difference decomposition -/

section Potential

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Adding a diagonal matrix raises the potential of the form. -/
theorem bilin_add_diagonal (A : Matrix ι ι ℝ) (d x : ι → ℝ) :
    bilin (A + diagonal d) x x = bilin A x x + ∑ i, d i * x i ^ 2 := by
  simp only [bilin, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
    ring
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hji), mul_zero]
  · exact fun h => absurd (Finset.mem_univ i) h

omit [Fintype ι] in
theorem add_diagonal_symm {A : Matrix ι ι ℝ} (hA : ∀ i j, A i j = A j i) (d : ι → ℝ) (i j : ι) :
    (A + diagonal d) i j = (A + diagonal d) j i := by
  rw [Matrix.add_apply, Matrix.add_apply, hA i j]
  by_cases h : i = j
  · rw [h]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

end Potential

/-! ### Raised-potential comparison and lowered square identity -/

section RankOneBracket

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- **The coupled form is at most the product model with raised potentials**, when the couplings
are at least the product of the charges. -/
theorem bilin_coupled_le_glued_raised (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ) (K : ι₁ → ι₂ → ℝ)
    (u : ι₁ → ℝ) (v : ι₂ → ℝ) (hK : ∀ i j, u i * v j ≤ K i j) (w : ι₁ ⊕ ι₂ → ℝ) :
    bilin (coupled A B K) w w ≤
      bilin (glued (A + diagonal (excessLeft K u v)) (B + diagonal (excessRight K u v)) u v) w w := by
  have hsq : 0 ≤ ∑ i, ∑ j, (K i j - u i * v j) * (w (Sum.inl i) + w (Sum.inr j)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hK i j)) (sq_nonneg _)
  have hterm : ∀ i j, (K i j - u i * v j) * (w (Sum.inl i) + w (Sum.inr j)) ^ 2 =
      (K i j - u i * v j) * w (Sum.inl i) ^ 2 + (K i j - u i * v j) * w (Sum.inr j) ^ 2 +
        2 * (w (Sum.inl i) * w (Sum.inr j) * K i j) -
          2 * (w (Sum.inl i) * w (Sum.inr j) * (u i * v j)) := fun i j => by ring
  have hexp : ∑ i, ∑ j, (K i j - u i * v j) * (w (Sum.inl i) + w (Sum.inr j)) ^ 2 =
      (∑ i, ∑ j, (K i j - u i * v j) * w (Sum.inl i) ^ 2) +
        (∑ i, ∑ j, (K i j - u i * v j) * w (Sum.inr j) ^ 2) +
        2 * (∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * K i j) -
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
  rw [bilin_glued, bilin_coupled, bilin_add_diagonal, bilin_add_diagonal, h1, h2, h3]
  linarith

/-- **The coupled form has at least the negative squares of the product model with raised
potentials.** -/
theorem hermNegIndex_glued_le_coupled (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (K : ι₁ → ι₂ → ℝ) (u : ι₁ → ℝ) (v : ι₂ → ℝ) (hK : ∀ i j, u i * v j ≤ K i j) :
    hermNegIndex ((glued (A + diagonal (excessLeft K u v))
        (B + diagonal (excessRight K u v)) u v).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) ≤
      hermNegIndex ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) :=
  HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_le _ _ fun c => by
    rw [hermQuad_map_eq_bilin, hermQuad_map_eq_bilin]
    exact add_le_add (bilin_coupled_le_glued_raised A B K u v hK _)
      (bilin_coupled_le_glued_raised A B K u v hK _)

/-- **Two bound states from the raised model.** If the forms with potentials raised by the excess
couplings satisfy the hypotheses of the gluing lemma with `α < 0`, `β < 0`, and `αβ < 1`, the
coupled form has at least two negative squares. -/
theorem two_le_hermNegIndex_coupled_of_raised {A : Matrix ι₁ ι₁ ℝ} {B : Matrix ι₂ ι₂ ℝ}
    {K : ι₁ → ι₂ → ℝ} {u a : ι₁ → ℝ} {v b : ι₂ → ℝ} (hK : ∀ i j, u i * v j ≤ K i j)
    (hAa : ∀ i, ∑ j, (A + diagonal (excessLeft K u v)) i j * a j = u i)
    (hBb : ∀ i, ∑ j, (B + diagonal (excessRight K u v)) i j * b j = v i)
    (hApos : ∀ x, chargeOf u x = 0 → 0 ≤ bilin (A + diagonal (excessLeft K u v)) x x)
    (hBpos : ∀ y, chargeOf v y = 0 → 0 ≤ bilin (B + diagonal (excessRight K u v)) y y)
    (hα : chargeOf u a < 0) (hβ : chargeOf v b < 0)
    (hαβ : chargeOf u a * chargeOf v b < 1) :
    2 ≤ hermNegIndex ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) := by
  have h := hermNegIndex_glued_le_coupled A B K u v hK
  rwa [hermNegIndex_glued_eq_two hAa hBb hApos hBpos hα hβ hαβ] at h

/-- **Two forms coupled by nonnegative couplings have together at least the negative squares of
the two forms with potentials raised by their couplings.** -/
theorem hermNegIndex_add_le_coupled {A : Matrix ι₁ ι₁ ℝ} {B : Matrix ι₂ ι₂ ℝ}
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i) (K : ι₁ → ι₂ → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) :
    hermNegIndex ((A + diagonal fun i => ∑ j, K i j).map (↑) : Matrix ι₁ ι₁ ℂ) +
        hermNegIndex ((B + diagonal fun j => ∑ i, K i j).map (↑) : Matrix ι₂ ι₂ ℂ) ≤
      hermNegIndex ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) := by
  have h := hermNegIndex_glued_le_coupled A B K (fun _ => 0) (fun _ => 0) fun i j => by
    rw [zero_mul]
    exact hK i j
  have eL : excessLeft K (fun _ => 0) (fun _ => 0) = fun i => ∑ j, K i j :=
    funext fun i => Finset.sum_congr rfl fun j _ => by rw [zero_mul, sub_zero]
  have eR : excessRight K (fun _ => 0) (fun _ => 0) = fun j => ∑ i, K i j :=
    funext fun j => Finset.sum_congr rfl fun i _ => by rw [zero_mul, sub_zero]
  rw [eL, eR] at h
  have hblocks : ((glued (A + diagonal fun i => ∑ j, K i j) (B + diagonal fun j => ∑ i, K i j)
      (fun _ => 0) (fun _ => 0)).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) =
        fromBlocks ((A + diagonal fun i => ∑ j, K i j).map (↑)) 0 0
          ((B + diagonal fun j => ∑ i, K i j).map (↑)) := by
    ext (i | i) (j | j) <;> simp [glued]
  rw [hblocks, negIndex_fromBlocks_zero (isHermitian_map_ofReal (add_diagonal_symm hA _))
    (isHermitian_map_ofReal (add_diagonal_symm hB _))] at h
  exact h

/-- **The raised-potential lower bound for two adjacent windows.** -/
theorem hermNegIndex_glued_le_neutralWindow_add (Q R J₁ J₂ : ℕ) (u : Fin J₁ → ℝ)
    (v : Fin J₂ → ℝ) (huv : ∀ i j, u i * v j ≤ blockWeight Q (R + i) (R + J₁ + j)) :
    hermNegIndex ((glued
        (neutralWindow Q R J₁ +
          diagonal (excessLeft
            (fun (i : Fin J₁) (j : Fin J₂) => blockWeight Q (R + i) (R + J₁ + j)) u v))
        (neutralWindow Q (R + J₁) J₂ +
          diagonal (excessRight
            (fun (i : Fin J₁) (j : Fin J₂) => blockWeight Q (R + i) (R + J₁ + j)) u v))
        u v).map (↑) : Matrix (Fin J₁ ⊕ Fin J₂) (Fin J₁ ⊕ Fin J₂) ℂ) ≤
      hermNegIndex ((neutralWindow Q R (J₁ + J₂)).map (↑) : Matrix (Fin (J₁ + J₂)) _ ℂ) := by
  rw [hermNegIndex_neutralWindow_add]
  exact hermNegIndex_glued_le_coupled _ _ _ u v huv

/-- **Two adjacent windows hold together at least the bound states of the two windows with
potentials raised by their couplings to each other.** -/
theorem hermNegIndex_add_le_neutralWindow_add (Q R J₁ J₂ : ℕ) :
    hermNegIndex ((neutralWindow Q R J₁ +
        diagonal fun i : Fin J₁ => ∑ j : Fin J₂, blockWeight Q (R + i) (R + J₁ + j)).map (↑) :
          Matrix (Fin J₁) (Fin J₁) ℂ) +
      hermNegIndex ((neutralWindow Q (R + J₁) J₂ +
        diagonal fun j : Fin J₂ => ∑ i : Fin J₁, blockWeight Q (R + i) (R + J₁ + j)).map (↑) :
          Matrix (Fin J₂) (Fin J₂) ℂ) ≤
      hermNegIndex ((neutralWindow Q R (J₁ + J₂)).map (↑) : Matrix (Fin (J₁ + J₂)) _ ℂ) := by
  rw [hermNegIndex_neutralWindow_add]
  exact hermNegIndex_add_le_coupled (fun i j => neutralBlock_comm Q _ _)
    (fun i j => neutralBlock_comm Q _ _) _ fun i j =>
      (blockWeight_pos (by have := i.2; omega) Q).le

/-- **Decomposition of the lowered product model.** Its quadratic form equals the zero-charge
lowered direct sum plus `Σ u_i v_j (x_i − y_j)²`. -/
theorem bilin_glued_lowered_eq (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ) (K : ι₁ → ι₂ → ℝ)
    (u : ι₁ → ℝ) (v : ι₂ → ℝ) (w : ι₁ ⊕ ι₂ → ℝ) :
    bilin (glued (A - diagonal (excessLeft K u v)) (B - diagonal (excessRight K u v)) u v) w w =
      bilin (A - diagonal fun i => ∑ j, K i j) (fun i => w (Sum.inl i)) (fun i => w (Sum.inl i)) +
        bilin (B - diagonal fun j => ∑ i, K i j)
          (fun j => w (Sum.inr j)) (fun j => w (Sum.inr j)) +
        ∑ i, ∑ j, u i * v j * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 := by
  have hterm : ∀ i j, u i * v j * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 =
      u i * v j * w (Sum.inl i) ^ 2 + u i * v j * w (Sum.inr j) ^ 2 -
        2 * (w (Sum.inl i) * w (Sum.inr j) * (u i * v j)) := fun _ _ => by ring
  have hexp : ∑ i, ∑ j, u i * v j * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 =
      (∑ i, ∑ j, u i * v j * w (Sum.inl i) ^ 2) +
        (∑ i, ∑ j, u i * v j * w (Sum.inr j) ^ 2) -
        2 * (∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * (u i * v j)) := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ i, excessLeft K u v i * w (Sum.inl i) ^ 2 =
      (∑ i, (∑ j, K i j) * w (Sum.inl i) ^ 2) - ∑ i, ∑ j, u i * v j * w (Sum.inl i) ^ 2 := by
    simp only [excessLeft, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
  have h2 : ∑ j, excessRight K u v j * w (Sum.inr j) ^ 2 =
      (∑ j, (∑ i, K i j) * w (Sum.inr j) ^ 2) - ∑ i, ∑ j, u i * v j * w (Sum.inr j) ^ 2 := by
    simp only [excessRight, Finset.sum_sub_distrib, sub_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
  have h3 : chargeOf u (fun i => w (Sum.inl i)) * chargeOf v (fun j => w (Sum.inr j)) =
      ∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * (u i * v j) := by
    rw [chargeOf, chargeOf, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [bilin_glued, bilin_sub_diagonal, bilin_sub_diagonal, bilin_sub_diagonal, bilin_sub_diagonal,
    h1, h2, h3, hexp]
  ring

end RankOneBracket

/-! ### Sign elimination and exact single-block maximum -/

section SignAndMaximum

/-- If a symmetric form `A` is nonnegative on `ker u`, satisfies `A a = u`, and takes a negative
value somewhere, then its susceptibility `u·a` is nonpositive. -/
theorem chargeOf_nonpos_of_ker_nonneg_of_exists_neg {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {u a : ι → ℝ} (hA : ∀ i j, A i j = A j i)
    (hAa : ∀ i, ∑ j, A i j * a j = u i)
    (hApos : ∀ x, chargeOf u x = 0 → 0 ≤ bilin A x x)
    (hneg : ∃ x₀, bilin A x₀ x₀ < 0) : chargeOf u a ≤ 0 := by
  rcases hneg with ⟨x₀, hx₀⟩
  by_contra hpos'
  have hpos : 0 < chargeOf u a := not_le.mp hpos'
  have hker := hApos (fun i => chargeOf u a * x₀ i - chargeOf u x₀ * a i) (by
    rw [chargeOf_sub_smul]
    ring)
  rw [bilin_sub_smul hA hAa] at hker
  have hsq : 0 ≤ (chargeOf u x₀) ^ 2 := sq_nonneg _
  have h1 : (chargeOf u a) ^ 2 * bilin A x₀ x₀ < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_pos hpos) hx₀
  have h2 : 0 ≤ chargeOf u a * (chargeOf u x₀) ^ 2 := mul_nonneg hpos.le hsq
  linarith

/-- **Automatic sign elimination for gluing.** When `A` and `B` each take a negative value,
nonnegativity on `ker u` and `ker v` with `1 ≤ (u·a)(v·b)` forces `u·a < 0`, `v·b < 0`, and
`hermNegIndex (glued A B u v) = 1`. -/
theorem hermNegIndex_glued_eq_one_of_exists_neg {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {A : Matrix ι₁ ι₁ ℝ} {B : Matrix ι₂ ι₂ ℝ} {u a : ι₁ → ℝ} {v b : ι₂ → ℝ}
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (hAa : ∀ i, ∑ j, A i j * a j = u i) (hBb : ∀ i, ∑ j, B i j * b j = v i)
    (hApos : ∀ x, chargeOf u x = 0 → 0 ≤ bilin A x x)
    (hBpos : ∀ y, chargeOf v y = 0 → 0 ≤ bilin B y y)
    (hAneg : ∃ x₀, bilin A x₀ x₀ < 0) (hBneg : ∃ y₀, bilin B y₀ y₀ < 0)
    (hαβ : 1 ≤ chargeOf u a * chargeOf v b) :
    hermNegIndex ((glued A B u v).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) = 1 := by
  have hα0 := chargeOf_nonpos_of_ker_nonneg_of_exists_neg hA hAa hApos hAneg
  have hβ0 := chargeOf_nonpos_of_ker_nonneg_of_exists_neg hB hBb hBpos hBneg
  have hβ : chargeOf v b < 0 := by
    rcases lt_or_eq_of_le hβ0 with hlt | heq
    · exact hlt
    · rw [heq, mul_zero] at hαβ
      linarith
  exact hermNegIndex_glued_eq_one hA hB hAa hBb hApos hBpos hβ hαβ

/-- Weighted Cauchy–Schwarz for nonnegative weights: `(∑ δ_j c_j)² ≤ (∑ δ_j)(∑ δ_j c_j²)`. -/
theorem sq_sum_mul_le_sum_mul_sum_sq {ι : Type*} [Fintype ι] (δ c : ι → ℝ)
    (hδ : ∀ j, 0 ≤ δ j) :
    (∑ j, δ j * c j) ^ 2 ≤ (∑ j, δ j) * ∑ j, δ j * c j ^ 2 := by
  have h0 : 0 ≤ ∑ j, ∑ m, δ j * δ m * (c j - c m) ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun m _ =>
      mul_nonneg (mul_nonneg (hδ j) (hδ m)) (sq_nonneg _)
  have hexp : ∑ j, ∑ m, δ j * δ m * (c j - c m) ^ 2 =
      2 * ((∑ j, δ j) * ∑ j, δ j * c j ^ 2 - (∑ j, δ j * c j) ^ 2) := by
    have hterm : ∀ j m, δ j * δ m * (c j - c m) ^ 2 =
        (δ j * c j ^ 2) * δ m + δ j * (δ m * c m ^ 2) - 2 * ((δ j * c j) * (δ m * c m)) :=
      fun _ _ => by ring
    have hsum : ∑ j, ∑ m, δ j * δ m * (c j - c m) ^ 2 =
        ∑ j, ∑ m, ((δ j * c j ^ 2) * δ m + δ j * (δ m * c m ^ 2) -
          2 * ((δ j * c j) * (δ m * c m))) :=
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => hterm j m
    rw [hsum]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, sq]
    ring
  linarith

/-- On a single left block, choosing `u = 1` and `v = K 0` leaves zero left excess. -/
theorem excessLeft_fin_one_zero {ι₂ : Type*} [Fintype ι₂] (K : Fin 1 → ι₂ → ℝ) :
    excessLeft K (fun _ => 1) (K 0) = 0 := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [excessLeft]

/-- On a single left block, choosing `u = 1` and `v = K 0` leaves zero right excess. -/
theorem excessRight_fin_one_zero {ι₂ : Type*} [Fintype ι₂] (K : Fin 1 → ι₂ → ℝ) :
    excessRight K (fun _ => 1) (K 0) = 0 := by
  ext j
  simp [excessRight]

/-- **Exact global maximum of the susceptibility product on a single left block.** Let `A` be a
`1 × 1` negative matrix (`A 0 0 < 0`), `B` symmetric, `K 0` coupled through `B b₀ = K 0` with
`b₀ ≤ 0`, and `1 ≤ (1 / A 0 0) * (K 0 · b₀)`. Then every admissible charge pair `(u, v)` whose
lowered forms are nonnegative on `ker u` and `ker v` satisfies
`(u · a) * (v · b) ≤ (1 / A 0 0) * (K 0 · b₀)`. -/
theorem susceptibility_mul_le_of_fin_one {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂]
    {A : Matrix (Fin 1) (Fin 1) ℝ} {B : Matrix ι₂ ι₂ ℝ} {K : Fin 1 → ι₂ → ℝ}
    {b₀ : ι₂ → ℝ} (hA0 : A 0 0 < 0) (hB : ∀ j m, B j m = B m j)
    (hBb₀ : ∀ j, ∑ m, B j m * b₀ m = K 0 j) (hb₀ : ∀ j, b₀ j ≤ 0)
    (hge1 : 1 ≤ 1 / A 0 0 * chargeOf (K 0) b₀)
    {u a : Fin 1 → ℝ} {v b : ι₂ → ℝ} (hK : ∀ i j, u i * v j ≤ K i j)
    (hBb : ∀ j, ∑ m, (B - diagonal (excessRight K u v)) j m * b m = v j)
    (hAa : ∀ i, ∑ l, (A - diagonal (excessLeft K u v)) i l * a l = u i)
    (hBpos : ∀ y, chargeOf v y = 0 → 0 ≤ bilin (B - diagonal (excessRight K u v)) y y) :
    chargeOf u a * chargeOf v b ≤ 1 / A 0 0 * chargeOf (K 0) b₀ := by
  set A₀ : ℝ := -A 0 0
  set B₀ : ℝ := -chargeOf (K 0) b₀
  have hA₀ : 0 < A₀ := neg_pos.mpr hA0
  have hdiv : 1 / A 0 0 * chargeOf (K 0) b₀ = B₀ / A₀ := by
    have hne : A 0 0 ≠ 0 := hA0.ne
    have hA₀ne : A₀ ≠ 0 := hA₀.ne'
    dsimp [A₀, B₀]
    field_simp
  rw [hdiv] at hge1 ⊢
  have hAB : A₀ ≤ B₀ := by
    have := mul_le_mul_of_nonneg_right hge1 hA₀.le
    rwa [one_mul, div_mul_cancel₀ _ hA₀.ne'] at this
  have hB₀ : 0 < B₀ := lt_of_lt_of_le hA₀ hAB
  by_cases hu0 : u 0 = 0
  · have hua : chargeOf u a = 0 := by
      simp [chargeOf, hu0]
    rw [hua, zero_mul]
    exact le_trans zero_le_one hge1
  · set δ : ι₂ → ℝ := fun j => K 0 j - u 0 * v j
    have hδ : ∀ j, 0 ≤ δ j := fun j => sub_nonneg.mpr (hK 0 j)
    set S₁ : ℝ := ∑ j, δ j
    have hS₁ : 0 ≤ S₁ := Finset.sum_nonneg fun j _ => hδ j
    have hexL : excessLeft K u v 0 = S₁ := rfl
    have hexR : excessRight K u v = δ := by
      ext j
      simp [excessRight, δ]
    -- rescale `(v, b)` by `u 0` to eliminate `u 0` without division
    set v' : ι₂ → ℝ := fun j => u 0 * v j
    set b' : ι₂ → ℝ := fun j => u 0 * b j
    have hBb' : ∀ j, ∑ m, (B - diagonal δ) j m * b' m = v' j := by
      intro j
      rw [← hexR]
      have h := congrArg (u 0 * ·) (hBb j)
      dsimp [v', b'] at h ⊢
      rw [← h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hB'pos : ∀ y, chargeOf v' y = 0 → 0 ≤ bilin (B - diagonal δ) y y := by
      intro y hy
      have hyv : chargeOf v y = 0 := by
        have h1 : chargeOf v' y = u 0 * chargeOf v y := by
          simp only [chargeOf, v', Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [h1] at hy
        exact (mul_eq_zero.mp hy).resolve_left hu0
      rw [← hexR]
      exact hBpos y hyv
    have hAa0 : (-A₀ - S₁) * a 0 = u 0 := by
      have h := hAa 0
      rw [Fin.sum_univ_one] at h
      simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, hexL] at h
      dsimp [A₀]
      linarith
    have hprod_eq : (A₀ + S₁) * (chargeOf u a * chargeOf v b) = -chargeOf v' b' := by
      have hua : chargeOf u a = u 0 * a 0 := by simp [chargeOf]
      have hvb' : chargeOf v' b' = u 0 ^ 2 * chargeOf v b := by
        simp only [chargeOf, v', b', Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      calc (A₀ + S₁) * (chargeOf u a * chargeOf v b)
          = u 0 * (-((-A₀ - S₁) * a 0) * chargeOf v b) := by rw [hua]; ring
        _ = -chargeOf v' b' := by rw [hAa0, hvb']; ring
    have hASpos : 0 < A₀ + S₁ := by linarith
    by_cases hβ' : 0 ≤ chargeOf v' b'
    · have hle0 : (A₀ + S₁) * (chargeOf u a * chargeOf v b) ≤ 0 := by linarith
      have hnonpos : chargeOf u a * chargeOf v b ≤ 0 :=
        nonpos_of_mul_nonpos_right hle0 hASpos
      exact le_trans hnonpos (le_trans zero_le_one hge1)
    · push Not at hβ'
      set T₁ : ℝ := ∑ j, δ j * (-b₀ j)
      set T₂ : ℝ := ∑ j, δ j * b₀ j ^ 2
      have hT₁ : 0 ≤ T₁ := Finset.sum_nonneg fun j _ =>
        mul_nonneg (hδ j) (neg_nonneg.mpr (hb₀ j))
      have hT₂ : 0 ≤ T₂ := Finset.sum_nonneg fun j _ => mul_nonneg (hδ j) (sq_nonneg _)
      have hBTpos : 0 < B₀ + T₂ := by linarith
      -- test kernel nonnegativity of `B - diagonal δ` on `β' b₀ - (v' · b₀) b'`
      have hker := hB'pos (fun j => chargeOf v' b' * b₀ j - chargeOf v' b₀ * b' j) (by
        rw [chargeOf_sub_smul]
        ring)
      rw [bilin_sub_smul (sub_diagonal_symm hB δ) hBb'] at hker
      have hB_b₀ : bilin (B - diagonal δ) b₀ b₀ = -(B₀ + T₂) := by
        rw [bilin_sub_diagonal, bilin_right_eq_chargeOf hBb₀ b₀]
        dsimp [B₀, T₂]
        ring
      have hv'_b₀ : chargeOf v' b₀ = -(B₀ - T₁) := by
        have hv'def : ∀ j, v' j * b₀ j = K 0 j * b₀ j + δ j * (-b₀ j) := fun j => by
          dsimp [v', δ]
          ring
        dsimp [B₀, T₁]
        simp only [chargeOf, hv'def, Finset.sum_add_distrib]
        ring
      rw [hB_b₀, hv'_b₀] at hker
      -- divide out `chargeOf v' b' < 0`
      have hbound : (-chargeOf v' b') * (B₀ + T₂) ≤ (B₀ - T₁) ^ 2 := by
        by_contra hlt
        have hlt' : (B₀ - T₁) ^ 2 < (-chargeOf v' b') * (B₀ + T₂) := not_le.mp hlt
        have hmul := mul_neg_of_neg_of_pos hβ' (sub_pos.mpr hlt')
        nlinarith
      have hcs : T₁ ^ 2 ≤ S₁ * T₂ := by
        have h := sq_sum_mul_le_sum_mul_sum_sq δ (fun j => -b₀ j) hδ
        have hsq : (∑ j, δ j * (-b₀ j) ^ 2) = T₂ :=
          Finset.sum_congr rfl fun j _ => by ring
        rwa [hsq] at h
      have hkey : A₀ * (B₀ - T₁) ^ 2 ≤ (A₀ + S₁) * (B₀ + T₂) * B₀ := by
        have hdiff : (A₀ + S₁) * (B₀ + T₂) * B₀ - A₀ * (B₀ - T₁) ^ 2 =
            S₁ * B₀ ^ 2 + 2 * A₀ * B₀ * T₁ + A₀ * B₀ * T₂ +
              (B₀ - A₀) * (S₁ * T₂) + A₀ * (S₁ * T₂ - T₁ ^ 2) := by ring
        have h1 : 0 ≤ S₁ * B₀ ^ 2 := mul_nonneg hS₁ (sq_nonneg _)
        have h2 : 0 ≤ 2 * A₀ * B₀ * T₁ := by positivity
        have h3 : 0 ≤ A₀ * B₀ * T₂ := by positivity
        have h4 : 0 ≤ (B₀ - A₀) * (S₁ * T₂) :=
          mul_nonneg (sub_nonneg.mpr hAB) (mul_nonneg hS₁ hT₂)
        have h5 : 0 ≤ A₀ * (S₁ * T₂ - T₁ ^ 2) :=
          mul_nonneg hA₀.le (sub_nonneg.mpr hcs)
        linarith
      -- conclude `chargeOf u a * chargeOf v b ≤ B₀ / A₀`
      rw [le_div_iff₀ hA₀]
      have hstep1 : A₀ * ((-chargeOf v' b') * (B₀ + T₂)) ≤ A₀ * (B₀ - T₁) ^ 2 :=
        mul_le_mul_of_nonneg_left hbound hA₀.le
      rw [← hprod_eq] at hstep1
      have hstep2 : (A₀ + S₁) * (B₀ + T₂) * (chargeOf u a * chargeOf v b * A₀) ≤
          (A₀ + S₁) * (B₀ + T₂) * B₀ := by
        calc (A₀ + S₁) * (B₀ + T₂) * (chargeOf u a * chargeOf v b * A₀)
            = A₀ * ((A₀ + S₁) * (chargeOf u a * chargeOf v b) * (B₀ + T₂)) := by ring
          _ ≤ A₀ * (B₀ - T₁) ^ 2 := hstep1
          _ ≤ (A₀ + S₁) * (B₀ + T₂) * B₀ := hkey
      exact le_of_mul_le_mul_left hstep2 (mul_pos hASpos hBTpos)

end SignAndMaximum

/-! ### Multi-charge gluing and response-matrix inertia -/

section MultiCharge

variable {ι₁ ι₂ ρ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ρ]
  [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ρ]

/-- Two forms coupled through `r` pairs of charges:
`A(x) + B(y) − 2 Σ_k (Uᵀ x)_k (Vᵀ y)_k`. -/
def gluedMatrix (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (U : Matrix ι₁ ρ ℝ) (V : Matrix ι₂ ρ ℝ) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ :=
  coupled A B fun i j => ∑ k, U i k * V j k

/-- Left excess over a multi-charge coupling `U Vᵀ`. -/
def excessLeftMatrix (K : ι₁ → ι₂ → ℝ) (U : Matrix ι₁ ρ ℝ) (V : Matrix ι₂ ρ ℝ) (i : ι₁) : ℝ :=
  ∑ j, (K i j - ∑ k, U i k * V j k)

/-- Right excess over a multi-charge coupling `U Vᵀ`. -/
def excessRightMatrix (K : ι₁ → ι₂ → ℝ) (U : Matrix ι₁ ρ ℝ) (V : Matrix ι₂ ρ ℝ) (j : ι₂) : ℝ :=
  ∑ i, (K i j - ∑ k, U i k * V j k)

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- On a single charge channel (`Fin 1`), `gluedMatrix` agrees with `glued`. -/
theorem gluedMatrix_fin_one (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ) (u : ι₁ → ℝ) (v : ι₂ → ℝ) :
    gluedMatrix A B (Matrix.of fun i (_ : Fin 1) => u i) (Matrix.of fun j (_ : Fin 1) => v j) =
      glued A B u v := by
  ext (i | i) (j | j) <;> simp [gluedMatrix, coupled, glued]

omit [DecidableEq ρ] in
/-- **Multi-charge lowered potential comparison.** When `∑_k U_ik V_jk ≤ K_ij`, the coupled form
dominates the multi-charge glued form with potentials lowered by the excess. -/
theorem bilin_gluedMatrix_le_coupled (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (K : ι₁ → ι₂ → ℝ) (U : Matrix ι₁ ρ ℝ) (V : Matrix ι₂ ρ ℝ)
    (hK : ∀ i j, (∑ k, U i k * V j k) ≤ K i j) (w : ι₁ ⊕ ι₂ → ℝ) :
    bilin (gluedMatrix (A - diagonal (excessLeftMatrix K U V))
        (B - diagonal (excessRightMatrix K U V)) U V) w w ≤
      bilin (coupled A B K) w w := by
  have hsq : 0 ≤ ∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hK i j)) (sq_nonneg _)
  have hterm : ∀ i j, (K i j - ∑ k, U i k * V j k) * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 =
      (K i j - ∑ k, U i k * V j k) * w (Sum.inl i) ^ 2 +
        (K i j - ∑ k, U i k * V j k) * w (Sum.inr j) ^ 2 -
        2 * (w (Sum.inl i) * w (Sum.inr j) * K i j) +
          2 * (w (Sum.inl i) * w (Sum.inr j) * ∑ k, U i k * V j k) := fun _ _ => by ring
  have hexp : ∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 =
      (∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * w (Sum.inl i) ^ 2) +
        (∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * w (Sum.inr j) ^ 2) -
        2 * (∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * K i j) +
          2 * (∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * ∑ k, U i k * V j k) := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ i, excessLeftMatrix K U V i * w (Sum.inl i) ^ 2 =
      ∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * w (Sum.inl i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [excessLeftMatrix, Finset.sum_mul]
  have h2 : ∑ j, excessRightMatrix K U V j * w (Sum.inr j) ^ 2 =
      ∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * w (Sum.inr j) ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [excessRightMatrix, Finset.sum_mul]
  rw [gluedMatrix, bilin_coupled, bilin_coupled, bilin_sub_diagonal, bilin_sub_diagonal, h1, h2]
  linarith

omit [DecidableEq ρ] in
/-- **Multi-charge upper bound on the negative index.** -/
theorem hermNegIndex_coupled_le_gluedMatrix (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (K : ι₁ → ι₂ → ℝ) (U : Matrix ι₁ ρ ℝ) (V : Matrix ι₂ ρ ℝ)
    (hK : ∀ i j, (∑ k, U i k * V j k) ≤ K i j) :
    hermNegIndex ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) ≤
      hermNegIndex ((gluedMatrix (A - diagonal (excessLeftMatrix K U V))
        (B - diagonal (excessRightMatrix K U V)) U V).map (↑) :
          Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) :=
  HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_le _ _ fun c => by
    rw [hermQuad_map_eq_bilin, hermQuad_map_eq_bilin]
    exact add_le_add (bilin_gluedMatrix_le_coupled A B K U V hK _)
      (bilin_gluedMatrix_le_coupled A B K U V hK _)

omit [DecidableEq ρ] in
/-- **Multi-charge raised potential comparison.** -/
theorem bilin_coupled_le_gluedMatrix_raised (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (K : ι₁ → ι₂ → ℝ) (U : Matrix ι₁ ρ ℝ) (V : Matrix ι₂ ρ ℝ)
    (hK : ∀ i j, (∑ k, U i k * V j k) ≤ K i j) (w : ι₁ ⊕ ι₂ → ℝ) :
    bilin (coupled A B K) w w ≤
      bilin (gluedMatrix (A + diagonal (excessLeftMatrix K U V))
        (B + diagonal (excessRightMatrix K U V)) U V) w w := by
  have hsq : 0 ≤ ∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * (w (Sum.inl i) + w (Sum.inr j)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hK i j)) (sq_nonneg _)
  have hterm : ∀ i j, (K i j - ∑ k, U i k * V j k) * (w (Sum.inl i) + w (Sum.inr j)) ^ 2 =
      (K i j - ∑ k, U i k * V j k) * w (Sum.inl i) ^ 2 +
        (K i j - ∑ k, U i k * V j k) * w (Sum.inr j) ^ 2 +
        2 * (w (Sum.inl i) * w (Sum.inr j) * K i j) -
          2 * (w (Sum.inl i) * w (Sum.inr j) * ∑ k, U i k * V j k) := fun _ _ => by ring
  have hexp : ∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * (w (Sum.inl i) + w (Sum.inr j)) ^ 2 =
      (∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * w (Sum.inl i) ^ 2) +
        (∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * w (Sum.inr j) ^ 2) +
        2 * (∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * K i j) -
          2 * (∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * ∑ k, U i k * V j k) := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ i, excessLeftMatrix K U V i * w (Sum.inl i) ^ 2 =
      ∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * w (Sum.inl i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [excessLeftMatrix, Finset.sum_mul]
  have h2 : ∑ j, excessRightMatrix K U V j * w (Sum.inr j) ^ 2 =
      ∑ i, ∑ j, (K i j - ∑ k, U i k * V j k) * w (Sum.inr j) ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [excessRightMatrix, Finset.sum_mul]
  rw [gluedMatrix, bilin_coupled, bilin_coupled, bilin_add_diagonal, bilin_add_diagonal, h1, h2]
  linarith

omit [DecidableEq ρ] in
/-- **Multi-charge lower bound on the negative index.** -/
theorem hermNegIndex_gluedMatrix_le_coupled (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (K : ι₁ → ι₂ → ℝ) (U : Matrix ι₁ ρ ℝ) (V : Matrix ι₂ ρ ℝ)
    (hK : ∀ i j, (∑ k, U i k * V j k) ≤ K i j) :
    hermNegIndex ((gluedMatrix (A + diagonal (excessLeftMatrix K U V))
        (B + diagonal (excessRightMatrix K U V)) U V).map (↑) :
          Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) ≤
      hermNegIndex ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) :=
  HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_le _ _ fun c => by
    rw [hermQuad_map_eq_bilin, hermQuad_map_eq_bilin]
    exact add_le_add (bilin_coupled_le_gluedMatrix_raised A B K U V hK _)
      (bilin_coupled_le_gluedMatrix_raised A B K U V hK _)

/-- The multi-charge susceptibility (response) matrix `Wᵀ M⁻¹ W` of a window `M` in channel `W`. -/
def responseMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (W : Matrix ι ρ ℝ) : Matrix ρ ρ ℝ :=
  Wᵀ * M⁻¹ * W

omit [Fintype ρ] [DecidableEq ρ] in
theorem responseMatrix_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : ∀ i j, M i j = M j i) (W : Matrix ι ρ ℝ) (k l : ρ) :
    responseMatrix M W k l = responseMatrix M W l k := by
  have hMt : Mᵀ = M := Matrix.ext fun i j => hM j i
  have hMinv : (M⁻¹)ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hMt]
  have hrt : (responseMatrix M W)ᵀ = responseMatrix M W := by
    simp only [responseMatrix, Matrix.transpose_mul, Matrix.transpose_transpose, hMinv,
      Matrix.mul_assoc]
  exact congrFun (congrFun hrt l) k

/-- An invertible Hermitian matrix has the same negative index as its inverse. -/
theorem hermNegIndex_nonsing_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hHu : IsUnit H) (hH : H.IsHermitian) :
    hermNegIndex H⁻¹ = hermNegIndex H := by
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hHu
  have hcongr : Hᴴ * H⁻¹ * H = H := by
    rw [hH.eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul H hdet, Matrix.mul_one]
  have h := negIndex_conjugate H⁻¹ hHu
  rw [hcongr] at h
  exact h.symm

/-- Complexification preserves matrix units and commutes with inversion on invertible matrices. -/
theorem isUnit_map_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hMu : IsUnit M) : IsUnit (M.map (↑) : Matrix ι ι ℂ) := by
  have heq : (M.map (↑) : Matrix ι ι ℂ) = RingHom.mapMatrix Complex.ofRealHom M := rfl
  rw [heq]
  exact hMu.map (RingHom.mapMatrix Complex.ofRealHom)

theorem map_ofReal_nonsing_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hMu : IsUnit M) :
    ((M⁻¹).map (↑) : Matrix ι ι ℂ) = (M.map (↑) : Matrix ι ι ℂ)⁻¹ := by
  have hdetR : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hMu
  have hdetC : IsUnit (M.map (↑) : Matrix ι ι ℂ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_map_ofReal hMu)
  have hmul : (M.map (↑) : Matrix ι ι ℂ) * ((M⁻¹).map (↑) : Matrix ι ι ℂ) = 1 := by
    have hm : (M.map (↑) : Matrix ι ι ℂ) * ((M⁻¹).map (↑) : Matrix ι ι ℂ) = (M * M⁻¹).map (↑) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [hm, Matrix.mul_nonsing_inv M hdetR]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  calc ((M⁻¹).map (↑) : Matrix ι ι ℂ)
      = (M.map (↑) : Matrix ι ι ℂ)⁻¹ *
          ((M.map (↑) : Matrix ι ι ℂ) * ((M⁻¹).map (↑) : Matrix ι ι ℂ)) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetC, Matrix.one_mul]
    _ = (M.map (↑) : Matrix ι ι ℂ)⁻¹ := by rw [hmul, Matrix.mul_one]

omit [DecidableEq ρ] in
/-- **Schur-complement inertia of `gluedMatrix`.** For invertible `A`, gluing through `U Vᵀ`
reduces to `A` and the perturbed second window `B − V (Uᵀ A⁻¹ U) Vᵀ`. -/
theorem hermNegIndex_gluedMatrix_schur {A : Matrix ι₁ ι₁ ℝ} {B : Matrix ι₂ ι₂ ℝ}
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i) (hAu : IsUnit A)
    (U : Matrix ι₁ ρ ℝ) (V : Matrix ι₂ ρ ℝ) :
    hermNegIndex ((gluedMatrix A B U V).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) =
      hermNegIndex (A.map (↑) : Matrix ι₁ ι₁ ℂ) +
        hermNegIndex ((B - V * responseMatrix A U * Vᵀ).map (↑) : Matrix ι₂ ι₂ ℂ) := by
  let C12 : Matrix ι₁ ι₂ ℂ := (-(U * Vᵀ)).map (↑)
  have hC12h : (C12ᴴ : Matrix ι₂ ι₁ ℂ) = (-(V * Uᵀ)).map (↑) := by
    ext j i
    simp [C12, Matrix.mul_apply, mul_comm]
  have hblocks : ((gluedMatrix A B U V).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) =
      fromBlocks (A.map (↑)) C12 C12ᴴ (B.map (↑)) := by
    rw [hC12h]
    ext (i | i) (j | j) <;> simp [gluedMatrix, coupled, C12, Matrix.mul_apply, mul_comm]
  rw [hblocks, haynsworth_negIndex (isUnit_map_ofReal hAu) (isHermitian_map_ofReal hA) C12
    (isHermitian_map_ofReal hB)]
  congr 2
  rw [hC12h, ← map_ofReal_nonsing_inv hAu]
  trans ((B - (-(V * Uᵀ) * A⁻¹ * -(U * Vᵀ))).map (↑) : Matrix ι₂ ι₂ ℂ)
  · ext j m
    simp only [C12, Matrix.sub_apply, Matrix.map_apply, Matrix.mul_apply,
      Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul]
  · have heqM : -(V * Uᵀ) * A⁻¹ * -(U * Vᵀ) = V * responseMatrix A U * Vᵀ := by
      simp only [responseMatrix, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
    rw [heqM]

/-- **Multi-charge response-matrix gluing law.** When `A`, `B`, and the left response matrix
`𝒜 = Uᵀ A⁻¹ U` are invertible,
`hermNegIndex (gluedMatrix A B U V) + hermNegIndex 𝒜 = hermNegIndex A + hermNegIndex B + hermNegIndex (𝒜⁻¹ − ℬ)`,
where `ℬ = Vᵀ B⁻¹ V`. -/
theorem hermNegIndex_gluedMatrix_response {A : Matrix ι₁ ι₁ ℝ} {B : Matrix ι₂ ι₂ ℝ}
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (hAu : IsUnit A) (hBu : IsUnit B) (U : Matrix ι₁ ρ ℝ) (V : Matrix ι₂ ρ ℝ)
    (hRu : IsUnit (responseMatrix A U)) :
    hermNegIndex ((gluedMatrix A B U V).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) +
        hermNegIndex ((responseMatrix A U).map (↑) : Matrix ρ ρ ℂ) =
      hermNegIndex (A.map (↑) : Matrix ι₁ ι₁ ℂ) +
        hermNegIndex (B.map (↑) : Matrix ι₂ ι₂ ℂ) +
        hermNegIndex (((responseMatrix A U)⁻¹ - responseMatrix B V).map (↑) : Matrix ρ ρ ℂ) := by
  have hR₁s : ∀ k l, responseMatrix A U k l = responseMatrix A U l k := responseMatrix_symm hA U
  have hR₁inv_s : ∀ k l, ((responseMatrix A U)⁻¹) k l = ((responseMatrix A U)⁻¹) l k := by
    have hRt : (responseMatrix A U)ᵀ = responseMatrix A U := Matrix.ext fun k l => hR₁s l k
    have hinv : ((responseMatrix A U)⁻¹)ᵀ = (responseMatrix A U)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hRt]
    exact fun k l => congrFun (congrFun hinv l) k
  have hdetR : IsUnit (responseMatrix A U).det :=
    (Matrix.isUnit_iff_isUnit_det (responseMatrix A U)).mp hRu
  have hR₁inv_u : IsUnit (responseMatrix A U)⁻¹ :=
    ⟨⟨(responseMatrix A U)⁻¹, responseMatrix A U,
      Matrix.nonsing_inv_mul (responseMatrix A U) hdetR,
      Matrix.mul_nonsing_inv (responseMatrix A U) hdetR⟩, rfl⟩
  let Iρ : Matrix ρ ρ ℝ := 1
  have hleft := hermNegIndex_gluedMatrix_schur hR₁inv_s hB hR₁inv_u (-Iρ) V
  have hrespI : V * responseMatrix (responseMatrix A U)⁻¹ (-Iρ) * Vᵀ =
      V * responseMatrix A U * Vᵀ := by
    have hinv2 : ((responseMatrix A U)⁻¹)⁻¹ = responseMatrix A U :=
      Matrix.nonsing_inv_nonsing_inv (responseMatrix A U) hdetR
    have hr : responseMatrix (responseMatrix A U)⁻¹ (-Iρ) = ((responseMatrix A U)⁻¹)⁻¹ := by
      simp [responseMatrix, Iρ]
    rw [hr, hinv2]
  rw [hrespI, map_ofReal_nonsing_inv (M := responseMatrix A U) hRu,
    hermNegIndex_nonsing_inv (isUnit_map_ofReal (M := responseMatrix A U) hRu)
      (isHermitian_map_ofReal hR₁s)]
    at hleft
  have hswap : ((gluedMatrix B (responseMatrix A U)⁻¹ V (-Iρ)).map (↑) :
      Matrix (ι₂ ⊕ ρ) (ι₂ ⊕ ρ) ℂ).submatrix
      (Equiv.sumComm ρ ι₂) (Equiv.sumComm ρ ι₂) =
        ((gluedMatrix (responseMatrix A U)⁻¹ B (-Iρ) V).map (↑) : Matrix (ρ ⊕ ι₂) (ρ ⊕ ι₂) ℂ) := by
    ext (k | j) (l | m) <;> simp [gluedMatrix, coupled, mul_comm]
  have hright := hermNegIndex_gluedMatrix_schur hB hR₁inv_s hBu V (-Iρ)
  have hrespB : (-Iρ) * responseMatrix B V * (-Iρ)ᵀ = responseMatrix B V := by
    simp [Iρ]
  rw [hrespB] at hright
  have heq : hermNegIndex ((gluedMatrix (responseMatrix A U)⁻¹ B (-Iρ) V).map (↑) :
      Matrix (ρ ⊕ ι₂) (ρ ⊕ ι₂) ℂ) =
      hermNegIndex ((gluedMatrix B (responseMatrix A U)⁻¹ V (-Iρ)).map (↑) :
        Matrix (ι₂ ⊕ ρ) (ι₂ ⊕ ρ) ℂ) := by
    rw [← hswap, hermNegIndex_submatrix_equiv]
  have hmain := hermNegIndex_gluedMatrix_schur hA hB hAu U V
  omega

end MultiCharge

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
