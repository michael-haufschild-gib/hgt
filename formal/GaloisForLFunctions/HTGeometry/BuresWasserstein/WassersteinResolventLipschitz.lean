import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinResolventExpansion

/-!
# Lipschitz dependence of the quadratic remainder

The remainder `R(Y,X) = G(Y,X) - (Y - X)` of the normalized resolvent increment is
`-(Y-X)Y⁻¹(Y-X) + X N X⁻¹ N X` with `N = 1 - (X # Y⁻¹)`.  Both summands are quadratic in
`Y - X`, so the difference of two of them telescopes into terms each carrying one factor
`Y₁ - Y₂` and one factor `Yᵢ - X`.  That gives

`‖R(Y₁,X) - R(Y₂,X)‖ ≤ C (‖Y₁-X‖ + ‖Y₂-X‖) ‖Y₁-Y₂‖`,

the estimate that makes the resolvent map a contraction on a ball of radius `O(h)`.
-/

open scoped NNReal Ring BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A five-fold product of nonnegative reals is monotone in each factor. -/
lemma mul5_le {a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ : ℝ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (h₄ : a₄ ≤ b₄) (h₅ : a₅ ≤ b₅)
    (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄) (ha₅ : 0 ≤ a₅)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) (hb₄ : 0 ≤ b₄) :
    a₁ * a₂ * a₃ * a₄ * a₅ ≤ b₁ * b₂ * b₃ * b₄ * b₅ := by
  have p1 : a₁ * a₂ ≤ b₁ * b₂ := mul_le_mul h₁ h₂ ha₂ hb₁
  have p2 : a₁ * a₂ * a₃ ≤ b₁ * b₂ * b₃ := mul_le_mul p1 h₃ ha₃ (mul_nonneg hb₁ hb₂)
  have p3 : a₁ * a₂ * a₃ * a₄ ≤ b₁ * b₂ * b₃ * b₄ :=
    mul_le_mul p2 h₄ ha₄ (mul_nonneg (mul_nonneg hb₁ hb₂) hb₃)
  exact mul_le_mul p3 h₅ ha₅ (mul_nonneg (mul_nonneg (mul_nonneg hb₁ hb₂) hb₃) hb₄)

omit [PartialOrder A] [StarOrderedRing A] in
/-- Telescoping a sandwich difference. -/
lemma sandwich_sub_telescope (u₁ u₂ v₁ v₂ : A) :
    u₁ * v₁ * u₁ - u₂ * v₂ * u₂
      = (u₁ - u₂) * v₁ * u₁ + u₂ * (v₁ - v₂) * u₁ + u₂ * v₂ * (u₁ - u₂) := by
  noncomm_ring

omit [PartialOrder A] [StarOrderedRing A] in
/-- Telescoping the quintuple product. -/
lemma quintuple_sub_telescope (x y n₁ n₂ : A) :
    x * n₁ * y * n₁ * x - x * n₂ * y * n₂ * x
      = x * (n₁ - n₂) * y * n₁ * x + x * n₂ * y * (n₁ - n₂) * x := by
  noncomm_ring

/-- The geometric mean is Lipschitz in its second argument through the inverse. -/
theorem norm_gm_sub_gm_le {X Y₁ Y₂ : A} (hX : IsStrictlyPositive X)
    (hY₁ : IsStrictlyPositive Y₁) (hY₂ : IsStrictlyPositive Y₂)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hXα : α • (1 : A) ≤ X) (hXβ : X ≤ β • (1 : A))
    (hY₁α : α • (1 : A) ≤ Y₁) (hY₁β : Y₁ ≤ β • (1 : A))
    (hY₂α : α • (1 : A) ≤ Y₂) (hY₂β : Y₂ ≤ β • (1 : A)) :
    ‖gm X Y₁⁻¹ʳ - gm X Y₂⁻¹ʳ‖ ≤ gmFieldLipConst α β * ‖Y₁ - Y₂‖ := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hβinv : (0 : ℝ) < β⁻¹ := inv_pos.mpr hβ
  have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  have hgb : (Real.sqrt (α * β⁻¹)) • (1 : A) ≤ gm X Y₁⁻¹ʳ :=
    smul_one_le_gm hX hY₁.ringInverse hα hβinv hXα
      (smul_one_le_ringInverse_of_le_smul_one hY₁ hβ hY₁β)
  have hgc : (Real.sqrt (α * β⁻¹)) • (1 : A) ≤ gm X Y₂⁻¹ʳ :=
    smul_one_le_gm hX hY₂.ringInverse hα hβinv hXα
      (smul_one_le_ringInverse_of_le_smul_one hY₂ hβ hY₂β)
  have hgmi := norm_gm_sub_le_of_Icc hX hY₁.ringInverse hY₂.ringInverse hα hγ hβ hXα hXβ hgb hgc
  have hinvn : ‖(Y₁⁻¹ʳ : A) - Y₂⁻¹ʳ‖ ≤ (α⁻¹ * α⁻¹) * ‖Y₁ - Y₂‖ :=
    norm_ringInverse_sub_le_of_smul_one_le hY₁ hY₂ hα hY₁α hY₂α
  have hstep : (2 * (Real.sqrt (α * β⁻¹) * β⁻¹)) * ‖gm X Y₁⁻¹ʳ - gm X Y₂⁻¹ʳ‖
      ≤ (β * α⁻¹) * ((α⁻¹ * α⁻¹) * ‖Y₁ - Y₂‖) :=
    hgmi.trans (mul_le_mul_of_nonneg_left hinvn (by positivity))
  rw [← le_div_iff₀' (by positivity : (0:ℝ) < 2 * (Real.sqrt (α * β⁻¹) * β⁻¹))] at hstep
  refine hstep.trans (le_of_eq ?_)
  unfold gmFieldLipConst
  field_simp

/-- The Lipschitz constant of the quadratic remainder. -/
noncomputable def wassRLipConst (α β : ℝ) : ℝ :=
  α⁻¹ + 2 * β * (α⁻¹ * α⁻¹)
    + (β * β * α⁻¹) * (gmFieldLipConst α β * gmFieldLipConst α β)

lemma wassRLipConst_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 ≤ wassRLipConst α β := by
  have h := gmFieldLipConst_nonneg hα hβ
  unfold wassRLipConst
  positivity

/-- **The quadratic remainder is Lipschitz with a modulus proportional to the distance from
the base point.** -/
theorem norm_wassG_remainder_sub_le {X Y₁ Y₂ : A} (hX : IsStrictlyPositive X)
    (hY₁ : IsStrictlyPositive Y₁) (hY₂ : IsStrictlyPositive Y₂)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hXα : α • (1 : A) ≤ X) (hXβ : X ≤ β • (1 : A))
    (hY₁α : α • (1 : A) ≤ Y₁) (hY₁β : Y₁ ≤ β • (1 : A))
    (hY₂α : α • (1 : A) ≤ Y₂) (hY₂β : Y₂ ≤ β • (1 : A)) :
    ‖(wassG Y₁ X - (Y₁ - X)) - (wassG Y₂ X - (Y₂ - X))‖
      ≤ wassRLipConst α β * ((‖Y₁ - X‖ + ‖Y₂ - X‖) * ‖Y₁ - Y₂‖) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hαi : (0 : ℝ) ≤ α⁻¹ := (inv_pos.mpr hα).le
  have hXn : ‖X‖ ≤ β := norm_le_of_le_smul_one hX.nonneg hβ.le hXβ
  have hY₁n : ‖Y₁‖ ≤ β := norm_le_of_le_smul_one hY₁.nonneg hβ.le hY₁β
  have hY₂n : ‖Y₂‖ ≤ β := norm_le_of_le_smul_one hY₂.nonneg hβ.le hY₂β
  have hXi : ‖(X⁻¹ʳ : A)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hX hα hXα
  have h1i : ‖(Y₁⁻¹ʳ : A)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hY₁ hα hY₁α
  have h2i : ‖(Y₂⁻¹ʳ : A)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hY₂ hα hY₂α
  have hd1 : ‖Y₁ - X‖ ≤ 2 * β := by
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hd2 : ‖Y₂ - X‖ ≤ 2 * β := by
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hd1n : (0 : ℝ) ≤ ‖Y₁ - X‖ := norm_nonneg _
  have hd2n : (0 : ℝ) ≤ ‖Y₂ - X‖ := norm_nonneg _
  have hΔ : (0 : ℝ) ≤ ‖Y₁ - Y₂‖ := norm_nonneg _
  have hinvn : ‖(Y₁⁻¹ʳ : A) - Y₂⁻¹ʳ‖ ≤ (α⁻¹ * α⁻¹) * ‖Y₁ - Y₂‖ :=
    norm_ringInverse_sub_le_of_smul_one_le hY₁ hY₂ hα hY₁α hY₂α
  have hL : (0 : ℝ) ≤ gmFieldLipConst α β := gmFieldLipConst_nonneg hα hβ
  have hN1 : ‖(1 : A) - gm X Y₁⁻¹ʳ‖ ≤ gmFieldLipConst α β * ‖Y₁ - X‖ := by
    have h := norm_one_sub_gm_le hX hY₁ hα hαβ hXα hXβ hY₁α hY₁β
    rwa [show ‖X - Y₁‖ = ‖Y₁ - X‖ by rw [← norm_neg (X - Y₁), neg_sub]] at h
  have hN2 : ‖(1 : A) - gm X Y₂⁻¹ʳ‖ ≤ gmFieldLipConst α β * ‖Y₂ - X‖ := by
    have h := norm_one_sub_gm_le hX hY₂ hα hαβ hXα hXβ hY₂α hY₂β
    rwa [show ‖X - Y₂‖ = ‖Y₂ - X‖ by rw [← norm_neg (X - Y₂), neg_sub]] at h
  have hNd : ‖((1 : A) - gm X Y₁⁻¹ʳ) - ((1 : A) - gm X Y₂⁻¹ʳ)‖
      ≤ gmFieldLipConst α β * ‖Y₁ - Y₂‖ := by
    have hid : ((1 : A) - gm X Y₁⁻¹ʳ) - ((1 : A) - gm X Y₂⁻¹ʳ)
        = -(gm X Y₁⁻¹ʳ - gm X Y₂⁻¹ʳ) := by abel
    rw [hid, norm_neg]
    exact norm_gm_sub_gm_le hX hY₁ hY₂ hα hαβ hXα hXβ hY₁α hY₁β hY₂α hY₂β
  -- the two telescoping pieces
  have hsplit : (wassG Y₁ X - (Y₁ - X)) - (wassG Y₂ X - (Y₂ - X))
      = -((Y₁ - X) * (Y₁⁻¹ʳ : A) * (Y₁ - X) - (Y₂ - X) * (Y₂⁻¹ʳ : A) * (Y₂ - X))
        + (X * ((1 : A) - gm X Y₁⁻¹ʳ) * X⁻¹ʳ * ((1 : A) - gm X Y₁⁻¹ʳ) * X
          - X * ((1 : A) - gm X Y₂⁻¹ʳ) * X⁻¹ʳ * ((1 : A) - gm X Y₂⁻¹ʳ) * X) := by
    rw [wassG_sub_eq hX hY₁, wassG_sub_eq hX hY₂]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  -- first piece
  have hT1 : ‖-((Y₁ - X) * (Y₁⁻¹ʳ : A) * (Y₁ - X) - (Y₂ - X) * (Y₂⁻¹ʳ : A) * (Y₂ - X))‖
      ≤ (α⁻¹ + 2 * β * (α⁻¹ * α⁻¹)) * ((‖Y₁ - X‖ + ‖Y₂ - X‖) * ‖Y₁ - Y₂‖) := by
    rw [norm_neg, sandwich_sub_telescope]
    have hab : ((Y₁ - X) - (Y₂ - X)) = Y₁ - Y₂ := by abel
    have e1 : ‖((Y₁ - X) - (Y₂ - X)) * (Y₁⁻¹ʳ : A) * (Y₁ - X)‖
        ≤ ‖Y₁ - Y₂‖ * α⁻¹ * ‖Y₁ - X‖ := by
      rw [hab]
      refine le_trans (norm_mul_le _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine le_trans (norm_mul_le _ _) ?_
      exact mul_le_mul_of_nonneg_left h1i (norm_nonneg _)
    have e2 : ‖(Y₂ - X) * ((Y₁⁻¹ʳ : A) - Y₂⁻¹ʳ) * (Y₁ - X)‖
        ≤ ‖Y₂ - X‖ * ((α⁻¹ * α⁻¹) * ‖Y₁ - Y₂‖) * ‖Y₁ - X‖ := by
      refine le_trans (norm_mul_le _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine le_trans (norm_mul_le _ _) ?_
      exact mul_le_mul_of_nonneg_left hinvn (norm_nonneg _)
    have e3 : ‖(Y₂ - X) * (Y₂⁻¹ʳ : A) * ((Y₁ - X) - (Y₂ - X))‖
        ≤ ‖Y₂ - X‖ * α⁻¹ * ‖Y₁ - Y₂‖ := by
      rw [hab]
      refine le_trans (norm_mul_le _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine le_trans (norm_mul_le _ _) ?_
      exact mul_le_mul_of_nonneg_left h2i (norm_nonneg _)
    refine le_trans (norm_add₃_le) ?_
    have hsum := add_le_add (add_le_add e1 e2) e3
    refine hsum.trans ?_
    have hkey : ‖Y₂ - X‖ * ((α⁻¹ * α⁻¹) * ‖Y₁ - Y₂‖) * ‖Y₁ - X‖
        ≤ (2 * β * (α⁻¹ * α⁻¹)) * ((‖Y₁ - X‖ + ‖Y₂ - X‖) * ‖Y₁ - Y₂‖) := by
      have h1 : ‖Y₂ - X‖ * ((α⁻¹ * α⁻¹) * ‖Y₁ - Y₂‖) * ‖Y₁ - X‖
          = (α⁻¹ * α⁻¹) * (‖Y₁ - X‖ * ‖Y₂ - X‖) * ‖Y₁ - Y₂‖ := by ring
      have h2 : (2 * β * (α⁻¹ * α⁻¹)) * ((‖Y₁ - X‖ + ‖Y₂ - X‖) * ‖Y₁ - Y₂‖)
          = (α⁻¹ * α⁻¹) * (2 * β * (‖Y₁ - X‖ + ‖Y₂ - X‖)) * ‖Y₁ - Y₂‖ := by ring
      rw [h1, h2]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hΔ
      nlinarith [hd1, hd2n, hd1n]
    have hrest : ‖Y₁ - Y₂‖ * α⁻¹ * ‖Y₁ - X‖ + ‖Y₂ - X‖ * α⁻¹ * ‖Y₁ - Y₂‖
        = α⁻¹ * ((‖Y₁ - X‖ + ‖Y₂ - X‖) * ‖Y₁ - Y₂‖) := by ring
    linarith [hkey, hrest]
  -- second piece
  have hT2 : ‖X * ((1 : A) - gm X Y₁⁻¹ʳ) * X⁻¹ʳ * ((1 : A) - gm X Y₁⁻¹ʳ) * X
        - X * ((1 : A) - gm X Y₂⁻¹ʳ) * X⁻¹ʳ * ((1 : A) - gm X Y₂⁻¹ʳ) * X‖
      ≤ ((β * β * α⁻¹) * (gmFieldLipConst α β * gmFieldLipConst α β))
        * ((‖Y₁ - X‖ + ‖Y₂ - X‖) * ‖Y₁ - Y₂‖) := by
    rw [quintuple_sub_telescope]
    have hchain : ∀ p q r : A, ‖X * p * (X⁻¹ʳ : A) * q * X‖
        ≤ ‖X‖ * ‖p‖ * ‖(X⁻¹ʳ : A)‖ * ‖q‖ * ‖X‖ := by
      intro p q r
      refine le_trans (norm_mul_le _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine le_trans (norm_mul_le _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine le_trans (norm_mul_le _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact norm_mul_le _ _
    have f1 := hchain (((1 : A) - gm X Y₁⁻¹ʳ) - ((1 : A) - gm X Y₂⁻¹ʳ))
      ((1 : A) - gm X Y₁⁻¹ʳ) 0
    have f2 := hchain ((1 : A) - gm X Y₂⁻¹ʳ)
      (((1 : A) - gm X Y₁⁻¹ʳ) - ((1 : A) - gm X Y₂⁻¹ʳ)) 0
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add f1 f2) ?_
    have g1 := mul5_le hXn hNd hXi hN1 hXn (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) hβ.le (mul_nonneg hL hΔ) hαi (mul_nonneg hL hd1n)
    have g2 := mul5_le hXn hN2 hXi hNd hXn (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) hβ.le (mul_nonneg hL hd2n) hαi (mul_nonneg hL hΔ)
    refine le_trans (add_le_add g1 g2) (le_of_eq ?_)
    ring
  refine le_trans (add_le_add hT1 hT2) (le_of_eq ?_)
  unfold wassRLipConst
  ring

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
