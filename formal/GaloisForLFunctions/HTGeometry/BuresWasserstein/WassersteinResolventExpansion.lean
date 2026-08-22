import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFlowInvariance
import GaloisForLFunctions.HTGeometry.LyapunovInverseBounds

/-!
# The normalized resolvent increment and its quadratic expansion

For `X, Y` in a Loewner interval put `N(Y,X) := 1 - (X # Y⁻¹)` and

`G(Y,X) := X N(Y,X) + N(Y,X) X`.

The Riccati equation for the geometric mean gives the **exact** identity

`G(Y,X) = (Y - X) - (Y - X) Y⁻¹ (Y - X) + X N X⁻¹ N X`,

so `G(Y,X) - (Y - X)` is a sum of two explicitly quadratic terms.  No Fréchet derivative, no
Taylor formula with integral remainder, and no second differential bound is needed: the
remainder is written down.  Dividing by the Lyapunov operator then shows that `N(Y,X)` agrees
with the solution `W` of `X W + W X = Y - X` up to a quadratic error, which is the content of the
first-order expansion of `Y ↦ 1 - (X # Y⁻¹)`.
-/

open scoped NNReal Ring BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The Riccati form of the difference of two geometric means.** -/
theorem gm_sub_riccati {a b c : A} (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (hc : IsStrictlyPositive c) :
    gm a b * a⁻¹ʳ * (gm a b - gm a c) + (gm a b - gm a c) * (a⁻¹ʳ * gm a c) = b - c := by
  have h1 := gm_riccati ha hb
  have h2 := gm_riccati ha hc
  have hexp : gm a b * a⁻¹ʳ * (gm a b - gm a c) + (gm a b - gm a c) * (a⁻¹ʳ * gm a c)
      = gm a b * a⁻¹ʳ * gm a b - gm a c * a⁻¹ʳ * gm a c := by noncomm_ring
  rw [hexp, h1, h2]

/-- The **normalized resolvent increment** `G(Y,X) = X(1 - X # Y⁻¹) + (1 - X # Y⁻¹)X`. -/
noncomputable def wassG (Y X : A) : A :=
  X * (1 - gm X Y⁻¹ʳ) + (1 - gm X Y⁻¹ʳ) * X

/-- **The exact quadratic expansion of the normalized resolvent increment.** -/
theorem wassG_sub_eq {X Y : A} (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y) :
    wassG Y X - (Y - X)
      = -((Y - X) * Y⁻¹ʳ * (Y - X))
        + X * (1 - gm X Y⁻¹ʳ) * X⁻¹ʳ * (1 - gm X Y⁻¹ʳ) * X := by
  have hinvX : X * (X⁻¹ʳ : A) = 1 := Ring.mul_inverse_cancel _ hX.isUnit
  have hinvX' : (X⁻¹ʳ : A) * X = 1 := Ring.inverse_mul_cancel _ hX.isUnit
  have hinvY : Y * (Y⁻¹ʳ : A) = 1 := Ring.mul_inverse_cancel _ hY.isUnit
  have hkey := gm_sub_riccati hX hX.ringInverse hY.ringInverse
  rw [gm_ringInverse_self' hX] at hkey
  -- `hkey : 1 * X⁻¹ * (1 - M) + (1 - M) * (X⁻¹ * M) = X⁻¹ - Y⁻¹`
  have hkey2 : (X⁻¹ʳ : A) * (1 - gm X Y⁻¹ʳ) + (1 - gm X Y⁻¹ʳ) * X⁻¹ʳ
      - (1 - gm X Y⁻¹ʳ) * X⁻¹ʳ * (1 - gm X Y⁻¹ʳ) = (X⁻¹ʳ : A) - Y⁻¹ʳ := by
    rw [← hkey]; noncomm_ring
  have hmul : X * ((X⁻¹ʳ : A) * (1 - gm X Y⁻¹ʳ) + (1 - gm X Y⁻¹ʳ) * X⁻¹ʳ
        - (1 - gm X Y⁻¹ʳ) * X⁻¹ʳ * (1 - gm X Y⁻¹ʳ)) * X
      = X * ((X⁻¹ʳ : A) - Y⁻¹ʳ) * X := by rw [hkey2]
  have hL : X * ((X⁻¹ʳ : A) * (1 - gm X Y⁻¹ʳ) + (1 - gm X Y⁻¹ʳ) * X⁻¹ʳ
        - (1 - gm X Y⁻¹ʳ) * X⁻¹ʳ * (1 - gm X Y⁻¹ʳ)) * X
      = (1 - gm X Y⁻¹ʳ) * X + X * (1 - gm X Y⁻¹ʳ)
        - X * (1 - gm X Y⁻¹ʳ) * X⁻¹ʳ * (1 - gm X Y⁻¹ʳ) * X := by
    have e : X * ((X⁻¹ʳ : A) * (1 - gm X Y⁻¹ʳ) + (1 - gm X Y⁻¹ʳ) * X⁻¹ʳ
          - (1 - gm X Y⁻¹ʳ) * X⁻¹ʳ * (1 - gm X Y⁻¹ʳ)) * X
        = (X * X⁻¹ʳ) * ((1 - gm X Y⁻¹ʳ) * X)
          + (X * (1 - gm X Y⁻¹ʳ)) * ((X⁻¹ʳ : A) * X)
          - X * (1 - gm X Y⁻¹ʳ) * X⁻¹ʳ * (1 - gm X Y⁻¹ʳ) * X := by noncomm_ring
    rw [e, hinvX, hinvX', one_mul, mul_one]
  have hR : X * ((X⁻¹ʳ : A) - Y⁻¹ʳ) * X = X - X * Y⁻¹ʳ * X := by
    have e : X * ((X⁻¹ʳ : A) - Y⁻¹ʳ) * X = (X * X⁻¹ʳ) * X - X * Y⁻¹ʳ * X := by noncomm_ring
    rw [e, hinvX, one_mul]
  rw [hL, hR] at hmul
  have hquad : (Y - X) * (Y⁻¹ʳ : A) * (Y - X) = Y - X - X + X * Y⁻¹ʳ * X := by
    have e : (Y - X) * (Y⁻¹ʳ : A) * (Y - X)
        = (Y * Y⁻¹ʳ) * Y - (Y * Y⁻¹ʳ) * X - X * Y⁻¹ʳ * Y + X * Y⁻¹ʳ * X := by noncomm_ring
    rw [e, hinvY]
    have e2 : X * (Y⁻¹ʳ : A) * Y = X * (Y⁻¹ʳ * Y) := by noncomm_ring
    rw [e2, Ring.inverse_mul_cancel _ hY.isUnit, mul_one]
    noncomm_ring
  unfold wassG
  rw [hquad]
  linear_combination (norm := noncomm_ring) hmul

/-! ### The quadratic bound -/

omit [StarOrderedRing A] in
lemma smul_one_le_smul_one_of_le [StarOrderedRing A] {c d : ℝ} (h : c ≤ d) :
    c • (1 : A) ≤ d • (1 : A) := by
  rw [← sub_nonneg, ← sub_smul]
  exact smul_nonneg (by linarith) zero_le_one

/-- The Lipschitz constant of `Y ↦ 1 - (X # Y⁻¹)` on a Loewner interval. -/
noncomputable def gmFieldLipConst (α β : ℝ) : ℝ :=
  β * α⁻¹ * (α⁻¹ * α⁻¹) / (2 * (Real.sqrt (α * β⁻¹) * β⁻¹))

lemma gmFieldLipConst_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 ≤ gmFieldLipConst α β := by
  have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  unfold gmFieldLipConst
  positivity

/-- `1 - (X # Y⁻¹)` is Lipschitz in `Y` on a Loewner interval, and vanishes at `Y = X`. -/
theorem norm_one_sub_gm_le {X Y : A} (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hXα : α • (1 : A) ≤ X) (hXβ : X ≤ β • (1 : A))
    (hYα : α • (1 : A) ≤ Y) (hYβ : Y ≤ β • (1 : A)) :
    ‖(1 : A) - gm X Y⁻¹ʳ‖ ≤ gmFieldLipConst α β * ‖X - Y‖ := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hβinv : (0 : ℝ) < β⁻¹ := inv_pos.mpr hβ
  have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  have hγ1 : Real.sqrt (α * β⁻¹) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    refine Real.sqrt_le_sqrt ?_
    rw [← div_eq_mul_inv, div_le_one hβ]
    exact hαβ
  have hgb : (Real.sqrt (α * β⁻¹)) • (1 : A) ≤ gm X X⁻¹ʳ := by
    rw [gm_ringInverse_self' hX]
    have h := smul_one_le_smul_one_of_le (A := A) hγ1
    rwa [one_smul] at h
  have hgc : (Real.sqrt (α * β⁻¹)) • (1 : A) ≤ gm X Y⁻¹ʳ :=
    smul_one_le_gm hX hY.ringInverse hα hβinv hXα
      (smul_one_le_ringInverse_of_le_smul_one hY hβ hYβ)
  have hgmi := norm_gm_sub_le_of_Icc hX hX.ringInverse hY.ringInverse hα hγ hβ hXα hXβ hgb hgc
  rw [gm_ringInverse_self' hX] at hgmi
  have hinvn : ‖(X⁻¹ʳ : A) - Y⁻¹ʳ‖ ≤ (α⁻¹ * α⁻¹) * ‖X - Y‖ :=
    norm_ringInverse_sub_le_of_smul_one_le hX hY hα hXα hYα
  have hstep : (2 * (Real.sqrt (α * β⁻¹) * β⁻¹)) * ‖(1 : A) - gm X Y⁻¹ʳ‖
      ≤ (β * α⁻¹) * ((α⁻¹ * α⁻¹) * ‖X - Y‖) :=
    hgmi.trans (mul_le_mul_of_nonneg_left hinvn (by positivity))
  rw [← le_div_iff₀' (by positivity : (0:ℝ) < 2 * (Real.sqrt (α * β⁻¹) * β⁻¹))] at hstep
  refine hstep.trans (le_of_eq ?_)
  unfold gmFieldLipConst
  field_simp

/-- The constant in the quadratic expansion of the normalized resolvent increment. -/
noncomputable def wassGConst (α β : ℝ) : ℝ :=
  α⁻¹ + (β * β * α⁻¹) * (gmFieldLipConst α β * gmFieldLipConst α β)

lemma wassGConst_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 ≤ wassGConst α β := by
  have h := gmFieldLipConst_nonneg hα hβ
  unfold wassGConst
  positivity

/-- **Lemma 4.10 (Kim–Mer–Pálfia).**  The normalized resolvent increment agrees with `Y - X` up
to a quadratic error. -/
theorem norm_wassG_sub_le {X Y : A} (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hXα : α • (1 : A) ≤ X) (hXβ : X ≤ β • (1 : A))
    (hYα : α • (1 : A) ≤ Y) (hYβ : Y ≤ β • (1 : A)) :
    ‖wassG Y X - (Y - X)‖ ≤ wassGConst α β * (‖Y - X‖ * ‖Y - X‖) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hXY : ‖X - Y‖ = ‖Y - X‖ := by rw [← norm_neg (X - Y), neg_sub]
  have hYinv : ‖(Y⁻¹ʳ : A)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hY hα hYα
  have hXinv : ‖(X⁻¹ʳ : A)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hX hα hXα
  have hXn : ‖X‖ ≤ β := norm_le_of_le_smul_one hX.nonneg hβ.le hXβ
  have hN : ‖(1 : A) - gm X Y⁻¹ʳ‖ ≤ gmFieldLipConst α β * ‖Y - X‖ := by
    have h := norm_one_sub_gm_le hX hY hα hαβ hXα hXβ hYα hYβ
    rwa [hXY] at h
  have hNnn : (0 : ℝ) ≤ gmFieldLipConst α β := gmFieldLipConst_nonneg hα hβ
  rw [wassG_sub_eq hX hY]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖-((Y - X) * (Y⁻¹ʳ : A) * (Y - X))‖ ≤ α⁻¹ * (‖Y - X‖ * ‖Y - X‖) := by
    rw [norm_neg]
    calc ‖(Y - X) * (Y⁻¹ʳ : A) * (Y - X)‖
        ≤ ‖(Y - X) * (Y⁻¹ʳ : A)‖ * ‖Y - X‖ := norm_mul_le _ _
      _ ≤ (‖Y - X‖ * ‖(Y⁻¹ʳ : A)‖) * ‖Y - X‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (‖Y - X‖ * α⁻¹) * ‖Y - X‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hYinv (norm_nonneg _)) (norm_nonneg _)
      _ = α⁻¹ * (‖Y - X‖ * ‖Y - X‖) := by ring
  have h2 : ‖X * ((1 : A) - gm X Y⁻¹ʳ) * X⁻¹ʳ * ((1 : A) - gm X Y⁻¹ʳ) * X‖
      ≤ (β * β * α⁻¹) * (gmFieldLipConst α β * gmFieldLipConst α β) * (‖Y - X‖ * ‖Y - X‖) := by
    have hchain : ‖X * ((1 : A) - gm X Y⁻¹ʳ) * X⁻¹ʳ * ((1 : A) - gm X Y⁻¹ʳ) * X‖
        ≤ ‖X‖ * ‖(1 : A) - gm X Y⁻¹ʳ‖ * ‖(X⁻¹ʳ : A)‖ * ‖(1 : A) - gm X Y⁻¹ʳ‖ * ‖X‖ := by
      refine le_trans (norm_mul_le _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine le_trans (norm_mul_le _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine le_trans (norm_mul_le _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact norm_mul_le _ _
    refine hchain.trans ?_
    have hd : (0 : ℝ) ≤ ‖Y - X‖ := norm_nonneg _
    have hαi : (0 : ℝ) ≤ α⁻¹ := (inv_pos.mpr hα).le
    have hLd : (0 : ℝ) ≤ gmFieldLipConst α β * ‖Y - X‖ := mul_nonneg hNnn hd
    have e1 : ‖X‖ * ‖(1 : A) - gm X Y⁻¹ʳ‖ ≤ β * (gmFieldLipConst α β * ‖Y - X‖) :=
      mul_le_mul hXn hN (norm_nonneg _) hβ.le
    have e2 : (‖X‖ * ‖(1 : A) - gm X Y⁻¹ʳ‖) * ‖(X⁻¹ʳ : A)‖
        ≤ (β * (gmFieldLipConst α β * ‖Y - X‖)) * α⁻¹ :=
      mul_le_mul e1 hXinv (norm_nonneg _) (mul_nonneg hβ.le hLd)
    have e3 : ((‖X‖ * ‖(1 : A) - gm X Y⁻¹ʳ‖) * ‖(X⁻¹ʳ : A)‖) * ‖(1 : A) - gm X Y⁻¹ʳ‖
        ≤ ((β * (gmFieldLipConst α β * ‖Y - X‖)) * α⁻¹)
          * (gmFieldLipConst α β * ‖Y - X‖) :=
      mul_le_mul e2 hN (norm_nonneg _) (mul_nonneg (mul_nonneg hβ.le hLd) hαi)
    have e4 : (((‖X‖ * ‖(1 : A) - gm X Y⁻¹ʳ‖) * ‖(X⁻¹ʳ : A)‖)
          * ‖(1 : A) - gm X Y⁻¹ʳ‖) * ‖X‖
        ≤ (((β * (gmFieldLipConst α β * ‖Y - X‖)) * α⁻¹)
          * (gmFieldLipConst α β * ‖Y - X‖)) * β :=
      mul_le_mul e3 hXn (norm_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg hβ.le hLd) hαi) hLd)
    refine e4.trans (le_of_eq ?_)
    ring
  have := add_le_add h1 h2
  refine this.trans (le_of_eq ?_)
  unfold wassGConst
  ring

/-! ### The first-order expansion -/

/-- **Lemma 4.9 (Kim–Mer–Pálfia).**  `1 - (X # Y⁻¹)` agrees, up to a quadratic error, with the
solution `W` of the Lyapunov equation `X W + W X = Y - X`, which is the value at `Y - X` of the
derivative of `Y ↦ 1 - (X # Y⁻¹)` at `Y = X`. -/
theorem norm_one_sub_gm_sub_lyapunov_le {X Y W : A} (hX : IsStrictlyPositive X)
    (hY : IsStrictlyPositive Y) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hXα : α • (1 : A) ≤ X) (hXβ : X ≤ β • (1 : A))
    (hYα : α • (1 : A) ≤ Y) (hYβ : Y ≤ β • (1 : A))
    (hW : X * W + W * X = Y - X) :
    (2 * α) * ‖((1 : A) - gm X Y⁻¹ʳ) - W‖ ≤ wassGConst α β * (‖Y - X‖ * ‖Y - X‖) := by
  have heq : X * (((1 : A) - gm X Y⁻¹ʳ) - W) + (((1 : A) - gm X Y⁻¹ʳ) - W) * X
      = wassG Y X - (Y - X) := by
    unfold wassG
    rw [← hW]
    noncomm_ring
  have hlyap := norm_le_of_lyapunov hX.isSelfAdjoint hα hXα heq
  exact hlyap.trans (norm_wassG_sub_le hX hY hα hαβ hXα hXβ hYα hYβ)

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
