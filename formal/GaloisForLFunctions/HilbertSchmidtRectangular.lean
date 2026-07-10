/-
# Rectangular Hilbert--Schmidt kernels

The square-kernel API is insufficient for column operators: their source and target bases have
different index types.  This file supplies the corresponding rectangular bridge
`K : κ × ι → ℂ ↔ ℓ²(ι) → ℓ²(κ)`, with exact preservation of Hilbert--Schmidt energy.
-/
import GaloisForLFunctions.HilbertSchmidtMatrix

open scoped BigOperators

namespace HilbertSchmidt

variable {κ ι : Type*}

/-- Square-summability for a rectangular matrix. -/
def IsHSRect (K : κ × ι → ℂ) : Prop := Summable (fun p => ‖K p‖ ^ 2)

/-- Squared Hilbert--Schmidt norm of a rectangular matrix. -/
noncomputable def hsNormSqRect (K : κ × ι → ℂ) : ℝ := ∑' p, ‖K p‖ ^ 2

theorem hsNormSqRect_nonneg (K : κ × ι → ℂ) : 0 ≤ hsNormSqRect K :=
  tsum_nonneg fun _ => sq_nonneg _

/-- Each row of a rectangular Hilbert--Schmidt matrix is square-summable. -/
theorem isHSRect_row {K : κ × ι → ℂ} (hK : IsHSRect K) (r : κ) :
    Summable (fun j => ‖K (r, j)‖ ^ 2) := by
  exact hK.comp_injective fun a b h => (Prod.ext_iff.mp h).2

/-- The row energies of a rectangular Hilbert--Schmidt matrix are summable. -/
theorem summable_rect_row {K : κ × ι → ℂ} (hK : IsHSRect K) :
    Summable (fun r => ∑' j, ‖K (r, j)‖ ^ 2) := by
  have h := hK
  change Summable (fun p : κ × ι => ‖K p‖ ^ 2) at h
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)] at h
  exact h.2

theorem tsum_rect_row_normSq {K : κ × ι → ℂ} (hK : IsHSRect K) :
    ∑' r, ∑' j, ‖K (r, j)‖ ^ 2 = hsNormSqRect K := by
  exact hK.tsum_prod.symm

/-- Transpose of a rectangular matrix. -/
def rectTranspose (K : κ × ι → ℂ) : ι × κ → ℂ := fun p => K (p.2, p.1)

theorem isHSRect_transpose {K : κ × ι → ℂ} (hK : IsHSRect K) :
    IsHSRect (rectTranspose K) := by
  have hre : (fun p : ι × κ => ‖rectTranspose K p‖ ^ 2) =
      (fun p : κ × ι => ‖K p‖ ^ 2) ∘ (Equiv.prodComm ι κ) := by
    funext p
    rfl
  rw [IsHSRect, hre]
  exact (Equiv.prodComm ι κ).summable_iff.mpr hK

/-- Each column of a rectangular Hilbert--Schmidt matrix is square-summable. -/
theorem isHSRect_col {K : κ × ι → ℂ} (hK : IsHSRect K) (j : ι) :
    Summable (fun r => ‖K (r, j)‖ ^ 2) := by
  simpa [rectTranspose] using isHSRect_row (isHSRect_transpose hK) j

/-- The column energies of a rectangular Hilbert--Schmidt matrix are summable. -/
theorem summable_rect_col {K : κ × ι → ℂ} (hK : IsHSRect K) :
    Summable (fun j => ∑' r, ‖K (r, j)‖ ^ 2) := by
  simpa [rectTranspose] using summable_rect_row (isHSRect_transpose hK)

theorem tsum_rect_col_normSq {K : κ × ι → ℂ} (hK : IsHSRect K) :
    ∑' j, ∑' r, ‖K (r, j)‖ ^ 2 = hsNormSqRect K := by
  calc
    ∑' j, ∑' r, ‖K (r, j)‖ ^ 2 =
        ∑' p : ι × κ, ‖rectTranspose K p‖ ^ 2 :=
      (isHSRect_transpose hK).tsum_prod.symm
    _ = ∑' p : κ × ι, ‖K p‖ ^ 2 :=
      (Equiv.prodComm ι κ).tsum_eq (fun p : κ × ι => ‖K p‖ ^ 2)
    _ = hsNormSqRect K := rfl

/-- Row action of a rectangular Hilbert--Schmidt matrix on an `ℓ²` vector converges. -/
theorem summable_rect_row_mul {K : κ × ι → ℂ} (hK : IsHSRect K)
    (f : lp (fun _ : ι => ℂ) 2) (r : κ) :
    Summable fun j => K (r, j) * f j := by
  apply Summable.of_norm_bounded (g := fun j => (‖K (r, j)‖ ^ 2 + ‖f j‖ ^ 2) / 2)
  · exact ((isHSRect_row hK r).add (summable_coe_sq f)).div_const 2
  · intro j
    rw [norm_mul]
    nlinarith [sq_nonneg (‖K (r, j)‖ - ‖f j‖), norm_nonneg (K (r, j)), norm_nonneg (f j)]

private theorem memℓp_rectMulVec {K : κ × ι → ℂ} (hK : IsHSRect K)
    (f : lp (fun _ : ι => ℂ) 2) :
    Memℓp (fun r => ∑' j, K (r, j) * f j) 2 := by
  refine memℓp_of_sq ?_
  refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_)
    ((summable_rect_row hK).mul_right (‖f‖ ^ 2))
  calc
    ‖∑' j, K (r, j) * f j‖ ^ 2
        ≤ (∑' j, ‖K (r, j)‖ ^ 2) * (∑' j, ‖f j‖ ^ 2) :=
      hsComp_entry_bound (isHSRect_row hK r) (summable_coe_sq f)
    _ = (∑' j, ‖K (r, j)‖ ^ 2) * ‖f‖ ^ 2 := by rw [lp_norm_sq_eq]

/-- Hilbert--Schmidt norm of a rectangular matrix. -/
noncomputable def hsNormRect (K : κ × ι → ℂ) : ℝ := Real.sqrt (hsNormSqRect K)

private theorem norm_rectMulVec_le {K : κ × ι → ℂ} (hK : IsHSRect K)
    (f : lp (fun _ : ι => ℂ) 2) :
    ‖(⟨fun r => ∑' j, K (r, j) * f j, memℓp_rectMulVec hK f⟩ :
        lp (fun _ : κ => ℂ) 2)‖ ≤ hsNormRect K * ‖f‖ := by
  set g : lp (fun _ : κ => ℂ) 2 :=
    ⟨fun r => ∑' j, K (r, j) * f j, memℓp_rectMulVec hK f⟩ with hg
  have hgsq : ‖g‖ ^ 2 ≤ hsNormSqRect K * ‖f‖ ^ 2 := by
    rw [lp_norm_sq_eq g]
    calc
      ∑' r, ‖g r‖ ^ 2
          ≤ ∑' r, (∑' j, ‖K (r, j)‖ ^ 2) * ‖f‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun r => ?_) (summable_coe_sq g)
          ((summable_rect_row hK).mul_right (‖f‖ ^ 2))
        calc
          ‖g r‖ ^ 2 = ‖∑' j, K (r, j) * f j‖ ^ 2 := rfl
          _ ≤ (∑' j, ‖K (r, j)‖ ^ 2) * (∑' j, ‖f j‖ ^ 2) :=
            hsComp_entry_bound (isHSRect_row hK r) (summable_coe_sq f)
          _ = (∑' j, ‖K (r, j)‖ ^ 2) * ‖f‖ ^ 2 := by rw [lp_norm_sq_eq]
      _ = (∑' r, ∑' j, ‖K (r, j)‖ ^ 2) * ‖f‖ ^ 2 := tsum_mul_right
      _ = hsNormSqRect K * ‖f‖ ^ 2 := by rw [tsum_rect_row_normSq hK]
  have hroot := Real.sqrt_le_sqrt hgsq
  rw [Real.sqrt_sq (norm_nonneg g)] at hroot
  calc
    ‖g‖ ≤ Real.sqrt (hsNormSqRect K * ‖f‖ ^ 2) := hroot
    _ = Real.sqrt (hsNormSqRect K) * Real.sqrt (‖f‖ ^ 2) :=
      Real.sqrt_mul (hsNormSqRect_nonneg K) _
    _ = hsNormRect K * ‖f‖ := by
      rw [Real.sqrt_sq (norm_nonneg f), hsNormRect]

/-- The operator `ℓ²(ι) → ℓ²(κ)` represented by a rectangular Hilbert--Schmidt matrix. -/
noncomputable def toOperatorRect {K : κ × ι → ℂ} (hK : IsHSRect K) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : κ => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun r => ∑' j, K (r, j) * f j, memℓp_rectMulVec hK f⟩
      map_add' := fun f g => by
        apply lp.ext
        funext r
        show ∑' j, K (r, j) * (f + g) j =
          (∑' j, K (r, j) * f j) + ∑' j, K (r, j) * g j
        rw [← (summable_rect_row_mul hK f r).tsum_add (summable_rect_row_mul hK g r)]
        refine tsum_congr fun j => ?_
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        apply lp.ext
        funext r
        show ∑' j, K (r, j) * (c • f) j = c • ∑' j, K (r, j) * f j
        rw [smul_eq_mul, ← tsum_mul_left]
        refine tsum_congr fun j => ?_
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    (hsNormRect K)
    (fun f => norm_rectMulVec_le hK f)

theorem toOperatorRect_apply {K : κ × ι → ℂ} (hK : IsHSRect K)
    (f : lp (fun _ : ι => ℂ) 2) (r : κ) :
    toOperatorRect hK f r = ∑' j, K (r, j) * f j := rfl

theorem toOperatorRect_single [DecidableEq ι] {K : κ × ι → ℂ} (hK : IsHSRect K)
    (r : κ) (j : ι) :
    toOperatorRect hK (lp.single 2 j (1 : ℂ)) r = K (r, j) := by
  rw [toOperatorRect_apply,
    tsum_eq_single j (fun j' hj' => by rw [lp.single_apply_ne _ _ _ hj', mul_zero])]
  rw [lp.single_apply_self, mul_one]

theorem norm_toOperatorRect_single_sq [DecidableEq ι] {K : κ × ι → ℂ}
    (hK : IsHSRect K) (j : ι) :
    ‖toOperatorRect hK (lp.single 2 j (1 : ℂ))‖ ^ 2 =
      ∑' r, ‖K (r, j)‖ ^ 2 := by
  rw [lp_norm_sq_eq]
  exact tsum_congr fun r => by rw [toOperatorRect_single hK r j]

/-- A rectangular Hilbert--Schmidt matrix represents an actual Hilbert--Schmidt operator. -/
theorem isHilbertSchmidt_toOperatorRect {K : κ × ι → ℂ} (hK : IsHSRect K) :
    (toOperatorRect hK).IsHilbertSchmidt := by
  classical
  refine ContinuousLinearMap.isHilbertSchmidt_of_summable (lpBasis ι) ?_
  refine (summable_rect_col hK).congr fun j => ?_
  rw [lpBasis_apply, norm_toOperatorRect_single_sq hK]

/-- Exact preservation of Hilbert--Schmidt energy by the rectangular kernel bridge. -/
theorem hsNormSq_toOperatorRect {K : κ × ι → ℂ} (hK : IsHSRect K) :
    ContinuousLinearMap.hsNormSq (toOperatorRect hK) = hsNormSqRect K := by
  classical
  rw [ContinuousLinearMap.hsNormSq_eq (isHilbertSchmidt_toOperatorRect hK) (lpBasis ι),
    ← tsum_rect_col_normSq hK]
  exact tsum_congr fun j => by rw [lpBasis_apply, norm_toOperatorRect_single_sq hK]

end HilbertSchmidt
