import GaloisForLFunctions.HTGeometry.RectangularTraceNorm

open scoped ENNReal

namespace RHTower

noncomputable section

variable {ι : Type}
variable {K : ι → Type*}
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, NormedSpace ℂ (K i)]

abbrev ScalarEllTwo (ι : Type*) := lp (fun _ : ι => ℂ) 2
theorem vectorDiagonal_memℓp (X : ∀ i, K i) {C : ℝ} (hC : 0 ≤ C)
    (hX : ∀ i, ‖X i‖ ≤ C) (x : ScalarEllTwo ι) :
    Memℓp (fun i => x i • X i) 2 := by
  refine memℓp_gen ?_
  have hx : Summable fun i => ‖(x : ∀ i, ℂ) i‖ ^ (2 : ℝ) :=
    (lp.memℓp x).summable (by norm_num)
  refine Summable.of_nonneg_of_le
    (fun i => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hx.mul_left (C ^ (2 : ℝ)))
  intro i
  rw [norm_smul]
  have hle : ‖(x : ∀ i, ℂ) i‖ * ‖X i‖ ≤
      C * ‖(x : ∀ i, ℂ) i‖ := by
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hX i) (norm_nonneg ((x : ∀ i, ℂ) i))
  calc
    (‖(x : ∀ i, ℂ) i‖ * ‖X i‖) ^ (2 : ℝ) ≤
        (C * ‖(x : ∀ i, ℂ) i‖) ^ (2 : ℝ) :=
      Real.rpow_le_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hle (by norm_num)
    _ = C ^ (2 : ℝ) * ‖(x : ∀ i, ℂ) i‖ ^ (2 : ℝ) :=
      Real.mul_rpow hC (norm_nonneg _)

def vectorDiagonalLinear (X : ∀ i, K i) {C : ℝ} (hC : 0 ≤ C)
    (hX : ∀ i, ‖X i‖ ≤ C) : ScalarEllTwo ι →ₗ[ℂ] lp K 2 where
  toFun x := ⟨fun i => x i • X i, vectorDiagonal_memℓp X hC hX x⟩
  map_add' x y := by ext i; simp [add_smul]
  map_smul' c x := by
    ext i
    change (c * x i) • X i = c • (x i • X i)
    exact (smul_smul c (x i) (X i)).symm

@[simp] theorem vectorDiagonalLinear_apply (X : ∀ i, K i) {C : ℝ}
    (hC : 0 ≤ C) (hX : ∀ i, ‖X i‖ ≤ C) (x : ScalarEllTwo ι) (i : ι) :
    vectorDiagonalLinear X hC hX x i = x i • X i := rfl

theorem vectorDiagonalLinear_norm_le (X : ∀ i, K i) {C : ℝ}
    (hC : 0 ≤ C) (hX : ∀ i, ‖X i‖ ≤ C) (x : ScalarEllTwo ι) :
    ‖vectorDiagonalLinear X hC hX x‖ ≤ C * ‖x‖ := by
  have hleft : 0 ≤ ‖vectorDiagonalLinear X hC hX x‖ := norm_nonneg _
  have hright : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  have hy : ‖vectorDiagonalLinear X hC hX x‖ ^ (2 : ℝ) =
      ∑' i, ‖(vectorDiagonalLinear X hC hX x : ∀ i, K i) i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := K) (by norm_num)
      (vectorDiagonalLinear X hC hX x)
  have hxnorm : ‖x‖ ^ (2 : ℝ) =
      ∑' i, ‖(x : ∀ i, ℂ) i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ι => ℂ)
      (by norm_num) x
  have hxsum : Summable fun i => ‖(x : ∀ i, ℂ) i‖ ^ (2 : ℝ) :=
    (lp.memℓp x).summable (by norm_num)
  have hysum : Summable fun i =>
      ‖(vectorDiagonalLinear X hC hX x : ∀ i, K i) i‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ i,
      ‖(vectorDiagonalLinear X hC hX x : ∀ i, K i) i‖ ^ (2 : ℝ) ≤
        C ^ (2 : ℝ) * ‖(x : ∀ i, ℂ) i‖ ^ (2 : ℝ) := by
    intro i
    rw [vectorDiagonalLinear_apply, norm_smul]
    have hle : ‖(x : ∀ i, ℂ) i‖ * ‖X i‖ ≤
        C * ‖(x : ∀ i, ℂ) i‖ := by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hX i) (norm_nonneg ((x : ∀ i, ℂ) i))
    calc
      (‖(x : ∀ i, ℂ) i‖ * ‖X i‖) ^ (2 : ℝ) ≤
          (C * ‖(x : ∀ i, ℂ) i‖) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hle (by norm_num)
      _ = C ^ (2 : ℝ) * ‖(x : ∀ i, ℂ) i‖ ^ (2 : ℝ) :=
        Real.mul_rpow hC (norm_nonneg _)
  have hpow : ‖vectorDiagonalLinear X hC hX x‖ ^ (2 : ℝ) ≤
      (C * ‖x‖) ^ (2 : ℝ) := by
    rw [hy, Real.mul_rpow hC (norm_nonneg _), hxnorm, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hysum
      (hxsum.mul_left (C ^ (2 : ℝ)))
  have hleft2 : ‖vectorDiagonalLinear X hC hX x‖ ^ (2 : ℝ) =
      ‖vectorDiagonalLinear X hC hX x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hright2 : (C * ‖x‖) ^ (2 : ℝ) =
      (C * ‖x‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hleft2, hright2] at hpow
  have hsqrt := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

noncomputable def vectorDiagonalOperator (X : ∀ i, K i) {C : ℝ}
    (hC : 0 ≤ C) (hX : ∀ i, ‖X i‖ ≤ C) :
    ScalarEllTwo ι →L[ℂ] lp K 2 :=
  LinearMap.mkContinuous (vectorDiagonalLinear X hC hX) C
    (vectorDiagonalLinear_norm_le X hC hX)

@[simp] theorem vectorDiagonalOperator_apply (X : ∀ i, K i) {C : ℝ}
    (hC : 0 ≤ C) (hX : ∀ i, ‖X i‖ ≤ C)
    (x : ScalarEllTwo ι) (i : ι) :
    vectorDiagonalOperator X hC hX x i = x i • X i := rfl

theorem vectorDiagonalOperator_single (X : ∀ i, K i) {C : ℝ}
    [DecidableEq ι]
    (hC : 0 ≤ C) (hX : ∀ i, ‖X i‖ ≤ C) (i : ι) (c : ℂ) :
    vectorDiagonalOperator X hC hX (lp.single 2 i c) =
      lp.single 2 i (c • X i) := by
  ext j
  rw [vectorDiagonalOperator_apply, lp.single_apply, lp.single_apply]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

theorem vectorDiagonalOperator_deningerIsNuclear_of_summable_norm
    [DecidableEq ι] (X : ∀ i, K i) {C : ℝ} (hC : 0 ≤ C) (hX : ∀ i, ‖X i‖ ≤ C)
    (hsum : Summable fun i => ‖X i‖) :
    DeningerIsNuclear (vectorDiagonalOperator X hC hX) := by
  let phi : ι → (ScalarEllTwo ι →L[ℂ] ℂ) := fun i =>
    lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i
  let y : ι → lp K 2 := fun i => lp.single 2 i (X i)
  refine ⟨ι, phi, y, ?_, ?_⟩
  · apply hsum.of_nonneg_of_le
    · intro i
      positivity
    · intro i
      have hphi : ‖phi i‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
        intro x
        change ‖x i‖ ≤ 1 * ‖x‖
        simpa using
          (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x i)
      have hy : ‖y i‖ = ‖X i‖ := by
        exact lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2) i (X i)
      rw [hy]
      calc
        ‖phi i‖ * ‖X i‖ ≤ 1 * ‖X i‖ :=
          mul_le_mul_of_nonneg_right hphi (norm_nonneg _)
        _ = ‖X i‖ := one_mul _
  · intro x
    have hsingle := lp.hasSum_single (E := K) (p := 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (vectorDiagonalOperator X hC hX x)
    convert hsingle using 1
    funext i
    change x i • lp.single 2 i (X i) = lp.single 2 i (x i • X i)
    exact (lp.single_smul 2 i (x i) (X i)).symm

end

section Hilbert

variable {ι : Type} [DecidableEq ι]
variable {K : ι → Type*}
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
variable [∀ i, CompleteSpace (K i)]

theorem vectorDiagonalOperator_memRectSchattenClass_one_of_summable_norm
    (X : ∀ i, K i) {C : ℝ} (hC : 0 ≤ C) (hX : ∀ i, ‖X i‖ ≤ C)
    (hsum : Summable fun i => ‖X i‖) :
    MemRectSchattenClass 1 (vectorDiagonalOperator X hC hX) :=
  (vectorDiagonalOperator_deningerIsNuclear_of_summable_norm X hC hX hsum).memRectSchattenClass_one

end Hilbert

end RHTower
