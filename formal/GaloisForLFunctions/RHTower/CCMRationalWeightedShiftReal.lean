import GaloisForLFunctions.RHTower.CCMRationalHilbertOperatorRealStructure

/-!
# Real-equivariant weighted shifts for rational CCM monomials

A bounded rational CCM monomial acts on the actual Morita Hilbert fiber as a weighted left
shift. This file constructs that bounded operator and proves that quaternionic operator
conjugation is exactly the rational source coefficient twist.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

def ccmRationalMoritaHilbertLeftScaleFunction
    (k : CCMRationalUnit) (f : CCMRationalMoritaHilbert)
    (q : CCMRationalUnit) : ℂ :=
  f (k⁻¹ * q)

theorem ccmRationalMoritaHilbertLeftScaleFunction_memℓp
    (k : CCMRationalUnit) (f : CCMRationalMoritaHilbert) :
    Memℓp (ccmRationalMoritaHilbertLeftScaleFunction k f) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hf := (lp.memℓp f).summable (by norm_num)
  have ht :=
    (Equiv.mulLeft k⁻¹).summable_iff.mpr (by simpa using hf)
  exact ht.congr (fun q => by
    dsimp only [Function.comp_apply,
      ccmRationalMoritaHilbertLeftScaleFunction]
    norm_num)

def ccmRationalMoritaHilbertLeftScale
    (k : CCMRationalUnit) (f : CCMRationalMoritaHilbert) :
    CCMRationalMoritaHilbert :=
  ⟨ccmRationalMoritaHilbertLeftScaleFunction k f,
    ccmRationalMoritaHilbertLeftScaleFunction_memℓp k f⟩

@[simp]
theorem ccmRationalMoritaHilbertLeftScale_apply
    (k : CCMRationalUnit) (f : CCMRationalMoritaHilbert)
    (q : CCMRationalUnit) :
    ccmRationalMoritaHilbertLeftScale k f q = f (k⁻¹ * q) :=
  rfl

theorem ccmRationalMoritaHilbertLeftScale_add
    (k : CCMRationalUnit) (f g : CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertLeftScale k (f + g) =
      ccmRationalMoritaHilbertLeftScale k f +
        ccmRationalMoritaHilbertLeftScale k g := by
  ext q
  rfl

theorem ccmRationalMoritaHilbertLeftScale_smul
    (k : CCMRationalUnit) (z : ℂ) (f : CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertLeftScale k (z • f) =
      z • ccmRationalMoritaHilbertLeftScale k f := by
  ext q
  rfl

theorem ccmRationalMoritaHilbertLeftScale_norm
    (k : CCMRationalUnit) (f : CCMRationalMoritaHilbert) :
    ‖ccmRationalMoritaHilbertLeftScale k f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num),
    lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  simpa [ccmRationalMoritaHilbertLeftScale_apply] using
    ((Equiv.mulLeft k⁻¹).tsum_eq
      (fun q : CCMRationalUnit => ‖f q‖ ^ (2 : ℕ)))

def ccmRationalMoritaHilbertLeftScaleIsometry
    (k : CCMRationalUnit) :
    CCMRationalMoritaHilbert ≃ₗᵢ[ℂ] CCMRationalMoritaHilbert where
  toFun := ccmRationalMoritaHilbertLeftScale k
  invFun := ccmRationalMoritaHilbertLeftScale k⁻¹
  left_inv f := by
    ext q
    simp [ccmRationalMoritaHilbertLeftScale_apply]
  right_inv f := by
    ext q
    simp [ccmRationalMoritaHilbertLeftScale_apply]
  map_add' := ccmRationalMoritaHilbertLeftScale_add k
  map_smul' := ccmRationalMoritaHilbertLeftScale_smul k
  norm_map' := ccmRationalMoritaHilbertLeftScale_norm k

def ccmRationalMoritaWeightedShiftFunction
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (f : CCMRationalMoritaHilbert) (q : CCMRationalUnit) : ℂ :=
  a q * f (k⁻¹ * q)

theorem ccmRationalMoritaWeightedShiftFunction_memℓp
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (f : CCMRationalMoritaHilbert) :
    Memℓp (ccmRationalMoritaWeightedShiftFunction a k f) 2 := by
  have hg :
      Memℓp (fun q : CCMRationalUnit =>
        (C : ℂ) * ccmRationalMoritaHilbertLeftScale k f q) 2 := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (lp.memℓp ((C : ℂ) • ccmRationalMoritaHilbertLeftScale k f))
  apply hg.mono'
  intro q
  simp only [ccmRationalMoritaWeightedShiftFunction,
    ccmRationalMoritaHilbertLeftScale_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((ha q).trans_eq (by simp [abs_of_nonneg hC]))
    (norm_nonneg _)

def ccmRationalMoritaWeightedShiftVector
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (f : CCMRationalMoritaHilbert) : CCMRationalMoritaHilbert :=
  ⟨ccmRationalMoritaWeightedShiftFunction a k f,
    ccmRationalMoritaWeightedShiftFunction_memℓp a k C hC ha f⟩

@[simp]
theorem ccmRationalMoritaWeightedShiftVector_apply
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (f : CCMRationalMoritaHilbert) (q : CCMRationalUnit) :
    ccmRationalMoritaWeightedShiftVector a k C hC ha f q =
      a q * f (k⁻¹ * q) :=
  rfl

def ccmRationalMoritaWeightedShiftLinearMap
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C) :
    CCMRationalMoritaHilbert →ₗ[ℂ] CCMRationalMoritaHilbert where
  toFun := ccmRationalMoritaWeightedShiftVector a k C hC ha
  map_add' f g := by
    ext q
    change a q * (f (k⁻¹ * q) + g (k⁻¹ * q)) =
      a q * f (k⁻¹ * q) + a q * g (k⁻¹ * q)
    rw [mul_add]
  map_smul' z f := by
    ext q
    change a q * (z * f (k⁻¹ * q)) =
      z * (a q * f (k⁻¹ * q))
    ring

def ccmRationalMoritaWeightedShift
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C) :
    CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert :=
  (ccmRationalMoritaWeightedShiftLinearMap a k C hC ha).mkContinuous C fun f => by
    calc
      ‖ccmRationalMoritaWeightedShiftLinearMap a k C hC ha f‖ ≤
          ‖(C : ℂ) • ccmRationalMoritaHilbertLeftScale k f‖ := by
        apply lp.norm_mono (by norm_num)
        intro q
        change ‖ccmRationalMoritaWeightedShiftVector
            a k C hC ha f q‖ ≤
          ‖((C : ℂ) • ccmRationalMoritaHilbertLeftScale k f) q‖
        rw [ccmRationalMoritaWeightedShiftVector_apply]
        change ‖a q * f (k⁻¹ * q)‖ ≤
          ‖(C : ℂ) * f (k⁻¹ * q)‖
        rw [norm_mul, norm_mul]
        have hnormC : ‖(C : ℂ)‖ = C := by
          simp [abs_of_nonneg hC]
        rw [hnormC]
        exact mul_le_mul_of_nonneg_right
          (ha q) (norm_nonneg _)
      _ = C * ‖f‖ := by
        rw [norm_smul, ccmRationalMoritaHilbertLeftScale_norm]
        simp [abs_of_nonneg hC]

@[simp]
theorem ccmRationalMoritaWeightedShift_apply
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (f : CCMRationalMoritaHilbert) (q : CCMRationalUnit) :
    ccmRationalMoritaWeightedShift a k C hC ha f q =
      a q * f (k⁻¹ * q) :=
  rfl

theorem ccmRationalMoritaWeightedShift_norm_le
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C) :
    ‖ccmRationalMoritaWeightedShift a k C hC ha‖ ≤ C := by
  unfold ccmRationalMoritaWeightedShift
  apply LinearMap.mkContinuous_norm_le _ hC

def ccmRationalMoritaCoefficientRealTwist
    (k : CCMRationalUnit) (a : CCMRationalUnit → ℂ)
    (q : CCMRationalUnit) : ℂ :=
  ccmRationalUnitSign k * star (a (-q))

theorem ccmRationalMoritaCoefficientRealTwist_bound
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (ha : ∀ q, ‖a q‖ ≤ C) :
    ∀ q, ‖ccmRationalMoritaCoefficientRealTwist k a q‖ ≤ C := by
  intro q
  simpa [ccmRationalMoritaCoefficientRealTwist, norm_mul,
    ccmRationalUnitSign_norm] using ha (-q)

theorem ccmRationalMoritaWeightedShift_real_equivariant
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C) :
    ccmRationalMoritaHilbertOperatorRealStructure
        (ccmRationalMoritaWeightedShift a k C hC ha) =
      ccmRationalMoritaWeightedShift
        (ccmRationalMoritaCoefficientRealTwist k a) k C hC
        (ccmRationalMoritaCoefficientRealTwist_bound a k C ha) := by
  apply ContinuousLinearMap.ext
  intro f
  ext q
  rw [ccmRationalMoritaHilbertOperatorRealStructure_apply]
  change -(ccmRationalUnitSign q *
      star (a (-q) *
        (ccmRationalUnitSign (k⁻¹ * -q) *
          star (f (-(k⁻¹ * -q)))))) =
    ccmRationalUnitSign k * star (a (-q)) * f (k⁻¹ * q)
  rw [star_mul, star_mul, ccmRationalUnitSign_star, star_star]
  rw [show -(k⁻¹ * -q) = k⁻¹ * q by simp]
  rw [ccmRationalUnitSign_mul, ccmRationalUnitSign_inv,
    ccmRationalUnitSign_neg]
  calc
    -(ccmRationalUnitSign q *
      (f (k⁻¹ * q) *
        (ccmRationalUnitSign k * -ccmRationalUnitSign q) *
          star (a (-q)))) =
      (ccmRationalUnitSign q * ccmRationalUnitSign q) *
        (ccmRationalUnitSign k * star (a (-q)) *
          f (k⁻¹ * q)) := by ring
    _ = ccmRationalUnitSign k * star (a (-q)) *
        f (k⁻¹ * q) := by
      rw [ccmRationalUnitSign_sq, one_mul]

end RHTower
end GaloisForLFunctions
