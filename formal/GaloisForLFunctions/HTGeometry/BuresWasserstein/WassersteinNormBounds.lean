import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinBounds

/-!
# Operator-norm bounds for the Wasserstein barycentre

Kim–Mer–Pálfia (arXiv:2607.29142), Theorem 6.5, sharpen the Loewner bounds of Theorem 6.2 to

`‖∑ wᵢ √Aᵢ‖² ≤ ‖X‖ ≤ (∑ wᵢ ‖Aᵢ‖^{1/2})²`

for any Wasserstein point `X` of the family.  The upper bound is the triangle inequality plus
submultiplicativity; the lower bound comes from the scaling argument: rescaling the family so that
`X ≤ 1` forces `∑ wᵢ √Aᵢ = ∑ wᵢ (Aᵢ # 1) ≤ ∑ wᵢ (Aᵢ # X⁻¹) = 1`.
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A} {X : A}

/-! ### Norm and square-root bookkeeping -/

theorem norm_cfcSqrt_mul_self {T : A} (hT : 0 ≤ T) :
    ‖CFC.sqrt T‖ * ‖CFC.sqrt T‖ = ‖T‖ := by
  rw [← CStarRing.norm_star_mul_self, (CFC.sqrt_nonneg T).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self T hT]

theorem norm_cfcSqrt {T : A} (hT : 0 ≤ T) : ‖CFC.sqrt T‖ = Real.sqrt ‖T‖ := by
  rw [← norm_cfcSqrt_mul_self hT, Real.sqrt_mul_self (norm_nonneg _)]

theorem cfcSqrt_smul {r : ℝ} (hr : 0 ≤ r) {a : A} (ha : 0 ≤ a) :
    CFC.sqrt (r • a) = Real.sqrt r • CFC.sqrt a := by
  refine CFC.sqrt_unique ?_ (smul_nonneg (Real.sqrt_nonneg r) (CFC.sqrt_nonneg a))
  rw [smul_mul_smul_comm, CFC.sqrt_mul_sqrt_self a ha, Real.mul_self_sqrt hr]

theorem le_smul_one_norm {a : A} (ha : 0 ≤ a) : a ≤ ‖a‖ • (1 : A) := by
  have h := ha.isSelfAdjoint.le_algebraMap_norm_self
  rwa [Algebra.algebraMap_eq_smul_one] at h

theorem norm_le_of_le_smul_one {a : A} (ha : 0 ≤ a) {r : ℝ} (hr : 0 ≤ r)
    (h : a ≤ r • (1 : A)) : ‖a‖ ≤ r := by
  rw [CStarAlgebra.norm_le_iff_le_algebraMap a hr ha, Algebra.algebraMap_eq_smul_one]
  exact h

/-! ### Theorem 6.5: the upper norm bound -/

/-- `‖X‖ ≤ (∑ wᵢ ‖Aᵢ‖^{1/2})²`. -/
theorem IsWassersteinPoint.norm_le (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (h : IsWassersteinPoint s w Av X) :
    ‖X‖ ≤ (∑ i ∈ s, w i * Real.sqrt ‖Av i‖) * ∑ i ∈ s, w i * Real.sqrt ‖Av i‖ := by
  have hX : IsStrictlyPositive X := h.1
  have hprimal := (isWassersteinPoint_iff_sqrt hX hA).mp h
  have hKnn : 0 ≤ ∑ i ∈ s, w i * Real.sqrt ‖Av i‖ :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.sqrt_nonneg _)
  have hXhalf : ‖X ^ (1/2 : ℝ)‖ = Real.sqrt ‖X‖ := by
    rw [← CFC.sqrt_eq_rpow, norm_cfcSqrt hX.nonneg]
  have hterm : ∀ i ∈ s, ‖CFC.sqrt (X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ))‖
      ≤ Real.sqrt ‖X‖ * Real.sqrt ‖Av i‖ := by
    intro i hi
    have hnn : (0 : A) ≤ X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ) :=
      nonneg_conjugate (isSelfAdjoint_rpow X _) (hA i hi).nonneg
    rw [norm_cfcSqrt hnn, ← Real.sqrt_mul (norm_nonneg X)]
    refine Real.sqrt_le_sqrt ?_
    calc ‖X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ)‖
        ≤ ‖X ^ (1/2 : ℝ) * Av i‖ * ‖X ^ (1/2 : ℝ)‖ := norm_mul_le _ _
      _ ≤ ‖X ^ (1/2 : ℝ)‖ * ‖Av i‖ * ‖X ^ (1/2 : ℝ)‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖X‖ * ‖Av i‖ := by
          rw [hXhalf]
          rw [show Real.sqrt ‖X‖ * ‖Av i‖ * Real.sqrt ‖X‖
            = (Real.sqrt ‖X‖ * Real.sqrt ‖X‖) * ‖Av i‖ by ring,
            Real.mul_self_sqrt (norm_nonneg X)]
  have hmain : ‖X‖ ≤ Real.sqrt ‖X‖ * ∑ i ∈ s, w i * Real.sqrt ‖Av i‖ := by
    calc ‖X‖ = ‖∑ i ∈ s, w i • CFC.sqrt (X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ))‖ := by
          rw [hprimal]
      _ ≤ ∑ i ∈ s, ‖w i • CFC.sqrt (X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, w i * (Real.sqrt ‖X‖ * Real.sqrt ‖Av i‖) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
          exact mul_le_mul_of_nonneg_left (hterm i hi) (hw i hi)
      _ = Real.sqrt ‖X‖ * ∑ i ∈ s, w i * Real.sqrt ‖Av i‖ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  rcases eq_or_lt_of_le (Real.sqrt_nonneg ‖X‖) with hc | hc
  · have : ‖X‖ = 0 := by
      rw [← Real.mul_self_sqrt (norm_nonneg X), ← hc, mul_zero]
    rw [this]
    positivity
  · have hle : Real.sqrt ‖X‖ ≤ ∑ i ∈ s, w i * Real.sqrt ‖Av i‖ := by
      by_contra hcon
      have hgt : (∑ i ∈ s, w i * Real.sqrt ‖Av i‖) < Real.sqrt ‖X‖ := not_le.mp hcon
      have hlt := lt_of_le_of_lt hmain (mul_lt_mul_of_pos_left hgt hc)
      rw [Real.mul_self_sqrt (norm_nonneg X)] at hlt
      exact lt_irrefl _ hlt
    calc ‖X‖ = Real.sqrt ‖X‖ * Real.sqrt ‖X‖ := (Real.mul_self_sqrt (norm_nonneg X)).symm
      _ ≤ (∑ i ∈ s, w i * Real.sqrt ‖Av i‖) * ∑ i ∈ s, w i * Real.sqrt ‖Av i‖ :=
          mul_le_mul hle hle (Real.sqrt_nonneg _) hKnn

/-! ### Theorem 6.5: the lower norm bound -/

/-- `‖∑ wᵢ √Aᵢ‖² ≤ ‖X‖`. -/
theorem IsWassersteinPoint.norm_sqrtMean_le (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (h : IsWassersteinPoint s w Av X) :
    ‖∑ i ∈ s, w i • CFC.sqrt (Av i)‖ * ‖∑ i ∈ s, w i • CFC.sqrt (Av i)‖ ≤ ‖X‖ := by
  have hX : IsStrictlyPositive X := h.1
  have hQnn : (0 : A) ≤ ∑ i ∈ s, w i • CFC.sqrt (Av i) :=
    Finset.sum_nonneg fun i hi => smul_nonneg (hw i hi) (CFC.sqrt_nonneg _)
  rcases eq_or_lt_of_le (norm_nonneg X) with hc | hc
  · -- `‖X‖ = 0` forces the algebra to be trivial
    have hX0 : X = 0 := norm_eq_zero.mp hc.symm
    have hsub : Subsingleton A := by
      rcases subsingleton_or_nontrivial A with hsub | _
      · exact hsub
      · exact absurd (hX0 ▸ hX.isUnit) not_isUnit_zero
    simp [Subsingleton.elim (∑ i ∈ s, w i • CFC.sqrt (Av i)) 0, ← hc]
  · set c := ‖X‖ with hcdef
    have hr : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
    have hrX : IsWassersteinPoint s w (fun i => c⁻¹ • Av i) (c⁻¹ • X) :=
      (isWassersteinPoint_smul hr hX hA).mpr h
    have hle : c⁻¹ • X ≤ (1 : A) := by
      have h1 : c⁻¹ • X ≤ c⁻¹ • (c • (1 : A)) :=
        smul_le_smul_of_nonneg_left (le_smul_one_norm hX.nonneg) hr.le
      rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h1
    have hrXpos : IsStrictlyPositive (c⁻¹ • X) := hX.smul hr
    have hinv : (1 : A) ≤ (c⁻¹ • X)⁻¹ʳ := by
      have hcmp := CStarAlgebra.ringInverse_le_ringInverse hle hrXpos
      rwa [Ring.inverse_one] at hcmp
    have hstep : ∀ i ∈ s, w i • CFC.sqrt (c⁻¹ • Av i)
        ≤ w i • gm (c⁻¹ • Av i) (c⁻¹ • X)⁻¹ʳ := by
      intro i hi
      refine smul_le_smul_of_nonneg_left ?_ (hw i hi)
      rw [← gm_one_right ((hA i hi).smul hr)]
      exact gm_mono_right _ hinv
    have hsum : Real.sqrt c⁻¹ • (∑ i ∈ s, w i • CFC.sqrt (Av i)) ≤ 1 := by
      have hrewrite : Real.sqrt c⁻¹ • (∑ i ∈ s, w i • CFC.sqrt (Av i))
          = ∑ i ∈ s, w i • CFC.sqrt (c⁻¹ • Av i) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [cfcSqrt_smul hr.le (hA i hi).nonneg, smul_comm]
      rw [hrewrite, ← hrX.2]
      exact Finset.sum_le_sum hstep
    have hsq : (0 : ℝ) < Real.sqrt c⁻¹ := Real.sqrt_pos.mpr hr
    have hQle : (∑ i ∈ s, w i • CFC.sqrt (Av i)) ≤ Real.sqrt c • (1 : A) := by
      have h2 := smul_le_smul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hsq))
      rw [smul_smul, inv_mul_cancel₀ hsq.ne', one_smul, Real.sqrt_inv, inv_inv] at h2
      exact h2
    have hQnorm : ‖∑ i ∈ s, w i • CFC.sqrt (Av i)‖ ≤ Real.sqrt c :=
      norm_le_of_le_smul_one hQnn (Real.sqrt_nonneg c) hQle
    calc ‖∑ i ∈ s, w i • CFC.sqrt (Av i)‖ * ‖∑ i ∈ s, w i • CFC.sqrt (Av i)‖
        ≤ Real.sqrt c * Real.sqrt c :=
          mul_le_mul hQnorm hQnorm (norm_nonneg _) (Real.sqrt_nonneg c)
      _ = c := Real.mul_self_sqrt hc.le

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
