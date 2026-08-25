import GaloisForLFunctions.HTGeometry.HardyDiskSpace
import GaloisForLFunctions.HTGeometry.HardyBoundaryValues
import GaloisForLFunctions.HTGeometry.HardySpace
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert

/-!
# Exact `H²(D)` boundary realization

This module packages one-sided square-summable Taylor coefficients as their literal
`L²(circleLebesgue)` Riesz--Fischer boundary.  The map is a linear isometry; no boundary-value
hypothesis is built into the construction.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology
open scoped ENNReal NNReal lp

noncomputable section

private def natSumNatEquivInt : ℕ ⊕ ℕ ≃ ℤ where
  toFun
    | Sum.inl n => Int.ofNat n
    | Sum.inr n => Int.negSucc n
  invFun
    | Int.ofNat n => Sum.inl n
    | Int.negSucc n => Sum.inr n
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

/-- Zero-extension from analytic Taylor modes to all integer Fourier modes preserves norm. -/
theorem norm_nonnegativeIntExtension (c : lp (fun _ : ℕ => ℂ) 2) :
    ‖(⟨nonnegativeIntExtension c,
        nonnegativeIntExtension_memℓp_two c (lp.memℓp c)⟩ :
          lp (fun _ : ℤ => ℂ) 2)‖ = ‖c‖ := by
  have hNat : Summable (fun n : ℕ => ‖c n‖ ^ 2) := by
    have hc := lp.memℓp c
    rw [memℓp_gen_iff (by norm_num)] at hc
    simpa using hc
  have hleft : Summable (fun x : ℕ =>
      ‖nonnegativeIntExtension c (natSumNatEquivInt (Sum.inl x))‖ ^ 2) := by
    simpa [natSumNatEquivInt] using hNat
  have hright : Summable (fun x : ℕ =>
      ‖nonnegativeIntExtension c (natSumNatEquivInt (Sum.inr x))‖ ^ 2) := by
    simpa [natSumNatEquivInt] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  let g : ℕ ⊕ ℕ → ℝ := fun x =>
    ‖nonnegativeIntExtension c (natSumNatEquivInt x)‖ ^ 2
  have hsplit : (∑' x, g x) =
      (∑' n : ℕ, g (Sum.inl n)) + ∑' n : ℕ, g (Sum.inr n) := by
    apply Summable.tsum_sum (f := g)
    · change Summable (fun x : ℕ =>
        ‖nonnegativeIntExtension c (natSumNatEquivInt (Sum.inl x))‖ ^ 2)
      exact hleft
    · change Summable (fun x : ℕ =>
        ‖nonnegativeIntExtension c (natSumNatEquivInt (Sum.inr x))‖ ^ 2)
      exact hright
  have hsq :
      ‖(⟨nonnegativeIntExtension c,
          nonnegativeIntExtension_memℓp_two c (lp.memℓp c)⟩ :
            lp (fun _ : ℤ => ℂ) 2)‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [lp_two_norm_sq_eq_tsum, lp_two_norm_sq_eq_tsum]
    rw [← natSumNatEquivInt.tsum_eq]
    change (∑' x, g x) = _
    rw [hsplit]
    simp [g, natSumNatEquivInt]
  rw [← Real.sqrt_sq (norm_nonneg
      (⟨nonnegativeIntExtension c,
        nonnegativeIntExtension_memℓp_two c (lp.memℓp c)⟩ :
          lp (fun _ : ℤ => ℂ) 2)),
    ← Real.sqrt_sq (norm_nonneg c), hsq]

/-- Isometric zero-extension from analytic Taylor modes to integer Fourier modes. -/
def nonnegativeIntExtensionLinearIsometry :
    lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun c := ⟨nonnegativeIntExtension c,
    nonnegativeIntExtension_memℓp_two c (lp.memℓp c)⟩
  map_add' := by
    intro c d
    apply lp.ext
    funext k
    cases k with
    | ofNat n => simp
    | negSucc n => simp
  map_smul' := by
    intro a c
    apply lp.ext
    funext k
    cases k with
    | ofNat n => simp
    | negSucc n => simp
  norm_map' := norm_nonnegativeIntExtension

@[simp] theorem nonnegativeIntExtensionLinearIsometry_apply
    (c : lp (fun _ : ℕ => ℂ) 2) (k : ℤ) :
    nonnegativeIntExtensionLinearIsometry c k = nonnegativeIntExtension c k := rfl

/-- Exact Riesz--Fischer boundary map from coefficient Hardy space to circle `L²`. -/
def hardyDiskBoundary : HardyDisk →ₗᵢ[ℂ] Lp ℂ 2 circleLebesgue :=
  circleLpAddCircleLinearIsometryEquiv.symm.toLinearIsometry.comp
    (fourierBasis.repr.symm.toLinearIsometry.comp nonnegativeIntExtensionLinearIsometry)

theorem hardyDiskBoundary_apply (f : HardyDisk) :
    hardyDiskBoundary f = circleRieszFischerOfNat f (lp.memℓp f) := rfl

theorem circleMonomialLp_inner_hardyDiskBoundary (f : HardyDisk) (n : ℕ) :
    inner ℂ (circleMonomialLp circleLebesgue n) (hardyDiskBoundary f) = f n := by
  rw [hardyDiskBoundary_apply]
  exact circleMonomialLp_inner_circleRieszFischerOfNat f (lp.memℓp f) n

/-! ## Canonical Abel radii and strong radial boundary convergence -/

/-- A fixed cofinal sequence of radii in `[0,1)`. -/
def hardyDiskAbelRadius (n : ℕ) : ℝ :=
  1 - 1 / ((n : ℝ) + 1)

theorem hardyDiskAbelRadius_nonneg (n : ℕ) : 0 ≤ hardyDiskAbelRadius n := by
  rw [hardyDiskAbelRadius]
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  have hinv : 1 / ((n : ℝ) + 1) ≤ 1 := by
    exact (div_le_one (by positivity)).2 hden
  linarith

theorem hardyDiskAbelRadius_lt_one (n : ℕ) : hardyDiskAbelRadius n < 1 := by
  rw [hardyDiskAbelRadius]
  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem tendsto_hardyDiskAbelRadius :
    Tendsto hardyDiskAbelRadius atTop (𝓝[<] (1 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    convert hone.sub hzero using 1
    · funext x
      simp [hardyDiskAbelRadius, one_div]
    · simp
  · exact Eventually.of_forall (fun n => hardyDiskAbelRadius_lt_one n)

/-- The radial coefficient synthesis at the canonical `n`th Abel radius. -/
def hardyDiskRadialBoundary (n : ℕ) (f : HardyDisk) :
    Lp ℂ 2 circleLebesgue :=
  circleLpAddCircleLinearIsometryEquiv.symm
    (fourierBasis.repr.symm
      (⟨fun k => radialMult (hardyDiskAbelRadius n) k *
          nonnegativeIntExtensionLinearIsometry f k,
        memLp_mul_of_bounded (a := nonnegativeIntExtensionLinearIsometry f)
          (norm_radialMult_le_one (hardyDiskAbelRadius_nonneg n)
            (hardyDiskAbelRadius_lt_one n).le)⟩ : lp (fun _ : ℤ => ℂ) 2))

/-- Exact Parseval defect between a radial synthesis and its boundary vector. -/
theorem norm_sub_hardyDiskRadialBoundary_sq (n : ℕ) (f : HardyDisk) :
    ‖hardyDiskRadialBoundary n f - hardyDiskBoundary f‖ ^ 2 =
      ∑' k : ℤ, ‖(radialMult (hardyDiskAbelRadius n) k - 1) *
        nonnegativeIntExtension f k‖ ^ 2 := by
  let a : lp (fun _ : ℤ => ℂ) 2 := nonnegativeIntExtensionLinearIsometry f
  let ar : lp (fun _ : ℤ => ℂ) 2 :=
    ⟨fun k => radialMult (hardyDiskAbelRadius n) k * a k,
      memLp_mul_of_bounded (a := a)
        (norm_radialMult_le_one (hardyDiskAbelRadius_nonneg n)
          (hardyDiskAbelRadius_lt_one n).le)⟩
  change ‖circleLpAddCircleLinearIsometryEquiv.symm (fourierBasis.repr.symm ar) -
      circleLpAddCircleLinearIsometryEquiv.symm (fourierBasis.repr.symm a)‖ ^ 2 = _
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  simpa [a, ar] using hardy_boundary_L2_eq a
    (hardyDiskAbelRadius_nonneg n) (hardyDiskAbelRadius_lt_one n).le

/-- Canonical radial syntheses converge strongly to the exact circle boundary vector. -/
theorem tendsto_hardyDiskRadialBoundary (f : HardyDisk) :
    Tendsto (fun n => hardyDiskRadialBoundary n f) atTop
      (𝓝 (hardyDiskBoundary f)) := by
  have hdefect := (tendsto_radial_defect
    (nonnegativeIntExtensionLinearIsometry f) (by
      intro k hk
      cases k with
      | ofNat n => exact (not_lt_of_ge (by simp) hk).elim
      | negSucc n => simp)).comp tendsto_hardyDiskAbelRadius
  have hsq : Tendsto
      (fun n => ‖hardyDiskRadialBoundary n f - hardyDiskBoundary f‖ ^ 2)
      atTop (𝓝 0) := by
    convert hdefect using 1
    · funext n
      exact norm_sub_hardyDiskRadialBoundary_sq n f
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  convert hsqrt using 1
  · funext n
    rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg
      (hardyDiskRadialBoundary n f - hardyDiskBoundary f))]
  · simp

end

end GaloisForLFunctions.HTGeometry
