import GaloisForLFunctions.RHTower.BurnolSoninProjectedEvaluationTransport

/-!
# Burnol bilateral aperture two-evaluator kernel

This module upgrades the diagonal bilateral defect-energy law to its exact polarized kernel.
It uses the concrete continuous Mellin evaluation vectors and actual extended-Sonine projection;
no abstract evaluator or spectral hypothesis is assumed.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Exact two-evaluator kernel of the finite bilateral extended-Sonine holonomy. -/
theorem burnolExtended_bilateralApertureHolonomy_kernel
    {w v : ℂ}
    (hwlo : 1 / 2 < w.re) (hwhi : w.re < 1)
    (hvlo : 1 / 2 < v.re) (hvhi : v.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    let b : ℝ := r⁻¹ * a
    let hb : 0 < b := mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha
    let lamw : ℂ := (r : ℂ) ^ (w - 1 / 2)
    let lamv : ℂ := (r : ℂ) ^ (v - 1 / 2)
    let zw : evenSubspace :=
      burnolExtendedSoninEvaluationVector w b hwlo hwhi hb
    let zv : evenSubspace :=
      burnolExtendedSoninEvaluationVector v b hvlo hvhi hb
    let kw : soninExtendedSpace a :=
      burnolExtendedSoninEvaluationVector w a hwlo hwhi ha
    let kv : soninExtendedSpace a :=
      burnolExtendedSoninEvaluationVector v a hvlo hvhi ha
    ⟪zw, burnolExtendedBilateralApertureHolonomy a ha r hr zv⟫_ℂ =
      (lamw * star lamv - (lamw * star lamv)⁻¹) * ⟪kw, kv⟫_ℂ := by
  dsimp only
  let hr0 : 0 < r := zero_lt_one.trans hr
  let b : ℝ := r⁻¹ * a
  have hb : 0 < b := mul_pos (inv_pos.mpr hr0) ha
  letI : Fact (0 < a) := ⟨ha⟩
  letI : Fact (0 < b) := ⟨hb⟩
  let U := evenDilationCLM r hr0
  let P := burnolExtendedSoninProjection a ha
  let V := ContinuousLinearMap.adjoint U
  let zw : evenSubspace :=
    burnolExtendedSoninEvaluationVector w b hwlo hwhi hb
  let zv : evenSubspace :=
    burnolExtendedSoninEvaluationVector v b hvlo hvhi hb
  let pwV : soninExtendedSpace a :=
    burnolProjectedAdjointEvaluationVector hwlo hwhi ha hr.le
  let pvV : soninExtendedSpace a :=
    burnolProjectedAdjointEvaluationVector hvlo hvhi ha hr.le
  let pwU : soninExtendedSpace a :=
    burnolProjectedForwardEvaluationVector hwlo hwhi ha hr.le
  let pvU : soninExtendedSpace a :=
    burnolProjectedForwardEvaluationVector hvlo hvhi ha hr.le
  have hVv : (pvV : evenSubspace) = P (V zv) := rfl
  have hUv : (pvU : evenSubspace) = P (U zv) := rfl
  have hfirst : ⟪zw, U (P (V zv))⟫_ℂ = ⟪pwV, pvV⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left U (P (V zv)) zw]
    change ⟪V zw, P (V zv)⟫_ℂ = _
    rw [← hVv]
    exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right pvV (V zw)).symm
  have hsecond : ⟪zw, V (P (U zv))⟫_ℂ = ⟪pwU, pvU⟫_ℂ := by
    rw [ContinuousLinearMap.adjoint_inner_right U zw (P (U zv))]
    change ⟪U zw, P (U zv)⟫_ℂ = _
    rw [← hUv]
    exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right pvU (U zw)).symm
  have hpwV := burnolProjectedAdjointEvaluationVector_eq hwlo hwhi ha hr.le
  have hpvV := burnolProjectedAdjointEvaluationVector_eq hvlo hvhi ha hr.le
  have hpwU := burnolProjectedForwardEvaluationVector_eq hwlo hwhi ha hr.le
  have hpvU := burnolProjectedForwardEvaluationVector_eq hvlo hvhi ha hr.le
  have hinner_smul_smul (x y : soninExtendedSpace a) (c d : ℂ) :
      ⟪c • x, d • y⟫_ℂ = star c * d * ⟪x, y⟫_ℂ := by
    calc
      ⟪c • x, d • y⟫_ℂ = star c * ⟪x, d • y⟫_ℂ :=
        inner_smul_left x (d • y) c
      _ = star c * (d * ⟪x, y⟫_ℂ) := by
        congr 1
        exact inner_smul_right x y d
      _ = star c * d * ⟪x, y⟫_ℂ := by ring
  change ⟪zw, (U * P * V - V * P * U) zv⟫_ℂ = _
  rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    mul_apply_eq_comp, mul_apply_eq_comp, inner_sub_right,
    hfirst, hsecond]
  dsimp only [pwV, pvV, pwU, pvU]
  rw [hpwV, hpvV, hpwU, hpvU]
  rw [hinner_smul_smul, hinner_smul_smul]
  simp only [star_star, star_inv₀]
  ring

end RHTower
