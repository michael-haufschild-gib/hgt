import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallRealZeroClosure
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergyLimit

/-!
# P-G105: exact first signed Fredholm jet at the exponential SP-E wall

The full atomic wall determinant already has a local-uniform exponential-wall limit.  This module
extracts its first source-native signed-permutation invariants.  The order-zero, order-one, and
order-two factorial-normalized coefficients are exactly `1`, `1`, and `19 / 70`.  Therefore the
quadratic coefficient of the signed product `D(z) D(-z)` is exactly `-16 / 35`.

This is an arithmetic-source invariant only: it makes no Xi-divisor identification.
-/

open Complex Filter Topology Set MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

/-- The normalized cubic wall kernel has exact unit diagonal on the positive half-line. -/
theorem routePPrimitiveGammaJuliaStokesWallCubicKernel_diagonal {a : ℝ} (ha : 0 < a) :
    routePPrimitiveGammaJuliaStokesWallCubicKernel a a = 1 := by
  rw [routePPrimitiveGammaJuliaStokesWallCubicKernel]
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  calc
    8 * Real.sqrt a ^ 3 * Real.sqrt a ^ 3 / (a + a) ^ 3 =
        8 * (Real.sqrt a ^ 2) ^ 3 / (2 * a) ^ 3 := by ring
    _ = 1 := by
      rw [hsq]
      field_simp [ha.ne']
      ring

/-- The normalized cubic wall kernel is symmetric. -/
theorem routePPrimitiveGammaJuliaStokesWallCubicKernel_symmetric (a b : ℝ) :
    routePPrimitiveGammaJuliaStokesWallCubicKernel a b =
      routePPrimitiveGammaJuliaStokesWallCubicKernel b a := by
  unfold routePPrimitiveGammaJuliaStokesWallCubicKernel
  rw [show b + a = a + b by ring]
  ring

/-- The empty signed-permutation sector of the exponential wall has coefficient one. -/
theorem routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_zero :
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) 0 = 1 := by
  simp only [routePPrimitiveGammaJuliaStokesWallFredholmCoefficient,
    Nat.factorial_zero, Nat.cast_one, div_one,
    routePPrimitiveGammaJuliaStokesWallFredholmIntegrand,
    Matrix.det_fin_zero, Matrix.empty_eq, integral_const]
  have hmass : (routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 0).real univ = 1 := by
    rw [Measure.real, routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure_apply_univ]
    norm_num
  rw [hmass]
  norm_num

/-- The one-label signed-permutation sector of the exponential wall has coefficient one. -/
theorem routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_one :
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) 1 = 1 := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hdiag : ∀ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (p, p) = 1 := by
    intro p hp
    rw [routePPrimitiveGammaJuliaStokesWallQuantileKernel, if_pos ⟨hp, hp⟩]
    apply routePPrimitiveGammaJuliaStokesWallCubicKernel_diagonal
    rw [GaloisForLFunctions.HTGeometry.quantile_expMeasure_one hp.1 hp.2]
    exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hp.2) (by linarith [hp.1]))
  have hpoint : ∀ x : Fin 1 → ℝ, (∀ i, x i ∈ Ioo (0 : ℝ) 1) →
      routePPrimitiveGammaJuliaStokesWallFredholmIntegrand (expMeasure 1) 1 x = 1 := by
    intro x hx
    rw [routePPrimitiveGammaJuliaStokesWallFredholmIntegrand, Matrix.det_fin_one]
    change (routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (x 0, x 0) : ℂ) = 1
    norm_cast
    exact hdiag (x 0) (hx 0)
  rw [routePPrimitiveGammaJuliaStokesWallFredholmCoefficient]
  norm_num [Nat.factorial_one]
  calc
    (∫ x : Fin 1 → ℝ,
      routePPrimitiveGammaJuliaStokesWallFredholmIntegrand (expMeasure 1) 1 x ∂
        routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 1) =
      ∫ _x : Fin 1 → ℝ, (1 : ℂ) ∂routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 1 := by
        apply integral_congr_ae
        filter_upwards [ae_routePPrimitiveGammaJuliaStokesWallUnitCube_all_mem_Ioo 1] with x hx
        exact hpoint x hx
    _ = 1 := by
      rw [integral_const]
      have hmass : (routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 1).real univ = 1 := by
        rw [Measure.real, routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure_apply_univ]
        norm_num
      rw [hmass]
      norm_num

/-- The two-label signed-permutation sector of the exponential wall has coefficient `19 / 70`. -/
theorem routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_two :
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) 2 =
      (19 / 70 : ℂ) := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  let m : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  have hdiag : ∀ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (p, p) = 1 := by
    intro p hp
    rw [routePPrimitiveGammaJuliaStokesWallQuantileKernel, if_pos ⟨hp, hp⟩]
    apply routePPrimitiveGammaJuliaStokesWallCubicKernel_diagonal
    rw [GaloisForLFunctions.HTGeometry.quantile_expMeasure_one hp.1 hp.2]
    exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hp.2) (by linarith [hp.1]))
  have hsym : ∀ p q : ℝ, p ∈ Ioo (0 : ℝ) 1 → q ∈ Ioo (0 : ℝ) 1 →
      routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (q, p) =
        routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (p, q) := by
    intro p q hp hq
    simp only [routePPrimitiveGammaJuliaStokesWallQuantileKernel]
    rw [if_pos ⟨hq, hp⟩, if_pos ⟨hp, hq⟩]
    exact routePPrimitiveGammaJuliaStokesWallCubicKernel_symmetric _ _
  have hsq : ∀ p q : ℝ, p ∈ Ioo (0 : ℝ) 1 → q ∈ Ioo (0 : ℝ) 1 →
      routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (p, q) ^ 2 =
        routePPrimitiveGammaJuliaStokesWallQuantileCoherence (expMeasure 1) (p, q) := by
    intro p q hp hq
    simp [routePPrimitiveGammaJuliaStokesWallQuantileKernel,
      routePPrimitiveGammaJuliaStokesWallQuantileCoherence, hp, hq]
    apply routePPrimitiveGammaJuliaStokesWallCubicKernel_sq
    · exact GaloisForLFunctions.HTGeometry.quantile_nonneg
        GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero hp.1 hp.2
    · exact GaloisForLFunctions.HTGeometry.quantile_nonneg
        GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero hq.1 hq.2
  have hpoint : ∀ x : Fin 2 → ℝ, (∀ i, x i ∈ Ioo (0 : ℝ) 1) →
      routePPrimitiveGammaJuliaStokesWallFredholmIntegrand (expMeasure 1) 2 x =
        ((1 - routePPrimitiveGammaJuliaStokesWallQuantileCoherence
          (expMeasure 1) (x 0, x 1) : ℝ) : ℂ) := by
    intro x hx
    rw [routePPrimitiveGammaJuliaStokesWallFredholmIntegrand, Matrix.det_fin_two]
    change
      (routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (x 0, x 0) : ℂ) *
          routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (x 1, x 1) -
        routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (x 0, x 1) *
          routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (x 1, x 0) = _
    rw [hdiag (x 0) (hx 0), hdiag (x 1) (hx 1), hsym (x 0) (x 1) (hx 0) (hx 1)]
    norm_cast
    rw [show routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (x 0, x 1) *
        routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (x 0, x 1) =
        routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (x 0, x 1) ^ 2 by ring,
      hsq (x 0) (x 1) (hx 0) (hx 1)]
    norm_num
  have hcoh :
      (∫ x : Fin 2 → ℝ,
        routePPrimitiveGammaJuliaStokesWallQuantileCoherence (expMeasure 1) (x 0, x 1) ∂
          routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 2) = 16 / 35 := by
    have htransport := (measurePreserving_finTwoArrow m).integral_comp'
      (routePPrimitiveGammaJuliaStokesWallQuantileCoherence (expMeasure 1))
    have hwall := integral_wallQuantileCoherence_eq_prod (expMeasure 1)
    rw [integral_wallCubicCoherence_exp_prod_eq] at hwall
    simpa [m, routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure,
      routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure] using htransport.trans hwall
  have hcoh_int : Integrable
      (fun x : Fin 2 → ℝ => (routePPrimitiveGammaJuliaStokesWallQuantileCoherence
        (expMeasure 1) (x 0, x 1) : ℂ))
      (routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 2) := by
    refine Integrable.of_bound ?_ 1 ?_
    · have hmeas : Measurable (fun x : Fin 2 → ℝ =>
        routePPrimitiveGammaJuliaStokesWallQuantileCoherence (expMeasure 1) (x 0, x 1)) :=
          (measurable_wallQuantileCoherence (expMeasure 1)).comp
            MeasurableEquiv.finTwoArrow.measurable
      exact (Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable
    · filter_upwards with x
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hbound := wallQuantileCoherence_norm_le_one (expMeasure 1)
        GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero (x 0, x 1)
      simpa using hbound
  have hcohC :
      (∫ x : Fin 2 → ℝ, (routePPrimitiveGammaJuliaStokesWallQuantileCoherence
        (expMeasure 1) (x 0, x 1) : ℂ) ∂
          routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 2) = (16 / 35 : ℂ) := by
    have hcohR_int : Integrable
        (fun x : Fin 2 → ℝ => routePPrimitiveGammaJuliaStokesWallQuantileCoherence
          (expMeasure 1) (x 0, x 1))
        (routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 2) := by
      refine Integrable.of_bound ?_ 1 ?_
      · exact ((measurable_wallQuantileCoherence (expMeasure 1)).comp
          MeasurableEquiv.finTwoArrow.measurable).aestronglyMeasurable
      · filter_upwards with x
        exact wallQuantileCoherence_norm_le_one (expMeasure 1)
          GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero (x 0, x 1)
    calc
      (∫ x : Fin 2 → ℝ, (routePPrimitiveGammaJuliaStokesWallQuantileCoherence
        (expMeasure 1) (x 0, x 1) : ℂ) ∂
          routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 2) =
        (∫ x : Fin 2 → ℝ, routePPrimitiveGammaJuliaStokesWallQuantileCoherence
          (expMeasure 1) (x 0, x 1) ∂
            routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 2 : ℝ) := by
          exact Complex.ofRealCLM.integral_comp_comm hcohR_int
      _ = 16 / 35 := by
        rw [hcoh]
        norm_num
  rw [routePPrimitiveGammaJuliaStokesWallFredholmCoefficient]
  norm_num [Nat.factorial_two]
  calc
    (∫ x : Fin 2 → ℝ,
      routePPrimitiveGammaJuliaStokesWallFredholmIntegrand (expMeasure 1) 2 x ∂
        routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 2) / 2 =
      (∫ x : Fin 2 → ℝ, ((1 - routePPrimitiveGammaJuliaStokesWallQuantileCoherence
        (expMeasure 1) (x 0, x 1) : ℝ) : ℂ) ∂
        routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 2) / 2 := by
        apply congrArg (fun w : ℂ => w / 2)
        apply integral_congr_ae
        filter_upwards [ae_routePPrimitiveGammaJuliaStokesWallUnitCube_all_mem_Ioo 2] with x hx
        exact hpoint x hx
    _ = 19 / 70 := by
      push_cast
      rw [integral_sub (integrable_const 1) hcoh_int]
      have hmass : (routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure 2).real univ = 1 := by
        rw [Measure.real, routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure_apply_univ]
        norm_num
      rw [integral_const, hmass]
      rw [hcohC]
      norm_num

/-- Exact quadratic signed-square Fredholm jet at the unit-exponential SP-E wall. -/
theorem routePPrimitiveGammaJuliaStokesWallSignedSquareQuadraticJet_exp :
    2 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) 2 -
      routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) 1 ^ 2 =
        -(16 / 35 : ℂ) := by
  rw [routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_one,
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_two]
  norm_num

end

end RHTower
