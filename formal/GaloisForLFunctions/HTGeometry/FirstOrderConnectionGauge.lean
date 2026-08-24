import GaloisForLFunctions.HTGeometry.LocallyIntegrableLinearEvolution
import GaloisForLFunctions.HTGeometry.SkewFrequencyCurrent

/-!
# Locally integrable first-order connection gauges

For a locally integrable self-adjoint operator potential `V` and real `c ≠ 0`, this module
constructs the noncommutative Carathéodory gauge solving `G' = -(i/c) V G`. It proves uniqueness,
compact-interval absolute continuity, the ODE almost everywhere, pointwise norm preservation, and
finite-dimensional unitarity. The final AE Leibniz theorem gives exact cancellation of the full
connection on its natural first-order/Sobolev representative domain.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex
open MeasureTheory Set Filter intervalIntegral

variable {m : ℕ}

def firstOrderGaugeCoefficient (c : ℝ) : ℂ := -(Complex.I / (c : ℂ))

theorem star_firstOrderGaugeCoefficient {c : ℝ} :
    star (firstOrderGaugeCoefficient c) = -firstOrderGaugeCoefficient c := by
  apply Complex.ext
  · simp [firstOrderGaugeCoefficient]
  · simp [firstOrderGaugeCoefficient, div_eq_mul_inv]

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsScalarTower ℝ (E →L[ℂ] E) E where
  smul_assoc _ _ _ := rfl

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsBoundedSMul (E →L[ℂ] E) E where
  dist_smul_pair' A x y := by
    change dist (A x) (A y) ≤ dist A 0 * dist x y
    simpa only [dist_eq_norm, sub_zero, map_sub] using A.le_opNorm (x - y)
  dist_pair_smul' A B x := by
    change dist (A x) (B x) ≤ dist A B * dist x 0
    simpa only [dist_eq_norm, sub_zero, sub_apply] using (A - B).le_opNorm x

theorem firstOrderGaugeProduct_hasDerivAt
    {c u : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {V G : ℝ → E →L[ℂ] E} {f : ℝ → E} {f' : E}
    (hG : HasDerivAt G (firstOrderGaugeCoefficient c • (V u * G u)) u)
    (hf : HasDerivAt f f' u) :
    HasDerivAt (fun t => G t (f t))
      ((firstOrderGaugeCoefficient c • (V u * G u)) (f u) + G u f') u := by
  change HasDerivAt (G • f)
    ((firstOrderGaugeCoefficient c • (V u * G u)) • f u + G u • f') u
  simpa only [add_comm] using hG.smul hf

theorem firstOrderGaugeConnection_cancel
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V G G' : E →L[ℂ] E) (f f' : E)
    (hG' : G' = firstOrderGaugeCoefficient c • (V * G)) :
    (-Complex.I * (c : ℂ)) • (G' f + G f') + V (G f) =
      G ((-Complex.I * (c : ℂ)) • f') := by
  rw [hG']
  unfold firstOrderGaugeCoefficient
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hcoeff : (-Complex.I * (c : ℂ)) * (-(Complex.I / (c : ℂ))) = -1 := by
    field_simp [hcC]
    rw [Complex.I_sq]
  simp only [smul_apply, mul_apply_eq_comp, map_smul]
  rw [smul_add, smul_smul, hcoeff, neg_one_smul]
  abel

theorem firstOrderGaugeCoefficient_eq_real_mul_I {c : ℝ} (hc : c ≠ 0) :
    firstOrderGaugeCoefficient c = (((-c⁻¹ : ℝ) : ℂ) * Complex.I) := by
  unfold firstOrderGaugeCoefficient
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp [hcC]

theorem firstOrderGaugeNormSq_hasDerivAt_zero
    {c u : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {V G : ℝ → E →L[ℂ] E}
    (hV : IsSelfAdjoint (V u))
    (hG : HasDerivAt G (firstOrderGaugeCoefficient c • (V u * G u)) u)
    (x : E) :
    HasDerivAt (fun t => ‖G t x‖ ^ 2) 0 u := by
  have hgx : HasDerivAt (fun t => G t x)
      ((firstOrderGaugeCoefficient c • (V u * G u)) x) u := by
    change HasDerivAt (fun t => G t • x)
      ((firstOrderGaugeCoefficient c • (V u * G u)) • x) u
    exact hG.smul_const x
  have hnorm := GaloisForLFunctions.HTGeometry.hasDerivAt_normSq_path hgx
  convert hnorm using 1
  simp only [smul_apply, mul_apply_eq_comp]
  rw [firstOrderGaugeCoefficient_eq_real_mul_I hc]
  have hz := GaloisForLFunctions.HTGeometry.re_inner_real_smul_I_smul_isSelfAdjoint_eq_zero
    hV (-c⁻¹) (G u x)
  symm
  rw [hz, mul_zero]

theorem firstOrderGaugeNorm_preserved
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {V G : ℝ → E →L[ℂ] E}
    (hV : ∀ u, IsSelfAdjoint (V u))
    (hG : ∀ u, HasDerivAt G (firstOrderGaugeCoefficient c • (V u * G u)) u)
    (hG0 : G 0 = 1) (t : ℝ) (x : E) :
    ‖G t x‖ = ‖x‖ := by
  have hsquare : ‖G 0 x‖ ^ 2 = ‖G t x‖ ^ 2 := by
    refine is_const_of_fderiv_eq_zero
      (fun u => (firstOrderGaugeNormSq_hasDerivAt_zero hc (hV u) (hG u) x).differentiableAt)
      (fun u => ?_) 0 t
    have hu := (firstOrderGaugeNormSq_hasDerivAt_zero hc (hV u) (hG u) x).hasFDerivAt.fderiv
    rw [hu]
    ext
    simp
  rw [hG0] at hsquare
  change ‖x‖ ^ 2 = ‖G t x‖ ^ 2 at hsquare
  nlinarith [norm_nonneg (G t x), norm_nonneg x]

theorem firstOrderGauge_isometry
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {V G : ℝ → E →L[ℂ] E}
    (hV : ∀ u, IsSelfAdjoint (V u))
    (hG : ∀ u, HasDerivAt G (firstOrderGaugeCoefficient c • (V u * G u)) u)
    (hG0 : G 0 = 1) (t : ℝ) : Isometry (G t) := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact firstOrderGaugeNorm_preserved hc hV hG hG0 t (x - y)

def firstOrderGaugeODECoefficient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℝ) (V : ℝ → E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  firstOrderGaugeCoefficient c • V t

theorem locallyIntegrable_firstOrderGaugeODECoefficient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c : ℝ} {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume) :
    LocallyIntegrable (firstOrderGaugeODECoefficient c V) MeasureTheory.volume := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro k hk
  let L : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
    (ContinuousLinearMap.lsmul ℂ ℂ) (firstOrderGaugeCoefficient c)
  have h := L.integrable_comp (hV.integrableOn_isCompact hk)
  change Integrable (firstOrderGaugeODECoefficient c V) (MeasureTheory.volume.restrict k)
  change Integrable (firstOrderGaugeODECoefficient c V) (MeasureTheory.volume.restrict k) at h
  exact h

def caratheodoryGauge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (c : ℝ) (V : ℝ → E →L[ℂ] E) : ℝ → E →L[ℂ] E :=
  GaloisForLFunctions.HTGeometry.caratheodoryEvolution (firstOrderGaugeODECoefficient c V)

@[simp]
theorem caratheodoryGauge_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {c : ℝ} {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume) :
    caratheodoryGauge c V 0 = 1 := by
  exact GaloisForLFunctions.HTGeometry.caratheodoryEvolution_zero
    (locallyIntegrable_firstOrderGaugeODECoefficient hV)

theorem continuous_caratheodoryGauge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {c : ℝ} {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume) :
    Continuous (caratheodoryGauge c V) :=
  GaloisForLFunctions.HTGeometry.continuous_caratheodoryEvolution
    (locallyIntegrable_firstOrderGaugeODECoefficient hV)

theorem absolutelyContinuousOnInterval_caratheodoryGauge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {c : ℝ} {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    (a b : ℝ) : AbsolutelyContinuousOnInterval (caratheodoryGauge c V) a b :=
  GaloisForLFunctions.HTGeometry.absolutelyContinuousOnInterval_caratheodoryEvolution
    (locallyIntegrable_firstOrderGaugeODECoefficient hV) a b

theorem ae_hasDerivAt_caratheodoryGauge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {c : ℝ} {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume) :
    ∀ᵐ t : ℝ ∂MeasureTheory.volume, HasDerivAt (caratheodoryGauge c V)
      (firstOrderGaugeCoefficient c • (V t * caratheodoryGauge c V t)) t := by
  have h := GaloisForLFunctions.HTGeometry.ae_hasDerivAt_caratheodoryEvolution
    (locallyIntegrable_firstOrderGaugeODECoefficient (c := c) hV)
  filter_upwards [h] with t ht
  simpa [caratheodoryGauge, firstOrderGaugeODECoefficient] using ht

theorem caratheodoryGauge_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {c : ℝ} {V F : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    (hF : Continuous F)
    (hvolterra : ∀ t : ℝ, F t = 1 + ∫ s in (0 : ℝ)..t,
      firstOrderGaugeODECoefficient c V s * F s) :
    F = caratheodoryGauge c V :=
  GaloisForLFunctions.HTGeometry.caratheodoryEvolution_unique
    (locallyIntegrable_firstOrderGaugeODECoefficient hV) hF hvolterra

theorem firstOrderGaugeNormSq_absolutelyContinuousOnInterval
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {c : ℝ} {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    (x : E) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => ‖caratheodoryGauge c V t x‖ ^ 2) a b := by
  have hG := absolutelyContinuousOnInterval_caratheodoryGauge (c := c) hV a b
  let ev : (E →L[ℂ] E) →L[ℂ] E := (ContinuousLinearMap.apply ℂ E) x
  have hev : AbsolutelyContinuousOnInterval
      (fun t => caratheodoryGauge c V t x) a b := by
    simpa [ev] using
      GaloisForLFunctions.HTGeometry.ContinuousLinearMap.comp_absolutelyContinuousOnInterval
        ev hG
  have hnormLip : LipschitzWith 1 (fun y : E => ‖y‖) :=
    LipschitzWith.of_dist_le_mul fun y z => by
      simpa [Real.dist_eq, dist_eq_norm] using abs_norm_sub_norm_le y z
  have hnorm : AbsolutelyContinuousOnInterval
      (fun t => ‖caratheodoryGauge c V t x‖) a b :=
    GaloisForLFunctions.HTGeometry.LipschitzWith.comp_absolutelyContinuousOnInterval
      hnormLip hev
  convert hnorm.mul hnorm using 1
  funext t
  simp [pow_two]

theorem ae_hasDerivAt_caratheodoryGauge_normSq_zero
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (x : E) :
    ∀ᵐ t : ℝ ∂MeasureTheory.volume,
      HasDerivAt (fun u => ‖caratheodoryGauge c V u x‖ ^ 2) 0 t := by
  filter_upwards [ae_hasDerivAt_caratheodoryGauge hV] with t ht
  exact firstOrderGaugeNormSq_hasDerivAt_zero hc (hVstar t) ht x

theorem caratheodoryGauge_norm_preserved
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (t : ℝ) (x : E) :
    ‖caratheodoryGauge c V t x‖ = ‖x‖ := by
  let q : ℝ → ℝ := fun u => ‖caratheodoryGauge c V u x‖ ^ 2
  have hqAC : AbsolutelyContinuousOnInterval q 0 t :=
    firstOrderGaugeNormSq_absolutelyContinuousOnInterval hV x 0 t
  have hqAE : ∀ᵐ u : ℝ ∂MeasureTheory.volume, HasDerivAt q 0 u :=
    ae_hasDerivAt_caratheodoryGauge_normSq_zero hc hV hVstar x
  have hintzero : (∫ u in (0 : ℝ)..t, deriv q u) = 0 := by
    calc
      (∫ u in (0 : ℝ)..t, deriv q u) = ∫ _u in (0 : ℝ)..t, (0 : ℝ) := by
        exact intervalIntegral.integral_congr_ae (by
          filter_upwards [hqAE] with u hu _
          exact hu.deriv)
      _ = 0 := by simp
  have hsq : q t = q 0 := by
    have hFTC := hqAC.integral_deriv_eq_sub
    rw [hintzero] at hFTC
    linarith
  rw [show q t = ‖caratheodoryGauge c V t x‖ ^ 2 by rfl,
    show q 0 = ‖caratheodoryGauge c V 0 x‖ ^ 2 by rfl,
    caratheodoryGauge_zero hV] at hsq
  change ‖caratheodoryGauge c V t x‖ ^ 2 = ‖x‖ ^ 2 at hsq
  change ‖caratheodoryGauge c V t x‖ = ‖x‖
  nlinarith [norm_nonneg (caratheodoryGauge c V t x), norm_nonneg x]

theorem caratheodoryGauge_isometry
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (t : ℝ) :
    Isometry (caratheodoryGauge c V t) := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact caratheodoryGauge_norm_preserved hc hV hVstar t (x - y)

noncomputable def caratheodoryGaugeLinearIsometry
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (t : ℝ) : E →ₗᵢ[ℂ] E :=
  LinearIsometry.mk (caratheodoryGauge c V t).toLinearMap
    (caratheodoryGauge_norm_preserved hc hV hVstar t)

theorem caratheodoryGaugeLinearIsometry_surjective
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E]
    {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (t : ℝ) :
    Function.Surjective (caratheodoryGaugeLinearIsometry hc hV hVstar t) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
    (caratheodoryGaugeLinearIsometry hc hV hVstar t).injective

noncomputable def caratheodoryGaugeUnitary
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E]
    {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (t : ℝ) : E ≃ₗᵢ[ℂ] E :=
  LinearIsometryEquiv.ofSurjective
    (caratheodoryGaugeLinearIsometry hc hV hVstar t)
    (caratheodoryGaugeLinearIsometry_surjective hc hV hVstar t)

@[simp]
theorem caratheodoryGaugeUnitary_apply
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E]
    {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (t : ℝ) (x : E) :
    caratheodoryGaugeUnitary hc hV hVstar t x = caratheodoryGauge c V t x := rfl

theorem ae_caratheodoryGauge_product_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {c : ℝ} {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    {f f' : ℝ → E}
    (hf : ∀ᵐ u : ℝ ∂MeasureTheory.volume, HasDerivAt f (f' u) u) :
    ∀ᵐ u : ℝ ∂MeasureTheory.volume,
      HasDerivAt (fun t => caratheodoryGauge c V t (f t))
        ((firstOrderGaugeCoefficient c • (V u * caratheodoryGauge c V u)) (f u) +
          caratheodoryGauge c V u (f' u)) u := by
  filter_upwards [ae_hasDerivAt_caratheodoryGauge hV, hf] with u hG hu
  exact firstOrderGaugeProduct_hasDerivAt hG hu

theorem caratheodoryGauge_connection_cancel
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (V : ℝ → E →L[ℂ] E) (u : ℝ) (f f' : E) :
    (-Complex.I * (c : ℂ)) •
        ((firstOrderGaugeCoefficient c • (V u * caratheodoryGauge c V u)) f +
          caratheodoryGauge c V u f') +
      V u (caratheodoryGauge c V u f) =
        caratheodoryGauge c V u ((-Complex.I * (c : ℂ)) • f') := by
  exact firstOrderGaugeConnection_cancel hc (V u) (caratheodoryGauge c V u)
    (firstOrderGaugeCoefficient c • (V u * caratheodoryGauge c V u)) f f' rfl

/-- Exact almost-everywhere gauge law on the natural first-order domain. The first conjunct is the
weak/Sobolev representative's product derivative; the second is the full connection cancellation. -/
theorem ae_caratheodoryGauge_trivializes_connection
    {c : ℝ} (hc : c ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V MeasureTheory.volume)
    {f f' : ℝ → E}
    (hf : ∀ᵐ u : ℝ ∂MeasureTheory.volume, HasDerivAt f (f' u) u) :
    ∀ᵐ u : ℝ ∂MeasureTheory.volume,
      HasDerivAt (fun t => caratheodoryGauge c V t (f t))
          ((firstOrderGaugeCoefficient c • (V u * caratheodoryGauge c V u)) (f u) +
            caratheodoryGauge c V u (f' u)) u ∧
        (-Complex.I * (c : ℂ)) •
            ((firstOrderGaugeCoefficient c • (V u * caratheodoryGauge c V u)) (f u) +
              caratheodoryGauge c V u (f' u)) +
          V u (caratheodoryGauge c V u (f u)) =
            caratheodoryGauge c V u ((-Complex.I * (c : ℂ)) • f' u) := by
  filter_upwards [ae_caratheodoryGauge_product_hasDerivAt hV hf] with u hu
  exact ⟨hu, caratheodoryGauge_connection_cancel hc V u (f u) (f' u)⟩

end GaloisForLFunctions.HTGeometry
