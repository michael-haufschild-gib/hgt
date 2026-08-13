import GaloisForLFunctions.RHTower.FieldOneFiniteStageAngularL2Density
import GaloisForLFunctions.RHTower.FieldOnePositiveLogSchwartzDensity
import GaloisForLFunctions.RHTower.L2SeparatedProductDensity

/-!
# Dense range of the finite-stage Connes--Marcolli half-density

This file proves Connes--Marcolli Proposition 2.30 on the literal finite-stage semilocal carrier.
The compact angular test function is extended by zero to the exact finite local unit locus; the
real Schwartz lift is supported on the positive half-line.  Therefore its rational `S`-unit orbit
has exactly one nonzero term, `q = 1`.  The half-density map consequently contains all separated
products of dense angular and logarithmic factor subspaces, and has dense range.
-/

open scoped ENNReal TensorProduct algebraMap

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function IsDedekindDomain MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open _root_.RHTower

/-- If a rational `S`-unit has norm one at every selected finite place, then its rational absolute
value is one. -/
theorem fieldOneSUnit_abs_eq_one_of_localNorm_one
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S)
    (hq : ∀ v : ↥S,
      ‖algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ)‖ = 1) :
    |(q.1 : ℚ)| = 1 := by
  have hexp : fieldOneSUnitExponent S q = 0 := by
    funext v
    let p : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v.1
    letI : Fact p.1.Prime := ⟨p.2⟩
    let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v.1
    let z : ℚ_[p.1] := e (algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ))
    have hz0 : z ≠ 0 := by
      dsimp [z]
      exact (map_ne_zero e).mpr <| map_ne_zero (algebraMap ℚ
        (v.1.adicCompletion ℚ)) |>.mpr (Units.ne_zero q.1)
    have hzle : ‖z‖ ≤ 1 := by
      exact (fieldOneAdic_padicEquiv_norm_le_one_iff v.1 _).2 (hq v).le
    have hzinvle : ‖z⁻¹‖ ≤ 1 := by
      have hlocalInv :
          ‖(algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ))⁻¹‖ ≤ 1 := by
        rw [norm_inv, hq v]
        simp
      have hmapInv :
          e ((algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ))⁻¹) = z⁻¹ := by
        simp [z]
      rw [← hmapInv]
      exact (fieldOneAdic_padicEquiv_norm_le_one_iff v.1 _).2 hlocalInv
    have honele : 1 ≤ ‖z‖ := by
      have hnorm0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
      calc
        1 = ‖z‖ * ‖z‖⁻¹ := (mul_inv_cancel₀ hnorm0).symm
        _ = ‖z‖ * ‖z⁻¹‖ := by rw [norm_inv]
        _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hzinvle (norm_nonneg z)
        _ = ‖z‖ := mul_one _
    have hznorm : ‖z‖ = 1 := le_antisymm hzle honele
    have hpow : (p.1 : ℝ) ^ (-z.valuation) = 1 := by
      rw [← Padic.norm_eq_zpow_neg_valuation hz0, hznorm]
    have hvalneg : -z.valuation = 0 :=
      (zpow_eq_one_iff_right₀ (by positivity)
        (by exact_mod_cast p.2.one_lt.ne')).1 hpow
    have hval : z.valuation = 0 := neg_eq_zero.mp hvalneg
    unfold fieldOneSUnitExponent
    rw [deningerRatExp_apply_of_prime p.2]
    have hzcast : z = ((q.1 : ℚ) : ℚ_[p.1]) := by
      change e (algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ)) =
        algebraMap ℚ ℚ_[p.1] (q.1 : ℚ)
      exact e.commutes (q.1 : ℚ)
    rw [hzcast, Padic.valuation_ratCast] at hval
    exact hval
  have hreconstruct := fieldOneSUnitProduct_exponent_eq_abs_value S q
  rw [hexp] at hreconstruct
  simpa [fieldOneSUnitProduct] using hreconstruct.symm

theorem fieldOneSUnit_eq_one_or_neg_one_of_localNorm_one
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S)
    (hq : ∀ v : ↥S,
      ‖algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ)‖ = 1) :
    (q.1 : ℚ) = 1 ∨ (q.1 : ℚ) = -1 := by
  simpa using eq_or_eq_neg_of_abs_eq
    (fieldOneSUnit_abs_eq_one_of_localNorm_one S q hq)

/-- Nonvanishing of the angular zero extension along an `S`-unit orbit forces that orbit element
to be a sign. -/
theorem fieldOneFiniteStageAngularBruhatExtension_orbit_eq_sign
    (S : Finset (HeightOneSpectrum ℤ))
    (a : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ)
    (k : FieldOneFiniteStageModuleOneClass S)
    (q : fieldOneSUnitSubgroup S)
    (hnonzero :
      (fieldOneFiniteStageAngularBruhatExtension S a).1
        (fun v =>
          algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
            fieldOneFiniteStageAngularFiniteEmbedding S k v) ≠ 0) :
    (q.1 : ℚ) = 1 ∨ (q.1 : ℚ) = -1 := by
  let x : FieldOneFiniteStageFinitePart S := fun v =>
    algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
      fieldOneFiniteStageAngularFiniteEmbedding S k v
  have hx : x ∈ fieldOneFiniteStageAngularUnitLocus S := by
    by_contra hxnot
    exact hnonzero <|
      fieldOneFiniteStageAngularZeroExtension_eq_zero_off_locus S a hxnot
  apply fieldOneSUnit_eq_one_or_neg_one_of_localNorm_one S q
  intro v
  have hxv := hx v
  change
    ‖algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
      fieldOneFiniteStageAngularFiniteEmbedding S k v‖ = 1 at hxv
  rw [norm_mul,
    show ‖fieldOneFiniteStageAngularFiniteEmbedding S k v‖ = 1 by
      exact (fieldOneFiniteStageAngularTorusRepresentative S k v).2,
    mul_one] at hxv
  exact hxv

/-- Dense source pure tensor: logarithmic test function lifted to the real Schwartz factor and
angular locally constant function extended to the finite factor. -/
def fieldOneFiniteStageBruhatDensePureTensor
    (S : Finset (HeightOneSpectrum ℤ))
    (a : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ)
    (h : FieldOneCompactSmoothLog) :
    FieldOneFiniteStageBruhatSchwartz S :=
  fieldOnePositiveLogTestToSchwartz h ⊗ₜ[ℂ]
    fieldOneFiniteStageAngularBruhatExtension S a

/-- Every nonidentity orbit term of a dense source pure tensor vanishes.  Finite-place support
reduces the possible rational `S`-unit to `±1`; positive real support eliminates `-1`. -/
theorem fieldOneFiniteStageBruhatDensePureTensor_orbit_eq_zero
    (S : Finset (HeightOneSpectrum ℤ))
    (a : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ)
    (h : FieldOneCompactSmoothLog)
    (k : FieldOneFiniteStageModuleOneClass S) (t : ℝ)
    (q : fieldOneSUnitSubgroup S) (hq : q ≠ 1) :
    fieldOneFiniteStageBruhatOrbit S
      (fieldOneFiniteStageBruhatDensePureTensor S a h)
      (fieldOneFiniteStageBruhatLogRayIdele S
        (fun v => (fieldOneFiniteStageAngularTorusRepresentative S k v).1) t) q = 0 := by
  rw [fieldOneFiniteStageBruhatDensePureTensor,
    fieldOneFiniteStageBruhatOrbit_tmul]
  unfold fieldOneFiniteStageBruhatPureTensorOrbit
  change
    fieldOnePositiveLogTestToSchwartz h
        (Real.exp t * (((q.1 : ℚ) : ℚ) : ℝ)) *
      (fieldOneFiniteStageAngularBruhatExtension S a).1
        (fun v =>
          algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
            fieldOneFiniteStageAngularFiniteEmbedding S k v) = 0
  by_cases hfinite :
      (fieldOneFiniteStageAngularBruhatExtension S a).1
        (fun v =>
          algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
            (((fieldOneFiniteStageAngularTorusRepresentative S k v).1 :
              (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ)) = 0
  · have hfinite' :
        (fieldOneFiniteStageAngularBruhatExtension S a).1
          (fun v =>
            algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
              fieldOneFiniteStageAngularFiniteEmbedding S k v) = 0 := by
      simpa [fieldOneFiniteStageAngularFiniteEmbedding] using hfinite
    rw [hfinite', mul_zero]
  · have hsign := fieldOneFiniteStageAngularBruhatExtension_orbit_eq_sign
      S a k q hfinite
    rcases hsign with hqone | hqneg
    · exfalso
      apply hq
      apply Subtype.ext
      apply Units.ext
      exact hqone
    · have hreal :
          fieldOnePositiveLogTestToSchwartz h
            (Real.exp t * (((q.1 : ℚ) : ℚ) : ℝ)) = 0 := by
        rw [fieldOnePositiveLogTestToSchwartz_apply]
        have hqnegReal : ((((q.1 : ℚ) : ℚ) : ℝ)) = -1 := by
          exact_mod_cast hqneg
        rw [fieldOnePositiveLogSchwartzRaw, hqnegReal]
        have hnotpos : ¬ 0 < Real.exp t * (-1 : ℝ) := by
          nlinarith [Real.exp_pos t]
        rw [if_neg hnotpos]
      rw [hreal, zero_mul]

/-- The identity orbit term is exactly the separated angular/logarithmic product before applying
the module half-density. -/
theorem fieldOneFiniteStageBruhatDensePureTensor_orbit_one
    (S : Finset (HeightOneSpectrum ℤ))
    (a : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ)
    (h : FieldOneCompactSmoothLog)
    (k : FieldOneFiniteStageModuleOneClass S) (t : ℝ) :
    fieldOneFiniteStageBruhatOrbit S
      (fieldOneFiniteStageBruhatDensePureTensor S a h)
      (fieldOneFiniteStageBruhatLogRayIdele S
        (fun v => (fieldOneFiniteStageAngularTorusRepresentative S k v).1) t) 1 =
      fieldOnePositiveLogTestToSchwartz h (Real.exp t) * a k := by
  rw [fieldOneFiniteStageBruhatDensePureTensor,
    fieldOneFiniteStageBruhatOrbit_tmul]
  unfold fieldOneFiniteStageBruhatPureTensorOrbit
  simp only [fieldOneFiniteStageBruhatLogRayIdele, Units.val_mk0,
    Subgroup.coe_one, Units.val_one, Rat.cast_one, mul_one, map_one, one_mul]
  change fieldOnePositiveLogTestToSchwartz h (Real.exp t) *
      (fieldOneFiniteStageAngularBruhatExtension S a).1
        (fieldOneFiniteStageAngularFiniteEmbedding S k) = _
  rw [fieldOneFiniteStageAngularBruhatExtension_apply_embedding]

/-- Exact singleton-orbit evaluation of periodization on the dense pure tensors. -/
theorem fieldOneFiniteStageBruhatDensePureTensor_logPeriodization
    (S : Finset (HeightOneSpectrum ℤ))
    (a : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ)
    (h : FieldOneCompactSmoothLog)
    (k : FieldOneFiniteStageModuleOneClass S) (t : ℝ) :
    fieldOneFiniteStageBruhatLogPeriodization S
      (fieldOneFiniteStageBruhatDensePureTensor S a h) (k, t) =
      fieldOnePositiveLogTestToSchwartz h (Real.exp t) * a k := by
  rw [fieldOneFiniteStageBruhatLogPeriodization,
    fieldOneFiniteStageBruhatPeriodization,
    tsum_eq_single (1 : fieldOneSUnitSubgroup S)]
  · exact fieldOneFiniteStageBruhatDensePureTensor_orbit_one S a h k t
  · intro q hq
    exact fieldOneFiniteStageBruhatDensePureTensor_orbit_eq_zero S a h k t q hq

/-- On the dense pure tensors, the Connes--Marcolli half-density is literally the separated
product `a(k) h(t)`. -/
theorem fieldOneFiniteStageBruhatDensePureTensor_logHalfDensity
    (S : Finset (HeightOneSpectrum ℤ))
    (a : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ)
    (h : FieldOneCompactSmoothLog)
    (k : FieldOneFiniteStageModuleOneClass S) (t : ℝ) :
    fieldOneFiniteStageBruhatLogHalfDensity S
      (fieldOneFiniteStageBruhatDensePureTensor S a h) (k, t) =
      a k * h t := by
  rw [fieldOneFiniteStageBruhatLogHalfDensity,
    fieldOneFiniteStageBruhatDensePureTensor_logPeriodization]
  change (Real.exp (t / 2) : ℂ) *
    (fieldOnePositiveLogTestToSchwartz h (Real.exp t) * a k) = a k * h t
  have hid := fieldOnePositiveLogTestToSchwartz_halfDensity_exp h t
  calc
    (Real.exp (t / 2) : ℂ) *
        (fieldOnePositiveLogTestToSchwartz h (Real.exp t) * a k) =
        a k * ((Real.exp (t / 2) : ℂ) *
          fieldOnePositiveLogTestToSchwartz h (Real.exp t)) := by ring
    _ = a k * h t := congrArg (fun z : ℂ => a k * z) hid

/-- Dense pure tensors as a linear map into the literal Bruhat--Schwartz tensor product. -/
def fieldOneFiniteStageBruhatDenseSource
    (S : Finset (HeightOneSpectrum ℤ)) :
    (LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ ⊗[ℂ]
      FieldOneCompactSmoothLog) →ₗ[ℂ]
      FieldOneFiniteStageBruhatSchwartz S :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ
    (fieldOneFiniteStageBruhatDensePureTensor S)
    (fun a b h => by
      simp [fieldOneFiniteStageBruhatDensePureTensor,
        TensorProduct.tmul_add])
    (fun c a h => by
      simp [fieldOneFiniteStageBruhatDensePureTensor,
        TensorProduct.tmul_smul])
    (fun a h g => by
      simp [fieldOneFiniteStageBruhatDensePureTensor,
        TensorProduct.add_tmul])
    (fun c a h => by
      simp [fieldOneFiniteStageBruhatDensePureTensor,
        TensorProduct.smul_tmul'])

@[simp]
theorem fieldOneFiniteStageBruhatDenseSource_tmul
    (S : Finset (HeightOneSpectrum ℤ))
    (a : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ)
    (h : FieldOneCompactSmoothLog) :
    fieldOneFiniteStageBruhatDenseSource S (a ⊗ₜ[ℂ] h) =
      fieldOneFiniteStageBruhatDensePureTensor S a h :=
  rfl

abbrev FieldOneFiniteStageSplitLogL2
    (S : Finset (HeightOneSpectrum ℤ)) :=
  Lp ℂ 2 ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
    (volume : Measure ℝ))

theorem fieldOneFiniteStageBruhatLogHalfDensity_add
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatLogHalfDensity S (x + y) =
      fieldOneFiniteStageBruhatLogHalfDensity S x +
        fieldOneFiniteStageBruhatLogHalfDensity S y := by
  funext z
  simp only [fieldOneFiniteStageBruhatLogHalfDensity,
    fieldOneFiniteStageBruhatLogPeriodization,
    fieldOneFiniteStageBruhatPeriodization_add, Pi.add_apply]
  ring

theorem fieldOneFiniteStageBruhatLogHalfDensity_smul
    (S : Finset (HeightOneSpectrum ℤ)) (c : ℂ)
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatLogHalfDensity S (c • x) =
      c • fieldOneFiniteStageBruhatLogHalfDensity S x := by
  funext z
  simp only [fieldOneFiniteStageBruhatLogHalfDensity,
    fieldOneFiniteStageBruhatLogPeriodization,
    fieldOneFiniteStageBruhatPeriodization_smul, Pi.smul_apply]
  ring

theorem fieldOneFiniteStageBruhatLogHalfDensity_memLp_product
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    MemLp (fieldOneFiniteStageBruhatLogHalfDensity S x) 2
      ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
        (volume : Measure ℝ)) := by
  simpa [fieldOneFiniteStageSplitLogHaarMeasure] using
    fieldOneFiniteStageBruhatLogHalfDensity_memLp S x

/-- Connes--Marcolli half-density as a linear map in exact compact-times-log coordinates. -/
def fieldOneFiniteStageBruhatLogHalfDensityLinearMap
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageBruhatSchwartz S →ₗ[ℂ]
      FieldOneFiniteStageSplitLogL2 S where
  toFun x :=
    (fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S x).toLp
      (fieldOneFiniteStageBruhatLogHalfDensity S x)
  map_add' x y := by
    apply Lp.ext
    filter_upwards [
      (fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S (x + y)).coeFn_toLp,
      (fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S x).coeFn_toLp,
      (fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S y).coeFn_toLp,
      Lp.coeFn_add
        ((fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S x).toLp
          (fieldOneFiniteStageBruhatLogHalfDensity S x))
        ((fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S y).toLp
          (fieldOneFiniteStageBruhatLogHalfDensity S y))]
      with z hxy hx hy hadd
    rw [hxy, hadd]
    change
      fieldOneFiniteStageBruhatLogHalfDensity S (x + y) z =
        ((fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S x).toLp
          (fieldOneFiniteStageBruhatLogHalfDensity S x)) z +
        ((fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S y).toLp
          (fieldOneFiniteStageBruhatLogHalfDensity S y)) z
    rw [hx, hy]
    exact congrFun (fieldOneFiniteStageBruhatLogHalfDensity_add S x y) z
  map_smul' c x := by
    apply Lp.ext
    filter_upwards [
      (fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S (c • x)).coeFn_toLp,
      (fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S x).coeFn_toLp,
      Lp.coeFn_smul c
        ((fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S x).toLp
          (fieldOneFiniteStageBruhatLogHalfDensity S x))]
      with z hcx hx hsmul
    rw [hcx]
    change
      fieldOneFiniteStageBruhatLogHalfDensity S (c • x) z =
        (c • ((fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S x).toLp
          (fieldOneFiniteStageBruhatLogHalfDensity S x))) z
    rw [hsmul]
    change
      fieldOneFiniteStageBruhatLogHalfDensity S (c • x) z =
        c • ((fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S x).toLp
          (fieldOneFiniteStageBruhatLogHalfDensity S x)) z
    rw [hx]
    exact congrFun (fieldOneFiniteStageBruhatLogHalfDensity_smul S c x) z

theorem fieldOneFiniteStageBruhatLogHalfDensityLinearMap_ae
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatLogHalfDensityLinearMap S x =ᵐ[
      fieldOneFiniteStageSplitLogHaarMeasure S]
      fieldOneFiniteStageBruhatLogHalfDensity S x :=
  (fieldOneFiniteStageBruhatLogHalfDensity_memLp_product S x).coeFn_toLp

theorem fieldOneFiniteStageAngularLocallyConstantToL2_ae
    (S : Finset (HeightOneSpectrum ℤ))
    (a : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ) :
    fieldOneFiniteStageAngularLocallyConstantToL2 S a =ᵐ[
      fieldOneFiniteStageModuleOneProbabilityHaarMeasure S] a := by
  change
    ContinuousMap.toLp 2
      (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S) ℂ
      (a : C(FieldOneFiniteStageModuleOneClass S, ℂ)) =ᵐ[
        fieldOneFiniteStageModuleOneProbabilityHaarMeasure S] a
  exact ContinuousMap.coeFn_toLp
    (p := 2) (𝕜 := ℂ)
    (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S)
    (a : C(FieldOneFiniteStageModuleOneClass S, ℂ))

/-- Exact `L²` identity: dense source pure tensors map to separated factor products. -/
theorem fieldOneFiniteStageBruhatLogHalfDensity_denseSource_tmul
    (S : Finset (HeightOneSpectrum ℤ))
    (a : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ)
    (h : FieldOneCompactSmoothLog) :
    fieldOneFiniteStageBruhatLogHalfDensityLinearMap S
        (fieldOneFiniteStageBruhatDenseSource S (a ⊗ₜ[ℂ] h)) =
      l2SeparatedProduct
        (fieldOneFiniteStageAngularLocallyConstantToL2 S a)
        (fieldOneCompactSmoothLogToL2 h) := by
  apply Lp.ext
  filter_upwards [
    fieldOneFiniteStageBruhatLogHalfDensityLinearMap_ae S
      (fieldOneFiniteStageBruhatDenseSource S (a ⊗ₜ[ℂ] h)),
    l2SeparatedProduct_ae
      (fieldOneFiniteStageAngularLocallyConstantToL2 S a)
      (fieldOneCompactSmoothLogToL2 h),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (fieldOneFiniteStageAngularLocallyConstantToL2_ae S a),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (fieldOneCompactSmoothLogToL2_ae h)]
      with z hleft hright ha hh
  rw [hleft, hright]
  simp only [Function.comp_apply] at ha hh
  change
    fieldOneFiniteStageBruhatLogHalfDensity S
      (fieldOneFiniteStageBruhatDensePureTensor S a h) z =
        fieldOneFiniteStageAngularLocallyConstantToL2 S a z.1 *
          fieldOneCompactSmoothLogToL2 h z.2
  rw [ha, hh]
  exact fieldOneFiniteStageBruhatDensePureTensor_logHalfDensity
    S a h z.1 z.2

/-- The half-density image is dense for the exact Haar normalization in logarithmic module
coordinates. -/
theorem fieldOneFiniteStageBruhatLogHalfDensityLinearMap_denseRange
    (S : Finset (HeightOneSpectrum ℤ)) :
    DenseRange (fieldOneFiniteStageBruhatLogHalfDensityLinearMap S) := by
  let E := fieldOneFiniteStageBruhatLogHalfDensityLinearMap S
  let J := fieldOneFiniteStageBruhatDenseSource S
  let T := denseFactorTensorToProduct
    (fieldOneFiniteStageAngularLocallyConstantToL2 S)
    fieldOneCompactSmoothLogToL2
  have hmaps : E.comp J = T := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a h =>
        exact fieldOneFiniteStageBruhatLogHalfDensity_denseSource_tmul S a h
    | add x y hx hy =>
        simp only [map_add, hx, hy]
  have hT : DenseRange T :=
    denseFactorTensorToProduct_denseRange
      (fieldOneFiniteStageAngularLocallyConstantToL2 S)
      fieldOneCompactSmoothLogToL2
      (fieldOneFiniteStageAngularLocallyConstantToL2_denseRange S)
      fieldOneCompactSmoothLogToL2_denseRange
  have hcomp : DenseRange (E.comp J) := by
    rw [hmaps]
    exact hT
  have hcomp' : DenseRange
      ((E : FieldOneFiniteStageBruhatSchwartz S →
          FieldOneFiniteStageSplitLogL2 S) ∘
        (J : (LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ ⊗[ℂ]
          FieldOneCompactSmoothLog) → FieldOneFiniteStageBruhatSchwartz S)) := by
    simpa only [LinearMap.coe_comp] using hcomp
  simpa only [E] using hcomp'.of_comp

abbrev FieldOneFiniteStageSplitPositiveLogL2
    (S : Finset (HeightOneSpectrum ℤ)) :=
  Lp ℂ 2 ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
    fieldOnePositiveUnitsLogHaarMeasure)

theorem fieldOnePositiveUnitsLog_measurePreserving :
    MeasurePreserving fieldOnePositiveUnitsExpHomeomorph.symm
      fieldOnePositiveUnitsLogHaarMeasure (volume : Measure ℝ) := by
  have hexp := fieldOnePositiveUnitsExp_measurePreserving
  change MeasurePreserving fieldOnePositiveUnitsExpHomeomorph.toMeasurableEquiv
    (volume : Measure ℝ) fieldOnePositiveUnitsLogHaarMeasure at hexp
  exact hexp.symm

theorem fieldOneFiniteStageSplitLogExp_measurePreserving
    (S : Finset (HeightOneSpectrum ℤ)) :
    MeasurePreserving
      (Prod.map id fieldOnePositiveUnitsExpHomeomorph)
      ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
        (volume : Measure ℝ))
      ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
        fieldOnePositiveUnitsLogHaarMeasure) :=
  (MeasurePreserving.id
    (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S)).prod
      fieldOnePositiveUnitsExp_measurePreserving

theorem fieldOneFiniteStageSplitLogExpSymm_measurePreserving
    (S : Finset (HeightOneSpectrum ℤ)) :
    MeasurePreserving
      (Prod.map id fieldOnePositiveUnitsExpHomeomorph.symm)
      ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
        fieldOnePositiveUnitsLogHaarMeasure)
      ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
        (volume : Measure ℝ)) :=
  (MeasurePreserving.id
    (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S)).prod
      fieldOnePositiveUnitsLog_measurePreserving

/-- Pullback by logarithm is a real-linear `L²` equivalence between logarithmic coordinates and
the positive multiplicative factor carrying logarithmic Haar. -/
def fieldOneFiniteStageSplitLogExpL2Equiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageSplitLogL2 S ≃ₗᵢ[ℝ]
      FieldOneFiniteStageSplitPositiveLogL2 S where
  __ := Lp.compMeasurePreservingₗᵢ ℝ
    (Prod.map id fieldOnePositiveUnitsExpHomeomorph.symm)
    (fieldOneFiniteStageSplitLogExpSymm_measurePreserving S)
  invFun := Lp.compMeasurePreserving
    (Prod.map id fieldOnePositiveUnitsExpHomeomorph)
    (fieldOneFiniteStageSplitLogExp_measurePreserving S)
  left_inv f := by
    change Lp.compMeasurePreserving
        (Prod.map id fieldOnePositiveUnitsExpHomeomorph)
        (fieldOneFiniteStageSplitLogExp_measurePreserving S)
      (Lp.compMeasurePreserving
        (Prod.map id fieldOnePositiveUnitsExpHomeomorph.symm)
        (fieldOneFiniteStageSplitLogExpSymm_measurePreserving S) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f
      (fieldOneFiniteStageSplitLogExpSymm_measurePreserving S)
      (fieldOneFiniteStageSplitLogExp_measurePreserving S)]
    have hfun :
        (Prod.map id fieldOnePositiveUnitsExpHomeomorph.symm ∘
          Prod.map id fieldOnePositiveUnitsExpHomeomorph) =
        (id : (FieldOneFiniteStageModuleOneClass S × ℝ) → _) := by
      funext z
      simp
    simpa only [hfun] using Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving
        (Prod.map id fieldOnePositiveUnitsExpHomeomorph.symm)
        (fieldOneFiniteStageSplitLogExpSymm_measurePreserving S)
      (Lp.compMeasurePreserving
        (Prod.map id fieldOnePositiveUnitsExpHomeomorph)
        (fieldOneFiniteStageSplitLogExp_measurePreserving S) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f
      (fieldOneFiniteStageSplitLogExp_measurePreserving S)
      (fieldOneFiniteStageSplitLogExpSymm_measurePreserving S)]
    have hfun :
        (Prod.map id fieldOnePositiveUnitsExpHomeomorph ∘
          Prod.map id fieldOnePositiveUnitsExpHomeomorph.symm) =
        (id : (FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) → _) := by
      funext z
      simp
    simpa only [hfun] using Lp.compMeasurePreserving_id_apply f

theorem fieldOneFiniteStageSplitProductHaar_le_logScalar
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageSplitProductHaarMeasure S ≤
      (haarScalarFactor fieldOnePositiveUnitsHaarMeasure
          fieldOnePositiveUnitsLogHaarMeasure : ℝ≥0∞) •
        ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
          fieldOnePositiveUnitsLogHaarMeasure) := by
  rw [fieldOneFiniteStageSplitProductHaarMeasure,
    fieldOnePositiveUnitsHaar_eq_smul_logHaar,
    Measure.prod_smul_right]

/-- Change only the positive-Haar normalization, preserving representatives pointwise. -/
def fieldOneFiniteStagePositiveLogToCanonicalL2
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageSplitPositiveLogL2 S →L[ℝ]
      FieldOneFiniteStageSplitProductL2 S :=
  Lp.LpToLpOfMeasureLeSMul
    (c := (haarScalarFactor fieldOnePositiveUnitsHaarMeasure
      fieldOnePositiveUnitsLogHaarMeasure : ℝ≥0∞))
    (by simp)
    (fieldOneFiniteStageSplitProductHaar_le_logScalar S)

theorem fieldOneFiniteStagePositiveLogToCanonicalL2_ae
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageSplitPositiveLogL2 S) :
    fieldOneFiniteStagePositiveLogToCanonicalL2 S f =ᵐ[
      fieldOneFiniteStageSplitProductHaarMeasure S] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul
    (c := (haarScalarFactor fieldOnePositiveUnitsHaarMeasure
      fieldOnePositiveUnitsLogHaarMeasure : ℝ≥0∞))
    (by simp)
    (fieldOneFiniteStageSplitProductHaar_le_logScalar S) f

theorem fieldOneFiniteStagePositiveLogToCanonicalL2_surjective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Surjective (fieldOneFiniteStagePositiveLogToCanonicalL2 S) := by
  intro f
  have hfLog : MemLp (f :
      FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ → ℂ) 2
      ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
        fieldOnePositiveUnitsLogHaarMeasure) := by
    have hf := Lp.memLp f
    rw [fieldOneFiniteStageSplitProductHaarMeasure,
      fieldOnePositiveUnitsLogHaar_eq_smul_haar,
      Measure.prod_smul_right]
    exact hf.smul_measure (by simp)
  let g : FieldOneFiniteStageSplitPositiveLogL2 S :=
    hfLog.toLp f
  refine ⟨g, ?_⟩
  apply Lp.ext
  have hcanonAC : fieldOneFiniteStageSplitProductHaarMeasure S ≪
      (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
        fieldOnePositiveUnitsLogHaarMeasure :=
    Measure.absolutelyContinuous_of_le_smul
      (fieldOneFiniteStageSplitProductHaar_le_logScalar S)
  have hgCanon : g =ᵐ[fieldOneFiniteStageSplitProductHaarMeasure S] f :=
    hcanonAC.ae_eq hfLog.coeFn_toLp
  filter_upwards [
    fieldOneFiniteStagePositiveLogToCanonicalL2_ae S g,
    hgCanon] with z hleft hright
  exact hleft.trans hright

/-- Continuous real-linear transport from log-coordinate `L²` to the canonical split Haar `L²`. -/
def fieldOneFiniteStageLogToCanonicalL2
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageSplitLogL2 S →L[ℝ]
      FieldOneFiniteStageSplitProductL2 S :=
  (fieldOneFiniteStagePositiveLogToCanonicalL2 S).comp
    (fieldOneFiniteStageSplitLogExpL2Equiv S).toLinearIsometry.toContinuousLinearMap

theorem fieldOneFiniteStageLogToCanonicalL2_surjective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Surjective (fieldOneFiniteStageLogToCanonicalL2 S) :=
  (fieldOneFiniteStagePositiveLogToCanonicalL2_surjective S).comp
    (fieldOneFiniteStageSplitLogExpL2Equiv S).surjective

/-- Transporting the log-coordinate half-density gives the already constructed canonical split
half-density exactly. -/
theorem fieldOneFiniteStageLogToCanonicalL2_halfDensity
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageLogToCanonicalL2 S
        (fieldOneFiniteStageBruhatLogHalfDensityLinearMap S x) =
      fieldOneFiniteStageBruhatHalfDensityLinearMap S x := by
  apply Lp.ext
  let F : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ →
      FieldOneFiniteStageModuleOneClass S × ℝ :=
    Prod.map id fieldOnePositiveUnitsExpHomeomorph.symm
  let hF := fieldOneFiniteStageSplitLogExpSymm_measurePreserving S
  have hlogPull := hF.quasiMeasurePreserving.ae_eq_comp
    (fieldOneFiniteStageBruhatLogHalfDensityLinearMap_ae S x)
  filter_upwards [
    fieldOneFiniteStagePositiveLogToCanonicalL2_ae S
      ((fieldOneFiniteStageSplitLogExpL2Equiv S)
        (fieldOneFiniteStageBruhatLogHalfDensityLinearMap S x)),
    Lp.coeFn_compMeasurePreserving
      (fieldOneFiniteStageBruhatLogHalfDensityLinearMap S x) hF,
    hlogPull,
    fieldOneFiniteStageBruhatHalfDensityL2_ae S x]
      with z hscalar hexp hlog hcanonical
  rw [hscalar, hexp]
  simp only [Function.comp_apply] at hlog
  rw [hlog, hcanonical]
  rfl

/-- **Connes--Marcolli Proposition 2.30 (dense range).**  The literal half-density map from
finite-stage Bruhat--Schwartz functions has dense range in canonical split-Haar `L²`. -/
theorem fieldOneFiniteStageBruhatHalfDensityLinearMap_denseRange
    (S : Finset (HeightOneSpectrum ℤ)) :
    DenseRange (fieldOneFiniteStageBruhatHalfDensityLinearMap S) := by
  let J := fieldOneFiniteStageLogToCanonicalL2 S
  let Elog := fieldOneFiniteStageBruhatLogHalfDensityLinearMap S
  have hcomp : DenseRange
      ((J : FieldOneFiniteStageSplitLogL2 S →
          FieldOneFiniteStageSplitProductL2 S) ∘
        (Elog : FieldOneFiniteStageBruhatSchwartz S →
          FieldOneFiniteStageSplitLogL2 S)) :=
    (fieldOneFiniteStageLogToCanonicalL2_surjective S).denseRange.comp
      (fieldOneFiniteStageBruhatLogHalfDensityLinearMap_denseRange S)
      J.continuous
  have heq :
      ((J : FieldOneFiniteStageSplitLogL2 S →
          FieldOneFiniteStageSplitProductL2 S) ∘
        (Elog : FieldOneFiniteStageBruhatSchwartz S →
          FieldOneFiniteStageSplitLogL2 S)) =
      fieldOneFiniteStageBruhatHalfDensityLinearMap S := by
    funext x
    exact fieldOneFiniteStageLogToCanonicalL2_halfDensity S x
  rw [heq] at hcomp
  exact hcomp

/-- Closed exact source theorem: the Connes--Marcolli half-density is a well-defined complex-linear
map with dense range. -/
theorem fieldOneFiniteStage_connesMarcolli_proposition_2_30
    (S : Finset (HeightOneSpectrum ℤ)) :
    DenseRange (fieldOneFiniteStageBruhatHalfDensityLinearMap S) :=
  fieldOneFiniteStageBruhatHalfDensityLinearMap_denseRange S

end

end GaloisForLFunctions.RHTower
