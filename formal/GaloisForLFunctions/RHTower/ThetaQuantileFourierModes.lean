import GaloisForLFunctions.RHTower.HedenmalmPinnedVolterraBoundaryDefect
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier modes of `L²(0,1)`

The exponentials `e_n(t) = e^{2πint}`, `n ∈ ℤ`, form a Hilbert basis of
`L²(unitIntervalMeasure)`.  The basis is transported from the Fourier basis of the circle
`ℝ/ℤ` along the measure-preserving quotient map, which is a bijection of `(0,1]` onto the
circle.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

local instance factZeroLtOneFourierModes : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

theorem unitIntervalMeasure_eq_restrict_Ioc :
    unitIntervalMeasure = (volume : Measure ℝ).restrict (Ioc 0 1) :=
  (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm

theorem volume_addCircle_one_eq_haar :
    (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

/-- The quotient map `ℝ → ℝ/ℤ` carries `unitIntervalMeasure` to Haar measure. -/
theorem measurePreserving_mk_unitInterval :
    MeasurePreserving (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ)) unitIntervalMeasure
      AddCircle.haarAddCircle := by
  have h := AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [zero_add, volume_addCircle_one_eq_haar] at h
  rwa [unitIntervalMeasure_eq_restrict_Ioc]

/-- The section `ℝ/ℤ → (0,1]`. -/
def circleSection (y : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIoc (1 : ℝ) 0 y : ℝ)

theorem measurePreserving_circleSection :
    MeasurePreserving circleSection AddCircle.haarAddCircle unitIntervalMeasure := by
  have h1 := AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0)
  have h2 := measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
    (measurableSet_Ioc (a := (0 : ℝ)) (b := 0 + 1))
  rw [volume_addCircle_one_eq_haar] at h1
  have h := h2.comp h1
  have hI : (volume : Measure ℝ).restrict (Ioc 0 (0 + 1)) = unitIntervalMeasure := by
    rw [zero_add, unitIntervalMeasure_eq_restrict_Ioc]
  rw [← hI]
  exact h

theorem circleSection_mk {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    circleSection (t : AddCircle (1 : ℝ)) = t :=
  AddCircle.equivIoc_coe_of_mem (by rwa [zero_add])

/-- Pulling back along the quotient map is a unitary `L²(ℝ/ℤ) ≅ L²(0,1)`. -/
def circleToUnitInterval :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) ≃ₗᵢ[ℂ] Lp ℂ 2 unitIntervalMeasure :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ _ measurePreserving_mk_unitInterval) fun g => by
    refine ⟨Lp.compMeasurePreserving circleSection measurePreserving_circleSection g, ?_⟩
    apply Lp.ext
    have h1 := Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving circleSection measurePreserving_circleSection g)
      measurePreserving_mk_unitInterval
    have h2 := measurePreserving_mk_unitInterval.quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving g measurePreserving_circleSection)
    have h3 : ∀ᵐ t ∂unitIntervalMeasure, t ∈ Ioc (0 : ℝ) 1 := by
      rw [unitIntervalMeasure_eq_restrict_Ioc]
      exact ae_restrict_mem measurableSet_Ioc
    filter_upwards [h1, h2, h3] with t h1t h2t h3t
    rw [show (Lp.compMeasurePreservingₗᵢ ℂ _ measurePreserving_mk_unitInterval
      (Lp.compMeasurePreserving circleSection measurePreserving_circleSection g) : Lp ℂ 2 _) =
        Lp.compMeasurePreserving _ measurePreserving_mk_unitInterval
          (Lp.compMeasurePreserving circleSection measurePreserving_circleSection g) from rfl]
    calc _ = _ := h1t
      _ = _ := h2t
      _ = (g : ℝ → ℂ) t := by simp only [Function.comp_apply, circleSection_mk h3t]

/-- The Fourier Hilbert basis `e_n` of `L²(0,1)`. -/
def unitFourierBasis : HilbertBasis ℤ ℂ (Lp ℂ 2 unitIntervalMeasure) :=
  HilbertBasis.ofRepr (circleToUnitInterval.symm.trans fourierBasis.repr)

theorem unitFourierBasis_apply (n : ℤ) :
    unitFourierBasis n = circleToUnitInterval (fourierBasis n) := by
  classical
  apply unitFourierBasis.repr.injective
  rw [HilbertBasis.repr_self]
  change lp.single 2 n 1 =
    (circleToUnitInterval.symm.trans fourierBasis.repr) (circleToUnitInterval (fourierBasis n))
  rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply, HilbertBasis.repr_self]

/-- The mode `e_n(t) = e^{2πint}`. -/
def fourierMode (n : ℤ) (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * n * t)

theorem coeFn_unitFourierBasis (n : ℤ) :
    (unitFourierBasis n : ℝ → ℂ) =ᵐ[unitIntervalMeasure] fourierMode n := by
  rw [unitFourierBasis_apply, coe_fourierBasis]
  have h1 := Lp.coeFn_compMeasurePreserving (fourierLp (T := (1 : ℝ)) 2 n)
    measurePreserving_mk_unitInterval
  have h2 := measurePreserving_mk_unitInterval.quasiMeasurePreserving.ae_eq_comp
    (coeFn_fourierLp (T := (1 : ℝ)) 2 n)
  filter_upwards [h1, h2] with t h1t h2t
  change (Lp.compMeasurePreserving _ measurePreserving_mk_unitInterval (fourierLp 2 n) : ℝ → ℂ) t = _
  rw [h1t, h2t, Function.comp_apply, fourier_coe_apply, fourierMode, Complex.ofReal_one, div_one]

theorem fourierMode_zero (t : ℝ) : fourierMode 0 t = 1 := by simp [fourierMode]

theorem norm_fourierMode (n : ℤ) (t : ℝ) : ‖fourierMode n t‖ = 1 := by
  rw [fourierMode, show (2 * Real.pi * Complex.I * n * t : ℂ) = ((2 * Real.pi * n * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem fourierMode_add (m n : ℤ) (t : ℝ) :
    fourierMode (m + n) t = fourierMode m t * fourierMode n t := by
  rw [fourierMode, fourierMode, fourierMode, ← Complex.exp_add]; push_cast; ring_nf

theorem conj_fourierMode (n : ℤ) (t : ℝ) :
    (starRingEnd ℂ) (fourierMode n t) = fourierMode (-n) t := by
  rw [fourierMode, fourierMode, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    map_intCast, map_ofNat]
  push_cast; ring

theorem continuous_fourierMode (n : ℤ) : Continuous (fourierMode n) := by
  unfold fourierMode; fun_prop

theorem fourierMode_one (n : ℤ) : fourierMode n 1 = 1 := by
  rw [fourierMode, show (2 * Real.pi * Complex.I * n * (1 : ℝ) : ℂ) = n * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

end

end RHTower
