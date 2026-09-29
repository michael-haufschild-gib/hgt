import GaloisForLFunctions.HTGeometry.HardyBoundaryCayleyIdentification

/-!
# Hardy functions with real boundary values are constant

The boundary of an `H²` function has vanishing negative Fourier modes.  A real boundary function
has conjugate-symmetric Fourier modes, so all positive modes vanish as well: the function is the
constant `f(0)`.
-/

open Complex MeasureTheory Filter
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The additive-circle Fourier modes of an `H²` boundary are its zero-extended Taylor
coefficients. -/
theorem fourierBasis_repr_hardyDiskBoundary (f : HardyDisk) (k : ℤ) :
    fourierBasis.repr (circleLpAddCircleLinearIsometryEquiv (hardyDiskBoundary f)) k =
      nonnegativeIntExtension f k := by
  change fourierBasis.repr (circleLpAddCircleLinearIsometryEquiv
    (circleLpAddCircleLinearIsometryEquiv.symm (fourierBasis.repr.symm
      (nonnegativeIntExtensionLinearIsometry f)))) k = _
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The additive-circle pullback of an `L²` circle function is its composition with the
circle identification. -/
theorem coeFn_circleLpAddCircleLinearIsometryEquiv (g : Lp ℂ 2 circleLebesgue) :
    (circleLpAddCircleLinearIsometryEquiv g : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[@AddCircle.haarAddCircle (1 : ℝ) inferInstance]
        (g : Circle → ℂ) ∘ addCircleCircleEquiv :=
  Lp.coeFn_compMeasurePreserving g addCircleCircleMeasurePreserving

/-- Fourier modes of an almost everywhere real function are conjugate symmetric. -/
theorem fourierCoeff_neg_of_ae_real {G : AddCircle (1 : ℝ) → ℂ}
    (hG : ∀ᵐ t ∂(@AddCircle.haarAddCircle (1 : ℝ) inferInstance), conj (G t) = G t) (n : ℤ) :
    fourierCoeff G (-n) = conj (fourierCoeff G n) := by
  rw [fourierCoeff, fourierCoeff, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [hG] with t ht
  simp only [smul_eq_mul, neg_neg, map_mul, ht, fourier_neg, RingHomCompTriple.comp_apply,
    RingHom.id_apply]

/-- **Real boundary rigidity.**  If the boundary of `f ∈ H²` is real almost everywhere, every
Taylor coefficient of positive order vanishes. -/
theorem hardyDisk_coeff_eq_zero_of_boundary_real (f : HardyDisk)
    (hreal : ∀ᵐ z ∂circleLebesgue, conj ((hardyDiskBoundary f : Circle → ℂ) z) =
      (hardyDiskBoundary f : Circle → ℂ) z) {n : ℕ} (hn : 1 ≤ n) : f n = 0 := by
  set G := circleLpAddCircleLinearIsometryEquiv (hardyDiskBoundary f)
  have hGreal : ∀ᵐ t ∂(@AddCircle.haarAddCircle (1 : ℝ) inferInstance),
      conj ((G : AddCircle (1 : ℝ) → ℂ) t) = (G : AddCircle (1 : ℝ) → ℂ) t := by
    filter_upwards [coeFn_circleLpAddCircleLinearIsometryEquiv (hardyDiskBoundary f),
      addCircleCircleMeasurePreserving.quasiMeasurePreserving.ae hreal] with t h1 h2
    rw [h1]
    exact h2
  have hpos := fourierBasis_repr_hardyDiskBoundary f (n : ℤ)
  have hneg := fourierBasis_repr_hardyDiskBoundary f (-(n : ℤ))
  rw [fourierBasis_repr] at hpos hneg
  rw [fourierCoeff_neg_of_ae_real hGreal, hpos, nonnegativeIntExtension_ofNat] at hneg
  have hneg0 : nonnegativeIntExtension f (-(n : ℤ)) = 0 := by
    rw [nonnegativeIntExtension, if_neg (by omega)]
  rw [hneg0, map_eq_zero] at hneg
  exact hneg

/-- An `H²` function with almost everywhere real boundary is constant: its boundary is `f(0)`. -/
theorem hardyDiskBoundary_ae_eq_const_of_real (f : HardyDisk)
    (hreal : ∀ᵐ z ∂circleLebesgue, conj ((hardyDiskBoundary f : Circle → ℂ) z) =
      (hardyDiskBoundary f : Circle → ℂ) z) :
    (hardyDiskBoundary f : Circle → ℂ) =ᵐ[circleLebesgue] fun _ => f 0 := by
  have hf : f = f 0 • hardyOne := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hardyOne]
    · rw [hardyDisk_coeff_eq_zero_of_boundary_real f hreal hn, lp.coeFn_smul, Pi.smul_apply,
        hardyOne, lp.single_apply_ne _ _ _ (by omega), smul_zero]
  have hb : hardyDiskBoundary f = f 0 • circleMonomialLp circleLebesgue 0 := by
    conv_lhs => rw [hf]
    rw [map_smul, hardyOne, hardyDiskBoundary_single]
  rw [hb]
  filter_upwards [Lp.coeFn_smul (f 0) (circleMonomialLp circleLebesgue 0),
    circleMonomialLp_coeFn_ae circleLebesgue 0] with z h1 h2
  rw [h1, Pi.smul_apply, h2, pow_zero, smul_eq_mul, mul_one]

end

end GaloisForLFunctions.HTGeometry
