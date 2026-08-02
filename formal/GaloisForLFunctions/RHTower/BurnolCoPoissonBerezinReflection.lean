import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezin
import GaloisForLFunctions.RHTower.BurnolSoninProjectedEvaluationTransport

/-!
# Fourier reflection and finite-holonomy value of the co-Poisson Berezin diagonal

The quotient kernel below the critical line is obtained from the reflected Burnol evaluator.  The
co-Poisson source projection commutes with the cosine involution, so quotient kernels satisfy the
same exact reflection law.  Fourier-odd ambient operators therefore have odd quotient Berezin
diagonals.  At a source-annihilator point, the quotient kernel is ambient and the finite bilateral
holonomy reads the exact aperture-orientation coefficient.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Canonical left-half-plane evaluation vector in the co-Poisson quotient realization. -/
def burnolCoPoissonQuotientReflectedEvaluationVector
    (w : ℂ) (b : ℝ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2) (hb : 0 < b) :
    burnolCoPoissonQuotientSpace b := by
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  let k : evenSubspace := burnolExtendedSoninReflectedEvaluationVector w b hlo hhi hb
  let p : evenSubspace := (burnolCoPoissonSourceSpace b).starProjection k
  refine ⟨k - p, ?_, ?_⟩
  · exact (soninExtendedSpace b).sub_mem
      (burnolExtendedSoninReflectedEvaluationVector w b hlo hhi hb).property
      (burnolCoPoissonSourceSpace_le_soninExtendedSpace hb
        ((burnolCoPoissonSourceSpace b).starProjection_apply_mem k))
  · exact Submodule.sub_starProjection_mem_orthogonal k

@[simp] theorem coe_burnolCoPoissonQuotientReflectedEvaluationVector
    (w : ℂ) (b : ℝ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2) (hb : 0 < b) :
    (burnolCoPoissonQuotientReflectedEvaluationVector w b hlo hhi hb : evenSubspace) =
      (burnolExtendedSoninReflectedEvaluationVector w b hlo hhi hb : evenSubspace) -
        burnolCoPoissonSourceProjection b
          (burnolExtendedSoninReflectedEvaluationVector w b hlo hhi hb : evenSubspace) :=
  rfl

/-- Reproducing identity for the continued left-half-plane quotient evaluator. -/
theorem inner_burnolCoPoissonQuotientReflectedEvaluationVector
    (w : ℂ) (b : ℝ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2) (hb : 0 < b)
    (f : burnolCoPoissonQuotientSpace b) :
    ⟪burnolCoPoissonQuotientReflectedEvaluationVector w b hlo hhi hb, f⟫_ℂ =
      burnolExtendedSoninReflectedEvaluation w b hlo hhi hb
        ⟨(f : evenSubspace), f.property.1⟩ := by
  change ⟪(burnolCoPoissonQuotientReflectedEvaluationVector w b hlo hhi hb :
      evenSubspace), (f : evenSubspace)⟫_ℂ = _
  rw [coe_burnolCoPoissonQuotientReflectedEvaluationVector, inner_sub_left]
  have hp0 : ⟪burnolCoPoissonSourceProjection b
        (burnolExtendedSoninReflectedEvaluationVector w b hlo hhi hb : evenSubspace),
      (f : evenSubspace)⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (burnolCoPoissonSourceProjection_apply_mem b _) f.property.2
  rw [hp0, sub_zero]
  exact inner_burnolExtendedSoninReflectedEvaluationVector w b hlo hhi hb
    ⟨(f : evenSubspace), f.property.1⟩

/-- Exact cosine reflection of quotient evaluation vectors in Lean's Hermitian Riesz convention. -/
theorem coe_burnolCoPoissonQuotientReflectedEvaluationVector_eq_cosine
    (w : ℂ) (b : ℝ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2) (hb : 0 < b) :
    (burnolCoPoissonQuotientReflectedEvaluationVector w b hlo hhi hb : evenSubspace) =
      soninCosineUnitary
        (burnolCoPoissonQuotientEvaluationVector (1 - w) b (by
          rw [Complex.sub_re, Complex.one_re]
          linarith) (by
          rw [Complex.sub_re, Complex.one_re]
          linarith) hb : evenSubspace) := by
  let hRlo : 1 / 2 < (1 - w).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  let hRhi : (1 - w).re < 1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  change (burnolCoPoissonQuotientReflectedEvaluationVector w b hlo hhi hb : evenSubspace) =
    soninCosineUnitary
      (burnolCoPoissonQuotientEvaluationVector (1 - w) b hRlo hRhi hb : evenSubspace)
  rw [coe_burnolCoPoissonQuotientReflectedEvaluationVector,
    coe_burnolCoPoissonQuotientEvaluationVector]
  have hk :
      (burnolExtendedSoninReflectedEvaluationVector w b hlo hhi hb : evenSubspace) =
        soninCosineUnitary
          (burnolExtendedSoninEvaluationVector (1 - w) b hRlo hRhi hb : evenSubspace) := by
    have h := congrArg (fun x : soninExtendedSpace b => (x : evenSubspace))
      (burnolExtendedSoninReflectedEvaluationVector_eq_cosine w b hlo hhi hb)
    exact h
  rw [hk, ← soninCosineUnitary_burnolCoPoissonSourceProjection, map_sub]

/-- Left-half-plane co-Poisson Berezin diagonal. -/
def burnolCoPoissonReflectedBerezin
    {b : ℝ} (T : evenSubspace →L[ℂ] evenSubspace)
    (w : ℂ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2) (hb : 0 < b) : ℂ :=
  ⟪(burnolCoPoissonQuotientReflectedEvaluationVector w b hlo hhi hb : evenSubspace),
    T (burnolCoPoissonQuotientReflectedEvaluationVector w b hlo hhi hb : evenSubspace)⟫_ℂ

/-- Fourier oddness of an operator makes its source-defined Berezin reader reflection odd. -/
theorem burnolCoPoissonReflectedBerezin_eq_neg
    {b : ℝ} {T : evenSubspace →L[ℂ] evenSubspace}
    (hodd : ∀ x : evenSubspace,
      T (soninCosineUnitary x) = -soninCosineUnitary (T x))
    (w : ℂ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2) (hb : 0 < b) :
    burnolCoPoissonReflectedBerezin T w hlo hhi hb =
      -burnolCoPoissonBerezin T (1 - w) (by
        rw [Complex.sub_re, Complex.one_re]
        linarith) (by
        rw [Complex.sub_re, Complex.one_re]
        linarith) hb := by
  let hRlo : 1 / 2 < (1 - w).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  let hRhi : (1 - w).re < 1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  change burnolCoPoissonReflectedBerezin T w hlo hhi hb =
    -burnolCoPoissonBerezin T (1 - w) hRlo hRhi hb
  rw [burnolCoPoissonReflectedBerezin, burnolCoPoissonBerezin,
    coe_burnolCoPoissonQuotientReflectedEvaluationVector_eq_cosine,
    hodd, inner_neg_right, soninCosineUnitary.inner_map_map]

/-- Pointwise anticommutation of the actual finite bilateral aperture holonomy with cosine
reflection. -/
theorem burnolExtendedBilateralApertureHolonomy_cosine_odd
    (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) (x : evenSubspace) :
    burnolExtendedBilateralApertureHolonomy a ha r hr (soninCosineUnitary x) =
      -soninCosineUnitary (burnolExtendedBilateralApertureHolonomy a ha r hr x) := by
  have h := burnolExtendedBilateralApertureHolonomy_fourier_odd a ha r hr
  have hx := congrArg (fun T : evenSubspace →L[ℂ] evenSubspace =>
    T (evenFourierTransform x)) h
  simp only [mul_apply_eq_comp, neg_apply, evenFourierTransform_involutive] at hx
  change evenFourierTransform
      (burnolExtendedBilateralApertureHolonomy a ha r hr x) =
    -burnolExtendedBilateralApertureHolonomy a ha r hr (evenFourierTransform x) at hx
  change burnolExtendedBilateralApertureHolonomy a ha r hr (soninCosineUnitary x) =
    -soninCosineUnitary (burnolExtendedBilateralApertureHolonomy a ha r hr x)
  rw [← neg_eq_iff_eq_neg]
  have hFU (y : evenSubspace) : evenFourierTransform y = soninCosineUnitary y := rfl
  rw [hFU x, hFU (burnolExtendedBilateralApertureHolonomy a ha r hr x)] at hx
  exact hx.symm

/-- At a co-Poisson annihilator point the finite-holonomy Berezin value is exactly the bilateral
aperture orientation. -/
theorem burnolCoPoissonBerezin_holonomy_re_of_annihilator
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hann : BurnolCoPoissonAnnihilatorPoint w (r⁻¹ * a) hlo hhi
      (mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha)) :
    (burnolCoPoissonBerezin
      (burnolExtendedBilateralApertureHolonomy a ha r hr) w hlo hhi
      (mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha)).re =
      (r ^ (2 * w.re - 1) - r ^ (1 - 2 * w.re)) *
        ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 := by
  let b : ℝ := r⁻¹ * a
  let hb : 0 < b := mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha
  change (burnolCoPoissonBerezin
      (burnolExtendedBilateralApertureHolonomy a ha r hr) w hlo hhi hb).re = _
  rw [burnolCoPoissonBerezin,
    coe_burnolCoPoissonQuotientEvaluationVector_eq_of_annihilator hlo hhi hb hann]
  exact (burnolExtended_bilateralApertureDefectEnergy_eq_holonomy hlo hhi ha hr).symm.trans
    (burnolExtended_bilateralApertureDefectEnergy hlo hhi ha hr)

/-- Normalized real finite-holonomy reader. -/
def burnolCoPoissonNormalizedHolonomy
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r) : ℝ :=
  (burnolCoPoissonBerezin
      (burnolExtendedBilateralApertureHolonomy a ha r hr) w hlo hhi
      (mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha)).re /
    ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2

/-- Exact normalized aperture orientation on every nonzero source-annihilator fibre. -/
theorem burnolCoPoissonNormalizedHolonomy_eq_of_annihilator
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hann : BurnolCoPoissonAnnihilatorPoint w (r⁻¹ * a) hlo hhi
      (mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha))
    (hk : burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0) :
    burnolCoPoissonNormalizedHolonomy hlo hhi ha hr =
      r ^ (2 * w.re - 1) - r ^ (1 - 2 * w.re) := by
  rw [burnolCoPoissonNormalizedHolonomy,
    burnolCoPoissonBerezin_holonomy_re_of_annihilator hlo hhi ha hr hann]
  have hn : ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hk)
  field_simp

theorem burnol_rpow_orientation_eq_two_sinh
    {r : ℝ} (hr : 0 < r) (sigma : ℝ) :
    r ^ (2 * sigma - 1) - r ^ (1 - 2 * sigma) =
      2 * Real.sinh (2 * Real.log r * (sigma - 1 / 2)) := by
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hr]
  have hplus : Real.log r * (2 * sigma - 1) =
      2 * Real.log r * (sigma - 1 / 2) := by ring
  have hminus : Real.log r * (1 - 2 * sigma) =
      -(2 * Real.log r * (sigma - 1 / 2)) := by ring
  rw [hplus, hminus, Real.sinh_eq]
  ring

/-- Hyperbolic form of the normalized co-Poisson finite-holonomy value. -/
theorem burnolCoPoissonNormalizedHolonomy_eq_two_sinh_of_annihilator
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hann : BurnolCoPoissonAnnihilatorPoint w (r⁻¹ * a) hlo hhi
      (mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha))
    (hk : burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0) :
    burnolCoPoissonNormalizedHolonomy hlo hhi ha hr =
      2 * Real.sinh (2 * Real.log r * (w.re - 1 / 2)) := by
  rw [burnolCoPoissonNormalizedHolonomy_eq_of_annihilator hlo hhi ha hr hann hk,
    burnol_rpow_orientation_eq_two_sinh (zero_lt_one.trans hr)]

end RHTower
