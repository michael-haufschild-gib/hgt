import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert

/-!
# Strictly accretive bounded multipliers

A bounded complex multiplier whose real part is exactly a positive constant times its squared
modulus cannot send a nonzero vector into the orthogonal complement of any subspace containing that
vector.  More sharply, every decomposition of the image into a source component and an orthogonal
remainder has a quantitative source-component floor.

This is the measure-independent Hilbert-space law used by the Burnol divided-shift source leakage
argument.  It needs no spectral theorem: the proof is the pointwise multiplier identity integrated
in `L²`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {φ : α → ℂ} {C δ : ℝ}

/-- Exact accretivity of a bounded multiplier from the pointwise identity
`Re φ = δ * |φ|²`. -/
theorem lpBoundedMulCLM_re_inner_eq
    (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hacc : ∀ x, (φ x).re = δ * Complex.normSq (φ x))
    (f : Lp ℂ 2 μ) :
    (inner ℂ f (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f)).re =
      δ * ‖lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def]
  rw [← RCLike.re_eq_complex_re]
  rw [← integral_re (𝕜 := ℂ) (MeasureTheory.L2.integrable_inner f
    (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f))]
  rw [← integral_re (𝕜 := ℂ) (MeasureTheory.L2.integrable_inner
    (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f)
    (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f))]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC f] with x hx
  rw [hx, RCLike.inner_apply', RCLike.inner_apply']
  rw [show (starRingEnd ℂ) (f x) * (φ x * f x) =
    φ x * ((starRingEnd ℂ) (f x) * f x) by ring]
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, hacc, Complex.normSq_mul]
  ring

/-- A strictly accretive, nowhere-zero multiplier has a nonzero quadratic pairing on every
nonzero vector. -/
theorem lpBoundedMulCLM_inner_ne_zero_of_strictAccretive
    (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hacc : ∀ x, (φ x).re = δ * Complex.normSq (φ x))
    (hδ : 0 < δ) (hne : ∀ x, φ x ≠ 0) {f : Lp ℂ 2 μ} (hf : f ≠ 0) :
    inner ℂ f (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f) ≠ 0 := by
  let T := lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC
  have hTf : T f ≠ 0 := by
    intro hzero
    apply hf
    apply lpBoundedMulCLM_injective_general hφ hC0 hC hne
    simpa [T] using hzero
  intro hzero
  have hreal := lpBoundedMulCLM_re_inner_eq hφ hC0 hC hacc f
  change (inner ℂ f (T f)).re = δ * ‖T f‖ ^ 2 at hreal
  rw [hzero] at hreal
  norm_num at hreal
  exact hreal.elim (fun h => hδ.ne' h) (fun h => hTf h)

/-- A strictly accretive multiplier cannot carry a nonzero vector into the orthogonal complement
of a subspace containing that vector. -/
theorem lpBoundedMulCLM_not_mem_orthogonal_of_strictAccretive
    (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hacc : ∀ x, (φ x).re = δ * Complex.normSq (φ x))
    (hδ : 0 < δ) (hne : ∀ x, φ x ≠ 0)
    (S : Submodule ℂ (Lp ℂ 2 μ)) {f : Lp ℂ 2 μ} (hfS : f ∈ S) (hf : f ≠ 0) :
    lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f ∉ Sᗮ := by
  intro hperp
  exact lpBoundedMulCLM_inner_ne_zero_of_strictAccretive
    hφ hC0 hC hacc hδ hne hf
    (Submodule.inner_right_of_mem_orthogonal hfS hperp)

/-- Quantitative leakage floor.  If `p` is any source component whose remainder is orthogonal to
the source subspace, exact accretivity forces `δ ‖T f‖² ≤ ‖f‖ ‖p‖`.  Taking `p` to be the
orthogonal projection gives the sharp fixed-source obstruction used downstream. -/
theorem lpBoundedMulCLM_sourceComponent_lower_bound
    (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hacc : ∀ x, (φ x).re = δ * Complex.normSq (φ x))
    (S : Submodule ℂ (Lp ℂ 2 μ)) {f p : Lp ℂ 2 μ}
    (hfS : f ∈ S)
    (hperp : lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f - p ∈ Sᗮ) :
    δ * ‖lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f‖ ^ 2 ≤
      ‖f‖ * ‖p‖ := by
  let T := lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC
  have hzero : inner ℂ f (T f - p) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hfS hperp
  have heq : inner ℂ f (T f) = inner ℂ f p := by
    rw [inner_sub_right] at hzero
    exact sub_eq_zero.mp hzero
  calc
    δ * ‖T f‖ ^ 2 = (inner ℂ f (T f)).re :=
      (lpBoundedMulCLM_re_inner_eq hφ hC0 hC hacc f).symm
    _ = (inner ℂ f p).re := congrArg Complex.re heq
    _ ≤ |(inner ℂ f p).re| := le_abs_self _
    _ ≤ ‖inner ℂ f p‖ := Complex.abs_re_le_norm _
    _ ≤ ‖f‖ * ‖p‖ := norm_inner_le_norm _ _

end GaloisForLFunctions.HTGeometry
