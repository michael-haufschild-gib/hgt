import GaloisForLFunctions.goldbach.SpectralSquareProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Entire products of square-summable spectral values

For an actual real `ℓ²` vector, the Li--Liu spectral-square factors form a
locally uniformly convergent entire product. Absolute summability of the
factor errors rules out extra zeros from the infinite limit. Consequently
the critical-line criterion remains exactly the coordinatewise spectral
bound, without any finite-rank restriction.
-/

namespace GaloisForLFunctions.Goldbach

open Filter Set
open scoped Topology

noncomputable section

variable {ι : Type*}

private theorem spectral_sq_summable (μ : lp (fun _ : ι => ℝ) 2) :
    Summable (fun i => μ i ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    (lp.hasSum_norm (p := 2) (by norm_num) μ).summable

/-- The entire spectral product for a real square-summable spectrum. -/
def infiniteSpectralSquareProduct (μ : lp (fun _ : ι => ℝ) 2) (z : ℂ) : ℂ :=
  ∏' i, spectralSquareFactor (μ i) z

private theorem norm_spectral_error (μ : ℝ) (z : ℂ) :
    ‖-(4 * (μ : ℂ) ^ 2 * z * (1 - z))‖ =
      (4 * ‖z‖ * ‖1 - z‖) * μ ^ 2 := by
  simp only [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num
  ring

private theorem summable_spectral_error (μ : lp (fun _ : ι => ℝ) 2) (z : ℂ) :
    Summable (fun i => ‖-(4 * (μ i : ℂ) ^ 2 * z * (1 - z))‖) := by
  simp_rw [norm_spectral_error]
  exact (spectral_sq_summable μ).mul_left _

/-- Absolute convergence of the factor errors gives convergence at every point. -/
theorem infiniteSpectralSquareProduct_multipliable
    (μ : lp (fun _ : ι => ℝ) 2) (z : ℂ) :
    Multipliable (fun i => spectralSquareFactor (μ i) z) := by
  simpa only [spectralSquareFactor_eq, sub_eq_add_neg] using
    Complex.multipliable_one_add_of_summable (summable_spectral_error μ z).of_norm

/-- An infinite spectral product vanishes precisely at a zero of one of its factors. -/
theorem infiniteSpectralSquareProduct_eq_zero_iff
    (μ : lp (fun _ : ι => ℝ) 2) (z : ℂ) :
    infiniteSpectralSquareProduct μ z = 0 ↔ ∃ i, spectralSquareFactor (μ i) z = 0 := by
  constructor
  · intro hz
    by_contra hn
    have hne : ∀ i, 1 + -(4 * (μ i : ℂ) ^ 2 * z * (1 - z)) ≠ 0 := by
      intro i hi
      exact hn ⟨i, by simpa only [spectralSquareFactor_eq, sub_eq_add_neg] using hi⟩
    have hprod := tprod_one_add_ne_zero_of_summable hne (summable_spectral_error μ z)
    exact hprod (by simpa only [infiniteSpectralSquareProduct, spectralSquareFactor_eq,
      sub_eq_add_neg] using hz)
  · exact fun hz => tprod_of_exists_eq_zero hz

/-- The exact critical-line spectral criterion survives infinitely many factors. -/
theorem infiniteSpectralSquareProduct_critical_iff (μ : lp (fun _ : ι => ℝ) 2) :
    (∀ z : ℂ, infiniteSpectralSquareProduct μ z = 0 → z.re = 1 / 2) ↔
      ∀ i, μ i ^ 2 ≤ 1 := by
  constructor
  · intro h i
    apply (spectralSquareFactor_critical_iff (μ i)).mp
    intro z hz
    exact h z ((infiniteSpectralSquareProduct_eq_zero_iff μ z).mpr ⟨i, hz⟩)
  · intro h z hz
    obtain ⟨i, hi⟩ := (infiniteSpectralSquareProduct_eq_zero_iff μ z).mp hz
    exact (spectralSquareFactor_critical_iff (μ i)).mpr (h i) z hi

/-- The functional equation holds without any restriction on the size of the spectrum. -/
theorem infiniteSpectralSquareProduct_reflect (μ : lp (fun _ : ι => ℝ) 2) (z : ℂ) :
    infiniteSpectralSquareProduct μ (1 - z) = infiniteSpectralSquareProduct μ z := by
  simp only [infiniteSpectralSquareProduct, spectralSquareFactor_reflect]

/-- Compact sets admit a common summable majorant for all spectral factors. -/
theorem infiniteSpectralSquareProduct_hasProdLocallyUniformlyOn
    (μ : lp (fun _ : ι => ℝ) 2) :
    HasProdLocallyUniformlyOn (fun i z => spectralSquareFactor (μ i) z)
      (infiniteSpectralSquareProduct μ) Set.univ := by
  simp only [infiniteSpectralSquareProduct, spectralSquareFactor_eq, sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine Summable.hasProdUniformlyOn_one_add hK
    ((spectral_sq_summable μ).mul_left (4 * max R 0 * (1 + max R 0)))
    (.of_forall fun i z hz => ?_) (fun i => by fun_prop)
  have hzR : ‖z‖ ≤ max R 0 :=
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hR hz : ‖z‖ ≤ R).trans
      (le_max_left _ _)
  rw [norm_spectral_error]
  have h1 : ‖1 - z‖ ≤ 1 + max R 0 :=
    (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add_left hzR 1)
  gcongr

/-- The spectral product is entire, including at repeated and zero spectral values. -/
theorem infiniteSpectralSquareProduct_differentiable (μ : lp (fun _ : ι => ℝ) 2) :
    Differentiable ℂ (infiniteSpectralSquareProduct μ) := by
  rw [← differentiableOn_univ]
  exact (infiniteSpectralSquareProduct_hasProdLocallyUniformlyOn μ).differentiableOn
    (.of_forall fun s => by
      simpa only [Finset.prod_fn] using
        DifferentiableOn.finsetProd (fun i (_ : i ∈ s) => by
          simp only [spectralSquareFactor_eq]
          fun_prop)) isOpen_univ

end

end GaloisForLFunctions.Goldbach
