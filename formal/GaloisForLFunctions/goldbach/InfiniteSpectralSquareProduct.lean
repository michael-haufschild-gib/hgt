import GaloisForLFunctions.goldbach.SpectralSquareProduct
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.LpDiagonalOperator
import GaloisForLFunctions.RHTower.PrimeIndexedRVMSourceUnitaryNoGo
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

The associated diagonal operator is symmetric and Hilbert--Schmidt. The
product equals the existing entire regularized determinant of its scaled
squared spectrum, after removing the exponential trace correction.
-/

namespace GaloisForLFunctions.Goldbach

open Filter Set
open scoped Topology Classical

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

/-- On compact sets, spectral factors have a common summable majorant. -/
theorem infiniteSpectralSquareProduct_hasProdLocallyUniformlyOn
    (μ : lp (fun _ : ι => ℝ) 2) :
    HasProdLocallyUniformlyOn (fun i z => spectralSquareFactor (μ i) z)
      (infiniteSpectralSquareProduct μ) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  change HasProdUniformlyOn (fun i z => spectralSquareFactor (μ i) z)
    (fun z => infiniteSpectralSquareProduct μ z) K
  simp only [infiniteSpectralSquareProduct, spectralSquareFactor_eq, sub_eq_add_neg]
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine Summable.hasProdUniformlyOn_one_add
    (f := fun i z => -(4 * (μ i : ℂ) ^ 2 * z * (1 - z))) hK
    ((spectral_sq_summable μ).mul_left (4 * max R 0 * (1 + max R 0)))
    (.of_forall fun i z hz => ?_) (fun i => by fun_prop)
  have hzR : ‖z‖ ≤ max R 0 :=
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hR hz : ‖z‖ ≤ R).trans
      (le_max_left _ _)
  rw [norm_spectral_error]
  have h1 : ‖1 - z‖ ≤ 1 + max R 0 :=
    (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add (le_refl (1 : ℝ)) hzR)
  gcongr

/-- The spectral product is entire, including at repeated and zero spectral values. -/
theorem infiniteSpectralSquareProduct_differentiable (μ : lp (fun _ : ι => ℝ) 2) :
    Differentiable ℂ (infiniteSpectralSquareProduct μ) := by
  rw [← differentiableOn_univ]
  have hf (i : ι) : DifferentiableOn ℂ (fun z => spectralSquareFactor (μ i) z) Set.univ := by
    have he : (fun z => spectralSquareFactor (μ i) z) =
        (fun z => 1 - 4 * (μ i : ℂ) ^ 2 * z * (1 - z)) :=
      funext (spectralSquareFactor_eq (μ i))
    rw [he]
    fun_prop
  exact (infiniteSpectralSquareProduct_hasProdLocallyUniformlyOn μ).differentiableOn
    (.of_forall fun s => by
      simpa only [Finset.prod_fn] using
        DifferentiableOn.finsetProd (fun i (_ : i ∈ s) => hf i)) isOpen_univ

private theorem spectral_coordinate_bound (μ : lp (fun _ : ι => ℝ) 2) (i : ι) :
    ‖(μ i : ℂ)‖ ≤ ‖μ‖ := by
  simpa only [Complex.norm_real] using lp.norm_apply_le_norm (by norm_num) μ i

/-- The actual bounded diagonal operator with the given real square-summable spectrum. -/
def spectralDiagonalOperator (μ : lp (fun _ : ι => ℝ) 2) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  lpDiagonalCLM (fun i => (μ i : ℂ)) (norm_nonneg μ) (spectral_coordinate_bound μ)

/-- The real diagonal makes the operator symmetric for the complex inner product. -/
theorem spectralDiagonalOperator_inner (μ : lp (fun _ : ι => ℝ) 2)
    (f g : lp (fun _ : ι => ℂ) 2) :
    inner ℂ (spectralDiagonalOperator μ f) g = inner ℂ f (spectralDiagonalOperator μ g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [spectralDiagonalOperator, lpDiagonalCLM_apply, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal]
  ring

private theorem spectral_complex_sq_summable (μ : lp (fun _ : ι => ℝ) 2) :
    Summable (fun i => ‖(μ i : ℂ)‖ ^ 2) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using spectral_sq_summable μ

private theorem spectralDiagonalOperator_eq_diagOp [DecidableEq ι]
    (μ : lp (fun _ : ι => ℝ) 2) :
    spectralDiagonalOperator μ =
      HilbertSchmidt.diagOp (fun i => (μ i : ℂ)) (spectral_complex_sq_summable μ) := by
  ext f i
  rw [HilbertSchmidt.diagOp_apply]
  rfl

/-- Square summability supplies the Hilbert--Schmidt property without an extra premise. -/
theorem spectralDiagonalOperator_isHilbertSchmidt (μ : lp (fun _ : ι => ℝ) 2) :
    (spectralDiagonalOperator μ).IsHilbertSchmidt := by
  classical
  rw [spectralDiagonalOperator_eq_diagOp]
  exact HilbertSchmidt.isHilbertSchmidt_diagOp _ _

/-- The Hilbert--Schmidt energy is the sum of the squared real spectral values. -/
theorem hsNormSq_spectralDiagonalOperator (μ : lp (fun _ : ι => ℝ) 2) :
    ContinuousLinearMap.hsNormSq (spectralDiagonalOperator μ) = ∑' i, μ i ^ 2 := by
  classical
  rw [spectralDiagonalOperator_eq_diagOp, HilbertSchmidt.hsNormSq_diagOp]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The operator trace of the square is the complex squared-spectrum sum. -/
theorem opTrace_square_spectralDiagonalOperator (μ : lp (fun _ : ι => ℝ) 2) :
    ContinuousLinearMap.opTrace (spectralDiagonalOperator μ ∘L spectralDiagonalOperator μ) =
      ∑' i, (μ i : ℂ) ^ 2 := by
  simp only [spectralDiagonalOperator_eq_diagOp, HilbertSchmidt.opTrace_diagOp_comp, pow_two]

/-- The spectral bound is exactly contractivity of the diagonal operator. -/
theorem norm_spectralDiagonalOperator_le_one_iff (μ : lp (fun _ : ι => ℝ) 2) :
    ‖spectralDiagonalOperator μ‖ ≤ 1 ↔ ∀ i, μ i ^ 2 ≤ 1 := by
  classical
  constructor
  · intro h i
    have hi := (spectralDiagonalOperator μ).le_opNorm (lp.single 2 i (1 : ℂ))
    rw [spectralDiagonalOperator, lpDiagonalCLM_single,
      lp.norm_single (by norm_num), lp.norm_single (by norm_num), norm_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs] at hi
    exact (sq_le_one_iff_abs_le_one _).mpr (hi.trans h)
  · intro h
    have hb (i : ι) : ‖(μ i : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (sq_le_one_iff_abs_le_one _).mp (h i)
    have he : spectralDiagonalOperator μ =
        lpDiagonalCLM (fun i => (μ i : ℂ)) (by norm_num : (0 : ℝ) ≤ 1) hb := by
      ext f i
      rfl
    rw [he]
    exact norm_lpDiagonalCLM_le _ _ _

/-- Critical-line zeros are equivalent to a norm bound on an actual operator. -/
theorem infiniteSpectralSquareProduct_critical_iff_operator_norm
    (μ : lp (fun _ : ι => ℝ) 2) :
    (∀ z : ℂ, infiniteSpectralSquareProduct μ z = 0 → z.re = 1 / 2) ↔
      ‖spectralDiagonalOperator μ‖ ≤ 1 := by
  rw [infiniteSpectralSquareProduct_critical_iff, norm_spectralDiagonalOperator_le_one_iff]

/-- The scaled squared spectrum appearing in the Fredholm determinant. -/
def spectralSquaredEigenvalue (μ : lp (fun _ : ι => ℝ) 2) (z : ℂ) (i : ι) : ℂ :=
  4 * (μ i : ℂ) ^ 2 * z * (1 - z)

private theorem summable_norm_spectralSquaredEigenvalue
    (μ : lp (fun _ : ι => ℝ) 2) (z : ℂ) :
    Summable (fun i => ‖spectralSquaredEigenvalue μ z i‖) := by
  simpa only [spectralSquaredEigenvalue, norm_neg] using summable_spectral_error μ z

private theorem summable_norm_sq_spectralSquaredEigenvalue
    (μ : lp (fun _ : ι => ℝ) 2) (z : ℂ) :
    Summable (fun i => ‖spectralSquaredEigenvalue μ z i‖ ^ 2) := by
  have hb (i : ι) : ‖spectralSquaredEigenvalue μ z i‖ ≤
      4 * ‖μ‖ ^ 2 * ‖z‖ * ‖1 - z‖ := by
    simp only [spectralSquaredEigenvalue, norm_mul, norm_pow,
      show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num]
    gcongr
    exact spectral_coordinate_bound μ i
  exact ((summable_norm_spectralSquaredEigenvalue μ z).mul_left
    (4 * ‖μ‖ ^ 2 * ‖z‖ * ‖1 - z‖)).of_nonneg_of_le (fun i => sq_nonneg _) fun i => by
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_right (hb i) (norm_nonneg (spectralSquaredEigenvalue μ z i))

/-- The literal diagonal kernel of the scaled squared spectrum. -/
def spectralSquaredKernel (μ : lp (fun _ : ι => ℝ) 2) (z : ℂ) : ι × ι → ℂ :=
  HilbertSchmidt.diagMul (spectralSquaredEigenvalue μ z)

/-- The squared spectral kernel belongs to the existing Hilbert--Schmidt determinant domain. -/
theorem spectralSquaredKernel_isHS (μ : lp (fun _ : ι => ℝ) 2) (z : ℂ) :
    HilbertSchmidt.IsHS (spectralSquaredKernel μ z) :=
  HilbertSchmidt.isHS_diagMul_of_summable (summable_norm_sq_spectralSquaredEigenvalue μ z)

/-- The spectral product is the existing regularized determinant with its trace correction removed. -/
theorem infiniteSpectralSquareProduct_eq_normalizedDet2
    (μ : lp (fun _ : ι => ℝ) 2) (z : ℂ) :
    infiniteSpectralSquareProduct μ z =
      GaloisForLFunctions.HTGeometry.entireDet2 (spectralSquaredKernel μ z) 1 *
        Complex.exp (-(∑' i, spectralSquaredEigenvalue μ z i)) := by
  have hs := (summable_norm_spectralSquaredEigenvalue μ z).of_norm
  have hp : HasProd (fun i => 1 - spectralSquaredEigenvalue μ z i)
      (infiniteSpectralSquareProduct μ z) := by
    simpa only [infiniteSpectralSquareProduct, spectralSquareFactor_eq,
      spectralSquaredEigenvalue] using (infiniteSpectralSquareProduct_multipliable μ z).hasProd
  have he : HasProd (fun i => Complex.exp (spectralSquaredEigenvalue μ z i))
      (Complex.exp (∑' i, spectralSquaredEigenvalue μ z i)) := by
    simpa only [Function.comp_def] using! hs.hasSum.cexp
  have hprod := hp.mul he
  rw [spectralSquaredKernel, RHTower.entireDet2_diagMul_one_eq_tprod
    (spectralSquaredEigenvalue μ z) (summable_norm_sq_spectralSquaredEigenvalue μ z)
    hprod.multipliable, hprod.tprod_eq, mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, mul_one]

end

end GaloisForLFunctions.Goldbach
