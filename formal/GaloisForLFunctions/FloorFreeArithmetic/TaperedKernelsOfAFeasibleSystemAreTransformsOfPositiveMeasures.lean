import GaloisForLFunctions.FloorFreeArithmetic.FeasibleSystemsArePositiveDefiniteOnIntervals
import GaloisForLFunctions.HTGeometry.BochnerPositiveDefiniteReal

/-!
# Tapered kernels of a feasible system are transforms of positive measures

A weight system feasible at an aperture has spectral kernels that are positive definite on
intervals. A kernel `K` positive definite on the nodes of `[−r, r]` need not be positive
definite on the line, but its product with a taper is: for `φ` supported in `[−r, r]` and
`T = φ ⋆ φ̃` its autocorrelation,

`Σ c̄_i c_j K(t_j − t_i) T(t_j − t_i) = ∫ Σ d̄_i(x) d_j(x) K(t_j − t_i) dx`,
`d_j(x) = c_j conj φ(x − t_j)`,

and for each `x` only the nodes within `r` of `x` enter, which form an admissible node set
after translation by `x`. So `K · T` is positive definite on the line, and by Bochner's theorem
it is the Fourier transform of a finite positive measure.

Hence feasibility at an aperture is a statement about positive measures, with no extension
theorem: for every test and every taper that the aperture admits, the tapered spectral kernel
is the characteristic function of a finite positive measure; and conversely such a measure for
one nonzero taper gives the sign of the Weil form on the test.

* `positiveDefiniteOnReal_mul_weilTest`: a kernel positive definite on an interval, times a
  taper, is positive definite on the line.
* `exists_measure_charFun_eq_taperedKernel`: the measure of a feasible system, a test and a
  taper.
* `re_weilFullFunctional_nonneg_of_charFun_taperedKernel`: the converse on one test.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate
open Zeta23

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open ArithmeticOfSquareRootPrecision
open _root_.RHTower _root_.RHTower.WeilSpectral

/-- The autocorrelation of a function at `0` is its square norm. -/
theorem weilTest_self_zero (φ : ℝ → ℂ) :
    EF.weilTest φ φ 0 = ((∫ x, ‖φ x‖ ^ 2 : ℝ) : ℂ) := by
  rw [WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show φ x * conj (φ (x - 0)) = ((‖φ x‖ ^ 2 : ℝ) : ℂ)
  rw [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **A kernel positive definite on an interval, times a taper, is positive definite on the
line.** The taper is the autocorrelation of a continuous function supported in `[−r, r]`. -/
theorem positiveDefiniteOnReal_mul_weilTest {K : ℝ → ℂ} {r : ℝ}
    (hK : PositiveDefiniteOnNodes K r) {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hφs : tsupport φ ⊆ Icc (-r) r) :
    HTGeometry.PositiveDefiniteOnReal fun y => K y * EF.weilTest φ φ y := by
  intro N t c
  show ∃ ρ : ℝ, 0 ≤ ρ ∧
    ∑ i, ∑ j, star (c i) * (K (t j - t i) * EF.weilTest φ φ (t j - t i)) * c j = (ρ : ℂ)
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport φ).trans hφs)
  -- `φ` vanishes outside `[−r, r]`
  have hφ0 : ∀ x, r < |x| → φ x = 0 := by
    intro x hx
    by_contra hne
    exact absurd (abs_le.mpr (hφs (subset_tsupport φ hne))) (not_le.mpr hx)
  -- products of two translates of `φ` are integrable
  obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuous hφ
  have hpair : ∀ a b : ℝ, Integrable fun x => φ (x - a) * conj (φ (x - b)) := by
    intro a b
    have hc : Continuous fun x => φ (x - a) * conj (φ (x - b)) :=
      (hφ.comp (continuous_id.sub continuous_const)).mul
        (Complex.continuous_conj.comp (hφ.comp (continuous_id.sub continuous_const)))
    have hint : Integrable fun x => C * ‖φ (x - a)‖ :=
      ((hφ.integrable_of_hasCompactSupport hφc).comp_sub_right a).norm.const_mul C
    refine hint.mono' hc.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [norm_mul, RCLike.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  -- the taper at a difference of nodes, as an integral in a common variable
  have htap : ∀ i j, EF.weilTest φ φ (t j - t i) = ∫ x, φ (x - t i) * conj (φ (x - t j)) := by
    intro i j
    rw [WeilSpectral.weilTest_apply,
      ← integral_sub_right_eq_self (fun u => φ u * conj (φ (u - (t j - t i)))) (t i)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show φ (x - t i) * conj (φ (x - t i - (t j - t i))) = φ (x - t i) * conj (φ (x - t j))
    rw [show x - t i - (t j - t i) = x - t j by ring]
  -- each term of the Gram form is an integral
  have hterm : ∀ i j, star (c i) * (K (t j - t i) * EF.weilTest φ φ (t j - t i)) * c j =
      ∫ x, star (c i * conj (φ (x - t i))) * K (t j - t i) * (c j * conj (φ (x - t j))) := by
    intro i j
    rw [htap i j, show star (c i) * (K (t j - t i) * ∫ x, φ (x - t i) * conj (φ (x - t j))) *
      c j = (star (c i) * K (t j - t i) * c j) * ∫ x, φ (x - t i) * conj (φ (x - t j)) by ring,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Complex.star_def, map_mul, Complex.conj_conj]
    ring
  have hint : ∀ i j, Integrable fun x =>
      star (c i * conj (φ (x - t i))) * K (t j - t i) * (c j * conj (φ (x - t j))) := by
    intro i j
    refine ((hpair (t i) (t j)).const_mul (star (c i) * K (t j - t i) * c j)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Complex.star_def, map_mul, Complex.conj_conj]
    ring
  -- the Gram form is the integral of the pointwise Gram forms
  have hsum : ∑ i, ∑ j, star (c i) * (K (t j - t i) * EF.weilTest φ φ (t j - t i)) * c j =
      ∫ x, ∑ i, ∑ j,
        star (c i * conj (φ (x - t i))) * K (t j - t i) * (c j * conj (φ (x - t j))) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  -- each pointwise Gram form is a nonnegative real: its nodes lie within `r` of `x`
  have hgx : ∀ x : ℝ, ∃ ρ : ℝ, 0 ≤ ρ ∧ (∑ i, ∑ j,
      star (c i * conj (φ (x - t i))) * K (t j - t i) * (c j * conj (φ (x - t j)))) = (ρ : ℂ) := by
    intro x
    by_cases hr : 0 ≤ r
    · obtain ⟨ρ, hρ, hGram⟩ := hK N (fun j => if |t j - x| ≤ r then t j - x else 0)
        (fun j => c j * conj (φ (x - t j))) (fun j => by
          split_ifs with h
          · exact h
          · rw [abs_zero]
            exact hr)
      refine ⟨ρ, hρ, ?_⟩
      rw [← hGram]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hi : |t i - x| ≤ r
      · by_cases hj : |t j - x| ≤ r
        · simp only [if_pos hi, if_pos hj]
          rw [show t j - x - (t i - x) = t j - t i by ring]
        · have hz : φ (x - t j) = 0 := hφ0 _ (by rw [abs_sub_comm]; exact not_le.mp hj)
          simp only [hz, map_zero, mul_zero]
      · have hz : φ (x - t i) = 0 := hφ0 _ (by rw [abs_sub_comm]; exact not_le.mp hi)
        simp only [hz, map_zero, mul_zero, star_zero, zero_mul]
    · have hz : ∀ y, φ y = 0 := fun y => hφ0 y (lt_of_lt_of_le (not_le.mp hr) (abs_nonneg y))
      refine ⟨0, le_rfl, ?_⟩
      simp only [hz, map_zero, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero]
  -- conclusion
  have hre : ∀ x : ℝ, (∑ i, ∑ j,
      star (c i * conj (φ (x - t i))) * K (t j - t i) * (c j * conj (φ (x - t j)))) =
      (((∑ i, ∑ j, star (c i * conj (φ (x - t i))) * K (t j - t i) *
        (c j * conj (φ (x - t j)))).re : ℝ) : ℂ) := by
    intro x
    obtain ⟨ρ, -, h⟩ := hgx x
    rw [h, Complex.ofReal_re]
  have hnn : ∀ x : ℝ, 0 ≤ (∑ i, ∑ j,
      star (c i * conj (φ (x - t i))) * K (t j - t i) * (c j * conj (φ (x - t j)))).re := by
    intro x
    obtain ⟨ρ, hρ, h⟩ := hgx x
    rw [h, Complex.ofReal_re]
    exact hρ
  refine ⟨∫ x, (∑ i, ∑ j, star (c i * conj (φ (x - t i))) * K (t j - t i) *
    (c j * conj (φ (x - t j)))).re, integral_nonneg hnn, ?_⟩
  rw [hsum, ← integral_complex_ofReal]
  exact integral_congr_ae (Eventually.of_forall hre)

/-- **The measure of a feasible system, a test and a taper.** Let `λ` be feasible at the
aperture `A`, `f` a test supported in `[−A', A']`, `A' ≤ A`, and `φ` a taper supported in
`[−(A − A'), A − A']`. Then the tapered spectral kernel `y ↦ K_f(y) (φ ⋆ φ̃)(y)` is the
characteristic function of a finite positive measure. -/
theorem exists_measure_charFun_eq_taperedKernel {A A' : ℝ} {lam : ℕ → ℝ}
    (hpos : AperturePositive A lam) (hA : A' ≤ A) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-A') A') {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hφs : tsupport φ ⊆ Icc (-(A - A')) (A - A')) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ y, charFun ν y = spectralKernel lam f y * EF.weilTest φ φ y := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport φ).trans hφs)
  have hK := (aperturePositive_iff_spectralKernel_positiveDefiniteOnNodes A lam).mp hpos A' hA
    f hf hfs
  have hcont : Continuous fun y => spectralKernel lam f y * EF.weilTest φ φ y :=
    (continuous_spectralKernel lam (admissible_weilTest hf hfc)).mul
      (EF.weilTest_contDiff hφ hφ.continuous hφc).continuous
  exact HTGeometry.exists_charFun_eq_of_positiveDefinite
    (positiveDefiniteOnReal_mul_weilTest hK hφ.continuous hφs) hcont

/-- **Conversely**, a measure for one nonzero taper gives the sign of the Weil form on the
test. -/
theorem re_weilFullFunctional_nonneg_of_charFun_taperedKernel {lam : ℕ → ℝ} {f φ : ℝ → ℂ}
    {ν : Measure ℝ} (hν : ∀ y, charFun ν y = spectralKernel lam f y * EF.weilTest φ φ y)
    (hφ : 0 < ∫ x, ‖φ x‖ ^ 2) :
    0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re := by
  have h0 : spectralKernel lam f 0 = weilFullFunctional lam (EF.weilTest f f) := by
    rw [spectralKernel]
    congr 1
    funext x
    simp [transl]
  have h := hν 0
  rw [charFun_zero, h0, weilTest_self_zero] at h
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re, Complex.re_mul_ofReal] at hre
  have hmass : 0 ≤ ν.real Set.univ := measureReal_nonneg
  rw [hre] at hmass
  exact nonneg_of_mul_nonneg_left hmass hφ

end GaloisForLFunctions.FloorFreeArithmetic
