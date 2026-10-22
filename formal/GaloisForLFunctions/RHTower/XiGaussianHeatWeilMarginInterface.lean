import GaloisForLFunctions.RHTower.XiGaussianHeatPhysicalRealForm
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundEnergy
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMMixedScrewWeilBridge
import GaloisForLFunctions.RHTower.XiResolventMassBudget

/-!
# The restricted Weil form on real even sources, and a smooth even cutoff

**Real even sources** (`ccmRestrictedWeilSourceQuadratic_realEven`).  For a real-valued even
smooth source `u` with compact support in `(−A, A)`, the restricted Weil quadratic form is the zero
sum of squares `Re Σ_q F_u(z_q)²`, `F_u(z) = ∫ u(x) e^{ixz} dx`.  Its pole coefficients are the
exponential moments `∫ e^{±x/2} u` (`inner_ccmPolarApertureVector_realSource`), and its aperture
norm is the `L²` norm of `u` (`norm_sq_ccmArchimedeanFormToAperture_realSource`).

**Comparison of zero sums of squares** (`re_tsum_sq_le_of_strip`).  If `|z_q| |G_q| ≤ M` and
`|z_q| |G_q − F_q| ≤ ρ` for every zero copy, then
`Re Σ F_q² ≤ Re Σ G_q² + (2Mρ + ρ²) Σ_q |z_q|^{-2}`.

**The cutoff** (`heatCutoff`).  `χ(x) = σ((B₁² − x²)/(B₁² − B₀²))` with the smooth transition `σ`
is smooth, even, `[0, 1]`-valued, `1` on `|x| ≤ B₀` and `0` on `|x| ≥ B₁`.
-/

open scoped Real
open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-! ## The smooth even cutoff -/

/-- The smooth even cutoff `σ((B₁² − x²)/(B₁² − B₀²))`. -/
def heatCutoff (B₀ B₁ x : ℝ) : ℝ := Real.smoothTransition ((B₁ ^ 2 - x ^ 2) / (B₁ ^ 2 - B₀ ^ 2))

variable {B₀ B₁ : ℝ}

theorem contDiff_heatCutoff (B₀ B₁ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (heatCutoff B₀ B₁) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_id.pow 2)).div_const _)

theorem heatCutoff_nonneg (x : ℝ) : 0 ≤ heatCutoff B₀ B₁ x := Real.smoothTransition.nonneg _

theorem heatCutoff_le_one (x : ℝ) : heatCutoff B₀ B₁ x ≤ 1 := Real.smoothTransition.le_one _

theorem heatCutoff_neg (x : ℝ) : heatCutoff B₀ B₁ (-x) = heatCutoff B₀ B₁ x := by
  simp only [heatCutoff, neg_sq]

theorem heatCutoff_eq_one (h0 : 0 ≤ B₀) (h01 : B₀ < B₁) {x : ℝ} (hx : |x| ≤ B₀) :
    heatCutoff B₀ B₁ x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hd : 0 < B₁ ^ 2 - B₀ ^ 2 := by nlinarith
  rw [le_div_iff₀ hd]
  have : x ^ 2 ≤ B₀ ^ 2 := by
    have := abs_nonneg x
    nlinarith [sq_abs x]
  linarith

theorem heatCutoff_eq_zero (h0 : 0 ≤ B₀) (h01 : B₀ < B₁) {x : ℝ} (hx : B₁ ≤ |x|) :
    heatCutoff B₀ B₁ x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hd : 0 < B₁ ^ 2 - B₀ ^ 2 := by nlinarith
  apply div_nonpos_of_nonpos_of_nonneg _ hd.le
  have : B₁ ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x]
  linarith

theorem support_heatCutoff_subset (h0 : 0 ≤ B₀) (h01 : B₀ < B₁) :
    Function.support (heatCutoff B₀ B₁) ⊆ Ioo (-B₁) B₁ := by
  intro x hx
  by_contra hmem
  apply hx
  apply heatCutoff_eq_zero h0 h01
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hmem
  rcases hmem with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; exact h

theorem tsupport_heatCutoff_subset (h0 : 0 ≤ B₀) (h01 : B₀ < B₁) :
    tsupport (heatCutoff B₀ B₁) ⊆ Icc (-B₁) B₁ :=
  closure_minimal ((support_heatCutoff_subset h0 h01).trans Ioo_subset_Icc_self) isClosed_Icc

theorem hasCompactSupport_heatCutoff (h0 : 0 ≤ B₀) (h01 : B₀ < B₁) :
    HasCompactSupport (heatCutoff B₀ B₁) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx =>
    Function.notMem_support.1 fun h => hx (Ioo_subset_Icc_self (support_heatCutoff_subset h0 h01 h))

theorem hasDerivAt_heatCutoff (x : ℝ) :
    HasDerivAt (heatCutoff B₀ B₁) (deriv (heatCutoff B₀ B₁) x) x :=
  ((contDiff_heatCutoff B₀ B₁).differentiable (by simp)).differentiableAt.hasDerivAt

theorem continuous_deriv_heatCutoff : Continuous (deriv (heatCutoff B₀ B₁)) :=
  (contDiff_heatCutoff B₀ B₁).continuous_deriv (by simp)

theorem deriv_heatCutoff_eq_zero (h0 : 0 ≤ B₀) (h01 : B₀ < B₁) {x : ℝ} (hx : |x| < B₀) :
    deriv (heatCutoff B₀ B₁) x = 0 := by
  have hev : heatCutoff B₀ B₁ =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    have hopen : IsOpen {y : ℝ | |y| < B₀} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact heatCutoff_eq_one h0 h01 (le_of_lt hy)
  rw [hev.deriv_eq, deriv_const]

theorem hasCompactSupport_deriv_heatCutoff (h0 : 0 ≤ B₀) (h01 : B₀ < B₁) :
    HasCompactSupport (deriv (heatCutoff B₀ B₁)) :=
  (hasCompactSupport_heatCutoff h0 h01).deriv

theorem exists_bound_deriv_heatCutoff (h0 : 0 ≤ B₀) (h01 : B₀ < B₁) :
    ∃ C, 0 ≤ C ∧ ∀ x, |deriv (heatCutoff B₀ B₁) x| ≤ C := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_deriv_heatCutoff h0 h01).exists_bound_of_continuous
    continuous_deriv_heatCutoff
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun x => by simpa using hC x⟩

/-! ## Real even sources -/

theorem heatStripTransform_neg_of_even {f : ℝ → ℂ} (hf : ∀ x, f (-x) = f x) (z : ℂ) :
    heatStripTransform f (-z) = heatStripTransform f z := by
  unfold heatStripTransform
  rw [← integral_neg_eq_self]
  congr 1
  funext x
  rw [hf]
  push_cast
  ring_nf

/-- A real even smooth function with compact support inside `(−A, A)` as a source. -/
def realEvenSource (A : SuzukiPositiveAperture) (u : ℝ → ℝ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) (hsupp : tsupport u ⊆ Ioo (-A.1) A.1) :
    CCMComplexSmoothInteriorSource A where
  toFun x := (u x : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp hsmooth
  hasCompactSupport := hcpt.comp_left Complex.ofReal_zero
  tsupport_subset := by
    refine (tsupport_comp_subset Complex.ofReal_zero u).trans hsupp

variable {A : SuzukiPositiveAperture} {u : ℝ → ℝ} {hsmooth : ContDiff ℝ (⊤ : ℕ∞) u}
  {hcpt : HasCompactSupport u} {hsupp : tsupport u ⊆ Ioo (-A.1) A.1}

/-- **The restricted Weil form of a real even source is a zero sum of squares.** -/
theorem ccmRestrictedWeilSourceQuadratic_realEven (heven : ∀ x, u (-x) = u x) :
    ccmRestrictedWeilSourceQuadratic A (realEvenSource A u hsmooth hcpt hsupp).toCCMFormVector =
      (∑' q : XiZeroCopy, heatStripTransform (fun x => (u x : ℂ)) (xiSpectralPoint q) ^ 2).re := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source,
    ccmRestrictedWeilForm_complexSmooth_eq_suzukiWeilDistribution,
    suzukiWeilDistribution_hermitianConvolution A.2.le]
  congr 1
  refine tsum_congr fun q => ?_
  have h1 : suzukiSmoothFourier (realEvenSource A u hsmooth hcpt hsupp).toSuzukiSmoothCompactTest
      (-xiSpectralPoint q) = heatStripTransform (fun x => (u x : ℂ)) (xiSpectralPoint q) := by
    change heatStripTransform (fun x => (u x : ℂ)) (-xiSpectralPoint q) = _
    exact heatStripTransform_neg_of_even (fun x => by simp only [heven]) _
  have h2 : suzukiSmoothFourier
      (realEvenSource A u hsmooth hcpt hsupp).toSuzukiSmoothCompactTest.conjugate
      (xiSpectralPoint q) = heatStripTransform (fun x => (u x : ℂ)) (xiSpectralPoint q) := by
    unfold suzukiSmoothFourier heatStripTransform
    congr 1
    funext x
    rw [SuzukiSmoothCompactTest.coe_conjugate]
    change (starRingEnd ℂ) ((u x : ℂ)) * _ = _
    rw [Complex.conj_ofReal]
  rw [h1, h2, sq]

/-- The pole coefficients of a real source are its exponential moments. -/
theorem inner_ccmPolarApertureVector_realSource (s : ℝ) :
    inner ℂ (ccmPolarApertureVector A s)
        (ccmArchimedeanFormToAperture A (realEvenSource A u hsmooth hcpt hsupp).toCCMFormVector) =
      ((∫ x, Real.exp (s * x) * u x : ℝ) : ℂ) := by
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector, ← integral_complex_ofReal]
  congr 1
  funext x
  push_cast
  rfl

/-- **Pole vanishing of an even real source.**  One exponential moment suffices. -/
theorem isPolarConstrained_realEven (heven : ∀ x, u (-x) = u x)
    (hmom : ∫ x, Real.exp (x / 2) * u x = 0) :
    IsPolarConstrained A (realEvenSource A u hsmooth hcpt hsupp).toCCMFormVector := by
  have hplus : ∫ x, Real.exp (1 / 2 * x) * u x = 0 := by
    rw [← hmom]; congr 1; funext x; ring_nf
  have hminus : ∫ x, Real.exp (-1 / 2 * x) * u x = 0 := by
    rw [← hplus, ← integral_neg_eq_self]
    congr 1
    funext x
    rw [heven]
    ring_nf
  refine ⟨?_, ?_⟩
  · rw [inner_ccmPolarApertureVector_realSource, hplus, Complex.ofReal_zero]
  · rw [inner_ccmPolarApertureVector_realSource, hminus, Complex.ofReal_zero]

theorem sq_norm_soninL2_of_ae_eq {f : SoninL2} {h : ℝ → ℂ} (hf : (f : ℝ → ℂ) =ᵐ[volume] h) :
    ‖f‖ ^ 2 = ∫ x, ‖h x‖ ^ 2 := by
  have hinner : (inner ℂ f f : ℂ) = ((∫ x, ‖h x‖ ^ 2 : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hf] with x hx
    rw [hx, RCLike.inner_apply, Complex.mul_conj']
    push_cast
    ring
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hre := congrArg Complex.re hinner
  simpa [← Complex.ofReal_pow] using hre

/-- The aperture norm of a real source is its `L²` norm. -/
theorem sq_norm_ccmArchimedeanFormToAperture_realSource :
    ‖ccmArchimedeanFormToAperture A (realEvenSource A u hsmooth hcpt hsupp).toCCMFormVector‖ ^ 2 =
      ∫ x, u x ^ 2 := by
  rw [Submodule.coe_norm,
    sq_norm_soninL2_of_ae_eq (realEvenSource A u hsmooth hcpt hsupp).toCCMFormVector_physical_coeFn]
  congr 1
  funext x
  change ‖((u x : ℝ) : ℂ)‖ ^ 2 = _
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## Comparison of zero sums of squares -/

/-- **Comparison.**  `Re Σ F_q² ≤ Re Σ G_q² + (2Mρ + ρ²) Σ_q |z_q|^{-2}` when `|z_q| |G_q| ≤ M` and
`|z_q| |G_q − F_q| ≤ ρ`. -/
theorem re_tsum_sq_le_of_strip {G F : XiZeroCopy → ℂ} {M ρ : ℝ}
    (hG : ∀ q, ‖xiSpectralPoint q‖ * ‖G q‖ ≤ M) (hR : ∀ q, ‖xiSpectralPoint q‖ * ‖G q - F q‖ ≤ ρ) :
    (∑' q, F q ^ 2).re ≤
      (∑' q, G q ^ 2).re + (2 * M * ρ + ρ ^ 2) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  have hpos : ∀ q, 0 < ‖xiSpectralPoint q‖ := fun q => norm_pos_iff.2 (xiSpectralPoint_ne_zero q)
  have hM : 0 ≤ M := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hG (Classical.arbitrary _))
  have hρ : 0 ≤ ρ := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hR (Classical.arbitrary _))
  have hS := xiSpectralPoint_inv_sq_summable
  have hGb : ∀ q, ‖G q‖ ≤ M / ‖xiSpectralPoint q‖ := fun q => by
    rw [le_div_iff₀ (hpos q), mul_comm]; exact hG q
  have hRb : ∀ q, ‖G q - F q‖ ≤ ρ / ‖xiSpectralPoint q‖ := fun q => by
    rw [le_div_iff₀ (hpos q), mul_comm]; exact hR q
  have hdiff : ∀ q, ‖F q ^ 2 - G q ^ 2‖ ≤ (2 * M * ρ + ρ ^ 2) * (1 / ‖xiSpectralPoint q‖ ^ 2) :=
    fun q => by
    have e : F q ^ 2 - G q ^ 2 = -(G q - F q) * (2 * G q - (G q - F q)) := by ring
    rw [e, norm_mul, norm_neg]
    have h2 : ‖2 * G q - (G q - F q)‖ ≤ (2 * M + ρ) / ‖xiSpectralPoint q‖ := by
      calc ‖2 * G q - (G q - F q)‖ ≤ ‖2 * G q‖ + ‖G q - F q‖ := norm_sub_le _ _
        _ = 2 * ‖G q‖ + ‖G q - F q‖ := by rw [norm_mul]; norm_num
        _ ≤ 2 * (M / ‖xiSpectralPoint q‖) + ρ / ‖xiSpectralPoint q‖ := by
            gcongr; exacts [hGb q, hRb q]
        _ = (2 * M + ρ) / ‖xiSpectralPoint q‖ := by ring
    calc ‖G q - F q‖ * ‖2 * G q - (G q - F q)‖
        ≤ ρ / ‖xiSpectralPoint q‖ * ((2 * M + ρ) / ‖xiSpectralPoint q‖) :=
          mul_le_mul (hRb q) h2 (norm_nonneg _) (by positivity)
      _ = (2 * M * ρ + ρ ^ 2) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring
  have hGs : Summable (fun q => G q ^ 2) := by
    refine Summable.of_norm_bounded (hS.mul_left (M ^ 2)) fun q => ?_
    rw [norm_pow]
    calc ‖G q‖ ^ 2 ≤ (M / ‖xiSpectralPoint q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hGb q) 2
      _ = M ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring
  have hDs : Summable (fun q => F q ^ 2 - G q ^ 2) :=
    Summable.of_norm_bounded (hS.mul_left _) hdiff
  have hFs : Summable (fun q => F q ^ 2) := by
    have := hDs.add hGs
    simpa using this
  have hsplit : (∑' q, F q ^ 2) = (∑' q, (F q ^ 2 - G q ^ 2)) + ∑' q, G q ^ 2 := by
    rw [← hDs.tsum_add hGs]
    congr 1
    funext q
    ring
  rw [hsplit, Complex.add_re]
  have hre : (∑' q, (F q ^ 2 - G q ^ 2)).re ≤
      ∑' q, (2 * M * ρ + ρ ^ 2) * (1 / ‖xiSpectralPoint q‖ ^ 2) :=
    (Complex.re_le_norm _).trans ((norm_tsum_le_tsum_norm hDs.norm).trans
      (hDs.norm.tsum_le_tsum hdiff (hS.mul_left _)))
  rw [tsum_mul_left] at hre
  linarith

end

end RHTower
