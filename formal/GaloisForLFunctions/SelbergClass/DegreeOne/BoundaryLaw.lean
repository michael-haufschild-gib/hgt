import GaloisForLFunctions.SelbergClass.DegreeOne.BoundaryPath
import GaloisForLFunctions.RHTower.SelbergShiftLatticeRegularity
import GaloisForLFunctions.RHTower.SelbergClass.FullConjugate

/-!
# The boundary law of the exponential series at degree one

Let `F` have degree one, conductor `q`, internal shift `θ`, and put `f(z) = Σ a(n) e^{−nz}`.  There is a
constant `C ≠ 0` such that, as `y → 0⁺`,

* `y^{1−iθ} f(y + 2πim/q) → C · ā(m) · m^{−iθ}` for every integer `m ≥ 1`;
* `y^{1−iθ} f(y + iβ) → 0` for every other `β > 0` (`exists_boundary_law`).

So the boundary singularities of `f` on the positive imaginary axis lie on the lattice `(2π/q)ℕ`, and
their strengths are the conjugate coefficients.

**Mechanism.**  Past a far-left line the functional equation turns the Mellin integral of `Γ(u)F(u)` into
`Σ_n ā(n) n^{σ−1} ∫ z^{−u} n^{it} A(t) dt`.  By the symbol law, `A(t)` is
`e^{−πt/2} (q/2π)^{−it} t^{−iθ}` up to a constant, so each integral is a Laplace transform at
`ε + iτₙ`, where `ε = π/2 − arg z` and `τₙ = log(|z|q/2πn)`.  The Abelian limit detects `τₙ = 0`, and
Tannery's theorem passes the limit through the sum over `n`.
-/

noncomputable section

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace GaloisForLFunctions.SelbergClass.DegreeOne

/-! ### Dirichlet data of the reflected series -/

/-- The coefficients `ā(n) n^{σ−1}` of the reflected series on the line `Re u = σ`. -/
def dualCoeff (F : ExtendedSelbergClass) (σ : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (selbergArithmeticFunctionConjugate F.coeff) ((1 - σ : ℝ) : ℂ) n

theorem summable_dualCoeff (F : ExtendedSelbergClass) {σ : ℝ} (hσ : σ < 0) :
    Summable (dualCoeff F σ) := by
  have h : 1 < (star (((1 - σ : ℝ)) : ℂ)).re := by
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_re]
    linarith
  exact lSeriesSummable_conjugate (F.lSeriesSummable _ h)

theorem dualCoeff_zero (F : ExtendedSelbergClass) (σ : ℝ) : dualCoeff F σ 0 = 0 :=
  LSeries.term_zero _ _

theorem dualCoeff_of_ne_zero (F : ExtendedSelbergClass) (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    dualCoeff F σ n = star (F.coeff n) / (n : ℂ) ^ (((1 - σ : ℝ)) : ℂ) := by
  rw [dualCoeff, LSeries.term_of_ne_zero hn]
  rfl

/-- The Dirichlet term at `1 − u` splits off the oscillation `n^{it}`. -/
theorem term_line (f : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    LSeries.term f (1 - linePoint σ t) n =
      LSeries.term f (((1 - σ : ℝ)) : ℂ) n * cexp (I * ((t * Real.log n : ℝ) : ℂ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  have hsplit : 1 - linePoint σ t = (((1 - σ : ℝ)) : ℂ) + (-((t : ℂ) * I)) := by
    simp only [linePoint]
    push_cast
    ring
  rw [hsplit, Complex.cpow_add _ _ hnc]
  have hE : (n : ℂ) ^ (-((t : ℂ) * I)) * cexp (I * ((t * Real.log n : ℝ) : ℂ)) = 1 := by
    rw [Complex.cpow_def_of_ne_zero hnc, ← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast
    ring
  have hEne : (n : ℂ) ^ (-((t : ℂ) * I)) ≠ 0 := left_ne_zero_of_mul_eq_one hE
  have hA : (n : ℂ) ^ (((1 - σ : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnc]
    exact Complex.exp_ne_zero _
  rw [eq_inv_of_mul_eq_one_right hE]
  field_simp

/-- The reflected series on a far-left line. -/
theorem conjReflection_eq_tsum (F : ExtendedSelbergClass) {σ : ℝ} (hσ : σ < 0) (t : ℝ) :
    selbergConjugateReflection F (linePoint σ t) =
      ∑' n, dualCoeff F σ n * cexp (I * ((t * Real.log n : ℝ) : ℂ)) := by
  have hre : 1 < (1 - star (linePoint σ t)).re := by
    simp [linePoint]
    linarith
  have hv : F (1 - star (linePoint σ t)) = LSeries F.coeff (1 - star (linePoint σ t)) :=
    (F.lSeries_eq_value _ hre).symm
  have hconj := lSeries_conjugate F.coeff (1 - linePoint σ t)
  have hstar : star (1 - linePoint σ t) = 1 - star (linePoint σ t) := by simp
  rw [hstar] at hconj
  unfold selbergConjugateReflection
  rw [hv, ← hconj, LSeries]
  exact tsum_congr fun n => term_line _ σ t n

/-- The functional equation in Mellin form, high on a vertical line. -/
theorem gamma_mul_value_eq (F : ExtendedSelbergClass) {σ t : ℝ}
    (ht : F.gammaData.gammaTailHeight < |t|) :
    Complex.Gamma (linePoint σ t) * F (linePoint σ t) =
      F.gammaData.rootNumber * symbol F.gammaData σ t *
        selbergConjugateReflection F (linePoint σ t) := by
  have hreg := F.mem_asymmetricFERegularSet_of_height (sigma := σ) ht
  have h := F.value_eq_raw_asymmetric_factor hreg.1.1 hreg.1.2 hreg.2
  have e : selbergVerticalPoint σ t = linePoint σ t := rfl
  rw [e] at h
  rw [h]
  unfold symbol
  ring

/-! ### Regularity of the symbol -/

theorem continuousAt_Gamma_comp {f : ℝ → ℂ} (hf : Continuous f) {t : ℝ} (him : (f t).im ≠ 0) :
    ContinuousAt (fun t => Complex.Gamma (f t)) t := by
  have hp : ∀ m : ℕ, f t ≠ -(m : ℂ) := by
    intro m h
    apply him
    rw [h]
    simp
  exact ContinuousAt.comp (f := f) (g := Complex.Gamma)
    (Complex.differentiableAt_Gamma _ hp).continuousAt hf.continuousAt

theorem Gamma_ne_zero_of_im_ne_zero {s : ℂ} (him : s.im ≠ 0) : Complex.Gamma s ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m h => him ?_
  rw [h]
  simp

theorem im_pair_ne_zero (G : SelbergGammaData) {σ t : ℝ} (ht : G.verticalTailCondition t)
    (j : Fin G.rank) : ((G.lambda j : ℂ) * linePoint σ t + G.mu j).im ≠ 0 := by
  have h := ht j
  have hl := G.lambda_pos j
  have him : ((G.lambda j : ℂ) * linePoint σ t + G.mu j).im = G.lambda j * t + (G.mu j).im := by
    simp [linePoint]
  rw [him]
  intro h0
  have e : (G.mu j).im = -(G.lambda j * t) := by linarith
  rw [e, abs_neg, abs_mul, abs_of_pos hl] at h
  exact lt_irrefl _ h

theorem im_pair_reflect_ne_zero (G : SelbergGammaData) {σ t : ℝ} (ht : G.verticalTailCondition t)
    (j : Fin G.rank) : ((G.lambda j : ℂ) * (1 - linePoint σ t) + star (G.mu j)).im ≠ 0 := by
  have h := ht j
  have hl := G.lambda_pos j
  have him : ((G.lambda j : ℂ) * (1 - linePoint σ t) + star (G.mu j)).im =
      -(G.lambda j * t + (G.mu j).im) := by
    simp [linePoint]
    ring
  rw [him, neg_ne_zero]
  intro h0
  have e : (G.mu j).im = -(G.lambda j * t) := by linarith
  rw [e, abs_neg, abs_mul, abs_of_pos hl] at h
  exact lt_irrefl _ h

theorem continuous_linePoint (σ : ℝ) : Continuous fun t : ℝ => linePoint σ t := by
  fun_prop

theorem continuousAt_symbol (G : SelbergGammaData) (σ : ℝ) {t : ℝ} (ht0 : t ≠ 0)
    (ht : G.verticalTailCondition t) : ContinuousAt (symbol G σ) t := by
  have hQ : ((G.Q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr G.Q_pos.ne'
  have hL := continuous_linePoint σ
  have h1 : ContinuousAt (fun t : ℝ => Complex.Gamma (linePoint σ t)) t :=
    continuousAt_Gamma_comp hL (by simpa [linePoint] using ht0)
  have h2 : ContinuousAt (fun t : ℝ => (G.Q : ℂ) ^ (1 - linePoint σ t)) t :=
    (Continuous.const_cpow (continuous_const.sub hL) (Or.inl hQ)).continuousAt
  have h3 : ContinuousAt (fun t : ℝ => ∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - linePoint σ t) +
      star (G.mu j))) t :=
    tendsto_finsetProd _ fun j _ => continuousAt_Gamma_comp
      ((continuous_const.mul (continuous_const.sub hL)).add continuous_const)
      (im_pair_reflect_ne_zero G ht j)
  have h4 : ContinuousAt (fun t : ℝ => (G.Q : ℂ) ^ (-linePoint σ t)) t :=
    (Continuous.const_cpow hL.neg (Or.inl hQ)).continuousAt
  have h5 : ContinuousAt (fun t : ℝ => ∏ j, (Complex.Gamma ((G.lambda j : ℂ) * linePoint σ t +
      G.mu j))⁻¹) t :=
    tendsto_finsetProd _ fun j _ => (continuousAt_Gamma_comp
      ((continuous_const.mul hL).add continuous_const) (im_pair_ne_zero G ht j)).inv₀
      (Gamma_ne_zero_of_im_ne_zero (im_pair_ne_zero G ht j))
  have h := h1.mul ((h2.mul h3).mul (h4.mul h5))
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only [symbol, G.gammaFactor_inv_expansion, Pi.mul_apply]

/-! ### The phase-normalized symbol -/

/-- `log (q/2π)`. -/
def condLog (G : SelbergGammaData) : ℝ := Real.log (G.conductor / (2 * π))

/-- The spacing `2π/q` of the boundary lattice. -/
def latticeStep (G : SelbergGammaData) : ℝ := 2 * π / G.conductor

theorem latticeStep_pos (G : SelbergGammaData) : 0 < latticeStep G :=
  div_pos (by positivity) G.conductor_pos

theorem log_latticeStep (G : SelbergGammaData) : Real.log (latticeStep G) = -condLog G := by
  unfold latticeStep condLog
  rw [← inv_div, Real.log_inv]

/-- The symbol with its exponential decay and oscillation removed. -/
def symbolPhase (G : SelbergGammaData) (σ t : ℝ) : ℂ :=
  symbol G σ t * ((Real.exp (π * t / 2) : ℝ) : ℂ) * cexp (I * ((t * condLog G : ℝ) : ℂ)) *
    cexp (I * ((G.internalShift * Real.log t : ℝ) : ℂ))

theorem continuousAt_symbolPhase (G : SelbergGammaData) (σ : ℝ) {t : ℝ} (ht0 : 0 < t)
    (ht : G.verticalTailCondition t) : ContinuousAt (symbolPhase G σ) t := by
  have h1 : ContinuousAt (fun t : ℝ => ((Real.exp (π * t / 2) : ℝ) : ℂ)) t := by fun_prop
  have h2 : ContinuousAt (fun t : ℝ => cexp (I * ((t * condLog G : ℝ) : ℂ))) t := by fun_prop
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0.ne'
  have h3 : ContinuousAt (fun t : ℝ => cexp (I * ((G.internalShift * Real.log t : ℝ) : ℂ))) t :=
    ContinuousAt.cexp (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_const.mul hlog)))
  exact ((continuousAt_symbol G σ ht0.ne' ht).mul h1).mul h2 |>.mul h3

/-- The shift of the wave at `z` against the `n`-th term. -/
def waveShift (G : SelbergGammaData) (z : ℂ) (n : ℕ) : ℝ :=
  Real.log ‖z‖ + condLog G - Real.log n

/-- The Laplace variable `ε + iτₙ`. -/
def wave (G : SelbergGammaData) (z : ℂ) (n : ℕ) : ℂ :=
  (gapAngle z : ℂ) + (waveShift G z n : ℂ) * I

/-- The kernel identity: `z^{−u} n^{it}` times the symbol is a Laplace kernel at `ε + iτₙ`. -/
theorem kernel_identity (G : SelbergGammaData) {σ : ℝ} {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : 0 < t)
    (S : ℂ) (n : ℕ) :
    z ^ (-((σ : ℂ) + (t : ℂ) * I)) * S * cexp (I * ((t * Real.log n : ℝ) : ℂ)) =
      z ^ (-(σ : ℂ)) * (S * ((Real.exp (π * t / 2) : ℝ) : ℂ) * cexp (I * ((t * condLog G : ℝ) : ℂ)) *
        cexp (I * ((G.internalShift * Real.log t : ℝ) : ℂ)) *
        abelKernel G.internalShift (wave G z n) t) := by
  have h1 : z ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      z ^ (-(σ : ℂ)) * cexp (Complex.log z * (-((t : ℂ) * I))) := by
    rw [neg_add, Complex.cpow_add _ _ hz, Complex.cpow_def_of_ne_zero hz (-((t : ℂ) * I))]
  have h2 : (t : ℂ) ^ (-(I * (G.internalShift : ℂ))) =
      cexp ((Real.log t : ℂ) * (-(I * (G.internalShift : ℂ)))) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.ofReal_log ht.le]
  have hexp : cexp (Complex.log z * (-((t : ℂ) * I))) * cexp (I * ((t * Real.log n : ℝ) : ℂ)) =
      ((Real.exp (π * t / 2) : ℝ) : ℂ) * cexp (I * ((t * condLog G : ℝ) : ℂ)) *
        cexp (I * ((G.internalShift * Real.log t : ℝ) : ℂ)) *
        (cexp ((Real.log t : ℂ) * (-(I * (G.internalShift : ℂ)))) *
          cexp (-(wave G z n * (t : ℂ)))) := by
    rw [Complex.ofReal_exp]
    simp only [← Complex.exp_add]
    congr 1
    have hlog : Complex.log z = (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * I := rfl
    unfold wave waveShift gapAngle
    rw [hlog]
    push_cast
    linear_combination (-(Complex.arg z : ℂ) * t) * Complex.I_sq
  unfold abelKernel
  rw [h1, h2]
  linear_combination (z ^ (-(σ : ℂ)) * S) * hexp

/-- The integrand high on the far-left line, as a sum of Laplace kernels over `n`. -/
theorem leftIntegrand_eq_tsum (F : ExtendedSelbergClass) (K : ℕ) {z : ℂ} (hz : z ≠ 0) {t : ℝ}
    (ht : 0 < t) (htail : F.gammaData.gammaTailHeight < |t|) :
    ordinaryMellinIntegrand F 0 z (leftLine K t) =
      ∑' n, F.gammaData.rootNumber * z ^ (-((-(K : ℝ) - 1 / 2 : ℝ) : ℂ)) *
        dualCoeff F (-(K : ℝ) - 1 / 2) n * (symbolPhase F.gammaData (-(K : ℝ) - 1 / 2) t *
          abelKernel F.gammaData.internalShift (wave F.gammaData z n) t) := by
  have hσ : -(K : ℝ) - 1 / 2 < 0 := by
    have := Nat.cast_nonneg (α := ℝ) K
    linarith
  have h0 : ordinaryMellinIntegrand F 0 z (leftLine K t) =
      z ^ (-linePoint (-(K : ℝ) - 1 / 2) t) *
        (Complex.Gamma (linePoint (-(K : ℝ) - 1 / 2) t) * F (linePoint (-(K : ℝ) - 1 / 2) t)) := by
    unfold ordinaryMellinIntegrand
    rw [zero_add]
    rfl
  rw [h0, gamma_mul_value_eq F htail, conjReflection_eq_tsum F hσ]
  rw [← mul_assoc, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hk := kernel_identity F.gammaData (σ := -(K : ℝ) - 1 / 2) hz ht
    (symbol F.gammaData (-(K : ℝ) - 1 / 2) t) n
  unfold symbolPhase
  simp only [linePoint] at *
  linear_combination (F.gammaData.rootNumber * dualCoeff F (-(K : ℝ) - 1 / 2) n) * hk

/-! ### Splitting the far-left integral -/

/-- The phase-normalized symbol cut off below height `T₀`. -/
def profile (G : SelbergGammaData) (σ T₀ t : ℝ) : ℂ := (Ioi T₀).indicator (symbolPhase G σ) t

/-- Below the cutoff the integral is left alone; above it, the functional equation is applied. -/
theorem integral_left_split (F : ExtendedSelbergClass) {K : ℕ} (ha : (-(K : ℝ) - 1 / 2) < -1)
    (haμ : ∀ j, F.gammaData.lambda j * (-(K : ℝ) - 1 / 2) < 1 - (F.gammaData.mu j).re)
    {T₀ R : ℝ} (hT₀ : 0 ≤ T₀) (htail : F.gammaData.gammaTailHeight < T₀)
    (hb : ∀ t, 0 < t → ‖profile F.gammaData (-(K : ℝ) - 1 / 2) T₀ t‖ ≤ R)
    (hm : AEStronglyMeasurable (profile F.gammaData (-(K : ℝ) - 1 / 2) T₀)
      (volume.restrict (Ioi 0))) {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ, ordinaryMellinIntegrand F 0 z (leftLine K t)) =
      (∫ t in Iic T₀, ordinaryMellinIntegrand F 0 z (leftLine K t)) +
        (F.gammaData.rootNumber * z ^ (-((-(K : ℝ) - 1 / 2 : ℝ) : ℂ))) *
          ∑' n, dualCoeff F (-(K : ℝ) - 1 / 2) n *
            abelIntegral (profile F.gammaData (-(K : ℝ) - 1 / 2) T₀) F.gammaData.internalShift
              (wave F.gammaData z n) := by
  have hσ : -(K : ℝ) - 1 / 2 < 0 := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hint := integrable_leftIntegrand F ha haμ hz
  have hsplit := integral_add_compl (measurableSet_Iic (a := T₀)) hint
  rw [compl_Iic] at hsplit
  rw [← hsplit]
  congr 1
  have h1 : ∫ t in Ioi T₀, ordinaryMellinIntegrand F 0 z (leftLine K t) =
      ∫ t in Ioi (0 : ℝ), (Ioi T₀).indicator
        (fun t => ordinaryMellinIntegrand F 0 z (leftLine K t)) t := by
    rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi hT₀)]
  rw [h1]
  let Φ : ℕ → ℝ → ℂ := fun n t => F.gammaData.rootNumber * z ^ (-((-(K : ℝ) - 1 / 2 : ℝ) : ℂ)) *
    dualCoeff F (-(K : ℝ) - 1 / 2) n * (profile F.gammaData (-(K : ℝ) - 1 / 2) T₀ t *
      abelKernel F.gammaData.internalShift (wave F.gammaData z n) t)
  have h2 : ∫ t in Ioi (0 : ℝ), (Ioi T₀).indicator
      (fun t => ordinaryMellinIntegrand F 0 z (leftLine K t)) t =
      ∫ t in Ioi (0 : ℝ), ∑' n, Φ n t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    by_cases htT : t ∈ Ioi T₀
    · have htT' : T₀ < t := htT
      rw [indicator_of_mem htT]
      rw [leftIntegrand_eq_tsum F K hz0 ht0 (by rw [abs_of_pos ht0]; linarith)]
      refine tsum_congr fun n => ?_
      simp only [Φ, profile, indicator_of_mem htT]
    · rw [indicator_of_notMem htT]
      simp [Φ, profile, indicator_of_notMem htT]
  rw [h2]
  have hwre : ∀ n, (wave F.gammaData z n).re = gapAngle z := by
    intro n
    simp [wave]
  have hw : ∀ n, 0 < (wave F.gammaData z n).re := fun n => by
    rw [hwre]
    exact gapAngle_pos hz
  have hint' : ∀ n, Integrable (Φ n) (volume.restrict (Ioi 0)) := fun n =>
    (integrableOn_mul_abelKernel hm hb _ (hw n)).const_mul _
  have hnorm : ∀ n, ∫ t in Ioi (0 : ℝ), ‖Φ n t‖ =
      ‖F.gammaData.rootNumber * z ^ (-((-(K : ℝ) - 1 / 2 : ℝ) : ℂ))‖ *
        ‖dualCoeff F (-(K : ℝ) - 1 / 2) n‖ * ∫ t in Ioi (0 : ℝ),
          ‖profile F.gammaData (-(K : ℝ) - 1 / 2) T₀ t‖ * Real.exp (-gapAngle z * t) := by
    intro n
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [Φ, norm_mul, norm_abelKernel _ _ ht, hwre]
  have hsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖Φ n t‖ := by
    simp only [hnorm]
    exact ((summable_dualCoeff F hσ).norm.mul_left _).mul_right _
  rw [← integral_tsum_of_summable_integral_norm hint' hsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [Φ]
  rw [integral_const_mul]
  unfold abelIntegral
  ring

/-- The part of the integral below the cutoff stays bounded as `z` approaches `iβ`. -/
theorem norm_integral_Iic_le (F : ExtendedSelbergClass) {K : ℕ} (ha : (-(K : ℝ) - 1 / 2) < -1)
    (haμ : ∀ j, F.gammaData.lambda j * (-(K : ℝ) - 1 / 2) < 1 - (F.gammaData.mu j).re)
    {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {β y : ℝ} (hβ : 0 < β) (hy : 0 < y) (hy1 : y < 1) :
    ‖∫ t in Iic T₀, ordinaryMellinIntegrand F 0 (boundaryPath β y) (leftLine K t)‖ ≤
      (1 + β) ^ (-(-(K : ℝ) - 1 / 2)) * Real.exp (π / 2 * T₀) * ∫ t, ‖leftValue F K t‖ := by
  have hV : Integrable (leftValue F K) := by
    have h := integrable_leftIntegrand F ha haμ (z := 1) (by simp)
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp [ordinaryMellinIntegrand, leftValue]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (1 + β) ^ (-(-(K : ℝ) - 1 / 2)) * Real.exp (π / 2 * T₀) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    positivity
  have hz := boundaryPath_ne_zero hβ y
  have hargnn : 0 ≤ Complex.arg (boundaryPath β y) :=
    Complex.arg_nonneg_iff.mpr (by rw [boundaryPath_im]; exact hβ.le)
  have hargle : Complex.arg (boundaryPath β y) ≤ π / 2 :=
    (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (by rwa [boundaryPath_re]))).le
  have hpt : ∀ t ∈ Iic T₀, ‖ordinaryMellinIntegrand F 0 (boundaryPath β y) (leftLine K t)‖ ≤
      c * ‖leftValue F K t‖ := by
    intro t ht
    have ht' : t ≤ T₀ := ht
    have hval : ordinaryMellinIntegrand F 0 (boundaryPath β y) (leftLine K t) =
        (boundaryPath β y) ^ (-(leftLine K t)) * leftValue F K t := rfl
    rw [hval, norm_mul, Complex.norm_cpow_of_ne_zero hz]
    have hre : (-(leftLine K t)).re = -(-(K : ℝ) - 1 / 2) := by simp [leftLine]
    have him : (-(leftLine K t)).im = -t := by simp [leftLine]
    rw [hre, him]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [hc, div_eq_mul_inv, ← Real.exp_neg]
    refine mul_le_mul ?_ (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
    · refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by linarith)
      linarith [norm_boundaryPath_le hβ hy]
    · have h1 : Complex.arg (boundaryPath β y) * t ≤ Complex.arg (boundaryPath β y) * T₀ :=
        mul_le_mul_of_nonneg_left ht' hargnn
      have h2 : Complex.arg (boundaryPath β y) * T₀ ≤ π / 2 * T₀ :=
        mul_le_mul_of_nonneg_right hargle hT₀
      linarith
  have hboundI : Integrable (fun t => c * ‖leftValue F K t‖) := hV.norm.const_mul c
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Iic T₀))
    hboundI.integrableOn (by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      exact hpt t ht)
  refine h.trans ?_
  rw [integral_const_mul, ← hc]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  exact setIntegral_le_integral hV.norm (Eventually.of_forall fun t => norm_nonneg _)

/-! ### The limit of each term -/

/-- On the lattice, the wave's shift is second order in `y`. -/
theorem tendsto_waveShift_div (G : SelbergGammaData) {n : ℕ} (hn : n ≠ 0)
    {β : ℝ} (hβ : 0 < β) (hβn : β = latticeStep G * n) :
    Tendsto (fun y => waveShift G (boundaryPath β y) n / gapAngle (boundaryPath β y)) (𝓝[>] 0)
      (𝓝 0) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : condLog G - Real.log n = -Real.log β := by
    rw [hβn, Real.log_mul (latticeStep_pos G).ne' hnpos.ne', log_latticeStep]
    ring
  have hlin : Tendsto (fun y : ℝ => y * ((1 + β) / (2 * β ^ 2))) (𝓝[>] 0) (𝓝 (0 * ((1 + β) / (2 * β ^ 2)))) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).mul_const _
  rw [zero_mul] at hlin
  have hpt : ∀ y : ℝ, 0 < y → y < 1 →
      0 ≤ waveShift G (boundaryPath β y) n / gapAngle (boundaryPath β y) ∧
      waveShift G (boundaryPath β y) n / gapAngle (boundaryPath β y) ≤
        y * ((1 + β) / (2 * β ^ 2)) := by
    intro y hy hy1
    have hgap := gapAngle_pos (z := boundaryPath β y) (by rwa [boundaryPath_re])
    have hN := le_norm_boundaryPath hβ y
    have hNpos : 0 < ‖boundaryPath β y‖ := hβ.trans_le hN
    have hval : waveShift G (boundaryPath β y) n = Real.log (‖boundaryPath β y‖ / β) := by
      rw [Real.log_div hNpos.ne' hβ.ne']
      unfold waveShift
      linarith
    have hτ0 : 0 ≤ waveShift G (boundaryPath β y) n := by
      rw [hval]
      exact Real.log_nonneg ((one_le_div hβ).mpr hN)
    have hτ1 : waveShift G (boundaryPath β y) n ≤ y ^ 2 / (2 * β ^ 2) := by
      rw [hval]
      refine (Real.log_le_sub_one_of_pos (div_pos hNpos hβ)).trans ?_
      have h2 := norm_boundaryPath_le_second (y := y) hβ
      rw [sub_le_iff_le_add, div_le_iff₀ hβ]
      calc ‖boundaryPath β y‖ ≤ β + y ^ 2 / (2 * β) := h2
        _ = _ := by
          field_simp
          ring
    refine ⟨div_nonneg hτ0 hgap.le, ?_⟩
    have hq : y / gapAngle (boundaryPath β y) ≤ 1 + β := by
      have := (div_gapAngle_le hβ hy).trans (norm_boundaryPath_le hβ hy)
      linarith
    have hinv : 1 / gapAngle (boundaryPath β y) ≤ (1 + β) / y := by
      rw [le_div_iff₀ hy]
      calc 1 / gapAngle (boundaryPath β y) * y = y / gapAngle (boundaryPath β y) := by ring
        _ ≤ _ := hq
    calc waveShift G (boundaryPath β y) n / gapAngle (boundaryPath β y)
        = waveShift G (boundaryPath β y) n * (1 / gapAngle (boundaryPath β y)) := by ring
      _ ≤ (y ^ 2 / (2 * β ^ 2)) * ((1 + β) / y) :=
          mul_le_mul hτ1 hinv (by positivity) (by positivity)
      _ = _ := by
          field_simp
  refine squeeze_zero' ?_ ?_ hlin
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with y hy
    exact (hpt y hy.1 hy.2).1
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with y hy
    exact (hpt y hy.1 hy.2).2

/-- Off the lattice, the wave's shift stays away from zero. -/
theorem exists_tendsto_waveShift (G : SelbergGammaData) {n : ℕ} (hn : n ≠ 0)
    {β : ℝ} (hβ : 0 < β) (hβn : β ≠ latticeStep G * n) :
    ∃ τ₀ : ℝ, τ₀ ≠ 0 ∧ Tendsto (fun y => waveShift G (boundaryPath β y) n) (𝓝[>] 0) (𝓝 τ₀) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine ⟨Real.log β + condLog G - Real.log n, fun h0 => hβn ?_, ?_⟩
  · have hmulpos : 0 < latticeStep G * n := mul_pos (latticeStep_pos G) hnpos
    refine Real.log_injOn_pos hβ hmulpos ?_
    rw [Real.log_mul (latticeStep_pos G).ne' hnpos.ne', log_latticeStep]
    linarith
  · have h := (Real.continuousAt_log hβ.ne').tendsto.comp (tendsto_norm_boundaryPath β (hβ := hβ))
    exact (h.add_const _).sub_const _

/-! ### Passing to the limit -/

/-- **The boundary limit at one point `β`.** -/
theorem tendsto_boundary_core (F : ExtendedSelbergClass) {K : ℕ} (ha : (-(K : ℝ) - 1 / 2) < -1)
    (haμ : ∀ j, F.gammaData.lambda j * (-(K : ℝ) - 1 / 2) < 1 - (F.gammaData.mu j).re)
    {T₀ R : ℝ} (hT₀ : 0 ≤ T₀) (htail : F.gammaData.gammaTailHeight < T₀) (hR : 0 ≤ R)
    (hb : ∀ t, 0 < t → ‖profile F.gammaData (-(K : ℝ) - 1 / 2) T₀ t‖ ≤ R)
    (hm : AEStronglyMeasurable (profile F.gammaData (-(K : ℝ) - 1 / 2) T₀)
      (volume.restrict (Ioi 0))) {c : ℂ}
    (hlim : Tendsto (profile F.gammaData (-(K : ℝ) - 1 / 2) T₀) atTop (𝓝 c))
    {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ abelExponent F.gammaData.internalShift *
      ordinaryExponentialSeries F (boundaryPath β y)) (𝓝[>] 0)
      (𝓝 ((1 / (2 * (π : ℂ))) * ((F.gammaData.rootNumber *
        ((β : ℂ) * I) ^ (-((-(K : ℝ) - 1 / 2 : ℝ) : ℂ))) *
        ∑' n : ℕ, (if n ≠ 0 ∧ β = latticeStep F.gammaData * n then
          dualCoeff F (-(K : ℝ) - 1 / 2) n * ((β : ℂ) ^ abelExponent F.gammaData.internalShift *
            (c * Complex.Gamma (abelExponent F.gammaData.internalShift))) else 0)))) := by
  have hσ : -(K : ℝ) - 1 / 2 < 0 := by linarith
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = F.gammaData.internalShift := ⟨_, rfl⟩
  rw [← hθ]
  have hslit : (β : ℂ) * I ∈ Complex.slitPlane := Or.inr (by simpa using hβ.ne')
  -- the terms
  have hterm : ∀ n : ℕ, Tendsto (fun y : ℝ => dualCoeff F (-(K : ℝ) - 1 / 2) n *
      ((y : ℂ) ^ abelExponent θ * abelIntegral (profile F.gammaData (-(K : ℝ) - 1 / 2) T₀) θ
        (wave F.gammaData (boundaryPath β y) n))) (𝓝[>] 0)
      (𝓝 (if n ≠ 0 ∧ β = latticeStep F.gammaData * n then
        dualCoeff F (-(K : ℝ) - 1 / 2) n * ((β : ℂ) ^ abelExponent θ *
          (c * Complex.Gamma (abelExponent θ))) else 0)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [dualCoeff_zero]
    by_cases hβn : β = latticeStep F.gammaData * n
    · rw [if_pos ⟨hn, hβn⟩]
      refine Tendsto.const_mul _ ?_
      exact tendsto_path_resonant hm hb hlim θ hβ (tendsto_waveShift_div F.gammaData hn hβ hβn)
    · rw [if_neg (fun h => hβn h.2)]
      obtain ⟨τ₀, hτ₀, hτ⟩ := exists_tendsto_waveShift F.gammaData hn hβ hβn
      have h := (tendsto_path_off hm hb hlim θ hβ hτ hτ₀).const_mul (dualCoeff F (-(K : ℝ) - 1 / 2) n)
      rw [mul_zero] at h
      exact h
  have htsum := tendsto_tsum_of_dominated_convergence
    (bound := fun n => ‖dualCoeff F (-(K : ℝ) - 1 / 2) n‖ * (R * (1 + β)))
    ((summable_dualCoeff F hσ).norm.mul_right _) hterm (by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with y hy n
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_path_le hb hR θ hβ hy.1 hy.2 _) (norm_nonneg _))
  -- the three parts
  have hzero := tendsto_cpow_abelExponent_zero θ
  have hreg : Tendsto (fun y : ℝ => (y : ℂ) ^ abelExponent θ *
      regularPart F K (boundaryPath β y)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (regularPart F K) ((β : ℂ) * I) :=
      (analyticOnNhd_regularPart F K _ hslit).continuousAt
    have h := hzero.mul (hc.tendsto.comp (tendsto_boundaryPath β))
    rw [zero_mul] at h
    exact h
  have hlow : Tendsto (fun y : ℝ => (y : ℂ) ^ abelExponent θ *
      ∫ t in Iic T₀, ordinaryMellinIntegrand F 0 (boundaryPath β y) (leftLine K t)) (𝓝[>] 0)
      (𝓝 0) := by
    have hlin : Tendsto (fun y : ℝ => y * ((1 + β) ^ (-(-(K : ℝ) - 1 / 2)) *
        Real.exp (π / 2 * T₀) * ∫ t, ‖leftValue F K t‖)) (𝓝[>] 0) (𝓝 (0 * _)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul_const _
    rw [zero_mul] at hlin
    refine squeeze_zero_norm' ?_ hlin
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with y hy
    rw [norm_mul, norm_ofReal_cpow_abelExponent hy.1]
    exact mul_le_mul_of_nonneg_left (norm_integral_Iic_le F ha haμ hT₀ hβ hy.1 hy.2) hy.1.le
  have hpow : Tendsto (fun y : ℝ => (boundaryPath β y) ^ (-((-(K : ℝ) - 1 / 2 : ℝ) : ℂ))) (𝓝[>] 0)
      (𝓝 (((β : ℂ) * I) ^ (-((-(K : ℝ) - 1 / 2 : ℝ) : ℂ)))) :=
    (continuousAt_cpow_const hslit).tendsto.comp (tendsto_boundaryPath β)
  have hall := (hreg.add (hlow.const_mul (1 / (2 * (π : ℂ))))).add
    (((hpow.const_mul F.gammaData.rootNumber).mul htsum).const_mul (1 / (2 * (π : ℂ))))
  simp only [mul_zero, add_zero, zero_add] at hall
  refine hall.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : (0 : ℝ) < y := hy
  have hzre : 0 < (boundaryPath β y).re := by rwa [boundaryPath_re]
  rw [ordinaryExponentialSeries_eq_left F ha haμ hzre,
    integral_left_split F ha haμ hT₀ htail hb hm hzre, ← hθ]
  have htm : (y : ℂ) ^ abelExponent θ * ∑' n, dualCoeff F (-(K : ℝ) - 1 / 2) n *
      abelIntegral (profile F.gammaData (-(K : ℝ) - 1 / 2) T₀) θ
        (wave F.gammaData (boundaryPath β y) n) =
      ∑' n, dualCoeff F (-(K : ℝ) - 1 / 2) n * ((y : ℂ) ^ abelExponent θ *
        abelIntegral (profile F.gammaData (-(K : ℝ) - 1 / 2) T₀) θ
          (wave F.gammaData (boundaryPath β y) n)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    ring
  rw [← htm]
  ring

/-- The constant at the lattice point `κm`. -/
theorem boundary_constant_identity {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : m ≠ 0) (σ θ : ℝ) :
    (((κ * m : ℝ) : ℂ) * I) ^ (-(σ : ℂ)) * (1 / (m : ℂ) ^ (((1 - σ : ℝ)) : ℂ)) *
        ((κ * m : ℝ) : ℂ) ^ abelExponent θ =
      (((κ : ℂ) * I) ^ (-(σ : ℂ)) * (κ : ℂ) ^ abelExponent θ) * (m : ℂ) ^ (-(I * (θ : ℂ))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hκI : (κ : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hκ.ne') Complex.I_ne_zero
  have e1 : ((κ * m : ℝ) : ℂ) * I = ((m : ℝ) : ℂ) * ((κ : ℂ) * I) := by
    push_cast
    ring
  have e2 : ((κ * m : ℝ) : ℂ) = (κ : ℂ) * ((m : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e1, e2, ofReal_mul_cpow hmR hκI, ofReal_mul_cpow hκ
    (Complex.ofReal_ne_zero.mpr hmR.ne'), Complex.ofReal_natCast]
  have h3 : (m : ℂ) ^ abelExponent θ = (m : ℂ) * (m : ℂ) ^ (-(I * (θ : ℂ))) := by
    have : abelExponent θ = 1 + (-(I * (θ : ℂ))) := by
      unfold abelExponent
      ring
    rw [this, Complex.cpow_add _ _ hmc, Complex.cpow_one]
  have h4 : (m : ℂ) ^ (((1 - σ : ℝ)) : ℂ) = (m : ℂ) * (m : ℂ) ^ (-(σ : ℂ)) := by
    have : (((1 - σ : ℝ)) : ℂ) = 1 + (-(σ : ℂ)) := by
      push_cast
      ring
    rw [this, Complex.cpow_add _ _ hmc, Complex.cpow_one]
  have h5 : (m : ℂ) ^ (-(σ : ℂ)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hmc]
    exact Complex.exp_ne_zero _
  rw [h3, h4]
  field_simp

/-- **The boundary law.**  At degree one, the exponential series has its boundary singularities on the
lattice `(2π/q)ℕ` of the positive imaginary axis, with strengths `C ā(m) m^{−iθ}`, `C ≠ 0`. -/
theorem exists_boundary_law (F : ExtendedSelbergClass) (hd : F.gammaData.degree = 1) :
    ∃ C : ℂ, C ≠ 0 ∧
      (∀ m : ℕ, m ≠ 0 → Tendsto (fun y : ℝ => (y : ℂ) ^ abelExponent F.gammaData.internalShift *
        ordinaryExponentialSeries F (boundaryPath (latticeStep F.gammaData * m) y)) (𝓝[>] 0)
        (𝓝 (C * (star (F.coeff m) * (m : ℂ) ^ (-(I * (F.gammaData.internalShift : ℂ))))))) ∧
      (∀ β : ℝ, 0 < β → (∀ m : ℕ, m ≠ 0 → β ≠ latticeStep F.gammaData * m) →
        Tendsto (fun y : ℝ => (y : ℂ) ^ abelExponent F.gammaData.internalShift *
          ordinaryExponentialSeries F (boundaryPath β y)) (𝓝[>] 0) (𝓝 0)) := by
  obtain ⟨K, ha, haμ⟩ := exists_farLeft F.gammaData
  obtain ⟨c, hc, hlimS⟩ := exists_tendsto_symbol F.gammaData hd (-(K : ℝ) - 1 / 2)
  have hlimS' : Tendsto (symbolPhase F.gammaData (-(K : ℝ) - 1 / 2)) atTop (𝓝 c) := hlimS
  -- the cutoff
  have hev : ∀ᶠ t : ℝ in atTop, ‖symbolPhase F.gammaData (-(K : ℝ) - 1 / 2) t‖ < ‖c‖ + 1 :=
    hlimS'.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  obtain ⟨T₀, hT₀def⟩ : ∃ T₀ : ℝ, T₀ = max T₁ (F.gammaData.gammaTailHeight + 1) := ⟨_, rfl⟩
  have hT₀1 : T₁ ≤ T₀ := hT₀def ▸ le_max_left _ _
  have htail : F.gammaData.gammaTailHeight < T₀ := by
    have : F.gammaData.gammaTailHeight + 1 ≤ T₀ := hT₀def ▸ le_max_right _ _
    linarith
  have hT₀ : 0 ≤ T₀ := F.gammaData.gammaTailHeight_nonneg.trans htail.le
  have hR : 0 ≤ ‖c‖ + 1 := by positivity
  have hb : ∀ t, 0 < t → ‖profile F.gammaData (-(K : ℝ) - 1 / 2) T₀ t‖ ≤ ‖c‖ + 1 := by
    intro t _
    unfold profile
    by_cases htT : t ∈ Ioi T₀
    · rw [indicator_of_mem htT]
      exact (hT₁ t (hT₀1.trans (le_of_lt htT))).le
    · rw [indicator_of_notMem htT, norm_zero]
      exact hR
  have hm : AEStronglyMeasurable (profile F.gammaData (-(K : ℝ) - 1 / 2) T₀)
      (volume.restrict (Ioi 0)) := by
    have hcont : ContinuousOn (symbolPhase F.gammaData (-(K : ℝ) - 1 / 2)) (Ioi T₀) := by
      intro t ht
      have ht' : T₀ < t := ht
      have ht0 : 0 < t := lt_of_le_of_lt hT₀ ht'
      exact (continuousAt_symbolPhase _ _ ht0
        (F.gammaData.verticalTailCondition_of_gammaTailHeight_lt_abs
          (by rw [abs_of_pos ht0]; linarith))).continuousWithinAt
    have h : AEStronglyMeasurable (symbolPhase F.gammaData (-(K : ℝ) - 1 / 2))
        (volume.restrict (Ioi T₀)) := hcont.aestronglyMeasurable measurableSet_Ioi
    exact ((aestronglyMeasurable_indicator_iff measurableSet_Ioi).mpr h).restrict
  have hlim : Tendsto (profile F.gammaData (-(K : ℝ) - 1 / 2) T₀) atTop (𝓝 c) := by
    refine hlimS'.congr' ?_
    filter_upwards [eventually_gt_atTop T₀] with t ht
    unfold profile
    rw [indicator_of_mem (show t ∈ Ioi T₀ from ht)]
  have hcore := fun {β : ℝ} (hβ : 0 < β) =>
    tendsto_boundary_core F ha haμ hT₀ htail hR hb hm hlim hβ
  -- the constant
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = F.gammaData.internalShift := ⟨_, rfl⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = latticeStep F.gammaData := ⟨_, rfl⟩
  have hκ : 0 < κ := hκdef ▸ latticeStep_pos _
  have hω : F.gammaData.rootNumber ≠ 0 := by
    intro h
    have := F.gammaData.rootNumber_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hκc : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ.ne'
  have hκI : (κ : ℂ) * I ≠ 0 := mul_ne_zero hκc Complex.I_ne_zero
  have hΓ : Complex.Gamma (abelExponent θ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [abelExponent_re]; norm_num)
  refine ⟨(1 / (2 * (π : ℂ))) * (F.gammaData.rootNumber * (((κ : ℂ) * I) ^
    (-((-(K : ℝ) - 1 / 2 : ℝ) : ℂ)) * (κ : ℂ) ^ abelExponent θ)) *
    (c * Complex.Gamma (abelExponent θ)), ?_, ?_, ?_⟩
  · refine mul_ne_zero (mul_ne_zero (one_div_ne_zero (mul_ne_zero two_ne_zero hπ)) (mul_ne_zero hω
      (mul_ne_zero ?_ ?_))) (mul_ne_zero hc hΓ)
    · rw [Complex.cpow_def_of_ne_zero hκI]
      exact Complex.exp_ne_zero _
    · rw [Complex.cpow_def_of_ne_zero hκc]
      exact Complex.exp_ne_zero _
  · intro m hm0
    have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hβ : 0 < latticeStep F.gammaData * m := mul_pos (latticeStep_pos _) hmR
    have h := hcore hβ
    have hsum : (∑' n : ℕ, (if n ≠ 0 ∧ latticeStep F.gammaData * m = latticeStep F.gammaData * n then
        dualCoeff F (-(K : ℝ) - 1 / 2) n * (((latticeStep F.gammaData * m : ℝ) : ℂ) ^
          abelExponent F.gammaData.internalShift *
          (c * Complex.Gamma (abelExponent F.gammaData.internalShift))) else 0)) =
        dualCoeff F (-(K : ℝ) - 1 / 2) m * (((latticeStep F.gammaData * m : ℝ) : ℂ) ^
          abelExponent F.gammaData.internalShift *
          (c * Complex.Gamma (abelExponent F.gammaData.internalShift))) := by
      rw [tsum_eq_single m]
      · rw [if_pos ⟨hm0, rfl⟩]
      · intro n hn
        refine if_neg fun hh => hn ?_
        have hne : latticeStep F.gammaData ≠ 0 := (latticeStep_pos _).ne'
        have := mul_left_cancel₀ hne hh.2
        exact_mod_cast this.symm
    rw [hsum] at h
    convert h using 2
    rw [← hθ, ← hκdef, dualCoeff_of_ne_zero F _ hm0]
    have hid := boundary_constant_identity hκ hm0 (-(K : ℝ) - 1 / 2) θ
    linear_combination (-(1 / (2 * (π : ℂ))) * F.gammaData.rootNumber * star (F.coeff m) *
      (c * Complex.Gamma (abelExponent θ))) * hid
  · intro β hβ hne
    have h := hcore hβ
    have hsum : (∑' n : ℕ, (if n ≠ 0 ∧ β = latticeStep F.gammaData * n then
        dualCoeff F (-(K : ℝ) - 1 / 2) n * ((β : ℂ) ^ abelExponent F.gammaData.internalShift *
          (c * Complex.Gamma (abelExponent F.gammaData.internalShift))) else 0)) = 0 := by
      refine (tsum_congr fun n => if_neg fun hh => hne n hh.1 hh.2).trans tsum_zero
    rw [hsum, mul_zero, mul_zero] at h
    exact h

end GaloisForLFunctions.SelbergClass.DegreeOne
