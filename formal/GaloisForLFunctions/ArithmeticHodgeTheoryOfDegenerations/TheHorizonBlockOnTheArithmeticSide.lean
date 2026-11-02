import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingTailOfAHorizonBlock
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheLedgerOfAWindowOfZeros
import GaloisForLFunctions.SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm
import GaloisForLFunctions.RHTower.SelbergSymbolCriticalStrip
import GaloisForLFunctions.RHTower.LittlewoodShortWindowZeroCount
import Zeta23.GammaFacts.Complete

/-!
# The horizon block on the arithmetic side

The localized explicit formula writes Weil's form of a real `C²` test supported in `[−a, a]` as its
pole terms plus the symbol integral `∫ |f̂(τ)|² ν(τ) dτ`, `ν = μ + P_{e^{2a}}` (the archimedean
density and the primes below `e^{2a}`). Applied to a horizon block, recentred at the horizon
`log N`, the transform of the block is `e^{−iτ log N} w φ̂(wτ) D_x(τ)`, and the normalized form,
divided by the overlap, splits exactly:

* **Horizon formula** (`horizonForm_eq`):
  `c⁻¹ ⟨W x, x⟩ = Re(α₊ ᾱ₋ + α₋ ᾱ₊)/∫φ² + (∫φ²)⁻¹ ∫ ‖φ̂(wτ)‖² (|D_x(τ)|²/N) ν(τ) dτ` with
  `α₊ = φ̂(iw/2) D_x(i/2)` and `α₋ = φ̂(−iw/2) D_x(−i/2)/N`.
* **Synthesized test** (`weilQuad_halfWeight_eq`): `Q(H) = Re(ĥ(0) ĥ(1)‾ + ĥ(1) ĥ(0)‾) + ∫ |ĥ(½ + iτ)|² ν(τ) dτ`.

Both sides use the same symbol `ν`; the comparison of the horizon block with Weil's form of the
synthesized test is a comparison of `‖φ̂(wτ)‖² |D_x(τ)|²/N` with `(∫φ)² |ĥ(½ + iτ)|²`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

/-- The symbol `ν_X = μ + P_X` of the localized explicit formula. -/
def nuSymbol (X τ : ℝ) : ℝ := mu τ + PX X τ

/-- `|μ(τ)| ≤ A + log(2 + |τ|)`: continuity on `[−1, 1]` and Stirling beyond. -/
theorem exists_abs_mu_le_log : ∃ A : ℝ, ∀ τ : ℝ, |mu τ| ≤ A + Real.log (2 + |τ|) := by
  obtain ⟨C, hC⟩ := gammaFacts.stirling
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    gammaFacts.smooth.continuous.continuousOn
  refine ⟨max (|C| + Real.log (2 * Real.pi)) B, fun τ => ?_⟩
  have hlog0 : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
  rcases le_or_gt |τ| 1 with h | h
  · have hτ : τ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
    have := hB τ hτ
    rw [Real.norm_eq_abs] at this
    linarith [le_max_right (|C| + Real.log (2 * Real.pi)) B]
  · have h1 : 1 ≤ |τ| := h.le
    have hs := hC τ h1
    have hτ2 : (1 : ℝ) ≤ τ ^ 2 := by nlinarith [sq_abs τ]
    have hCτ : C / τ ^ 2 ≤ |C| := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [le_abs_self C, abs_nonneg C]
    have hpi : 0 < 2 * Real.pi := by positivity
    have hlogτ : 0 ≤ Real.log |τ| := Real.log_nonneg h1
    have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have habs : |Real.log (|τ| / (2 * Real.pi))| ≤ Real.log (2 + |τ|) + Real.log (2 * Real.pi) := by
      rw [Real.log_div (by linarith) hpi.ne']
      have : Real.log |τ| ≤ Real.log (2 + |τ|) := Real.log_le_log (by linarith) (by linarith)
      rw [abs_le]; constructor <;> linarith
    have hfac : |(1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤
        |Real.log (|τ| / (2 * Real.pi))| := by
      rw [abs_mul, abs_of_pos (by positivity)]
      have : 1 / (2 * Real.pi) ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
      nlinarith [abs_nonneg (Real.log (|τ| / (2 * Real.pi)))]
    have := abs_sub_abs_le_abs_sub (mu τ) ((1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi)))
    linarith [le_max_left (|C| + Real.log (2 * Real.pi)) B]

/-- `|ν_X(τ)| ≤ A_ν + log(2 + |τ|)` with `A_ν ≥ 0`. -/
theorem exists_abs_nuSymbol_le {X : ℝ} (hX : 0 ≤ X) :
    ∃ Aν : ℝ, 0 ≤ Aν ∧ ∀ τ, |nuSymbol X τ| ≤ Aν + Real.log (2 + |τ|) := by
  obtain ⟨Aμ, hAμ⟩ := exists_abs_mu_le_log
  refine ⟨max Aμ 0 + X ^ 2 / Real.pi, by positivity, fun τ => ?_⟩
  unfold nuSymbol
  have h1 := hAμ τ
  have h2 := RHTower.Littlewood.abs_PX_le hX τ
  have := abs_add_le (mu τ) (PX X τ)
  have := le_max_left Aμ 0
  linarith

/-- **Localized explicit formula for real tests.** -/
theorem weilQuad_eq_pole_add_symbol {a : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Set.Icc (-a) a) :
    weilQuad f = (paperFT (EF.weilTest (cx f) (cx f)) (Complex.I / 2) +
        paperFT (EF.weilTest (cx f) (cx f)) (-Complex.I / 2)).re +
      ∫ τ : ℝ, ‖paperFT (cx f) τ‖ ^ 2 * nuSymbol (Real.exp (2 * a)) τ := by
  have hfc : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc fun u hu => by
    by_contra hne
    exact hu (hfs (subset_tsupport f hne))
  have hcx : ContDiff ℝ 2 (cx f) := Complex.ofRealCLM.contDiff.comp hf
  have hcxs : tsupport (cx f) ⊆ Set.Icc (-a) a := by
    refine (tsupport_comp_subset Complex.ofReal_zero f).trans hfs
  have hcxc : HasCompactSupport (cx f) := hfc.comp_left Complex.ofReal_zero
  rw [LogCells.weilQuad_eq_zetaW hf hfc]
  change (zetaZeroConfig.W (cx f) (cx f)).re = _
  rw [SquareRootThreshold.zetaZeroConfig_W_eq_pole_add_integral hcx hcxs, Complex.add_re]
  congr 1
  have hfun : (fun τ : ℝ => paperFT (EF.weilTest (cx f) (cx f)) τ *
      ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ)) =
      fun τ : ℝ => ((‖paperFT (cx f) τ‖ ^ 2 * nuSymbol (Real.exp (2 * a)) τ : ℝ) : ℂ) := by
    funext τ
    rw [RHTower.paperFT_weilTest_self_ofReal hcx.continuous hcxc τ, nuSymbol]
    push_cast
    ring
  rw [hfun, integral_complex_ofReal, Complex.ofReal_re]

/-! ### The centred horizon block -/

/-- The horizon block recentred at the horizon: `T₀(u) = T_N(u + log N)`. -/
def centredHorizonTest (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  atomicTest N (horizonWeights h N) (atomDilate φ (c / N)) (u + Real.log N)

theorem weilQuad_centredHorizonTest (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    weilQuad (centredHorizonTest φ h c N) =
      weilQuad (atomicTest N (horizonWeights h N) (atomDilate φ (c / N))) := by
  have h1 := weilQuad_comp_sub (atomicTest N (horizonWeights h N) (atomDilate φ (c / N)))
    (-Real.log N)
  simp only [sub_neg_eq_add] at h1
  unfold centredHorizonTest
  exact h1

/-- The transform of a translate: `∫ f(u + L) e^{izu} du = e^{−izL} f̂(z)`. -/
theorem paperFT_comp_add (f : ℝ → ℂ) (L : ℝ) (z : ℂ) :
    paperFT (fun u => f (u + L)) z = Complex.exp (-(Complex.I * z * L)) * paperFT f z := by
  unfold paperFT
  have h := integral_add_right_eq_self (μ := volume)
    (fun v : ℝ => f v * Complex.exp (Complex.I * z * ((v - L : ℝ) : ℂ))) L
  simp only [add_sub_cancel_right] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem paperFT_centredHorizonTest {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (z : ℂ) :
    paperFT (cx (centredHorizonTest φ h c N)) z =
      Complex.exp (-(Complex.I * z * Real.log N)) *
        (((c / N : ℝ) : ℂ) * paperFT (cx φ) (((c / N : ℝ) : ℂ) * z) *
          dirichletPoly N (horizonWeights h N) z) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have := paperFT_comp_add (cx (atomicTest N (horizonWeights h N) (atomDilate φ (c / N))))
    (Real.log N) z
  rw [show (fun u => cx (atomicTest N (horizonWeights h N) (atomDilate φ (c / N))) (u + Real.log N))
      = cx (centredHorizonTest φ h c N) from rfl] at this
  rw [this, paperFT_atomicTest_atomDilate hφ hφc hw]

theorem contDiff_centredHorizonTest {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (h : ℝ → ℝ) (c : ℝ)
    (N : ℕ) : ContDiff ℝ 2 (centredHorizonTest φ h c N) := by
  unfold centredHorizonTest
  have hg : ContDiff ℝ 2 (atomDilate φ (c / N)) := by
    unfold atomDilate; exact hφ.comp (contDiff_id.div_const _)
  exact (contDiff_atomicTest hg N _).comp (contDiff_id.add contDiff_const)

/-- The centred block lives in `[−A, w]`. -/
theorem tsupport_centredHorizonTest_subset {φ : ℝ → ℝ} (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {h : ℝ → ℝ} {A : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) :
    tsupport (centredHorizonTest φ h c N) ⊆ Set.Icc (-A) (c / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hout
  apply hu
  unfold centredHorizonTest atomicTest
  refine sum_eq_zero fun n hn => ?_
  have hn1 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  by_cases hx : h (Real.log n - Real.log N) = 0
  · rw [horizonWeights, hx, zero_div, zero_mul]
  · have hy : Real.log n - Real.log N ∈ Set.Icc (-A) 0 := by
      by_contra hy; exact hx (hsupp _ hy)
    rw [atomDilate, hφsupp _ (fun hm => hout ?_), mul_zero]
    obtain ⟨hm0, hm1⟩ := hm
    rw [le_div_iff₀ hw, zero_mul] at hm0
    rw [div_le_one hw] at hm1
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-! ### The exact horizon formula -/

/-- The pole amplitudes `α₊ = φ̂(iw/2) D_x(i/2)`, `α₋ = φ̂(−iw/2) D_x(−i/2)/N`. -/
def alphaPlus (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℂ :=
  paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2)) *
    dirichletPoly N (horizonWeights h N) (Complex.I / 2)

def alphaMinus (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℂ :=
  paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2)) *
    dirichletPoly N (horizonWeights h N) (-Complex.I / 2) / N

/-- The symbol integrand of a horizon block. -/
def horizonSymbolIntegrand (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) (X τ : ℝ) : ℝ :=
  ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
    (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) * nuSymbol X τ

theorem norm_sq_paperFT_centredHorizonTest {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    ‖paperFT (cx (centredHorizonTest φ h c N)) τ‖ ^ 2 =
      (c / N) ^ 2 * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [paperFT_centredHorizonTest hφ hφc h hc hN, norm_mul, norm_mul, norm_mul]
  have he : ‖Complex.exp (-(Complex.I * (τ : ℂ) * (Real.log N : ℂ)))‖ = 1 := by
    rw [show -(Complex.I * (τ : ℂ) * (Real.log N : ℂ)) = ((-(τ * Real.log N) : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [he, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hc hN0)]
  ring

theorem paperFT_centredHorizonTest_I_half {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    paperFT (cx (centredHorizonTest φ h c N)) (Complex.I / 2) =
      ((Real.exp (Real.log N / 2) * (c / N) : ℝ) : ℂ) * alphaPlus φ h c N := by
  rw [paperFT_centredHorizonTest hφ hφc h hc hN, alphaPlus]
  have : -(Complex.I * (Complex.I / 2) * (Real.log N : ℂ)) = ((Real.log N / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [this, ← Complex.ofReal_exp]
  push_cast
  ring

theorem paperFT_centredHorizonTest_neg_I_half {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    paperFT (cx (centredHorizonTest φ h c N)) (-Complex.I / 2) =
      ((Real.exp (-(Real.log N / 2)) * (c / N) * N : ℝ) : ℂ) * alphaMinus φ h c N := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [paperFT_centredHorizonTest hφ hφc h hc hN, alphaMinus]
  have : -(Complex.I * (-Complex.I / 2) * (Real.log N : ℂ)) = ((-(Real.log N / 2) : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [this, ← Complex.ofReal_exp]
  push_cast
  field_simp

/-- The pole terms of the centred block are `w² N (α₊ ᾱ₋ + α₋ ᾱ₊)`. -/
theorem pole_centredHorizonTest {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : 1 ≤ N) :
    paperFT (EF.weilTest (cx (centredHorizonTest φ h c N)) (cx (centredHorizonTest φ h c N)))
        (Complex.I / 2) +
      paperFT (EF.weilTest (cx (centredHorizonTest φ h c N)) (cx (centredHorizonTest φ h c N)))
        (-Complex.I / 2) =
      (((c / N) ^ 2 * N : ℝ) : ℂ) * (alphaPlus φ h c N * conj (alphaMinus φ h c N) +
        alphaMinus φ h c N * conj (alphaPlus φ h c N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT : Continuous (cx (centredHorizonTest φ h c N)) := by
    unfold cx centredHorizonTest atomicTest atomDilate
    fun_prop
  have hTc : HasCompactSupport (cx (centredHorizonTest φ h c N)) := by
    refine HasCompactSupport.comp_left ?_ Complex.ofReal_zero
    unfold centredHorizonTest
    have hg : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := fun u hu => by
      unfold atomDilate
      refine hφs _ fun hm => hu ?_
      obtain ⟨h0, h1⟩ := hm
      have hw : 0 < c / N := div_pos hc hN0
      exact ⟨by rw [le_div_iff₀ hw, zero_mul] at h0; exact h0,
        by rw [div_le_one hw] at h1; exact h1⟩
    exact (hasCompactSupport_atomicTest hg N _).comp_homeomorph (Homeomorph.addRight _)
  rw [EF.paperFT_weilTest hT hT hTc hTc, EF.paperFT_weilTest hT hT hTc hTc]
  have hc1 : conj (Complex.I / 2) = -Complex.I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-Complex.I / 2) = Complex.I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [hc1, hc2, paperFT_centredHorizonTest_I_half hφ hφc h hc hN,
    paperFT_centredHorizonTest_neg_I_half hφ hφc h hc hN, map_mul, map_mul,
    Complex.conj_ofReal, Complex.conj_ofReal]
  have hexp : Real.exp (Real.log N / 2) * Real.exp (-(Real.log N / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have key : ((Real.exp (Real.log N / 2) * (c / N) : ℝ) : ℂ) *
      ((Real.exp (-(Real.log N / 2)) * (c / N) * N : ℝ) : ℂ) = (((c / N) ^ 2 * N : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [show Real.exp (Real.log N / 2) * (c / N) * (Real.exp (-(Real.log N / 2)) * (c / N) * N) =
      (Real.exp (Real.log N / 2) * Real.exp (-(Real.log N / 2))) * ((c / N) ^ 2 * N) by ring,
      hexp, one_mul]
  linear_combination (alphaPlus φ h c N * conj (alphaMinus φ h c N) +
    alphaMinus φ h c N * conj (alphaPlus φ h c N)) * key

/-- **The exact horizon formula.** -/
theorem horizonForm_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {h : ℝ → ℝ} {A : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (hcN : c ≤ N) :
    c⁻¹ * (weilQuad (atomicTest N (horizonWeights h N) (atomDilate φ (c / N))) /
        ∫ u, atomDilate φ (c / N) u ^ 2) =
      (alphaPlus φ h c N * conj (alphaMinus φ h c N) +
          alphaMinus φ h c N * conj (alphaPlus φ h c N)).re / (∫ u, φ u ^ 2) +
        (∫ u, φ u ^ 2)⁻¹ * ∫ τ : ℝ, horizonSymbolIntegrand φ h c N (Real.exp (2 * (A + 1))) τ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr hcN
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hsupp' : tsupport (centredHorizonTest φ h c N) ⊆ Set.Icc (-(A + 1)) (A + 1) :=
    (tsupport_centredHorizonTest_subset hφsupp hsupp hc hN).trans
      (Set.Icc_subset_Icc (by linarith) (by linarith))
  rw [← weilQuad_centredHorizonTest, weilQuad_eq_pole_add_symbol
    (contDiff_centredHorizonTest hφ h c N) hsupp',
    pole_centredHorizonTest hφ.continuous hφc hφsupp h hc hN, integral_atomDilate_sq φ hw,
    Complex.re_ofReal_mul]
  have hint : ∫ τ : ℝ, ‖paperFT (cx (centredHorizonTest φ h c N)) τ‖ ^ 2 *
      nuSymbol (Real.exp (2 * (A + 1))) τ =
      (c / N) ^ 2 * N * ∫ τ : ℝ, horizonSymbolIntegrand φ h c N (Real.exp (2 * (A + 1))) τ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [horizonSymbolIntegrand]
    rw [norm_sq_paperFT_centredHorizonTest hφ.continuous hφc h hc hN]
    field_simp
  rw [hint]
  have hM : 0 < ∫ u, φ u ^ 2 := hφ2
  field_simp

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
