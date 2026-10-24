import GaloisForLFunctions.SquareRootThreshold.DifferenceLagFamilyPositiveThroughTheFirstPrime
import GaloisForLFunctions.SquareRootThreshold.WindowCertificatesAndThePrimeWeight
import GaloisForLFunctions.SquareRootThreshold.SharpArchimedeanHorizonOfTheZetaSymbol
import GaloisForLFunctions.SquareRootThreshold.WindowedExcursionBalanceAndDoubleWindowRealVarianceLaw

/-!
# Sharper Odd Windows, Weight-Selective Certificates, and Phase-Selective Single-Height Positivity

This module establishes the sharper odd-window constants on complex tests and on the difference
lag family `P_{w,v}`, weight-selective certificates at the first prime atom, and the
phase-selective single-height localized Weil positivity law that replaces the height-uniform
`(4 + ε)√X` symbol horizon by the signed prime polynomial `Re Π_f(⌊e^{2a}⌋, ξ)` at height `ξ`.

## Main Results

1. **Sharper odd window `181/500 = 362/1000` on complex tests and `P_{w,v}`
   (`zetaZeroConfig_re_W_ge_of_odd_aperture_le_oneHundredEightyOneFiveHundredths`,
   `one_div_500_mul_le_re_lagPrimeWindowRHS_of_le_oneHundredEightyOneFiveHundredths`,
   `lt_of_re_lagPrimeWindowRHS_neg_sharper`,
   `one_div_500_mul_le_re_lagPrimeWindowRHS_of_near_log_two_sharper`,
   `firstPrime_atom_paid_on_lagFamily_sharper`):**
   Transfers the Schur-lending odd window `[-181/500, 181/500]` to complex odd `C²` tests and to
   the unmodulated difference lag family `P_{w,v}`, extending unconditional positivity to
   `v/2 + w ≤ 181/500` (`v ≤ 362/500 − 2w`), covering the entire first-prime window
   `|v − log 2| ≤ 2w` for all widths `0 < w ≤ 77/10000`, and forcing any negative lag to satisfy
   `v/2 + w > 181/500`.

2. **Weight-selective odd window inequality at the first prime
   (`re_weilFullFunctional_ge_of_odd_window_sub_atom_two`,
   `re_weilFullFunctional_ge_of_odd_window_of_atom_nonneg`):**
   For any prime weight `w : ℕ → ℝ` and odd real test `F` supported in `[-181/500, 181/500]`,
   `Re W_w(F ⋆ F̃) ≥ (1/1000) ∫ F² + ((log 2 − w(2))/√2) Re(k_F(log 2) + k_F(−log 2))`.

3. **Phase-selective single-height localized Weil lower bound beyond `4√X`
   (`zetaZeroConfig_re_W_heightShift_ge_sub_re_primePolynomial`,
   `zetaZeroConfig_re_W_heightShift_nonneg_of_phase_bound`,
   `exists_kronecker_trough_height_re_W_ge_archPart_add`,
   `exists_height_re_W_ge_archPart`):**
   Combines the exact localized explicit formula `Re W_ζ(S_ξ f, S_ξ f) = Re A_f(ξ) − Re Π_f(⌊e^{2a}⌋, ξ)`
   with the prime-independent archimedean lower bound `re_archPart_ge`:
   $$\operatorname{Re} W_\zeta(S_\xi f, S_\xi f) \ge
     \bigl(\log(1 + \pi|\xi|/4) - 10 - 2S(a)\bigr)\|f\|_2^2 - \frac{B_f^2}{8(1 + \pi|\xi|)}
     - \operatorname{Re}\Pi_f(\lfloor e^{2a}\rfloor, \xi).$$
   At any height `ξ` where `Re Π_f(⌊e^{2a}⌋, ξ) ≤ c e^a ‖f‖₂²` (with any `c ∈ ℝ`, including `c ≤ 0`),
   the `(4 + ε)e^a` horizon exponent is replaced by `c e^a`. Moreover, unconditionally and at
   Kronecker trough heights, there exist heights where `Re Π_f ≤ 0` (resp. `Re Π_f < −B`),
   completely removing the `4√X` prime-symbol cost at single heights.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity GaloisForLFunctions.ArithmeticPositivityTheory

/-! ### 1. Complex odd tests and the difference lag family through `181/500 = 362/1000` -/

/-- **Odd complex tests through `181/500`.** Every odd complex `C²` test supported in
`[−181/500, 181/500]` satisfies `Re W_ζ(f, f) ≥ (1/1000) ∫ ‖f‖²`. -/
theorem zetaZeroConfig_re_W_ge_of_odd_aperture_le_oneHundredEightyOneFiveHundredths {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-(181 / 500)) (181 / 500))
    (hodd : ∀ x, f (-x) = -f x) :
    1 / 1000 * ∫ x, ‖f x‖ ^ 2 ≤ (zetaZeroConfig.W f f).re := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport f).trans hfs)
  have hzero : ∀ x, 181 / 500 < |x| → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hfs hmem
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hRe : ContDiff ℝ 2 (fun u => (f u).re) := Complex.reCLM.contDiff.comp hf
  have hIm : ContDiff ℝ 2 (fun u => (f u).im) := Complex.imCLM.contDiff.comp hf
  have hRec : HasCompactSupport (fun u => (f u).re) :=
    hfc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hImc : HasCompactSupport (fun u => (f u).im) :=
    hfc.comp_left (g := fun z : ℂ => z.im) (by simp)
  have h1 := fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths hRe hRec
    (fun x => by simp [hodd x]) fun x hx => by simp [hzero x hx]
  have h2 := fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths hIm hImc
    (fun x => by simp [hodd x]) fun x hx => by simp [hzero x hx]
  have hint (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      Integrable (fun x => g x ^ 2) volume := by
    have hs : HasCompactSupport (fun x => g x ^ 2) :=
      HasCompactSupport.of_support_subset_isCompact hgc.isCompact fun x hx =>
        subset_tsupport g (by simpa using hx)
    exact (hg.pow 2).integrable_of_hasCompactSupport hs
  have hsplit : ∫ x, ‖f x‖ ^ 2 = (∫ x, (f x).re ^ 2) + ∫ x, (f x).im ^ 2 := by
    rw [← integral_add (hint _ hRe.continuous hRec) (hint _ hIm.continuous hImc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [zeta_W_re_eq_fullZeroForm_re_add_im hf hfc, hsplit, mul_add]
  exact add_le_add h1 h2

/-- **Sharper odd window on the difference lag family.** For `0 < w`, `0 ≤ v` and
`v/2 + w ≤ 181/500`: `Re W_ζ(f_{w,v}, f_{w,v}) ≥ (1/1000) ∫ ‖f_{w,v}‖²`. -/
theorem one_div_1000_mul_le_re_W_twoBump_of_le_oneHundredEightyOneFiveHundredths {w v : ℝ}
    (hw : 0 < w) (hv0 : 0 ≤ v) (hvw : v / 2 + w ≤ 181 / 500) :
    1 / 1000 * ∫ t, ‖twoBump (modScaledBump w 0) v (-1) t‖ ^ 2 ≤
      (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re := by
  refine zetaZeroConfig_re_W_ge_of_odd_aperture_le_oneHundredEightyOneFiveHundredths
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    ((tsupport_twoBump_modScaledBump_subset hw hv0).trans ?_)
    (twoBump_modScaledBump_zero_neg w v)
  exact Icc_subset_Icc (by linarith) hvw

/-- **The difference lag family is positive through `v/2 + w ≤ 181/500`.** For `0 < w`, `2w < v`
and `v/2 + w ≤ 181/500` (`v ≤ 362/500 − 2w`): `Re P_{w,v} ≥ (1/500) ∫ ‖κ_w‖²`. -/
theorem one_div_500_mul_le_re_lagPrimeWindowRHS_of_le_oneHundredEightyOneFiveHundredths {w v : ℝ}
    (hw : 0 < w) (hv : 2 * w < v) (hvw : v / 2 + w ≤ 181 / 500) :
    1 / 500 * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re := by
  have hv0 : 0 ≤ v := by linarith
  have hw2 : 2 * w < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h := one_div_1000_mul_le_re_W_twoBump_of_le_oneHundredEightyOneFiveHundredths hw hv0 hvw
  rw [integral_norm_sq_twoBump_modScaledBump_eq hw hv,
    zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support hw 0)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv0] at h
  linarith

/-- **Every negative lag of `P_{w,v}` satisfies `v/2 + w > 181/500`.** -/
theorem lt_of_re_lagPrimeWindowRHS_neg_sharper {w v : ℝ} (hw : 0 < w) (hv : 2 * w < v)
    (hneg : (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1)))).re < 0) :
    181 / 500 < v / 2 + w := by
  by_contra hle
  have h := one_div_500_mul_le_re_lagPrimeWindowRHS_of_le_oneHundredEightyOneFiveHundredths
    hw hv (not_lt.mp hle)
  have h0 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 500)
    (integral_norm_sq_modScaledBump_pos hw).le
  linarith

/-- **First-prime atom paid through `v/2 + w ≤ 181/500`.** -/
theorem firstPrime_atom_paid_on_lagFamily_sharper {w v : ℝ} (hw : 0 < w) (hw' : w < 1 / 12)
    (hv : |v - Real.log 2| ≤ 2 * w) (hvw : v / 2 + w ≤ 181 / 500) :
    Real.log 2 / Real.sqrt 2 *
        (EF.weilTest (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))
            (Real.log 2) +
          EF.weilTest (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))
            (-Real.log 2)).re +
        1 / 500 * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 ≤
      (paperFT (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
            (twoBump (modScaledBump w 0) v (-1))) (I / 2) +
        paperFT (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
            (twoBump (modScaledBump w 0) v (-1))) (-I / 2) +
        (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
            (twoBump (modScaledBump w 0) v (-1))) r * (EF.gammaBracket r : ℂ)).re := by
  have hv' := abs_le.mp hv
  have h2v : 2 * w < v := by linarith [Real.log_two_gt_d9]
  have h := one_div_500_mul_le_re_lagPrimeWindowRHS_of_le_oneHundredEightyOneFiveHundredths
    hw h2v hvw
  rw [lagPrimeWindowRHS, lagPrimeWindow_eq_singleton_two hw hw' hv, Finset.sum_singleton,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h
  simp only [Nat.cast_ofNat, Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul] at h ⊢
  linarith

/-- **Full first-prime lag window covered for `0 < w ≤ 77/10000`.** -/
theorem one_div_500_mul_le_re_lagPrimeWindowRHS_of_near_log_two_sharper {w v : ℝ} (hw : 0 < w)
    (hw' : w ≤ 77 / 10000) (hv : |v - Real.log 2| ≤ 2 * w) :
    1 / 500 * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re := by
  have hl2 := Real.log_two_lt_d9
  have hg2 := Real.log_two_gt_d9
  norm_num at hl2 hg2
  obtain ⟨hv1, hv2⟩ := abs_le.mp hv
  exact one_div_500_mul_le_re_lagPrimeWindowRHS_of_le_oneHundredEightyOneFiveHundredths
    hw (by linarith) (by linarith)

/-! ### 2. Weight-selective odd window law at the first prime -/

private theorem tsupport_ofReal_subset_181 {F : ℝ → ℝ}
    (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) :
    tsupport (fun x => (F x : ℂ)) ⊆ Icc (-(181 / 500)) (181 / 500) := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hxI
  have hx' : 181 / 500 < |x| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hxI
    rcases hxI with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h
  exact hx (by simp [hsupp x hx'])

private theorem window_181_lt_log_three : (181 / 500 + 181 / 500 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 : Real.exp (181 / 500 + 181 / 500) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
  have h2 := Real.exp_one_lt_d9
  norm_num at h2
  linarith

/-- **Exact weight-selective lower bound on the `[-181/500, 181/500]` odd window.** For any prime
weight `w : ℕ → ℝ` and odd real test `F` supported in `[-181/500, 181/500]`, the Weil functional
exceeds `(1/1000) ∫ F²` by `((log 2 − w(2))/√2) Re(k_F(log 2) + k_F(−log 2))`. -/
theorem re_weilFullFunctional_ge_of_odd_window_sub_atom_two (w : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) :
    1 / 1000 * (∫ x, F x ^ 2) + (Real.log 2 - w 2) / Real.sqrt 2 *
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (Real.log 2) +
          EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (-Real.log 2)).re ≤
      (weilFullFunctional w
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by
  have hk := tsupport_weilTest_subset_add
    (tsupport_ofReal_subset_181 hsupp) (tsupport_ofReal_subset_181 hsupp)
  have hdiff := weilFullFunctional_sub_eq_atom_two hk window_181_lt_log_three
    w (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
  have hΛ2 : (ArithmeticFunction.vonMangoldt 2 : ℝ) = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; norm_num
  rw [hΛ2] at hdiff
  have hbase : 1 / 1000 * ∫ x, F x ^ 2 ≤
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by
    rw [← ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc]
    exact ArithmeticIncidencePositivity.fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths
      hF hFc hodd hsupp
  have hre := congrArg Complex.re hdiff
  rw [Complex.sub_re, Complex.re_ofReal_mul] at hre
  linarith

/-- Whenever `(log 2 − w(2)) Re(k_F(log 2) + k_F(−log 2)) ≥ 0`, the odd-window certificate
`Re W_w(F ⋆ F̃) ≥ (1/1000) ∫ F²` holds for `w`. -/
theorem re_weilFullFunctional_ge_of_odd_window_of_atom_nonneg (w : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 181 / 500 < |x| → F x = 0)
    (hatom : 0 ≤ (Real.log 2 - w 2) *
      (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (Real.log 2) +
        EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (-Real.log 2)).re) :
    1 / 1000 * (∫ x, F x ^ 2) ≤
      (weilFullFunctional w
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by
  have h := re_weilFullFunctional_ge_of_odd_window_sub_atom_two w hF hFc hodd hsupp
  have h0 : 0 ≤ (Real.log 2 - w 2) / Real.sqrt 2 *
      (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (Real.log 2) +
        EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (-Real.log 2)).re := by
    rw [div_mul_eq_mul_div]
    exact div_nonneg hatom (Real.sqrt_nonneg 2)
  linarith

/-! ### 3. Phase-selective single-height localized Weil positivity beyond `4√X` -/

/-- **Phase-selective single-height localized Weil lower bound.** For any `C²` profile `f`
supported in `[-a, a]` (`a ≥ 0`) and height `ξ ∈ ℝ`,
`Re W_ζ(S_ξ f, S_ξ f) ≥ (log(1 + π|ξ|/4) − 10 − 2S(a))‖f‖² − B_f²/(8(1 + π|ξ|)) − Re Π_f(⌊e^{2a}⌋, ξ)`. -/
theorem zetaZeroConfig_re_W_heightShift_ge_sub_re_primePolynomial {a : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    (Real.log (1 + π * |ξ| / 4) - 10 - 2 * pairEnergy (1 / 2) a) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) -
      (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤
      (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  have hid := re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial hf hfs ξ
  have harch := re_archPart_ge ha hf hfs ξ
  linarith

/-- **Single-height positivity under a prime-phase bound `Re Π_f(⌊e^{2a}⌋, ξ) ≤ c e^a ‖f‖²`.**
Whenever the prime phases at height `ξ` give `Re Π_f(⌊e^{2a}⌋, ξ) ≤ c e^a ∫ ‖f‖²` (for any
`c ∈ ℝ`, strictly smaller than `4` or even `c ≤ 0`), `Re W_ζ(S_ξ f, S_ξ f) ≥ 0` holds as soon as
`10 + c e^a + 2S(a) + 1 ≤ log(1 + π|ξ|/4)` and `B_f² / (8(1 + π|ξ|)) ≤ ∫ ‖f‖²`. -/
theorem zetaZeroConfig_re_W_heightShift_nonneg_of_phase_bound {a c : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ)
    (hphase : (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ c * Real.exp a * ∫ t, ‖f t‖ ^ 2)
    (hlog : 10 + c * Real.exp a + 2 * pairEnergy (1 / 2) a + 1 ≤ Real.log (1 + π * |ξ| / 4))
    (htail : (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
      ∫ t, ‖f t‖ ^ 2) :
    0 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  have h := zetaZeroConfig_re_W_heightShift_ge_sub_re_primePolynomial ha hf hfs ξ
  have hN0 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Kronecker trough enhancement of single-height positivity.** For every
`B < primeOnlyEnvelope f ⌊e^{2a}⌋₊ − primePowerTailEnvelope f ⌊e^{2a}⌋₊`, there exists a height
`ξ ∈ ℝ` at which `Re Π_f(⌊e^{2a}⌋, ξ) < −B` and hence
`Re W_ζ(S_ξ f, S_ξ f) > Re A_f(ξ) + B ≥ (log(1 + π|ξ|/4) − 10 − 2S(a))‖f‖² − B_f²/(8(1 + π|ξ|)) + B`. -/
theorem exists_kronecker_trough_height_re_W_ge_archPart_add {a B : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊) :
    ∃ ξ : ℝ, (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re < -B ∧
      (archPart f ξ).re + B < (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re ∧
      (Real.log (1 + π * |ξ| / 4) - 10 - 2 * pairEnergy (1 / 2) a) * (∫ t, ‖f t‖ ^ 2) -
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) + B <
        (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  obtain ⟨-, ⟨ξ, hξ⟩⟩ :=
    exists_gt_and_lt_re_primePolynomial_of_lt_primeSubCompEnvelope f ⌊Real.exp (2 * a)⌋₊ hB
  have hid := re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial hf hfs ξ
  have harch := re_archPart_ge ha hf hfs ξ
  exact ⟨ξ, hξ, by linarith, by linarith⟩

/-- **Unconditional existence of a height free of the `4√X` prime cost.** For every `C²` profile
`f` supported in `[-a, a]` (`a ≥ 0`), there exists a height `ξ ∈ ℝ` at which
`Re Π_f(⌊e^{2a}⌋, ξ) ≤ 0` and therefore
`Re W_ζ(S_ξ f, S_ξ f) ≥ Re A_f(ξ) ≥ (log(1 + π|ξ|/4) − 10 − 2S(a))‖f‖² − B_f²/(8(1 + π|ξ|))`. -/
theorem exists_height_re_W_ge_archPart {a : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    ∃ ξ : ℝ, (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ 0 ∧
      (archPart f ξ).re ≤
        (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re ∧
      (Real.log (1 + π * |ξ| / 4) - 10 - 2 * pairEnergy (1 / 2) a) * (∫ t, ‖f t‖ ^ 2) -
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
        (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  set N := ⌊Real.exp (2 * a)⌋₊
  have hex : ∃ ξ : ℝ, (primePolynomial f N ξ).re ≤ 0 := by
    have hsum : ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ ^ 2 =
        primeVariance f N := by
      simpa using sum_norm_sq_primeCoeff_shift_eq f N 0
    have hV0 : 0 ≤ primeVariance f N := by
      rw [← hsum]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    rcases hV0.lt_or_eq with hV | hV
    · obtain ⟨-, ξ, hξ⟩ := exists_pos_and_neg_re_primePolynomial f N hV
      exact ⟨ξ, hξ.le⟩
    · have h0 : ∀ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ = 0 :=
        fun j hj => sq_eq_zero_iff.mp
          ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp (hsum.trans hV.symm) j hj)
      have hE0 : primeEnvelope f N = 0 := Finset.sum_eq_zero h0
      exact ⟨0, (re_primePolynomial_le_primeEnvelope f N 0).trans_eq hE0⟩
  obtain ⟨ξ, hξ⟩ := hex
  have hid := re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial hf hfs ξ
  have harch := re_archPart_ge ha hf hfs ξ
  exact ⟨ξ, hξ, by linarith, by linarith⟩

end GaloisForLFunctions.SquareRootThreshold