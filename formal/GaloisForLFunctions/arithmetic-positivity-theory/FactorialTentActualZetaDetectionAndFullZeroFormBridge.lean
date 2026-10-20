import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentPatternWeilCompleteness
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentOffLineDetection
import GaloisForLFunctions.«arithmetic-positivity-theory».SourceRelativeSchurMarginAndPerturbationCalculus
import GaloisForLFunctions.SquareRootThreshold.PrimeSideTwoBumpCriterion
import GaloisForLFunctions.SquareRootThreshold.FiniteOffLineSetsAreVisible
import GaloisForLFunctions.ArithmeticCriticalityTheory.FullZeroFormWeilPositivity
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse

/-!
# Actual-Zeta Off-Line Detection by Single-Scale Grid Tent Patterns and the Full Zero Form Bridge

This module connects four previously separate parts of the corpus:
1. **Universal Zero-Side Reflection Identity (`configurationSquareMass_sub_re_W_eq_reflectionDefect`,
   `zeta_squareMass_sub_re_W_eq_reflectionDefect`):**
   Using the reflection involution `ρ ↦ 1 - conj ρ` on `Z.carrier`, the identity
   `configurationSquareMass Z f - (Z.W f f).re = configurationReflectionDefect Z f`
   holds for **every** `Z : ZeroConfig` and **every** square-summable `f : ℝ → ℂ` (in particular,
   unconditionally for every tempered configuration `Z`, including `zetaZeroConfig`, on all
   `f ∈ C_c²(ℝ, ℂ)`), without any periodic-lattice or on-line annihilation premise.
2. **Exact Five-Way Unification (`fullZeroForm_eq_re_weilFullFunctional`,
   `fullZeroForm_eq_compactFullWeilEnergy`, `fullZeroForm_eq_zeta_W_re`,
   `fullZeroForm_eq_zeta_squareMass_sub_reflectionDefect`,
   `poleFreeForm_eq_zeta_squareMass_sub_reflectionDefect`):**
   On all `g ∈ C_c(ℝ, ℝ)` (including non-smooth translated factorial-tent patterns), the full zero
   form `fullZeroForm g = markovEnergy g - 2 oddPoleMoment(g)² + 2 evenPoleMoment(g)²` of
   `ArithmeticCriticalityTheory` coincides identically with `compactFullWeilEnergy g` of
   `ArithmeticPositivityTheory` and `(weilFullFunctional Λ (EF.weilTest g g)).re` of `RHTower`.
   On `F ∈ C_c²(ℝ, ℝ)`, all three equal `(zetaZeroConfig.W F F).re` of `SquareRootThreshold` and
   `configurationSquareMass zetaZeroConfig F - configurationReflectionDefect zetaZeroConfig F`.
   Consequently, the single-shift pole-free variation form `2 S_a(u) - D_a(u) + V_a(u)` equals
   this exact actual-zeta zero-side difference on `Φ(ω_a u)`, and plateau truncations of the
   entire theta-translate span leave the actual-zeta zero-side difference asymptotically invariant.
3. **Actual-Zeta Separation and Explicit-Aperture Detection by Single-Scale Grid Tent Patterns
   (`actual_zeta_offLine_detected_by_gridTentPattern`,
   `actual_zeta_finiteOffLine_detected_by_gridTentPattern_at_aperture`,
   `riemannHypothesis_iff_eventually_gridTentPattern_nonneg`,
   `singleShift_vanishing_profile_detected_by_gridTentPattern_of_not_riemannHypothesis`):**
   Combining `offLine_visible` and `finiteOffLine_visible` (`SquareRootThreshold`) with real-part
   splitting (`RHTower`), single-scale grid tent convergence (`FactorialTentPatternWeilCompleteness`),
   and joint complete-form smoothing (`FactorialTranslatedTentApproximation`), every actual off-line
   zero of `ζ` (and every finite residual off-line set at its explicit Nyquist–Ingham aperture) is
   detected at all sufficiently large arithmetic scales by a single-scale uniform-grid factorial-tent
   pattern and its smoothed `C_c²` detector with an explicit strictly positive margin across all
   channels (`compactFullWeilEnergy`, `fullZeroForm`, `weilFullFunctional Λ`, `zetaZeroConfig.W`,
   and `configurationReflectionDefect - configurationSquareMass`).
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open scoped Real BigOperators CompactlySupported ComplexConjugate
open _root_.Zeta23 _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.WeilOneSided _root_.RHTower.WeilWorkPBAP _root_.RHTower.WeilSpectral
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: Universal Zero-Side Reflection Defect Identity -/

/-- The reflection involution `ρ ↦ 1 - conj ρ` as a permutation of `Z.carrier` for any `ZeroConfig`. -/
def zeroConfigReflectPerm (Z : ZeroConfig) : Equiv.Perm Z.carrier :=
  Function.Involutive.toPerm
    (fun ρ => ⟨reflect ρ, Z.reflect_mem _ ρ.2⟩)
    (fun ρ => Subtype.ext (Tail.reflect_reflect ρ))

theorem zeroConfigSquareSummand_reflectPerm (Z : ZeroConfig) (f : ℝ → ℂ) (ρ : Z.carrier) :
    (Z.mult (zeroConfigReflectPerm Z ρ) : ℝ) * ‖paperFT f (gammaOf (zeroConfigReflectPerm Z ρ))‖ ^ 2 =
      (Z.mult ρ : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2 := by
  change (Z.mult (reflect ρ) : ℝ) * ‖paperFT f (gammaOf (reflect ρ))‖ ^ 2 = _
  rw [Z.mult_reflect _ ρ.2, Tail.gammaOf_reflect]

/-- Pointwise algebraic identity relating the square summands, real Weil summand, and reflection defect summand. -/
theorem re_Wsummand_add_reflectionDefect_summand (Z : ZeroConfig) (f : ℝ → ℂ) (ρ : Z.carrier) :
    (Z.Wsummand f f ρ).re +
        (Z.mult ρ : ℝ) / 2 * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 =
      ((Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2 +
        (Z.mult (zeroConfigReflectPerm Z ρ) : ℝ) *
          ‖paperFT f (gammaOf (zeroConfigReflectPerm Z ρ))‖ ^ 2) / 2 := by
  rw [zeroConfigSquareSummand_reflectPerm]
  unfold ZeroConfig.Wsummand
  set u := paperFT f (gammaOf ρ)
  set v := paperFT f (conj (gammaOf ρ))
  have hnorm : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (u * conj v).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hre : (((Z.mult ρ : ℂ) * u * conj v)).re = (Z.mult ρ : ℝ) * (u * conj v).re := by
    rw [mul_assoc]
    simp
  rw [hre, hnorm]
  ring

/-- **Universal Zero-Side Reflection Identity.** For any `Z : ZeroConfig` and any `f : ℝ → ℂ` with
summable multiplicity-weighted square mass, the difference between the square mass and the real
zero-side Weil form equals the reflection defect, with no lattice-annihilation hypothesis. -/
theorem configurationSquareMass_sub_re_W_eq_reflectionDefect (Z : ZeroConfig) (f : ℝ → ℂ)
    (hf : Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2)) :
    configurationSquareMass Z f - (Z.W f f).re = configurationReflectionDefect Z f := by
  set s : Z.carrier → ℝ := fun ρ => (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2
  set e := zeroConfigReflectPerm Z
  have hse : Summable (fun ρ : Z.carrier => s (e ρ)) := hf.comp_injective e.injective
  have hb : Summable (fun ρ : Z.carrier => (s ρ + s (e ρ)) / 2) := (hf.add hse).div_const 2
  have hW_bound (ρ : Z.carrier) : ‖Z.Wsummand f f ρ‖ ≤ (s ρ + s (e ρ)) / 2 := by
    dsimp only [s]
    rw [zeroConfigSquareSummand_reflectPerm]
    unfold ZeroConfig.Wsummand
    simp only [norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    have hs := mul_nonneg (Nat.cast_nonneg (Z.mult ρ) : (0 : ℝ) ≤ _)
      (sq_nonneg (‖paperFT f (gammaOf ρ)‖ - ‖paperFT f (conj (gammaOf ρ))‖))
    nlinarith only [hs]
  have hW_sum : Summable (fun ρ : Z.carrier => Z.Wsummand f f ρ) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hW_bound hb).of_norm
  have hWre_sum : Summable (fun ρ : Z.carrier => (Z.Wsummand f f ρ).re) :=
    Complex.reCLM.summable hW_sum
  have hdef_eq : (fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) / 2 * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2) =
      fun ρ => (s ρ + s (e ρ)) / 2 - (Z.Wsummand f f ρ).re := by
    funext ρ
    linarith [re_Wsummand_add_reflectionDefect_summand Z f ρ]
  unfold configurationReflectionDefect configurationSquareMass ZeroConfig.W
  rw [hdef_eq, hb.tsum_sub hWre_sum, tsum_div_const, hf.tsum_add hse, e.tsum_eq s,
    Complex.re_tsum hW_sum]
  dsimp only [s]
  ring

/-- For any tempered configuration `Z` and any `f ∈ C_c²(ℝ, ℂ)`, the multiplicity-weighted
zero-square summand is unconditionally summable. -/
theorem summable_squareMass_of_temperedConfig (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2) := by
  obtain ⟨w, -, hfs⟩ := exists_radius_bound hfc
  set C : ℝ := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)
  have hC0 : 0 ≤ C := mul_nonneg (by norm_num)
    (add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _))
  set B : ℝ := Real.exp |w| * C
  have hB0 : 0 ≤ B := mul_nonneg (Real.exp_pos _).le hC0
  set K : ℝ := B ^ 2 * (4 / 3)
  refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (fun ρ => ?_) (hZ.mul_left K)
  have hstrip := Z.strip ρ.1 ρ.2
  have him : |(gammaOf ρ).im| ≤ 1 / 2 := by
    rw [im_gammaOf, abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
  have hdecay := norm_paperFT_le_decay hf hfs (gammaOf ρ)
  have hE1 : Real.exp (|(gammaOf ρ).im| * w) ≤ Real.exp |w| := by
    apply Real.exp_le_exp.mpr
    calc |(gammaOf ρ).im| * w ≤ |(gammaOf ρ).im| * |w| :=
          mul_le_mul_of_nonneg_left (le_abs_self w) (abs_nonneg _)
      _ ≤ 1 * |w| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |w| := one_mul _
  have hden1 : 1 ≤ (1 + |(gammaOf ρ).re|) ^ 2 := by nlinarith [abs_nonneg (gammaOf ρ).re]
  have hden2 : 1 / (1 + |(gammaOf ρ).re|) ^ 2 ≤ (4 / 3) / (1 + Complex.normSq (gammaOf ρ)) := by
    rw [Complex.normSq_apply, div_le_div_iff₀ (by positivity)
      (by nlinarith [mul_self_nonneg (gammaOf ρ).re, mul_self_nonneg (gammaOf ρ).im])]
    have h1 : (gammaOf ρ).im * (gammaOf ρ).im ≤ 1 / 4 := by nlinarith [abs_le.mp him]
    nlinarith [abs_nonneg (gammaOf ρ).re, sq_abs (gammaOf ρ).re]
  have hP1 : ‖paperFT f (gammaOf ρ)‖ ≤ B / (1 + |(gammaOf ρ).re|) ^ 2 :=
    hdecay.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hE1 hC0) (by positivity))
  have hP_le_B : ‖paperFT f (gammaOf ρ)‖ ≤ B :=
    hP1.trans (div_le_self hB0 hden1)
  have hP_le_Bd : ‖paperFT f (gammaOf ρ)‖ ≤ B * ((4 / 3) / (1 + Complex.normSq (gammaOf ρ))) := by
    rw [div_eq_mul_one_div] at hP1
    exact hP1.trans (mul_le_mul_of_nonneg_left hden2 hB0)
  have hsq : ‖paperFT f (gammaOf ρ)‖ ^ 2 ≤
      B ^ 2 * ((4 / 3) / (1 + Complex.normSq (gammaOf ρ))) := by
    calc ‖paperFT f (gammaOf ρ)‖ ^ 2
        = ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f (gammaOf ρ)‖ := sq _
      _ ≤ B * (B * ((4 / 3) / (1 + Complex.normSq (gammaOf ρ)))) :=
          mul_le_mul hP_le_B hP_le_Bd (norm_nonneg _) hB0
      _ = B ^ 2 * ((4 / 3) / (1 + Complex.normSq (gammaOf ρ))) := by ring
  calc (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2
      ≤ (Z.mult ρ : ℝ) * (B ^ 2 * ((4 / 3) / (1 + Complex.normSq (gammaOf ρ)))) :=
        mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
    _ = K * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by dsimp only [K]; ring

/-- For any tempered configuration `Z` and any `f ∈ C_c²(ℝ, ℂ)`,
`configurationSquareMass Z f - (Z.W f f).re = configurationReflectionDefect Z f`. -/
theorem configurationSquareMass_sub_re_W_eq_reflectionDefect_of_tempered
    (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    configurationSquareMass Z f - (Z.W f f).re = configurationReflectionDefect Z f :=
  configurationSquareMass_sub_re_W_eq_reflectionDefect Z f
    (summable_squareMass_of_temperedConfig Z hZ hf hfc)

/-- **Actual-Zeta Zero-Side Reflection Identity.** For every `f ∈ C_c²(ℝ, ℂ)`, the literal
nontrivial zeros of `ζ` satisfy
`configurationSquareMass zetaZeroConfig f - (zetaZeroConfig.W f f).re = configurationReflectionDefect zetaZeroConfig f`. -/
theorem zeta_squareMass_sub_re_W_eq_reflectionDefect {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    configurationSquareMass zetaZeroConfig f - (zetaZeroConfig.W f f).re =
      configurationReflectionDefect zetaZeroConfig f :=
  configurationSquareMass_sub_re_W_eq_reflectionDefect_of_tempered
    zetaZeroConfig temperedConfig_zetaZeroConfig hf hfc

/-! ## Section 2: Unification of `fullZeroForm`, `compactFullWeilEnergy`, `weilFullFunctional`, and `zetaZeroConfig.W` -/

/-- The transform of a real compactly supported source at `i/2` is `evenPoleMoment F - oddPoleMoment F`. -/
theorem paperFT_ofReal_I_half_eq_moments {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    paperFT (fun x => (F x : ℂ)) (I / 2) = (evenPoleMoment F - oddPoleMoment F : ℂ) := by
  rw [_root_.RHTower.paperFT_ofReal_I_half_eq_integral]
  have hc : Integrable fun x => F x * Real.cosh (x / 2) :=
    integrable_mul_of_compactSupport hF hFc (Real.continuous_cosh.comp (continuous_id.div_const 2))
  have hs : Integrable fun x => F x * Real.sinh (x / 2) :=
    integrable_mul_of_compactSupport hF hFc (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hpt : (fun x => F x * Real.exp (-(x / 2))) =
      fun x => F x * Real.cosh (x / 2) - F x * Real.sinh (x / 2) := by
    funext x
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  rw [hpt, integral_sub hc hs, Complex.ofReal_sub]
  rfl

/-- The transform of a real compactly supported source at `-i/2` is `evenPoleMoment F + oddPoleMoment F`. -/
theorem paperFT_ofReal_neg_I_half_eq_moments {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    paperFT (fun x => (F x : ℂ)) (-I / 2) = (evenPoleMoment F + oddPoleMoment F : ℂ) := by
  have hneg : -I / 2 = -(I / 2) := by ring
  rw [hneg, ← paperFT_comp_neg, _root_.RHTower.paperFT_ofReal_I_half_eq_integral]
  have hc : Integrable fun x => F x * Real.cosh (x / 2) :=
    integrable_mul_of_compactSupport hF hFc (Real.continuous_cosh.comp (continuous_id.div_const 2))
  have hs : Integrable fun x => F x * Real.sinh (x / 2) :=
    integrable_mul_of_compactSupport hF hFc (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hchg : (∫ x, F (-x) * Real.exp (-(x / 2))) = ∫ x, F x * Real.exp (x / 2) := by
    rw [← MeasureTheory.integral_neg_eq_self (fun x => F (-x) * Real.exp (-(x / 2)))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [neg_neg, neg_div]
  have hpt : (fun x => F x * Real.exp (x / 2)) =
      fun x => F x * Real.cosh (x / 2) + F x * Real.sinh (x / 2) := by
    funext x
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  rw [hchg, hpt, integral_add hc hs, Complex.ofReal_add]
  rfl

/-- **Lorentz Moment Identity for the Weil Pole Term.** For any continuous compactly supported
real function `F`, the pole term of `EF.weilTest F F` equals `2 evenPoleMoment(F)² - 2 oddPoleMoment(F)²`. -/
theorem weilPoleTerm_ofReal_eq_lorentz_moments {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    (weilPoleTerm (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re =
      2 * evenPoleMoment F ^ 2 - 2 * oddPoleMoment F ^ 2 := by
  have hFc' : HasCompactSupport (fun x => (F x : ℂ)) := hFc.comp_left Complex.ofReal_zero
  have hF_cont : Continuous (fun x => (F x : ℂ)) := by fun_prop
  rw [_root_.RHTower.weilPoleTerm_weilTest_eq hF_cont hFc',
    paperFT_ofReal_I_half_eq_moments hF hFc, paperFT_ofReal_neg_I_half_eq_moments hF hFc]
  simp only [map_add, map_sub, Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
    Complex.sub_re, Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Exact Identity between ACT's `fullZeroForm` and RHTower's `weilFullFunctional`.**
For every continuous compactly supported `F : ℝ → ℝ` (without requiring `C²` regularity),
`fullZeroForm F` equals the real part of the full Weil functional of `Λ` on `EF.weilTest F F`. -/
theorem fullZeroForm_eq_re_weilFullFunctional {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    fullZeroForm F =
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by
  unfold fullZeroForm _root_.RHTower.markovEnergy
  rw [Complex.sub_re, weilPoleTerm_ofReal_eq_lorentz_moments hF hFc]
  ring

/-- **Exact Unification of ACT's `fullZeroForm` and APT's `compactFullWeilEnergy`.**
For every compactly supported continuous real source `g : C_c(ℝ, ℝ)` (including non-smooth
translated factorial-tent patterns), `fullZeroForm g = compactFullWeilEnergy g`. -/
theorem fullZeroForm_eq_compactFullWeilEnergy (g : C_c(ℝ, ℝ)) :
    fullZeroForm g = compactFullWeilEnergy g :=
  fullZeroForm_eq_re_weilFullFunctional g.continuous g.hasCompactSupport

/-- For every translated factorial-tent pattern, ACT's `fullZeroForm` coincides identically with
APT's `compactFullWeilEnergy`, and inherits the `O(1/(k+1))` complete-form mollification bound. -/
theorem factorialTentPattern_fullZeroForm_smoothing_error (S : Finset ℕ) (n : ℕ → ℕ)
    (b t : ℕ → ℝ) (k : ℕ) :
    |fullZeroForm (smoothCompactSource (factorialTentPattern S n b t) k) -
      fullZeroForm (factorialTentPattern S n b t)| ≤
      compactFullWeilApproximationCost (factorialTentPatternRadius S t)
        (factorialTentPatternValueBound S n b) (factorialTentPatternSlopeBound S n b) / ((k : ℝ) + 1) := by
  rw [fullZeroForm_eq_compactFullWeilEnergy, fullZeroForm_eq_compactFullWeilEnergy]
  exact factorialTentPattern_fullWeil_smoothing_error S n b t k

/-- **Five-Way Master Identity on `C_c²(ℝ, ℝ)`.** For every real `C_c²` test `F`,
ACT's `fullZeroForm F`, APT's `compactFullWeilEnergy F`, RHTower's `(weilFullFunctional Λ ...).re`,
SRT's `(zetaZeroConfig.W F F).re`, and the zero-side difference
`configurationSquareMass zetaZeroConfig F - configurationReflectionDefect zetaZeroConfig F` are all equal. -/
theorem fullZeroForm_eq_zeta_W_re {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    fullZeroForm F = (zetaZeroConfig.W (fun x => (F x : ℂ)) (fun x => (F x : ℂ))).re := by
  have hFd : ContDiff ℝ 2 (fun x => (F x : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
  have hFc' : HasCompactSupport (fun x => (F x : ℂ)) := hFc.comp_left Complex.ofReal_zero
  rw [fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc,
    weilFullFunctional_vonMangoldt, ← zeta_W_eq_literatureRHS hFd hFc']

theorem fullZeroForm_eq_zeta_squareMass_sub_reflectionDefect {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    fullZeroForm F =
      configurationSquareMass zetaZeroConfig (fun x => (F x : ℂ)) -
        configurationReflectionDefect zetaZeroConfig (fun x => (F x : ℂ)) := by
  have hFd : ContDiff ℝ 2 (fun x => (F x : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
  have hFc' : HasCompactSupport (fun x => (F x : ℂ)) := hFc.comp_left Complex.ofReal_zero
  rw [fullZeroForm_eq_zeta_W_re hF hFc, ← zeta_squareMass_sub_re_W_eq_reflectionDefect hFd hFc']
  ring

/-- **Single-Shift Gauge Realization of the Actual-Zeta Zero-Side Reflection Balance.**
For every shift `a > 0` and every even profile `u ∈ C_c²(ℝ, ℝ)`, ACT's gauge-invariant pole-free
variation form `2 S_a(u) - D_a(u) + V_a(u)` equals the actual-zeta zero-side difference
`configurationSquareMass zetaZeroConfig (liftC (Φ(ω_a u))) - configurationReflectionDefect zetaZeroConfig (liftC (Φ(ω_a u)))`. -/
theorem poleFreeForm_eq_zeta_squareMass_sub_reflectionDefect {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    2 * sameSideEnergy (shiftedGroundState a) u - reflectedDifferenceEnergy (shiftedGroundState a) u +
        profileVariance a u =
      configurationSquareMass zetaZeroConfig
        (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) -
      configurationReflectionDefect zetaZeroConfig
        (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
  have hzu : ContDiff ℝ 2 (fun y => shiftedGroundState a y * u y) :=
    (contDiff_shiftedGroundState a).mul hu
  have hzuc : HasCompactSupport (fun y => shiftedGroundState a y * u y) := huc.mul_left
  have hF : ContDiff ℝ 2 (phiDoobTest (fun y => shiftedGroundState a y * u y)) :=
    contDiff_phiDoobTest hzu
  have hFc : HasCompactSupport (phiDoobTest (fun y => shiftedGroundState a y * u y)) :=
    hasCompactSupport_phiDoobTest hzuc
  have hodd : ∀ x, phiDoobTest (fun y => shiftedGroundState a y * u y) (-x) =
      -phiDoobTest (fun y => shiftedGroundState a y * u y) x := fun x => by
    unfold phiDoobTest
    dsimp only
    rw [riemannKernelReal_neg', shiftedGroundState_neg, heven]
    ring
  rw [poleFreeForm_eq_zeroForm ha hu huc heven]
  have hzf : zeroForm (phiDoobTest (fun y => shiftedGroundState a y * u y)) =
      fullZeroForm (phiDoobTest (fun y => shiftedGroundState a y * u y)) := by
    unfold fullZeroForm zeroForm
    rw [evenPoleMoment_eq_zero_of_odd hodd]
    ring
  rw [hzf, fullZeroForm_eq_zeta_squareMass_sub_reflectionDefect hF hFc]

/-- **Theta-Span Radical Invariance of the Actual-Zeta Zero-Side Reflection Balance.**
Adding the plateau truncation `Φ(ω u_L)` of any finite combination of theta translates
`ω = Σ_{j ∈ s} α_j τ_{b_j}` to `Φ v` leaves the actual-zeta zero-side balance
`configurationSquareMass - configurationReflectionDefect` asymptotically invariant as `L → ∞`. -/
theorem tendsto_zeta_squareMass_sub_reflectionDefect_add_translatePlateau {ι : Type*}
    (s : Finset ι) (α b : ι → ℝ) {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    Tendsto (fun L =>
      configurationSquareMass zetaZeroConfig
        (fun x => (phiDoobTest (fun y => translateSpan s α b y * smoothPlateau L y + v y) x : ℂ)) -
      configurationReflectionDefect zetaZeroConfig
        (fun x => (phiDoobTest (fun y => translateSpan s α b y * smoothPlateau L y + v y) x : ℂ)))
      atTop
      (𝓝 (configurationSquareMass zetaZeroConfig (fun x => (phiDoobTest v x : ℂ)) -
        configurationReflectionDefect zetaZeroConfig (fun x => (phiDoobTest v x : ℂ)))) := by
  have hlim := tendsto_fullZeroForm_add_translatePlateau s α b hv hvc
  rw [fullZeroForm_eq_zeta_squareMass_sub_reflectionDefect (contDiff_phiDoobTest hv)
    (hasCompactSupport_phiDoobTest hvc)] at hlim
  refine hlim.congr fun L => ?_
  have hz : ContDiff ℝ 2 (fun y => translateSpan s α b y * smoothPlateau L y + v y) :=
    ((contDiff_translateSpan s α b).mul (contDiff_smoothPlateau L)).add hv
  have hzc : HasCompactSupport (fun y => translateSpan s α b y * smoothPlateau L y + v y) :=
    ((hasCompactSupport_smoothPlateau L).mul_left).add hvc
  exact fullZeroForm_eq_zeta_squareMass_sub_reflectionDefect
    (contDiff_phiDoobTest hz) (hasCompactSupport_phiDoobTest hzc)

/-! ## Section 3: Actual-Zeta Real-Imaginary Splitting & Off-Line Detection by Single-Scale Grid Tent Patterns -/

/-- **Actual-Zeta Zero-Side Real-Imaginary Splitting.** For every `f ∈ C_c²(ℝ, ℂ)`,
the zero-side Weil energy `(zetaZeroConfig.W f f).re` splits additively into `fullZeroForm`
on the real and imaginary parts of `f`. -/
theorem zeta_W_re_eq_fullZeroForm_re_add_im {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (zetaZeroConfig.W f f).re =
      fullZeroForm (fun u => (f u).re) + fullZeroForm (fun u => (f u).im) := by
  set lam : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ)
  set F : WeilTestFn := ⟨f, hf, hfc⟩
  set R := paperRealPartTestFn F
  set J := paperImagPartTestFn F
  have hsplit : paperSplitRealMixture (Finsupp.single F 1) =
      Finsupp.single R 1 + Finsupp.single J 1 := by
    simp [paperSplitRealMixture, R, J, Finsupp.mapDomain_single]
  have hE := energy_paperSplitRealMixture (Finsupp.single F 1)
  have hD := defect_paperSplitRealMixture (Finsupp.single F 1)
  rw [hsplit] at hE hD
  simp only [energy, defect, map_add, linearCombination_single, one_smul] at hE hD
  have hF := re_weilFullFunctional_eq lam F
  have hRe := re_weilFullFunctional_eq lam R
  have hIm := re_weilFullFunctional_eq lam J
  have hRe_cont : ContDiff ℝ 2 (fun u => (f u).re) := Complex.reCLM.contDiff.comp hf
  have hIm_cont : ContDiff ℝ 2 (fun u => (f u).im) := Complex.imCLM.contDiff.comp hf
  have hRe_cpt : HasCompactSupport (fun u => (f u).re) :=
    hfc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hIm_cpt : HasCompactSupport (fun u => (f u).im) :=
    hfc.comp_left (g := fun z : ℂ => z.im) (by simp)
  rw [zeta_W_eq_literatureRHS hf hfc, ← weilFullFunctional_vonMangoldt,
    fullZeroForm_eq_re_weilFullFunctional hRe_cont.continuous hRe_cpt,
    fullZeroForm_eq_re_weilFullFunctional hIm_cont.continuous hIm_cpt]
  have hfF : (weilFullFunctional lam (EF.weilTest f f)).re =
      (weilFullFunctional lam (EF.weilTest F.1 F.1)).re := rfl
  have hRe' : (weilFullFunctional lam (EF.weilTest R.1 R.1)).re =
      (weilFullFunctional lam
        (EF.weilTest (fun u => ((f u).re : ℂ)) (fun u => ((f u).re : ℂ)))).re := rfl
  have hIm' : (weilFullFunctional lam (EF.weilTest J.1 J.1)).re =
      (weilFullFunctional lam
        (EF.weilTest (fun u => ((f u).im : ℂ)) (fun u => ((f u).im : ℂ)))).re := rfl
  rw [hfF, ← hRe', ← hIm', hF, hRe, hIm, ← hE, ← hD, map_add]
  ring

/-- If a complex `C_c²` test supported inside `[-R, R]` has `(zetaZeroConfig.W f f).re < 0`,
then either its real part or its imaginary part is a real `C_c²` test vanishing outside `[-R, R]`
with `fullZeroForm φ ≤ (zetaZeroConfig.W f f).re / 2 < 0`. -/
theorem exists_real_contDiff_fullZeroForm_neg_of_zeta_W_neg {f : ℝ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hfR : ∀ x, R < |x| → f x = 0)
    (hneg : (zetaZeroConfig.W f f).re < 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧ (∀ x, R < |x| → φ x = 0) ∧
      fullZeroForm φ ≤ (zetaZeroConfig.W f f).re / 2 ∧ fullZeroForm φ < 0 := by
  have hsplit := zeta_W_re_eq_fullZeroForm_re_add_im hf hfc
  have hRe_cont : ContDiff ℝ 2 (fun u => (f u).re) := Complex.reCLM.contDiff.comp hf
  have hIm_cont : ContDiff ℝ 2 (fun u => (f u).im) := Complex.imCLM.contDiff.comp hf
  have hRe_cpt : HasCompactSupport (fun u => (f u).re) :=
    hfc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hIm_cpt : HasCompactSupport (fun u => (f u).im) :=
    hfc.comp_left (g := fun z : ℂ => z.im) (by simp)
  rcases le_total (fullZeroForm (fun u => (f u).re)) (fullZeroForm (fun u => (f u).im)) with hle | hle
  · refine ⟨fun u => (f u).re, hRe_cont, hRe_cpt, fun x hx => by simp [hfR x hx], ?_, ?_⟩ <;> linarith
  · refine ⟨fun u => (f u).im, hIm_cont, hIm_cpt, fun x hx => by simp [hfR x hx], ?_, ?_⟩ <;> linarith

/-- Coefficient family of the single-scale grid tent pattern `gridTentPattern G n a M`. -/
def gridTentCoeff (G : ℝ → ℝ) (n : ℕ) (a : ℝ) (i : ℕ) : ℝ :=
  G (a + i * sourceFactorialWidth (n + 1)) *
    (Real.exp (sourceFactorialWidth (n + 1)) - 1) ^ 2 *
    Real.exp (-(3 * (sourceFactorialWidth (n + 1) - (a + i * sourceFactorialWidth (n + 1))) / 2)) /
    sourceFactorialWidth (n + 1)

/-- Translation site family of the single-scale grid tent pattern `gridTentPattern G n a M`. -/
def gridTentSite (n : ℕ) (a : ℝ) (i : ℕ) : ℝ :=
  sourceFactorialWidth (n + 1) - (a + i * sourceFactorialWidth (n + 1))

theorem gridTentPattern_eq_factorialTentPattern (G : ℝ → ℝ) (n : ℕ) (a : ℝ) (M : ℕ) :
    gridTentPattern G n a M =
      factorialTentPattern (Finset.range (M + 1)) (fun _ => n)
        (gridTentCoeff G n a) (gridTentSite n a) := rfl

/-- Smoothing index that pays the complete-form approximation cost of `gridTentPattern G n a M`
to within `1/(q+1)`. -/
def gridTentSmoothingIndex (G : ℝ → ℝ) (n : ℕ) (a : ℝ) (M q : ℕ) : ℕ :=
  factorialTentPatternSmoothingIndex (Finset.range (M + 1)) (fun _ => n)
    (gridTentCoeff G n a) (gridTentSite n a) q

/-- The smoothed `C_c²(ℝ, ℂ)` detector associated to a single-scale grid tent pattern `gridTentPattern G n a M`. -/
def smoothGridTentDetector (G : ℝ → ℝ) (n : ℕ) (a : ℝ) (M q : ℕ) : ℝ → ℂ :=
  liftC (smoothCompactSource (gridTentPattern G n a M) (gridTentSmoothingIndex G n a M q))

theorem smoothGridTentDetector_admissible (G : ℝ → ℝ) (n : ℕ) (a : ℝ) (M q : ℕ) :
    ContDiff ℝ 2 (smoothGridTentDetector G n a M q) ∧
      HasCompactSupport (smoothGridTentDetector G n a M q) := by
  let f := gridTentPattern G n a M
  let k := gridTentSmoothingIndex G n a M q
  exact ⟨contDiff_liftC (smooth_contDiff (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport) k),
    hasCompactSupport_liftC (smoothCompactSource f k).hasCompactSupport⟩

/-- Joint complete-form approximation for `smoothGridTentDetector`, simultaneously equal to
the actual-zeta zero-side Weil form and `configurationSquareMass - configurationReflectionDefect`. -/
theorem smoothGridTentDetector_fullWeil_approximation (G : ℝ → ℝ) (n : ℕ) (a : ℝ) (M q : ℕ) :
    |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
        (EF.weilTest (smoothGridTentDetector G n a M q) (smoothGridTentDetector G n a M q))).re -
      compactFullWeilEnergy (gridTentPattern G n a M)| ≤ 1 / ((q : ℝ) + 1) ∧
    (zetaZeroConfig.W (smoothGridTentDetector G n a M q) (smoothGridTentDetector G n a M q)).re =
      (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
        (EF.weilTest (smoothGridTentDetector G n a M q) (smoothGridTentDetector G n a M q))).re ∧
    configurationSquareMass zetaZeroConfig (smoothGridTentDetector G n a M q) -
        (zetaZeroConfig.W (smoothGridTentDetector G n a M q) (smoothGridTentDetector G n a M q)).re =
      configurationReflectionDefect zetaZeroConfig (smoothGridTentDetector G n a M q) := by
  obtain ⟨hd, hc⟩ := smoothGridTentDetector_admissible G n a M q
  refine ⟨?_, ?_, zeta_squareMass_sub_re_W_eq_reflectionDefect hd hc⟩
  · exact factorialTentPattern_joint_approximation (Finset.range (M + 1)) (fun _ => n)
      (gridTentCoeff G n a) (gridTentSite n a) q
  · rw [zeta_W_eq_literatureRHS hd hc, weilFullFunctional_vonMangoldt]

/-- **Actual-Zeta Detector Specification for Negative Real `C_c²` Seeds.**
Given any `φ ∈ C_c²(ℝ, ℝ)` vanishing outside `[-R, R]` (`R ≥ 0`) with `fullZeroForm φ < 0`,
let `G(x) = e^{-3x/2} φ(x)` and `μ = -fullZeroForm φ / 4 > 0`. For all sufficiently large
arithmetic scales `n` (`∀ᶠ n in atTop`) and every accuracy index `q` with `1/(q+1) ≤ μ`, the
single-scale grid factorial-tent pattern `P_n` and its smoothed detector `D_{n,q}` simultaneously
achieve strict negativity `≤ -μ < 0` on `compactFullWeilEnergy`, `fullZeroForm`,
`weilFullFunctional Λ`, `zetaZeroConfig.W`, and the actual-zeta reflection gap
`configurationReflectionDefect zetaZeroConfig D_{n,q} - configurationSquareMass zetaZeroConfig D_{n,q} ≥ μ`. -/
theorem gridTentPattern_actual_zeta_detector_spec {φ : ℝ → ℝ} {R : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hR : 0 ≤ R)
    (hφR : ∀ x, R < |x| → φ x = 0) (hneg : fullZeroForm φ < 0) :
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * φ x
    let μ : ℝ := -fullZeroForm φ / 4
    0 < μ ∧ ∀ᶠ n : ℕ in atTop,
      let M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
      let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
      compactFullWeilEnergy P ≤ -2 * μ ∧
      fullZeroForm P ≤ -2 * μ ∧
      ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
        let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
        ContDiff ℝ 2 D ∧
        HasCompactSupport D ∧
        |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
            (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
        (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
            (EF.weilTest D D)).re ≤ -μ ∧
        (zetaZeroConfig.W D D).re ≤ -μ ∧
        μ ≤ configurationReflectionDefect zetaZeroConfig D -
          configurationSquareMass zetaZeroConfig D := by
  dsimp only
  set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * φ x
  set μ : ℝ := -fullZeroForm φ / 4
  have hμ : 0 < μ := by dsimp [μ]; linarith
  refine ⟨hμ, ?_⟩
  set φc : C_c(ℝ, ℝ) := ⟨⟨φ, hφ.continuous⟩, hφc⟩
  have hφ_eq : compactFullWeilEnergy φc = fullZeroForm φ :=
    (fullZeroForm_eq_compactFullWeilEnergy φc).symm
  obtain ⟨Mg, hMg⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨Kg, hKg⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by norm_num)
  have hGc : ContDiff ℝ 2 G := by dsimp [G]; fun_prop
  obtain ⟨L, hL⟩ := hGc.lipschitzWith_of_hasCompactSupport (hφc.mul_left) (by norm_num)
  have hlim := tendsto_compactFullWeilEnergy_gridTentPattern φc hR hφR
    (fun x => by rw [← Real.norm_eq_abs]; exact hMg x)
    (fun x y => by have := hKg.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this)
    (fun x y => by have := hL.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this)
  have hlt : compactFullWeilEnergy φc < -2 * μ := by rw [hφ_eq]; dsimp [μ]; linarith
  filter_upwards [hlim.eventually (eventually_lt_nhds hlt)] with n hn
  set M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
  set P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
  have hP_le : compactFullWeilEnergy P ≤ -2 * μ := le_of_lt hn
  have hP_zf : fullZeroForm P ≤ -2 * μ := by
    rw [fullZeroForm_eq_compactFullWeilEnergy P]
    exact hP_le
  refine ⟨hP_le, hP_zf, fun q hq => ?_⟩
  set D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
  obtain ⟨hD_diff, hD_cpt⟩ := smoothGridTentDetector_admissible G n (-(R + 1)) M q
  obtain ⟨hD_approx, hD_W, hD_refl⟩ := smoothGridTentDetector_fullWeil_approximation G n (-(R + 1)) M q
  have hD_weil_le : (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
      (EF.weilTest D D)).re ≤ -μ := by
    have h1 := (abs_le.mp hD_approx).2
    linarith
  have hD_zeta_le : (zetaZeroConfig.W D D).re ≤ -μ := by
    rw [hD_W]
    exact hD_weil_le
  have hD_gap : μ ≤ configurationReflectionDefect zetaZeroConfig D -
      configurationSquareMass zetaZeroConfig D := by
    linarith [hD_refl, hD_zeta_le]
  exact ⟨hD_diff, hD_cpt, hD_approx, hD_weil_le, hD_zeta_le, hD_gap⟩

/-- **Unconditional Actual-Zeta Off-Line Zero Detection by Single-Scale Grid Tent Patterns.**
Every off-line zero `ρ₀ ∈ zetaZeroConfig.carrier` (`ρ₀.re ≠ 1/2`), regardless of multiplicity,
clustering, or the non-periodic background of on-line zeros of `ζ`, is detected at all sufficiently
large arithmetic scales `n` by a single-scale grid factorial-tent pattern and its smoothed `C_c²`
detector with an explicit strictly positive margin `μ > 0`. -/
theorem actual_zeta_offLine_detected_by_gridTentPattern {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hre : ρ₀.re ≠ 1 / 2) :
    ∃ (G : ℝ → ℝ) (R μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧ 0 ≤ R ∧ 0 < μ ∧
      ∀ᶠ n : ℕ in atTop,
        let M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
        compactFullWeilEnergy P ≤ -2 * μ ∧
        fullZeroForm P ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D := by
  obtain ⟨f, hf, hfc, hneg⟩ := offLine_visible zetaZeroConfig temperedConfig_zetaZeroConfig hρ₀ hre
  obtain ⟨R, hR, hfR⟩ := exists_radius_bound hfc
  have hfR' : ∀ x, R < |x| → f x = 0 := fun x hx => by
    by_contra hne
    exact not_le.mpr hx (hfR x hne)
  obtain ⟨φ, hφ, hφc, hφR, -, hφneg⟩ :=
    exists_real_contDiff_fullZeroForm_neg_of_zeta_W_neg hf hfc hfR' hneg
  have hspec := gridTentPattern_actual_zeta_detector_spec hφ hφc hR hφR hφneg
  refine ⟨fun x => Real.exp (-(3 * x / 2)) * φ x, R, -fullZeroForm φ / 4,
    by fun_prop, hφc.mul_left, hR, hspec.1, hspec.2⟩

/-- **Explicit-Aperture Actual-Zeta Finite-Off-Line Set Detection by Single-Scale Grid Tent Patterns.**
If the off-line zeros of `zetaZeroConfig` right of the critical line form a finite set `T` with
top point `t₀ ∈ T` and depth gap `g ∈ (0, t₀.re - 1/2]`, then for every aperture
`a ≥ (1/2g) log⁺((2 M_b + 4 Σ_{t ∈ T} ‖q_t‖)/c) + (|T| + 2)ℓ/2 + w`, there exist a seed `G`
supported in `[-a, a]` and a margin `μ > 0` such that the single-scale grid tent pattern on
`[-(a+1), a+1]` and its smoothed detector detect `zetaZeroConfig` with margin `μ` for all large `n`. -/
theorem actual_zeta_finiteOffLine_detected_by_gridTentPattern_at_aperture
    {T : Finset ℂ} {t₀ : ℂ} (ht₀ : t₀ ∈ T) {g : ℝ} (hg : 0 < g) (hgD : g ≤ t₀.re - 1 / 2)
    (hgap : ∀ t ∈ T, t.re ≠ t₀.re → t.re ≤ t₀.re - g) {w : ℝ} (hw : 0 < w) :
    ∃ c ℓ : ℝ, 0 < c ∧ 0 < ℓ ∧
      ((∀ z, z ∈ T ↔ z ∈ zetaZeroConfig.carrier ∧ 1 / 2 < z.re) →
      ∀ a : ℝ, 1 / (2 * g) * max 0 (Real.log ((2 * onLineMassOf zetaZeroConfig (modScaledBump w t₀.im) +
          4 * ∑ t ∈ T, ‖offLineWeight (modScaledBump w t₀.im) (zetaZeroConfig.mult t) t‖) / c)) +
          (T.card + 2) * ℓ / 2 + w ≤ a →
        ∃ (G : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧
          (∀ x, a < |x| → G x = 0) ∧ 0 < μ ∧
          ∀ᶠ n : ℕ in atTop,
            let M : ℕ := ⌈2 * (a + 1) / sourceFactorialWidth (n + 1)⌉₊
            let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(a + 1)) M
            compactFullWeilEnergy P ≤ -2 * μ ∧
            fullZeroForm P ≤ -2 * μ ∧
            ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
              let D : ℝ → ℂ := smoothGridTentDetector G n (-(a + 1)) M q
              ContDiff ℝ 2 D ∧
              HasCompactSupport D ∧
              |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
                  (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
              (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
                  (EF.weilTest D D)).re ≤ -μ ∧
              (zetaZeroConfig.W D D).re ≤ -μ ∧
              μ ≤ configurationReflectionDefect zetaZeroConfig D -
                configurationSquareMass zetaZeroConfig D) := by
  obtain ⟨c, ℓ, hc, hℓ, hvis⟩ :=
    finiteOffLine_visible zetaZeroConfig.mult ht₀ hg hgD hgap hw
  refine ⟨c, ℓ, hc, hℓ, fun hT a ha => ?_⟩
  have ha0 : 0 ≤ a := by
    have h1 : 0 ≤ 1 / (2 * g) * max 0 (Real.log ((2 * onLineMassOf zetaZeroConfig (modScaledBump w t₀.im) +
        4 * ∑ t ∈ T, ‖offLineWeight (modScaledBump w t₀.im) (zetaZeroConfig.mult t) t‖) / c)) := by
      positivity
    have h2 : 0 ≤ (T.card + 2 : ℝ) * ℓ / 2 := by positivity
    linarith
  obtain ⟨f, hf, hfs, hneg⟩ :=
    hvis zetaZeroConfig temperedConfig_zetaZeroConfig hT (fun _ _ => rfl) a ha
  have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  have hfa : ∀ x, a < |x| → f x = 0 := fun x hx => by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := abs_le.mpr (hfs hmem)
    linarith
  obtain ⟨φ, hφ, hφc, hφa, -, hφneg⟩ :=
    exists_real_contDiff_fullZeroForm_neg_of_zeta_W_neg hf hfc hfa hneg
  have hspec := gridTentPattern_actual_zeta_detector_spec hφ hφc ha0 hφa hφneg
  refine ⟨fun x => Real.exp (-(3 * x / 2)) * φ x, -fullZeroForm φ / 4,
    by fun_prop, hφc.mul_left, fun x hx => by simp [hφa x hx], hspec.1, hspec.2⟩

/-- **Single-Scale Grid Factorial-Tent Completeness for the Riemann Hypothesis.**
RH holds if and only if for every `G : ℝ → ℝ` and every `R ≥ 0`, the single-scale uniform-grid
factorial-tent pattern `gridTentPattern G n (-(R+1)) ⌈2(R+1)/d_n⌉₊` has nonnegative complete
Weil energy (equivalently, nonnegative `fullZeroForm`) for all sufficiently large scales `n`. -/
theorem riemannHypothesis_iff_eventually_gridTentPattern_nonneg :
    RiemannHypothesis ↔ ∀ (G : ℝ → ℝ) (R : ℝ), 0 ≤ R →
      ∀ᶠ n : ℕ in atTop,
        0 ≤ compactFullWeilEnergy
          (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊) := by
  constructor
  · intro hRH G R _
    exact Eventually.of_forall fun n =>
      riemannHypothesis_iff_factorialTentPattern_nonneg.mp hRH _ _ _ _
  · intro h
    rw [_root_.RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive]
    intro g hg hgc
    set gc : C_c(ℝ, ℝ) := ⟨⟨g, hg.continuous⟩, hgc⟩
    obtain ⟨R₀, hR₀⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    set R := max R₀ 0
    have hR : 0 ≤ R := le_max_right R₀ 0
    have hgR : ∀ x, R < |x| → gc x = 0 := fun x hx => by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hR₀ hmem
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      linarith [le_max_left R₀ 0]
    obtain ⟨Mg, hMg⟩ := hg.continuous.bounded_above_of_compact_support hgc
    obtain ⟨Kg, hKg⟩ := hg.lipschitzWith_of_hasCompactSupport hgc (by norm_num)
    have hGc : ContDiff ℝ 2 fun x => Real.exp (-(3 * x / 2)) * g x := by fun_prop
    obtain ⟨L, hL⟩ := hGc.lipschitzWith_of_hasCompactSupport (hgc.mul_left) (by norm_num)
    have hlim := tendsto_compactFullWeilEnergy_gridTentPattern gc hR hgR
      (fun x => by rw [← Real.norm_eq_abs]; exact hMg x)
      (fun x y => by have := hKg.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this)
      (fun x y => by have := hL.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this)
    exact ge_of_tendsto hlim (h (fun x => Real.exp (-(3 * x / 2)) * gc x) R hR)

/-- **Single-Shift Origin-Vanishing Doob Profile Detection by Single-Scale Grid Tent Patterns.**
Without RH, for every shift `a > 0`, there exist an even profile `u ∈ C_c²(ℝ, ℝ)` vanishing
on `(-ε, ε)` (`ε > 0`), a support radius `R ≥ 0`, and a margin `μ > 0` such that the single-shift
pole-free variation form `2 S_a(u) - D_a(u) + V_a(u)` is `≤ -4μ < 0`, and for all sufficiently
large arithmetic scales `n`, the single-scale grid tent pattern of `Φ(ω_a u)` and its smoothed
detector simultaneously achieve `≤ -μ < 0` on `compactFullWeilEnergy`, `fullZeroForm`,
`weilFullFunctional Λ`, and `zetaZeroConfig.W`. -/
theorem singleShift_vanishing_profile_detected_by_gridTentPattern_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) {a : ℝ} (ha : 0 < a) :
    ∃ (u : ℝ → ℝ) (ε R μ : ℝ), ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      0 < ε ∧ (∀ x, |x| < ε → u x = 0) ∧ 0 ≤ R ∧ 0 < μ ∧
      2 * sameSideEnergy (shiftedGroundState a) u - reflectedDifferenceEnergy (shiftedGroundState a) u +
          profileVariance a u ≤ -4 * μ ∧
      let F : ℝ → ℝ := phiDoobTest (fun y => shiftedGroundState a y * u y)
      let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
      ∀ᶠ n : ℕ in atTop,
        let M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
        compactFullWeilEnergy P ≤ -2 * μ ∧
        fullZeroForm P ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D := by
  obtain ⟨u, ε, hu, huc, heven, hε, hvan, hneg⟩ :=
    exists_profile_vanishing_markovEnergy_neg_of_not_riemannHypothesis hRH ha
  set F : ℝ → ℝ := phiDoobTest (fun y => shiftedGroundState a y * u y)
  have hzu : ContDiff ℝ 2 (fun y => shiftedGroundState a y * u y) :=
    (contDiff_shiftedGroundState a).mul hu
  have hzuc : HasCompactSupport (fun y => shiftedGroundState a y * u y) := huc.mul_left
  have hF : ContDiff ℝ 2 F := contDiff_phiDoobTest hzu
  have hFc : HasCompactSupport F := hasCompactSupport_phiDoobTest hzuc
  have hodd : ∀ x, F (-x) = -F x := fun x => by
    dsimp [F]
    unfold phiDoobTest
    dsimp only
    rw [riemannKernelReal_neg', shiftedGroundState_neg, heven]
    ring
  have hzf_eq : fullZeroForm F = zeroForm F := by
    unfold fullZeroForm zeroForm
    rw [evenPoleMoment_eq_zero_of_odd hodd]
    ring
  have hzf_le : fullZeroForm F ≤ markovEnergy (fun x => (F x : ℂ)) := by
    rw [hzf_eq]
    unfold zeroForm
    nlinarith [sq_nonneg (oddPoleMoment F)]
  have hzf_neg : fullZeroForm F < 0 := lt_of_le_of_lt hzf_le hneg
  obtain ⟨R₀, hR₀⟩ := hFc.isCompact.isBounded.subset_closedBall 0
  set R := max R₀ 0
  have hR : 0 ≤ R := le_max_right R₀ 0
  have hFR : ∀ x, R < |x| → F x = 0 := fun x hx => by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hR₀ hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith [le_max_left R₀ 0]
  have hspec := gridTentPattern_actual_zeta_detector_spec hF hFc hR hFR hzf_neg
  have hpole : 2 * sameSideEnergy (shiftedGroundState a) u -
      reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u ≤
      -4 * (-fullZeroForm F / 4) := by
    rw [poleFreeForm_eq_zeroForm ha hu huc heven, ← hzf_eq]
    linarith
  refine ⟨u, ε, R, -fullZeroForm F / 4, hu, huc, heven, hε, hvan, hR, hspec.1, hpole, ?_⟩
  filter_upwards [hspec.2] with n hn
  refine ⟨hn.1, hn.2.1, fun q hq => ?_⟩
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := hn.2.2 q hq
  exact ⟨h1, h2, h4, h5, h6⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
end
