import GaloisForLFunctions.RHTower.CCM.CCMTruncatedExponentialFourierBudget
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPrimeOuterShell
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarShiftLower
import GaloisForLFunctions.RHTower.PrimeMassSharpUpper

/-!
# Finite exponential control of the actual remainder orbit

Translations and aperture projections preserve finite truncated-exponential
representations. The complete prime sum and crossed polar operator increase
their endpoint budget by at most a fixed multiple of `exp a`. The prescribed
Suzuki shift absorbs this aperture factor. Consequently every normalized
remainder iterate of the odd pole source has a certified representation and
an almost-everywhere Fourier bound, with cost exponential only in iteration
count. No regularity of the unknown Riesz response is assumed.

The integrated tail, source norm contraction, odd response energy, signed
Wronskian, and removal of the form shift remain separate obligations.
-/

open MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry
open scoped FourierTransform InnerProduct ENNReal
noncomputable section
namespace RHTower

/-- A finite source representation with an upper bound on its total endpoint
amplitude. Every constructor acts on the actual L2 vector. -/
inductive CCMFiniteExponentialBudget : SoninL2 → ℝ → Prop
  | zero : CCMFiniteExponentialBudget 0 0
  | atom (s l r : ℝ) (z : ℂ) (f : SoninL2) (hlr : l ≤ r)
      (hf : (f : ℝ → ℂ) =ᵐ[volume] ccmTruncatedExponential s l r z) :
      CCMFiniteExponentialBudget f (ccmTruncatedExponentialBudget s l r z)
  | add {f g : SoninL2} {V W : ℝ}
      (hf : CCMFiniteExponentialBudget f V) (hg : CCMFiniteExponentialBudget g W) :
      CCMFiniteExponentialBudget (f + g) (V + W)
  | smul (z : ℂ) {f : SoninL2} {V : ℝ} (hf : CCMFiniteExponentialBudget f V) :
      CCMFiniteExponentialBudget (z • f) (‖z‖ * V)
  | mono {f : SoninL2} {V W : ℝ} (hf : CCMFiniteExponentialBudget f V) (hVW : V ≤ W) :
      CCMFiniteExponentialBudget f W

namespace CCMFiniteExponentialBudget

theorem nonneg {f : SoninL2} {V : ℝ} (hf : CCMFiniteExponentialBudget f V) : 0 ≤ V := by
  induction hf with
  | zero => rfl
  | atom => unfold ccmTruncatedExponentialBudget; positivity
  | add _ _ ihf ihg => exact add_nonneg ihf ihg
  | smul z _ ih => exact mul_nonneg (norm_nonneg z) ih
  | mono _ hVW ih => exact ih.trans hVW

theorem ae_norm_le {f : SoninL2} {V : ℝ} (hf : CCMFiniteExponentialBudget f V) :
    ∀ᵐ x : ℝ, ‖f x‖ ≤ V := by
  induction hf with
  | zero =>
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)] with x hx
      rw [hx]
      simp
  | atom s l r z f hlr hrep =>
      filter_upwards [hrep] with x hx
      rw [hx]
      exact norm_ccmTruncatedExponential_le s l r z x
  | @add f g V W hf hg ihf ihg =>
      filter_upwards [Lp.coeFn_add f g, ihf, ihg] with x hx hfx hgx
      rw [hx]
      exact (norm_add_le _ _).trans (add_le_add hfx hgx)
  | @smul z f V hf ih =>
      filter_upwards [Lp.coeFn_smul z f, ih] with x hx hfx
      rw [hx, Pi.smul_apply, norm_smul]
      exact mul_le_mul_of_nonneg_left hfx (norm_nonneg z)
  | mono hf hVW ih => exact ih.mono fun _ hx => hx.trans hVW

theorem integrable {f : SoninL2} {V : ℝ} (hf : CCMFiniteExponentialBudget f V) :
    Integrable (f : ℝ → ℂ) := by
  induction hf with
  | zero => exact (integrable_zero ℝ ℂ volume).congr (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)).symm
  | atom s l r z f hlr hrep => exact (integrable_ccmTruncatedExponential s l r z).congr hrep.symm
  | @add f g V W hf hg ihf ihg => exact (ihf.add ihg).congr (Lp.coeFn_add f g).symm
  | @smul z f V hf ih => exact (ih.smul z).congr (Lp.coeFn_smul z f).symm
  | mono hf hVW ih => exact ih

/-- Uniform Fourier decay survives every constructor of the source class. -/
theorem ae_norm_fourier_le {f : SoninL2} {V : ℝ} (hf : CCMFiniteExponentialBudget f V) :
    ∀ᵐ ξ : ℝ, ξ ≠ 0 → ‖(𝓕 f : SoninL2) ξ‖ ≤ V / (Real.pi * |ξ|) := by
  induction hf with
  | zero =>
      simp only [FourierTransform.fourier_zero]
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)] with ξ hξ
      simp
  | atom s l r z f hlr hrep =>
      have hint := (integrable_ccmTruncatedExponential s l r z).congr hrep.symm
      have hfour := GaloisForLFunctions.RHTower.coeFn_fourier_toLp hint (Lp.memLp f)
      rw [Lp.toLp_coeFn] at hfour
      filter_upwards [hfour] with ξ hξ
      intro hξ0
      rw [hξ, Real.fourier_congr_ae hrep ξ]
      exact norm_fourier_ccmTruncatedExponential_le hlr s z hξ0
  | @add f g V W hf hg ihf ihg =>
      rw [FourierTransform.fourier_add]
      filter_upwards [Lp.coeFn_add (𝓕 f : SoninL2) (𝓕 g : SoninL2), ihf, ihg] with ξ hξ hfx hgx
      intro hξ0
      rw [hξ, Pi.add_apply, add_div]
      exact (norm_add_le _ _).trans (add_le_add (hfx hξ0) (hgx hξ0))
  | @smul z f V hf ih =>
      rw [FourierTransform.fourier_smul]
      filter_upwards [Lp.coeFn_smul z (𝓕 f : SoninL2), ih] with ξ hξ hfx
      intro hξ0
      rw [hξ, Pi.smul_apply, norm_smul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hfx hξ0) (norm_nonneg z)
  | mono hf hVW ih =>
      filter_upwards [ih] with ξ hξ
      intro hξ0
      exact (hξ hξ0).trans (div_le_div_of_nonneg_right hVW (by positivity))

theorem neg {f : SoninL2} {V : ℝ} (hf : CCMFiniteExponentialBudget f V) :
    CCMFiniteExponentialBudget (-f) V := by
  simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using hf.smul (-1)

theorem sub {f g : SoninL2} {V W : ℝ} (hf : CCMFiniteExponentialBudget f V)
    (hg : CCMFiniteExponentialBudget g W) : CCMFiniteExponentialBudget (f - g) (V + W) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem finset_sum {ι : Type*} (t : Finset ι) (f : ι → SoninL2) (V : ι → ℝ)
    (hf : ∀ i ∈ t, CCMFiniteExponentialBudget (f i) (V i)) :
    CCMFiniteExponentialBudget (∑ i ∈ t, f i) (∑ i ∈ t, V i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using CCMFiniteExponentialBudget.zero
  | @insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self _ _)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem translation_ae (h : ℝ) (f : SoninL2) :
    (logTranslationCLM h f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + h) :=
  (Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving h)).trans
      (Eventually.of_forall fun _ => rfl)

/-- Every literal prime translation preserves the source budget. -/
theorem translate {f : SoninL2} {V : ℝ} (hf : CCMFiniteExponentialBudget f V) (h : ℝ) :
    CCMFiniteExponentialBudget (logTranslationCLM h f) V := by
  induction hf with
  | zero => simpa only [map_zero] using CCMFiniteExponentialBudget.zero
  | atom s l r z f hlr hrep =>
      have hshift := (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae.eventually hrep
      have hcoe : (logTranslationCLM h f : ℝ → ℂ) =ᵐ[volume]
          ccmTruncatedExponential s (l + -h) (r + -h) (z * (Real.exp (-s * -h) : ℂ)) := by
        filter_upwards [translation_ae h f, hshift] with x hx hr
        rw [hx]
        change f (x + h) = ccmTruncatedExponential s l r z (x + h) at hr
        rw [hr]
        simpa only [sub_neg_eq_add] using ccmTruncatedExponential_translate s l r (-h) z x
      have hb := CCMFiniteExponentialBudget.atom s (l + -h) (r + -h)
        (z * (Real.exp (-s * -h) : ℂ)) (logTranslationCLM h f) (by linarith) hcoe
      rwa [ccmTruncatedExponentialBudget_translate] at hb
  | add hf hg ihf ihg => simpa only [map_add] using ihf.add ihg
  | smul z hf ih => simpa only [map_smul] using ih.smul z
  | mono hf hVW ih => exact ih.mono hVW

/-- Actual interval projection preserves the finite source class and budget. -/
theorem cutoff {f : SoninL2} {V : ℝ} (hf : CCMFiniteExponentialBudget f V) (u v : ℝ) :
    CCMFiniteExponentialBudget (indicatorCutoff (Icc u v) measurableSet_Icc f) V := by
  induction hf with
  | zero => simpa only [map_zero] using CCMFiniteExponentialBudget.zero
  | atom s l r z f hlr hrep =>
      let g := indicatorCutoff (Icc u v) measurableSet_Icc f
      have hcoe : (g : ℝ → ℂ) =ᵐ[volume]
          ccmTruncatedExponential s (max l u) (min r v) z := by
        filter_upwards [indicatorCutoff_ae (Icc u v) measurableSet_Icc f, hrep] with x hx hr
        rw [← ccmTruncatedExponential_restrict s l r u v z]
        change g x = (Icc u v).indicator (f : ℝ → ℂ) x at hx
        rw [hx]
        by_cases hxI : x ∈ Icc u v
        · rw [indicator_of_mem hxI, indicator_of_mem hxI, hr]
        · rw [indicator_of_notMem hxI, indicator_of_notMem hxI]
      by_cases hnew : max l u ≤ min r v
      · exact (CCMFiniteExponentialBudget.atom s (max l u) (min r v) z g hnew hcoe).mono
          (ccmTruncatedExponentialBudget_mono_interval (le_max_left _ _) hnew (min_le_left _ _) s z)
      · have hempty : Icc (max l u) (min r v) = ∅ := by
          ext x
          simp only [mem_Icc, mem_empty_iff_false, iff_false, not_and]
          intro hx
          linarith
        have hzero : g = 0 := by
          apply Lp.ext
          filter_upwards [hcoe, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)] with x hx hz
          rw [hx, hz]
          simp [ccmTruncatedExponential, hempty]
        rw [show indicatorCutoff (Icc u v) measurableSet_Icc f = g from rfl, hzero]
        exact CCMFiniteExponentialBudget.zero.mono (by unfold ccmTruncatedExponentialBudget; positivity)
  | add hf hg ihf ihg => simpa only [map_add] using ihf.add ihg
  | smul z hf ih => simpa only [map_smul] using ih.smul z
  | mono hf hVW ih => exact ih.mono hVW

/-- Both actual polar vectors have the natural endpoint budget. -/
theorem polar (a : SuzukiPositiveAperture) (s : ℝ) :
    CCMFiniteExponentialBudget (ccmPolarL2Vector a s) (Real.exp (|s| * a.1)) := by
  have hrep : (ccmPolarL2Vector a s : ℝ → ℂ) =ᵐ[volume]
      ccmTruncatedExponential s (-a.1) a.1 1 := by
    have h := ccmPolarL2Vector_coeFn a s
    change (ccmPolarL2Vector a s : ℝ → ℂ) =ᵐ[volume]
      (Icc (-a.1) a.1).indicator (fun x => (Real.exp (s * x) : ℂ)) at h
    simpa only [ccmTruncatedExponential, one_mul] using h
  have hb := CCMFiniteExponentialBudget.atom s (-a.1) a.1 1
    (ccmPolarL2Vector a s) (by linarith [a.2]) hrep
  have hm : ccmTruncatedExponentialBudget s (-a.1) a.1 1 = Real.exp (|s| * a.1) := by
    unfold ccmTruncatedExponentialBudget
    rw [norm_one, one_mul]
    congr 1
    by_cases hs : 0 ≤ s
    · rw [abs_of_nonneg hs, max_eq_right (by nlinarith [a.2])]
    · rw [abs_of_nonpos (le_of_not_ge hs), max_eq_left (by nlinarith [a.2])]
      ring
  rwa [hm] at hb

private theorem integral_pole_le (a : SuzukiPositiveAperture) (s : ℝ)
    (hs : s = 1 / 2 ∨ s = -1 / 2) :
    (∫ x in Icc (-a.1) a.1, Real.exp (s * x)) ≤ 2 * Real.exp (a.1 / 2) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -a.1 ≤ a.1 by linarith [a.2])]
  rcases hs with rfl | rfl
  · rw [intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : (1 / 2 : ℝ) ≠ 0),
      integral_exp]
    norm_num only [inv_div, inv_one, smul_eq_mul]
    rw [show (1 / 2 : ℝ) * a.1 = a.1 / 2 by ring,
      show (1 / 2 : ℝ) * -a.1 = -a.1 / 2 by ring]
    linarith [Real.exp_pos (-a.1 / 2)]
  · rw [intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : (-1 / 2 : ℝ) ≠ 0),
      integral_exp]
    norm_num only [inv_div, inv_neg, inv_one, smul_eq_mul]
    rw [show (-(1 / 2) : ℝ) * a.1 = -a.1 / 2 by ring,
      show (-(1 / 2) : ℝ) * -a.1 = a.1 / 2 by ring]
    linarith [Real.exp_pos (-a.1 / 2)]

/-- The actual pole charge is controlled by the source envelope without an
aperture-length loss. This is essential for linearly many remainder steps. -/
theorem norm_pole_charge_le (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    {V : ℝ} (hf : CCMFiniteExponentialBudget f.1 V) (s : ℝ)
    (hs : s = 1 / 2 ∨ s = -1 / 2) :
    ‖inner ℂ (ccmPolarApertureVector a s) f‖ ≤ 2 * Real.exp (a.1 / 2) * V := by
  let w : ℝ → ℝ := (Icc (-a.1) a.1).indicator (fun x => Real.exp (s * x) * V)
  have hw : Integrable w :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (s * x) * V)).integrableOn_Icc.integrable_indicator
      measurableSet_Icc
  have hb : ∀ᵐ x : ℝ, ‖inner ℂ ((ccmPolarL2Vector a s : SoninL2) x) (f.1 x)‖ ≤ w x := by
    filter_upwards [ccmPolarL2Vector_coeFn a s, hf.ae_norm_le] with x hx hfx
    rw [hx]
    by_cases hxI : x ∈ Icc (-a.1) a.1
    · rw [show centralInterval a.1 = Icc (-a.1) a.1 from rfl,
        indicator_of_mem hxI]
      change _ ≤ (Icc (-a.1) a.1).indicator (fun x => Real.exp (s * x) * V) x
      rw [indicator_of_mem hxI]
      refine (norm_inner_le_norm _ _).trans ?_
      rw [ccmPolarProfile, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left hfx (Real.exp_pos _).le
    · rw [show centralInterval a.1 = Icc (-a.1) a.1 from rfl,
        indicator_of_notMem hxI, inner_zero_left, norm_zero]
      change 0 ≤ (Icc (-a.1) a.1).indicator (fun x => Real.exp (s * x) * V) x
      rw [indicator_of_notMem hxI]
  change ‖inner ℂ (ccmPolarL2Vector a s) f.1‖ ≤ _
  rw [L2.inner_def]
  refine (norm_integral_le_of_norm_le hw hb).trans ?_
  change (∫ x, (Icc (-a.1) a.1).indicator (fun x => Real.exp (s * x) * V) x) ≤ _
  rw [integral_indicator measurableSet_Icc, integral_mul_const]
  exact mul_le_mul_of_nonneg_right (integral_pole_le a s hs) hf.nonneg

/-- The literal crossed rank-two polar map preserves the finite source class. -/
theorem polar_operator (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    {V : ℝ} (hf : CCMFiniteExponentialBudget f.1 V) :
    CCMFiniteExponentialBudget (ccmPolarOperator a f : SoninL2) (4 * Real.exp a.1 * V) := by
  have hp : CCMFiniteExponentialBudget (ccmPolarL2Vector a (1 / 2)) (Real.exp (a.1 / 2)) := by
    convert polar a (1 / 2) using 1
    norm_num
    ring
  have hm : CCMFiniteExponentialBudget (ccmPolarL2Vector a (-1 / 2)) (Real.exp (a.1 / 2)) := by
    convert polar a (-1 / 2) using 1
    norm_num
    ring
  let cp := inner ℂ (ccmPolarApertureVector a (-1 / 2)) f
  let cm := inner ℂ (ccmPolarApertureVector a (1 / 2)) f
  have hval : (ccmPolarOperator a f : SoninL2) =
      cp • ccmPolarL2Vector a (1 / 2) + cm • ccmPolarL2Vector a (-1 / 2) := by
    simp only [ccmPolarOperator, add_apply, InnerProductSpace.rankOne_apply]
    rfl
  rw [hval]
  refine ((hp.smul cp).add (hm.smul cm)).mono ?_
  have hcp : ‖cp‖ ≤ 2 * Real.exp (a.1 / 2) * V :=
    norm_pole_charge_le a f hf (-1 / 2) (Or.inr rfl)
  have hcm : ‖cm‖ ≤ 2 * Real.exp (a.1 / 2) * V :=
    norm_pole_charge_le a f hf (1 / 2) (Or.inl rfl)
  have h := add_le_add (mul_le_mul_of_nonneg_right hcp (Real.exp_pos (a.1 / 2)).le)
    (mul_le_mul_of_nonneg_right hcm (Real.exp_pos (a.1 / 2)).le)
  refine h.trans_eq ?_
  have he : Real.exp (a.1 / 2) * Real.exp (a.1 / 2) = Real.exp a.1 := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = 4 * (Real.exp (a.1 / 2) * Real.exp (a.1 / 2)) * V := by ring
    _ = _ := by rw [he]

/-- The two compressed translations at an actual prime displacement keep their
literal source representation. -/
theorem prime_atom (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    {V : ℝ} (hf : CCMFiniteExponentialBudget f.1 V) (n : ℕ) :
    CCMFiniteExponentialBudget
      ((ArithmeticFunction.vonMangoldt n : ℂ) • (ccmPrimeTransportOperator a n f : SoninL2))
      (2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * V) := by
  have ht := ((hf.translate (Real.log n)).add (hf.translate (-Real.log n))).cutoff (-a.1) a.1
  have hc : CCMFiniteExponentialBudget
      (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n)) f : SoninL2) (V + V) := by
    rw [ccmApertureCompression_val]
    exact ht
  have hw := (hc.smul ((1 / Real.sqrt n : ℝ) : ℂ)).smul
    (ArithmeticFunction.vonMangoldt n : ℂ)
  change CCMFiniteExponentialBudget
    ((ArithmeticFunction.vonMangoldt n : ℂ) • (ccmPrimeTransportOperator a n f : SoninL2)) _ at hw
  convert hw using 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (n : ℝ))]
  ring

/-- The complete actual prime sum preserves the source class, including every
prime power and the terminal cutoff. -/
theorem prime_operator (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    {V : ℝ} (hf : CCMFiniteExponentialBudget f.1 V) :
    CCMFiniteExponentialBudget (ccmFinitePrimeOperator a f : SoninL2) (42 * Real.exp a.1 * V) := by
  let S := Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊
  have hb := finset_sum S
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) • (ccmPrimeTransportOperator a n f : SoninL2))
    (fun n => 2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * V)
    (fun n _ => prime_atom a f hf n)
  have hval : (ccmFinitePrimeOperator a f : SoninL2) =
      ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℂ) • (ccmPrimeTransportOperator a n f : SoninL2) := by
    simp only [ccmFinitePrimeOperator, sum_apply, smul_apply, S,
      Submodule.coe_sum, Submodule.coe_smul]
  rw [hval]
  refine hb.mono ?_
  have hmass : (∑ n ∈ S, ArithmeticFunction.vonMangoldt n / Real.sqrt n) ≤
      21 * Real.exp a.1 := by
    have hsub : S ⊆ Finset.Icc 0 ⌊Real.exp (2 * a.1)⌋₊ := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hn).2⟩
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (Real.sqrt_nonneg (n : ℝ)))
    have hp := primeMassHalf_le_sqrt (Real.one_le_exp (show 0 ≤ 2 * a.1 by linarith [a.2]))
    have he : Real.sqrt (Real.exp (2 * a.1)) = Real.exp a.1 := by
      rw [show 2 * a.1 = a.1 + a.1 by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos a.1).le]
    rw [he] at hp
    exact hsum.trans hp
  have heq : (∑ n ∈ S, 2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * V) =
      2 * (∑ n ∈ S, ArithmeticFunction.vonMangoldt n / Real.sqrt n) * V := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [heq]
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 2)) hf.nonneg
  convert h using 1 <;> first | rfl | ring

/-- Actual bounded remainder closure with an aperture-independent normalized
budget cost. No property of its unknown Riesz response is assumed. -/
theorem remainder (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    {V : ℝ} (hf : CCMFiniteExponentialBudget f.1 V) :
    CCMFiniteExponentialBudget (ccmRestrictedWeilBoundedRemainder a f : SoninL2)
      ((‖ccmArchimedeanRemainderScalar‖ + 46) * Real.exp a.1 * V) := by
  have hb := ((hf.smul ccmArchimedeanRemainderScalar).add (polar_operator a f hf)).sub
    (prime_operator a f hf)
  have hval : (ccmRestrictedWeilBoundedRemainder a f : SoninL2) =
      ccmArchimedeanRemainderScalar • f.1 + (ccmPolarOperator a f : SoninL2) -
        (ccmFinitePrimeOperator a f : SoninL2) := by
    simp only [ccmRestrictedWeilBoundedRemainder, sub_apply, add_apply, smul_apply, one_apply_eq_self]
    rfl
  rw [hval]
  refine hb.mono ?_
  have hscale := mul_le_mul_of_nonneg_left (Real.one_le_exp a.2.le)
    (norm_nonneg ccmArchimedeanRemainderScalar)
  have h := mul_le_mul_of_nonneg_right hscale hf.nonneg
  nlinarith only [h]

end CCMFiniteExponentialBudget

/-- The actual physical remainder normalized by the shift prescribed in the
completed Suzuki form. -/
def ccmNormalizedWeilRemainder (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a))⁻¹ : ℂ) •
    ccmRestrictedWeilBoundedRemainder a

namespace CCMFiniteExponentialBudget

/-- Normalization removes all aperture dependence from the cost of one actual
remainder step. -/
theorem normalized_remainder (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    {V : ℝ} (hf : CCMFiniteExponentialBudget f.1 V) :
    CCMFiniteExponentialBudget (ccmNormalizedWeilRemainder a f : SoninL2)
      ((2 * (‖ccmArchimedeanRemainderScalar‖ + 46)) * V) := by
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have hb := (remainder a f hf).smul (c⁻¹ : ℂ)
  change CCMFiniteExponentialBudget (ccmNormalizedWeilRemainder a f : SoninL2) _ at hb
  refine hb.mono ?_
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have he : Real.exp a.1 / c ≤ 2 :=
    (div_le_iff₀ hc).2 (exp_aperture_le_twice_suzukiWeilIntervalShift a)
  calc
    _ = ((‖ccmArchimedeanRemainderScalar‖ + 46) * V) * (Real.exp a.1 / c) := by ring
    _ ≤ ((‖ccmArchimedeanRemainderScalar‖ + 46) * V) * 2 :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (by positivity) hf.nonneg)
    _ = _ := by ring

end CCMFiniteExponentialBudget

/-- Every actual normalized remainder iterate of the odd pole source has a
finite exponential representation. Its cost is exponential only in iteration
count, with a base independent of aperture. -/
theorem ccmNormalizedWeilRemainder_odd_iterate_budget
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMFiniteExponentialBudget
      (((ccmNormalizedWeilRemainder a)^[n])
        ((1 / 2 : ℂ) • (ccmPolarApertureVector a (1 / 2) -
          ccmPolarApertureVector a (-1 / 2))) : SoninL2)
      ((2 * (‖ccmArchimedeanRemainderScalar‖ + 46)) ^ n * Real.exp (a.1 / 2)) := by
  induction n with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
      have hp : CCMFiniteExponentialBudget (ccmPolarL2Vector a (1 / 2)) (Real.exp (a.1 / 2)) := by
        convert CCMFiniteExponentialBudget.polar a (1 / 2) using 1
        norm_num
        ring
      have hm : CCMFiniteExponentialBudget (ccmPolarL2Vector a (-1 / 2)) (Real.exp (a.1 / 2)) := by
        convert CCMFiniteExponentialBudget.polar a (-1 / 2) using 1
        norm_num
        ring
      have hb := (hp.sub hm).smul (1 / 2 : ℂ)
      change CCMFiniteExponentialBudget
        ((1 / 2 : ℂ) • (ccmPolarApertureVector a (1 / 2) - ccmPolarApertureVector a (-1 / 2)) : SoninL2) _ at hb
      convert hb using 1
      · rfl
      · rw [norm_div, norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl,
          Complex.norm_real, Real.norm_eq_abs]
        norm_num
        ring
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      convert CCMFiniteExponentialBudget.normalized_remainder a _ ih using 1
      ring

/-- The pointwise Fourier envelope is proved for the literal odd source orbit,
without an assumed regularity or tail bound on the Riesz response. -/
theorem ccmNormalizedWeilRemainder_odd_iterate_fourier
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ∀ᵐ ξ : ℝ, ξ ≠ 0 →
      ‖(𝓕 ((((ccmNormalizedWeilRemainder a)^[n])
        ((1 / 2 : ℂ) • (ccmPolarApertureVector a (1 / 2) -
          ccmPolarApertureVector a (-1 / 2)))) : SoninL2) : SoninL2) ξ‖ ≤
        ((2 * (‖ccmArchimedeanRemainderScalar‖ + 46)) ^ n * Real.exp (a.1 / 2)) /
          (Real.pi * |ξ|) :=
  (ccmNormalizedWeilRemainder_odd_iterate_budget a n).ae_norm_fourier_le

end RHTower
end
