import GaloisForLFunctions.RHTower.FZZCigarPlaneScreeningMarkedDerivative
import GaloisForLFunctions.RHTower.ReflectionCocycleArchimedean

/-!
# Exact zero locus of the original marked plane screening source

The normalized first logarithmic plane mark is the difference of one symmetric Gamma-log slope
at two chamber parameters.  Strict trigamma decrease makes that symmetric slope injective modulo
reflection.  This classifies every zero of the actual convergent integral: cancellation occurs
exactly on the chart line `y = 0`.
-/

open Complex Filter Set
open scoped Topology

noncomputable section
namespace GaloisForLFunctions.RHTower

private theorem deriv_digamma_real_diff_re_neg
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (deriv Complex.digamma (y : ℂ) - deriv Complex.digamma (x : ℂ)).re < 0 := by
  have hy : 0 < y := lt_trans hx hxy
  have hyre : 0 < ((y : ℂ)).re := by rw [Complex.ofReal_re]; exact hy
  have hxre : 0 < ((x : ℂ)).re := by rw [Complex.ofReal_re]; exact hx
  have hSre : ∀ (w : ℝ) (N : ℕ),
      (∑ n ∈ Finset.range N, (((w : ℂ) + (n : ℂ)) ^ 2)⁻¹).re =
        ∑ n ∈ Finset.range N, ((w + n) ^ 2)⁻¹ := by
    intro w N
    rw [show (∑ n ∈ Finset.range N, (((w : ℂ) + (n : ℂ)) ^ 2)⁻¹) =
        ((∑ n ∈ Finset.range N, ((w + n) ^ 2)⁻¹ : ℝ) : ℂ) from ?_, Complex.ofReal_re]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  have hlim := (_root_.RHTower.deriv_digamma_eq_tsum_limit hyre).sub
    (_root_.RHTower.deriv_digamma_eq_tsum_limit hxre)
  have hlimre : Tendsto (fun N : ℕ =>
      ((∑ n ∈ Finset.range N, (((y : ℂ) + (n : ℂ)) ^ 2)⁻¹) -
        (∑ n ∈ Finset.range N, (((x : ℂ) + (n : ℂ)) ^ 2)⁻¹)).re)
      atTop (nhds ((deriv Complex.digamma (y : ℂ) -
        deriv Complex.digamma (x : ℂ)).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp hlim
  have hbound : ∀ N : ℕ,
      ((∑ n ∈ Finset.range N, (((y : ℂ) + (n : ℂ)) ^ 2)⁻¹) -
        (∑ n ∈ Finset.range N, (((x : ℂ) + (n : ℂ)) ^ 2)⁻¹)).re ≤ 0 := by
    intro N
    rw [Complex.sub_re, hSre, hSre, ← Finset.sum_sub_distrib]
    apply Finset.sum_nonpos
    intro n _
    have hxn : (0 : ℝ) < x + n := by positivity
    have hle : (x + n) ^ 2 ≤ (y + n) ^ 2 := by nlinarith
    have hi : ((y + n) ^ 2)⁻¹ ≤ ((x + n) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hle
    linarith
  have hle : (deriv Complex.digamma (y : ℂ) -
      deriv Complex.digamma (x : ℂ)).re ≤ 0 :=
    le_of_tendsto hlimre (Filter.Eventually.of_forall hbound)
  have him_zero : ∀ {w : ℝ}, 0 < w → (deriv Complex.digamma (w : ℂ)).im = 0 := by
    intro w hw
    have hwre : 0 < ((w : ℂ)).re := by simpa using hw
    have hlimw := Complex.continuous_im.continuousAt.tendsto.comp
      (_root_.RHTower.deriv_digamma_eq_tsum_limit hwre)
    have hterms : ∀ N : ℕ,
        (∑ n ∈ Finset.range N, (((w : ℂ) + (n : ℂ)) ^ 2)⁻¹).im = 0 := by
      intro N
      rw [show (∑ n ∈ Finset.range N, (((w : ℂ) + (n : ℂ)) ^ 2)⁻¹) =
          ((∑ n ∈ Finset.range N, ((w + n) ^ 2)⁻¹ : ℝ) : ℂ) from ?_,
        Complex.ofReal_im]
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro n _
      push_cast
      ring
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
    exact tendsto_nhds_unique hlimw
      (hzero.congr' (Filter.Eventually.of_forall fun N => (hterms N).symm))
  have hne := _root_.RHTower.deriv_digamma_real_diff_ne hx hxy
  have hreal_ne : (deriv Complex.digamma (y : ℂ) -
      deriv Complex.digamma (x : ℂ)).re ≠ 0 := by
    intro hre
    apply hne
    apply Complex.ext
    · simpa using hre
    · simp [Complex.sub_im, him_zero hy, him_zero hx]
  exact lt_of_le_of_ne hle hreal_ne


private theorem real_no_gamma_poles_of_pos {s : ℝ} (hs : 0 < s) :
    ∀ n : ℕ, s ≠ -n := by
  intro n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem complex_no_gamma_poles_of_pos {s : ℝ} (hs : 0 < s) :
    ∀ n : ℕ, (s : ℂ) ≠ -(n : ℂ) := by
  intro n hn
  apply real_no_gamma_poles_of_pos hs n
  exact_mod_cast hn

private theorem fzzScreeningPlaneGammaLogSlope_eq_re_digamma_of_pos
    {s : ℝ} (hs : 0 < s) :
    fzzScreeningPlaneGammaLogSlope s = (Complex.digamma (s : ℂ)).re := by
  have hd := (Complex.differentiableAt_Gamma (s : ℂ)
    (complex_no_gamma_poles_of_pos hs)).hasDerivAt.real_of_complex
  have hr : deriv Real.Gamma s = (deriv Complex.Gamma (s : ℂ)).re := hd.deriv
  simp only [fzzScreeningPlaneGammaLogSlope, hr, Complex.digamma_def, logDeriv_apply,
    Complex.Gamma_ofReal, Complex.div_ofReal_re]

private theorem fzzScreeningPlaneGammaLogSlope_eventuallyEq_re_digamma
    {s : ℝ} (hs : 0 < s) :
    (fun x : ℝ => fzzScreeningPlaneGammaLogSlope x) =ᶠ[nhds s]
      fun x : ℝ => (Complex.digamma (x : ℂ)).re := by
  filter_upwards [Ioi_mem_nhds hs] with x hx
  exact fzzScreeningPlaneGammaLogSlope_eq_re_digamma_of_pos hx

private theorem hasDerivAt_fzzScreeningPlaneGammaLogSlope_of_pos
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt fzzScreeningPlaneGammaLogSlope
      (deriv Complex.digamma (s : ℂ)).re s := by
  exact (_root_.RHTower.hasDerivAt_re_digamma_ofReal hs).congr_of_eventuallyEq
    (fzzScreeningPlaneGammaLogSlope_eventuallyEq_re_digamma hs)

/-- Symmetric logarithmic-Gamma slope controlling the original normalized first mark. -/
def fzzScreeningPlaneSymmetricGammaSlope (s : ℝ) : ℝ :=
  fzzScreeningPlaneGammaLogSlope s + fzzScreeningPlaneGammaLogSlope (1 - s)

theorem fzzScreeningPlaneSymmetricGammaSlope_reflect (s : ℝ) :
    fzzScreeningPlaneSymmetricGammaSlope (1 - s) =
      fzzScreeningPlaneSymmetricGammaSlope s := by
  unfold fzzScreeningPlaneSymmetricGammaSlope
  ring

private theorem hasDerivAt_fzzScreeningPlaneSymmetricGammaSlope
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    HasDerivAt fzzScreeningPlaneSymmetricGammaSlope
      ((deriv Complex.digamma (s : ℂ)).re -
        (deriv Complex.digamma ((1 - s : ℝ) : ℂ)).re) s := by
  have h₁ := hasDerivAt_fzzScreeningPlaneGammaLogSlope_of_pos hs
  have hinner' := (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)
  have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) s := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using hinner'
  have h₂ := (hasDerivAt_fzzScreeningPlaneGammaLogSlope_of_pos
    (show 0 < 1 - s by linarith)).comp s hinner
  simpa only [fzzScreeningPlaneSymmetricGammaSlope, Function.comp_apply,
    Pi.add_apply, mul_neg, mul_one, add_neg_eq_sub] using h₁.add h₂

private theorem deriv_fzzScreeningPlaneSymmetricGammaSlope_pos
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2) :
    0 < deriv fzzScreeningPlaneSymmetricGammaSlope s := by
  have hdiff := deriv_digamma_real_diff_re_neg hs (by linarith : s < 1 - s)
  have hd := hasDerivAt_fzzScreeningPlaneSymmetricGammaSlope hs (by linarith)
  rw [hd.deriv]
  rw [Complex.sub_re] at hdiff
  linarith

theorem fzzScreeningPlaneSymmetricGammaSlope_strictMonoOn :
    StrictMonoOn fzzScreeningPlaneSymmetricGammaSlope (Ioc 0 (1 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 (1 / 2))
  · intro s hs
    exact (hasDerivAt_fzzScreeningPlaneSymmetricGammaSlope hs.1
      (by linarith [hs.2])).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    exact deriv_fzzScreeningPlaneSymmetricGammaSlope_pos hs.1 hs.2

private def fzzScreeningPlaneSymmetricFold (s : ℝ) : ℝ :=
  min s (1 - s)

private theorem fzzScreeningPlaneSymmetricFold_mem
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    fzzScreeningPlaneSymmetricFold s ∈ Ioc 0 (1 / 2) := by
  constructor
  · exact lt_min hs (by linarith)
  · by_cases h : s ≤ 1 / 2
    · exact (min_le_left s (1 - s)).trans h
    · exact (min_le_right s (1 - s)).trans (by linarith)

private theorem fzzScreeningPlaneSymmetricGammaSlope_fold (s : ℝ) :
    fzzScreeningPlaneSymmetricGammaSlope (fzzScreeningPlaneSymmetricFold s) =
      fzzScreeningPlaneSymmetricGammaSlope s := by
  by_cases h : s ≤ 1 - s
  · rw [fzzScreeningPlaneSymmetricFold, min_eq_left h]
  · rw [fzzScreeningPlaneSymmetricFold, min_eq_right (le_of_not_ge h),
      fzzScreeningPlaneSymmetricGammaSlope_reflect]

/-- Complete equality classification for the symmetric Gamma slope in the unit chamber. -/
theorem fzzScreeningPlaneSymmetricGammaSlope_eq_iff
    {a c : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hc0 : 0 < c) (hc1 : c < 1) :
    fzzScreeningPlaneSymmetricGammaSlope c =
      fzzScreeningPlaneSymmetricGammaSlope a ↔ c = a ∨ c = 1 - a := by
  constructor
  · intro h
    have hfoldValue : fzzScreeningPlaneSymmetricGammaSlope
        (fzzScreeningPlaneSymmetricFold c) =
        fzzScreeningPlaneSymmetricGammaSlope (fzzScreeningPlaneSymmetricFold a) := by
      rw [fzzScreeningPlaneSymmetricGammaSlope_fold,
        fzzScreeningPlaneSymmetricGammaSlope_fold, h]
    have hfold : fzzScreeningPlaneSymmetricFold c =
        fzzScreeningPlaneSymmetricFold a :=
      fzzScreeningPlaneSymmetricGammaSlope_strictMonoOn.injOn
        (fzzScreeningPlaneSymmetricFold_mem hc0 hc1)
        (fzzScreeningPlaneSymmetricFold_mem ha0 ha1) hfoldValue
    unfold fzzScreeningPlaneSymmetricFold at hfold
    by_cases hc : c ≤ 1 - c
    · rw [min_eq_left hc] at hfold
      by_cases ha : a ≤ 1 - a
      · rw [min_eq_left ha] at hfold
        exact Or.inl hfold
      · rw [min_eq_right (le_of_not_ge ha)] at hfold
        exact Or.inr hfold
    · rw [min_eq_right (le_of_not_ge hc)] at hfold
      by_cases ha : a ≤ 1 - a
      · rw [min_eq_left ha] at hfold
        right
        linarith
      · rw [min_eq_right (le_of_not_ge ha)] at hfold
        left
        linarith
  · rintro (rfl | rfl)
    · rfl
    · exact fzzScreeningPlaneSymmetricGammaSlope_reflect a

/-- The original normalized first logarithmic mark has exactly one zero in the complete positive
screening chart: the previously known line `y = 0`. -/
theorem fzzScreeningPlaneMarkedMoment_first_eq_zero_iff (x y : ℝ) :
    fzzScreeningPlaneMarkedMoment x y 1 0 = 0 ↔ y = 0 := by
  constructor
  · intro hz
    let a := fzzScreeningBetaA x y
    let b := fzzScreeningBetaB x y
    let c := a + b - 1
    obtain ⟨ha0, ha1, hb0, hb1, hab⟩ := fzzScreeningBeta_chamber x y
    have hresp := fzzScreeningPlaneMarkedMoment_logResponse x y
    rw [hz, zero_div] at hresp
    have hsymm : fzzScreeningPlaneSymmetricGammaSlope c =
        fzzScreeningPlaneSymmetricGammaSlope a := by
      change 0 = fzzScreeningPlaneGammaLogSlope c -
        fzzScreeningPlaneGammaLogSlope (1 - a) -
        fzzScreeningPlaneGammaLogSlope a +
        fzzScreeningPlaneGammaLogSlope (2 - a - b) at hresp
      have hccomp : 2 - a - b = 1 - c := by
        dsimp only [c]
        ring
      rw [hccomp] at hresp
      dsimp only [fzzScreeningPlaneSymmetricGammaSlope]
      linarith
    have hc0 : 0 < c := by dsimp only [c, a, b]; linarith
    have hc1 : c < 1 := by dsimp only [c, a, b]; linarith
    have hclass := (fzzScreeningPlaneSymmetricGammaSlope_eq_iff
      ha0 ha1 hc0 hc1).mp hsymm
    have hbalance : 2 * a + b = 2 := by
      rcases hclass with hca | hca
      · exfalso
        dsimp only [c] at hca
        linarith
      · dsimp only [c] at hca
        linarith
    have hden : 0 < 1 + Real.exp x + Real.exp y := by positivity
    dsimp only [a, b, fzzScreeningBetaA, fzzScreeningBetaB] at hbalance
    have hey : Real.exp y = 1 := by
      field_simp [ne_of_gt hden] at hbalance
      linarith
    apply Real.exp_injective
    simpa using hey
  · rintro rfl
    exact fzzScreeningPlaneMarkedMoment_first_zero x

end GaloisForLFunctions.RHTower
