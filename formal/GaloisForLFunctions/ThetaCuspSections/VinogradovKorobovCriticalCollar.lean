import GaloisForLFunctions.ThetaCuspSections.LogarithmicCriticalCollar
import GaloisForLFunctions.RHTower.XiLogDerivVinogradovKorobovPositive

/-!
# Vinogradov–Korobov critical collars for all finite theta ranks

The current `current a b` is nonnegative wherever `Re (ξ'/ξ)(½ + a + ib) ≥ 0`, and this holds right of
the Vinogradov–Korobov boundary. So the logarithmic collar of the finite ranks widens: rank `N` is
strict for `|a − ½| < w(4(D(N+1)³ + 1))/2` (`signedHankel_posDef_vinogradovKorobov_collar`), with
`w(T) = (log T)^{−2/3} (log log T)^{−5/3}/10⁸`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set

namespace GaloisForLFunctions.ThetaCuspSections.LogarithmicCollar
open _root_.RHTower CriticalCollar QuantitativeCollar

/-- The current is nonnegative where the completed logarithmic derivative has nonnegative real part. -/
theorem current_nonneg_of_re_logDeriv_nonneg {a b : ℝ}
    (hlog : 0 ≤ (logDeriv xi (1/2+((b:ℂ)-(a:ℂ)*I)*I)).re) : 0 ≤ current a b := by
  let z : ℂ := (b:ℂ)-(a:ℂ)*I
  by_cases hXi : XiC z = 0
  · change 0 ≤ 2*((starRingEnd ℂ) (XiC z)*(-I*deriv XiC z)).re
    simp only [hXi,map_zero,zero_mul,Complex.zero_re,mul_zero,le_refl]
  have hlogXi : 0 ≤ (logDeriv XiC z).im := by
    rw [logDeriv_XiC_eq_mul_I_logDeriv_xi]
    simpa using hlog
  change 0 ≤ 2*((starRingEnd ℂ) (XiC z)*(-I*deriv XiC z)).re
  rw [kreinCurrent_eq_normSq_mul_logDeriv_im _ _ hXi,← logDeriv_apply]
  exact mul_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) hlogXi

/-- **The Vinogradov–Korobov collar.** There are constants `D` and `c₀ > 0` such that rank `N` is
strict for `|a − ½| < min c₀ (w(4(D(N+1)³ + 1))/2)`. -/
theorem signedHankel_posDef_vinogradovKorobov_collar : ∃ D c₀ : ℝ, 4 ≤ D ∧ 0 < c₀ ∧
    ∀ N : ℕ, ∀ a : ℝ,
      |a-1/2| < min c₀ (vkHadamardWidth (4*(D*((N:ℝ)+1)^3+1))/2) →
        (thetaCuspCenterMixedSignedHankel a N).PosDef := by
  obtain ⟨D,ε,hD,hε,hcrit⟩ := exists_signedHankel_posDef_of_current_nonneg_on_window
  obtain ⟨T₀,hT₀⟩ := exists_re_logDeriv_xi_nonneg_vinogradovKorobov
  set T₁ := max (max T₀ (Real.exp (Real.exp 1))) 4 with hT₁def
  have hT₁4 : (4:ℝ) ≤ T₁ := le_max_right _ _
  have hT₁0 : T₀ ≤ T₁ := (le_max_left _ _).trans (le_max_left _ _)
  have hT₁e : Real.exp (Real.exp 1) ≤ T₁ := (le_max_right _ _).trans (le_max_left _ _)
  have hL₁ : 0 < Real.log (T₁ + 1 + 1/2) := Real.log_pos (by linarith only [hT₁4])
  refine ⟨D,min ε (min (1/8) (1/58/Real.log (T₁ + 1 + 1/2))),hD,
    lt_min hε (lt_min (by norm_num) (by positivity)),fun N a ha => ?_⟩
  have hc := ha.trans_le (min_le_left _ _)
  have hw := ha.trans_le (min_le_right _ _)
  have hdist : |a-1/2| ≤ ε := hc.le.trans (min_le_left _ _)
  have h8 : |a-1/2| ≤ 1/8 := hc.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h58 : |a-1/2| ≤ 1/58/Real.log (T₁ + 1 + 1/2) :=
    hc.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hlo,hhi⟩ := abs_le.mp h8
  have ha0 : 0 < a := by linarith only [hlo]
  have habs : |a| ≤ 3/4 := abs_le.mpr ⟨by linarith only [hlo],by linarith only [hhi]⟩
  refine hcrit N a hdist ha0 habs fun b hb => current_nonneg_of_re_logDeriv_nonneg ?_
  set s : ℂ := 1/2+((b:ℂ)-(a:ℂ)*I)*I with hs
  have hre : s.re = 1/2+a := by norm_num [hs,Complex.mul_re,Complex.mul_im]
  have him : s.im = b := by norm_num [hs,Complex.mul_re,Complex.mul_im]
  have hx : 1/2 < s.re := by rw [hre]; linarith only [ha0]
  rcases le_or_gt |b| 4 with hb4 | hb4
  · exact re_logDeriv_xi_nonneg_of_abs_im_le_four hx (by rwa [him])
  rcases le_or_gt T₁ |b| with hbig | hsmallb
  · -- above `T₁`: the Vinogradov–Korobov boundary
    refine hT₀ s (by rw [him]; exact hT₁0.trans hbig) ?_
    rw [him,hre]
    have hee : Real.exp (Real.exp 1) ≤ 4*(|b|+1) := by
      linarith only [hT₁e,hbig,abs_nonneg b]
    have hanti := vkHadamardWidth_anti hee (show 4*(|b|+1) ≤ 4*(D*((N:ℝ)+1)^3+1) by
      linarith only [hb])
    have hlow := (abs_lt.mp hw).1
    linarith only [hlow,hanti]
  · -- between `4` and `T₁`: the classical boundary at a fixed height
    apply re_logDeriv_xi_nonneg_of_zeroFree_sharp hx (by rwa [him])
    rw [him,hre]
    have hbpos : 0 < |b|+1/2 := by positivity
    have hle : |b|+1/2 ≤ T₁ + 1 + 1/2 := by linarith only [hsmallb]
    have hLb : 0 < Real.log (|b|+1/2) := Real.log_pos (by linarith only [hb4])
    have hlogs := Real.log_le_log hbpos hle
    have hfrac : 1/58/Real.log (T₁ + 1 + 1/2) ≤ 1/58/Real.log (|b|+1/2) := by
      apply (div_le_div_iff₀ hL₁ hLb).mpr
      nlinarith only [hlogs]
    have hlow := (abs_le.mp h58).1
    linarith only [hlow,hfrac]

end GaloisForLFunctions.ThetaCuspSections.LogarithmicCollar

#print axioms GaloisForLFunctions.ThetaCuspSections.LogarithmicCollar.signedHankel_posDef_vinogradovKorobov_collar
