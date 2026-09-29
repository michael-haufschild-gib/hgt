import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.RHTower.CCMZetaWeilSmoothIdentity
import GaloisForLFunctions.RHTower.SuzukiRayleighInfimum
import GaloisForLFunctions.RHTower.WeilParityPoleOneSidedRH
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCCMScalingBridge

/-!
# Full-cone Weil positivity is positivity of every restricted Weil form

**Theorem** (`ccmRestrictedWeilSourceQuadraticWith_nonneg_of_weilPositiveFull`). If `lam` is
Weil-positive with the pole term (`WeilPositiveFull`), then for every aperture `a` the restricted
source form of Connes–Consani–Moscovici with weights `lam` is nonnegative on its whole form domain:
`0 ≤ Q_a^{lam}(u)` for every `u`, including the literal pole vectors.

On a smooth interior source `v`, the restricted form is the full Weil functional of `lam` on
`v ⋆ ṽ` (`ccmRestrictedWeilSourceQuadraticWith_smooth_eq`). This uses the zeta identification
`ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil`, together with the translation pairing
`⟨τ_h v, v⟩ = conj((v ⋆ ṽ)(h))`. The form is continuous, and smooth interior sources are dense
(`denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector`).

**Corollary** (`riemannHypothesis_of_weilPositiveFull_of_le`). A full-cone Weil-positive system
`0 ≤ lam ≤ Λ` forces RH. The odd literal pole vector becomes an admissible test, and the one-sided
Chebyshev criterion applies (`riemannHypothesis_of_oddParityPole_subsystem`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate InnerProduct
open Zeta23

namespace RHTower

noncomputable section

/-- The translation pairing of a smooth source is the conjugate of its Weil test. -/
theorem inner_logTranslation_smooth_eq {a : SuzukiPositiveAperture}
    (v : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    inner ℂ (logTranslationCLM h (ccmArchimedeanFormToAperture a v.toCCMFormVector).1)
        (ccmArchimedeanFormToAperture a v.toCCMFormVector).1 =
      conj (EF.weilTest v v h) := by
  set F : SoninL2 := (ccmArchimedeanFormToAperture a v.toCCMFormVector).1 with hF
  have hFv : (F : ℝ → ℂ) =ᵐ[volume] v := v.toCCMFormVector_physical_coeFn
  rw [L2.inner_def]
  have hT := logTranslationCLM_ae h F
  have hshift : (fun x : ℝ => (F : ℝ → ℂ) (x + h)) =ᵐ[volume] fun x => v (x + h) :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hFv
  have hpt : (fun x : ℝ => inner ℂ ((logTranslationCLM h F : ℝ → ℂ) x) ((F : ℝ → ℂ) x)) =ᵐ[volume]
      fun x : ℝ => conj (v (x + h)) * v x := by
    filter_upwards [hT, hshift, hFv] with x h1 h2 h3
    rw [h1, h2, h3, RCLike.inner_apply]
    ring
  rw [integral_congr_ae hpt]
  unfold EF.weilTest convolution EF.tilde
  rw [← integral_conj]
  rw [← integral_add_right_eq_self (μ := volume)
    (fun t : ℝ => conj ((ContinuousLinearMap.mul ℝ ℂ) (v t) (conj (v (-(h - t)))))) h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ContinuousLinearMap.mul_apply', map_mul, Complex.conj_conj]
  rw [show -(h - (x + h)) = x by ring]

/-- **The restricted form on smooth sources is the full Weil functional.** -/
theorem ccmRestrictedWeilSourceQuadraticWith_smooth_eq {a : SuzukiPositiveAperture}
    (lam : ℕ → ℝ) (v : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊ v.toCCMFormVector =
      (weilFullFunctional lam (EF.weilTest v v)).re := by
  set N := ⌊Real.exp (2 * a.1)⌋₊ with hN
  have hv2 : ContDiff ℝ 2 (v : ℝ → ℂ) := v.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
  have hvc : HasCompactSupport (v : ℝ → ℂ) := v.hasCompactSupport
  have hkc : HasCompactSupport (EF.weilTest v v) := EF.weilTest_hasCompactSupport hvc hvc
  set f := ccmArchimedeanFormToAperture a v.toCCMFormVector with hf
  -- the difference with the von Mangoldt form
  have hdiff : ccmRestrictedWeilSourceQuadraticWith a lam N v.toCCMFormVector =
      ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector -
        ∑ n ∈ Finset.Icc 2 N, (lam n - ArithmeticFunction.vonMangoldt n) * (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
            inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re := by
    unfold ccmRestrictedWeilSourceQuadraticWith ccmRestrictedWeilSourceQuadratic
    simp only [← hf, ← hN, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hdiff, ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil,
    zeta_W_eq_weilFullFunctional hv2 hvc, weilFullFunctional_eq_sub lam hkc,
    ← weilFullFunctional_vonMangoldt, ← zeta_W_eq_weilFullFunctional hv2 hvc, Complex.sub_re]
  congr 1
  -- the atoms: a finite sum on the aperture
  obtain ⟨-, -, hks, -, -⟩ := weilTest_self_data hv2 (a := a.1) (fun x hx => by
    have := v.tsupport_subset hx
    exact ⟨this.1.le, this.2.le⟩)
  have hvan : ∀ n : ℕ, N < n → EF.weilTest v v (Real.log n) = 0 ∧
      EF.weilTest v v (-Real.log n) = 0 := by
    intro n hn
    have hn' : Real.exp (2 * a.1) < n := by
      have := Nat.lt_floor_add_one (Real.exp (2 * a.1))
      have h2 : ((N + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn'
    have hlog : 2 * a.1 < Real.log n := by rw [Real.lt_log_iff_exp_lt hnpos]; exact hn'
    have hout : ∀ y : ℝ, 2 * a.1 < |y| → EF.weilTest v v y = 0 := by
      intro y hy
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have := hks hmem
      rw [mem_Icc] at this
      rcases le_or_gt 0 y with h0 | h0
      · rw [abs_of_nonneg h0] at hy; linarith [this.2]
      · rw [abs_of_neg h0] at hy; linarith [this.1]
    have hl0 : 0 < Real.log n := by linarith [a.2]
    exact ⟨hout _ (by rw [abs_of_pos hl0]; exact hlog),
      hout _ (by rw [abs_neg, abs_of_pos hl0]; exact hlog)⟩
  rw [tsum_eq_sum (s := Finset.Icc 2 N) (fun n hn => ?_), Complex.re_sum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (Finset.mem_Icc.mp hn).1, Complex.re_ofReal_mul, inner_logTranslation_smooth_eq,
      inner_logTranslation_smooth_eq, ← map_add, Complex.conj_re]
    ring
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with h | h
    · rw [if_neg (by omega), Complex.ofReal_zero, zero_mul]
    · rw [(hvan n h).1, (hvan n h).2, add_zero, mul_zero]

/-- The restricted form with weights `lam` is continuous on the form domain. -/
theorem continuous_ccmRestrictedWeilSourceQuadraticWith (a : SuzukiPositiveAperture)
    (lam : ℕ → ℝ) :
    Continuous (ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊) := by
  have heq : ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊ = fun u =>
      ccmRestrictedWeilSourceQuadratic a u -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          (lam n - ArithmeticFunction.vonMangoldt n) * (1 / Real.sqrt n) *
            (inner ℂ (logTranslationCLM (Real.log n) (ccmArchimedeanFormToAperture a u).1)
                (ccmArchimedeanFormToAperture a u).1 +
              inner ℂ (logTranslationCLM (-Real.log n) (ccmArchimedeanFormToAperture a u).1)
                (ccmArchimedeanFormToAperture a u).1).re := by
    funext u
    unfold ccmRestrictedWeilSourceQuadraticWith ccmRestrictedWeilSourceQuadratic
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  refine (continuous_ccmRestrictedWeilSourceQuadratic a).sub
    (continuous_finsetSum _ fun n _ => continuous_const.mul ?_)
  have hf : Continuous fun u : CCMArchimedeanFormDomain a =>
      ((ccmArchimedeanFormToAperture a u).1 : SoninL2) :=
    continuous_subtype_val.comp (ccmArchimedeanFormToAperture a).continuous
  exact Complex.continuous_re.comp
    ((((logTranslationCLM (Real.log n)).continuous.comp hf).inner hf).add
      (((logTranslationCLM (-Real.log n)).continuous.comp hf).inner hf))

/-- **Full-cone Weil positivity gives positivity of every restricted Weil form.** -/
theorem ccmRestrictedWeilSourceQuadraticWith_nonneg_of_weilPositiveFull {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    0 ≤ ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊ u := by
  refine (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).induction_on u
    (isClosed_le continuous_const (continuous_ccmRestrictedWeilSourceQuadraticWith a lam))
    fun v => ?_
  rw [ccmRestrictedWeilSourceQuadraticWith_smooth_eq]
  exact hW _ (v.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) v.hasCompactSupport

/-- **Weil-positive minorants force RH (full cone).** If `lam` is Weil-positive with the pole term
and `0 ≤ lam ≤ Λ` on `n ≥ 2`, then RH holds. -/
theorem riemannHypothesis_of_weilPositiveFull_of_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (h0 : ∀ n, 2 ≤ n → 0 ≤ lam n)
    (hle : ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) :
    RiemannHypothesis :=
  riemannHypothesis_of_oddParityPole_subsystem h0 hle fun a =>
    ccmRestrictedWeilSourceQuadraticWith_nonneg_of_weilPositiveFull hW a _

/-- **Weil-positive majorants force RH (full cone).** -/
theorem riemannHypothesis_of_weilPositiveFull_of_ge {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hge : ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) :
    RiemannHypothesis := by
  have h := eq_vonMangoldt_of_weilPositiveFull_of_ge hW hge
  refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
  rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
  exact hW f hf hfc

end

end RHTower
