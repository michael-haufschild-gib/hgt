import GaloisForLFunctions.RHTower.XiMassStripFourierLipschitz
import GaloisForLFunctions.RHTower.CCMPolarPrimeStieltjesAutocorrelation
import GaloisForLFunctions.RHTower.ExpFourierNormalization
import GaloisForLFunctions.RHTower.XiMassArchimedeanUniformBound
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# Mass-shifted critical-error flux

This module completes exact prime-polar Stieltjes integration by parts for the mass-shifted
Fourier profile without an artificial endpoint-zero hypothesis. The finite critical
von-Mangoldt source splits into three terms:

* a polar partial source;
* a terminal completed-error flux;
* a centered completed-Chebyshev-error current paired with the true Fourier derivative.

For every mass greater than one half, the polar partial source converges to evaluation of the
analytic mass test at the archimedean pole, with height-independent norm
2 pi exp(-sigma sqrt(a^2 - 1/4)). The terminal completed-error flux tends to zero
unconditionally. Its proof uses the corpus bound for half-weighted von-Mangoldt mass and an
interior strip shift, not a numerical estimate or an RH-strength remainder.

The derivative kernel has matching interior-shift decay, so the centered error current is
absolutely integrable for every fixed complex time. Consequently the prime partial source
converges to explicit archimedean boundary value plus this source-defined infinite current. This
removes cumulative square-root main mass and cofinal terminal flux from mass-shifted spectral-face
open core. Uniform control in vertical height of surviving centered current remains exact
arithmetic problem; no boundedness or RH hypothesis is assumed.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

def xiMassFourierDerivative (a σ u w : ℝ) : ℂ :=
  ∫ x : ℝ,
    xiMassAnalyticTest a ((σ : ℂ) + u * I) x *
      (Complex.exp (-(I * (w : ℂ) * x)) * (-(I * x)))

theorem hasDerivAt_xiMassRealFourierProfile
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u w : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (r : ℂ))
      (xiMassFourierDerivative a σ u w) w := by
  let g : ℝ → ℂ := fun x => xiMassAnalyticTest a ((σ : ℂ) + u * I) x
  let F : ℝ → ℝ → ℂ := fun r x =>
    g x * Complex.exp (-(I * (r : ℂ) * (x : ℂ)))
  let F' : ℝ → ℝ → ℂ := fun r x =>
    g x * (Complex.exp (-(I * (r : ℂ) * (x : ℂ))) * (-(I * (x : ℂ))))
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    have hz : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      change HasDerivAt (⇑Complex.ofRealCLM) 1 x
      exact Complex.ofRealCLM.hasDerivAt
    have hmem : (x : ℂ) ∈ xiMassStrip a := by
      change |((x : ℂ)).im| < a
      simpa using ha
    exact ((hasDerivAt_xiMassAnalyticTest ha _ hmem).comp x hz).continuousAt
  have hFint : Integrable (F w) := by
    apply Integrable.mono' (integrable_exp_neg_mul_abs hσ)
    · exact (hgcont.mul
        (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
    · refine ae_of_all _ fun x => ?_
      have hmem : (x : ℂ) ∈ xiMassStrip a := by
        change |((x : ℂ)).im| < a
        simpa using ha
      have hg := norm_xiMassAnalyticTest_le
        (τ := ((σ : ℂ) + u * I)) ha (by simpa using hσ.le) hmem
      dsimp only [F]
      rw [norm_mul, Complex.norm_exp]
      have hphase : (-(I * (w : ℂ) * (x : ℂ))).re = 0 := by simp
      rw [hphase, Real.exp_zero, mul_one]
      simpa [g] using hg
  have hdom : Integrable (fun x : ℝ => |x| * Real.exp (-(σ * |x|))) :=
    integrable_abs_mul_exp_neg_mul_abs hσ
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F')
    (bound := fun x : ℝ => |x| * Real.exp (-(σ * |x|)))
    (univ_mem : (Set.univ : Set ℝ) ∈ 𝓝 w)
    (Filter.Eventually.of_forall fun _ =>
      (hgcont.mul (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable)
    hFint
    (by
      have : Continuous (F' w) := by
        dsimp only [F']
        fun_prop
      exact this.aestronglyMeasurable)
    (by
      refine ae_of_all _ fun x r hr => ?_
      have hmem : (x : ℂ) ∈ xiMassStrip a := by
        change |((x : ℂ)).im| < a
        simpa using ha
      have hg := norm_xiMassAnalyticTest_le
        (τ := ((σ : ℂ) + u * I)) ha (by simpa using hσ.le) hmem
      dsimp only [F']
      rw [norm_mul, norm_mul, Complex.norm_exp]
      have hphase : (-(I * (r : ℂ) * (x : ℂ))).re = 0 := by simp
      have hnormIx : ‖-(I * (x : ℂ))‖ = |x| := by
        rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs]
      rw [hphase, Real.exp_zero, one_mul, hnormIx]
      calc
        ‖g x‖ * |x| ≤ Real.exp (-(σ * |x|)) * |x| :=
          mul_le_mul_of_nonneg_right (by
            simpa [g] using hg) (abs_nonneg x)
        _ = |x| * Real.exp (-(σ * |x|)) := by ring)
    hdom
    (by
      refine ae_of_all _ fun x r hr => ?_
      have h1 : HasDerivAt (fun q : ℝ => (-(I * (x : ℂ))) * (q : ℂ))
          (-(I * (x : ℂ))) r := by
        simpa using
          ((Complex.ofRealCLM.hasDerivAt (x := r)).const_mul (-(I * (x : ℂ))))
      have hphaseFun : (fun q : ℝ => (-(I * (x : ℂ))) * (q : ℂ)) =
          fun q : ℝ => -(I * (q : ℂ) * (x : ℂ)) := by
        funext q
        ring
      rw [hphaseFun] at h1
      have h2 := h1.cexp
      have h3 := h2.const_mul (g x)
      dsimp only [F, F']
      simpa using h3)
  have hd := h.2
  change HasDerivAt (fun r : ℝ => ∫ x : ℝ, F r x) (∫ x : ℝ, F' w x) w at hd
  simpa [stripFourier, xiMassFourierDerivative, F, F', g] using hd

theorem criticalMellinStieltjesPairing_eq_terminal_sub_errorFlux
    {A : ℝ} (hA : 0 ≤ A) {F F' : ℝ → ℂ}
    (hF : ∀ x ∈ Set.Icc (0 : ℝ) (2 * A), HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume 0 (2 * A)) :
    criticalMellinStieltjesPairing A F =
      (criticalMellinCompletedError (2 * A) : ℂ) * F (2 * A) -
        ∫ h in Ioc (0 : ℝ) (2 * A),
          (criticalMellinCompletedError h : ℂ) * F' h := by
  let H : ℝ := 2 * A
  let C : ℂ := F H
  let G : ℝ → ℂ := fun h => F h - C
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hG : ∀ x ∈ Set.Icc (0 : ℝ) H, HasDerivAt G (F' x) x := by
    intro x hx
    exact (hF x (by simpa [H] using hx)).sub_const C
  have hGend : G H = 0 := by simp [G, C]
  have hpairG : criticalMellinStieltjesPairing A G =
      -(∫ h in Ioc (0 : ℝ) H,
        (criticalMellinCompletedError h : ℂ) * F' h) := by
    simpa [H] using
      criticalMellinStieltjesPairing_integrationByParts hA hG
        (by simpa [H] using hF') hGend
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) H) := by
    intro x hx
    exact (hF x (by simpa [H] using hx)).continuousAt.continuousWithinAt
  let D : ℝ → ℂ := fun h => (2 * Real.cosh (h / 2) : ℂ)
  have hDcont : Continuous D := by
    dsimp [D]
    fun_prop
  have hFDint : Integrable (fun h => F h * D h)
      (volume.restrict (Ioc (0 : ℝ) H)) := by
    exact (hFcont.mul hDcont.continuousOn).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hCDint : Integrable (fun h => C * D h)
      (volume.restrict (Ioc (0 : ℝ) H)) := by
    have hc : Continuous (fun h => C * D h) := continuous_const.mul hDcont
    exact hc.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hint :
      (∫ h in Ioc (0 : ℝ) H, G h * D h) =
        (∫ h in Ioc (0 : ℝ) H, F h * D h) -
          C * ∫ h in Ioc (0 : ℝ) H, D h := by
    calc
      (∫ h in Ioc (0 : ℝ) H, G h * D h) =
          ∫ h in Ioc (0 : ℝ) H, (F h * D h - C * D h) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with h
            simp [G]
            ring
      _ = (∫ h in Ioc (0 : ℝ) H, F h * D h) -
          ∫ h in Ioc (0 : ℝ) H, C * D h :=
            MeasureTheory.integral_sub hFDint hCDint
      _ = (∫ h in Ioc (0 : ℝ) H, F h * D h) -
          C * ∫ h in Ioc (0 : ℝ) H, D h := by
            rw [MeasureTheory.integral_const_mul]
  let K : Finset ℕ := Finset.Icc 2 ⌊Real.exp H⌋₊
  have hsum :
      (∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) * G (Real.log k)) =
        (∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) * F (Real.log k)) -
          C * ∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) := by
    calc
      (∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) * G (Real.log k)) =
          ∑ k ∈ K,
            ((criticalMellinAtomWeight k : ℂ) * F (Real.log k) -
              C * (criticalMellinAtomWeight k : ℂ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [G]
            ring
      _ = (∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) * F (Real.log k)) -
          ∑ k ∈ K, C * (criticalMellinAtomWeight k : ℂ) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) * F (Real.log k)) -
          C * ∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) := by
            rw [Finset.mul_sum]
  have hsplit : criticalMellinStieltjesPairing A G =
      criticalMellinStieltjesPairing A F -
        C * criticalMellinStieltjesPairing A (fun _ => 1) := by
    rw [criticalMellinStieltjesPairing, criticalMellinStieltjesPairing,
      criticalMellinStieltjesPairing]
    change
      (∫ h in Ioc (0 : ℝ) H, G h * D h) -
          ∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) * G (Real.log k) =
        ((∫ h in Ioc (0 : ℝ) H, F h * D h) -
            ∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) * F (Real.log k)) -
          C * ((∫ h in Ioc (0 : ℝ) H, (1 : ℂ) * D h) -
            ∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) * 1)
    rw [hint, hsum]
    simp only [one_mul, mul_one]
    ring
  have hone := criticalMellinStieltjesPairing_one hA
  rw [hsplit, hone] at hpairG
  dsimp only [H, C] at hpairG ⊢
  linear_combination hpairG

theorem xiMassCriticalStieltjes_eq_terminal_sub_errorFlux
    {a σ A : ℝ} (ha : 0 < a) (hσ : 0 < σ) (hA : 0 ≤ A) (u : ℝ) :
    criticalMellinStieltjesPairing A
        (fun h : ℝ =>
          stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (h : ℂ)) =
      (criticalMellinCompletedError (2 * A) : ℂ) *
          stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) ((2 * A : ℝ) : ℂ) -
        ∫ h in Ioc (0 : ℝ) (2 * A),
          (criticalMellinCompletedError h : ℂ) *
            xiMassFourierDerivative a σ u h := by
  let g : ℝ → ℂ := fun x => xiMassAnalyticTest a ((σ : ℂ) + u * I) x
  let g1 : ℝ → ℂ := fun x => g x * (-(I * (x : ℂ)))
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    have hz : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      change HasDerivAt (⇑Complex.ofRealCLM) 1 x
      exact Complex.ofRealCLM.hasDerivAt
    have hmem : (x : ℂ) ∈ xiMassStrip a := by
      change |((x : ℂ)).im| < a
      simpa using ha
    exact ((hasDerivAt_xiMassAnalyticTest ha _ hmem).comp x hz).continuousAt
  have hg1cont : Continuous g1 := by
    dsimp only [g1]
    fun_prop
  have hg1bound : ∀ x : ℝ,
      ‖g1 x‖ ≤ (2 / σ) * Real.exp (-((σ / 2) * |x|)) := by
    intro x
    have hmem : (x : ℂ) ∈ xiMassStrip a := by
      change |((x : ℂ)).im| < a
      simpa using ha
    have hg := norm_xiMassAnalyticTest_le
      (τ := ((σ : ℂ) + u * I)) ha (by simpa using hσ.le) hmem
    have hmoment := pow_abs_mul_exp_neg_le hσ 1 x
    rw [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at hmoment
    have hnormIx : ‖-(I * (x : ℂ))‖ = |x| := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    dsimp only [g1]
    rw [norm_mul, hnormIx]
    calc
      ‖g x‖ * |x| ≤ Real.exp (-(σ * |x|)) * |x| :=
        mul_le_mul_of_nonneg_right (by simpa [g] using hg) (abs_nonneg x)
      _ = |x| * Real.exp (-(σ * |x|)) := by ring
      _ ≤ (2 / σ) * Real.exp (-(σ / 2 * |x|)) := by
        simpa using hmoment
  have hderivEq : (fun h : ℝ => xiMassFourierDerivative a σ u h) =
      fun h : ℝ => expFourier g1 (h : ℂ) := by
    funext h
    rw [xiMassFourierDerivative, expFourier]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [g1, g]
    ring
  have hg1K : 0 ≤ 2 / σ := by positivity
  have hg1eps : 0 < σ / 2 := by positivity
  have hDcont : Continuous (fun h : ℝ => xiMassFourierDerivative a σ u h) := by
    rw [hderivEq, continuous_iff_continuousAt]
    intro h
    have hw : |((h : ℂ)).im| < σ / 2 := by simpa using hg1eps
    have hout := hasDerivAt_expFourier hg1cont.aestronglyMeasurable
      hg1K hg1bound hw
    have hin : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 h := by
      change HasDerivAt (⇑Complex.ofRealCLM) 1 h
      exact Complex.ofRealCLM.hasDerivAt
    exact (hout.comp h hin).continuousAt
  apply criticalMellinStieltjesPairing_eq_terminal_sub_errorFlux hA
  · intro h hh
    exact hasDerivAt_xiMassRealFourierProfile ha hσ u h
  · exact hDcont.intervalIntegrable _ _

def xiMassCriticalPrimePartialSource (a σ u H : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
    (criticalMellinAtomWeight k : ℂ) *
      stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (Real.log k : ℂ)

def xiMassPolarPartialSource (a σ u H : ℝ) : ℂ :=
  ∫ h in Ioc (0 : ℝ) H,
    stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (h : ℂ) *
      (2 * Real.cosh (h / 2) : ℂ)

def xiMassCompletedErrorFluxPartial (a σ u H : ℝ) : ℂ :=
  ∫ h in Ioc (0 : ℝ) H,
    (criticalMellinCompletedError h : ℂ) *
      xiMassFourierDerivative a σ u h

theorem criticalMellinPrimeMass_eq_primeMassHalf (h : ℝ) :
    criticalMellinPrimeMass h = primeMassHalf (Real.exp h) := by
  rw [criticalMellinPrimeMass, primeMassHalf]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    norm_num
  · have hkpos : (0 : ℝ) < k := by
      exact_mod_cast (Nat.pos_of_ne_zero hk0)
    symm
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hkpos.le]
    ring_nf

theorem criticalMellinPrimeMass_le_log_sqrt
    {h : ℝ} (hh : 0 ≤ h) :
    criticalMellinPrimeMass h ≤ 2 * h * Real.exp (h / 2) := by
  rw [criticalMellinPrimeMass_eq_primeMassHalf]
  have hmass := primeMassHalf_le (Real.one_le_exp hh)
  rw [Real.log_exp, ← Real.exp_half] at hmass
  exact hmass

theorem abs_criticalMellinCompletedError_le_log_sqrt
    {h : ℝ} (hh : 0 ≤ h) :
    |criticalMellinCompletedError h| ≤
      2 * (h + 1) * Real.exp (h / 2) := by
  have hexpNegLe : Real.exp (-(h / 2)) ≤ Real.exp (h / 2) := by
    rw [Real.exp_le_exp]
    linarith
  have hsinh0 : 0 ≤ Real.sinh (h / 2) := by
    rw [Real.sinh_eq]
    linarith
  have hpolar : 4 * Real.sinh (h / 2) ≤ 2 * Real.exp (h / 2) := by
    rw [Real.sinh_eq]
    have hneg0 : 0 ≤ Real.exp (-(h / 2)) := Real.exp_nonneg _
    linarith
  have hmass0 : 0 ≤ criticalMellinPrimeMass h :=
    criticalMellinPrimeMass_nonneg h
  have hmass := criticalMellinPrimeMass_le_log_sqrt hh
  rw [criticalMellinCompletedError_eq_polar_sub_primeMass]
  calc
    |4 * Real.sinh (h / 2) - criticalMellinPrimeMass h| ≤
        |4 * Real.sinh (h / 2)| + |criticalMellinPrimeMass h| := abs_sub _ _
    _ = 4 * Real.sinh (h / 2) + criticalMellinPrimeMass h := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) hsinh0), abs_of_nonneg hmass0]
    _ ≤ 2 * Real.exp (h / 2) + 2 * h * Real.exp (h / 2) :=
      add_le_add hpolar hmass
    _ = 2 * (h + 1) * Real.exp (h / 2) := by ring

theorem xiMassCriticalPrimePartialSource_eq_polar_sub_terminal_add_errorFlux
    {a σ A : ℝ} (ha : 0 < a) (hσ : 0 < σ) (hA : 0 ≤ A) (u : ℝ) :
    xiMassCriticalPrimePartialSource a σ u (2 * A) =
      xiMassPolarPartialSource a σ u (2 * A) -
        (criticalMellinCompletedError (2 * A) : ℂ) *
          stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) ((2 * A : ℝ) : ℂ) +
        ∫ h in Ioc (0 : ℝ) (2 * A),
          (criticalMellinCompletedError h : ℂ) *
            xiMassFourierDerivative a σ u h := by
  have h := xiMassCriticalStieltjes_eq_terminal_sub_errorFlux ha hσ hA u
  rw [criticalMellinStieltjesPairing] at h
  change xiMassPolarPartialSource a σ u (2 * A) -
      xiMassCriticalPrimePartialSource a σ u (2 * A) = _ at h
  calc
    xiMassCriticalPrimePartialSource a σ u (2 * A) =
        xiMassPolarPartialSource a σ u (2 * A) -
          (xiMassPolarPartialSource a σ u (2 * A) -
            xiMassCriticalPrimePartialSource a σ u (2 * A)) := by ring
    _ = xiMassPolarPartialSource a σ u (2 * A) -
        ((criticalMellinCompletedError (2 * A) : ℂ) *
          stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I))
            ((2 * A : ℝ) : ℂ) -
          ∫ h in Ioc (0 : ℝ) (2 * A),
            (criticalMellinCompletedError h : ℂ) *
              xiMassFourierDerivative a σ u h) := by rw [h]
    _ = _ := by ring

theorem xiMassCriticalPrimePartialSource_eq_polar_sub_terminal_add_errorFlux_height
    {a σ H : ℝ} (ha : 0 < a) (hσ : 0 < σ) (hH : 0 ≤ H) (u : ℝ) :
    xiMassCriticalPrimePartialSource a σ u H =
      xiMassPolarPartialSource a σ u H -
        (criticalMellinCompletedError H : ℂ) *
          stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (H : ℂ) +
        xiMassCompletedErrorFluxPartial a σ u H := by
  have h := xiMassCriticalPrimePartialSource_eq_polar_sub_terminal_add_errorFlux
    ha hσ (show 0 ≤ H / 2 by positivity) u
  simpa [xiMassCompletedErrorFluxPartial,
    show 2 * (H / 2) = H by ring] using h

def xiMassHalfShiftedTest (a σ u : ℝ) (x : ℝ) : ℂ :=
  xiMassAnalyticTest a ((σ : ℂ) + u * I)
    ((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I)

def xiMassHalfWeightedFourier (a σ u : ℝ) (w : ℝ) : ℂ :=
  (Real.exp (w / 2) : ℂ) *
    stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (w : ℂ)

theorem expFourier_xiMassHalfShifted_eq_halfWeighted
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u w : ℝ) :
    expFourier (xiMassHalfShiftedTest a σ u) (w : ℂ) =
      xiMassHalfWeightedFourier a σ u w := by
  let τ : ℂ := (σ : ℂ) + u * I
  let Q : ℂ → ℂ := fun z =>
    xiMassAnalyticTest a τ z * Complex.exp (-(I * (w : ℂ) * z))
  have ha : 0 < a := by linarith
  have hc0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hca : (1 / 2 : ℝ) < a := hhalf
  have hdiff : ∀ z : ℂ, |z.im| ≤ (1 / 2 : ℝ) → DifferentiableAt ℂ Q z := by
    intro z hz
    have hmem : z ∈ xiMassStrip a := lt_of_le_of_lt hz hca
    exact (hasDerivAt_xiMassAnalyticTest ha τ hmem).differentiableAt.mul (by fun_prop)
  have hbound : ∀ z : ℂ, |z.im| ≤ (1 / 2 : ℝ) →
      ‖Q z‖ ≤ Real.exp ((|τ.im| + |w|) * (1 / 2 : ℝ)) *
        Real.exp (-(σ * |z.re|)) := by
    intro z hz
    simpa [Q, τ] using
      (norm_xiMassFourierKernel_le (τ := τ) hca (by simpa [τ]) w hz)
  have hshift := integral_horizontal_shift_neg_of_decay hc0 hσ hdiff hbound
  have hintegrand : ∀ x : ℝ,
      Q ((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I) =
        (Real.exp (-(w / 2)) : ℂ) *
          (xiMassHalfShiftedTest a σ u x *
            Complex.exp (-(I * (w : ℂ) * (x : ℂ)))) := by
    intro x
    dsimp only [Q, xiMassHalfShiftedTest, τ]
    rw [show (Real.exp (-(w / 2)) : ℂ) *
        (xiMassAnalyticTest a ((σ : ℂ) + u * I)
          ((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I) *
            Complex.exp (-(I * (w : ℂ) * (x : ℂ)))) =
        xiMassAnalyticTest a ((σ : ℂ) + u * I)
          ((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I) *
            ((Real.exp (-(w / 2)) : ℂ) *
              Complex.exp (-(I * (w : ℂ) * (x : ℂ)))) by ring]
    congr 1
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hleft :
      (∫ x : ℝ, Q ((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I)) =
        (Real.exp (-(w / 2)) : ℂ) *
          expFourier (xiMassHalfShiftedTest a σ u) (w : ℂ) := by
    rw [show (fun x : ℝ => Q ((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I)) =
        fun x : ℝ => (Real.exp (-(w / 2)) : ℂ) *
          (xiMassHalfShiftedTest a σ u x *
            Complex.exp (-(I * (w : ℂ) * (x : ℂ)))) by
      funext x
      exact hintegrand x]
    rw [MeasureTheory.integral_const_mul]
    rfl
  have hright : (∫ x : ℝ, Q (x : ℂ)) =
      stripFourier (xiMassAnalyticTest a τ) (w : ℂ) := by
    rfl
  rw [hleft, hright] at hshift
  dsimp only [xiMassHalfWeightedFourier]
  calc
    expFourier (xiMassHalfShiftedTest a σ u) (w : ℂ) =
        (Real.exp (w / 2) : ℂ) *
          ((Real.exp (-(w / 2)) : ℂ) *
            expFourier (xiMassHalfShiftedTest a σ u) (w : ℂ)) := by
      rw [← mul_assoc]
      rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
      simp
    _ = (Real.exp (w / 2) : ℂ) *
        stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (w : ℂ) := by
      rw [hshift]

theorem norm_stripFourier_xiMass_deepShift_le
    {a σ d : ℝ} (hd0 : 0 ≤ d) (hda : d < a) (hσ : 0 < σ) (u w : ℝ) :
    ‖stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (w : ℂ)‖ ≤
      Real.exp (|u| * d - w * d) *
        ∫ x : ℝ, Real.exp (-(σ * |x|)) := by
  let τ : ℂ := (σ : ℂ) + u * I
  let Q : ℂ → ℂ := fun z =>
    xiMassAnalyticTest a τ z * Complex.exp (-(I * (w : ℂ) * z))
  have ha : 0 < a := lt_of_le_of_lt hd0 hda
  have hdiff : ∀ z : ℂ, |z.im| ≤ d → DifferentiableAt ℂ Q z := by
    intro z hz
    have hmem : z ∈ xiMassStrip a := lt_of_le_of_lt hz hda
    exact (hasDerivAt_xiMassAnalyticTest ha τ hmem).differentiableAt.mul (by fun_prop)
  have hrough : ∀ z : ℂ, |z.im| ≤ d →
      ‖Q z‖ ≤ Real.exp ((|τ.im| + |w|) * d) *
        Real.exp (-(σ * |z.re|)) := by
    intro z hz
    simpa [Q, τ] using
      (norm_xiMassFourierKernel_le (τ := τ) hda (by simpa [τ]) w hz)
  have hshift := integral_horizontal_shift_neg_of_decay hd0 hσ hdiff hrough
  have hmajor : Integrable (fun x : ℝ =>
      Real.exp (|u| * d - w * d) * Real.exp (-(σ * |x|))) :=
    (integrable_exp_neg_mul_abs hσ).const_mul _
  have hright : (∫ x : ℝ, Q (x : ℂ)) =
      stripFourier (xiMassAnalyticTest a τ) (w : ℂ) := rfl
  rw [hright] at hshift
  rw [← hshift]
  calc
    ‖∫ x : ℝ, Q ((x : ℂ) - (d : ℂ) * I)‖ ≤
        ∫ x : ℝ, Real.exp (|u| * d - w * d) * Real.exp (-(σ * |x|)) := by
      apply norm_integral_le_of_norm_le hmajor
      refine ae_of_all _ fun x => ?_
      have hzmem : ((x : ℂ) - (d : ℂ) * I) ∈ xiMassStrip a := by
        change |(((x : ℂ) - (d : ℂ) * I).im)| < a
        simpa [abs_of_nonneg hd0] using hda
      have hg := norm_xiMassAnalyticTest_le
        (τ := τ) ha (by simpa [τ] using hσ.le) hzmem
      have hzre : ((x : ℂ) - (d : ℂ) * I).re = x := by simp
      have hzim : ((x : ℂ) - (d : ℂ) * I).im = -d := by simp
      rw [hzre, hzim, abs_neg, abs_of_nonneg hd0] at hg
      dsimp only [Q]
      rw [norm_mul, Complex.norm_exp]
      have hphase : (-(I * (w : ℂ) * ((x : ℂ) - (d : ℂ) * I))).re = -w * d := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hphase]
      calc
        ‖xiMassAnalyticTest a τ ((x : ℂ) - (d : ℂ) * I)‖ * Real.exp (-w * d) ≤
            Real.exp (-σ * |x| + |u| * d) * Real.exp (-w * d) :=
          mul_le_mul_of_nonneg_right (by simpa [τ] using hg) (Real.exp_nonneg _)
        _ = Real.exp (|u| * d - w * d) * Real.exp (-(σ * |x|)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    _ = Real.exp (|u| * d - w * d) *
        ∫ x : ℝ, Real.exp (-(σ * |x|)) := by
      rw [MeasureTheory.integral_const_mul]

theorem integrable_xiMassHalfWeightedFourier
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    Integrable (xiMassHalfWeightedFourier a σ u) := by
  let d : ℝ := (a + 1 / 2) / 2
  let δ : ℝ := d - 1 / 2
  let r : ℝ := min (1 / 2 : ℝ) δ
  let J : ℝ := ∫ x : ℝ, Real.exp (-(σ * |x|))
  let C : ℝ := Real.exp (|u| * d) * J
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  have hδ : 0 < δ := by dsimp [δ, d]; linarith
  have hr : 0 < r := lt_min (by norm_num) hδ
  have hrhalf : r ≤ 1 / 2 := min_le_left _ _
  have hrδ : r ≤ δ := min_le_right _ _
  have hJ : 0 ≤ J := integral_nonneg fun _ => Real.exp_nonneg _
  have hC : 0 ≤ C := mul_nonneg (Real.exp_nonneg _) hJ
  have hJC : J ≤ C := by
    dsimp only [C]
    have he : 1 ≤ Real.exp (|u| * d) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact mul_nonneg (abs_nonneg u) hd0
    nlinarith [mul_le_mul_of_nonneg_right he hJ]
  have hFcont : Continuous (fun w : ℝ =>
      stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (w : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro w
    exact (hasDerivAt_xiMassRealFourierProfile
      (lt_trans (by norm_num) hhalf) hσ u w).continuousAt
  have hWcont : Continuous (xiMassHalfWeightedFourier a σ u) := by
    change Continuous (fun w : ℝ => (Real.exp (w / 2) : ℂ) *
      stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (w : ℂ))
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_id.div_const 2))).mul hFcont
  apply Integrable.mono'
    ((integrable_exp_neg_mul_abs hr).const_mul C)
    hWcont.aestronglyMeasurable
  refine ae_of_all _ fun w => ?_
  by_cases hw : 0 ≤ w
  · have hdeep := norm_stripFourier_xiMass_deepShift_le
      hd0 hda hσ u w
    rw [xiMassHalfWeightedFourier, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hδexp : Real.exp (-(δ * |w|)) ≤ Real.exp (-(r * |w|)) := by
      apply Real.exp_le_exp.mpr
      have haw : |w| = w := abs_of_nonneg hw
      rw [haw]
      nlinarith
    calc
      Real.exp (w / 2) *
          ‖stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (w : ℂ)‖ ≤
          Real.exp (w / 2) *
            (Real.exp (|u| * d - w * d) * J) :=
        mul_le_mul_of_nonneg_left hdeep (Real.exp_nonneg _)
      _ = C * Real.exp (-(δ * |w|)) := by
        rw [abs_of_nonneg hw]
        dsimp only [C, δ]
        rw [show Real.exp (w / 2) *
            (Real.exp (|u| * d - w * d) * J) =
            (Real.exp (w / 2) * Real.exp (|u| * d - w * d)) * J by ring,
          ← Real.exp_add]
        rw [show w / 2 + (|u| * d - w * d) =
            |u| * d - (d - 1 / 2) * w by ring]
        rw [show Real.exp (|u| * d) * J * Real.exp (-((d - 1 / 2) * w)) =
            (Real.exp (|u| * d) * Real.exp (-((d - 1 / 2) * w))) * J by ring,
          ← Real.exp_add]
        congr 2
      _ ≤ C * Real.exp (-(r * |w|)) :=
        mul_le_mul_of_nonneg_left hδexp hC
  · have hwneg : w < 0 := lt_of_not_ge hw
    have hbase := norm_stripFourier_xiMassAnalyticTest_vertical_le
      (lt_trans (by norm_num) hhalf) hσ u w
    rw [xiMassHalfWeightedFourier, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hwabs : |w| = -w := abs_of_neg hwneg
    have hhexp : Real.exp (w / 2) ≤ Real.exp (-(r * |w|)) := by
      apply Real.exp_le_exp.mpr
      rw [hwabs]
      have hwle : w ≤ 0 := hwneg.le
      nlinarith
    calc
      Real.exp (w / 2) *
          ‖stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (w : ℂ)‖ ≤
          Real.exp (w / 2) * J :=
        mul_le_mul_of_nonneg_left (by simpa [J] using hbase) (Real.exp_nonneg _)
      _ ≤ Real.exp (w / 2) * C :=
        mul_le_mul_of_nonneg_left hJC (Real.exp_nonneg _)
      _ ≤ Real.exp (-(r * |w|)) * C :=
        mul_le_mul_of_nonneg_right hhexp hC
      _ = C * Real.exp (-(r * |w|)) := by ring

theorem fourier_xiMassHalfShifted_eq_expFourier_two_pi (f : ℝ → ℂ) (w : ℝ) :
    FourierTransform.fourier f w = expFourier f ((2 * Real.pi * w : ℝ) : ℂ) :=
  fourier_eq_expFourier_two_pi f w

theorem integral_xiMassHalfWeightedFourier_eq_pointValue
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    (∫ w : ℝ, xiMassHalfWeightedFourier a σ u w) =
      (2 * Real.pi : ℂ) * xiMassHalfShiftedTest a σ u 0 := by
  let φ : ℝ → ℂ := xiMassHalfShiftedTest a σ u
  have ha : 0 < a := lt_trans (by norm_num) hhalf
  have hφcont : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hz : HasDerivAt
        (fun y : ℝ => (y : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I) 1 x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).sub_const
        ((((1 / 2 : ℝ) : ℂ)) * I)
    have hmem : ((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I) ∈ xiMassStrip a := by
      change |(((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I).im)| < a
      norm_num
      exact hhalf
    exact ((hasDerivAt_xiMassAnalyticTest ha ((σ : ℂ) + u * I) hmem).comp x hz).continuousAt
  have hφint : Integrable φ := by
    apply Integrable.mono'
      ((integrable_exp_neg_mul_abs hσ).const_mul (Real.exp (|u| / 2)))
      hφcont.aestronglyMeasurable
    refine ae_of_all _ fun x => ?_
    have hmem : ((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I) ∈ xiMassStrip a := by
      change |(((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I).im)| < a
      norm_num
      exact hhalf
    have hg := norm_xiMassAnalyticTest_le
      (τ := ((σ : ℂ) + u * I)) ha (by simpa using hσ.le) hmem
    have hzre : ((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I).re = x := by simp
    have hzim : ((x : ℂ) - (((1 / 2 : ℝ) : ℂ)) * I).im = -(1 / 2 : ℝ) := by simp
    rw [hzre, hzim, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hg
    change ‖xiMassHalfShiftedTest a σ u x‖ ≤ _
    calc
      ‖xiMassHalfShiftedTest a σ u x‖ ≤
          Real.exp (-σ * |x| + |u| / 2) := by
        simpa [φ, xiMassHalfShiftedTest, div_eq_mul_inv] using hg
      _ = Real.exp (|u| / 2) * Real.exp (-(σ * |x|)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hWint := integrable_xiMassHalfWeightedFourier hhalf hσ u
  have hWscale : Integrable (fun w : ℝ =>
      xiMassHalfWeightedFourier a σ u ((2 * Real.pi) * w)) :=
    hWint.comp_mul_left' (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourEq : (fun w : ℝ => FourierTransform.fourier φ w) =
      fun w : ℝ => xiMassHalfWeightedFourier a σ u ((2 * Real.pi) * w) := by
    funext w
    rw [fourier_xiMassHalfShifted_eq_expFourier_two_pi]
    exact expFourier_xiMassHalfShifted_eq_halfWeighted hhalf hσ u (2 * Real.pi * w)
  have hfourInt : Integrable (FourierTransform.fourier φ) := by
    exact hWscale.congr (ae_of_all _ fun w => (congrFun hfourEq w).symm)
  have hinv := hφcont.fourierInv_fourier_eq hφint hfourInt
  have hzero := congrFun hinv 0
  rw [Real.fourierInv_eq] at hzero
  have hchar : ∀ w : ℝ,
      (Real.fourierChar (inner ℝ w (0 : ℝ)) • FourierTransform.fourier φ w) =
        FourierTransform.fourier φ w := by
    intro w
    simp
  simp_rw [hchar] at hzero
  rw [hfourEq] at hzero
  have hscale := MeasureTheory.Measure.integral_comp_mul_left
    (xiMassHalfWeightedFourier a σ u) (2 * Real.pi)
  rw [hscale] at hzero
  have habs : |((2 * Real.pi)⁻¹)| = (2 * Real.pi)⁻¹ := by
    rw [abs_of_pos]
    positivity
  rw [habs, real_smul] at hzero
  change (∫ w : ℝ, xiMassHalfWeightedFourier a σ u w) =
      (2 * Real.pi : ℂ) * xiMassHalfShiftedTest a σ u 0
  have hscaleNe : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  apply (mul_left_cancel₀ (a := (2 * Real.pi : ℂ)⁻¹) (inv_ne_zero hscaleNe))
  rw [← mul_assoc]
  have hcancel : (2 * Real.pi : ℂ)⁻¹ * (2 * Real.pi : ℂ) = 1 :=
    inv_mul_cancel₀ hscaleNe
  rw [hcancel, one_mul]
  simpa [φ, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat] using hzero

theorem stripFourier_xiMassAnalyticTest_neg
    (a σ u w : ℝ) :
    stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (-w : ℂ) =
      stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (w : ℂ) := by
  rw [stripFourier, stripFourier]
  have href := MeasureTheory.integral_neg_eq_self
    (fun x : ℝ => xiMassAnalyticTest a ((σ : ℂ) + u * I) x *
      Complex.exp (-(I * (-w : ℂ) * x))) volume
  rw [← href]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  push_cast
  rw [xiMassAnalyticTest_neg]
  congr 1
  ring_nf

theorem xiMassPolarKernel_eq_halfWeighted_add_reflect
    (a σ u h : ℝ) :
    stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (h : ℂ) *
        (2 * Real.cosh (h / 2) : ℂ) =
      xiMassHalfWeightedFourier a σ u h +
        xiMassHalfWeightedFourier a σ u (-h) := by
  dsimp only [xiMassHalfWeightedFourier]
  rw [show ((-h : ℝ) : ℂ) = -(h : ℂ) by push_cast; rfl]
  rw [stripFourier_xiMassAnalyticTest_neg]
  rw [← add_mul, ← Complex.ofReal_add]
  rw [show Real.exp (h / 2) + Real.exp (-h / 2) =
      2 * Real.cosh (h / 2) by
    rw [show -h / 2 = -(h / 2) by ring]
    rw [Real.cosh_eq]
    ring]
  push_cast
  ring

theorem integrableOn_xiMassPolarKernel
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    IntegrableOn
      (fun h : ℝ =>
        stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (h : ℂ) *
          (2 * Real.cosh (h / 2) : ℂ))
      (Ioi 0) := by
  let W : ℝ → ℂ := xiMassHalfWeightedFourier a σ u
  have hWint : Integrable W := integrable_xiMassHalfWeightedFourier hhalf hσ u
  have hsum : Integrable (fun h : ℝ => W h + W (-h)) := hWint.add hWint.comp_neg
  refine hsum.integrableOn.congr_fun ?_ measurableSet_Ioi
  intro h hh
  exact (xiMassPolarKernel_eq_halfWeighted_add_reflect a σ u h).symm

theorem integral_xiMassPolarInfinite_eq_halfWeighted
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    (∫ h in Ioi (0 : ℝ),
        stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (h : ℂ) *
          (2 * Real.cosh (h / 2) : ℂ)) =
      ∫ w : ℝ, xiMassHalfWeightedFourier a σ u w := by
  let W : ℝ → ℂ := xiMassHalfWeightedFourier a σ u
  have hWint : Integrable W := integrable_xiMassHalfWeightedFourier hhalf hσ u
  rw [integral_eq_integral_Ioi_add_reflect hWint]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro h hh
  exact xiMassPolarKernel_eq_halfWeighted_add_reflect a σ u h

theorem integral_xiMassPolarInfinite_eq_archPole
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    (∫ h in Ioi (0 : ℝ),
        stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (h : ℂ) *
          (2 * Real.cosh (h / 2) : ℂ)) =
      (2 * Real.pi : ℂ) *
        xiMassAnalyticTest a ((σ : ℂ) + u * I) xiMassArchPole := by
  rw [integral_xiMassPolarInfinite_eq_halfWeighted hhalf hσ u,
    integral_xiMassHalfWeightedFourier_eq_pointValue hhalf hσ u]
  congr 1
  rw [xiMassHalfShiftedTest, xiMassArchPole]
  congr 2
  push_cast
  ring

theorem norm_integral_xiMassPolarInfinite_eq
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    ‖∫ h in Ioi (0 : ℝ),
        stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (h : ℂ) *
          (2 * Real.cosh (h / 2) : ℂ)‖ =
      2 * Real.pi * Real.exp (-σ * xiMassArchPoleFrequency a) := by
  rw [integral_xiMassPolarInfinite_eq_archPole hhalf hσ u,
    norm_mul, norm_xiMassAnalyticTest_archPole_eq hhalf]
  simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem tendsto_xiMassPolarPartialSource_atTop
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    Tendsto (fun H : ℝ => xiMassPolarPartialSource a σ u H) atTop
      (𝓝 ((2 * Real.pi : ℂ) *
        xiMassAnalyticTest a ((σ : ℂ) + u * I) xiMassArchPole)) := by
  have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) (0 : ℝ)
    (integrableOn_xiMassPolarKernel hhalf hσ u) tendsto_id
  rw [integral_xiMassPolarInfinite_eq_archPole hhalf hσ u] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  simp only [id_eq]
  rw [xiMassPolarPartialSource, intervalIntegral.integral_of_le hH]

theorem tendsto_xiMassCompletedError_terminal_zero
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    Tendsto
      (fun H : ℝ =>
        (criticalMellinCompletedError H : ℂ) *
          stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (H : ℂ))
      atTop (𝓝 0) := by
  let d : ℝ := (a + 1 / 2) / 2
  let δ : ℝ := d - 1 / 2
  let J : ℝ := ∫ x : ℝ, Real.exp (-(σ * |x|))
  let K : ℝ := 2 * J * Real.exp (|u| * d)
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  have hdhalf : 1 / 2 < d := by dsimp [d]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    apply MeasureTheory.integral_nonneg
    intro x
    exact Real.exp_nonneg _
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpoint : ∀ H : ℝ, 0 ≤ H →
      ‖(criticalMellinCompletedError H : ℂ) *
          stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (H : ℂ)‖ ≤
        K * ((H + 1) * Real.exp (-δ * H)) := by
    intro H hH
    have hE := abs_criticalMellinCompletedError_le_log_sqrt hH
    have hF := norm_stripFourier_xiMass_deepShift_le
      hd0 hda hσ u H
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |criticalMellinCompletedError H| *
          ‖stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (H : ℂ)‖ ≤
        (2 * (H + 1) * Real.exp (H / 2)) *
          (Real.exp (|u| * d - H * d) * J) := by
            apply mul_le_mul hE hF (norm_nonneg _)
            positivity
      _ = 2 * J * (H + 1) *
          (Real.exp (H / 2) * Real.exp (|u| * d - H * d)) := by ring
      _ = 2 * J * (H + 1) *
          Real.exp (|u| * d - (d - 1 / 2) * H) := by
            rw [← Real.exp_add]
            congr 2
            ring
      _ = 2 * J * (H + 1) *
          (Real.exp (|u| * d) * Real.exp (-(d - 1 / 2) * H)) := by
            rw [← Real.exp_add]
            congr 3
            ring
      _ = K * ((H + 1) * Real.exp (-δ * H)) := by
            dsimp [K, δ]
            ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun H => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    exact hpoint H hH
  · have hcoef : -δ < 0 := by linarith
    have harg : Tendsto (fun H : ℝ => (-δ) * H) atTop atBot := by
      simpa only [id_eq] using tendsto_id.const_mul_atTop_of_neg hcoef
    have hexp : Tendsto (fun H : ℝ => Real.exp (-δ * H)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp harg
    have hlinear := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 δ hδ
    have hsum : Tendsto
        (fun H : ℝ => H ^ (1 : ℝ) * Real.exp (-δ * H) + Real.exp (-δ * H))
        atTop (𝓝 0) := by
      simpa using hlinear.add hexp
    have hpoly : Tendsto (fun H : ℝ => (H + 1) * Real.exp (-δ * H))
        atTop (𝓝 0) := by
      refine hsum.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
      rw [Real.rpow_one]
      ring
    simpa using hpoly.const_mul K

theorem tendsto_xiMassPrimePartial_sub_completedErrorFlux_atTop
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    Tendsto
      (fun H : ℝ =>
        xiMassCriticalPrimePartialSource a σ u H -
          xiMassCompletedErrorFluxPartial a σ u H)
      atTop
      (𝓝 ((2 * Real.pi : ℂ) *
        xiMassAnalyticTest a ((σ : ℂ) + u * I) xiMassArchPole)) := by
  have hpolar := tendsto_xiMassPolarPartialSource_atTop hhalf hσ u
  have hterminal := tendsto_xiMassCompletedError_terminal_zero hhalf hσ u
  have hmain := hpolar.sub hterminal
  have heq :
      (fun H : ℝ =>
        xiMassPolarPartialSource a σ u H -
          (criticalMellinCompletedError H : ℂ) *
            stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (H : ℂ)) =ᶠ[atTop]
      (fun H : ℝ =>
        xiMassCriticalPrimePartialSource a σ u H -
          xiMassCompletedErrorFluxPartial a σ u H) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    rw [xiMassCriticalPrimePartialSource_eq_polar_sub_terminal_add_errorFlux_height
      (show 0 < a by linarith) hσ hH u]
    ring
  simpa using hmain.congr' heq

/-- Interior contour-shift decay for the true frequency derivative of the mass Fourier profile. -/
theorem norm_xiMassFourierDerivative_deepShift_le
    {a σ d : ℝ} (hd0 : 0 ≤ d) (hda : d < a) (hσ : 0 < σ) (u w : ℝ) :
    ‖xiMassFourierDerivative a σ u w‖ ≤
      Real.exp (|u| * d - w * d) *
        ∫ x : ℝ, (|x| + d) * Real.exp (-(σ * |x|)) := by
  let τ : ℂ := (σ : ℂ) + u * I
  let Q : ℂ → ℂ := fun z =>
    (xiMassAnalyticTest a τ z * Complex.exp (-(I * (w : ℂ) * z))) * (-(I * z))
  have ha : 0 < a := lt_of_le_of_lt hd0 hda
  have hdiff : ∀ z : ℂ, |z.im| ≤ d → DifferentiableAt ℂ Q z := by
    intro z hz
    have hmem : z ∈ xiMassStrip a := lt_of_le_of_lt hz hda
    exact ((hasDerivAt_xiMassAnalyticTest ha τ hmem).differentiableAt.mul
      (by fun_prop)).mul (by fun_prop)
  have hrough : ∀ z : ℂ, |z.im| ≤ d →
      ‖Q z‖ ≤
        (Real.exp ((|τ.im| + |w|) * d) * (2 / σ + d)) *
          Real.exp (-((σ / 2) * |z.re|)) := by
    intro z hz
    have hk := norm_xiMassFourierKernel_le (τ := τ) hda
      (by simpa [τ] using hσ) w hz
    have hk' :
        ‖xiMassAnalyticTest a τ z * Complex.exp (-(I * (w : ℂ) * z))‖ ≤
          Real.exp ((|τ.im| + |w|) * d) * Real.exp (-(σ * |z.re|)) := by
      simpa [τ] using hk
    have hnormz : ‖z‖ ≤ |z.re| + d := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ |z.re| + d := add_le_add le_rfl hz
    have hmoment := pow_abs_mul_exp_neg_le hσ 1 z.re
    have hmoment' : |z.re| * Real.exp (-(σ * |z.re|)) ≤
        (2 / σ) * Real.exp (-((σ / 2) * |z.re|)) := by
      simpa only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] using hmoment
    have hexp : Real.exp (-(σ * |z.re|)) ≤
        Real.exp (-((σ / 2) * |z.re|)) := by
      rw [Real.exp_le_exp]
      nlinarith [abs_nonneg z.re]
    dsimp only [Q]
    rw [norm_mul]
    rw [show ‖-(I * z)‖ = ‖z‖ by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul]]
    calc
      ‖xiMassAnalyticTest a τ z * Complex.exp (-(I * (w : ℂ) * z))‖ * ‖z‖ ≤
          (Real.exp ((|τ.im| + |w|) * d) * Real.exp (-(σ * |z.re|))) *
            (|z.re| + d) := by
              exact mul_le_mul hk' hnormz (norm_nonneg _)
                (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ = Real.exp ((|τ.im| + |w|) * d) *
          ((|z.re| + d) * Real.exp (-(σ * |z.re|))) := by ring
      _ ≤ Real.exp ((|τ.im| + |w|) * d) *
          ((2 / σ + d) * Real.exp (-((σ / 2) * |z.re|))) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
            calc
              (|z.re| + d) * Real.exp (-(σ * |z.re|)) =
                  |z.re| * Real.exp (-(σ * |z.re|)) +
                    d * Real.exp (-(σ * |z.re|)) := by ring
              _ ≤ (2 / σ) * Real.exp (-((σ / 2) * |z.re|)) +
                  d * Real.exp (-((σ / 2) * |z.re|)) :=
                    add_le_add hmoment' (mul_le_mul_of_nonneg_left hexp hd0)
              _ = (2 / σ + d) * Real.exp (-((σ / 2) * |z.re|)) := by ring
      _ = (Real.exp ((|τ.im| + |w|) * d) * (2 / σ + d)) *
          Real.exp (-((σ / 2) * |z.re|)) := by ring
  have hshift := integral_horizontal_shift_neg_of_decay hd0 (by positivity : 0 < σ / 2)
    hdiff hrough
  have hB : Integrable (fun x : ℝ => (|x| + d) * Real.exp (-(σ * |x|))) := by
    have h1 := integrable_abs_mul_exp_neg_mul_abs hσ
    have h2 := (integrable_exp_neg_mul_abs hσ).const_mul d
    rw [show (fun x : ℝ => (|x| + d) * Real.exp (-(σ * |x|))) =
        fun x : ℝ => |x| * Real.exp (-(σ * |x|)) +
          d * Real.exp (-(σ * |x|)) by
      funext x
      ring]
    exact h1.add h2
  have hmajor : Integrable (fun x : ℝ =>
      Real.exp (|u| * d - w * d) *
        ((|x| + d) * Real.exp (-(σ * |x|)))) := hB.const_mul _
  have hright : (∫ x : ℝ, Q (x : ℂ)) = xiMassFourierDerivative a σ u w := by
    rw [xiMassFourierDerivative]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    dsimp only [Q, τ]
    ring
  rw [hright] at hshift
  rw [← hshift]
  calc
    ‖∫ x : ℝ, Q ((x : ℂ) - (d : ℂ) * I)‖ ≤
        ∫ x : ℝ, Real.exp (|u| * d - w * d) *
          ((|x| + d) * Real.exp (-(σ * |x|))) := by
      apply norm_integral_le_of_norm_le hmajor
      refine ae_of_all _ fun x => ?_
      have hzmem : ((x : ℂ) - (d : ℂ) * I) ∈ xiMassStrip a := by
        change |(((x : ℂ) - (d : ℂ) * I).im)| < a
        simpa [abs_of_nonneg hd0] using hda
      have hg := norm_xiMassAnalyticTest_le
        (τ := τ) ha (by simpa [τ] using hσ.le) hzmem
      have hzre : ((x : ℂ) - (d : ℂ) * I).re = x := by simp
      have hzim : ((x : ℂ) - (d : ℂ) * I).im = -d := by simp
      rw [hzre, hzim, abs_neg, abs_of_nonneg hd0] at hg
      have hnormz : ‖(x : ℂ) - (d : ℂ) * I‖ ≤ |x| + d := by
        calc
          ‖(x : ℂ) - (d : ℂ) * I‖ ≤
              |((x : ℂ) - (d : ℂ) * I).re| +
                |((x : ℂ) - (d : ℂ) * I).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = |x| + d := by simp [abs_of_nonneg hd0]
      dsimp only [Q]
      rw [norm_mul, norm_mul, Complex.norm_exp, norm_neg, norm_mul,
        Complex.norm_I, one_mul]
      have hphase : (-(I * (w : ℂ) * ((x : ℂ) - (d : ℂ) * I))).re = -w * d := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hphase]
      calc
        ‖xiMassAnalyticTest a τ ((x : ℂ) - (d : ℂ) * I)‖ *
            Real.exp (-w * d) * ‖(x : ℂ) - (d : ℂ) * I‖ ≤
          (Real.exp (-σ * |x| + |u| * d) * Real.exp (-w * d)) *
            (|x| + d) := by
              exact mul_le_mul
                (mul_le_mul_of_nonneg_right (by simpa [τ] using hg) (Real.exp_nonneg _))
                hnormz (norm_nonneg _)
                (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        _ = Real.exp (|u| * d - w * d) *
            ((|x| + d) * Real.exp (-(σ * |x|))) := by
              rw [← Real.exp_add]
              rw [show (-σ * |x| + |u| * d) + -w * d =
                  (|u| * d - w * d) + -(σ * |x|) by ring,
                Real.exp_add]
              ring
    _ = Real.exp (|u| * d - w * d) *
        ∫ x : ℝ, (|x| + d) * Real.exp (-(σ * |x|)) := by
      rw [MeasureTheory.integral_const_mul]

/-- The true mass Fourier derivative is continuous on the real frequency line. -/
theorem continuous_xiMassFourierDerivative
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Continuous (fun h : ℝ => xiMassFourierDerivative a σ u h) := by
  let g : ℝ → ℂ := fun x => xiMassAnalyticTest a ((σ : ℂ) + u * I) x
  let g1 : ℝ → ℂ := fun x => g x * (-(I * (x : ℂ)))
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    have hz : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      change HasDerivAt (⇑Complex.ofRealCLM) 1 x
      exact Complex.ofRealCLM.hasDerivAt
    have hmem : (x : ℂ) ∈ xiMassStrip a := by
      change |((x : ℂ)).im| < a
      simpa using ha
    exact ((hasDerivAt_xiMassAnalyticTest ha _ hmem).comp x hz).continuousAt
  have hg1cont : Continuous g1 := by
    dsimp only [g1]
    fun_prop
  have hg1bound : ∀ x : ℝ,
      ‖g1 x‖ ≤ (2 / σ) * Real.exp (-((σ / 2) * |x|)) := by
    intro x
    have hmem : (x : ℂ) ∈ xiMassStrip a := by
      change |((x : ℂ)).im| < a
      simpa using ha
    have hg := norm_xiMassAnalyticTest_le
      (τ := ((σ : ℂ) + u * I)) ha (by simpa using hσ.le) hmem
    have hmoment := pow_abs_mul_exp_neg_le hσ 1 x
    have hmoment' : |x| * Real.exp (-(σ * |x|)) ≤
        (2 / σ) * Real.exp (-((σ / 2) * |x|)) := by
      simpa only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] using hmoment
    have hnormIx : ‖-(I * (x : ℂ))‖ = |x| := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    dsimp only [g1]
    rw [norm_mul, hnormIx]
    calc
      ‖g x‖ * |x| ≤ Real.exp (-(σ * |x|)) * |x| :=
        mul_le_mul_of_nonneg_right (by simpa [g] using hg) (abs_nonneg x)
      _ = |x| * Real.exp (-(σ * |x|)) := by ring
      _ ≤ (2 / σ) * Real.exp (-(σ / 2 * |x|)) := hmoment'
  have hderivEq : (fun h : ℝ => xiMassFourierDerivative a σ u h) =
      fun h : ℝ => expFourier g1 (h : ℂ) := by
    funext h
    rw [xiMassFourierDerivative, expFourier]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [g1, g]
    ring
  rw [hderivEq, continuous_iff_continuousAt]
  intro h
  have hw : |((h : ℂ)).im| < σ / 2 := by simpa using (show 0 < σ / 2 by positivity)
  have hout := hasDerivAt_expFourier hg1cont.aestronglyMeasurable
    (show 0 ≤ 2 / σ by positivity) hg1bound hw
  have hin : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 h := by
    change HasDerivAt (⇑Complex.ofRealCLM) 1 h
    exact Complex.ofRealCLM.hasDerivAt
  exact (hout.comp h hin).continuousAt

/-- The centered completed-error current is absolutely integrable for every fixed complex time. -/
theorem integrableOn_xiMassCompletedErrorFlux
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    IntegrableOn
      (fun h : ℝ => (criticalMellinCompletedError h : ℂ) *
        xiMassFourierDerivative a σ u h)
      (Ioi 0) := by
  let d : ℝ := (a + 1 / 2) / 2
  let δ : ℝ := d - 1 / 2
  let J : ℝ := ∫ x : ℝ, (|x| + d) * Real.exp (-(σ * |x|))
  let K : ℝ := 2 * Real.exp (|u| * d) * J
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  have hδ : 0 < δ := by dsimp [δ, d]; linarith
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    apply MeasureTheory.integral_nonneg
    intro x
    exact mul_nonneg (add_nonneg (abs_nonneg _) hd0) (Real.exp_nonneg _)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hlin0 := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (1 : ℝ)) (p := (1 : ℝ)) (b := δ) (by norm_num) (by norm_num) hδ
  have hlin : IntegrableOn (fun h : ℝ => h * Real.exp (-δ * h)) (Ioi 0) := by
    refine hlin0.congr_fun ?_ measurableSet_Ioi
    intro h hh
    simp
  have hexp : IntegrableOn (fun h : ℝ => Real.exp (-δ * h)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (show -δ < 0 by linarith) 0
  have hpoly : IntegrableOn
      (fun h : ℝ => (h + 1) * Real.exp (-δ * h)) (Ioi 0) := by
    rw [show (fun h : ℝ => (h + 1) * Real.exp (-δ * h)) =
        (fun h : ℝ => h * Real.exp (-δ * h)) +
          fun h : ℝ => Real.exp (-δ * h) by
      funext h
      simp only [Pi.add_apply]
      ring]
    exact hlin.add hexp
  have hmajor : IntegrableOn
      (fun h : ℝ => K * ((h + 1) * Real.exp (-δ * h))) (Ioi 0) :=
    hpoly.const_mul K
  have hEmeas : Measurable criticalMellinCompletedError := by
    rw [show criticalMellinCompletedError = fun h : ℝ =>
        4 * Real.sinh (h / 2) - criticalMellinPrimeMass h by
      funext h
      exact criticalMellinCompletedError_eq_polar_sub_primeMass h]
    exact (Real.continuous_sinh.comp (continuous_id.div_const 2)).const_mul 4
      |>.measurable.sub measurable_criticalMellinPrimeMass
  have hmeas : AEStronglyMeasurable
      (fun h : ℝ => (criticalMellinCompletedError h : ℂ) *
        xiMassFourierDerivative a σ u h) := by
    exact ((Complex.measurable_ofReal.comp hEmeas).mul
      (continuous_xiMassFourierDerivative (show 0 < a by linarith) hσ u).measurable)
      |>.aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [mem_Ioi] at hh
  have hE := abs_criticalMellinCompletedError_le_log_sqrt hh.le
  have hD := norm_xiMassFourierDerivative_deepShift_le hd0 hda hσ u h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |criticalMellinCompletedError h| * ‖xiMassFourierDerivative a σ u h‖ ≤
        (2 * (h + 1) * Real.exp (h / 2)) *
          (Real.exp (|u| * d - h * d) * J) := by
            apply mul_le_mul hE hD (norm_nonneg _)
            positivity
    _ = K * ((h + 1) * Real.exp (-δ * h)) := by
      have hexpid : Real.exp (h / 2) * Real.exp (|u| * d - h * d) =
          Real.exp (|u| * d) * Real.exp (-(d - 1 / 2) * h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      dsimp [K, δ]
      calc
        2 * (h + 1) * Real.exp (h / 2) *
            (Real.exp (|u| * d - h * d) * J) =
          2 * (h + 1) * J *
            (Real.exp (h / 2) * Real.exp (|u| * d - h * d)) := by ring
        _ = 2 * (h + 1) * J *
            (Real.exp (|u| * d) * Real.exp (-(d - 1 / 2) * h)) := by rw [hexpid]
        _ = 2 * Real.exp (|u| * d) * J *
            ((h + 1) * Real.exp (-(d - 1 / 2) * h)) := by ring

/-- Infinite centered completed-error current on the positive logarithmic ray. -/
def xiMassCompletedErrorFlux (a σ u : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ),
    (criticalMellinCompletedError h : ℂ) * xiMassFourierDerivative a σ u h

/-- Finite centered error currents converge to the absolutely convergent infinite current. -/
theorem tendsto_xiMassCompletedErrorFluxPartial_atTop
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    Tendsto (fun H : ℝ => xiMassCompletedErrorFluxPartial a σ u H) atTop
      (𝓝 (xiMassCompletedErrorFlux a σ u)) := by
  have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) (0 : ℝ)
    (integrableOn_xiMassCompletedErrorFlux hhalf hσ u) tendsto_id
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  simp only [id_eq]
  rw [xiMassCompletedErrorFluxPartial, intervalIntegral.integral_of_le hH]

/-- Exact infinite completed-source decomposition: prime source is pole value plus error current. -/
theorem tendsto_xiMassCriticalPrimePartialSource_atTop
    {a σ : ℝ} (hhalf : 1 / 2 < a) (hσ : 0 < σ) (u : ℝ) :
    Tendsto (fun H : ℝ => xiMassCriticalPrimePartialSource a σ u H) atTop
      (𝓝 ((2 * Real.pi : ℂ) *
          xiMassAnalyticTest a ((σ : ℂ) + u * I) xiMassArchPole +
        xiMassCompletedErrorFlux a σ u)) := by
  have hcenter := tendsto_xiMassPrimePartial_sub_completedErrorFlux_atTop hhalf hσ u
  have hflux := tendsto_xiMassCompletedErrorFluxPartial_atTop hhalf hσ u
  have hsum := hcenter.add hflux
  refine hsum.congr' ?_
  exact Eventually.of_forall fun H => by ring

end

end RHTower
