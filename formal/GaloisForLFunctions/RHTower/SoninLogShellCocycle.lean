/-
# The logarithmic Sonin shell cocycle

The exact even logarithmic unitary transports the physical cutoff to a half-line cutoff and
normalized dilation to additive translation.  Closing the cutoff/translation commutator by the
inverse translation leaves precisely the finite interval swept across the boundary.  Lebesgue
weight of that shell is the intrinsic logarithmic orbital length.  Pairing it with the existing
Euler-logarithm coefficient recovers the unsquared von Mangoldt flux coefficient exactly.

This is a semifinite principal-shell identity, not an ordinary Hilbert-space trace assertion.
-/
import GaloisForLFunctions.RHTower.SoninSemilocalRelativeTrace
import GaloisForLFunctions.RHTower.EvenL2LogUnitary

noncomputable section

namespace RHTower

open MeasureTheory Set
open scoped ENNReal

/-- Cutoff onto a left logarithmic half-line. -/
def logHalflineCutoff (b : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (Iic b) measurableSet_Iic

/-- The even physical cutoff `|x| ≤ a` is exactly the logarithmic half-line cutoff
`t ≤ log a` under the concrete even `L²` logarithmic unitary. -/
theorem logEvenUnitary_evenIndicatorCutoff
    (a : ℝ) (ha : 0 < a) (f : evenSubspace) :
    logEvenUnitary (evenIndicatorCutoff a f) =
      logHalflineCutoff (Real.log a) (logEvenUnitary f) := by
  apply Lp.ext
  have hcutExp :=
    (indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) f.1).comp_tendsto
      realExp_quasiMeasurePreserving.tendsto_ae
  filter_upwards [
    logEvenUnitary_ae (evenIndicatorCutoff a f),
    hcutExp,
    indicatorCutoff_ae (Iic (Real.log a)) measurableSet_Iic (logEvenUnitary f),
    logEvenUnitary_ae f
  ] with t hleft hcentral hright hbase
  rw [hleft]
  change (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
      indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f.1
        (Real.exp t)) =
    logHalflineCutoff (Real.log a) (logEvenUnitary f) t
  rw [show indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f.1
      (Real.exp t) =
      (centralInterval a).indicator (fun x => f.1 x) (Real.exp t) by
        simpa only [Function.comp_apply] using hcentral,
    show logHalflineCutoff (Real.log a) (logEvenUnitary f) t =
      (Iic (Real.log a)).indicator (fun x => logEvenUnitary f x) t by
        simpa [logHalflineCutoff] using hright]
  by_cases ht : t ≤ Real.log a
  · have hexp : Real.exp t ≤ a := by
      rw [← Real.exp_log ha]
      exact Real.exp_le_exp.mpr ht
    have hcentralMem : Real.exp t ∈ centralInterval a := by
      rw [centralInterval, mem_Icc]
      exact ⟨by linarith [Real.exp_pos t, ha], hexp⟩
    have hlogMem : t ∈ Iic (Real.log a) := ht
    rw [Set.indicator_of_mem hcentralMem, Set.indicator_of_mem hlogMem]
    exact hbase.symm
  · have hexp : a < Real.exp t := by
      rw [← Real.exp_log ha]
      exact Real.exp_lt_exp.mpr (lt_of_not_ge ht)
    have hcentralNot : Real.exp t ∉ centralInterval a := by
      intro hmem
      exact (not_le_of_gt hexp) hmem.2
    have hlogNot : t ∉ Iic (Real.log a) := ht
    rw [Set.indicator_of_notMem hcentralNot, Set.indicator_of_notMem hlogNot]
    simp

/-- Cutoff onto one finite logarithmic shell. -/
def logIntervalCutoff (lo hi : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (Ioc lo hi) measurableSet_Ioc

/-- Difference of nested logarithmic half-line cutoffs is the intervening shell projection. -/
theorem logHalflineCutoff_sub_eq_logIntervalCutoff
    {lo hi : ℝ} (hlohi : lo ≤ hi) :
    logHalflineCutoff hi - logHalflineCutoff lo =
      logIntervalCutoff lo hi := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [
    indicatorCutoff_ae (Iic hi) measurableSet_Iic f,
    indicatorCutoff_ae (Iic lo) measurableSet_Iic f,
    indicatorCutoff_ae (Ioc lo hi) measurableSet_Ioc f,
    Lp.coeFn_sub (logHalflineCutoff hi f) (logHalflineCutoff lo f)
  ] with x hhi hlo hint hsub
  rw [_root_.sub_apply, hsub]
  change logHalflineCutoff hi f x - logHalflineCutoff lo f x =
    logIntervalCutoff lo hi f x
  rw [show logHalflineCutoff hi f x = (Iic hi).indicator (fun y => f y) x by
        simpa [logHalflineCutoff] using hhi,
    show logHalflineCutoff lo f x = (Iic lo).indicator (fun y => f y) x by
        simpa [logHalflineCutoff] using hlo,
    show logIntervalCutoff lo hi f x = (Ioc lo hi).indicator (fun y => f y) x by
        simpa [logIntervalCutoff] using hint]
  by_cases hxlo : x ≤ lo
  · have hxhi : x ≤ hi := hxlo.trans hlohi
    have hxnot : x ∉ Ioc lo hi := fun hx => (not_lt_of_ge hxlo) hx.1
    simp [hxlo, hxhi, hxnot]
  · by_cases hxhi : x ≤ hi
    · have hxmem : x ∈ Ioc lo hi := ⟨lt_of_not_ge hxlo, hxhi⟩
      simp [hxlo, hxhi, hxmem]
    · have hxnot : x ∉ Ioc lo hi := fun hx => hxhi hx.2
      simp [hxlo, hxhi, hxnot]

/-- Additive translation as a bounded operator in logarithmic coordinates. -/
def logTranslationCLM (h : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  (MellinL2.additiveTranslationUnitary h).toLinearIsometry.toContinuousLinearMap

/-- Exact cutoff covariance under logarithmic translation. -/
theorem logHalflineCutoff_mul_logTranslationCLM (b h : ℝ) :
    logHalflineCutoff b * logTranslationCLM h =
      logTranslationCLM h * logHalflineCutoff (b + h) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hcutShift :=
    (indicatorCutoff_ae (Iic (b + h)) measurableSet_Iic f).comp_tendsto
      (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  filter_upwards [
    indicatorCutoff_ae (Iic b) measurableSet_Iic (logTranslationCLM h f),
    Lp.coeFn_compMeasurePreserving f (MellinL2.realTranslation_measurePreserving h),
    Lp.coeFn_compMeasurePreserving (logHalflineCutoff (b + h) f)
      (MellinL2.realTranslation_measurePreserving h),
    hcutShift
  ] with x hleft htrans hright hcut
  change logHalflineCutoff b (logTranslationCLM h f) x =
    logTranslationCLM h (logHalflineCutoff (b + h) f) x
  rw [show logHalflineCutoff b (logTranslationCLM h f) x =
      (Iic b).indicator (fun y => logTranslationCLM h f y) x by
        simpa [logHalflineCutoff] using hleft]
  change (Iic b).indicator (fun y => logTranslationCLM h f y) x =
    Lp.compMeasurePreserving (MellinL2.realTranslationEquiv h)
      (MellinL2.realTranslation_measurePreserving h)
      (logHalflineCutoff (b + h) f) x
  rw [hright]
  change (Iic b).indicator (fun y => logTranslationCLM h f y) x =
    logHalflineCutoff (b + h) f (x + h)
  rw [show logHalflineCutoff (b + h) f (x + h) =
      (Iic (b + h)).indicator (fun y => f y) (x + h) by
        simpa only [Function.comp_apply, MellinL2.realTranslationEquiv] using! hcut]
  have htrans' : logTranslationCLM h f x = f (x + h) := by
    simpa [logTranslationCLM, MellinL2.additiveTranslationUnitary,
      MellinL2.realTranslationEquiv] using! htrans
  by_cases hx : x ≤ b
  · have hxh : x + h ≤ b + h := by linarith
    simp [hx, hxh, htrans']
  · have hxh : ¬ x + h ≤ b + h := fun hle => hx (by linarith)
    simp [hx, hxh]

/-- Translation by `-h` is a left inverse to translation by `h`. -/
theorem logTranslationCLM_neg_mul (h : ℝ) :
    logTranslationCLM (-h) * logTranslationCLM h = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hinner :=
    (Lp.coeFn_compMeasurePreserving f
      (MellinL2.realTranslation_measurePreserving h)).comp_tendsto
        (MellinL2.realTranslation_measurePreserving (-h)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [
    Lp.coeFn_compMeasurePreserving (logTranslationCLM h f)
      (MellinL2.realTranslation_measurePreserving (-h)),
    hinner
  ] with x houter hinner'
  change logTranslationCLM (-h) (logTranslationCLM h f) x = f x
  change Lp.compMeasurePreserving (MellinL2.realTranslationEquiv (-h))
      (MellinL2.realTranslation_measurePreserving (-h))
      (logTranslationCLM h f) x = f x
  rw [houter]
  change logTranslationCLM h f (x + -h) = f x
  have hinner'' : logTranslationCLM h f (x + -h) = f ((x + -h) + h) := by
    simpa [logTranslationCLM, MellinL2.additiveTranslationUnitary,
      MellinL2.realTranslationEquiv, Function.comp_apply] using! hinner'
  rw [hinner'']
  congr 2
  ring

/-- Exact cutoff/translation cyclic cocycle: after closing the translation, the commutator is
the finite shell swept across the logarithmic boundary. -/
theorem logTranslation_cutoffCocycle_eq_shell {h : ℝ} (hh : 0 ≤ h) :
    logTranslationCLM (-h) *
        (logHalflineCutoff 0 * logTranslationCLM h -
          logTranslationCLM h * logHalflineCutoff 0) =
      logIntervalCutoff 0 h := by
  rw [mul_sub, logHalflineCutoff_mul_logTranslationCLM,
    ← mul_assoc, logTranslationCLM_neg_mul, one_mul,
    ← mul_assoc, logTranslationCLM_neg_mul, one_mul, zero_add,
    ← logHalflineCutoff_sub_eq_logIntervalCutoff hh]

/-- Under the logarithmic unitary, the concrete physical Sonin shell is exactly the finite
logarithmic interval projection. -/
theorem logEvenUnitary_evenPhysicalShell
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) (f : evenSubspace) :
    logEvenUnitary
        ((evenIndicatorCutoff (p * a) - evenIndicatorCutoff a) f) =
      logIntervalCutoff (Real.log a) (Real.log (p * a))
        (logEvenUnitary f) := by
  have hpa : 0 < p * a := mul_pos (zero_lt_one.trans hp) ha
  have hlog : Real.log a ≤ Real.log (p * a) := by
    rw [Real.log_mul (ne_of_gt (zero_lt_one.trans hp)) ha.ne']
    exact le_add_of_nonneg_left (Real.log_nonneg hp.le)
  rw [_root_.sub_apply, map_sub,
    logEvenUnitary_evenIndicatorCutoff (p * a) hpa,
    logEvenUnitary_evenIndicatorCutoff a ha,
    ← _root_.sub_apply,
    logHalflineCutoff_sub_eq_logIntervalCutoff hlog]

/-- Canonical semifinite weight of a physical logarithmic shell. -/
def soninPhysicalLogShellWeight (a p : ℝ) : ℝ :=
  volume.real (Ioc (Real.log a) (Real.log (p * a)))

/-- The shell weight is exactly logarithmic scale length and is independent of aperture. -/
theorem soninPhysicalLogShellWeight_eq_log
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    soninPhysicalLogShellWeight a p = Real.log p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hnonneg : 0 ≤ Real.log (p * a) - Real.log a := by
    rw [Real.log_mul hp0.ne' ha.ne']
    linarith [Real.log_nonneg hp.le]
  rw [soninPhysicalLogShellWeight, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal hnonneg, Real.log_mul hp0.ne' ha.ne']
  ring

/-- Prime-power Euler coefficient paired with the intrinsic physical shell weight. -/
def soninPrimePowerLogShellTraceDensity (pk : Nat.Primes × ℕ) : ℂ :=
  soninSemilocalLogPrimePowerCoefficient pk *
    (soninPhysicalLogShellWeight 1 (soninSemilocalPrimePowerScale pk) : ℂ)

/-- The logarithmic shell cocycle recovers the exact unsquared von Mangoldt flux coefficient. -/
theorem soninPrimePowerLogShellTraceDensity_eq_fluxCoefficient
    (pk : Nat.Primes × ℕ) :
    soninPrimePowerLogShellTraceDensity pk =
      soninSemilocalPrimeFluxCoefficient pk := by
  rw [soninPrimePowerLogShellTraceDensity,
    soninPhysicalLogShellWeight_eq_log 1 (soninSemilocalPrimePowerScale pk)
      zero_lt_one (one_lt_soninSemilocalPrimePowerScale pk),
    soninSemilocalPrimeFluxCoefficient,
    soninSemilocalLogScaleLength_eq_log_scale]

/-- The degree-zero coefficient integral is cyclic on a pair of crossed-product
monomials whose translation degrees are opposite. -/
theorem integral_mul_add_translate_cyclic
    (f g : ℝ → ℂ) (h : ℝ) :
    (∫ x : ℝ, f x * g (x + h)) =
      ∫ x : ℝ, g x * f (x - h) := by
  let F : ℝ → ℂ := fun x => f (x - h) * g x
  calc
    (∫ x : ℝ, f x * g (x + h)) = ∫ x : ℝ, F (x + h) := by
      congr 1
      funext x
      simp only [F, add_sub_cancel_right]
    _ = ∫ x : ℝ, F x := by
      exact (measurePreserving_add_right volume h).integral_comp
        (Homeomorph.addRight h).measurableEmbedding F
    _ = ∫ x : ℝ, g x * f (x - h) := by
      congr 1
      funext x
      exact mul_comm _ _

/-- Degree-paired coefficient integral for two finite algebraic logarithmic
translation sums.  This is the degree-zero coefficient integral of their
crossed-product product. -/
def logCrossedProductPairTrace
    (A B : ℝ →₀ (ℝ → ℂ)) : ℂ :=
  ∑ h ∈ A.support, ∑ k ∈ B.support,
    if h + k = 0 then ∫ x : ℝ, A h x * B k (x + h) else 0

/-- The degree-zero coefficient integral is cyclic on the full finite-support
algebraic logarithmic translation core. -/
theorem logCrossedProductPairTrace_comm
    (A B : ℝ →₀ (ℝ → ℂ)) :
    logCrossedProductPairTrace A B =
      logCrossedProductPairTrace B A := by
  rw [logCrossedProductPairTrace, logCrossedProductPairTrace,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hsum : h + k = 0
  · have hsum' : k + h = 0 := by linarith
    rw [if_pos hsum, if_pos hsum']
    have hk : k = -h := by linarith
    rw [hk]
    simpa only [sub_eq_add_neg] using
      integral_mul_add_translate_cyclic (A h) (B (-h)) h
  · have hsum' : k + h ≠ 0 := by
      simpa [add_comm] using hsum
    rw [if_neg hsum, if_neg hsum']

end RHTower
