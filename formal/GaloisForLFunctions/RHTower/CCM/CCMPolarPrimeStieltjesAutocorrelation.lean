import GaloisForLFunctions.RHTower.CCM.CCMPolarPrimeSourceSign
import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The polar--prime critical Mellin Stieltjes carrier

The continuous polar density and the finite von Mangoldt atoms are assembled here into one signed
Stieltjes pairing.  The pairing recovers the corrected finite-aperture symbol on exponential tests,
the completed critical-Mellin error on the constant test, and the positive-lag autocorrelation
quadratic form.  A finite-atom fundamental-theorem argument supplies the genuine Stieltjes
integration-by-parts identity for smooth aperture correlations.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory Set Finset ArithmeticFunction

noncomputable section

namespace RHTower

/-- The critical square-root von Mangoldt mass at the logarithmic atom `log k`. -/
def criticalMellinAtomWeight (k : ℕ) : ℝ :=
  ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k

/-- The cumulative prime mass can be indexed from `2`; zero and one carry no von Mangoldt mass. -/
theorem criticalMellinPrimeMass_eq_atomSum (h : ℝ) :
    criticalMellinPrimeMass h =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp h⌋₊, criticalMellinAtomWeight k := by
  rw [criticalMellinPrimeMass]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    exact ⟨by omega, hk.2⟩
  · intro k hk hnot
    simp only [Finset.mem_Icc] at hk
    have hklt : k < 2 := Nat.lt_of_not_ge fun hk2 =>
      hnot (Finset.mem_Icc.mpr ⟨hk2, hk.2⟩)
    interval_cases k <;> norm_num [criticalMellinAtomWeight]

/-- A common finite step expansion for every cumulative prime mass below a fixed height. -/
theorem criticalMellinPrimeMass_eq_commonAtomStep
    {h H : ℝ} (hhH : h ≤ H) :
    criticalMellinPrimeMass h =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if Real.log k ≤ h then criticalMellinAtomWeight k else 0 := by
  rw [criticalMellinPrimeMass_eq_atomSum]
  let K : Finset ℕ := Finset.Icc 2 ⌊Real.exp H⌋₊
  let p : ℕ → Prop := fun k => Real.log k ≤ h
  have hfin : (Finset.Icc 2 ⌊Real.exp h⌋₊ : Finset ℕ) = K.filter p := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_filter, K, p]
    constructor
    · intro hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hkexp : (k : ℝ) ≤ Real.exp h :=
        (Nat.le_floor_iff (Real.exp_pos h).le).mp hk.2
      have hlog : Real.log k ≤ h :=
        (Real.log_le_iff_le_exp hkpos).mpr hkexp
      have hfloor : ⌊Real.exp h⌋₊ ≤ ⌊Real.exp H⌋₊ :=
        Nat.floor_mono (Real.exp_le_exp.mpr hhH)
      exact ⟨⟨hk.1, hk.2.trans hfloor⟩, hlog⟩
    · intro hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hkexp : (k : ℝ) ≤ Real.exp h :=
        (Real.log_le_iff_le_exp hkpos).mp hk.2
      exact ⟨hk.1.1, (Nat.le_floor_iff (Real.exp_pos h).le).mpr hkexp⟩
  rw [hfin]
  exact Finset.sum_filter p criticalMellinAtomWeight

/-- The signed Stieltjes pairing `∫ F d(4 sinh(h/2) - A(h))` on `(0,2a]`. -/
def criticalMellinStieltjesPairing (a : ℝ) (F : ℝ → ℂ) : ℂ :=
  (∫ h in Ioc (0 : ℝ) (2 * a),
      F h * (2 * Real.cosh (h / 2) : ℂ)) -
    ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
      (criticalMellinAtomWeight k : ℂ) * F (Real.log k)

/-- The finite critical-weight prime cosine module in the corrected aperture symbol. -/
def criticalMellinPrimeCosineModule (a ξ : ℝ) : ℝ :=
  2 * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
    criticalMellinAtomWeight k * Real.cos (ξ * Real.log k)

/-- The polar--prime part of the corrected finite-aperture symbol. -/
def polarPrimeStieltjesSymbol (a ξ : ℝ) : ℝ :=
  polarMultiplier a ξ - criticalMellinPrimeCosineModule a ξ

/-- The aperture-independent archimedean digamma multiplier in the corrected CCM symbol. -/
def ccmArchimedeanMultiplier (ξ : ℝ) : ℝ :=
  (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((ξ / 2 : ℝ) : ℂ) * Complex.I)).re -
    Real.log Real.pi

/-- The complete corrected finite-aperture CCM symbol `W_a`. -/
def correctedCCMSymbol (a ξ : ℝ) : ℝ :=
  ccmArchimedeanMultiplier ξ + polarPrimeStieltjesSymbol a ξ

/-- Exponential tests recover the complete polar--prime symbol at every real frequency. -/
theorem criticalMellinStieltjesPairing_cexp_re
    {a ξ : ℝ} (ha : 0 ≤ a) :
    2 * (criticalMellinStieltjesPairing a
      (fun h => Complex.exp (((ξ * h : ℝ) : ℂ) * Complex.I))).re =
      polarPrimeStieltjesSymbol a ξ := by
  let F : ℝ → ℂ := fun h =>
    Complex.exp (((ξ * h : ℝ) : ℂ) * Complex.I) *
      (2 * Real.cosh (h / 2) : ℂ)
  have hFcont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hFint : Integrable F (volume.restrict (Ioc (0 : ℝ) (2 * a))) :=
    hFcont.continuousOn.integrableOn_Icc.mono_set fun h hh => ⟨hh.1.le, hh.2⟩
  have hintRe :
      (∫ h in Ioc (0 : ℝ) (2 * a), F h).re =
        ∫ h in Ioc (0 : ℝ) (2 * a),
          2 * Real.cosh (h / 2) * Real.cos (ξ * h) := by
    calc
      (∫ h in Ioc (0 : ℝ) (2 * a), F h).re =
          ∫ h in Ioc (0 : ℝ) (2 * a), (F h).re := (integral_re hFint).symm
      _ = ∫ h in Ioc (0 : ℝ) (2 * a),
          2 * Real.cosh (h / 2) * Real.cos (ξ * h) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with h
        dsimp only [F]
        rw [Complex.exp_mul_I]
        simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im,
          Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
          Complex.sin_ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          add_zero, sub_zero]
        norm_num
        ring
  have hsumRe :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        (criticalMellinAtomWeight k : ℂ) *
          Complex.exp ((((ξ * Real.log k : ℝ)) : ℂ) * Complex.I)).re =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        criticalMellinAtomWeight k * Real.cos (ξ * Real.log k) := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Complex.exp_mul_I]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_mul, add_zero, sub_zero]
  rw [criticalMellinStieltjesPairing, Complex.sub_re, hintRe, hsumRe,
    polarPrimeStieltjesSymbol, criticalMellinPrimeCosineModule,
    polarMultiplier_eq_cosineTransform ha]
  ring

/-- The complete corrected symbol is the archimedean multiplier plus the Fourier--Stieltjes
transform of the one signed critical Mellin carrier, equation `(18a)`. -/
theorem correctedCCMSymbol_eq_archimedean_add_stieltjes
    {a ξ : ℝ} (ha : 0 ≤ a) :
    correctedCCMSymbol a ξ =
      ccmArchimedeanMultiplier ξ +
        2 * (criticalMellinStieltjesPairing a
          (fun h => Complex.exp (((ξ * h : ℝ) : ℂ) * Complex.I))).re := by
  rw [correctedCCMSymbol,
    criticalMellinStieltjesPairing_cexp_re ha]

/-- The constant test reads the cumulative completed critical-Mellin error. -/
theorem criticalMellinStieltjesPairing_one
    {a : ℝ} (ha : 0 ≤ a) :
    criticalMellinStieltjesPairing a (fun _ => 1) =
      (criticalMellinCompletedError (2 * a) : ℂ) := by
  have hpolar :
      (∫ h in Ioc (0 : ℝ) (2 * a), 2 * Real.cosh (h / 2)) =
        4 * Real.sinh a := by
    have h := polarMultiplier_eq_cosineTransform (a := a) (ξ := 0) ha
    rw [polarMultiplier_zero] at h
    simp only [zero_mul, Real.cos_zero, mul_one] at h
    linarith
  rw [criticalMellinStieltjesPairing]
  simp only [one_mul, mul_one]
  have hpolarC : (∫ h in Ioc (0 : ℝ) (2 * a),
      (2 * Real.cosh (h / 2) : ℂ)) =
      (4 * Real.sinh a : ℂ) := by
    let Ip : ℝ := ∫ h in Ioc (0 : ℝ) (2 * a), 2 * Real.cosh (h / 2)
    have hdist :
        (∫ h in Ioc (0 : ℝ) (2 * a), (2 * Real.cosh (h / 2) : ℂ)) =
        ∫ h in Ioc (0 : ℝ) (2 * a),
          Complex.ofReal (2 * Real.cosh (h / 2)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with h
      rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
    have hwhole :
        (∫ h in Ioc (0 : ℝ) (2 * a),
          Complex.ofReal (2 * Real.cosh (h / 2))) = (Ip : ℂ) := by
      simp only [Ip]
      exact integral_ofReal
    have hIp : Ip = 4 * Real.sinh a := by
      simpa only [Ip] using hpolar
    have hfinal : (Ip : ℂ) = (4 * Real.sinh a : ℂ) := by
      rw [hIp]
      rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
    exact hdist.trans (hwhole.trans hfinal)
  have hsumC :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        (criticalMellinAtomWeight k : ℂ)) =
      (criticalMellinPrimeMass (2 * a) : ℂ) := by
    rw [← Complex.ofReal_sum, ← criticalMellinPrimeMass_eq_atomSum]
  rw [hpolarC, hsumC]
  rw [criticalMellinCompletedError_eq_polar_sub_primeMass]
  norm_cast
  rw [show 2 * a / 2 = a by ring]

/-- Zero frequency is twice the endpoint cumulative carrier, exactly equation `(21)`. -/
theorem polarPrimeStieltjesSymbol_zero
    {a : ℝ} (ha : 0 ≤ a) :
    polarPrimeStieltjesSymbol a 0 =
      2 * criticalMellinCompletedError (2 * a) := by
  have hpair := criticalMellinStieltjesPairing_cexp_re (a := a) (ξ := 0) ha
  have hone := criticalMellinStieltjesPairing_one (a := a) ha
  simp only [zero_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at hpair
  rw [hone] at hpair
  norm_num at hpair ⊢
  exact hpair.symm

/-- The zero-frequency defect of the complete symbol is exactly twice the endpoint carrier. -/
theorem correctedCCMSymbol_zero_sub_archimedean
    {a : ℝ} (ha : 0 ≤ a) :
    correctedCCMSymbol a 0 - ccmArchimedeanMultiplier 0 =
      2 * criticalMellinCompletedError (2 * a) := by
  rw [correctedCCMSymbol, polarPrimeStieltjesSymbol_zero ha]
  ring

/-- The cumulative Stieltjes carrier has the exact critical Chebyshev-error form. -/
theorem criticalMellinStieltjesCumulative_eq_criticalErrorForm
    {h : ℝ} (hh : 0 ≤ h) :
    criticalMellinCompletedError h =
      1 - 2 / Real.sqrt (Real.exp h) -
        criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h) /
          Real.sqrt (Real.exp h) -
        (1 / 2 : ℝ) * ∫ t in Ioc (1 : ℝ) (Real.exp h),
          criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
            t ^ (-3 / 2 : ℝ) := by
  simpa only [criticalMellinChebyshevPotential] using
    criticalMellinCompletedError_eq_chebyshevPotential hh

/-- Positive-lag autocorrelation of a zero-extended aperture vector. -/
def apertureAutocorrelation (v : ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ x : ℝ, v (x + h) * conj (v x)

/-- A vector supported in the closed aperture has zero autocorrelation at the full lag `2a`. -/
theorem apertureAutocorrelation_two_mul_eq_zero
    {a : ℝ} {v : ℝ → ℂ}
    (hv : ∀ x : ℝ, x ≤ -a ∨ a ≤ x → v x = 0) :
    apertureAutocorrelation v (2 * a) = 0 := by
  rw [apertureAutocorrelation]
  have hzero : (fun x : ℝ => v (x + 2 * a) * conj (v x)) = 0 := by
    funext x
    by_cases hx : x ≤ -a
    · rw [hv x (Or.inl hx)]
      simp
    · have hshift : a ≤ x + 2 * a := by linarith
      rw [hv (x + 2 * a) (Or.inr hshift)]
      simp
  rw [hzero]
  simp

/-- The exact polar--prime aperture quadratic form carried by the signed Stieltjes source. -/
def polarPrimeAutocorrelationQuadratic (a : ℝ) (v : ℝ → ℂ) : ℝ :=
  2 * (criticalMellinStieltjesPairing a (apertureAutocorrelation v)).re

/-- Expanded continuous-minus-atomic form of the autocorrelation carrier. -/
theorem polarPrimeAutocorrelationQuadratic_eq_integral_sub_sum
    {a : ℝ} {v : ℝ → ℂ}
    (hInt : Integrable
      (fun h => apertureAutocorrelation v h * (2 * Real.cosh (h / 2) : ℂ))
      (volume.restrict (Ioc (0 : ℝ) (2 * a)))) :
    polarPrimeAutocorrelationQuadratic a v =
      2 * (∫ h in Ioc (0 : ℝ) (2 * a),
          (apertureAutocorrelation v h).re * (2 * Real.cosh (h / 2))) -
        2 * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          criticalMellinAtomWeight k *
            (apertureAutocorrelation v (Real.log k)).re := by
  have hintRe :
      (∫ h in Ioc (0 : ℝ) (2 * a),
        apertureAutocorrelation v h * (2 * Real.cosh (h / 2) : ℂ)).re =
      ∫ h in Ioc (0 : ℝ) (2 * a),
        (apertureAutocorrelation v h).re * (2 * Real.cosh (h / 2)) := by
    calc
      _ = ∫ h in Ioc (0 : ℝ) (2 * a),
          (apertureAutocorrelation v h * (2 * Real.cosh (h / 2) : ℂ)).re :=
        (integral_re hInt).symm
      _ = _ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with h
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        norm_num
  have hsumRe :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        (criticalMellinAtomWeight k : ℂ) *
          apertureAutocorrelation v (Real.log k)).re =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        criticalMellinAtomWeight k *
          (apertureAutocorrelation v (Real.log k)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [polarPrimeAutocorrelationQuadratic, criticalMellinStieltjesPairing,
    Complex.sub_re, hintRe, hsumRe]
  ring

/-- Integral of one logarithmic atom against a derivative test. -/
private theorem integral_logAtom_mul_deriv
    {F F' : ℝ → ℂ} {H y : ℝ} (hy0 : 0 < y) (hyH : y ≤ H)
    (hF : ∀ x ∈ Set.uIcc y H, HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume y H) (c : ℂ) :
    (∫ h in Ioc (0 : ℝ) H, (if y ≤ h then c else 0) * F' h) =
      c * (F H - F y) := by
  have hfun : (fun h : ℝ => (if y ≤ h then c else 0) * F' h) =
      (Ici y).indicator (fun h => c * F' h) := by
    funext h
    by_cases hyh : y ≤ h <;> simp [Set.indicator, hyh]
  rw [hfun]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [Set.indicator_indicator]
  have hset : Ioc (0 : ℝ) H ∩ Ici y = Icc y H := by
    ext h
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
    constructor
    · intro hh
      exact ⟨hh.2, hh.1.2⟩
    · intro hh
      exact ⟨⟨hy0.trans_le hh.1, hh.2⟩, hh.1⟩
  rw [hset, MeasureTheory.integral_indicator measurableSet_Icc]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hyH]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hF']

/-- The cumulative prime step times an interval-integrable derivative is integrable. -/
private theorem integrableOn_criticalMellinPrimeMass_mul
    {F' : ℝ → ℂ} {H : ℝ} (hH : 0 ≤ H)
    (hF' : IntervalIntegrable F' volume 0 H) :
    Integrable (fun h => (criticalMellinPrimeMass h : ℂ) * F' h)
      (volume.restrict (Ioc (0 : ℝ) H)) := by
  let K : Finset ℕ := Finset.Icc 2 ⌊Real.exp H⌋₊
  have hbase : Integrable F' (volume.restrict (Ioc (0 : ℝ) H)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hH).mp hF'
  have hstep : ∀ k ∈ K, Integrable
      (fun h : ℝ =>
        ((if Real.log k ≤ h then criticalMellinAtomWeight k else 0 : ℝ) : ℂ) * F' h)
      (volume.restrict (Ioc (0 : ℝ) H)) := by
    intro k hk
    have hi := (hbase.const_mul (criticalMellinAtomWeight k : ℂ)).indicator
      (measurableSet_Ici : MeasurableSet (Ici (Real.log k)))
    apply hi.congr
    filter_upwards with h
    by_cases hkh : Real.log k ≤ h <;> simp [Set.indicator, hkh]
  have hsum := MeasureTheory.integrable_finsetSum K hstep
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
  rw [criticalMellinPrimeMass_eq_commonAtomStep hh.2]
  push_cast
  rw [Finset.sum_mul]

/-- Finite-atom Stieltjes integration by parts for the cumulative critical prime mass. -/
theorem criticalMellinPrimeMass_stieltjesIntegrationByParts
    {F F' : ℝ → ℂ} {H : ℝ} (hH : 0 ≤ H)
    (hF : ∀ x ∈ Set.Icc (0 : ℝ) H, HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume 0 H) (hFH : F H = 0) :
    (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      (criticalMellinAtomWeight k : ℂ) * F (Real.log k)) =
      -(∫ h in Ioc (0 : ℝ) H,
        (criticalMellinPrimeMass h : ℂ) * F' h) := by
  let K : Finset ℕ := Finset.Icc 2 ⌊Real.exp H⌋₊
  have hrepr :
      (∫ h in Ioc (0 : ℝ) H,
        (criticalMellinPrimeMass h : ℂ) * F' h) =
      ∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) *
        (F H - F (Real.log k)) := by
    have hbase : Integrable F' (volume.restrict (Ioc (0 : ℝ) H)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hH).mp hF'
    have hstep : ∀ k ∈ K, Integrable
        (fun h : ℝ =>
          ((if Real.log k ≤ h then criticalMellinAtomWeight k else 0 : ℝ) : ℂ) * F' h)
        (volume.restrict (Ioc (0 : ℝ) H)) := by
      intro k hk
      have hi := (hbase.const_mul (criticalMellinAtomWeight k : ℂ)).indicator
        (measurableSet_Ici : MeasurableSet (Ici (Real.log k)))
      apply hi.congr
      filter_upwards with h
      by_cases hkh : Real.log k ≤ h <;> simp [Set.indicator, hkh]
    have hmass :
        (∫ h in Ioc (0 : ℝ) H,
          (criticalMellinPrimeMass h : ℂ) * F' h) =
        ∫ h in Ioc (0 : ℝ) H,
          ∑ k ∈ K,
            ((if Real.log k ≤ h then criticalMellinAtomWeight k else 0 : ℝ) : ℂ) *
              F' h := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
      rw [criticalMellinPrimeMass_eq_commonAtomStep hh.2]
      push_cast
      rw [Finset.sum_mul]
    rw [hmass, MeasureTheory.integral_finsetSum K hstep]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hlog0 : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk2)
    have hkexp : (k : ℝ) ≤ Real.exp H :=
      (Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hk).2
    have hlogH : Real.log k ≤ H :=
      (Real.log_le_iff_le_exp hkpos).mpr hkexp
    have hFsub : ∀ x ∈ Set.uIcc (Real.log k) H, HasDerivAt F (F' x) x := by
      intro x hx
      apply hF x
      rw [Set.uIcc_of_le hlogH] at hx
      exact ⟨hlog0.le.trans hx.1, hx.2⟩
    have hFsubInt : IntervalIntegrable F' volume (Real.log k) H :=
      hF'.mono_set (by
        rw [Set.uIcc_of_le hlogH, Set.uIcc_of_le hH]
        exact Set.Icc_subset_Icc hlog0.le le_rfl)
    have hatom := integral_logAtom_mul_deriv (F := F) (F' := F') hlog0 hlogH
      hFsub hFsubInt (criticalMellinAtomWeight k : ℂ)
    rw [← hatom]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with h
    by_cases hkh : Real.log k ≤ h <;> simp [hkh]
  rw [hrepr, hFH]
  simp only [zero_sub, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rfl

/-- Continuous polar Stieltjes integration by parts. -/
theorem continuousPolar_stieltjesIntegrationByParts
    {F F' : ℝ → ℂ} {H : ℝ} (hH : 0 ≤ H)
    (hF : ∀ x ∈ Set.Icc (0 : ℝ) H, HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume 0 H) (hFH : F H = 0) :
    (∫ h in Ioc (0 : ℝ) H,
      F h * (2 * Real.cosh (h / 2) : ℂ)) =
      -(∫ h in Ioc (0 : ℝ) H,
        (4 * Real.sinh (h / 2) : ℂ) * F' h) := by
  let P : ℝ → ℂ := fun h => Complex.ofReal (4 * Real.sinh (h / 2))
  have hP : ∀ x ∈ Set.uIcc (0 : ℝ) H,
      HasDerivAt P (Complex.ofReal (2 * Real.cosh (x / 2))) x := by
    intro x hx
    dsimp only [P]
    have hr : HasDerivAt (fun h : ℝ => 4 * Real.sinh (h / 2))
        (2 * Real.cosh (x / 2)) x := by
      apply (((Real.hasDerivAt_sinh (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2)).const_mul 4).congr_deriv
      ring
    have hc := (Complex.ofRealCLM.hasFDerivAt.comp x hr.hasFDerivAt).hasDerivAt
    simpa only [Function.comp_apply, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] using! hc
  have hP' : IntervalIntegrable
      (fun h : ℝ => Complex.ofReal (2 * Real.cosh (h / 2)))
      volume 0 H := by
    have hc : Continuous (fun h : ℝ => Complex.ofReal (2 * Real.cosh (h / 2))) := by fun_prop
    exact hc.intervalIntegrable (μ := volume) 0 H
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := F) (v := P) (u' := F')
    (v' := fun h => Complex.ofReal (2 * Real.cosh (h / 2)))
    (fun x hx => hF x (by simpa only [Set.uIcc_of_le hH] using hx))
    hP hF' hP'
  dsimp only [P] at hibp
  have hPzero : Complex.ofReal (4 * Real.sinh ((0 : ℝ) / 2)) = 0 := by norm_num
  rw [hFH, hPzero] at hibp
  simp only [zero_mul, mul_zero, sub_zero, zero_sub] at hibp
  rw [intervalIntegral.integral_of_le hH,
    intervalIntegral.integral_of_le hH] at hibp
  have hcomm :
      (∫ h in Ioc (0 : ℝ) H,
        F' h * Complex.ofReal (4 * Real.sinh (h / 2))) =
      ∫ h in Ioc (0 : ℝ) H,
        Complex.ofReal (4 * Real.sinh (h / 2)) * F' h := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with h
    ring
  rw [hcomm] at hibp
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hibp

/-- Stieltjes integration by parts for the complete signed critical Mellin carrier. -/
theorem criticalMellinStieltjesPairing_integrationByParts
    {a : ℝ} (ha : 0 ≤ a) {F F' : ℝ → ℂ}
    (hF : ∀ x ∈ Set.Icc (0 : ℝ) (2 * a), HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume 0 (2 * a))
    (hFend : F (2 * a) = 0) :
    criticalMellinStieltjesPairing a F =
      -(∫ h in Ioc (0 : ℝ) (2 * a),
        (criticalMellinCompletedError h : ℂ) * F' h) := by
  have hH : (0 : ℝ) ≤ 2 * a := by linarith
  have hpolar := continuousPolar_stieltjesIntegrationByParts hH hF hF' hFend
  have hprime := criticalMellinPrimeMass_stieltjesIntegrationByParts hH hF hF' hFend
  have hpolarInt : Integrable
      (fun h => (4 * Real.sinh (h / 2) : ℂ) * F' h)
      (volume.restrict (Ioc (0 : ℝ) (2 * a))) := by
    have hpi : IntervalIntegrable
        (fun h => (4 * Real.sinh (h / 2) : ℂ) * F' h) volume 0 (2 * a) :=
      hF'.continuousOn_mul (by fun_prop)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hH).mp hpi
  have hprimeInt := integrableOn_criticalMellinPrimeMass_mul hH hF'
  rw [criticalMellinStieltjesPairing, hpolar, hprime]
  have hcarrier : ∀ h : ℝ,
      (criticalMellinCompletedError h : ℂ) =
        (4 * Real.sinh (h / 2) : ℂ) - (criticalMellinPrimeMass h : ℂ) := by
    intro h
    rw [criticalMellinCompletedError_eq_polar_sub_primeMass]
    rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hsplit :
      (∫ h in Ioc (0 : ℝ) (2 * a),
        (criticalMellinCompletedError h : ℂ) * F' h) =
      (∫ h in Ioc (0 : ℝ) (2 * a),
        (4 * Real.sinh (h / 2) : ℂ) * F' h) -
      ∫ h in Ioc (0 : ℝ) (2 * a),
        (criticalMellinPrimeMass h : ℂ) * F' h := by
    rw [← MeasureTheory.integral_sub hpolarInt hprimeInt]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with h
    rw [hcarrier h]
    ring
  rw [hsplit]
  ring

/-- Smooth autocorrelations with vanishing edge value satisfy equation `(19)`. -/
theorem polarPrimeAutocorrelationQuadratic_integrationByParts
    {a : ℝ} (ha : 0 ≤ a) {v : ℝ → ℂ} {C' : ℝ → ℂ}
    (hC : ∀ x ∈ Set.Icc (0 : ℝ) (2 * a),
      HasDerivAt (apertureAutocorrelation v) (C' x) x)
    (hC' : IntervalIntegrable C' volume 0 (2 * a))
    (hCend : apertureAutocorrelation v (2 * a) = 0) :
    polarPrimeAutocorrelationQuadratic a v =
      -2 * (∫ h in Ioc (0 : ℝ) (2 * a),
        (criticalMellinCompletedError h : ℂ) * C' h).re := by
  rw [polarPrimeAutocorrelationQuadratic,
    criticalMellinStieltjesPairing_integrationByParts ha hC hC' hCend]
  simp only [Complex.neg_re]
  ring

/-- Aperture support supplies the vanishing endpoint in the smooth autocorrelation law. -/
theorem polarPrimeAutocorrelationQuadratic_integrationByParts_of_support
    {a : ℝ} (ha : 0 ≤ a) {v : ℝ → ℂ} {C' : ℝ → ℂ}
    (hv : ∀ x : ℝ, x ≤ -a ∨ a ≤ x → v x = 0)
    (hC : ∀ x ∈ Set.Icc (0 : ℝ) (2 * a),
      HasDerivAt (apertureAutocorrelation v) (C' x) x)
    (hC' : IntervalIntegrable C' volume 0 (2 * a)) :
    polarPrimeAutocorrelationQuadratic a v =
      -2 * (∫ h in Ioc (0 : ℝ) (2 * a),
        (criticalMellinCompletedError h : ℂ) * C' h).re := by
  exact polarPrimeAutocorrelationQuadratic_integrationByParts ha hC hC'
    (apertureAutocorrelation_two_mul_eq_zero hv)

end RHTower
