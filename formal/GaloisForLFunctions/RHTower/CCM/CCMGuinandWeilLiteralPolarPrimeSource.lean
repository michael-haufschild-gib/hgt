import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilContinuousSourceQuotient
import GaloisForLFunctions.RHTower.CCM.CCMPublishedSourceSineCoefficient
import Mathlib.Topology.ContinuousMap.Interval

/-!
# Literal polar--prime source in the continuous Guinand--Weil quotient

This file places the finite-aperture pole and prime-power channels of the critical-Mellin
Stieltjes distribution inside the source-native continuous dual on the physical horizon `[0,1]`.
The logarithmic coordinate `h in [0,2a]` is sent to `omega = 1 - h/(2a)`.  The pole channel is a
bounded interval-integral functional; the prime channel is the literal finite von-Mangoldt atomic
sum.  They remain separate before being added.

At every physical mode, horizon reflection negates the sine test.  Consequently the combined
continuous source value is exactly the published polar--prime CCM sine coefficient, including all
signs and the factor of `pi`.  This is unconditional.  It identifies one literal arithmetic
channel of the source quotient; it does not prove positivity of the completed CCM matrix.
-/

noncomputable section

open scoped BigOperators Interval

namespace RHTower

open Matrix MeasureTheory Set

/-- Continuous logarithmic-to-horizon map, clamped outside the physical aperture. -/
def ccmGuinandWeilLogToHorizon (a : ℝ) : C(ℝ, CCMGuinandWeilHorizon) := by
  refine ⟨fun h => Set.projIcc 0 1 (by norm_num)
      (1 - h / (2 * a)), ?_⟩
  fun_prop

/-- On the physical logarithmic aperture, the clamped map is the literal affine coordinate. -/
theorem ccmGuinandWeilLogToHorizon_coe_of_mem {a h : ℝ} (ha : 0 < a)
    (hh : h ∈ Set.Icc (0 : ℝ) (2 * a)) :
    (ccmGuinandWeilLogToHorizon a h).1 = 1 - h / (2 * a) := by
  have hx : 1 - h / (2 * a) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · have hdiv : h / (2 * a) ≤ 1 := (div_le_one (by positivity)).2 hh.2
      linarith
    · have hdiv : 0 ≤ h / (2 * a) := div_nonneg hh.1 (by positivity)
      linarith
  change (Set.projIcc 0 1 (by norm_num) (1 - h / (2 * a)) : ℝ) = _
  rw [Set.coe_projIcc, min_eq_right hx.2, max_eq_right hx.1]

/-- Prime-power indices visible below logarithmic aperture `2a`. -/
abbrev CCMGuinandWeilPrimeIndex (a : ℝ) :=
  {k : ℕ // k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊}

/-- Every visible prime-power logarithm lies in the closed logarithmic aperture. -/
theorem ccmGuinandWeilPrimeLog_mem {a : ℝ} {k : ℕ}
    (hk : k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊) :
    Real.log k ∈ Set.Icc (0 : ℝ) (2 * a) := by
  have hk' := Finset.mem_Icc.mp hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (show 0 < k by omega)
  have hkle : (k : ℝ) ≤ Real.exp (2 * a) := by
    calc
      (k : ℝ) ≤ (⌊Real.exp (2 * a)⌋₊ : ℝ) := by exact_mod_cast hk'.2
      _ ≤ Real.exp (2 * a) := Nat.floor_le (Real.exp_pos _).le
  exact ⟨Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega)),
    (Real.log_le_iff_le_exp hkpos).mpr hkle⟩

/-- Literal horizon location of a visible prime-power atom. -/
def ccmGuinandWeilPrimeHorizon {a : ℝ} (ha : 0 < a)
    (k : CCMGuinandWeilPrimeIndex a) : CCMGuinandWeilHorizon := by
  refine ⟨1 - Real.log k.1 / (2 * a), ?_⟩
  have hlog := ccmGuinandWeilPrimeLog_mem k.2
  constructor
  · have := (div_le_one (by positivity : 0 < 2 * a)).2 hlog.2
    linarith
  · have := div_nonneg hlog.1 (by positivity : 0 ≤ 2 * a)
    linarith

/-- The continuous logarithmic map agrees with the literal prime horizon. -/
theorem ccmGuinandWeilLogToHorizon_log_eq_primeHorizon {a : ℝ} (ha : 0 < a)
    (k : CCMGuinandWeilPrimeIndex a) :
    ccmGuinandWeilLogToHorizon a (Real.log k.1) =
      ccmGuinandWeilPrimeHorizon ha k := by
  ext
  rw [ccmGuinandWeilLogToHorizon_coe_of_mem ha
    (ccmGuinandWeilPrimeLog_mem k.2)]
  rfl

/-- At a physical mode, affine horizon transport negates the logarithmic sine test. -/
theorem ccmGuinandWeilSineCoordinate_logToHorizon {a : ℝ} (ha : 0 < a)
    (n : ℕ) {h : ℝ} (hh : h ∈ Set.Icc (0 : ℝ) (2 * a)) :
    ccmGuinandWeilSineCoordinate (n : ℤ) (ccmGuinandWeilLogToHorizon a h) =
      -Real.sin (ccmPublishedPhysicalFrequency a n * h) := by
  rw [show ccmGuinandWeilSineCoordinate (n : ℤ) (ccmGuinandWeilLogToHorizon a h) =
      Real.sin (2 * Real.pi * (ccmGuinandWeilLogToHorizon a h).1 * (n : ℝ)) by rfl,
    ccmGuinandWeilLogToHorizon_coe_of_mem ha hh]
  have harg :
      2 * Real.pi * (1 - h / (2 * a)) * (n : ℝ) =
        (n : ℝ) * (2 * Real.pi) - ccmPublishedPhysicalFrequency a n * h := by
    rw [ccmPublishedPhysicalFrequency]
    field_simp [ha.ne']
  rw [harg, Real.sin_nat_mul_two_pi_sub]

/-- Literal finite critical-weight prime-power source channel. -/
def ccmGuinandWeilPrimeSourceFunctional (a : ℝ) :
    CCMGuinandWeilContinuousSource :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
    (-criticalMellinAtomWeight k) •
      ContinuousMap.evalCLM ℝ (ccmGuinandWeilLogToHorizon a (Real.log k))

@[simp] theorem ccmGuinandWeilPrimeSourceFunctional_apply (a : ℝ)
    (f : C(CCMGuinandWeilHorizon, ℝ)) :
    ccmGuinandWeilPrimeSourceFunctional a f =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        -criticalMellinAtomWeight k *
          f (ccmGuinandWeilLogToHorizon a (Real.log k)) := by
  simp [ccmGuinandWeilPrimeSourceFunctional]

/-- Literal polar density `2 cosh(h/2) dh`, transported to the physical horizon. -/
def ccmGuinandWeilPoleSourceFunctional {a : ℝ} (ha : 0 < a) :
    CCMGuinandWeilContinuousSource :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ h in (0 : ℝ)..(2 * a),
        f (ccmGuinandWeilLogToHorizon a h) * (2 * Real.cosh (h / 2))
      map_add' := by
        intro f g
        change (∫ h in (0 : ℝ)..(2 * a),
            (f (ccmGuinandWeilLogToHorizon a h) +
                g (ccmGuinandWeilLogToHorizon a h)) *
              (2 * Real.cosh (h / 2))) = _
        rw [show (fun h : ℝ =>
              (f (ccmGuinandWeilLogToHorizon a h) +
                  g (ccmGuinandWeilLogToHorizon a h)) *
                (2 * Real.cosh (h / 2))) =
            (fun h => f (ccmGuinandWeilLogToHorizon a h) *
                (2 * Real.cosh (h / 2)) +
              g (ccmGuinandWeilLogToHorizon a h) *
                (2 * Real.cosh (h / 2))) by
              funext h
              ring]
        rw [intervalIntegral.integral_add]
        · exact (by fun_prop : Continuous (fun h : ℝ =>
            f (ccmGuinandWeilLogToHorizon a h) *
              (2 * Real.cosh (h / 2)))).intervalIntegrable _ _
        · exact (by fun_prop : Continuous (fun h : ℝ =>
            g (ccmGuinandWeilLogToHorizon a h) *
              (2 * Real.cosh (h / 2)))).intervalIntegrable _ _
      map_smul' := by
        intro c f
        change (∫ h in (0 : ℝ)..(2 * a),
            (c * f (ccmGuinandWeilLogToHorizon a h)) *
              (2 * Real.cosh (h / 2))) =
          c * ∫ h in (0 : ℝ)..(2 * a),
            f (ccmGuinandWeilLogToHorizon a h) * (2 * Real.cosh (h / 2))
        rw [show (fun h : ℝ =>
              (c * f (ccmGuinandWeilLogToHorizon a h)) *
                (2 * Real.cosh (h / 2))) =
            (fun h => c *
              (f (ccmGuinandWeilLogToHorizon a h) *
                (2 * Real.cosh (h / 2)))) by
              funext h
              ring]
        simpa only using intervalIntegral.integral_const_mul c
          (fun h : ℝ => f (ccmGuinandWeilLogToHorizon a h) *
            (2 * Real.cosh (h / 2))) }
    (4 * a * Real.cosh a)
    (fun f => by
      change ‖∫ h in (0 : ℝ)..(2 * a),
        f (ccmGuinandWeilLogToHorizon a h) * (2 * Real.cosh (h / 2))‖ ≤ _
      have hpoint : ∀ h ∈ Set.uIoc (0 : ℝ) (2 * a),
          ‖f (ccmGuinandWeilLogToHorizon a h) * (2 * Real.cosh (h / 2))‖ ≤
            2 * Real.cosh a * ‖f‖ := by
        intro h hh
        rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] at hh
        have hh' : h ∈ Set.Icc (0 : ℝ) (2 * a) := ⟨hh.1.le, hh.2⟩
        have habs : |h / 2| ≤ a := by
          rw [abs_of_nonneg (div_nonneg hh'.1 (by norm_num))]
          have : h / 2 ≤ a := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
            linarith [hh'.2])
          exact this
        have hcosh : Real.cosh (h / 2) ≤ Real.cosh a :=
          Real.cosh_le_cosh.mpr (by simpa [abs_of_pos ha] using habs)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity :
          0 ≤ 2 * Real.cosh (h / 2))]
        calc
          |f (ccmGuinandWeilLogToHorizon a h)| * (2 * Real.cosh (h / 2)) ≤
              ‖f‖ * (2 * Real.cosh (h / 2)) :=
            mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (by positivity)
          _ ≤ ‖f‖ * (2 * Real.cosh a) := by
            gcongr
          _ = 2 * Real.cosh a * ‖f‖ := by ring
      have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
      have hlen : |2 * a - 0| = 2 * a := by
        rw [sub_zero, abs_of_pos (by positivity)]
      rw [hlen] at hbound
      nlinarith [Real.cosh_pos a])

@[simp] theorem ccmGuinandWeilPoleSourceFunctional_apply {a : ℝ} (ha : 0 < a)
    (f : C(CCMGuinandWeilHorizon, ℝ)) :
    ccmGuinandWeilPoleSourceFunctional ha f =
      ∫ h in (0 : ℝ)..(2 * a),
        f (ccmGuinandWeilLogToHorizon a h) *
          (2 * Real.cosh (h / 2)) := rfl

/-- Polar and prime channels combined only after their separate construction. -/
def ccmGuinandWeilPolarPrimeSourceFunctional {a : ℝ} (ha : 0 < a) :
    CCMGuinandWeilContinuousSource :=
  ccmGuinandWeilPoleSourceFunctional ha + ccmGuinandWeilPrimeSourceFunctional a

@[simp] theorem ccmGuinandWeilPolarPrimeSourceFunctional_apply
    {a : ℝ} (ha : 0 < a) (f : C(CCMGuinandWeilHorizon, ℝ)) :
    ccmGuinandWeilPolarPrimeSourceFunctional ha f =
      (∫ h in (0 : ℝ)..(2 * a),
        f (ccmGuinandWeilLogToHorizon a h) * (2 * Real.cosh (h / 2))) +
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        -criticalMellinAtomWeight k *
          f (ccmGuinandWeilLogToHorizon a (Real.log k)) := by
  simp [ccmGuinandWeilPolarPrimeSourceFunctional]

/-- Real interval form of the critical-Mellin Stieltjes pairing on a sine test. -/
theorem ccmCriticalMellinStieltjesPairing_sine_re_interval
    {a xi : ℝ} (ha : 0 ≤ a) :
    (criticalMellinStieltjesPairing a
      (fun h => (Real.sin (xi * h) : ℂ))).re =
      (∫ h in (0 : ℝ)..(2 * a),
        Real.sin (xi * h) * (2 * Real.cosh (h / 2))) -
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        criticalMellinAtomWeight k * Real.sin (xi * Real.log k) := by
  let F : ℝ → ℂ := fun h =>
    (Real.sin (xi * h) : ℂ) * (2 * Real.cosh (h / 2) : ℂ)
  have hFcont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hFint : Integrable F (volume.restrict (Set.Ioc (0 : ℝ) (2 * a))) :=
    hFcont.continuousOn.integrableOn_Icc.mono_set fun h hh => ⟨hh.1.le, hh.2⟩
  have hintRe :
      (∫ h in Set.Ioc (0 : ℝ) (2 * a), F h).re =
        ∫ h in (0 : ℝ)..(2 * a),
          Real.sin (xi * h) * (2 * Real.cosh (h / 2)) := by
    calc
      (∫ h in Set.Ioc (0 : ℝ) (2 * a), F h).re =
          ∫ h in Set.Ioc (0 : ℝ) (2 * a), (F h).re :=
        (integral_re hFint).symm
      _ = ∫ h in Set.Ioc (0 : ℝ) (2 * a),
          Real.sin (xi * h) * (2 * Real.cosh (h / 2)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with h
        dsimp only [F]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        norm_num
      _ = _ := (intervalIntegral.integral_of_le (by positivity :
        (0 : ℝ) ≤ 2 * a)).symm
  rw [criticalMellinStieltjesPairing, Complex.sub_re, hintRe]
  simp only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- **Literal polar--prime source weld.**  At every physical mode, the source-native continuous
functional is exactly the published polar--prime CCM sine coefficient. -/
theorem ccmGuinandWeilPolarPrimeSourceValue_physical_eq_published
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ccmGuinandWeilContinuousSourceValue
        (ccmGuinandWeilPolarPrimeSourceFunctional ha) (n : ℤ) =
      ccmPublishedPolarPrimeSineCoefficient a
        (ccmPublishedPhysicalFrequency a n) := by
  let xi := ccmPublishedPhysicalFrequency a n
  have hpole :
      (∫ h in (0 : ℝ)..(2 * a),
        ccmGuinandWeilSineCoordinate (n : ℤ)
            (ccmGuinandWeilLogToHorizon a h) *
          (2 * Real.cosh (h / 2))) =
        -∫ h in (0 : ℝ)..(2 * a),
          Real.sin (xi * h) * (2 * Real.cosh (h / 2)) := by
    calc
      _ = ∫ h in (0 : ℝ)..(2 * a),
          (-Real.sin (xi * h)) * (2 * Real.cosh (h / 2)) := by
        apply intervalIntegral.integral_congr
        intro h hh
        have hh' : h ∈ Set.Icc (0 : ℝ) (2 * a) := by
          simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] using hh
        change ccmGuinandWeilSineCoordinate (n : ℤ)
              (ccmGuinandWeilLogToHorizon a h) * (2 * Real.cosh (h / 2)) =
          (-Real.sin (xi * h)) * (2 * Real.cosh (h / 2))
        rw [ccmGuinandWeilSineCoordinate_logToHorizon ha n hh']
      _ = _ := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro h _hh
        ring
  have hprime :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        -criticalMellinAtomWeight k *
          ccmGuinandWeilSineCoordinate (n : ℤ)
            (ccmGuinandWeilLogToHorizon a (Real.log k))) =
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          criticalMellinAtomWeight k * Real.sin (xi * Real.log k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [ccmGuinandWeilSineCoordinate_logToHorizon ha n
      (ccmGuinandWeilPrimeLog_mem hk)]
    dsimp only [xi]
    ring
  rw [ccmGuinandWeilContinuousSourceValue,
    ccmGuinandWeilPolarPrimeSourceFunctional_apply, hpole, hprime,
    ccmPublishedPolarPrimeSineCoefficient,
    ccmCriticalMellinStieltjesPairing_sine_re_interval ha.le]
  dsimp only [xi]
  ring

end RHTower
