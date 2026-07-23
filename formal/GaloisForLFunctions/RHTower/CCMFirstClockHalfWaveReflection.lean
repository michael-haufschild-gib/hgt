import GaloisForLFunctions.RHTower.CCMFirstClockVolterraReflection

/-!
# CCM first-clock half-wave reflection

The literal published CCM source is split at the midpoint of its first physical sine clock.
Midpoint reflection makes the complete continuous Gamma--polar term strictly positive.  The
prime-power term has an exact Jordan split into aligned and counter-phased nonnegative masses.
Consequently RH is equivalent to domination of the counter-phased mass by the aligned mass plus
the strict continuous budget.

Every theorem here is unconditional.  The final equivalence identifies the remaining arithmetic
frontier; it does not assume or assert that dominance.
-/

open MeasureTheory Set intervalIntegral

namespace RHTower

noncomputable section

theorem integral_sin_fullPeriod_eq_halfWaveReflection
    {L ξ : ℝ} (hL : 0 ≤ L) (hperiod : ξ * L = 2 * Real.pi)
    (f : ℝ → ℝ)
    (hg : IntervalIntegrable
      (fun h : ℝ => Real.sin (ξ * h) * f h) volume 0 L) :
    (∫ h : ℝ in (0 : ℝ)..L, Real.sin (ξ * h) * f h) =
      ∫ h : ℝ in (0 : ℝ)..(L / 2),
        Real.sin (ξ * h) * (f h - f (h + L / 2)) := by
  let g : ℝ → ℝ := fun h => Real.sin (ξ * h) * f h
  change IntervalIntegrable g volume 0 L at hg
  have hg0 : IntervalIntegrable g volume 0 (L / 2) :=
    hg.mono_set (by grind [uIcc])
  have hg1 : IntervalIntegrable g volume (L / 2) L :=
    hg.mono_set (by grind [uIcc])
  have hgshift :
      IntervalIntegrable (fun h : ℝ => g (h + L / 2))
        volume 0 (L / 2) := by
    convert hg1.comp_add_right (L / 2) using 1 <;> ring
  have hsplit :
      (∫ h : ℝ in (0 : ℝ)..L, g h) =
        (∫ h : ℝ in (0 : ℝ)..(L / 2), g h) +
          ∫ h : ℝ in (L / 2)..L, g h := by
    symm
    exact integral_add_adjacent_intervals hg0 hg1
  have hshift :
      (∫ h : ℝ in (L / 2)..L, g h) =
        ∫ h : ℝ in (0 : ℝ)..(L / 2), g (h + L / 2) := by
    have h := integral_comp_add_right g (a := (0 : ℝ)) (b := L / 2) (L / 2)
    rw [show (0 : ℝ) + L / 2 = L / 2 by ring,
      show L / 2 + L / 2 = L by ring] at h
    exact h.symm
  have hsine (h : ℝ) :
      Real.sin (ξ * (h + L / 2)) = -Real.sin (ξ * h) := by
    have hhalf : ξ * (L / 2) = Real.pi := by linarith
    rw [show ξ * (h + L / 2) = ξ * h + ξ * (L / 2) by ring,
      hhalf, Real.sin_add_pi]
  rw [hsplit, hshift]
  dsimp only [g]
  rw [← intervalIntegral.integral_add hg0 hgshift]
  apply intervalIntegral.integral_congr
  intro h _hh
  change g h + g (h + L / 2) =
    Real.sin (ξ * h) * (f h - f (h + L / 2))
  dsimp only [g]
  rw [hsine]
  ring

/-- Continuous Gamma--polar density left after expanding the literal published CCM source. -/
def ccmFirstClockContinuousSourceDensity (h : ℝ) : ℝ :=
  ccmPublishedArchimedeanDensity h - 2 * Real.cosh (h / 2)

/-- Half-turn reflection defect of the continuous Gamma--polar density. -/
def ccmFirstClockContinuousReflectionGap (L h : ℝ) : ℝ :=
  ccmFirstClockContinuousSourceDensity h -
    ccmFirstClockContinuousSourceDensity (h + L / 2)

theorem ccmPublishedArchimedeanDensity_strictAntiOn :
    StrictAntiOn ccmPublishedArchimedeanDensity (Ioi 0) := by
  intro h₁ hh₁ h₂ hh₂ hh
  change 0 < h₁ at hh₁
  change 0 < h₂ at hh₂
  rw [ccmPublishedArchimedeanDensity_eq_exp_neg_half_div hh₁,
    ccmPublishedArchimedeanDensity_eq_exp_neg_half_div hh₂]
  have hnpos₁ : 0 < Real.exp (-h₁ / 2) := Real.exp_pos _
  have hnpos₂ : 0 < Real.exp (-h₂ / 2) := Real.exp_pos _
  have hn : Real.exp (-h₂ / 2) < Real.exp (-h₁ / 2) := by
    exact Real.exp_lt_exp.mpr (by linarith)
  have he :
      Real.exp (-2 * h₂) < Real.exp (-2 * h₁) := by
    exact Real.exp_lt_exp.mpr (by linarith)
  have hdpos₁ : 0 < 1 - Real.exp (-2 * h₁) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hdpos₂ : 0 < 1 - Real.exp (-2 * h₂) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hd :
      1 - Real.exp (-2 * h₁) < 1 - Real.exp (-2 * h₂) := by
    linarith
  rw [div_lt_div_iff₀ hdpos₂ hdpos₁]
  calc
    Real.exp (-h₂ / 2) * (1 - Real.exp (-2 * h₁)) <
        Real.exp (-h₁ / 2) * (1 - Real.exp (-2 * h₁)) :=
      mul_lt_mul_of_pos_right hn hdpos₁
    _ < Real.exp (-h₁ / 2) * (1 - Real.exp (-2 * h₂)) :=
      mul_lt_mul_of_pos_left hd hnpos₁

/-- **Continuous first-clock orientation.**  Half-turn reflection makes the complete
Gamma--polar density strictly positive pointwise on the open first half-aperture. -/
theorem ccmFirstClockContinuousReflectionGap_pos
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h) :
    0 < ccmFirstClockContinuousReflectionGap L h := by
  have hhshift : h < h + L / 2 := by linarith
  have hrho :
      ccmPublishedArchimedeanDensity (h + L / 2) <
        ccmPublishedArchimedeanDensity h :=
    ccmPublishedArchimedeanDensity_strictAntiOn hh
      (by change 0 < h + L / 2; linarith) hhshift
  have hcosh :
      Real.cosh (h / 2) < Real.cosh ((h + L / 2) / 2) := by
    rw [Real.cosh_lt_cosh]
    rw [abs_of_pos (by linarith : 0 < h / 2),
      abs_of_pos (by linarith : 0 < (h + L / 2) / 2)]
    linarith
  rw [ccmFirstClockContinuousReflectionGap,
    ccmFirstClockContinuousSourceDensity,
    ccmFirstClockContinuousSourceDensity]
  linarith

/-- The physical sine removes the apparent pole of the one-sided CCM Gamma density. -/
theorem intervalIntegrable_sin_mul_ccmPublishedArchimedeanDensity
    {L ξ : ℝ} (hL : 0 < L) :
    IntervalIntegrable
      (fun h : ℝ =>
        Real.sin (ξ * h) * ccmPublishedArchimedeanDensity h)
      volume 0 L := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le]
  apply Measure.integrableOn_of_bounded (M := |ξ| * (1 + 2 * L) / 2)
    measure_Ioc_lt_top.ne
  · apply Measurable.aestronglyMeasurable
    unfold ccmPublishedArchimedeanDensity
    measurability
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    have hh0 : 0 < h := hh.1
    have hhL : h ≤ L := hh.2
    have hadd : 1 + 2 * h ≤ Real.exp (2 * h) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * h)
    have hlin : 0 < 1 + 2 * h := by linarith
    have hinv :
        Real.exp (-2 * h) ≤ (1 + 2 * h)⁻¹ := by
      rw [show -2 * h = -(2 * h) by ring, Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos (2 * h)) hlin).2 hadd
    have hdenLower :
        (2 * h) / (1 + 2 * h) ≤ 1 - Real.exp (-2 * h) := by
      calc
        (2 * h) / (1 + 2 * h) =
            1 - (1 + 2 * h)⁻¹ := by
              field_simp
              ring
        _ ≤ 1 - Real.exp (-2 * h) := by linarith
    have hdenPos : 0 < 1 - Real.exp (-2 * h) := by
      exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    have hlowerPos : 0 < (2 * h) / (1 + 2 * h) := div_pos (by linarith) hlin
    have hsin : |Real.sin (ξ * h)| ≤ |ξ| * h := by
      calc
        |Real.sin (ξ * h)| ≤ |ξ * h| := Real.abs_sin_le_abs
        _ = |ξ| * h := by rw [abs_mul, abs_of_pos hh0]
    have hexpLe : Real.exp (-h / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    rw [ccmPublishedArchimedeanDensity_eq_exp_neg_half_div hh0,
      Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (Real.exp_pos _), abs_of_pos hdenPos]
    rw [← mul_div_assoc]
    calc
      |Real.sin (ξ * h)| * Real.exp (-h / 2) /
          (1 - Real.exp (-2 * h)) ≤
          (|ξ| * h) / (1 - Real.exp (-2 * h)) := by
            apply div_le_div_of_nonneg_right _ hdenPos.le
            calc
              |Real.sin (ξ * h)| * Real.exp (-h / 2) ≤
                  (|ξ| * h) * Real.exp (-h / 2) :=
                mul_le_mul_of_nonneg_right hsin (Real.exp_pos _).le
              _ ≤ (|ξ| * h) * 1 :=
                mul_le_mul_of_nonneg_left hexpLe
                  (mul_nonneg (abs_nonneg _) hh0.le)
              _ = |ξ| * h := by ring
      _ ≤ (|ξ| * h) / ((2 * h) / (1 + 2 * h)) := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (abs_nonneg _) hh0.le) hlowerPos hdenLower
      _ = |ξ| * (1 + 2 * h) / 2 := by
        field_simp
      _ ≤ |ξ| * (1 + 2 * L) / 2 := by
        gcongr

/-- Prime-power mass seen by one full CCM sine clock. -/
def ccmFirstClockPrimeSineMass (L ξ : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    criticalMellinAtomWeight k * Real.sin (ξ * Real.log k)

/-- Prime mass whose phase agrees with the first sine half-wave. -/
def ccmFirstClockPrimeAlignedMass (L ξ : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    criticalMellinAtomWeight k *
      max (Real.sin (ξ * Real.log k)) 0

/-- Prime mass whose phase opposes the first sine half-wave. -/
def ccmFirstClockPrimeCounterMass (L ξ : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    criticalMellinAtomWeight k *
      max (-Real.sin (ξ * Real.log k)) 0

/-- Positive continuous half-wave budget exposed by reflection through the clock midpoint. -/
def ccmFirstClockContinuousHalfWaveBudget (L ξ : ℝ) : ℝ :=
  ∫ h : ℝ in (0 : ℝ)..(L / 2),
    Real.sin (ξ * h) * ccmFirstClockContinuousReflectionGap L h

theorem criticalMellinAtomWeight_nonneg (k : ℕ) :
    0 ≤ criticalMellinAtomWeight k := by
  rw [criticalMellinAtomWeight]
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    ArithmeticFunction.vonMangoldt_nonneg

theorem ccmFirstClockPrimeAlignedMass_nonneg (L ξ : ℝ) :
    0 ≤ ccmFirstClockPrimeAlignedMass L ξ := by
  rw [ccmFirstClockPrimeAlignedMass]
  exact Finset.sum_nonneg fun k _hk =>
    mul_nonneg (criticalMellinAtomWeight_nonneg k) (le_max_right _ _)

theorem ccmFirstClockPrimeCounterMass_nonneg (L ξ : ℝ) :
    0 ≤ ccmFirstClockPrimeCounterMass L ξ := by
  rw [ccmFirstClockPrimeCounterMass]
  exact Finset.sum_nonneg fun k _hk =>
    mul_nonneg (criticalMellinAtomWeight_nonneg k) (le_max_right _ _)

/-- Jordan half-wave decomposition of the finite prime sine mass. -/
theorem ccmFirstClockPrimeSineMass_eq_aligned_sub_counter (L ξ : ℝ) :
    ccmFirstClockPrimeSineMass L ξ =
      ccmFirstClockPrimeAlignedMass L ξ -
        ccmFirstClockPrimeCounterMass L ξ := by
  rw [ccmFirstClockPrimeSineMass, ccmFirstClockPrimeAlignedMass,
    ccmFirstClockPrimeCounterMass, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [← mul_sub]
  congr 1
  exact (max_zero_sub_max_neg_zero_eq_self
    (Real.sin (ξ * Real.log k))).symm

theorem intervalIntegrable_ccmFirstClockContinuousSource
    {L ξ : ℝ} (hL : 0 < L) :
    IntervalIntegrable
      (fun h : ℝ =>
        Real.sin (ξ * h) * ccmFirstClockContinuousSourceDensity h)
      volume 0 L := by
  have harch :=
    intervalIntegrable_sin_mul_ccmPublishedArchimedeanDensity
      (L := L) (ξ := ξ) hL
  have hpolar :
      IntervalIntegrable
        (fun h : ℝ => Real.sin (ξ * h) * (2 * Real.cosh (h / 2)))
        volume 0 L :=
    (by fun_prop : Continuous
      (fun h : ℝ => Real.sin (ξ * h) * (2 * Real.cosh (h / 2))))
      |>.intervalIntegrable 0 L
  refine IntervalIntegrable.congr ?_ (harch.sub hpolar)
  intro h _hh
  unfold ccmFirstClockContinuousSourceDensity
  ring

theorem intervalIntegrable_ccmFirstClockContinuousHalfWave
    {L ξ : ℝ} (hL : 0 < L) (hperiod : ξ * L = 2 * Real.pi) :
    IntervalIntegrable
      (fun h : ℝ =>
        Real.sin (ξ * h) * ccmFirstClockContinuousReflectionGap L h)
      volume 0 (L / 2) := by
  let f := ccmFirstClockContinuousSourceDensity
  let g : ℝ → ℝ := fun h => Real.sin (ξ * h) * f h
  have hg : IntervalIntegrable g volume 0 L := by
    exact intervalIntegrable_ccmFirstClockContinuousSource hL
  have hg0 : IntervalIntegrable g volume 0 (L / 2) :=
    hg.mono_set (by grind [uIcc])
  have hg1 : IntervalIntegrable g volume (L / 2) L :=
    hg.mono_set (by grind [uIcc])
  have hgshift :
      IntervalIntegrable (fun h : ℝ => g (h + L / 2))
        volume 0 (L / 2) := by
    convert hg1.comp_add_right (L / 2) using 1 <;> ring
  refine IntervalIntegrable.congr ?_ (hg0.add hgshift)
  intro h _hh
  have hhalf : ξ * (L / 2) = Real.pi := by linarith
  have hsine :
      Real.sin (ξ * (h + L / 2)) = -Real.sin (ξ * h) := by
    rw [show ξ * (h + L / 2) = ξ * h + ξ * (L / 2) by ring,
      hhalf, Real.sin_add_pi]
  dsimp only [g, f]
  unfold ccmFirstClockContinuousReflectionGap
  rw [hsine]
  ring

/-- Literal source expansion before midpoint reflection. -/
theorem pi_mul_ccmPublishedSourceSineCoefficient_eq_continuous_add_prime
    {L ξ : ℝ} (hL : 0 < L) :
    Real.pi * ccmPublishedSourceSineCoefficient (L / 2) ξ =
      (∫ h : ℝ in (0 : ℝ)..L,
        Real.sin (ξ * h) * ccmFirstClockContinuousSourceDensity h) +
      ccmFirstClockPrimeSineMass L ξ := by
  have harch :=
    intervalIntegrable_sin_mul_ccmPublishedArchimedeanDensity
      (L := L) (ξ := ξ) hL
  have hpolar :
      IntervalIntegrable
        (fun h : ℝ => Real.sin (ξ * h) * (2 * Real.cosh (h / 2)))
        volume 0 L :=
    (by fun_prop : Continuous
      (fun h : ℝ => Real.sin (ξ * h) * (2 * Real.cosh (h / 2))))
      |>.intervalIntegrable 0 L
  have hcombine :
      (∫ h : ℝ in (0 : ℝ)..L,
          Real.sin (ξ * h) * ccmFirstClockContinuousSourceDensity h) =
        (∫ h : ℝ in (0 : ℝ)..L,
          Real.sin (ξ * h) * ccmPublishedArchimedeanDensity h) -
        ∫ h : ℝ in (0 : ℝ)..L,
          Real.sin (ξ * h) * (2 * Real.cosh (h / 2)) := by
    rw [← intervalIntegral.integral_sub harch hpolar]
    apply intervalIntegral.integral_congr
    intro h _hh
    unfold ccmFirstClockContinuousSourceDensity
    ring
  have hpair :=
    criticalMellinStieltjesPairing_sine_re
      (L := L) (xi := ξ) hL.le
  rw [ccmPublishedSourceSineCoefficient,
    ccmPublishedArchimedeanSineCoefficient,
    ccmPublishedPolarPrimeSineCoefficient,
    show 2 * (L / 2) = L by ring,
    ← intervalIntegral.integral_of_le hL.le] at *
  rw [hpair, ccmFirstClockPrimeSineMass, hcombine]
  field_simp [Real.pi_ne_zero]
  ring_nf

/-- **CCM first-clock half-wave budget law.**  Every complete sine clock splits the
literal published source into a strictly oriented continuous midpoint-reflection budget
and the signed prime-power half-wave mass. -/
theorem pi_mul_ccmPublishedSourceSineCoefficient_eq_halfWaveBudget_add_prime
    {L ξ : ℝ} (hL : 0 < L) (hperiod : ξ * L = 2 * Real.pi) :
    Real.pi * ccmPublishedSourceSineCoefficient (L / 2) ξ =
      ccmFirstClockContinuousHalfWaveBudget L ξ +
        ccmFirstClockPrimeSineMass L ξ := by
  rw [pi_mul_ccmPublishedSourceSineCoefficient_eq_continuous_add_prime hL]
  congr 1
  exact integral_sin_fullPeriod_eq_halfWaveReflection
    hL.le hperiod ccmFirstClockContinuousSourceDensity
    (intervalIntegrable_ccmFirstClockContinuousSource hL)

/-- Oriented form: all three displayed quantities are nonnegative, and only the
counter-phased prime mass is subtractive. -/
theorem pi_mul_ccmPublishedSourceSineCoefficient_eq_budget_add_aligned_sub_counter
    {L ξ : ℝ} (hL : 0 < L) (hperiod : ξ * L = 2 * Real.pi) :
    Real.pi * ccmPublishedSourceSineCoefficient (L / 2) ξ =
      ccmFirstClockContinuousHalfWaveBudget L ξ +
        ccmFirstClockPrimeAlignedMass L ξ -
          ccmFirstClockPrimeCounterMass L ξ := by
  rw [pi_mul_ccmPublishedSourceSineCoefficient_eq_halfWaveBudget_add_prime
      hL hperiod,
    ccmFirstClockPrimeSineMass_eq_aligned_sub_counter]
  ring

theorem ccmFirstClockContinuousHalfWaveBudget_pos
    {L ξ : ℝ} (hL : 0 < L) (hperiod : ξ * L = 2 * Real.pi) :
    0 < ccmFirstClockContinuousHalfWaveBudget L ξ := by
  rw [ccmFirstClockContinuousHalfWaveBudget]
  apply intervalIntegral_pos_of_pos_on
    (intervalIntegrable_ccmFirstClockContinuousHalfWave hL hperiod)
  · intro h hh
    have hxi : 0 < ξ := by
      have hmul : 0 < ξ * L := by rw [hperiod]; positivity
      nlinarith
    have hsine : 0 < Real.sin (ξ * h) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · exact mul_pos hxi hh.1
      · have hhalf : ξ * (L / 2) = Real.pi := by linarith
        calc
          ξ * h < ξ * (L / 2) := mul_lt_mul_of_pos_left hh.2 hxi
          _ = Real.pi := hhalf
    exact mul_pos hsine (ccmFirstClockContinuousReflectionGap_pos hL hh.1)
  · linarith

/-- At the actual first CCM clock, source positivity is exactly domination of the
negative prime half-wave by the positive continuous reflection budget plus positive
prime half-wave. -/
theorem ccmPublishedSourceSineCoefficient_firstClock_nonneg_iff_primeMass
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    0 ≤ ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) ↔
      -ccmFirstClockPrimeSineMass L (2 * Real.pi / L) ≤
        ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  have hperiod : (2 * Real.pi / L) * L = 2 * Real.pi := by
    field_simp
  have hlaw :=
    pi_mul_ccmPublishedSourceSineCoefficient_eq_halfWaveBudget_add_prime
      hLpos hperiod
  constructor
  · intro hs
    have hsmul :
        0 ≤ Real.pi *
          ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) :=
      mul_nonneg Real.pi_pos.le hs
    rw [hlaw] at hsmul
    linarith
  · intro hdom
    apply (mul_nonneg_iff_of_pos_left Real.pi_pos).mp
    rw [hlaw]
    linarith

/-- Exact positive-mass criterion at the physical first clock. -/
theorem ccmPublishedSourceSineCoefficient_firstClock_nonneg_iff_halfWaveDominance
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    0 ≤ ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) ↔
      ccmFirstClockPrimeCounterMass L (2 * Real.pi / L) ≤
        ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
          ccmFirstClockPrimeAlignedMass L (2 * Real.pi / L) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  have hperiod : (2 * Real.pi / L) * L = 2 * Real.pi := by
    field_simp
  have hlaw :=
    pi_mul_ccmPublishedSourceSineCoefficient_eq_budget_add_aligned_sub_counter
      hLpos hperiod
  constructor
  · intro hs
    have hsmul :
        0 ≤ Real.pi *
          ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) :=
      mul_nonneg Real.pi_pos.le hs
    rw [hlaw] at hsmul
    linarith
  · intro hdom
    apply (mul_nonneg_iff_of_pos_left Real.pi_pos).mp
    rw [hlaw]
    linarith

/-- Source-only CCM frontier: counter-phased von Mangoldt mass is absorbed by
the strictly positive Gamma--polar reflection budget and aligned prime mass. -/
def CCMFirstClockPrimeHalfWaveDominance : Prop :=
  ∀ L : ℝ, Real.pi / 2 ≤ L →
    ccmFirstClockPrimeCounterMass L (2 * Real.pi / L) ≤
      ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
        ccmFirstClockPrimeAlignedMass L (2 * Real.pi / L)

/-- The positive-mass dominance law is exactly the published CCM source sign. -/
theorem ccmFirstClockPrimeHalfWaveDominance_iff_publishedSourceNonnegative :
    CCMFirstClockPrimeHalfWaveDominance ↔
      CCMFirstClockPublishedSourceNonnegative := by
  constructor
  · intro hdom L hL
    exact
      (ccmPublishedSourceSineCoefficient_firstClock_nonneg_iff_halfWaveDominance
        hL).2 (hdom L hL)
  · intro hsource L hL
    exact
      (ccmPublishedSourceSineCoefficient_firstClock_nonneg_iff_halfWaveDominance
        hL).1 (hsource L hL)

/-- **Positive-mass CCM criterion for RH.**  RH is equivalent to a single universal
dominance law between two nonnegative prime half-wave masses and the strictly positive
Gamma--polar reflection budget. -/
theorem ccmFirstClockPrimeHalfWaveDominance_iff_rh :
    CCMFirstClockPrimeHalfWaveDominance ↔ RiemannHypothesis := by
  rw [ccmFirstClockPrimeHalfWaveDominance_iff_publishedSourceNonnegative,
    ccmFirstClockPublishedSourceNonnegative_iff_rh]

end

end RHTower
