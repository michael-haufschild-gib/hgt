import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalTranslatedPrimeHarmonicDiagonal
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeCumulativeCharge
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Physical and periodic kernels of the complete critical prime form

The complete limiting prime form is an integral against a single arithmetic
physical density, then against its real L1 periodization on a unit cell.
Reflection symmetrization preserves every finite real coefficient pattern.
Closed harmonic tails give an exact floor-charge identity at integer endpoints;
absolute cubic summability justifies the integral exchange. The existing real
periodization and Fourier coefficient APIs supply the unit-cell reduction.

These identities do not assert positivity or negativity of the total form.
The L1 periodization uses its own endpoint convention; continuity at integers
is not assumed.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The common physical weight after removing the harmonic dilation. -/
def factorialCriticalPrimeKernelWeight (u : ℝ) : ℝ :=
  u ^ (-2 : ℝ) * (1 - Real.cos (2 * Real.pi * u / 12))

/-- Real finite coefficient patterns have period one. -/
theorem factorialCriticalPatternDensity_periodic (S : Finset ℕ) (b : ℕ → ℝ) :
    Function.Periodic (factorialCriticalPatternDensity S b) 1 := by
  intro t
  have hc (j : ℕ) : Real.cos (2 * Real.pi * j * (t + 1)) =
      Real.cos (2 * Real.pi * j * t) := by
    rw [show 2 * Real.pi * (j : ℝ) * (t + 1) =
      2 * Real.pi * j * t + j * (2 * Real.pi) by ring]
    exact Real.cos_add_nat_mul_two_pi _ _
  have hs (j : ℕ) : Real.sin (2 * Real.pi * j * (t + 1)) =
      Real.sin (2 * Real.pi * j * t) := by
    rw [show 2 * Real.pi * (j : ℝ) * (t + 1) =
      2 * Real.pi * j * t + j * (2 * Real.pi) by ring]
    exact Real.sin_add_nat_mul_two_pi _ _
  simp only [factorialCriticalPatternDensity, hc, hs]

/-- Real finite coefficient patterns are symmetric under reflection of the unit cell. -/
theorem factorialCriticalPatternDensity_reflection (S : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    factorialCriticalPatternDensity S b (1 - t) = factorialCriticalPatternDensity S b t := by
  have hc (j : ℕ) : Real.cos (2 * Real.pi * j * (1 - t)) =
      Real.cos (2 * Real.pi * j * t) := by
    rw [show 2 * Real.pi * (j : ℝ) * (1 - t) =
      j * (2 * Real.pi) - 2 * Real.pi * j * t by ring]
    exact Real.cos_nat_mul_two_pi_sub _ _
  have hs (j : ℕ) : Real.sin (2 * Real.pi * j * (1 - t)) =
      -Real.sin (2 * Real.pi * j * t) := by
    rw [show 2 * Real.pi * (j : ℝ) * (1 - t) =
      j * (2 * Real.pi) - 2 * Real.pi * j * t by ring]
    exact Real.sin_nat_mul_two_pi_sub _ _
  simp only [factorialCriticalPatternDensity, hc, hs, mul_neg, Finset.sum_neg_distrib, neg_sq]

/-- Each positive harmonic tail of the common pattern density is integrable. -/
theorem integrable_factorialCriticalPrimeKernelWeight_mul_patternDensity
    (S : Finset ℕ) (b : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    IntegrableOn (fun u : ℝ => factorialCriticalPrimeKernelWeight u *
      factorialCriticalPatternDensity S b u) (Ioi (m : ℝ)) := by
  have hf := integrable_factorialCriticalPatternHarmonicMass S b 1
  have hset : Ioi (m : ℝ) ⊆ Ioi (1 : ℝ) := by
    intro u hu
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    exact lt_of_le_of_lt hm1 hu
  simpa only [factorialCriticalPrimeKernelWeight, Nat.cast_one, mul_one, one_mul, mul_assoc]
    using hf.mono_set hset

/-- Every harmonic mass is a tail integral of the same periodic pattern density. -/
theorem factorialCriticalPatternHarmonicMass_eq_common_tail
    (S : Finset ℕ) (b : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    factorialCriticalPatternHarmonicMass S b m =
      (m : ℝ) * ∫ u in Ioi (m : ℝ), factorialCriticalPrimeKernelWeight u *
        factorialCriticalPatternDensity S b u := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let f : ℝ → ℝ := fun u => factorialCriticalPrimeKernelWeight u *
    factorialCriticalPatternDensity S b u
  have hscale (v : ℝ) (hv : v ∈ Ioi (1 : ℝ)) :
      v ^ (-2 : ℝ) = (m : ℝ)^2 * ((m : ℝ) * v) ^ (-2 : ℝ) := by
    have hvp : 0 < v := lt_trans zero_lt_one hv
    rw [Real.rpow_neg hvp.le, Real.rpow_two,
      Real.rpow_neg (mul_pos hmR hvp).le, Real.rpow_two]
    field_simp [hmR.ne', hvp.ne']
  have hcv := integral_comp_mul_left_Ioi f 1 hmR
  calc
    factorialCriticalPatternHarmonicMass S b m =
        ∫ v in Ioi (1 : ℝ), (m : ℝ)^2 * f ((m : ℝ) * v) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      unfold f factorialCriticalPrimeKernelWeight
      dsimp only
      rw [hscale v hv]
      simp only [mul_assoc]
    _ = (m : ℝ)^2 * ∫ v in Ioi (1 : ℝ), f ((m : ℝ) * v) := integral_const_mul _ _
    _ = (m : ℝ) * ∫ u in Ioi (m : ℝ), f u := by
      rw [hcv]
      simp only [mul_one, smul_eq_mul]
      field_simp [hmR.ne']

/-- Closed harmonic tails recover the cumulative charge, including integer endpoints. -/
theorem factorialCriticalPrimeCumulativeCharge_floor_eq_tsum (u : ℝ) :
    factorialCriticalPrimeCumulativeCharge ⌊u⌋₊ =
      ∑' m : ℕ, if (m : ℝ) ≤ u then factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3 else 0 := by
  unfold factorialCriticalPrimeCumulativeCharge
  symm
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊u⌋₊) (fun m hm => ?_)]
  · apply Finset.sum_congr rfl
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hmu : (m : ℝ) ≤ u := (Nat.le_floor_iff' (by omega : m ≠ 0)).mp
      (Finset.mem_Icc.mp hm).2
    exact if_pos hmu
  · by_cases hm0 : m = 0
    · simp [hm0]
    · have hmu : ¬ (m : ℝ) ≤ u := by
        intro h
        exact hm (Finset.mem_Icc.mpr ⟨by omega, (Nat.le_floor_iff' hm0).mpr h⟩)
      exact if_neg hmu

/-- The signed physical kernel whose periodization determines the prime form. -/
def factorialCriticalPrimeKernelDensity (u : ℝ) : ℝ :=
  factorialCriticalPrimeKernelWeight u * factorialCriticalPrimeCumulativeCharge ⌊u⌋₊

private def kernelPatternBase (S : Finset ℕ) (b : ℕ → ℝ) (u : ℝ) : ℝ :=
  (Ici (1 : ℝ)).indicator (fun v => factorialCriticalPrimeKernelWeight v *
    factorialCriticalPatternDensity S b v) u

private def kernelChargeTail (S : Finset ℕ) (b : ℕ → ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  (factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3) *
    (Ici (m : ℝ)).indicator (kernelPatternBase S b) u

private theorem kernel_pattern_base_integrable (S : Finset ℕ) (b : ℕ → ℝ) :
    Integrable (kernelPatternBase S b) := by
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  apply (integrableOn_Ici_iff_integrableOn_Ioi).mpr
  simpa only [Nat.cast_one] using
    integrable_factorialCriticalPrimeKernelWeight_mul_patternDensity S b (by norm_num : 0 < 1)

private theorem kernel_charge_tail_integrability (S : Finset ℕ) (b : ℕ → ℝ) :
    (∀ m : ℕ, Integrable (kernelChargeTail S b m)) ∧
      Summable (fun m : ℕ => ∫ u : ℝ, ‖kernelChargeTail S b m u‖) := by
  have hF := kernel_pattern_base_integrable S b
  have hi (m : ℕ) : Integrable (kernelChargeTail S b m) :=
    (hF.indicator measurableSet_Ici).const_mul _
  refine ⟨hi, ?_⟩
  have hbound (m : ℕ) : (∫ u : ℝ, ‖kernelChargeTail S b m u‖) ≤
      (|factorialCriticalPrimeHarmonicCharge m| / (m : ℝ)^3) *
        ∫ u : ℝ, ‖kernelPatternBase S b u‖ := by
    have hc : ‖factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3‖ =
        |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ)^3 := by
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (show 0 ≤ (m : ℝ)^3 by positivity)]
    calc
      (∫ u : ℝ, ‖kernelChargeTail S b m u‖) ≤
          ∫ u : ℝ, (|factorialCriticalPrimeHarmonicCharge m| / (m : ℝ)^3) *
            ‖kernelPatternBase S b u‖ := by
        apply integral_mono_ae (hi m).norm (hF.norm.const_mul _)
        filter_upwards with u
        simp only [kernelChargeTail, norm_mul, hc]
        exact mul_le_mul_of_nonneg_left
          (norm_indicator_le_norm_self (kernelPatternBase S b) u) (by positivity)
      _ = _ := integral_const_mul _ _
  exact Summable.of_nonneg_of_le (fun m => integral_nonneg (fun u => norm_nonneg _)) hbound
    (summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube.mul_right _)

private theorem kernel_charge_tail_sum (S : Finset ℕ) (b : ℕ → ℝ) (u : ℝ) :
    (∑' m : ℕ, kernelChargeTail S b m u) =
      factorialCriticalPrimeKernelDensity u * factorialCriticalPatternDensity S b u := by
  have heq (m : ℕ) : kernelChargeTail S b m u =
      (if (m : ℝ) ≤ u then factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3 else 0) *
        kernelPatternBase S b u := by
    by_cases hm : (m : ℝ) ≤ u
    · simp [kernelChargeTail, hm]
    · simp [kernelChargeTail, hm]
  simp_rw [heq]
  rw [tsum_mul_right, ← factorialCriticalPrimeCumulativeCharge_floor_eq_tsum]
  by_cases hu : 1 ≤ u
  · simp only [kernelPatternBase, factorialCriticalPrimeKernelDensity]
    rw [Set.indicator_of_mem (show u ∈ Ici (1 : ℝ) from hu)]
    ring
  · have hfloor : ⌊u⌋₊ ≤ 1 := by
      by_contra h
      have htwo : (2 : ℝ) ≤ u := (Nat.le_floor_iff' (by decide : (2 : ℕ) ≠ 0)).mp
        (by omega : 2 ≤ ⌊u⌋₊)
      linarith
    have hz := (factorialCriticalPrimeCumulativeCharge_sign ⌊u⌋₊).2.1.mpr hfloor
    simp [factorialCriticalPrimeKernelDensity, hz]

private theorem kernel_charge_tail_integral (S : Finset ℕ) (b : ℕ → ℝ) (m : ℕ) :
    (∫ u : ℝ, kernelChargeTail S b m u) = factorialCriticalPrimeHarmonicCharge m *
      factorialCriticalPatternHarmonicMass S b m / (m : ℝ)^4 := by
  by_cases hm0 : m = 0
  · subst m
    simp [kernelChargeTail]
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hbase : (∫ u in Ici (m : ℝ), kernelPatternBase S b u) =
      ∫ u in Ioi (m : ℝ), factorialCriticalPrimeKernelWeight u *
        factorialCriticalPatternDensity S b u := by
    rw [← integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ici
    intro u hu
    have hu1 : (1 : ℝ) ≤ u := le_trans (by exact_mod_cast (show 1 ≤ m by omega)) hu
    exact Set.indicator_of_mem hu1 _
  unfold kernelChargeTail
  rw [integral_const_mul, integral_indicator measurableSet_Ici, hbase,
    factorialCriticalPatternHarmonicMass_eq_common_tail S b hm]
  field_simp [hmR.ne']

/-- The physical kernel is integrable against every actual finite pattern density. -/
theorem integrable_factorialCriticalPrimeKernelDensity_mul_patternDensity
    (S : Finset ℕ) (b : ℕ → ℝ) :
    Integrable (fun u : ℝ => factorialCriticalPrimeKernelDensity u *
      factorialCriticalPatternDensity S b u) := by
  obtain ⟨hi, hs⟩ := kernel_charge_tail_integrability S b
  exact (HTGeometry.integrable_tsum_of_summable_integral_norm hi hs).congr
    (Filter.Eventually.of_forall (kernel_charge_tail_sum S b))

/-- The native physical kernel has finite absolute mass on the real line. -/
theorem integrable_factorialCriticalPrimeKernelDensity :
    Integrable factorialCriticalPrimeKernelDensity := by
  simpa [factorialCriticalPatternDensity] using
    integrable_factorialCriticalPrimeKernelDensity_mul_patternDensity {0} (fun _ => 1)

/-- The complete limiting prime form is the integral of one native physical kernel. -/
theorem factorialCriticalTranslatedPrimeLimit_eq_kernel_integral
    (S : Finset ℕ) (b : ℕ → ℝ) :
    factorialCriticalTranslatedPrimeLimit S b = (4 / Real.pi^4) *
      ∫ u : ℝ, factorialCriticalPrimeKernelDensity u * factorialCriticalPatternDensity S b u := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_harmonic_diagonal]
  congr 1
  obtain ⟨hi, hs⟩ := kernel_charge_tail_integrability S b
  calc
    (∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m *
        factorialCriticalPatternHarmonicMass S b m / (m : ℝ)^4) =
        ∑' m : ℕ, ∫ u : ℝ, kernelChargeTail S b m u :=
      tsum_congr (fun m => (kernel_charge_tail_integral S b m).symm)
    _ = ∫ u : ℝ, ∑' m : ℕ, kernelChargeTail S b m u :=
      MeasureTheory.integral_tsum_of_summable_integral_norm hi hs
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (kernel_charge_tail_sum S b))

/-- The existing real L1 periodization applied to the native physical prime kernel. -/
def factorialCriticalPrimePeriodizedKernel (t : ℝ) : ℝ :=
  HTGeometry.realL1Periodization factorialCriticalPrimeKernelDensity t

/-- The native periodized kernel has period one, with its L1 endpoint convention. -/
theorem factorialCriticalPrimePeriodizedKernel_periodic :
    Function.Periodic factorialCriticalPrimePeriodizedKernel 1 :=
  HTGeometry.realL1Periodization_periodic _

/-- The periodized native kernel is integrable on a unit cell. -/
theorem integrableOn_factorialCriticalPrimePeriodizedKernel :
    IntegrableOn factorialCriticalPrimePeriodizedKernel (Ioc (0 : ℝ) 1) :=
  HTGeometry.integrableOn_Ioc_realL1Periodization integrable_factorialCriticalPrimeKernelDensity

private theorem prime_kernel_periodization_mul_pattern
    (S : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    HTGeometry.realL1Periodization (fun u => factorialCriticalPrimeKernelDensity u *
      factorialCriticalPatternDensity S b u) t =
      factorialCriticalPrimePeriodizedKernel t * factorialCriticalPatternDensity S b t := by
  have hQ (k : ℤ) : factorialCriticalPatternDensity S b (t + k) =
      factorialCriticalPatternDensity S b t := by
    simpa only [mul_one] using (factorialCriticalPatternDensity_periodic S b).int_mul k t
  change (∑' k : ℤ, factorialCriticalPrimeKernelDensity (t + k) *
    factorialCriticalPatternDensity S b (t + k)) =
    (∑' k : ℤ, factorialCriticalPrimeKernelDensity (t + k)) * factorialCriticalPatternDensity S b t
  simp_rw [hQ]
  exact tsum_mul_right

private theorem real_periodization_zero_mode {f : ℝ → ℝ} (hf : Integrable f) :
    (∫ t in Ioc (0 : ℝ) 1, HTGeometry.realL1Periodization f t) = ∫ u : ℝ, f u := by
  have h := HTGeometry.integral_unit_l1Periodization_mul_fourier_eq hf.ofReal (0 : ℤ)
  apply Complex.ofReal_injective
  simpa [Real.fourier_eq, ← HTGeometry.ofReal_realL1Periodization, integral_complex_ofReal] using h

/-- The complete limiting prime form is the unit-cell pairing with its native periodization. -/
theorem factorialCriticalTranslatedPrimeLimit_eq_periodized_integral
    (S : Finset ℕ) (b : ℕ → ℝ) :
    factorialCriticalTranslatedPrimeLimit S b = (4 / Real.pi^4) *
      ∫ t in Ioc (0 : ℝ) 1, factorialCriticalPrimePeriodizedKernel t *
        factorialCriticalPatternDensity S b t := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_kernel_integral,
    ← real_periodization_zero_mode (integrable_factorialCriticalPrimeKernelDensity_mul_patternDensity S b)]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => prime_kernel_periodization_mul_pattern S b t)

/-- Reflection symmetrization is the kernel seen by real finite coefficient patterns. -/
def factorialCriticalPrimeRealKernel (t : ℝ) : ℝ :=
  (factorialCriticalPrimePeriodizedKernel t + factorialCriticalPrimePeriodizedKernel (1 - t)) / 2

/-- The real-pattern kernel is exactly symmetric on the unit cell. -/
theorem factorialCriticalPrimeRealKernel_reflection (t : ℝ) :
    factorialCriticalPrimeRealKernel (1 - t) = factorialCriticalPrimeRealKernel t := by
  unfold factorialCriticalPrimeRealKernel
  rw [show (1 : ℝ) - (1 - t) = t by ring]
  ring

/-- Symmetrizing the periodized kernel preserves every actual finite real-pattern pairing. -/
theorem factorialCriticalTranslatedPrimeLimit_eq_real_kernel_integral
    (S : Finset ℕ) (b : ℕ → ℝ) :
    factorialCriticalTranslatedPrimeLimit S b = (4 / Real.pi^4) *
      ∫ t in Ioc (0 : ℝ) 1, factorialCriticalPrimeRealKernel t *
        factorialCriticalPatternDensity S b t := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_periodized_integral]
  congr 1
  let G : ℝ → ℝ := fun t => factorialCriticalPrimePeriodizedKernel t *
    factorialCriticalPatternDensity S b t
  have hG : IntervalIntegrable G volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    have h := HTGeometry.integrableOn_Ioc_realL1Periodization
      (integrable_factorialCriticalPrimeKernelDensity_mul_patternDensity S b)
    exact h.congr (Filter.Eventually.of_forall (prime_kernel_periodization_mul_pattern S b))
  have hGr : IntervalIntegrable (fun t : ℝ => G (1 - t)) volume 0 1 := by
    simpa only [sub_zero, sub_self] using (hG.comp_sub_left 1).symm
  have hri : (∫ t in (0 : ℝ)..1, G (1 - t)) = ∫ t in (0 : ℝ)..1, G t := by
    simpa only [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left G (1 : ℝ) (a := 0) (b := 1))
  rw [← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le zero_le_one]
  change (∫ t in (0 : ℝ)..1, G t) = _
  symm
  calc
    (∫ t in (0 : ℝ)..1, factorialCriticalPrimeRealKernel t * factorialCriticalPatternDensity S b t) =
        ∫ t in (0 : ℝ)..1, (1 / 2 : ℝ) * (G t + G (1 - t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only [factorialCriticalPrimeRealKernel, G]
      rw [factorialCriticalPatternDensity_reflection]
      ring
    _ = (1 / 2 : ℝ) * ((∫ t in (0 : ℝ)..1, G t) + (∫ t in (0 : ℝ)..1, G (1 - t))) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hG hGr]
    _ = ∫ t in (0 : ℝ)..1, G t := by rw [hri]; ring

end GaloisForLFunctions.ArithmeticPositivityTheory
