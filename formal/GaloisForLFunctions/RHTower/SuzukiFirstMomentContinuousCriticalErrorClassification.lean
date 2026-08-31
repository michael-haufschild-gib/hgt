import GaloisForLFunctions.RHTower.SuzukiFirstMomentCriticalErrorClassification
import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainder

/-!
# Continuous critical-error classification for the Suzuki first-moment route

The discrete square-root Chebyshev remainder condition is exactly uniform boundedness of the
critical-normalized Chebyshev error on the entire late logarithmic ray, not only at integer-log
samples.  The elementary floor cell contributes at most one after critical normalization.

Consequently that condition bounds the error paired with every integrable complex detector
supported on the late ray by the detector's `L¹` norm.  This closes continuous interpolation and
the source-bound-to-detector estimate in the CCM-FU hostile no-go chain; the remaining burden is
the compact-test explicit-formula identification with the amplified Xi divisor packet.
-/

open Set MeasureTheory

namespace RHTower

noncomputable section

/-- Uniform boundedness of the critical-normalized Chebyshev error on the full late logarithmic
ray. -/
def CriticalMellinNormalizedChebyshevErrorEventuallyBounded : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, Real.log 3 ≤ h →
    |criticalMellinNormalizedChebyshevError h| ≤ C

/-- A square-root bound for the discrete Chebyshev remainder controls every point of the late
continuous logarithmic ray. -/
theorem criticalMellinNormalizedChebyshevErrorEventuallyBounded_of_psiRemainderSquareRootBounded
    (hpsi : PsiRemainderSquareRootBounded) :
    CriticalMellinNormalizedChebyshevErrorEventuallyBounded := by
  obtain ⟨C, hC0, hR⟩ := hpsi
  refine ⟨C + 1, add_nonneg hC0 zero_le_one, ?_⟩
  intro h hh
  let N : ℕ := ⌊Real.exp h⌋₊
  have hh0 : 0 ≤ h := by
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  have hexp3 : (3 : ℝ) ≤ Real.exp h := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.mpr hh
  have hN3 : 3 ≤ N := by
    exact (Nat.le_floor_iff (Real.exp_pos h).le).mpr hexp3
  have hRN : |psiRemainder N| ≤ C * Real.sqrt (N : ℝ) := hR N hN3
  have hNexp : (N : ℝ) ≤ Real.exp h := Nat.floor_le (Real.exp_pos h).le
  have hsqrt : Real.sqrt (N : ℝ) ≤ Real.exp (h / 2) := by
    calc
      Real.sqrt (N : ℝ) ≤ Real.sqrt (Real.exp h) := Real.sqrt_le_sqrt hNexp
      _ = Real.exp (h / 2) := by rw [← Real.exp_half]
  have hscale : Real.exp (-h / 2) * Real.sqrt (N : ℝ) ≤ 1 := by
    calc
      Real.exp (-h / 2) * Real.sqrt (N : ℝ) ≤
          Real.exp (-h / 2) * Real.exp (h / 2) :=
        mul_le_mul_of_nonneg_left hsqrt (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
  have hexpsmall : Real.exp (-h / 2) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  rw [criticalMellinNormalizedChebyshevError_eq_discrete_add_floor]
  calc
    |Real.exp (-h / 2) * psiRemainder N +
        Real.exp (-h / 2) * ((N : ℝ) - Real.exp h)| ≤
        |Real.exp (-h / 2) * psiRemainder N| +
          |Real.exp (-h / 2) * ((N : ℝ) - Real.exp h)| := abs_add_le _ _
    _ = Real.exp (-h / 2) * |psiRemainder N| +
        Real.exp (-h / 2) * |(N : ℝ) - Real.exp h| := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-h / 2) * (C * Real.sqrt (N : ℝ)) +
        Real.exp (-h / 2) * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hRN (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_left (abs_natFloor_exp_sub_le_one h) (Real.exp_pos _).le)
    _ = C * (Real.exp (-h / 2) * Real.sqrt (N : ℝ)) +
        Real.exp (-h / 2) := by ring
    _ ≤ C * 1 + 1 := add_le_add (mul_le_mul_of_nonneg_left hscale hC0) hexpsmall
    _ = C + 1 := by ring

/-- Exact continuous classification: the discrete square-root remainder bound is neither weakened
nor strengthened by passing from integer-log samples to the whole late ray. -/
theorem psiRemainderSquareRootBounded_iff_criticalMellinNormalizedErrorEventuallyBounded :
    PsiRemainderSquareRootBounded ↔
      CriticalMellinNormalizedChebyshevErrorEventuallyBounded := by
  constructor
  · exact
      criticalMellinNormalizedChebyshevErrorEventuallyBounded_of_psiRemainderSquareRootBounded
  · rintro ⟨C, hC0, herror⟩
    apply normalizedErrorLogNatBounded_iff_psiRemainderSquareRootBounded.mp
    refine ⟨C, hC0, ?_⟩
    intro M hM
    apply herror
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hM)

/-- Uniform `L¹` detector boundedness for the late normalized Chebyshev error. -/
def CriticalMellinNormalizedChebyshevErrorLateL1DetectorBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℝ → ℂ, Integrable K →
    (∀ x : ℝ, x < Real.log 3 → K x = 0) →
      ‖∫ x : ℝ, (criticalMellinNormalizedChebyshevError x : ℂ) * K x‖ ≤
        C * ∫ x : ℝ, ‖K x‖

/-- The square-root Chebyshev condition supplies one operator-norm bound for every integrable
detector supported after `log 3`. -/
theorem criticalMellinNormalizedChebyshevErrorLateL1DetectorBound_of_psiRemainderSquareRootBounded
    (hpsi : PsiRemainderSquareRootBounded) :
    CriticalMellinNormalizedChebyshevErrorLateL1DetectorBound := by
  obtain ⟨C, hC0, herror⟩ :=
    criticalMellinNormalizedChebyshevErrorEventuallyBounded_of_psiRemainderSquareRootBounded hpsi
  refine ⟨C, hC0, ?_⟩
  intro K hK hsupport
  have hmajor : Integrable (fun x : ℝ => C * ‖K x‖) := hK.norm.const_mul C
  have hbound : ∀ᵐ x : ℝ,
      ‖(criticalMellinNormalizedChebyshevError x : ℂ) * K x‖ ≤ C * ‖K x‖ := by
    filter_upwards with x
    by_cases hx : Real.log 3 ≤ x
    · rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (herror x hx) (norm_nonneg _)
    · have hx' : x < Real.log 3 := lt_of_not_ge hx
      rw [hsupport x hx']
      simp
  calc
    ‖∫ x : ℝ, (criticalMellinNormalizedChebyshevError x : ℂ) * K x‖ ≤
        ∫ x : ℝ, C * ‖K x‖ :=
      MeasureTheory.norm_integral_le_of_norm_le hmajor hbound
    _ = C * ∫ x : ℝ, ‖K x‖ := MeasureTheory.integral_const_mul C _

end

end RHTower
