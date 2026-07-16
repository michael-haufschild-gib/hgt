import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.Real.Irrational

/-!
# Incommensurate phase clocks remove global time ambiguity

A phase reporter at rate `a` observes

`t |-> exp(i * a * t)`.

One reporter is periodic and therefore cannot identify an unrestricted real clock coordinate.
Two reporters at rates `a,b` are different: if `a != 0` and `b/a` is irrational, equality of both
phases forces equality of the underlying real clock values.  Thus the paired reporter is globally
injective even though each component is noninjective.

This is a static observability theorem.  It applies to multi-transition quantum clocks,
interferometric phase estimation, oscillatory cosmological standard-clock signals, multi-band
gravitational-wave clock readouts, and any HTGeometry clock whose value is observed only through
unit phases.  No temporal evolution equation is assumed.
-/

namespace HTGeometry

noncomputable section

/-- Unit phase reported by a real clock at one real frequency. -/
def phaseClockValue (rate time : ℝ) : ℂ :=
  Complex.exp (((rate * time : ℝ) : ℂ) * Complex.I)

/-- Pair of phase reporters observing the same real clock value. -/
def phaseClockPair (rate₁ rate₂ time : ℝ) : ℂ × ℂ :=
  (phaseClockValue rate₁ time, phaseClockValue rate₂ time)

/-- Every single phase-clock report has unit norm. -/
theorem norm_phaseClockValue (rate time : ℝ) :
    ‖phaseClockValue rate time‖ = 1 := by
  rw [phaseClockValue, Complex.norm_exp]
  simp

/-- A nonzero single-frequency reporter repeats after its usual period. -/
theorem phaseClockValue_add_period {rate : ℝ} (hrate : rate ≠ 0) (time : ℝ) :
    phaseClockValue rate (time + 2 * Real.pi / rate) =
      phaseClockValue rate time := by
  rw [phaseClockValue, phaseClockValue]
  have hreal : rate * (time + 2 * Real.pi / rate) =
      rate * time + 2 * Real.pi := by
    field_simp
  have harg :
      (((rate * (time + 2 * Real.pi / rate) : ℝ) : ℂ) * Complex.I) =
        (((rate * time : ℝ) : ℂ) * Complex.I) + 2 * (Real.pi : ℂ) * Complex.I := by
    rw [hreal]
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **Single-phase no-go.**  Every nonzero phase frequency is globally noninjective on real clock
time. -/
theorem not_injective_phaseClockValue {rate : ℝ} (hrate : rate ≠ 0) :
    ¬ Function.Injective (phaseClockValue rate) := by
  intro hinjective
  have heq := phaseClockValue_add_period hrate 0
  have htime := hinjective heq
  have hperiod : 2 * Real.pi / rate ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hrate
  exact hperiod (by simpa using htime)

/-- An integral number of phase turns is observationally indistinguishable from zero. -/
theorem phaseClockValue_eq_zero_of_rate_mul_time_eq_int_two_pi
    (rate time : ℝ) (n : ℤ)
    (hturn : rate * time = (n : ℝ) * (2 * Real.pi)) :
    phaseClockValue rate time = phaseClockValue rate 0 := by
  rw [phaseClockValue, phaseClockValue]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨n, ?_⟩
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, zero_add]
  rw [hturn]
  push_cast
  ring

/-- A rational rate ratio gives the phase pair a nonzero common period. -/
theorem not_injective_phaseClockPair_of_rateRatio_eq_int_div
    {rate₁ rate₂ : ℝ} (hrate₁ : rate₁ ≠ 0)
    (m n : ℤ) (hn : n ≠ 0)
    (hratio : rate₂ / rate₁ = (m : ℝ) / (n : ℝ)) :
    ¬ Function.Injective (phaseClockPair rate₁ rate₂) := by
  let period : ℝ := (n : ℝ) * (2 * Real.pi) / rate₁
  have hnReal : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hperiod : period ≠ 0 := by
    exact div_ne_zero
      (mul_ne_zero hnReal (mul_ne_zero (by norm_num) Real.pi_ne_zero)) hrate₁
  have hrate₁Turn : rate₁ * period = (n : ℝ) * (2 * Real.pi) := by
    dsimp only [period]
    field_simp
  have hcross : rate₂ * (n : ℝ) = rate₁ * (m : ℝ) := by
    field_simp [hrate₁, hnReal] at hratio
    nlinarith [hratio]
  have hrate₂Turn : rate₂ * period = (m : ℝ) * (2 * Real.pi) := by
    dsimp only [period]
    field_simp
    nlinarith [hcross]
  intro hinjective
  have hpair : phaseClockPair rate₁ rate₂ period =
      phaseClockPair rate₁ rate₂ 0 := by
    apply Prod.ext
    · exact phaseClockValue_eq_zero_of_rate_mul_time_eq_int_two_pi
        rate₁ period n hrate₁Turn
    · exact phaseClockValue_eq_zero_of_rate_mul_time_eq_int_two_pi
        rate₂ period m hrate₂Turn
  exact hperiod (hinjective hpair)

/-- **Incommensurate two-phase clock theorem.**  If the rate ratio is irrational, the paired
phase reporter recovers unrestricted real clock time exactly. -/
theorem phaseClockPair_injective {rate₁ rate₂ : ℝ}
    (hrate₁ : rate₁ ≠ 0) (hirrational : Irrational (rate₂ / rate₁)) :
    Function.Injective (phaseClockPair rate₁ rate₂) := by
  intro time₁ time₂ hpair
  have h₁ : phaseClockValue rate₁ time₁ = phaseClockValue rate₁ time₂ :=
    congrArg Prod.fst hpair
  have h₂ : phaseClockValue rate₂ time₁ = phaseClockValue rate₂ time₂ :=
    congrArg Prod.snd hpair
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h₁
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h₂
  have hrate₁Period :
      rate₁ * (time₁ - time₂) = (n : ℝ) * (2 * Real.pi) := by
    have hc : ((rate₁ * (time₁ - time₂) : ℝ) : ℂ) * Complex.I =
        ((n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      calc
        ((rate₁ * (time₁ - time₂) : ℝ) : ℂ) * Complex.I =
            ((rate₁ * time₁ : ℝ) : ℂ) * Complex.I -
              ((rate₁ * time₂ : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        _ = ((n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
          rw [hn]
          ring
    have hc' := mul_right_cancel₀ Complex.I_ne_zero hc
    exact_mod_cast hc'
  have hrate₂Period :
      rate₂ * (time₁ - time₂) = (m : ℝ) * (2 * Real.pi) := by
    have hc : ((rate₂ * (time₁ - time₂) : ℝ) : ℂ) * Complex.I =
        ((m : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      calc
        ((rate₂ * (time₁ - time₂) : ℝ) : ℂ) * Complex.I =
            ((rate₂ * time₁ : ℝ) : ℂ) * Complex.I -
              ((rate₂ * time₂ : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        _ = ((m : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
          rw [hm]
          ring
    have hc' := mul_right_cancel₀ Complex.I_ne_zero hc
    exact_mod_cast hc'
  by_contra htime
  have hnzero : n ≠ 0 := by
    intro hnzero
    rw [hnzero, Int.cast_zero, zero_mul] at hrate₁Period
    have hsub : time₁ - time₂ = 0 :=
      (mul_eq_zero.mp hrate₁Period).resolve_left hrate₁
    exact htime (sub_eq_zero.mp hsub)
  have hratio : rate₂ / rate₁ = (m : ℝ) / (n : ℝ) := by
    have htwoPi : 2 * Real.pi ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    have hcross : rate₂ * (n : ℝ) = rate₁ * (m : ℝ) := by
      apply mul_right_cancel₀ htwoPi
      calc
        rate₂ * (n : ℝ) * (2 * Real.pi) =
            rate₂ * (rate₁ * (time₁ - time₂)) := by
          rw [hrate₁Period]
          ring
        _ = rate₁ * (rate₂ * (time₁ - time₂)) := by ring
        _ = rate₁ * (m : ℝ) * (2 * Real.pi) := by
          rw [hrate₂Period]
          ring
    field_simp
    nlinarith [hcross]
  exact ((irrational_iff_ne_rational (rate₂ / rate₁)).mp
    hirrational m n hnzero) hratio

/-- **Exact rate classification.**  For a nonzero first rate, a two-phase clock is globally
injective exactly when the rate ratio is irrational. -/
theorem phaseClockPair_injective_iff_irrational {rate₁ rate₂ : ℝ}
    (hrate₁ : rate₁ ≠ 0) :
    Function.Injective (phaseClockPair rate₁ rate₂) ↔
      Irrational (rate₂ / rate₁) := by
  rw [irrational_iff_ne_rational]
  constructor
  · intro hinjective m n hn hratio
    exact (not_injective_phaseClockPair_of_rateRatio_eq_int_div
      hrate₁ m n hn hratio) hinjective
  · intro hrat
    exact phaseClockPair_injective hrate₁
      ((irrational_iff_ne_rational (rate₂ / rate₁)).2 hrat)

/-- Equality of an incommensurate phase pair is exactly equality of the underlying clock value. -/
theorem phaseClockPair_eq_iff {rate₁ rate₂ : ℝ}
    (hrate₁ : rate₁ ≠ 0) (hirrational : Irrational (rate₂ / rate₁))
    (time₁ time₂ : ℝ) :
    phaseClockPair rate₁ rate₂ time₁ = phaseClockPair rate₁ rate₂ time₂ ↔
      time₁ = time₂ := by
  constructor
  · intro hpair
    exact (phaseClockPair_injective hrate₁ hirrational) hpair
  · rintro rfl
    rfl

/-- Composing an incommensurate phase pair with any clock coordinate preserves and reflects
injectivity. -/
theorem phaseClockPair_comp_injective_iff
    {X : Type*} {rate₁ rate₂ : ℝ}
    (hrate₁ : rate₁ ≠ 0) (hirrational : Irrational (rate₂ / rate₁))
    (clock : X → ℝ) :
    Function.Injective (fun x => phaseClockPair rate₁ rate₂ (clock x)) ↔
      Function.Injective clock := by
  constructor
  · intro hphase x y hclock
    apply hphase
    exact congrArg (phaseClockPair rate₁ rate₂) hclock
  · intro hclock x y hphase
    apply hclock
    exact (phaseClockPair_injective hrate₁ hirrational) hphase

/-- For any possibly noninjective clock coordinate, the fused phase reporters lose exactly the
same equivalence relation and no additional information. -/
theorem phaseClockPair_comp_eq_iff
    {X : Type*} {rate₁ rate₂ : ℝ}
    (hrate₁ : rate₁ ≠ 0) (hirrational : Irrational (rate₂ / rate₁))
    (clock : X → ℝ) (x y : X) :
    phaseClockPair rate₁ rate₂ (clock x) = phaseClockPair rate₁ rate₂ (clock y) ↔
      clock x = clock y :=
  phaseClockPair_eq_iff hrate₁ hirrational (clock x) (clock y)

end

end HTGeometry
