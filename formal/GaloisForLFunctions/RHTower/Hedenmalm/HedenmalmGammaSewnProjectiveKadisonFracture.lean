import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnProjectiveParityLeakageBridge

/-!
# The Route N projective/Kadison fracture dictionary

The positive transverse modular cocycle has one canonical multiplicative-domain defect

`D_t(p) = 1 - p^(-2|t|)`.

This file proves that the signed Route N Krein current, its Kakutani numerator, and the literal
projective Weyl leakage are respectively the oriented linear, normalized quadratic, and
residue-compressed quadratic polarizations of this same defect.  Its normalized logarithm recovers
the complete radial grade exactly.

Consequently these apparently different Route N constraints are reporters of one conserved
duality--adjunction fracture.  Their exact collision does not make the fracture vanish; a source
producer must prove inverse and adjoint transport agree on the landed Xi conormal.
-/

namespace RHTower

noncomputable section

/-- Multiplicative-domain/Kadison defect of the Route N projective marked state. -/
def routeNGammaSewnProjectiveKadisonDefect
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  1 - routeNGammaSewnTransverseModularCocycle t p

/-- The Kadison defect is the complement of the selected marked-amplitude square. -/
theorem routeNGammaSewnProjectiveKadisonDefect_eq_one_sub_rpow
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveKadisonDefect t p =
      1 - (p : ℝ) ^ (-2 * |t|) := by
  rfl

/-- The surviving modular cocycle is exactly one minus the Kadison defect. -/
theorem one_sub_routeNGammaSewnProjectiveKadisonDefect
    (t : ℝ) (p : Nat.Primes) :
    1 - routeNGammaSewnProjectiveKadisonDefect t p =
      routeNGammaSewnTransverseModularCocycle t p := by
  rw [routeNGammaSewnProjectiveKadisonDefect]
  ring

/-- **Oriented linear fracture law.**  The Route N Krein charge is the Kadison defect divided by
the universal critical channel mass, with orientation supplied by `sign(t)`. -/
theorem routeNGammaSewnProjectiveKadisonDefect_eq_neg_sign_mul_prime_mul_krein
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveKadisonDefect t p =
      -(Real.sign t * (p : ℝ) *
        routeNGammaSewnCriticalHorizonKreinCharge t p) := by
  have h := one_add_sign_mul_prime_mul_routeNKrein_eq_modularCocycle t p
  rw [routeNGammaSewnProjectiveKadisonDefect]
  linarith

/-- One local projective/Kadison record is pure exactly at neutral Route N grade. -/
theorem routeNGammaSewnProjectiveKadisonDefect_eq_zero_iff
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveKadisonDefect t p = 0 ↔ t = 0 := by
  rw [routeNGammaSewnProjectiveKadisonDefect, sub_eq_zero]
  simpa only [eq_comm] using
    routeNGammaSewnTransverseModularCocycle_eq_one_iff t p

/-- The Kadison defect lies in the positive unit interval. -/
theorem routeNGammaSewnProjectiveKadisonDefect_mem_Ico
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveKadisonDefect t p ∈ Set.Ico 0 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hcocycle0 : 0 < routeNGammaSewnTransverseModularCocycle t p :=
    Real.rpow_pos_of_pos (by positivity) _
  have hcocycle1 : routeNGammaSewnTransverseModularCocycle t p ≤ 1 := by
    have hexp : -2 * |t| ≤ 0 := by nlinarith [abs_nonneg t]
    rw [routeNGammaSewnTransverseModularCocycle,
      routeNGammaSewnTransverseModularClockCocycle,
      ← Real.rpow_zero (p : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le hexp
  constructor
  · rw [routeNGammaSewnProjectiveKadisonDefect]
    linarith
  · rw [routeNGammaSewnProjectiveKadisonDefect]
    linarith

/-- **Normalized quadratic fracture law.**  The Route N Kakutani numerator is the square of the
Kadison defect divided by the universal prime mass and the positive half-density seam. -/
theorem primeValuationHellingerGap_neg_abs_eq_projectiveKadisonDefect_sq
    (t : ℝ) (p : Nat.Primes) :
    primeValuationHellingerGap (-|t|) p =
      routeNGammaSewnProjectiveKadisonDefect t p ^ 2 /
        ((p : ℝ) * (1 + (p : ℝ) ^ (-|t|)) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hplus : 1 + (p : ℝ) ^ (-|t|) ≠ 0 := by positivity
  by_cases ht : t = 0
  · subst t
    norm_num [primeValuationHellingerGap,
      routeNGammaSewnProjectiveKadisonDefect,
      routeNGammaSewnTransverseModularCocycle,
      routeNGammaSewnTransverseModularClockCocycle]
  · have hsignSq : Real.sign t ^ 2 = 1 := by
      rcases Real.sign_apply_eq_of_ne_zero t ht with hsign | hsign <;>
        rw [hsign] <;> norm_num
    rw [primeValuationHellingerGap_neg_abs_eq_routeNKreinPolarization,
      routeNGammaSewnProjectiveKadisonDefect_eq_neg_sign_mul_prime_mul_krein]
    field_simp [hp0.ne', hplus]
    rw [hsignSq, mul_one]

/-- **Residue-compressed quadratic fracture law.**  Literal projective Weyl leakage is the square
of the same Kadison defect with its complete normalization displayed. -/
theorem routeNGammaSewnProjectiveLeakage_eq_projectiveKadisonDefect_sq
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveLeakage t p =
      routeNGammaSewnProjectiveKadisonDefect t p ^ 2 *
        ((p : ℝ) - 1) /
        ((p : ℝ) * (1 + (p : ℝ) ^ (-|t|)) ^ 2 *
          ((p : ℝ) + ((p : ℝ) ^ (-|t|)) ^ 2)) := by
  rw [routeNGammaSewnProjectiveLeakage_eq_hGap_mul,
    primeValuationHellingerGap_neg_abs_eq_projectiveKadisonDefect_sq]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hplus : 1 + (p : ℝ) ^ (-|t|) ≠ 0 := by positivity
  have hden : (p : ℝ) + ((p : ℝ) ^ (-|t|)) ^ 2 ≠ 0 := by positivity
  field_simp [hp0.ne', hplus, hden]

/-- **Exact logarithmic record density.**  The normalized logarithm of the surviving modular
mass recovers the complete absolute Route N grade. -/
theorem log_one_sub_routeNGammaSewnProjectiveKadisonDefect_div
    (t : ℝ) (p : Nat.Primes) :
    Real.log (1 - routeNGammaSewnProjectiveKadisonDefect t p) /
        (2 * Real.log (p : ℝ)) = -|t| := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast p.2.one_lt))
  rw [one_sub_routeNGammaSewnProjectiveKadisonDefect,
    routeNGammaSewnTransverseModularCocycle,
    routeNGammaSewnTransverseModularClockCocycle,
    Real.log_rpow hp0]
  field_simp [hlog]

end

end RHTower
