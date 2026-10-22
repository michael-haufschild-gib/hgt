import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnSquarefreeParityLocalization
import GaloisForLFunctions.RHTower.ProjectivePrimeWeylModel

/-!
# Projective realization of the Gamma-sewn Route N parity wall

The Gamma-sewn radial grade selects a canonical marked weight on the residue projective clock,

`z_t(p) = -|t| log p`.

At this weight the marked-to-bulk odds of the projective natural-cone vector are exactly the
twisted Route N squarefree-parity odds `p^(-1-2|t|)`.  Neutral grade is therefore the uniform
projective source line fixed by residue Weyl inversion.

For a foreign producer/reporter polarization, the exact projective compression leakage is the
Route N Kakutani numerator times the bounded factor

`(p - 1) / (p + p^(-2|t|))`.

That factor lies between `1/3` and `1`.  Consequently projective leakage is summable over all
ordinary primes exactly at neutral grade.  This identifies the Route N sector wall with a literal
residue-clock Weyl leakage, while also showing that scalar Hilbert compression deletes every
off-neutral grade rather than proving its absence.
-/

namespace RHTower

noncomputable section

/-- Canonical projective marked weight selected by the Gamma-sewn Route N radial grade. -/
def routeNGammaSewnProjectiveWeight (t : ℝ) (p : Nat.Primes) : ℝ :=
  -|t| * Real.log (p : ℝ)

/-- The marked amplitude of the selected projective natural-cone state is the square root of the
Route N transverse modular cocycle. -/
theorem exp_routeNGammaSewnProjectiveWeight
    (t : ℝ) (p : Nat.Primes) :
    Real.exp (routeNGammaSewnProjectiveWeight t p) = (p : ℝ) ^ (-|t|) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnProjectiveWeight, Real.rpow_def_of_pos hp0]
  congr 1
  ring

/-- Squaring the projective marked amplitude recovers the complete transverse modular cocycle. -/
theorem exp_two_mul_routeNGammaSewnProjectiveWeight
    (t : ℝ) (p : Nat.Primes) :
    Real.exp (2 * routeNGammaSewnProjectiveWeight t p) =
      routeNGammaSewnTransverseModularCocycle t p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnProjectiveWeight,
    routeNGammaSewnTransverseModularCocycle,
    routeNGammaSewnTransverseModularClockCocycle,
    Real.rpow_def_of_pos hp0]
  congr 1
  ring

/-- Marked-to-bulk odds of a projective natural-cone state. -/
def projNaturalMarkedOdds (X : Type*) [Fintype X] (z : ℝ) : ℝ :=
  Real.exp (2 * z) / projDeg X

/-- Route N projective marked odds on `P¹(F_p)`. -/
def routeNGammaSewnProjectiveMarkedOdds
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  projNaturalMarkedOdds (Option (ZMod (p : ℕ)))
    (routeNGammaSewnProjectiveWeight t p)

/-- **Projective/parity collision.**  The selected projective marked odds are exactly the
Gamma-sewn twisted squarefree-parity odds. -/
theorem routeNGammaSewnProjectiveMarkedOdds_eq_twistedSquarefreeParityOdds
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveMarkedOdds t p =
      routeNGammaSewnTwistedSquarefreeParityOdds t p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnProjectiveMarkedOdds, projNaturalMarkedOdds,
    exp_two_mul_routeNGammaSewnProjectiveWeight,
    routeNGammaSewnTransverseModularCocycle,
    routeNGammaSewnTransverseModularClockCocycle,
    projDeg_optionZMod,
    routeNGammaSewnTwistedSquarefreeParityOdds_eq,
    routeNGammaSewnTwistedCriticalChannelMass,
    div_eq_mul_inv, ← Real.rpow_neg_one,
    ← Real.rpow_add hp0]
  congr 1
  ring

/-- Neutral Route N grade is the projective uniform source line. -/
theorem routeNGammaSewnProjectiveNatural_zero
    (p : Nat.Primes) (a : Option (ZMod (p : ℕ))) :
    projNatural a (routeNGammaSewnProjectiveWeight 0 p) =
      projUniform (Option (ZMod (p : ℕ))) := by
  simp [routeNGammaSewnProjectiveWeight, projNatural_zero]

/-- Residue Weyl inversion fixes the neutral Route N projective state. -/
theorem routeNGammaSewnProjectiveNatural_zero_weylFixed
    (p : Nat.Primes) :
    projPermute (weylInversion (p : ℕ))
        (projNatural (none : Option (ZMod (p : ℕ)))
          (routeNGammaSewnProjectiveWeight 0 p)) =
      projNatural (none : Option (ZMod (p : ℕ)))
        (routeNGammaSewnProjectiveWeight 0 p) := by
  simp only [routeNGammaSewnProjectiveWeight, abs_zero, neg_zero, zero_mul,
    projNatural_zero, projPermute_projUniform]

/-- Projective producer/reporter compression leakage at the Route N selected weight. -/
def routeNGammaSewnProjectiveLeakage
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  projLeakageValue (Option (ZMod (p : ℕ)))
    (routeNGammaSewnProjectiveWeight t p)

/-- Exact projective Weyl leakage of the Route N selected natural-cone state. -/
theorem routeNGammaSewnProjectiveWeylLeakage
    (t : ℝ) (p : Nat.Primes) :
    ‖projNatural (some (0 : ZMod (p : ℕ)))
          (routeNGammaSewnProjectiveWeight t p) -
        projCompress (none : Option (ZMod (p : ℕ)))
          (projNatural (some (0 : ZMod (p : ℕ)))
            (routeNGammaSewnProjectiveWeight t p))‖ ^ 2 =
      routeNGammaSewnProjectiveLeakage t p := by
  exact projWeylLeakage (two_le_card_optionZMod (p : ℕ)) (by simp) _

/-- **Exact leakage polarization.**  Projective leakage is the Route N Kakutani numerator times a
bounded residue-clock factor. -/
theorem routeNGammaSewnProjectiveLeakage_eq_hGap_mul
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveLeakage t p =
      primeValuationHellingerGap (-|t|) p *
        (((p : ℝ) - 1) /
          ((p : ℝ) + ((p : ℝ) ^ (-|t|)) ^ 2)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hden : 0 < (p : ℝ) + ((p : ℝ) ^ (-|t|)) ^ 2 := by positivity
  have htwisted :
      routeNGammaSewnTwistedCriticalChannelAmplitude t p =
        routeNGammaSewnUniversalCriticalChannelAmplitude p *
          (p : ℝ) ^ (-|t|) :=
    routeNGammaSewnTwistedCriticalChannelAmplitude_eq_universal_mul_sqrtCocycle t p
  rw [routeNGammaSewnProjectiveLeakage, projLeakageValue,
    projDeg_optionZMod, exp_routeNGammaSewnProjectiveWeight,
    primeValuationHellingerGap_neg_abs_eq_routeNCriticalAmplitudeGap,
    htwisted]
  rw [show (routeNGammaSewnUniversalCriticalChannelAmplitude p -
          routeNGammaSewnUniversalCriticalChannelAmplitude p * (p : ℝ) ^ (-|t|)) ^ 2 =
        routeNGammaSewnUniversalCriticalChannelAmplitude p ^ 2 *
          (1 - (p : ℝ) ^ (-|t|)) ^ 2 by ring,
    routeNGammaSewnUniversalCriticalChannelAmplitude_sq,
    routeNGammaSewnUniversalCriticalChannelMass,
    Real.rpow_neg_one]
  simp only [div_eq_mul_inv]
  ring

/-- The residue factor comparing projective leakage to the Kakutani numerator is at least `1/3`. -/
theorem one_third_le_routeNGammaSewnProjectiveLeakageFactor
    (t : ℝ) (p : Nat.Primes) :
    (1 / 3 : ℝ) ≤
      ((p : ℝ) - 1) / ((p : ℝ) + ((p : ℝ) ^ (-|t|)) ^ 2) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  have hp1 : (1 : ℝ) ≤ p := le_trans (by norm_num) hp2
  have hr0 : 0 ≤ (p : ℝ) ^ (-|t|) :=
    (Real.rpow_pos_of_pos (by positivity) _).le
  have hr1 : (p : ℝ) ^ (-|t|) ≤ 1 := by
    rw [← Real.rpow_zero (p : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (neg_nonpos.mpr (abs_nonneg t))
  have hrsq : ((p : ℝ) ^ (-|t|)) ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      (sq_le_sq₀ hr0 (by norm_num : (0 : ℝ) ≤ 1)).2 hr1
  have hden : 0 < (p : ℝ) + ((p : ℝ) ^ (-|t|)) ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  nlinarith

/-- The residue factor comparing projective leakage to the Kakutani numerator is at most `1`. -/
theorem routeNGammaSewnProjectiveLeakageFactor_le_one
    (t : ℝ) (p : Nat.Primes) :
    ((p : ℝ) - 1) / ((p : ℝ) + ((p : ℝ) ^ (-|t|)) ^ 2) ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hden : 0 < (p : ℝ) + ((p : ℝ) ^ (-|t|)) ^ 2 := by positivity
  rw [div_le_one hden]
  nlinarith [sq_nonneg ((p : ℝ) ^ (-|t|))]

/-- Projective leakage is bounded above by the Route N Kakutani numerator. -/
theorem routeNGammaSewnProjectiveLeakage_le_primeValuationHellingerGap_neg_abs
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveLeakage t p ≤
      primeValuationHellingerGap (-|t|) p := by
  have hgap : 0 ≤ primeValuationHellingerGap (-|t|) p := by
    rw [primeValuationHellingerGap]
    positivity
  rw [routeNGammaSewnProjectiveLeakage_eq_hGap_mul]
  exact mul_le_of_le_one_right hgap
    (routeNGammaSewnProjectiveLeakageFactor_le_one t p)

/-- Projective leakage controls the full Route N Kakutani numerator with a universal constant. -/
theorem primeValuationHellingerGap_neg_abs_le_three_mul_projectiveLeakage
    (t : ℝ) (p : Nat.Primes) :
    primeValuationHellingerGap (-|t|) p ≤
      3 * routeNGammaSewnProjectiveLeakage t p := by
  have hgap : 0 ≤ primeValuationHellingerGap (-|t|) p := by
    rw [primeValuationHellingerGap]
    positivity
  have hfactor := one_third_le_routeNGammaSewnProjectiveLeakageFactor t p
  have hmul := mul_le_mul_of_nonneg_left hfactor hgap
  rw [routeNGammaSewnProjectiveLeakage_eq_hGap_mul]
  nlinarith

/-- A single residue clock has zero Route N projective leakage exactly at neutral grade. -/
theorem routeNGammaSewnProjectiveLeakage_eq_zero_iff
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveLeakage t p = 0 ↔ t = 0 := by
  constructor
  · intro hzero
    by_contra ht
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.2.one_lt)
    have habs : 0 < |t| := abs_pos.mpr ht
    have hweight : routeNGammaSewnProjectiveWeight t p ≠ 0 := by
      rw [routeNGammaSewnProjectiveWeight]
      nlinarith
    have hpos := projLeakageValue_pos
      (three_le_card_optionZMod (p : ℕ)) hweight
    exact (ne_of_gt hpos) hzero
  · rintro rfl
    simp [routeNGammaSewnProjectiveLeakage,
      routeNGammaSewnProjectiveWeight]

/-- **All-prime projective-sector classifier.**  Route N projective Weyl leakage is summable
exactly at neutral grade. -/
theorem summable_routeNGammaSewnProjectiveLeakage_iff (t : ℝ) :
    Summable (routeNGammaSewnProjectiveLeakage t) ↔ t = 0 := by
  constructor
  · intro hleak
    have hgap : Summable (primeValuationHellingerGap (-|t|)) :=
      Summable.of_nonneg_of_le
        (fun p => by rw [primeValuationHellingerGap]; positivity)
        (primeValuationHellingerGap_neg_abs_le_three_mul_projectiveLeakage t)
        (hleak.mul_left 3)
    have hcenter := (summable_primeValuationHellingerGap_iff (-|t|)).mp hgap
    have habs : |t| = 0 := by linarith
    exact abs_eq_zero.mp habs
  · rintro rfl
    have hzero : routeNGammaSewnProjectiveLeakage 0 =
        fun _p : Nat.Primes => (0 : ℝ) := by
      funext p
      exact (routeNGammaSewnProjectiveLeakage_eq_zero_iff 0 p).2 rfl
    rw [hzero]
    exact summable_zero

end

end RHTower
