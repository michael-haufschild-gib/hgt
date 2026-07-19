import GaloisForLFunctions.RHTower.PrimeClockShaleDiagonal
import GaloisForLFunctions.RHTower.XiPrimeSeamReflectionEnergy
import GaloisForLFunctions.HTGeometry.PositiveSummabilityComparison

/-!
# The exact damping aperture of every reflected prime-log moment

For every logarithmic order `m`, this module classifies the power loss required to place the
FE--Schwarz prime reflection seam in a summable square sector.  The exact threshold is

`|2 * sigma - 1| < theta`.

The result simultaneously subsumes the undamped prime-clock theorem (`m = 0`, `theta = 0`) and
the reciprocal-prime logarithmic seam on the open strip (`m = 2`, `theta = 1`).  Requiring the
estimate for every positive loss is equivalent, on each fibre, to the critical-line equation and,
on all Xi fibres, to RH.  The theorem consumes such estimates; it does not assert that the
Euler--Gamma source supplies them.
-/

namespace RHTower

noncomputable section

/-- The `m`-th logarithmic moment of the power-damped prime-clock reflection energy. -/
def weightedPrimeClockReflectionLogMomentEnergy
    (m : ℕ) (theta sigma : ℝ) (p : Nat.Primes) : ℝ :=
  |Real.log (p : ℝ)| ^ m *
    ((p : ℝ) ^ (-theta) * primeClockReflectionEnergy sigma p)

/-- Exact factorization relative to the lower reflected amplitude.  The identity itself requires
no order hypothesis; the threshold proof below uses it on the lower half-plane. -/
theorem weightedPrimeClockReflectionLogMomentEnergy_eq_factor
    (m : ℕ) (theta sigma : ℝ) (p : Nat.Primes) :
    weightedPrimeClockReflectionLogMomentEnergy m theta sigma p =
      |Real.log (p : ℝ)| ^ m * (p : ℝ) ^ (-(theta + 2 * sigma)) *
        (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hfactor :
      (p : ℝ) ^ (-sigma) - (p : ℝ) ^ (-(1 - sigma)) =
        (p : ℝ) ^ (-sigma) *
          (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) := by
    rw [show -(1 - sigma) = -sigma + -(1 - 2 * sigma) by ring,
      Real.rpow_add hp0]
    ring
  have hsquare : ((p : ℝ) ^ (-sigma)) ^ 2 =
      (p : ℝ) ^ (-2 * sigma) := by
    rw [pow_two, ← Real.rpow_add hp0]
    congr 1
    ring
  have hweight :
      (p : ℝ) ^ (-theta) * (p : ℝ) ^ (-2 * sigma) =
        (p : ℝ) ^ (-(theta + 2 * sigma)) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  rw [weightedPrimeClockReflectionLogMomentEnergy,
    primeClockReflectionEnergy, hfactor, mul_pow, hsquare]
  calc
    |Real.log (p : ℝ)| ^ m *
          ((p : ℝ) ^ (-theta) *
            ((p : ℝ) ^ (-2 * sigma) *
              (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2)) =
        |Real.log (p : ℝ)| ^ m *
          ((p : ℝ) ^ (-theta) * (p : ℝ) ^ (-2 * sigma)) *
            (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 := by ring
    _ = _ := by rw [hweight]

private theorem summable_weightedPrimeClockReflectionLogMomentEnergy_of_lt_half
    (m : ℕ) {theta sigma : ℝ} (hsigma : sigma < 1 / 2)
    (hthreshold : 1 - 2 * sigma < theta) :
    Summable (weightedPrimeClockReflectionLogMomentEnergy m theta sigma) := by
  have hbeta : 1 < theta + 2 * sigma := by linarith
  have hmajor : Summable (fun p : Nat.Primes =>
      |Real.log (p : ℝ)| ^ m * (p : ℝ) ^ (-(theta + 2 * sigma))) := by
    exact (summable_abs_log_natCast_pow_mul_rpow_neg m
      (theta + 2 * sigma) hbeta).comp_injective Subtype.coe_injective
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hmajor
  · exact mul_nonneg (pow_nonneg (abs_nonneg _) m)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
  · have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hdelta : 0 < 1 - 2 * sigma := by linarith
    have hpow : 0 < (p : ℝ) ^ (-(1 - 2 * sigma)) :=
      Real.rpow_pos_of_pos (by positivity) (-(1 - 2 * sigma))
    have hpow_lt : (p : ℝ) ^ (-(1 - 2 * sigma)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hfactorSq :
        (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((p : ℝ) ^ (-(1 - 2 * sigma)))]
    rw [weightedPrimeClockReflectionLogMomentEnergy_eq_factor
      m theta sigma p]
    have hinner :
        (p : ℝ) ^ (-(theta + 2 * sigma)) *
            (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 ≤
          (p : ℝ) ^ (-(theta + 2 * sigma)) :=
      mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _) hfactorSq
    calc
      |Real.log (p : ℝ)| ^ m * (p : ℝ) ^ (-(theta + 2 * sigma)) *
          (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 =
        |Real.log (p : ℝ)| ^ m *
          ((p : ℝ) ^ (-(theta + 2 * sigma)) *
            (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2) := by ring
      _ ≤ |Real.log (p : ℝ)| ^ m *
          (p : ℝ) ^ (-(theta + 2 * sigma)) :=
        mul_le_mul_of_nonneg_left hinner (pow_nonneg (abs_nonneg _) m)

private theorem not_summable_weightedPrimeClockReflectionLogMomentEnergy_of_lt_half
    (m : ℕ) {theta sigma : ℝ} (hsigma : sigma < 1 / 2)
    (hthreshold : theta ≤ 1 - 2 * sigma) :
    ¬ Summable (weightedPrimeClockReflectionLogMomentEnergy m theta sigma) := by
  intro hsum
  let c : ℝ := (Real.log 2) ^ m *
    (1 - (2 : ℝ) ^ (-(1 - 2 * sigma))) ^ 2
  have hdelta : 0 < 1 - 2 * sigma := by linarith
  have hfactor2 : 0 < 1 - (2 : ℝ) ^ (-(1 - 2 * sigma)) := by
    exact sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  have hc : 0 < c := by
    exact mul_pos (pow_pos (Real.log_pos one_lt_two) m) (sq_pos_of_pos hfactor2)
  have hlower : ∀ p : Nat.Primes,
      c * (1 / (p : ℝ)) ≤
        weightedPrimeClockReflectionLogMomentEnergy m theta sigma p := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := one_le_two.trans hp2
    have hp0 : (0 : ℝ) < (p : ℝ) := zero_lt_one.trans_le hp1
    have hlogp : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.prop.one_lt)
    have hlog : Real.log 2 ≤ |Real.log (p : ℝ)| := by
      rw [abs_of_pos hlogp]
      exact Real.log_le_log (by norm_num) hp2
    have hlogPow : (Real.log 2) ^ m ≤ |Real.log (p : ℝ)| ^ m :=
      pow_le_pow_left₀ (Real.log_pos one_lt_two).le hlog m
    have hpowFactor :
        (p : ℝ) ^ (-(1 - 2 * sigma)) ≤
          (2 : ℝ) ^ (-(1 - 2 * sigma)) :=
      Real.rpow_le_rpow_of_nonpos zero_lt_two hp2 (by linarith)
    have hfactorP : 0 ≤ 1 - (p : ℝ) ^ (-(1 - 2 * sigma)) :=
      sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.prop.one_lt) (by linarith)).le
    have hfactorSq :
        (1 - (2 : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 ≤
          (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 :=
      pow_le_pow_left₀ hfactor2.le (by linarith) 2
    have hpow : 1 / (p : ℝ) ≤
        (p : ℝ) ^ (-(theta + 2 * sigma)) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    rw [weightedPrimeClockReflectionLogMomentEnergy_eq_factor
      m theta sigma p]
    dsimp only [c]
    have hleft :
        (Real.log 2) ^ m *
            (1 - (2 : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 ≤
          |Real.log (p : ℝ)| ^ m *
            (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 :=
      mul_le_mul hlogPow hfactorSq (sq_nonneg _) (pow_nonneg (abs_nonneg _) m)
    calc
      ((Real.log 2) ^ m *
          (1 - (2 : ℝ) ^ (-(1 - 2 * sigma))) ^ 2) * (1 / (p : ℝ)) ≤
        (|Real.log (p : ℝ)| ^ m *
          (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2) * (1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right hleft (by positivity)
      _ ≤ (|Real.log (p : ℝ)| ^ m *
          (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2) *
            (p : ℝ) ^ (-(theta + 2 * sigma)) :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (pow_nonneg (abs_nonneg _) m) (sq_nonneg _))
      _ = |Real.log (p : ℝ)| ^ m * (p : ℝ) ^ (-(theta + 2 * sigma)) *
          (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 := by ring
  have hscaled : Summable (fun p : Nat.Primes => c * (1 / (p : ℝ))) := by
    exact Summable.of_nonneg_of_le (fun _ => by positivity) hlower hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff hc.ne').mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

private theorem summable_weightedPrimeClockReflectionLogMomentEnergy_iff_of_lt_half
    (m : ℕ) (theta : ℝ) {sigma : ℝ} (hsigma : sigma < 1 / 2) :
    Summable (weightedPrimeClockReflectionLogMomentEnergy m theta sigma) ↔
      1 - 2 * sigma < theta := by
  constructor
  · intro hsum
    by_contra h
    exact not_summable_weightedPrimeClockReflectionLogMomentEnergy_of_lt_half
      m hsigma (le_of_not_gt h) hsum
  · exact summable_weightedPrimeClockReflectionLogMomentEnergy_of_lt_half m hsigma

/-- Reflection about `1/2` preserves every weighted logarithmic moment pointwise. -/
theorem weightedPrimeClockReflectionLogMomentEnergy_one_sub
    (m : ℕ) (theta sigma : ℝ) (p : Nat.Primes) :
    weightedPrimeClockReflectionLogMomentEnergy m theta (1 - sigma) p =
      weightedPrimeClockReflectionLogMomentEnergy m theta sigma p := by
  simp only [weightedPrimeClockReflectionLogMomentEnergy,
    primeClockReflectionEnergy_one_sub]

/-- Every damped logarithmic reflected moment is nonnegative, with no sign condition on the
damping exponent. -/
theorem weightedPrimeClockReflectionLogMomentEnergy_nonneg
    (m : ℕ) (theta sigma : ℝ) (p : Nat.Primes) :
    0 ≤ weightedPrimeClockReflectionLogMomentEnergy m theta sigma p := by
  rw [weightedPrimeClockReflectionLogMomentEnergy, primeClockReflectionEnergy]
  exact mul_nonneg (pow_nonneg (abs_nonneg _) m)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))

/-- **All-moment damping-aperture law.**  No sign hypothesis on the damping exponent is needed:
at the critical line the seam is identically zero, while off the line the exact threshold is the
horizontal reflection charge `|2 * sigma - 1|`. -/
theorem summable_weightedPrimeClockReflectionLogMomentEnergy_iff
    (m : ℕ) (theta sigma : ℝ) :
    Summable (weightedPrimeClockReflectionLogMomentEnergy m theta sigma) ↔
      sigma = 1 / 2 ∨ |2 * sigma - 1| < theta := by
  rcases lt_trichotomy sigma (1 / 2) with hlt | heq | hgt
  · rw [summable_weightedPrimeClockReflectionLogMomentEnergy_iff_of_lt_half
      m theta hlt]
    have hneg : 2 * sigma - 1 < 0 := by linarith
    rw [abs_of_neg hneg]
    constructor
    · exact fun h => Or.inr (by linarith)
    · rintro (h | h)
      · linarith
      · linarith

  · subst sigma
    constructor
    · exact fun _ => Or.inl rfl
    · intro _
      have hzero :
          weightedPrimeClockReflectionLogMomentEnergy m theta (1 / 2) =
            (fun _ : Nat.Primes => (0 : ℝ)) := by
        funext p
        rw [weightedPrimeClockReflectionLogMomentEnergy,
          primeClockReflectionEnergy_half]
        ring
      rw [hzero]
      exact summable_zero
  · have hreflect : 1 - sigma < 1 / 2 := by linarith
    have hfun :
        weightedPrimeClockReflectionLogMomentEnergy m theta sigma =
          weightedPrimeClockReflectionLogMomentEnergy m theta (1 - sigma) := by
      funext p
      exact (weightedPrimeClockReflectionLogMomentEnergy_one_sub
        m theta sigma p).symm
    rw [hfun,
      summable_weightedPrimeClockReflectionLogMomentEnergy_iff_of_lt_half
        m theta hreflect]
    have hpos : 0 < 2 * sigma - 1 := by linarith
    rw [abs_of_pos hpos]
    constructor
    · exact fun h => Or.inr (by linarith)
    · rintro (h | h)
      · linarith
      · linarith

/-- **Bounded-source all-moment aperture law.** Multiplying any reflected logarithmic moment by a
prime weight uniformly bounded above and away from zero leaves its exact damping aperture
unchanged. -/
theorem summable_mul_weightedPrimeClockReflectionLogMomentEnergy_iff
    (m : ℕ) (theta sigma : ℝ) (w : Nat.Primes → ℝ) {c C : ℝ}
    (hc : 0 < c) (hlower : ∀ p, c ≤ w p) (hupper : ∀ p, w p ≤ C) :
    Summable (fun p => w p *
      weightedPrimeClockReflectionLogMomentEnergy m theta sigma p) ↔
      sigma = 1 / 2 ∨ |2 * sigma - 1| < theta :=
  (HTGeometry.summable_mul_iff_of_nonneg_of_uniform_pos_le_of_le
    (f := weightedPrimeClockReflectionLogMomentEnergy m theta sigma) (w := w)
    (weightedPrimeClockReflectionLogMomentEnergy_nonneg m theta sigma)
    hc hlower hupper).trans
      (summable_weightedPrimeClockReflectionLogMomentEnergy_iff m theta sigma)

/-- Power-damped reflected prime-clock energy (`m = 0`). -/
def weightedPrimeClockReflectionEnergy
    (theta sigma : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-theta) * primeClockReflectionEnergy sigma p

/-- The amplitude interface is the zeroth member of the logarithmic-moment hierarchy. -/
theorem weightedPrimeClockReflectionLogMomentEnergy_zero
    (theta sigma : ℝ) :
    weightedPrimeClockReflectionLogMomentEnergy 0 theta sigma =
      weightedPrimeClockReflectionEnergy theta sigma := by
  funext p
  simp [weightedPrimeClockReflectionLogMomentEnergy,
    weightedPrimeClockReflectionEnergy]

/-- Exact damping aperture for the reflected prime amplitudes. -/
theorem summable_weightedPrimeClockReflectionEnergy_iff
    (theta sigma : ℝ) :
    Summable (weightedPrimeClockReflectionEnergy theta sigma) ↔
      sigma = 1 / 2 ∨ |2 * sigma - 1| < theta := by
  rw [← weightedPrimeClockReflectionLogMomentEnergy_zero]
  exact summable_weightedPrimeClockReflectionLogMomentEnergy_iff 0 theta sigma

/-- Zeroth-moment form of the bounded-source aperture law. -/
theorem summable_mul_weightedPrimeClockReflectionEnergy_iff
    (theta sigma : ℝ) (w : Nat.Primes → ℝ) {c C : ℝ}
    (hc : 0 < c) (hlower : ∀ p, c ≤ w p) (hupper : ∀ p, w p ≤ C) :
    Summable (fun p => w p * weightedPrimeClockReflectionEnergy theta sigma p) ↔
      sigma = 1 / 2 ∨ |2 * sigma - 1| < theta := by
  rw [← weightedPrimeClockReflectionLogMomentEnergy_zero]
  exact summable_mul_weightedPrimeClockReflectionLogMomentEnergy_iff
    0 theta sigma w hc hlower hupper

/-- Power-damped square norm of the actual finite-value prime seam. -/
def weightedNatPrimeSeamChargeNormSq
    (theta : ℝ) (rho : ℂ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-theta) *
    ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2

/-- The actual complex prime seam has the same square as the real reflected amplitude, multiplied
by the squared logarithmic scale. -/
theorem norm_sq_orbitwiseNatPrimeSeamCharge_eq_log_sq_mul_primeClockReflectionEnergy
    (rho : ℂ) (p : Nat.Primes) :
    ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 =
      (Real.log (p : ℝ)) ^ 2 * primeClockReflectionEnergy rho.re p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hleft :
      ((p : ℝ) ^ (-rho.re)) ^ 2 * (p : ℝ) ^ (-1 : ℝ) =
        (p : ℝ) ^ (-(1 + 2 * rho.re)) := by
    rw [pow_two, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
    congr 1
    ring
  have hright :
      ((p : ℝ) ^ (-(1 - rho.re))) ^ 2 * (p : ℝ) ^ (-1 : ℝ) =
        (p : ℝ) ^ (-(3 - 2 * rho.re)) := by
    rw [pow_two, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
    congr 1
    ring
  have hcross :
      (p : ℝ) ^ (-rho.re) * (p : ℝ) ^ (-(1 - rho.re)) *
          (p : ℝ) ^ (-1 : ℝ) =
        (p : ℝ) ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hp0, ← Real.rpow_add hp0]
    congr 1
    ring
  have henergy :
      primeClockReflectionEnergy rho.re p / (p : ℝ) =
        (p : ℝ) ^ (-(1 + 2 * rho.re)) +
          (p : ℝ) ^ (-(3 - 2 * rho.re)) -
            2 * (p : ℝ) ^ (-2 : ℝ) := by
    rw [primeClockReflectionEnergy, div_eq_mul_inv, ← Real.rpow_neg_one]
    rw [show (p : ℝ) ^ (-rho.re) - (p : ℝ) ^ (-(1 - rho.re)) =
        (p : ℝ) ^ (-rho.re) - (p : ℝ) ^ (-(1 - rho.re)) by rfl]
    calc
      ((p : ℝ) ^ (-rho.re) - (p : ℝ) ^ (-(1 - rho.re))) ^ 2 *
          (p : ℝ) ^ (-1 : ℝ) =
        ((p : ℝ) ^ (-rho.re)) ^ 2 * (p : ℝ) ^ (-1 : ℝ) +
          ((p : ℝ) ^ (-(1 - rho.re))) ^ 2 * (p : ℝ) ^ (-1 : ℝ) -
            2 * ((p : ℝ) ^ (-rho.re) * (p : ℝ) ^ (-(1 - rho.re)) *
              (p : ℝ) ^ (-1 : ℝ)) := by ring
      _ = _ := by rw [hleft, hright, hcross]
  have h := orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_reflectionSecondDifference
    rho p
  rw [← henergy] at h
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  field_simp [hpne] at h
  exact h

/-- The logarithmic prime-seam interface is exactly the second moment of the general hierarchy. -/
theorem weightedNatPrimeSeamChargeNormSq_eq_logMomentTwo
    (theta : ℝ) (rho : ℂ) :
    weightedNatPrimeSeamChargeNormSq theta rho =
      weightedPrimeClockReflectionLogMomentEnergy 2 theta rho.re := by
  funext p
  rw [weightedNatPrimeSeamChargeNormSq,
    weightedPrimeClockReflectionLogMomentEnergy,
    norm_sq_orbitwiseNatPrimeSeamCharge_eq_log_sq_mul_primeClockReflectionEnergy]
  rw [abs_of_pos (Real.log_pos (by exact_mod_cast p.prop.one_lt))]
  ring

/-- Exact damping aperture for the actual reflected rational-Hurwitz prime seam. -/
theorem summable_weightedNatPrimeSeamCharge_norm_sq_iff
    (theta : ℝ) (rho : ℂ) :
    Summable (weightedNatPrimeSeamChargeNormSq theta rho) ↔
      rho.re = 1 / 2 ∨ |2 * rho.re - 1| < theta := by
  rw [weightedNatPrimeSeamChargeNormSq_eq_logMomentTwo]
  exact summable_weightedPrimeClockReflectionLogMomentEnergy_iff 2 theta rho.re

/-- A fibre belongs to every positively damped prime-seam Hilbert sector exactly on the critical
line.  This discharges the positive-loss quantifier without a strip hypothesis. -/
theorem allPositivePrimeSeamDamping_iff_re_eq_half (rho : ℂ) :
    (∀ theta : ℝ, 0 < theta →
      Summable (weightedNatPrimeSeamChargeNormSq theta rho)) ↔
        rho.re = 1 / 2 := by
  constructor
  · intro h
    by_contra hline
    let theta := |2 * rho.re - 1| / 2
    have hcharge : 0 < |2 * rho.re - 1| := abs_pos.mpr (by
      intro hzero
      apply hline
      linarith)
    have hsum := h theta (by dsimp [theta]; positivity)
    have hthreshold :=
      (summable_weightedNatPrimeSeamCharge_norm_sq_iff theta rho).mp hsum
    rcases hthreshold with hline' | hstrict
    · exact hline hline'
    · dsimp [theta] at hstrict
      linarith
  · intro hline theta _
    exact (summable_weightedNatPrimeSeamCharge_norm_sq_iff theta rho).mpr
      (Or.inl hline)

/-- Global all-positive-loss source interface. -/
def XiAllPositivePrimeSeamDamping : Prop :=
  ∀ theta : ℝ, 0 < theta → ∀ rho : ℂ, xi rho = 0 →
    Summable (weightedNatPrimeSeamChargeNormSq theta rho)

/-- **Cofinal-loss RH interface.**  Uniform access to every positive damping loss on every Xi
fibre is equivalent to RH.  The reverse implication is a consumer theorem, not a source estimate. -/
theorem xiAllPositivePrimeSeamDamping_iff_riemannHypothesis :
    XiAllPositivePrimeSeamDamping ↔ RiemannHypothesis := by
  constructor
  · intro hall
    apply riemannHypothesis_iff_xiZero_primeClockShale.mpr
    intro rho hzero
    have hline : rho.re = 1 / 2 :=
      (allPositivePrimeSeamDamping_iff_re_eq_half rho).mp
        (fun theta htheta => hall theta htheta rho hzero)
    exact (summable_primeClockReflectionEnergy_iff rho.re).mpr hline
  · intro hRH theta htheta rho hzero
    have hline : rho.re = 1 / 2 :=
      (summable_primeClockReflectionEnergy_iff rho.re).mp
        ((riemannHypothesis_iff_xiZero_primeClockShale.mp hRH) rho hzero)
    exact (summable_weightedNatPrimeSeamCharge_norm_sq_iff theta rho).mpr
      (Or.inl hline)

/-- Requested one-way consumer form of the cofinal-loss criterion. -/
theorem riemannHypothesis_of_allPositivePrimeSeamDamping
    (h : XiAllPositivePrimeSeamDamping) : RiemannHypothesis :=
  xiAllPositivePrimeSeamDamping_iff_riemannHypothesis.mp h

end

end RHTower
