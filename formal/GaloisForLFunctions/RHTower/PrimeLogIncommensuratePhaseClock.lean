import GaloisForLFunctions.HTGeometry.IncommensuratePhaseClock
import GaloisForLFunctions.RHTower.GelfondSchneider

/-!
# Two distinct prime-log phases recover a real clock exactly

Distinct prime logarithms have irrational ratio.  The general incommensurate-clock theorem therefore
shows that any pair of distinct prime phases

`t |-> (exp(i log(p) t), exp(i log(q) t))`

is globally injective on real clock time.  One prime phase is periodic; the pair loses no additional
information beyond whatever equivalence relation was already present in the underlying clock
coordinate.

This supplies a direct RHTower instance of the quantum/cosmological multi-frequency clock-fusion
law.  It is a source-coordinate observability theorem, not an RH criterion.
-/

namespace RHTower

noncomputable section

/-- Paired phase readout at the logarithmic frequencies of two natural numbers. -/
def primeLogPhaseClockPair (p q : ℕ) (time : ℝ) : ℂ × ℂ :=
  HTGeometry.phaseClockPair (Real.log p) (Real.log q) time

/-- Two distinct prime-log phase reporters identify unrestricted real clock time exactly. -/
theorem primeLogPhaseClockPair_injective {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (primeLogPhaseClockPair p q) := by
  exact HTGeometry.phaseClockPair_injective
    (ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt)))
    (GaloisForLFunctions.RHTower.irrational_log_ratio hp hq hpq)

/-- Equality of two distinct prime-log phase pairs is exactly equality of real clock time. -/
theorem primeLogPhaseClockPair_eq_iff {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (time₁ time₂ : ℝ) :
    primeLogPhaseClockPair p q time₁ = primeLogPhaseClockPair p q time₂ ↔
      time₁ = time₂ := by
  constructor
  · intro h
    exact (primeLogPhaseClockPair_injective hp hq hpq) h
  · rintro rfl
    rfl

/-- The concrete prime pair `(2,3)` is a faithful real phase clock. -/
theorem primeLogPhaseClockPair_two_three_injective :
    Function.Injective (primeLogPhaseClockPair 2 3) := by
  exact primeLogPhaseClockPair_injective (by norm_num) (by norm_num) (by norm_num)

/-- Fusing the `log 2` and `log 3` phases of any real-valued source observable loses exactly the
same fibers as the source observable itself. -/
theorem primeLogPhaseClockPair_two_three_comp_eq_iff
    {X : Type*} (clock : X → ℝ) (x y : X) :
    primeLogPhaseClockPair 2 3 (clock x) =
        primeLogPhaseClockPair 2 3 (clock y) ↔
      clock x = clock y := by
  constructor
  · intro h
    exact primeLogPhaseClockPair_two_three_injective h
  · intro h
    exact congrArg (primeLogPhaseClockPair 2 3) h

/-- A real source clock is injective exactly when its fused `(log 2, log 3)` phase report is
injective. -/
theorem primeLogPhaseClockPair_two_three_comp_injective_iff
    {X : Type*} (clock : X → ℝ) :
    Function.Injective (fun x => primeLogPhaseClockPair 2 3 (clock x)) ↔
      Function.Injective clock := by
  simpa only [primeLogPhaseClockPair] using
    (HTGeometry.phaseClockPair_comp_injective_iff
      (rate₁ := Real.log 2) (rate₂ := Real.log 3)
      (ne_of_gt (Real.log_pos (by norm_num)))
      (GaloisForLFunctions.RHTower.irrational_log_ratio
        (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)) clock)

end

end RHTower
