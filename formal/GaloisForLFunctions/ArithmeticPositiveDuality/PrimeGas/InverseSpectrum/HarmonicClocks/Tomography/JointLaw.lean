import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.ClockReadings

/-! # Joint prime phases identify every occupation in one observation law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open MeasureTheory

/-- The two phases recorded on the same occupied label. -/
def jointClockLabel (p q : Nat.Primes) (D E n : ℕ+) : Circle × Circle :=
  (occupationPhase (primeClockTime p D) n,occupationPhase (primeClockTime q E) n)

theorem jointClockLabel_injective (p q : Nat.Primes) (hpq : p ≠ q) (D E : ℕ+) :
    Function.Injective (jointClockLabel p q D E) := by
  have ordered (a b : ℕ+) (hab : a ≤ b) (h : jointClockLabel p q D E a = jointClockLabel p q D E b) : a = b := by
    obtain ⟨j,hj⟩ := (primeClock_alias_iff p D a b hab).mp (congrArg Prod.fst h)
    obtain ⟨k,hk⟩ := (primeClock_alias_iff q E a b hab).mp (congrArg Prod.snd h)
    cases j with
    | zero => simpa [primeRayLabel] using hj.symm
    | succ j =>
      have he := congrArg PNat.val (mul_left_cancel (hj.symm.trans hk))
      change p.val^(D.val*(j+1)) = q.val^(E.val*k) at he
      have hd := dvd_pow_self p.val (Nat.mul_pos D.pos (Nat.succ_pos j)).ne'
      rw [he] at hd
      exact False.elim (hpq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property q.property).mp
        (p.property.dvd_of_dvd_pow hd))))
  intro a b he
  rcases le_total a b with hab | hba
  · exact ordered a b hab he
  · exact (ordered b a hba he.symm).symm

theorem jointClock_fiber (w : ℕ+ → ℝ) (p q : Nat.Primes) (hpq : p ≠ q) (D E n : ℕ+) :
    selectedMass w (fun k => jointClockLabel p q D E k = jointClockLabel p q D E n) = w n :=
  (selectedMass_congr w (fun _ => (jointClockLabel_injective p q hpq D E).eq_iff)).trans (selectedMass_single w n)

def jointClockLaw (v : MissingWave) (p q : Nat.Primes) (D E : ℕ+) :=
  labelReportLaw v (jointClockLabel p q D E)

/-- Each joint atom directly reads one occupation probability, even above both single-clock cutoffs. -/
theorem jointClockLaw_atom (v : MissingWave) (p q : Nat.Primes) (hpq : p ≠ q) (D E n : ℕ+) :
    ((jointClockLaw v p q D E : Measure (Circle × Circle)) {jointClockLabel p q D E n}).toReal =
      occupationProbability v n := by
  rw [jointClockLaw,labelReportLaw_atom]
  exact jointClock_fiber _ p q hpq D E n

theorem jointClockLaw_identifies_occupations (p q : Nat.Primes) (hpq : p ≠ q) (D E : ℕ+) (v w : MissingWave) :
    jointClockLaw v p q D E = jointClockLaw w p q D E ↔ occupationProbability v = occupationProbability w := by
  constructor
  · intro he
    funext n
    rw [← jointClockLaw_atom v p q hpq D E n,he,jointClockLaw_atom]
    exact hpq
  · exact fun he => labelReportLaw_congr he _

#print axioms jointClockLabel_injective
#print axioms jointClock_fiber
#print axioms jointClockLaw_atom
#print axioms jointClockLaw_identifies_occupations

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
