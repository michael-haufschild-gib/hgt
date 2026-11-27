import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Alphabet
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Universal.Density

/-! # Dense obstructions inside the countable set of integer-spectrum ratios -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family

open Set

/-- Elementary prime spectra are among the finite lists of integer energy labels. -/
theorem elementary_subset : Universal.exceptional ⊆ exceptional energy := by
  rintro r ⟨S,hs,x,hx,y,hy,ratio⟩
  by_contra good
  have rpos : 0 < r := ratio ▸ div_pos hx.1 hy.1
  have scale : r*y=x := ((div_eq_iff hy.1.ne').mp ratio).symm
  let a := elementary (S := S)
  let E := energy ∘ a
  have tests : agrees E y ∧ agrees E (r*y) := ⟨hy.2,by rw [scale]; exact hx.2⟩
  have reflecting := ((calibrated energy a rpos good y).mp tests).resolve_left hy.1.ne'
  have hit : Coincides a (1 : ℝ) := reflection_agrees reflecting 1
  have small := (prime_packet_iff S 1).mp (by simpa only [Nat.cast_one] using hit)
  omega

/-- Every calibration interval above one contains both universal ratios and ratios
that fail already on elementary primes. -/
theorem both_between {a b : ℝ} (ha : 1 < a) (ab : a < b) :
    (∃ r ∈ Ioo a b, r ∉ exceptional energy) ∧ ∃ r ∈ Ioo a b, r ∈ exceptional energy := by
  obtain ⟨r,hr,bad⟩ := (Universal.both_between ha ab).2
  exact ⟨good_between energy ab,r,hr,elementary_subset bad⟩

#print axioms elementary_subset
#print axioms both_between

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family
