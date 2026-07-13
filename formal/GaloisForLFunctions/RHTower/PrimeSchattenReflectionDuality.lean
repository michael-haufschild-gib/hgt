import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.PSeries

/-!
# Functional-equation reflection as Schatten-exponent duality

The prime diagonal with amplitudes `p^(-sigma)` has critical Schatten exponent `1/sigma`:
its `r`-energy is summable exactly when `r*sigma > 1`.  Reflection
`sigma ↦ 1-sigma` exchanges this exponent with its Hölder conjugate.  The unique self-dual point is
`sigma=1/2`, where both critical exponents equal `2`.

The pointwise product of the two reflected prime amplitudes is always `p^(-1)`, so their formal
trace pairing lies exactly on Euler's divergent prime-harmonic boundary for every point of the
critical strip.  At `sigma=1/2` this boundary pairing is a self-pairing of two Hilbert--Schmidt
critical sectors; away from the line it pairs distinct conjugate Banach ideals.
-/

noncomputable section

namespace GaloisForLFunctions

/-- The `r`th Schatten energy density of the prime diagonal at real coordinate `sigma`. -/
def primeSchattenMass (sigma r : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-r * sigma)

/-- The prime diagonal has finite `r`th Schatten energy exactly when `r*sigma>1`. -/
theorem summable_primeSchattenMass_iff (sigma r : ℝ) :
    Summable (primeSchattenMass sigma r) ↔ 1 < r * sigma := by
  rw [show primeSchattenMass sigma r =
    fun p : Nat.Primes => (p : ℝ) ^ (-r * sigma) by rfl]
  rw [Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- The critical Schatten exponent attached to the prime amplitude `p^(-sigma)`. -/
def primeSchattenCriticalExponent (sigma : ℝ) : ℝ := sigma⁻¹

/-- Reflection exchanges the two critical exponents as a Hölder-conjugate pair. -/
theorem critical_exponents_holder_conjugate (sigma : ℝ) :
    (primeSchattenCriticalExponent sigma)⁻¹ +
      (primeSchattenCriticalExponent (1 - sigma))⁻¹ = 1 := by
  dsimp [primeSchattenCriticalExponent]
  rw [inv_inv, inv_inv]
  ring

/-- The reflected critical exponents agree only at the Hilbert--Schmidt point `sigma=1/2`. -/
theorem critical_exponents_eq_iff_half (sigma : ℝ) :
    primeSchattenCriticalExponent sigma =
      primeSchattenCriticalExponent (1 - sigma) ↔ sigma = 1 / 2 := by
  dsimp [primeSchattenCriticalExponent]
  rw [inv_inj]
  constructor <;> intro h
  · linarith
  · rw [h]
    norm_num

/-- Product density of the two functional-equation-reflected prime amplitudes. -/
def reflectedPrimeMass (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-sigma) * (p : ℝ) ^ (-(1 - sigma))

/-- Reflection makes the product density the fixed prime-harmonic density `1/p`, independently of
`sigma`. -/
theorem reflectedPrimeMass_eq (sigma : ℝ) (p : Nat.Primes) :
    reflectedPrimeMass sigma p = 1 / (p : ℝ) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [reflectedPrimeMass, ← Real.rpow_add hp]
  rw [show -sigma + -(1 - sigma) = (-1 : ℝ) by ring]
  rw [Real.rpow_neg_one]
  simp [one_div]

/-- The ordinary trace pairing of the reflected prime sectors diverges everywhere: it is Euler's
prime harmonic series. -/
theorem reflectedPrimeMass_not_summable (sigma : ℝ) :
    ¬ Summable (reflectedPrimeMass sigma) := by
  intro h
  apply Nat.Primes.not_summable_one_div
  exact h.congr (fun p => reflectedPrimeMass_eq sigma p)

end GaloisForLFunctions
