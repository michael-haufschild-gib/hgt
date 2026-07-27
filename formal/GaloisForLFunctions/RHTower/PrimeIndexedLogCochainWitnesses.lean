import GaloisForLFunctions.RHTower.OmegaObstruction

/-!
# Prime-indexed log cochain formulas exist, and are exactly the prime-log cochains

The prime-log integrality layer consumes a `PrimeIndexedLogCochainFormula` but never exhibits one.
The bundle is in fact free: any family of prime-indexed integer coefficients induces a formula for
the cochain it evaluates to, and every formula arises this way.  Two instances follow — the zero
cochain and the constant cochain `log p` — and with them the integrality conclusions of the layer
hold on explicit objects.
-/

namespace GaloisForLFunctions.RHTower

/-- **Every prime-indexed coefficient family is a formula** for the cochain it evaluates to. -/
def primeIndexedLogCochainFormula_ofCoeff {G : Type*} (c : G → G → Nat.Primes →₀ ℤ) :
    PrimeIndexedLogCochainFormula
      (fun g h => (c g h).sum fun p n => n • Real.log (p : ℕ)) where
  coeff := c
  eval_eq := fun _ _ => rfl

/-- The zero cochain carries a formula. -/
def primeIndexedLogCochainFormula_zero (G : Type*) :
    PrimeIndexedLogCochainFormula (fun _ _ : G => (0 : ℝ)) where
  coeff := fun _ _ => 0
  eval_eq := fun _ _ => by simp

/-- The constant cochain `log p` carries a formula, for every prime `p`. -/
noncomputable def primeIndexedLogCochainFormula_const (G : Type*) (p : Nat.Primes) :
    PrimeIndexedLogCochainFormula (fun _ _ : G => Real.log (p : ℕ)) where
  coeff := fun _ _ => Finsupp.single p 1
  eval_eq := fun _ _ => by
    rw [Finsupp.sum_single_index] <;> simp

/-- **Prime-log integrality on an explicit family.**  The cochain evaluated from any prime-indexed
coefficient family is prime-log integral. -/
theorem isPrimeLogIntegral_ofCoeff {G : Type*} (c : G → G → Nat.Primes →₀ ℤ) :
    IsPrimeLogIntegral (fun g h => (c g h).sum fun p n => n • Real.log (p : ℕ)) :=
  (primeIndexedLogCochainFormula_ofCoeff c).isPrimeLogIntegral

/-- The constant cochain `log p` is prime-log integral. -/
theorem isPrimeLogIntegral_const (G : Type*) (p : Nat.Primes) :
    IsPrimeLogIntegral (fun _ _ : G => Real.log (p : ℕ)) :=
  (primeIndexedLogCochainFormula_const G p).isPrimeLogIntegral

end GaloisForLFunctions.RHTower
