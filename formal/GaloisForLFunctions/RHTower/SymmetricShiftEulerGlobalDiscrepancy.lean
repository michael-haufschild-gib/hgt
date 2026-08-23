import GaloisForLFunctions.RHTower.SymmetricShiftEulerPrimePowers

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Universal support, kept named so its subtype can be reindexed explicitly. -/
abbrev symmetricShiftAllPrimeSupport : Set Nat.Primes := Set.univ

/-- Equivalence between direct prime-power coordinates and the universal prime support. -/
def symmetricShiftAllPrimePowerEquiv : Nat.Primes × ℕ ≃
    symmetricShiftAllPrimeSupport × ℕ where
  toFun z := (⟨z.1, Set.mem_univ z.1⟩, z.2)
  invFun z := (z.1.1, z.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full all-prime symmetric-shift logarithmic Euler discrepancy. -/
def symmetricShiftEulerGlobalDiscrepancyTerm
    (a : SymmetricPositiveShift) (sigma : ℝ) (z : Nat.Primes × ℕ) : ℝ :=
  symmetricShiftEulerPrimePowerDiscrepancyTerm (S := symmetricShiftAllPrimeSupport) a sigma
    (symmetricShiftAllPrimePowerEquiv z)

/-- To the right of `1+a`, the complete prime-power discrepancy is summable. -/
theorem summable_symmetricShiftEulerGlobalDiscrepancyTerm_of_lt
    (a : SymmetricPositiveShift) {sigma : ℝ} (hsigma : 1 + a.1 < sigma) :
    Summable (fun z : Nat.Primes × ℕ => symmetricShiftEulerGlobalDiscrepancyTerm a sigma z) := by
  have hprime : Summable (fun p : Nat.Primes => ((p.1 : ℕ) : ℝ) ^ (-(sigma - a.1))) :=
    RHTower.summable_primeRpow (by linarith)
  have hbase : Summable (fun p : symmetricShiftAllPrimeSupport =>
      ((p.1.1 : ℕ) : ℝ) ^ (-(sigma - a.1))) := by
    apply ((Equiv.Set.univ Nat.Primes).summable_iff).mpr hprime |>.congr
    intro p
    rfl
  have hpower : Summable (fun z : symmetricShiftAllPrimeSupport × ℕ =>
      symmetricShiftEulerPrimePowerDiscrepancyTerm a sigma z) :=
    summable_symmetricShiftEulerPrimePowerDiscrepancyTerm_of_lt a hsigma hbase
  change Summable ((fun z : symmetricShiftAllPrimeSupport × ℕ =>
    symmetricShiftEulerPrimePowerDiscrepancyTerm a sigma z) ∘ symmetricShiftAllPrimePowerEquiv)
  exact (symmetricShiftAllPrimePowerEquiv.summable_iff).mpr hpower

/-- The global prime-power term restricted to the first layer is the first-prime term. -/
theorem symmetricShiftEulerGlobalDiscrepancyTerm_zero
    (a : SymmetricPositiveShift) (sigma : ℝ) (p : Nat.Primes) :
    symmetricShiftEulerGlobalDiscrepancyTerm a sigma (p, 0) =
      symmetricShiftEulerPrimeDiscrepancyTerm a sigma p := by
  dsimp [symmetricShiftEulerGlobalDiscrepancyTerm, symmetricShiftAllPrimePowerEquiv,
    symmetricShiftEulerPrimePowerDiscrepancyTerm, symmetricShiftEulerPrimePowerDiscrepancy]
  unfold symmetricShiftEulerPrimeDiscrepancyTerm
  rw [RHTower.exp_primePowerMu]
  simp only [Nat.cast_zero, zero_add, one_mul, mul_one, RHTower.primePowerWeight, one_div, inv_one]

/-- The complete nonnegative prime-power discrepancy has exact abscissa `1+a`. -/
theorem summable_symmetricShiftEulerGlobalDiscrepancyTerm_iff
    (a : SymmetricPositiveShift) (sigma : ℝ) :
    Summable (fun z : Nat.Primes × ℕ => symmetricShiftEulerGlobalDiscrepancyTerm a sigma z) ↔
      1 + a.1 < sigma := by
  constructor
  · intro hsum
    have hzero := hsum.comp_injective (i := fun p : Nat.Primes => (p, 0)) (by
      intro p q hpq
      exact congrArg Prod.fst hpq)
    have hfirst : Summable (fun p : Nat.Primes =>
        symmetricShiftEulerPrimeDiscrepancyTerm a sigma p) := by
      apply hzero.congr
      intro p
      exact symmetricShiftEulerGlobalDiscrepancyTerm_zero a sigma p
    exact (summable_symmetricShiftEulerPrimeDiscrepancyTerm_iff a sigma).mp hfirst
  · exact summable_symmetricShiftEulerGlobalDiscrepancyTerm_of_lt a

end

end GaloisForLFunctions.RHTower
