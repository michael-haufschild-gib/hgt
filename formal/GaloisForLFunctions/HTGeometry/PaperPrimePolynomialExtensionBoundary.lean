import GaloisForLFunctions.HTGeometry.PaperPrimePolynomialActions
import GaloisForLFunctions.HTGeometry.PaperArithmeticLogRigidity

/-!
# Exact boundary between polynomial prime clocks and the full coefficient algebra

Finite-prime polynomial charts admit genuine compatible additive actions.
Their prime alphabet is exact, every chart is proper, and neither the clocks
nor their actions extend as locally nilpotent or polynomial additive motions
on the full Dirichlet-convolution algebra.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate CoactionLND

noncomputable section

/-- A prime outside the chart kills every element of its polynomial subalgebra. -/
theorem paperPrimePolynomialAlgebra_primeDeriv_outside (S : Finset Nat.Primes)
    (q : Nat.Primes) (f : paperPrimePolynomialAlgebra S) (hq : q ∉ S) :
    primeDeriv (q : ℕ) (f : ArithmeticFunction ℂ) = 0 := by
  classical
  obtain ⟨P, rfl⟩ := (paperPrimePolynomialEquiv S).surjective f
  rw [paperPrimePolynomialEquiv_coe,
    jacobian_aeval_eq_sum_pderiv (K := ℂ) (primeDeriv (q : ℕ))
      (primeDeriv_add (q : ℕ)) (primeDeriv_mul (q : ℕ) q.2)
      (primeDeriv_algebraMap (q : ℕ) q.2)]
  apply Finset.sum_eq_zero
  intro j _
  have hne : q ≠ j.1 := by
    intro h
    apply hq
    rw [h]
    exact j.2
  rw [paperPrimeCoordinate_primeDeriv, if_neg hne, mul_zero]

/-- The polynomial chart contains exactly the prime coordinates in its declared prime set. -/
theorem paperPrimePolynomialAlgebra_coordinate_mem_iff (S : Finset Nat.Primes)
    (q : Nat.Primes) : paperPrimeCoordinate q ∈ paperPrimePolynomialAlgebra S ↔ q ∈ S := by
  classical
  constructor
  · intro hmem
    by_contra hq
    have he := paperPrimePolynomialAlgebra_primeDeriv_outside S q
      ⟨paperPrimeCoordinate q, hmem⟩ hq
    simp [paperPrimeCoordinate_primeDeriv] at he
  · intro hq
    apply Algebra.subset_adjoin
    exact ⟨⟨q, hq⟩, rfl⟩

/-- No finite-prime polynomial chart equals the full arithmetic-function algebra. -/
theorem paperPrimePolynomialAlgebra_ne_top (S : Finset Nat.Primes) :
    paperPrimePolynomialAlgebra S ≠ ⊤ := by
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset S
  intro htop
  apply hq
  apply (paperPrimePolynomialAlgebra_coordinate_mem_iff S q).mp
  rw [htop]
  trivial

/-- The native ambient prime derivation never terminates on every arithmetic function. -/
theorem paperNativePrimeDerivation_not_locallyNilpotent (q : Nat.Primes) :
    ¬ IsLocallyNilpotent (primeArithmeticDerivation (q : ℕ) q.2) := by
  intro h
  have hzero := (paperArithmeticFunction_LND_iff_eq_zero _).mp h
  have he := congrArg
    (fun D : Derivation ℂ (ArithmeticFunction ℂ) (ArithmeticFunction ℂ) =>
      D (paperPrimeCoordinate q)) hzero
  simp [primeArithmeticDerivation_apply, paperPrimeCoordinate_primeDeriv] at he

/-- A nonzero polynomial prime clock has no locally nilpotent extension to the full algebra. -/
theorem paperPrimePolynomialClock_no_lnd_extension (S : Finset Nat.Primes) (p : S) :
    ¬ ∃ D : Derivation ℂ (ArithmeticFunction ℂ) (ArithmeticFunction ℂ),
      IsLocallyNilpotent D ∧ ∀ f : paperPrimePolynomialAlgebra S,
        D (f : ArithmeticFunction ℂ) = (paperPrimePolynomialClock S p f : ArithmeticFunction ℂ) := by
  rintro ⟨D, hD, hrestrict⟩
  have hzero := (paperArithmeticFunction_LND_iff_eq_zero D).mp hD
  have he := hrestrict (paperPrimePolynomialGenerator S p)
  rw [hzero, Derivation.zero_apply, paperPrimePolynomialClock_self] at he
  exact zero_ne_one he

/-- The integrated prime action likewise has no polynomial additive extension to the full algebra. -/
theorem paperPrimePolynomialAction_no_global_extension (S : Finset Nat.Primes) (p : S) :
    ¬ ∃ ρ : PolynomialAdditiveAction ℂ (ArithmeticFunction ℂ),
      ∀ f : paperPrimePolynomialAlgebra S,
        ρ.toAlgHom (f : ArithmeticFunction ℂ) =
          Polynomial.map (paperPrimePolynomialAlgebra S).val.toRingHom
            ((paperPrimePolynomialAction S p).toAlgHom f) := by
  rintro ⟨ρ, hrestrict⟩
  have he := hrestrict (paperPrimePolynomialGenerator S p)
  rw [paperArithmeticFunction_additiveAction_trivial, paperPrimePolynomialAction_generator] at he
  have hc := congrArg (fun P => Polynomial.coeff P 1) he
  simp at hc

end

end GaloisForLFunctions.HTGeometry
