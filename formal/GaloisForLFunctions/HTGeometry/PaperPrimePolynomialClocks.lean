import GaloisForLFunctions.HTGeometry.PaperPrimePolynomialAlgebra
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.CoordinateDerivation
import GaloisForLFunctions.HTGeometry.PaperLocallyNilpotentMultipliers
import GaloisForLFunctions.HTGeometry.FreeCoordinateConstantKernel

/-!
# Terminating native prime clocks on finite polynomial subalgebras

The source coordinate derivations become the restrictions of the existing
prime derivations of arithmetic functions. Their polynomial degree bounds,
common constants, invariant multipliers and compatibility under enlargement
are paid by the explicit polynomial chart.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

attribute [local instance 2000] Algebra.toModule
attribute [local instance 2100] Semiring.toModule

/-- A source coordinate clock on the literal finite-prime convolution subalgebra. -/
def paperPrimePolynomialClock (S : Finset Nat.Primes) (p : S) :
    Derivation ℂ (paperPrimePolynomialAlgebra S) (paperPrimePolynomialAlgebra S) :=
  CoordinateDerivation.coordinatePartial (paperPrimePolynomialEquiv S) p

/-- The clock has the native partial-derivative formula in the paid polynomial chart. -/
theorem paperPrimePolynomialClock_apply (S : Finset Nat.Primes) (p : S)
    (f : paperPrimePolynomialAlgebra S) :
    paperPrimePolynomialClock S p f = paperPrimePolynomialEquiv S
      (MvPolynomial.pderiv p ((paperPrimePolynomialEquiv S).symm f)) := rfl

/-- The chosen prime coordinate is an exact clock coordinate. -/
@[simp] theorem paperPrimePolynomialClock_self (S : Finset Nat.Primes) (p : S) :
    paperPrimePolynomialClock S p (paperPrimePolynomialGenerator S p) = 1 :=
  CoordinateDerivation.coordinatePartial_self _ p

/-- Every other prime coordinate remains constant. -/
theorem paperPrimePolynomialClock_generator (S : Finset Nat.Primes) (p q : S) :
    paperPrimePolynomialClock S p (paperPrimePolynomialGenerator S q) =
      if q = p then 1 else 0 := by
  classical
  by_cases h : q = p
  · subst q
    simp
  · rw [if_neg h]
    exact CoordinateDerivation.coordinatePartial_other _ h

/-- Every iterate is exactly the corresponding iterated polynomial partial derivative. -/
theorem paperPrimePolynomialClock_iterate (S : Finset Nat.Primes) (p : S)
    (f : paperPrimePolynomialAlgebra S) (m : ℕ) :
    ((paperPrimePolynomialClock S p : paperPrimePolynomialAlgebra S →
      paperPrimePolynomialAlgebra S)^[m]) f =
      paperPrimePolynomialEquiv S
        (((MvPolynomial.pderiv p : MvPolynomial S ℂ → MvPolynomial S ℂ)^[m])
          ((paperPrimePolynomialEquiv S).symm f)) :=
  CoordinateDerivation.transport_iterate _ _ m f

/-- The native prime clock vanishes one step beyond the input's degree in that prime. -/
theorem paperPrimePolynomialClock_degree_bound (S : Finset Nat.Primes) (p : S)
    (f : paperPrimePolynomialAlgebra S) :
    ((paperPrimePolynomialClock S p : paperPrimePolynomialAlgebra S →
      paperPrimePolynomialAlgebra S)^[((paperPrimePolynomialEquiv S).symm f).degreeOf p + 1]) f = 0 := by
  rw [paperPrimePolynomialClock_iterate]
  have hz : ((MvPolynomial.pderiv p : MvPolynomial S ℂ → MvPolynomial S ℂ)^[
      ((paperPrimePolynomialEquiv S).symm f).degreeOf p + 1])
        ((paperPrimePolynomialEquiv S).symm f) = 0 := by
    ext m
    exact CoordinateDerivation.coeff_iterate_pderiv_eq_zero p _ _ m (by omega)
  rw [hz, map_zero]

/-- Source local nilpotence now holds on the actual arithmetic-function subalgebra. -/
theorem paperPrimePolynomialClock_locallyNilpotent (S : Finset Nat.Primes) (p : S) :
    IsLocallyNilpotent (k := ℂ) (A := paperPrimePolynomialAlgebra S)
      (paperPrimePolynomialClock S p) :=
  CoordinateDerivation.coordinatePartial_locallyNilpotent _ p

/-- None of these prime clocks is zero. -/
theorem paperPrimePolynomialClock_ne_zero (S : Finset Nat.Primes) (p : S) :
    paperPrimePolynomialClock S p ≠ 0 :=
  CoordinateDerivation.coordinatePartial_ne_zero _ p

/-- The transported source clock is literally the existing native prime derivation restricted here. -/
theorem paperPrimePolynomialClock_coe (S : Finset Nat.Primes) (p : S)
    (f : paperPrimePolynomialAlgebra S) :
    (paperPrimePolynomialClock S p f : ArithmeticFunction ℂ) =
      primeDeriv (p.1 : ℕ) (f : ArithmeticFunction ℂ) := by
  classical
  obtain ⟨P, rfl⟩ := (paperPrimePolynomialEquiv S).surjective f
  have hcoord (j : S) : primeDeriv (p.1 : ℕ) (paperPrimeCoordinate j.1) =
      if j = p then 1 else 0 := by
    rw [paperPrimeCoordinate_primeDeriv]
    simp only [Subtype.val_inj, eq_comm]
  have h := jacobian_aeval_eq_sum_pderiv (K := ℂ)
    (primeDeriv (p.1 : ℕ)) (primeDeriv_add (p.1 : ℕ))
    (primeDeriv_mul (p.1 : ℕ) p.1.2) (primeDeriv_algebraMap (p.1 : ℕ) p.1.2)
    (fun j : S => paperPrimeCoordinate j.1) P
  simp only [paperPrimePolynomialClock, CoordinateDerivation.coordinatePartial,
    CoordinateDerivation.transport_apply_image, paperPrimePolynomialEquiv_coe]
  rw [h]
  simp [hcoord]

/-- Clocks agree on overlapping finite-prime algebras under the literal inclusion. -/
theorem paperPrimePolynomialClock_inclusion {S T : Finset Nat.Primes} (h : S ⊆ T)
    (p : S) (f : paperPrimePolynomialAlgebra S) :
    paperPrimePolynomialClock T ⟨p.1, h p.2⟩
        (Subalgebra.inclusion (paperPrimePolynomialAlgebra_mono h) f) =
      Subalgebra.inclusion (paperPrimePolynomialAlgebra_mono h)
        (paperPrimePolynomialClock S p f) := by
  apply Subtype.ext
  calc
    (paperPrimePolynomialClock T ⟨p.1, h p.2⟩
        (Subalgebra.inclusion (paperPrimePolynomialAlgebra_mono h) f) : ArithmeticFunction ℂ) =
        primeDeriv (p.1 : ℕ)
          (Subalgebra.inclusion (paperPrimePolynomialAlgebra_mono h) f : ArithmeticFunction ℂ) :=
      paperPrimePolynomialClock_coe T ⟨p.1, h p.2⟩ _
    _ = primeDeriv (p.1 : ℕ) (f : ArithmeticFunction ℂ) :=
      congrArg (primeDeriv (p.1 : ℕ)) (Subalgebra.coe_inclusion _ f)
    _ = (paperPrimePolynomialClock S p f : ArithmeticFunction ℂ) :=
      (paperPrimePolynomialClock_coe S p f).symm
    _ = (Subalgebra.inclusion (paperPrimePolynomialAlgebra_mono h)
        (paperPrimePolynomialClock S p f) : ArithmeticFunction ℂ) :=
      (Subalgebra.coe_inclusion _ _).symm

/-- Every iterate is compatible with enlargement of the selected prime set. -/
theorem paperPrimePolynomialClock_iterate_inclusion {S T : Finset Nat.Primes}
    (h : S ⊆ T) (p : S) (f : paperPrimePolynomialAlgebra S) (m : ℕ) :
    ((paperPrimePolynomialClock T ⟨p.1, h p.2⟩ : paperPrimePolynomialAlgebra T →
      paperPrimePolynomialAlgebra T)^[m])
        (Subalgebra.inclusion (paperPrimePolynomialAlgebra_mono h) f) =
      Subalgebra.inclusion (paperPrimePolynomialAlgebra_mono h)
        (((paperPrimePolynomialClock S p : paperPrimePolynomialAlgebra S →
          paperPrimePolynomialAlgebra S)^[m]) f) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, paperPrimePolynomialClock_inclusion,
      Function.iterate_succ_apply']

/-- Joint prime-clock invariants are exactly the scalar convolution constants. -/
theorem paperPrimePolynomialClock_common_kernel (S : Finset Nat.Primes)
    (f : paperPrimePolynomialAlgebra S) :
    (∀ p : S, paperPrimePolynomialClock S p f = 0) ↔
      ∃ c : ℂ, f = algebraMap ℂ (paperPrimePolynomialAlgebra S) c := by
  constructor
  · intro h
    have hp : ∀ p : S, MvPolynomial.pderiv p ((paperPrimePolynomialEquiv S).symm f) = 0 := by
      intro p
      have he := congrArg (paperPrimePolynomialEquiv S).symm (h p)
      simpa only [paperPrimePolynomialClock_apply, AlgEquiv.symm_apply_apply, map_zero] using he
    obtain ⟨c, hc⟩ := exists_C_of_forall_pderiv_eq_zero hp
    refine ⟨c, (paperPrimePolynomialEquiv S).symm.injective ?_⟩
    simpa only [AlgEquiv.commutes, MvPolynomial.algebraMap_eq] using hc
  · rintro ⟨c, rfl⟩ p
    exact (paperPrimePolynomialClock S p).map_algebraMap c

/-- Source multiplier rigidity is exact on every finite-prime convolution chart. -/
theorem paperPrimePolynomialClock_multiplier_iff (S : Finset Nat.Primes) (p : S)
    (q : paperPrimePolynomialAlgebra S) :
    (∀ f : paperPrimePolynomialAlgebra S,
      ∃ m, (fun a => q * paperPrimePolynomialClock S p a)^[m] f = 0) ↔
      paperPrimePolynomialClock S p q = 0 := by
  letI : CharZero (paperPrimePolynomialAlgebra S) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (paperPrimePolynomialAlgebra S)).injective
  have h := paperLND_smul_iff (k := ℂ) (A := paperPrimePolynomialAlgebra S)
    (paperPrimePolynomialClock S p) (paperPrimePolynomialClock_locallyNilpotent S p) q
  change (∀ f : paperPrimePolynomialAlgebra S,
    ∃ m, (fun a => q * paperPrimePolynomialClock S p a)^[m] f = 0) ↔ _ at h
  exact h

end

end GaloisForLFunctions.HTGeometry
