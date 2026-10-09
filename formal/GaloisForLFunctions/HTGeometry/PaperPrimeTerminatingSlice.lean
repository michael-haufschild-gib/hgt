import GaloisForLFunctions.HTGeometry.PaperPrimeTerminatingSupport
import GaloisForLFunctions.HTGeometry.PaperComplexDerivationSlice

/-!
# Polynomial coordinates on the entire prime-terminating algebra

The native prime coordinate is a slice on the maximal terminating core.
The proven slice theorem therefore gives a polynomial presentation over the
actual ambient prime constants, whose support excludes multiples of the prime.
No finite-prime support restriction is imposed on the coefficient algebra.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

attribute [local instance 2000] Algebra.toModule
attribute [local instance 2100] Semiring.toModule

/-- The full ambient coefficient algebra for one prime direction. -/
def paperPrimeConstants (p : Nat.Primes) : Subalgebra ℂ (ArithmeticFunction ℂ) :=
  complexDerivationKernel (primeArithmeticDerivation (p : ℕ) p.property)

/-- The coefficient algebra has an exact divisibility description. -/
theorem paperPrimeConstants_mem_iff (p : Nat.Primes) (f : ArithmeticFunction ℂ) :
    f ∈ paperPrimeConstants p ↔ ∀ n : ℕ, (p : ℕ) ∣ n → f n = 0 :=
  paperPrimeArithmetic_kernel_iff p f

/-- Every ambient prime constant belongs to the maximal terminating algebra. -/
theorem paperPrimeConstants_le_terminatingCore (p : Nat.Primes) :
    paperPrimeConstants p ≤
      paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property) := by
  intro f hf
  exact (paperTerminatingCore_mem_iff _ f).mpr ⟨1, hf⟩

private def constantsEquiv (p : Nat.Primes) :
    complexDerivationKernel
        (B := paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property))
        (paperTerminatingClock (primeArithmeticDerivation (p : ℕ) p.property)) ≃ₐ[ℂ]
      paperPrimeConstants p where
  toFun a := ⟨a.val.val, congrArg Subtype.val a.property⟩
  invFun a := ⟨⟨a.val, paperPrimeConstants_le_terminatingCore p a.property⟩,
    Subtype.ext a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The literal native prime coordinate, regarded as an element of the full core. -/
def paperPrimeTerminatingGenerator (p : Nat.Primes) :
    paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property) :=
  ⟨paperPrimeCoordinate p, by
    apply (paperTerminatingCore_mem_iff _ _).mpr
    refine ⟨2, ?_⟩
    change primeArithmeticDerivation (p : ℕ) p.property
      (primeArithmeticDerivation (p : ℕ) p.property (paperPrimeCoordinate p)) = 0
    have h : primeArithmeticDerivation (p : ℕ) p.property (paperPrimeCoordinate p) = 1 := by
      simp [primeArithmeticDerivation_apply, paperPrimeCoordinate_primeDeriv]
    rw [h]
    simp⟩

/-- The core clock has an unconditional slice. -/
@[simp] theorem paperPrimeTerminatingGenerator_clock (p : Nat.Primes) :
    paperTerminatingClock (primeArithmeticDerivation (p : ℕ) p.property)
      (paperPrimeTerminatingGenerator p) = 1 := by
  apply Subtype.ext
  simp [paperPrimeTerminatingGenerator, primeArithmeticDerivation_apply,
    paperPrimeCoordinate_primeDeriv]

/-- All bounded-prime-exponent arithmetic functions form a polynomial algebra over prime constants. -/
def paperPrimeTerminatingSlice (p : Nat.Primes) :
    Polynomial (paperPrimeConstants p) ≃ₐ[ℂ]
      paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property) := by
  let D := primeArithmeticDerivation (p : ℕ) p.property
  have hs := paperPrimeTerminatingGenerator_clock p
  have hnil : ∀ b : paperTerminatingCore D, ∃ n : ℕ,
      ((paperTerminatingClock D : paperTerminatingCore D → paperTerminatingCore D)^[n]) b = 0 :=
    paperTerminatingClock_locallyNilpotent D
  let e := complexSliceAlgEquiv (B := paperTerminatingCore D)
    (D := paperTerminatingClock D) (s := paperPrimeTerminatingGenerator p) hs hnil
  exact (Polynomial.mapAlgEquiv (constantsEquiv p).symm).trans e

/-- The polynomial variable lands on the original arithmetic prime coordinate. -/
@[simp] theorem paperPrimeTerminatingSlice_X (p : Nat.Primes) :
    (paperPrimeTerminatingSlice p Polynomial.X : ArithmeticFunction ℂ) =
      paperPrimeCoordinate p := by
  simp [paperPrimeTerminatingSlice, paperPrimeTerminatingGenerator]

/-- The presentation preserves the actual arithmetic coefficient functions. -/
@[simp] theorem paperPrimeTerminatingSlice_C (p : Nat.Primes) (a : paperPrimeConstants p) :
    (paperPrimeTerminatingSlice p (Polynomial.C a) : ArithmeticFunction ℂ) = a := by
  simp only [paperPrimeTerminatingSlice, AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv,
    Polynomial.map_C]
  change ((Polynomial.aeval (paperPrimeTerminatingGenerator p)
    (Polynomial.C ((constantsEquiv p).symm a)) :
      paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) :
        ArithmeticFunction ℂ) = a
  rw [Polynomial.aeval_C]
  rfl

/-- A unique finite expansion exists exactly on the sharp support boundary. -/
theorem paperPrimeTerminatingSlice_unique_iff (p : Nat.Primes) (f : ArithmeticFunction ℂ) :
    (∃! P : Polynomial (paperPrimeConstants p),
      (paperPrimeTerminatingSlice p P : ArithmeticFunction ℂ) = f) ↔
        ∃ m : ℕ, ∀ n : ℕ, f n ≠ 0 → n.factorization (p : ℕ) < m := by
  rw [← paperPrimeTerminatingCore_support_iff]
  constructor
  · rintro ⟨P, hP, _⟩
    rw [← hP]
    exact (paperPrimeTerminatingSlice p P).property
  · intro hf
    obtain ⟨P, hP⟩ := (paperPrimeTerminatingSlice p).surjective ⟨f, hf⟩
    refine ⟨P, congrArg Subtype.val hP, ?_⟩
    intro Q hQ
    apply (paperPrimeTerminatingSlice p).injective
    exact (Subtype.ext hQ).trans hP.symm

end

end GaloisForLFunctions.HTGeometry
