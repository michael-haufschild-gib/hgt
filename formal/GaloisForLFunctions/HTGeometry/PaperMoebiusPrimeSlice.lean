import GaloisForLFunctions.HTGeometry.PaperMoebiusPrimeClock
import GaloisForLFunctions.HTGeometry.PaperComplexSliceFibers

/-!
# Möbius polynomial coordinates and all level fibres

The proven slice and fibre theorems apply to the normalized native prime
clock. The resulting variable is the literal Möbius function, and the
coefficient algebra is the actual p-free arithmetic-function algebra.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

attribute [local instance 2000] Algebra.toModule
attribute [local instance 2100] Semiring.toModule

private def moebiusConstantsEquiv (p : Nat.Primes) :
    complexDerivationKernel
        (B := paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property))
        (paperMoebiusPrimeClock p) ≃ₐ[ℂ] paperPrimeConstants p where
  toFun a := ⟨a.val.val, (paperPrimeConstants_mem_iff p _).mpr
    ((paperMoebiusPrimeClock_kernel_iff p a.val).mp a.property)⟩
  invFun a := ⟨⟨a.val, paperPrimeConstants_le_terminatingCore p a.property⟩,
    (paperMoebiusPrimeClock_kernel_iff p _).mpr
      ((paperPrimeConstants_mem_iff p _).mp a.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private def coordinateFiber {B C : Type*} [CommRing B] [Algebra ℂ B]
    [CommRing C] [Algebra ℂ C] (e : Polynomial C ≃ₐ[ℂ] B)
    (s : B) (hs : e Polynomial.X = s) (c : ℂ) :
    (B ⧸ Ideal.span {s - algebraMap ℂ B c}) ≃ₐ[ℂ] C :=
  (StableCoordinate.fiberQuotientEquiv e.symm s Polynomial.X (by
    apply e.injective
    rw [AlgEquiv.apply_symm_apply, hs]) c).trans
      ((Polynomial.quotientSpanXSubCAlgEquiv (algebraMap ℂ C c)).restrictScalars ℂ)

private theorem coordinateFiber_constant {B C : Type*} [CommRing B] [Algebra ℂ B]
    [CommRing C] [Algebra ℂ C] (e : Polynomial C ≃ₐ[ℂ] B)
    (s : B) (hs : e Polynomial.X = s) (c : ℂ) (a : C) :
    coordinateFiber e s hs c (Ideal.Quotient.mk _ (e (Polynomial.C a))) = a := by
  change (e.symm (e (Polynomial.C a))).eval (algebraMap ℂ C c) = a
  rw [AlgEquiv.symm_apply_apply, Polynomial.eval_C]

/-- The literal Möbius source is a polynomial coordinate on the entire prime core. -/
def paperMoebiusPrimeSlice (p : Nat.Primes) :
    Polynomial (paperPrimeConstants p) ≃ₐ[ℂ]
      paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property) := by
  have hs := paperMoebiusPrimeClock_moebius p
  have hnil : ∀ b : paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property),
      ∃ n : ℕ, (paperMoebiusPrimeClock p)^[n] b = 0 :=
    paperMoebiusPrimeClock_locallyNilpotent p
  let e := complexSliceAlgEquiv
    (B := paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property))
    (D := paperMoebiusPrimeClock p) (s := paperMoebiusInPrimeCore p)
    hs hnil
  exact (Polynomial.mapAlgEquiv (moebiusConstantsEquiv p).symm).trans e

@[simp] theorem paperMoebiusPrimeSlice_X (p : Nat.Primes) :
    (paperMoebiusPrimeSlice p Polynomial.X : ArithmeticFunction ℂ) =
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) := by
  simp [paperMoebiusPrimeSlice, paperMoebiusInPrimeCore]

@[simp] theorem paperMoebiusPrimeSlice_C (p : Nat.Primes) (a : paperPrimeConstants p) :
    (paperMoebiusPrimeSlice p (Polynomial.C a) : ArithmeticFunction ℂ) = a := by
  simp only [paperMoebiusPrimeSlice, AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv,
    Polynomial.map_C]
  change ((Polynomial.aeval (paperMoebiusInPrimeCore p)
    (Polynomial.C ((moebiusConstantsEquiv p).symm a)) :
      paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) :
        ArithmeticFunction ℂ) = a
  rw [Polynomial.aeval_C]
  rfl

/-- Unique Möbius polynomial expansions have the sharp bounded-exponent support domain. -/
theorem paperMoebiusPrimeSlice_unique_iff (p : Nat.Primes) (f : ArithmeticFunction ℂ) :
    (∃! P : Polynomial (paperPrimeConstants p),
      (paperMoebiusPrimeSlice p P : ArithmeticFunction ℂ) = f) ↔
        ∃ m : ℕ, ∀ n : ℕ, f n ≠ 0 → n.factorization (p : ℕ) < m := by
  rw [← paperPrimeTerminatingCore_support_iff]
  constructor
  · rintro ⟨P, hP, _⟩
    rw [← hP]
    exact (paperMoebiusPrimeSlice p P).property
  · intro hf
    obtain ⟨P, hP⟩ := (paperMoebiusPrimeSlice p).surjective ⟨f, hf⟩
    refine ⟨P, congrArg Subtype.val hP, ?_⟩
    intro Q hQ
    apply (paperMoebiusPrimeSlice p).injective
    exact (Subtype.ext hQ).trans hP.symm

/-- Every Möbius level fibre is the actual p-free coefficient algebra. -/
def paperMoebiusPrimeFiberEquiv (p : Nat.Primes) (c : ℂ) :=
  let hX : paperMoebiusPrimeSlice p Polynomial.X = paperMoebiusInPrimeCore p :=
    Subtype.ext (paperMoebiusPrimeSlice_X p)
  coordinateFiber
    (B := paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property))
    (C := paperPrimeConstants p) (paperMoebiusPrimeSlice p) (paperMoebiusInPrimeCore p)
    hX c

/-- The fibre identification fixes the original arithmetic constants. -/
@[simp] theorem paperMoebiusPrimeFiberEquiv_constant (p : Nat.Primes) (c : ℂ)
    (a : paperPrimeConstants p) :
    paperMoebiusPrimeFiberEquiv p c (Ideal.Quotient.mk _
      (⟨(a : ArithmeticFunction ℂ), paperPrimeConstants_le_terminatingCore p a.property⟩ :
        paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property))) = a := by
  have hX : paperMoebiusPrimeSlice p Polynomial.X = paperMoebiusInPrimeCore p :=
    Subtype.ext (paperMoebiusPrimeSlice_X p)
  have h := coordinateFiber_constant
    (B := paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property))
    (C := paperPrimeConstants p) (paperMoebiusPrimeSlice p) (paperMoebiusInPrimeCore p)
    hX c a
  have hC : paperMoebiusPrimeSlice p (Polynomial.C a) =
      ⟨(a : ArithmeticFunction ℂ), paperPrimeConstants_le_terminatingCore p a.property⟩ :=
    Subtype.ext (paperMoebiusPrimeSlice_C p a)
  rw [hC] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
