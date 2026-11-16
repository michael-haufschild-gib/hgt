import Mathlib.FieldTheory.Finite.Trace
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Additive characters pulled back through finite-field traces

Trace pullback preserves nontriviality and is compatible with towers.
It is invariant under every automorphism over the base field, hence
under every power of the relative Frobenius.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K L R : Type*} [Field K] [Field L] [CommMonoid R]
    [Fintype K] [Finite L] [Algebra K L]

/-- Pullback of an additive character through the actual finite-field trace. -/
def finiteFieldTraceCharacter (ψ : AddChar K R) : AddChar L R :=
  ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom

/-- Surjectivity of the trace makes pullback injective on additive characters. -/
theorem finiteFieldTraceCharacter_injective :
    Function.Injective (finiteFieldTraceCharacter (K := K) (L := L) (R := R)) := by
  intro ψ φ h
  apply AddChar.ext
  intro a
  obtain ⟨x, rfl⟩ := Algebra.trace_surjective K L a
  exact DFunLike.congr_fun h x

/-- Trace pullback preserves and reflects nontriviality of additive characters. -/
theorem finiteFieldTraceCharacter_ne_one_iff (ψ : AddChar K R) :
    finiteFieldTraceCharacter (L := L) ψ ≠ 1 ↔ ψ ≠ 1 := by
  have hone : finiteFieldTraceCharacter (L := L) (1 : AddChar K R) = 1 := rfl
  rw [← hone]
  constructor
  · rintro h rfl
    exact h rfl
  · intro h hf
    exact h (finiteFieldTraceCharacter_injective hf)

/-- A nontrivial character becomes a primitive character on every finite extension by trace pullback. -/
theorem finiteFieldTraceCharacter_primitive (ψ : AddChar K R) (hψ : ψ ≠ 1) :
    (finiteFieldTraceCharacter (L := L) ψ).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one ((finiteFieldTraceCharacter_ne_one_iff ψ).mpr hψ)

omit [Fintype K] [Finite L] in
/-- Every base-field automorphism preserves a trace-pulled additive character. -/
theorem finiteFieldTraceCharacter_algEquiv (ψ : AddChar K R) (σ : L ≃ₐ[K] L) (x : L) :
    finiteFieldTraceCharacter ψ (σ x) = finiteFieldTraceCharacter ψ x :=
  congrArg ψ (Algebra.trace_eq_of_algEquiv σ x)

omit [Fintype K] in
/-- Pulling an additive character through a tower of traces equals direct trace pullback. -/
theorem finiteFieldTraceCharacter_tower
    {M : Type*} [Field M] [Finite M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Fintype L] (ψ : AddChar K R) :
    finiteFieldTraceCharacter (L := M) (finiteFieldTraceCharacter (L := L) ψ) =
      finiteFieldTraceCharacter (L := M) ψ := by
  apply AddChar.ext
  intro x
  change ψ (Algebra.trace K L (Algebra.trace L M x)) = ψ (Algebra.trace K M x)
  rw [Algebra.trace_trace]

/-- Every power of the relative Frobenius fixes a trace-pulled additive character. -/
theorem finiteFieldTraceCharacter_frobenius (ψ : AddChar K R) (e : ℕ) (x : L) :
    finiteFieldTraceCharacter ψ (x ^ (Fintype.card K ^ e)) = finiteFieldTraceCharacter ψ x := by
  have hstep (y : L) : finiteFieldTraceCharacter ψ (y ^ Fintype.card K) =
      finiteFieldTraceCharacter ψ y :=
    finiteFieldTraceCharacter_algEquiv ψ (FiniteField.frobeniusAlgEquivOfAlgebraic K L) y
  induction e with
  | zero => rw [pow_zero, pow_one]
  | succ e ih => rw [pow_succ, pow_mul, hstep, ih]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
