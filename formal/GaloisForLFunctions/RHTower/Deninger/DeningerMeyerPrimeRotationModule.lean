import GaloisForLFunctions.HTGeometry.RotationInducedArithmeticModule
import GaloisForLFunctions.RHTower.PrimeRotationCanonicalTraceIntegrality
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHalfDensityFiniteXiJetVerticalDefect

/-!
# The actual Meyer arithmetic source as a prime rotation module

Clock induction applies to literal centered Meyer dilation. It descends
through the coefficientwise global Poisson boundary, with precisely that
boundary as kernel, and maps equivariantly onto every finite full Xi jet
packet. The packet has an explicit finite free cover. No projectivity,
completed C*-action, spectral synthesis, or Chern identity is assumed.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open scoped Classical

/-- Literal centered prime dilation on Meyer cohomology, including all integer powers. -/
def deningerMeyerPrimeIntegerFlow (p : Nat.Primes) :
    IntegerLinearFlow DeningerMeyerStrongLogCohomology where
  toFun b := deningerMeyerStrongLogCenteredCohomologyFlow
    (-((Multiplicative.toAdd b : ℤ) : ℝ) * Real.log p)
  map_one' := by
    apply LinearMap.ext
    intro u
    simp only [toAdd_one, Int.cast_zero, neg_zero, zero_mul, Module.End.one_apply,
      deningerMeyerStrongLogCenteredCohomologyFlow_zero]
  map_mul' a b := by
    apply LinearMap.ext
    intro u
    change deningerMeyerStrongLogCenteredCohomologyFlow
      (-((Multiplicative.toAdd a + Multiplicative.toAdd b : ℤ) : ℝ) * Real.log p) u =
      deningerMeyerStrongLogCenteredCohomologyFlow (-((Multiplicative.toAdd a : ℤ) : ℝ) * Real.log p)
        (deningerMeyerStrongLogCenteredCohomologyFlow (-((Multiplicative.toAdd b : ℤ) : ℝ) * Real.log p) u)
    rw [deningerMeyerStrongLogCenteredCohomologyFlow_add]
    congr 1
    push_cast
    ring_nf

/-- The full integer clock family of actual Meyer Poisson cohomology. -/
abbrev DeningerMeyerPrimeClockSource := ℤ →₀ DeningerMeyerStrongLogCohomology

private theorem prime_phase_infinite (p : Nat.Primes) (q : ℕ) (b : ℤ) :
    paperRotationPhase ((b : ℝ) * paperPrimeRotationFrequency p (q + 1)) = 1 ↔ b = 0 := by
  simpa only [Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or] using
    paperPrimeRotationPhase_int_eq_one p (q + 1) b

/-- Actual native prime rotation representation on the arithmetic clock source. -/
def deningerMeyerPrimeRotationRepresentation (p : Nat.Primes) (q : ℕ) :
    paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1)) →ₐ[ℂ]
      Module.End ℂ DeningerMeyerPrimeClockSource :=
  rotationInducedRepresentation _ (prime_phase_infinite p q) (deningerMeyerPrimeIntegerFlow p)

/-- Word action retains the actual centered Meyer dilation in every clock fiber. -/
theorem deningerMeyerPrimeRotationRepresentation_word_single
    (p : Nat.Primes) (q : ℕ) (a b n : ℤ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPrimeRotationRepresentation p q
      (paperRotationPolynomialWord (paperPrimeRotationFrequency p (q + 1)) a b)
      (Finsupp.single n u) =
        Finsupp.single (n + a)
          (paperRotationPhase ((b : ℝ) * paperPrimeRotationFrequency p (q + 1) *
            ((n + a : ℤ) : ℝ)) •
              deningerMeyerStrongLogCenteredCohomologyFlow (-(b : ℝ) * Real.log p) u) := by
  rw [deningerMeyerPrimeRotationRepresentation, rotationInducedRepresentation_word,
    rotationInducedWord_single]
  rfl

/-- Exact centered prime flow on every full finite Xi jet packet. -/
def deningerMeyerXiPacketPrimeIntegerFlow (p : Nat.Primes) (S : Finset XiDivisorSupport) :
    IntegerLinearFlow (DeningerMeyerFiniteXiJetPacket S) where
  toFun b := deningerMeyerFiniteXiJetPacketCenteredFlow S
    (-((Multiplicative.toAdd b : ℤ) : ℝ) * Real.log p)
  map_one' := by
    apply LinearMap.ext
    intro x
    simp only [toAdd_one, Int.cast_zero, neg_zero, zero_mul, Module.End.one_apply,
      deningerMeyerFiniteXiJetPacketCenteredFlow_zero]
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    change deningerMeyerFiniteXiJetPacketCenteredFlow S
      (-((Multiplicative.toAdd a + Multiplicative.toAdd b : ℤ) : ℝ) * Real.log p) x =
      deningerMeyerFiniteXiJetPacketCenteredFlow S (-((Multiplicative.toAdd a : ℤ) : ℝ) * Real.log p)
        (deningerMeyerFiniteXiJetPacketCenteredFlow S (-((Multiplicative.toAdd b : ℤ) : ℝ) * Real.log p) x)
    rw [deningerMeyerFiniteXiJetPacketCenteredFlow_add]
    congr 1
    push_cast
    ring_nf

/-- Every selected jet, at every integer clock step. -/
abbrev DeningerMeyerXiClockPacket (S : Finset XiDivisorSupport) :=
  ℤ →₀ DeningerMeyerFiniteXiJetPacket S

def deningerMeyerXiClockRepresentation (p : Nat.Primes) (q : ℕ) (S : Finset XiDivisorSupport) :
    paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1)) →ₐ[ℂ]
      Module.End ℂ (DeningerMeyerXiClockPacket S) :=
  rotationInducedRepresentation _ (prime_phase_infinite p q)
    (deningerMeyerXiPacketPrimeIntegerFlow p S)

/-- Coefficientwise literal Xi jet observation of the arithmetic source. -/
def deningerMeyerXiClockEvaluation (S : Finset XiDivisorSupport) :
    DeningerMeyerPrimeClockSource →ₗ[ℂ] DeningerMeyerXiClockPacket S :=
  Finsupp.mapRange.linearMap (deningerMeyerFiniteXiJetPacketLM S)

@[simp] theorem deningerMeyerXiClockEvaluation_apply (S : Finset XiDivisorSupport)
    (x : DeningerMeyerPrimeClockSource) (n : ℤ) :
    deningerMeyerXiClockEvaluation S x n = deningerMeyerFiniteXiJetPacketLM S (x n) := rfl

/-- Full multiplicity packets are actual equivariant quotients, with no synthesis premise. -/
theorem deningerMeyerXiClockEvaluation_surjective (S : Finset XiDivisorSupport) :
    Function.Surjective (deningerMeyerXiClockEvaluation S) :=
  Finsupp.mapRange_surjective _ (map_zero (deningerMeyerFiniteXiJetPacketLM S))
    (deningerMeyerFiniteXiJetPacketLM_surjective S)

theorem deningerMeyerXiClockEvaluation_equivariant (p : Nat.Primes) (q : ℕ)
    (S : Finset XiDivisorSupport)
    (A : paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1)))
    (x : DeningerMeyerPrimeClockSource) :
    deningerMeyerXiClockEvaluation S (deningerMeyerPrimeRotationRepresentation p q A x) =
      deningerMeyerXiClockRepresentation p q S A (deningerMeyerXiClockEvaluation S x) := by
  apply rotationInducedRepresentation_natural
  intro b u
  exact deningerMeyerFiniteXiJetPacketLM_centeredFlow S (-(b : ℝ) * Real.log p) u

/-- A finite free cover with one clock-zero generator for each actual multiplicity-bounded jet. -/
def deningerMeyerXiClockFreeCover (p : Nat.Primes) (q : ℕ) (S : Finset XiDivisorSupport) :
    (DeningerMeyerFiniteXiJetSlot S →
      paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1))) →ₗ[ℂ]
        DeningerMeyerXiClockPacket S :=
  rotationInducedFreeCover _ (prime_phase_infinite p q)
    (deningerMeyerXiPacketPrimeIntegerFlow p S) (Pi.basisFun ℂ _)

theorem deningerMeyerXiClockFreeCover_surjective (p : Nat.Primes) (q : ℕ)
    (S : Finset XiDivisorSupport) : Function.Surjective (deningerMeyerXiClockFreeCover p q S) :=
  rotationInducedFreeCover_surjective _ _ _ _

theorem deningerMeyerXiClockFreeCover_equivariant (p : Nat.Primes) (q : ℕ)
    (S : Finset XiDivisorSupport)
    (A : paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1)))
    (C : DeningerMeyerFiniteXiJetSlot S →
      paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1))) :
    deningerMeyerXiClockRepresentation p q S A (deningerMeyerXiClockFreeCover p q S C) =
      deningerMeyerXiClockFreeCover p q S (fun i => A * C i) :=
  rotationInducedFreeCover_equivariant _ _ _ _ _ _

/-- The integer family of actual all-weight target representatives. -/
abbrev DeningerMeyerPrimeClockTarget := ℤ →₀ DeningerMeyerStrongLogTarget

/-- Literal Poisson boundary on every clock fiber. -/
def deningerMeyerClockBoundary :
    (ℤ →₀ DeningerMeyerCap) →ₗ[ℂ] DeningerMeyerPrimeClockTarget :=
  Finsupp.mapRange.linearMap deningerMeyerStrongLogSumLM

/-- Quotient by the actual Poisson range on every clock fiber. -/
def deningerMeyerClockQuotient :
    DeningerMeyerPrimeClockTarget →ₗ[ℂ] DeningerMeyerPrimeClockSource :=
  Finsupp.mapRange.linearMap (LinearMap.range deningerMeyerStrongLogSumLM).mkQ

theorem deningerMeyerClockQuotient_surjective :
    Function.Surjective deningerMeyerClockQuotient :=
  Finsupp.mapRange_surjective _ (map_zero (LinearMap.range deningerMeyerStrongLogSumLM).mkQ)
    (Submodule.mkQ_surjective _)

/-- No new source relations are introduced by clock induction: the kernel is exactly the
coefficientwise literal Poisson boundary. -/
theorem deningerMeyerClockQuotient_ker :
    LinearMap.ker deningerMeyerClockQuotient = LinearMap.range deningerMeyerClockBoundary := by
  apply le_antisymm
  · intro x hx
    have hx0 : ∀ n : ℤ, (LinearMap.range deningerMeyerStrongLogSumLM).mkQ (x n) = 0 := by
      intro n
      exact congrArg (fun z : DeningerMeyerPrimeClockSource => z n) hx
    have hxrange : ∀ n, ∃ f : DeningerMeyerCap, deningerMeyerStrongLogSumLM f = x n := by
      intro n
      exact (Submodule.Quotient.mk_eq_zero _).mp (hx0 n)
    choose f hf using hxrange
    let y : ℤ →₀ DeningerMeyerCap := Finsupp.onFinset x.support
      (fun n => if n ∈ x.support then f n else 0)
      (by intro n h; by_contra hn; exact h (if_neg hn))
    refine ⟨y, ?_⟩
    apply Finsupp.ext
    intro n
    change deningerMeyerStrongLogSumLM (y n) = x n
    dsimp [y]
    by_cases hn : n ∈ x.support
    · rw [if_pos hn, hf]
    · rw [if_neg hn, map_zero, Finsupp.notMem_support_iff.mp hn]
  · rintro _ ⟨f, rfl⟩
    apply Finsupp.ext
    intro n
    change (LinearMap.range deningerMeyerStrongLogSumLM).mkQ (deningerMeyerStrongLogSumLM (f n)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨f n, rfl⟩

/-- Centered prime flow before taking the arithmetic quotient. -/
def deningerMeyerTargetPrimeIntegerFlow (p : Nat.Primes) :
    IntegerLinearFlow DeningerMeyerStrongLogTarget where
  toFun b := deningerMeyerStrongLogCenteredFlow (-((Multiplicative.toAdd b : ℤ) : ℝ) * Real.log p)
  map_one' := by
    apply LinearMap.ext
    intro g
    simp only [toAdd_one, Int.cast_zero, neg_zero, zero_mul, Module.End.one_apply,
      deningerMeyerStrongLogCenteredFlow_zero]
  map_mul' a b := by
    apply LinearMap.ext
    intro g
    change deningerMeyerStrongLogCenteredFlow
      (-((Multiplicative.toAdd a + Multiplicative.toAdd b : ℤ) : ℝ) * Real.log p) g =
      deningerMeyerStrongLogCenteredFlow (-((Multiplicative.toAdd a : ℤ) : ℝ) * Real.log p)
        (deningerMeyerStrongLogCenteredFlow (-((Multiplicative.toAdd b : ℤ) : ℝ) * Real.log p) g)
    rw [deningerMeyerStrongLogCenteredFlow_add]
    congr 1
    push_cast
    ring_nf

def deningerMeyerTargetRotationRepresentation (p : Nat.Primes) (q : ℕ) :
    paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1)) →ₐ[ℂ]
      Module.End ℂ DeningerMeyerPrimeClockTarget :=
  rotationInducedRepresentation _ (prime_phase_infinite p q) (deningerMeyerTargetPrimeIntegerFlow p)

/-- The rotation action descends through the literal global Poisson boundary. -/
theorem deningerMeyerClockQuotient_equivariant (p : Nat.Primes) (q : ℕ)
    (A : paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1)))
    (x : DeningerMeyerPrimeClockTarget) :
    deningerMeyerClockQuotient (deningerMeyerTargetRotationRepresentation p q A x) =
      deningerMeyerPrimeRotationRepresentation p q A (deningerMeyerClockQuotient x) := by
  apply rotationInducedRepresentation_natural
  intro b g
  exact (deningerMeyerStrongLogCenteredCohomologyFlow_mk (-(b : ℝ) * Real.log p) g).symm

/-- Every actual arithmetic boundary is preserved by every finite prime-Weyl operator. -/
theorem deningerMeyerClockBoundary_invariant (p : Nat.Primes) (q : ℕ)
    (A : paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1)))
    {x : DeningerMeyerPrimeClockTarget} (hx : x ∈ LinearMap.range deningerMeyerClockBoundary) :
    deningerMeyerTargetRotationRepresentation p q A x ∈ LinearMap.range deningerMeyerClockBoundary := by
  rw [← deningerMeyerClockQuotient_ker, LinearMap.mem_ker] at hx ⊢
  rw [deningerMeyerClockQuotient_equivariant, hx, map_zero]

end
end RHTower
