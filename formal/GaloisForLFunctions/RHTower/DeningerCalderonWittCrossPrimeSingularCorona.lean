import GaloisForLFunctions.RHTower.DeningerCalderonWittAllCrossPrimeArithmeticSourceCompletion

/-!
# Singular corona of the all-cross-prime Calderon--Witt packet

The concrete cross-prime arithmetic source is the finite linear span of the
actual ordered Calderon--Witt witnesses.  Its image is dense in the packet
Hilbert space, so quotienting by its closure destroys every packet.  The
algebraic quotient by the source span itself is different: the normalized
full-support packet horizon is not finitely supported and survives.

This file constructs that singular quotient and proves the exact separation
needed by Route R:

* every finite actual arithmetic source packet has zero corona class;
* the full-support horizon has nonzero corona class;
* the simultaneous completed-Xi comparison becomes scalar multiplication of
  that nonzero class and is therefore coefficient-faithful.

The quotient is deliberately algebraic and non-Hausdorff with respect to the
ambient `ell^2` topology.  This is forced by the existing closed-relation
no-go: no continuous Hausdorff quotient can both kill the dense arithmetic
core and retain the horizon.
-/

open Complex Function Set Topology

namespace RHTower

noncomputable section

noncomputable local instance :
    DecidableEq DeningerCalderonWittCrossPrimePacketIndex :=
  Classical.decEq _

private def crossPrimePacketIndexOfPrime (p : Nat.Primes) :
    DeningerCalderonWittCrossPrimePacketIndex :=
  if hp : p = ⟨2, Nat.prime_two⟩ then
    ⟨(p, ⟨3, Nat.prime_three⟩), by
      intro h
      have hval := congrArg (fun r : Nat.Primes => r.1) h
      simp [hp] at hval⟩
  else
    ⟨(p, ⟨2, Nat.prime_two⟩), hp⟩

private theorem crossPrimePacketIndexOfPrime_first (p : Nat.Primes) :
    (crossPrimePacketIndexOfPrime p).1.1 = p := by
  rw [crossPrimePacketIndexOfPrime]
  split <;> rfl

private theorem crossPrimePacketIndexOfPrime_injective :
    Function.Injective crossPrimePacketIndexOfPrime := by
  intro p q h
  have hval := congrArg
    (fun i : DeningerCalderonWittCrossPrimePacketIndex => i.1.1) h
  simpa [crossPrimePacketIndexOfPrime_first] using hval

noncomputable local instance :
    Infinite DeningerCalderonWittCrossPrimePacketIndex :=
  Infinite.of_injective crossPrimePacketIndexOfPrime
    crossPrimePacketIndexOfPrime_injective

/-- Dense algebraic core consisting of the finite actual cross-prime source
packets. -/
def deningerCalderonWittCrossPrimeArithmeticPacketCore :
    Submodule ℂ DeningerCalderonWittCrossPrimePacketHilbert :=
  LinearMap.range deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert

/-- Singular algebraic corona of the completed cross-prime packet. -/
abbrev DeningerCalderonWittCrossPrimeSingularCorona :=
  DeningerCalderonWittCrossPrimePacketHilbert ⧸
    deningerCalderonWittCrossPrimeArithmeticPacketCore

/-- Canonical singular-corona projection. -/
def deningerCalderonWittCrossPrimeSingularCoronaClass :
    DeningerCalderonWittCrossPrimePacketHilbert →ₗ[ℂ]
      DeningerCalderonWittCrossPrimeSingularCorona :=
  deningerCalderonWittCrossPrimeArithmeticPacketCore.mkQ

/-- Every finite actual arithmetic source packet is zero in the singular
corona. -/
@[simp]
theorem deningerCalderonWittCrossPrimeSingularCoronaClass_sourceSpan
    (x : deningerCalderonWittCrossPrimeAlgebraicSourceSpan) :
    deningerCalderonWittCrossPrimeSingularCoronaClass
        (deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨x, rfl⟩

/-- The normalized full-support horizon is not a finite arithmetic source
packet. -/
theorem deningerCalderonWittCrossPrimePacketHorizon_not_mem_arithmeticCore :
    deningerCalderonWittCrossPrimePacketHorizon ∉
      deningerCalderonWittCrossPrimeArithmeticPacketCore := by
  rintro ⟨x, hx⟩
  let a : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
    deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan.symm x
  have hsource :
      deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x =
        deningerCalderonWittCrossPrimeAlgebraicPacketToHilbert a := by
    change deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x = _
    rw [show x =
        deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan a by
      exact
        (deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan
          |>.apply_symm_apply x).symm]
    exact deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_finsupp a
  rw [hsource] at hx
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset a.support
  have hcoord := congrArg
    (fun z : DeningerCalderonWittCrossPrimePacketHilbert => z i) hx
  rw [deningerCalderonWittCrossPrimeAlgebraicPacketToHilbert_apply,
    Finsupp.not_mem_support_iff.mp hi] at hcoord
  exact
    deningerCalderonWittCrossPrimePacketHorizon_apply_ne_zero i hcoord.symm

/-- Nonzero corona class of the full-support packet horizon. -/
def deningerCalderonWittCrossPrimeSingularCoronaHorizon :
    DeningerCalderonWittCrossPrimeSingularCorona :=
  deningerCalderonWittCrossPrimeSingularCoronaClass
    deningerCalderonWittCrossPrimePacketHorizon

theorem deningerCalderonWittCrossPrimeSingularCoronaHorizon_ne_zero :
    deningerCalderonWittCrossPrimeSingularCoronaHorizon ≠ 0 := by
  intro hzero
  exact deningerCalderonWittCrossPrimePacketHorizon_not_mem_arithmeticCore
    ((Submodule.Quotient.mk_eq_zero _).1 hzero)

/-- The killed arithmetic core is dense in the ambient Hilbert packet.  Thus
the nonzero quotient above is genuinely singular: replacing the core by its
topological closure would give the zero quotient. -/
theorem deningerCalderonWittCrossPrimeArithmeticPacketCore_dense :
    Dense
      (deningerCalderonWittCrossPrimeArithmeticPacketCore :
        Set DeningerCalderonWittCrossPrimePacketHilbert) := by
  exact deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_denseRange

/-- Completed-Xi coefficients landed in the singular corona. -/
def deningerCalderonWittSingularCoronaXiComparison :
    DeningerArithmeticCompletedH1 →ₗ[ℂ]
      (XiZeroCopy → DeningerCalderonWittCrossPrimeSingularCorona) where
  toFun x r :=
    x r • deningerCalderonWittCrossPrimeSingularCoronaHorizon
  map_add' x y := by
    funext r
    exact add_smul (x r) (y r) _
  map_smul' c x := by
    funext r
    exact mul_smul c (x r) _

/-- Pointwise quotient of the existing all-cross-prime completed comparison
is exactly the singular-corona comparison. -/
theorem deningerCalderonWittSingularCoronaXiComparison_eq_packetQuotient
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy) :
    deningerCalderonWittSingularCoronaXiComparison x r =
      deningerCalderonWittCrossPrimeSingularCoronaClass
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison x r) := by
  change
    x r • deningerCalderonWittCrossPrimeSingularCoronaHorizon =
      deningerCalderonWittCrossPrimeSingularCoronaClass
        (x r • deningerCalderonWittCrossPrimePacketHorizon)
  rw [map_smul]
  rfl

/-- The singular comparison retains the complete Xi coefficient: killing its
corona field kills the original completed coefficient and nothing else. -/
theorem deningerCalderonWittSingularCoronaXiComparison_injective :
    Function.Injective deningerCalderonWittSingularCoronaXiComparison := by
  intro x y hxy
  apply lp.ext
  funext r
  have hr := congrFun hxy r
  change
    x r • deningerCalderonWittCrossPrimeSingularCoronaHorizon =
      y r • deningerCalderonWittCrossPrimeSingularCoronaHorizon at hr
  have hzero :
      (x r - y r) • deningerCalderonWittCrossPrimeSingularCoronaHorizon = 0 := by
    rw [sub_smul, hr, sub_self]
  exact sub_eq_zero.mp
    ((smul_eq_zero.mp hzero).resolve_right
      deningerCalderonWittCrossPrimeSingularCoronaHorizon_ne_zero)

end

end RHTower
