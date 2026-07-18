import GaloisForLFunctions.HTGeometry.SeparatedRayTailPacket
import GaloisForLFunctions.HTGeometry.PrimeProfileJetPacket

/-!
# Exact ray-tail criterion for arbitrary prime-profile packets

The cofinite packet hypothesis used by the dynamic Jacobian is not extra geometry.  It is exactly
linear independence of every finite profile-jet rectangle modulo finitely many prime rays.  The
nontrivial reverse direction uses the separated-ray transversal theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix

noncomputable section

/-- Scalar row of a profile jet at one prime direction and one valuation coordinate. -/
def primeProfileJetRayCoefficient
    {I : Type*} [Fintype I]
    (g : I -> ArithmeticFunction ℂ) (m : Nat)
    (col : I × Fin (m + 1)) (p : Nat.Primes) (e : Nat) : ℂ :=
  primeDeriv p.1 (primeProfileJetSource g m col) ((p : Nat) ^ e)

/-- Linear independence of one finite jet rectangle modulo finitely many prime rays. -/
def PrimeProfileJetRayTailIndependent
    {I : Type*} [Fintype I]
    (g : I -> ArithmeticFunction ℂ) (m : Nat) : Prop :=
  RayTailCoefficientIndependent (primeProfileJetRayCoefficient g m)

/-- Ray-tail independence produces the cofinite separated packet at the selected jet order. -/
theorem cofinitePrimeProfileJetPacket_at_of_rayTailIndependent
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> ArithmeticFunction ℂ) (m : Nat)
    (h : PrimeProfileJetRayTailIndependent g m)
    (forbidden : Set Nat.Primes) (hforbidden : forbidden.Finite) :
    ∃ (q : I × Fin (m + 1) -> Nat.Primes)
      (e : I × Fin (m + 1) -> Nat),
      Function.Injective q ∧
      (∀ row, q row ∉ forbidden) ∧
      (primeProfileJetPacketMatrix g m q e).det ≠ 0 := by
  obtain ⟨q, e, hq, havoid, hunit⟩ :=
    h.exists_separated_fullRank_packet_avoiding
      (primeProfileJetRayCoefficient g m) forbidden hforbidden
  refine ⟨q, e, hq, havoid, ?_⟩
  have hdetUnit : IsUnit (primeProfileJetPacketMatrix g m q e).det := by
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    simpa [primeProfileJetPacketMatrix, primeProfileJetRayCoefficient,
      Matrix.of_apply] using hunit
  exact hdetUnit.ne_zero

/-- A cofinite packet at one jet order forces ray-tail independence at that order. -/
theorem rayTailIndependent_of_cofinitePrimeProfileJetPacket_at
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> ArithmeticFunction ℂ) (m : Nat)
    (hpacket : ∀ (forbidden : Set Nat.Primes), forbidden.Finite ->
      ∃ (q : I × Fin (m + 1) -> Nat.Primes)
        (e : I × Fin (m + 1) -> Nat),
        Function.Injective q ∧
        (∀ row, q row ∉ forbidden) ∧
        (primeProfileJetPacketMatrix g m q e).det ≠ 0) :
    PrimeProfileJetRayTailIndependent g m := by
  intro c hactive
  obtain ⟨q, e, _hq, havoid, hdet⟩ := hpacket _ hactive
  let M : Matrix (I × Fin (m + 1)) (I × Fin (m + 1)) ℂ :=
    primeProfileJetPacketMatrix g m q e
  have hunit : IsUnit M := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    exact isUnit_iff_ne_zero.mpr hdet
  have hmul : M.mulVec c = 0 := by
    funext row
    have hzero :
        ∑ col, c col * primeProfileJetRayCoefficient g m col (q row) (e row) = 0 := by
      by_contra hne
      apply havoid row
      exact ⟨e row, hne⟩
    simpa [M, Matrix.mulVec, dotProduct, primeProfileJetPacketMatrix,
      primeProfileJetRayCoefficient, mul_comm] using hzero
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  exact hinj (by simpa using hmul)

/-- **Exact profile-packet criterion.**  Cofinite separated packets at every finite jet order are
equivalent to ray-tail independence of every finite jet rectangle. -/
theorem cofinitePrimeProfileJetPacket_iff_rayTailIndependent
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> ArithmeticFunction ℂ) :
    CofinitePrimeProfileJetPacket g ↔
      ∀ m, PrimeProfileJetRayTailIndependent g m := by
  constructor
  · intro hpacket m
    apply rayTailIndependent_of_cofinitePrimeProfileJetPacket_at g m
    intro forbidden hforbidden
    exact hpacket m forbidden hforbidden
  · intro htail m forbidden hforbidden
    exact cofinitePrimeProfileJetPacket_at_of_rayTailIndependent
      g m (htail m) forbidden hforbidden

end

end GaloisForLFunctions.HTGeometry
