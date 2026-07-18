import GaloisForLFunctions.HTGeometry.SeparatedRayTailPacket
import GaloisForLFunctions.HTGeometry.PrimeProfileJetPacket
import GaloisForLFunctions.HTGeometry.PrimeProfileTailMatroid

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

/-- Finite linear combinations of jet rows are read by the prime derivation of the corresponding
finite linear combination of arithmetic jet sources. -/
theorem sum_primeProfileJetRayCoefficient_eq
    {I : Type*} [Fintype I]
    (g : I -> ArithmeticFunction ℂ) (m : Nat)
    (c : I × Fin (m + 1) -> ℂ) (p : Nat.Primes) (e : Nat) :
    ∑ col, c col * primeProfileJetRayCoefficient g m col p e =
      primeDeriv p.1 (∑ col, c col • primeProfileJetSource g m col)
        ((p : Nat) ^ e) := by
  have hlinear := congrArg
    (fun f : ArithmeticFunction ℂ => f ((p : Nat) ^ e))
    (primeDeriv_profileLinearCombination p (primeProfileJetSource g m) c)
  calc
    ∑ col, c col * primeProfileJetRayCoefficient g m col p e =
        (∑ col, c col • primeDeriv p.1 (primeProfileJetSource g m col))
          ((p : Nat) ^ e) := by
      let ev : ArithmeticFunction ℂ →+ ℂ :=
        { toFun := fun f => f ((p : Nat) ^ e)
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      rw [show (∑ col, c col • primeDeriv p.1 (primeProfileJetSource g m col))
          ((p : Nat) ^ e) =
          ∑ col, (c col • primeDeriv p.1 (primeProfileJetSource g m col))
            ((p : Nat) ^ e) by
        exact map_sum ev _ Finset.univ]
      simp [ArithmeticFunction.smul_map, smul_eq_mul,
        primeProfileJetRayCoefficient]
    _ = primeDeriv p.1 (∑ col, c col • primeProfileJetSource g m col)
        ((p : Nat) ^ e) := hlinear.symm

/-- The active prime rays detected by a finite jet-row combination are exactly the active rays of
the corresponding arithmetic profile. -/
theorem primeProfileJetRayActivity_eq
    {I : Type*} [Fintype I]
    (g : I -> ArithmeticFunction ℂ) (m : Nat)
    (c : I × Fin (m + 1) -> ℂ) :
    {p : Nat.Primes |
      ∃ e : Nat,
        ∑ col, c col * primeProfileJetRayCoefficient g m col p e ≠ 0} =
    {p : Nat.Primes |
      ∃ e : Nat,
        (∑ col, c col • primeProfileJetSource g m col)
          ((p : Nat) ^ (e + 1)) ≠ 0} := by
  calc
    {p : Nat.Primes |
        ∃ e : Nat,
          ∑ col, c col * primeProfileJetRayCoefficient g m col p e ≠ 0} =
      {p : Nat.Primes |
        ∃ e : Nat,
          primeDeriv p.1 (∑ col, c col • primeProfileJetSource g m col)
            ((p : Nat) ^ e) ≠ 0} := by
        ext p
        simp_rw [sum_primeProfileJetRayCoefficient_eq]
    _ = {p : Nat.Primes |
        ∃ e : Nat,
          (∑ col, c col • primeProfileJetSource g m col)
            ((p : Nat) ^ (e + 1)) ≠ 0} :=
      primeDeriv_rayActivity_eq _

/-- The ray-tail packet predicate is exactly linear independence of the finite jet rectangle in
the quotient by finite-prime profiles. -/
theorem primeProfileJetRayTailIndependent_iff_tailIndependent
    {I : Type*} [Fintype I]
    (g : I -> ArithmeticFunction ℂ) (m : Nat) :
    PrimeProfileJetRayTailIndependent g m ↔
      PrimeProfileTailIndependent (primeProfileJetSource g m) := by
  constructor
  · intro h c hlocal
    apply h c
    rw [primeProfileJetRayActivity_eq]
    exact (primePowerClockLocal_coordinateProfile_iff _).mp hlocal
  · intro h c hactive
    apply h c
    apply (primePowerClockLocal_coordinateProfile_iff _).mpr
    rw [← primeProfileJetRayActivity_eq]
    exact hactive

/-- Logarithmic jets preserve positive-prime-power support. -/
theorem primeProfileRotatedLogJet_supportedOnPositivePrimePowers
    (f : ArithmeticFunction ℂ)
    (hsupport : PrimeProfileSupportedOnPositivePrimePowers f) (k : Nat) :
    PrimeProfileSupportedOnPositivePrimePowers (primeProfileRotatedLogJet k f) := by
  intro n hn
  apply hsupport
  intro hz
  apply hn
  rw [primeProfileRotatedLogJet_apply, hz, mul_zero]

/-- Every member of a finite profile-jet rectangle remains supported on positive prime powers. -/
theorem primeProfileJetSource_supportedOnPositivePrimePowers
    {I : Type*} (g : I -> ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i))
    (m : Nat) (col : I × Fin (m + 1)) :
    PrimeProfileSupportedOnPositivePrimePowers (primeProfileJetSource g m col) := by
  exact primeProfileRotatedLogJet_supportedOnPositivePrimePowers
    (g col.1) (hsupport col.1) col.2

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

/-- **Exact absolute prime-clock differential matroid.**  Differential independence of arbitrary
positive-prime-power profiles over the intrinsic finite-prime coefficient field is equivalent to
linear independence, modulo finite prime rays, of every finite clock-jet rectangle. -/
theorem differentialIndependent_fractionPrimeProfiles_iff_clockTailIndependent
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (g : I -> ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeCoefficientField
        (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (g i)) ↔
      ∀ m, PrimeProfileTailIndependent (primeProfileJetSource g m) := by
  constructor
  · intro hDI m
    unfold GaloisForLFunctions.DifferentialIndependent at hDI
    let j : I × Fin (m + 1) -> I × Nat := fun col => (col.1, col.2)
    have hj : Function.Injective j := by
      rintro ⟨i, k⟩ ⟨i', k'⟩ h
      simp only [j, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, Fin.ext h.2⟩
    have hrect := hDI.comp j hj
    simp_rw [differentialJet_algebraMap_primeProfileRotatedLogJet] at hrect
    have hAI : AlgebraicIndependent finitePrimeCoefficientField
        (fun col : I × Fin (m + 1) =>
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (primeProfileJetSource g m col)) := by
      simpa only [j, primeProfileJetSource] using hrect
    exact primeProfileTailIndependent_of_algebraicIndependent
      (primeProfileJetSource g m)
      (primeProfileJetSource_supportedOnPositivePrimePowers g hsupport m) hAI
  · intro htail
    have hray : ∀ m, PrimeProfileJetRayTailIndependent g m := fun m =>
      (primeProfileJetRayTailIndependent_iff_tailIndependent g m).mpr (htail m)
    have hpacket : CofinitePrimeProfileJetPacket g :=
      (cofinitePrimeProfileJetPacket_iff_rayTailIndependent g).mpr hray
    exact differentialIndependent_fractionPrimeProfiles_over_finitePrimeCoefficientField
      g hsupport hpacket

end

end GaloisForLFunctions.HTGeometry
