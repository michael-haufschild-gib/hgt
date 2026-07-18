import GaloisForLFunctions.HTGeometry.SeparatedRayTailPacket
import GaloisForLFunctions.HTGeometry.PrimeProfileJetPacket
import GaloisForLFunctions.HTGeometry.PrimeProfileTailMatroid
import GaloisForLFunctions.HTGeometry.DifferentialMatroidClosure
import Mathlib.LinearAlgebra.Dimension.Constructions

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

/-- The vector-space quotient of complete prime-power profiles by profiles carried on finitely
many prime rays.  This is the additive carrier of the prime-clock module. -/
abbrev PrimeProfileClockQuotient :=
  (PrimePowerClockIndex -> ℂ) ⧸ (rayLocalSubmodule primePowerClockRay)

/-- The quotient class of an arithmetic prime-power profile.  Defining this as a linear map keeps
all finite clock-jet combinations definitionally compatible with quotient linear algebra. -/
def primeProfileClockClass :
    ArithmeticFunction ℂ →ₗ[ℂ] PrimeProfileClockQuotient := by
  let coordinateMap : ArithmeticFunction ℂ →ₗ[ℂ]
      (PrimePowerClockIndex -> ℂ) :=
    { toFun := primePowerCoordinateProfile
      map_add' := by
        intro f g
        ext x
        rfl
      map_smul' := by
        intro c f
        ext x
        change (c • f) (Nat.Primes.prodNatEquiv x : Nat) =
          c • f (Nat.Primes.prodNatEquiv x : Nat)
        exact ArithmeticFunction.smul_map c f _ }
  exact (rayLocalSubmodule primePowerClockRay).mkQ.comp coordinateMap

/-- Independence modulo finite prime rays is ordinary linear independence of the quotient
classes.  This is the static coordinate-free form of the tail matroid. -/
theorem primeProfileTailIndependent_iff_linearIndependent_clockClass
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> ArithmeticFunction ℂ) :
    PrimeProfileTailIndependent g ↔
      LinearIndependent ℂ (fun i => primeProfileClockClass (g i)) := by
  constructor
  · intro htail
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hclass : primeProfileClockClass (∑ j, c j • g j) = 0 := by
      simpa only [map_sum, map_smul] using hc
    have hlocal : PrimePowerClockLocal
        (primePowerCoordinateProfile (∑ j, c j • g j)) := by
      change primePowerCoordinateProfile (∑ j, c j • g j) ∈
        rayLocalSubmodule primePowerClockRay
      simpa only [primeProfileClockClass, LinearMap.comp_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hclass
    exact congrFun (htail c hlocal) i
  · intro hlinear c hlocal
    funext i
    have hc : ∀ j, c j = 0 := Fintype.linearIndependent_iff.mp hlinear c (by
      have hq : primeProfileClockClass (∑ j, c j • g j) = 0 := by
        unfold primeProfileClockClass
        change (rayLocalSubmodule primePowerClockRay).mkQ
          (primePowerCoordinateProfile (∑ j, c j • g j)) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hlocal
      simpa only [map_sum, map_smul] using hq)
    exact hc i

/-- Dynamic finite-prime descent at one prescribed jet order.  Unlike the earlier all-order
wrapper, this theorem consumes exactly one cofinite packet and is therefore also usable for the
static order-zero classification. -/
theorem algebraicIndependent_fractionPrimeProfileJets_of_cofinitePacketAt
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i))
    (m : Nat)
    (hpacket : ∀ (forbidden : Set Nat.Primes), forbidden.Finite ->
      ∃ (q : I × Fin (m + 1) -> Nat.Primes)
        (e : I × Fin (m + 1) -> Nat),
        Function.Injective q ∧
        (∀ row, q row ∉ forbidden) ∧
        (primeProfileJetPacketMatrix g m q e).det ≠ 0) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun col : I × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primeProfileJetSource g m col)) := by
  rw [algebraicIndependent_iff]
  intro P hPeval
  by_contra hPne
  have hPne' : P ≠ 0 := hPne
  obtain ⟨q, e, hq, havoid, hdet⟩ :=
    hpacket (polynomialPrimeActivity P) (polynomialPrimeActivity_finite P)
  have hAIK : AlgebraicIndependent (primeCommonKernelField q)
      (fun col : I × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primeProfileJetSource g m col)) :=
    algebraicIndependent_fractionPrimeProfileJets_over_commonKernel
      g hsupport m q e hq hdet
  let Q : MvPolynomial (I × Fin (m + 1)) (primeCommonKernelField q) :=
    liftPolynomialToPrimeCommonKernel q P havoid
  have hQne : Q ≠ 0 :=
    liftPolynomialToPrimeCommonKernel_ne_zero q P havoid hPne'
  have hmap := map_liftPolynomialToPrimeCommonKernel q P havoid
  let y : I × Fin (m + 1) -> arithmeticFunctionFractionField := fun col =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (primeProfileJetSource g m col)
  have heval := congrArg (MvPolynomial.eval y) hmap
  have hQeval : MvPolynomial.aeval y Q = 0 := by
    have heq : MvPolynomial.aeval y Q = MvPolynomial.aeval y P := by
      simpa [Q, y, MvPolynomial.aeval_def, MvPolynomial.eval_map] using heval
    exact heq.trans hPeval
  exact hQne (hAIK.eq_zero_of_aeval_eq_zero Q hQeval)

/-- **Exact static prime-profile matroid.**  For every finite positive-prime-power source family,
algebraic independence over the intrinsic finite-prime field is equivalent to complex-linear
independence of its classes modulo finite prime rays. -/
theorem algebraicIndependent_fractionPrimeProfiles_iff_clockClassIndependent
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i)) :
    AlgebraicIndependent finitePrimeCoefficientField
        (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (g i)) ↔
      LinearIndependent ℂ (fun i => primeProfileClockClass (g i)) := by
  constructor
  · intro hAI
    exact (primeProfileTailIndependent_iff_linearIndependent_clockClass g).mp
      (primeProfileTailIndependent_of_algebraicIndependent g hsupport hAI)
  · intro hlinear
    have hrectLinear : LinearIndependent ℂ
        (fun col : I × Fin 1 =>
          primeProfileClockClass (primeProfileJetSource g 0 col)) := by
      have hcomp := hlinear.comp (fun col : I × Fin 1 => col.1) (by
        intro a b hab
        apply Prod.ext hab
        exact Subsingleton.elim _ _)
      simpa [primeProfileJetSource, primeProfileRotatedLogJet] using hcomp
    have hrectTail : PrimeProfileTailIndependent (primeProfileJetSource g 0) :=
      (primeProfileTailIndependent_iff_linearIndependent_clockClass
        (primeProfileJetSource g 0)).mpr hrectLinear
    have hray : PrimeProfileJetRayTailIndependent g 0 :=
      (primeProfileJetRayTailIndependent_iff_tailIndependent g 0).mpr hrectTail
    have hpacket := fun forbidden hforbidden =>
      cofinitePrimeProfileJetPacket_at_of_rayTailIndependent
        g 0 hray forbidden hforbidden
    have hAIrect :=
      algebraicIndependent_fractionPrimeProfileJets_of_cofinitePacketAt
        g hsupport 0 hpacket
    let e : I -> I × Fin 1 := fun i => (i, 0)
    have he : Function.Injective e := by
      intro i j hij
      exact congrArg Prod.fst hij
    have hsub := hAIrect.comp e he
    simpa [e, primeProfileJetSource, primeProfileRotatedLogJet] using hsub

/-- **Arbitrary-family static prime-profile matroid.**  The exact quotient classification has
finite character: no global cardinality restriction on the source family is needed. -/
theorem algebraicIndependent_fractionPrimeProfiles_iff_clockClassIndependent_arbitrary
    {I : Type*} (g : I -> ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i)) :
    AlgebraicIndependent finitePrimeCoefficientField
        (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (g i)) ↔
      LinearIndependent ℂ (fun i => primeProfileClockClass (g i)) := by
  classical
  constructor
  · intro hAI
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have hAIs : AlgebraicIndependent finitePrimeCoefficientField
        (fun z : s => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (g z.1)) :=
      hAI.comp Subtype.val Subtype.val_injective
    have hsupports : ∀ z : s,
        PrimeProfileSupportedOnPositivePrimePowers (g z.1) := fun z => hsupport z.1
    have hLIs : LinearIndependent ℂ
        (fun z : s => primeProfileClockClass (g z.1)) :=
      (algebraicIndependent_fractionPrimeProfiles_iff_clockClassIndependent
        (fun z : s => g z.1) hsupports).mp hAIs
    have hsum' : ∑ z : s, c z.1 • primeProfileClockClass (g z.1) = 0 := by
      rw [← s.sum_attach] at hsum
      simpa only [Finset.attach_eq_univ] using hsum
    exact (Fintype.linearIndependent_iff.mp hLIs
      (fun z : s => c z.1) hsum' ⟨i, hi⟩)
  · intro hlinear
    apply algebraicIndependent_of_finite_type
    intro t ht
    letI : Fintype t := ht.fintype
    letI : DecidableEq t := Classical.decEq t
    apply (algebraicIndependent_fractionPrimeProfiles_iff_clockClassIndependent
      (fun z : t => g z.1) (fun z => hsupport z.1)).mpr
    exact hlinear.comp Subtype.val Subtype.val_injective

/-- Linear independence of every finite initial rectangle implies independence of the entire
natural clock orbit.  This is the linear analogue of
`algebraicIndependent_prod_nat_of_fin`. -/
theorem linearIndependent_prod_nat_of_fin
    {R V I : Type*} [Ring R] [AddCommGroup V] [Module R V] [Nonempty I]
    (x : I -> Nat -> V)
    (hfin : ∀ m, LinearIndependent R
      (fun ik : I × Fin (m + 1) => x ik.1 ik.2)) :
    LinearIndependent R (fun ik : I × Nat => x ik.1 ik.2) := by
  rw [linearIndependent_iff']
  intro t c hsum ik hik
  obtain ⟨q, hq⟩ :=
    Set.exists_upper_bound_image (t : Set (I × Nat)) Prod.snd t.finite_toSet
  let f : t -> I × Fin (q.2 + 1) := fun z =>
    (z.1.1, ⟨z.1.2, Nat.lt_succ_of_le (hq z.1 z.2)⟩)
  have hf : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun u : I × Fin (q.2 + 1) => u.1) hzw
    · exact congrArg (fun u : I × Fin (q.2 + 1) => (u.2 : Nat)) hzw
  have hsub := (hfin q.2).comp f hf
  have hzero : ∑ z : t, c z.1 • x z.1.1 z.1.2 = 0 := by
    rw [← t.sum_attach] at hsum
    simpa only [Finset.attach_eq_univ] using hsum
  exact (Fintype.linearIndependent_iff.mp hsub
    (fun z : t => c z.1) (by simpa only [Function.comp_apply, f] using hzero)
    ⟨ik, hik⟩)

/-- The full prime-clock orbit of a source family in the finite-ray quotient. -/
def primeProfileClockJetFamily
    {I : Type*} (g : I -> ArithmeticFunction ℂ) :
    I × Nat -> PrimeProfileClockQuotient :=
  fun ik => primeProfileClockClass (primeProfileRotatedLogJet ik.2 (g ik.1))

/-- Freeness of the complete polynomial clock orbit of a source family. -/
def PrimeProfileClockIndependent
    {I : Type*} (g : I -> ArithmeticFunction ℂ) : Prop :=
  LinearIndependent ℂ (primeProfileClockJetFamily g)

/-- Full clock-orbit freeness is exactly finite-ray independence of every finite jet rectangle. -/
theorem primeProfileClockIndependent_iff_finiteTailIndependent
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (g : I -> ArithmeticFunction ℂ) :
    PrimeProfileClockIndependent g ↔
      ∀ m, PrimeProfileTailIndependent (primeProfileJetSource g m) := by
  constructor
  · intro hclock m
    apply (primeProfileTailIndependent_iff_linearIndependent_clockClass
      (primeProfileJetSource g m)).mpr
    let j : I × Fin (m + 1) -> I × Nat := fun col => (col.1, col.2)
    have hj : Function.Injective j := by
      rintro ⟨i, k⟩ ⟨i', k'⟩ h
      simp only [j, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, Fin.ext h.2⟩
    have hrect := hclock.comp j hj
    simpa only [primeProfileClockJetFamily, j, primeProfileJetSource] using hrect
  · intro htail
    apply linearIndependent_prod_nat_of_fin
      (fun i n => primeProfileClockClass (primeProfileRotatedLogJet n (g i)))
    intro m
    simpa only [primeProfileJetSource] using
      (primeProfileTailIndependent_iff_linearIndependent_clockClass
        (primeProfileJetSource g m)).mp (htail m)

/-- **Absolute prime-clock module classification.** Differential independence of an arbitrary
finite family of positive-prime-power sources is exactly freeness of its complete polynomial
clock orbit in the quotient by finite prime rays. -/
theorem differentialIndependent_fractionPrimeProfiles_iff_clockIndependent
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (g : I -> ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeCoefficientField
        (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (g i)) ↔
      PrimeProfileClockIndependent g := by
  rw [differentialIndependent_fractionPrimeProfiles_iff_clockTailIndependent
    g hsupport, primeProfileClockIndependent_iff_finiteTailIndependent]

/-- The old-source clock submodule: the complex span of every logarithmic jet class.  It is the
underlying complex space of the `ℂ[X]`-submodule generated by the old profiles. -/
def primeProfileClockSubmodule
    {I : Type*} (c : I -> ArithmeticFunction ℂ) :
    Submodule ℂ PrimeProfileClockQuotient :=
  Submodule.span ℂ (Set.range (primeProfileClockJetFamily c))

/-- The exact relative clock condition: all jets of the new sources remain linearly independent
after quotienting by the complete old-source clock submodule. -/
def PrimeProfileRelativeClockIndependent
    {I H : Type*} (c : I -> ArithmeticFunction ℂ)
    (g : H -> ArithmeticFunction ℂ) : Prop :=
  LinearIndependent ℂ
    ((primeProfileClockSubmodule c).mkQ ∘ primeProfileClockJetFamily g)

/-- Splitting linear independence through the quotient by the span of the left block. -/
theorem linearIndependent_sumElim_iff_quotient
    {R V I H : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (x : I -> V) (y : H -> V) :
    LinearIndependent R (Sum.elim x y) ↔
      LinearIndependent R x ∧
        LinearIndependent R
          ((Submodule.span R (Set.range x)).mkQ ∘ y) := by
  constructor
  · intro hsum
    have hparts := linearIndependent_sum.mp hsum
    refine ⟨by simpa using hparts.1, ?_⟩
    have hy : LinearIndependent R y := by
      simpa using hparts.2.1
    apply hy.map
    rw [Submodule.ker_mkQ]
    simpa using hparts.2.2.symm
  · rintro ⟨hx, hy⟩
    have hx' := linearIndependent_span hx
    have hsum := hx'.sumElim_of_quotient y hy
    simpa using hsum

/-- Clock-submodule membership gives actual membership in the differential field generated by
the source pivots: a finite clock combination is a finite linear combination of source jets, up
to one finite-prime residual already contained in the coefficient field. -/
theorem carrier_mem_differentialAdjoin_of_primeProfileClockClass_mem
    {I : Type*} (c : I -> ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (f : ArithmeticFunction ℂ)
    (hfsupport : PrimeProfileSupportedOnPositivePrimePowers f)
    (hmem : primeProfileClockClass f ∈ primeProfileClockSubmodule c) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
      GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (c i))) := by
  classical
  change primeProfileClockClass f ∈
    Submodule.span ℂ (Set.range (primeProfileClockJetFamily c)) at hmem
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨a, ha⟩ := hmem
  let oldProfile : I × Nat -> ArithmeticFunction ℂ := fun ik =>
    primeProfileRotatedLogJet ik.2 (c ik.1)
  let combo : ArithmeticFunction ℂ :=
    Finsupp.linearCombination ℂ oldProfile a
  have hclassCombo : primeProfileClockClass combo = primeProfileClockClass f := by
    calc
      primeProfileClockClass combo =
          Finsupp.linearCombination ℂ
            (primeProfileClockJetFamily c) a := by
        dsimp only [combo]
        rw [Finsupp.linearCombination_apply,
          Finsupp.linearCombination_apply, map_finsuppSum]
        simp only [map_smul, oldProfile, primeProfileClockJetFamily]
      _ = primeProfileClockClass f := ha
  let residual : ArithmeticFunction ℂ := f - combo
  have hresidualClass : primeProfileClockClass residual = 0 := by
    dsimp only [residual]
    rw [map_sub, hclassCombo, sub_self]
  have hresidualLocal : PrimePowerClockLocal
      (primePowerCoordinateProfile residual) := by
    unfold primeProfileClockClass at hresidualClass
    change primePowerCoordinateProfile residual ∈
      rayLocalSubmodule primePowerClockRay
    simpa only [LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] using hresidualClass
  have holdSupport : ∀ ik,
      PrimeProfileSupportedOnPositivePrimePowers (oldProfile ik) := by
    intro ik
    exact primeProfileRotatedLogJet_supportedOnPositivePrimePowers
      (c ik.1) (hcsupport ik.1) ik.2
  have hcomboSupport : PrimeProfileSupportedOnPositivePrimePowers combo := by
    intro n hn
    by_contra hnone
    have hzero : ∀ ik, oldProfile ik n = 0 := by
      intro ik
      by_contra hik
      exact hnone (holdSupport ik hik)
    have hsum : ∀ s : Finset (I × Nat),
        (∑ ik ∈ s, a ik • oldProfile ik) n = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert ik s hik ih =>
          rw [Finset.sum_insert hik, ArithmeticFunction.add_apply,
            ArithmeticFunction.smul_map, hzero ik, smul_zero, ih, zero_add]
    apply hn
    dsimp only [combo]
    rw [Finsupp.linearCombination_apply_of_mem_supported ℂ
      (Finsupp.mem_supported_support a)]
    exact hsum a.support
  have hresidualSupport : PrimeProfileSupportedOnPositivePrimePowers residual := by
    intro n hn
    by_contra hnone
    have hfzero : f n = 0 := by
      by_contra hfn
      exact hnone (hfsupport hfn)
    have hczero : combo n = 0 := by
      by_contra hcn
      exact hnone (hcomboSupport hcn)
    apply hn
    dsimp only [residual]
    simp [hfzero, hczero]
  have hresidualBase :
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField residual ∈
        finitePrimeCoefficientField :=
    algebraMap_primeProfile_mem_finitePrimeCoefficientField_of_local
      residual hresidualSupport hresidualLocal
  let K := GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
    (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField (c i)))
  have hcomboMem :
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField combo ∈ K := by
    dsimp only [combo]
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    unfold Finsupp.sum
    apply IntermediateField.sum_mem
    intro ik hik
    rw [Algebra.smul_def, map_mul]
    apply IntermediateField.mul_mem
    · rw [IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField]
      exact IntermediateField.algebraMap_mem K
        (algebraMap ℂ finitePrimeCoefficientField (a ik))
    · have hjet :
          GaloisForLFunctions.differentialJet ik.2
              (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
                (c ik.1)) ∈ K :=
          GaloisForLFunctions.differentialJet_mem_differentialAdjoin
            finitePrimeCoefficientField (Set.mem_range_self ik.1) ik.2
      simpa only [oldProfile,
        differentialJet_algebraMap_primeProfileRotatedLogJet] using hjet
  let r : finitePrimeCoefficientField :=
    ⟨algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField residual,
      hresidualBase⟩
  have hresidualMem :
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField residual ∈ K := by
    have hr := IntermediateField.algebraMap_mem K r
    simpa only [r] using hr
  have hdecomp : f = combo + residual := by
    simp [residual]
  rw [hdecomp, map_add]
  exact IntermediateField.add_mem K hcomboMem hresidualMem

/-- **No nonlinear source collapse.**  For a clock-free pivot family, membership of a new
prime-power carrier in the pivot-generated differential field forces the new clock class to lie
in the complete old clock submodule.  Thus rational field operations cannot manufacture a new
prime-clock direction. -/
theorem primeProfileClockClass_mem_of_carrier_mem_differentialAdjoin
    {I : Type*} [Nonempty I]
    (c : I -> ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (hc : PrimeProfileClockIndependent c)
    (f : ArithmeticFunction ℂ)
    (hfsupport : PrimeProfileSupportedOnPositivePrimePowers f)
    (hfmem : algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
      GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (c i)))) :
    primeProfileClockClass f ∈ primeProfileClockSubmodule c := by
  classical
  by_contra hnot
  let oldProfile : I × Nat -> ArithmeticFunction ℂ := fun ik =>
    primeProfileRotatedLogJet ik.2 (c ik.1)
  let newProfile : Unit -> ArithmeticFunction ℂ := fun _ => f
  have hnewQuotient : LinearIndependent ℂ
      ((primeProfileClockSubmodule c).mkQ ∘
        (fun _ : Unit => primeProfileClockClass f)) := by
    rw [linearIndependent_unique_iff]
    change (primeProfileClockSubmodule c).mkQ (primeProfileClockClass f) ≠ 0
    rw [Submodule.mkQ_apply]
    exact mt (Submodule.Quotient.mk_eq_zero (primeProfileClockSubmodule c)).mp hnot
  have hclassSum : LinearIndependent ℂ
      (Sum.elim (primeProfileClockJetFamily c)
        (fun _ : Unit => primeProfileClockClass f)) :=
    (linearIndependent_sumElim_iff_quotient
      (primeProfileClockJetFamily c)
      (fun _ : Unit => primeProfileClockClass f)).mpr ⟨hc, hnewQuotient⟩
  let profile : (I × Nat) ⊕ Unit -> ArithmeticFunction ℂ :=
    Sum.elim oldProfile newProfile
  have hprofileSupport : ∀ z,
      PrimeProfileSupportedOnPositivePrimePowers (profile z) := by
    intro z
    rcases z with ik | u
    · exact primeProfileRotatedLogJet_supportedOnPositivePrimePowers
        (c ik.1) (hcsupport ik.1) ik.2
    · exact hfsupport
  have hclassFamily : (fun z => primeProfileClockClass (profile z)) =
      Sum.elim (primeProfileClockJetFamily c)
        (fun _ : Unit => primeProfileClockClass f) := by
    funext z
    rcases z with ik | u <;> rfl
  have hprofileClasses : LinearIndependent ℂ
      (fun z => primeProfileClockClass (profile z)) := by
    rw [hclassFamily]
    exact hclassSum
  have hAI : AlgebraicIndependent finitePrimeCoefficientField
      (fun z => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (profile z)) :=
    (algebraicIndependent_fractionPrimeProfiles_iff_clockClassIndependent_arbitrary
      profile hprofileSupport).mpr hprofileClasses
  have hswap := hAI.comp (Equiv.sumComm Unit (I × Nat))
    (Equiv.sumComm Unit (I × Nat)).injective
  let oldCarrier : I × Nat -> arithmeticFunctionFractionField := fun ik =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (oldProfile ik)
  let newCarrier : Unit -> arithmeticFunctionFractionField := fun _ =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f
  have hswapFamily :
      ((fun z => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (profile z)) ∘ (Equiv.sumComm Unit (I × Nat))) =
      Sum.elim newCarrier oldCarrier := by
    funext z
    rcases z with u | ik <;> rfl
  have hAIswap : AlgebraicIndependent finitePrimeCoefficientField
      (Sum.elim newCarrier oldCarrier) := by
    rw [hswapFamily] at hswap
    exact hswap
  have hnewOverAlg : AlgebraicIndependent
      (Algebra.adjoin finitePrimeCoefficientField (Set.range oldCarrier)) newCarrier :=
    (AlgebraicIndependent.sumElim_iff.mp hAIswap).2
  have hnewOverField : AlgebraicIndependent
      (IntermediateField.adjoin finitePrimeCoefficientField (Set.range oldCarrier))
      newCarrier :=
    IntermediateField.algebraicIndependent_adjoin_iff.mpr hnewOverAlg
  let x : I -> arithmeticFunctionFractionField := fun i =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (c i)
  have hjetFamily :
      (fun ik : I × Nat =>
        GaloisForLFunctions.differentialJet ik.2 (x ik.1)) = oldCarrier := by
    funext ik
    exact differentialJet_algebraMap_primeProfileRotatedLogJet ik.2 (c ik.1)
  have hfield :
      GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range x) =
        IntermediateField.adjoin finitePrimeCoefficientField (Set.range oldCarrier) := by
    unfold GaloisForLFunctions.differentialAdjoin
    rw [GaloisForLFunctions.differentialJetSet_range_eq, hjetFamily]
  have hfmem' : algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
      IntermediateField.adjoin finitePrimeCoefficientField (Set.range oldCarrier) := by
    rw [← hfield]
    simpa only [x] using hfmem
  have htrans : Transcendental
      (IntermediateField.adjoin finitePrimeCoefficientField (Set.range oldCarrier))
      (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) := by
    simpa only [newCarrier] using hnewOverField.transcendental ()
  exact htrans (by
    simpa using isAlgebraic_algebraMap
      (R := IntermediateField.adjoin finitePrimeCoefficientField (Set.range oldCarrier))
      (A := arithmeticFunctionFractionField)
      (⟨algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f, hfmem'⟩ :
        IntermediateField.adjoin finitePrimeCoefficientField (Set.range oldCarrier)))

/-- **Exact source recovery, pivot form.**  A positive-prime-power carrier belongs to the
differential field generated by a clock-free pivot family exactly when its prime-clock class lies
in the complete clock submodule generated by those pivots. -/
theorem primeProfileCarrier_mem_differentialAdjoin_iff_clockClass_mem
    {I : Type*} [Nonempty I]
    (c : I -> ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (hc : PrimeProfileClockIndependent c)
    (f : ArithmeticFunction ℂ)
    (hfsupport : PrimeProfileSupportedOnPositivePrimePowers f) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
        GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (c i))) ↔
      primeProfileClockClass f ∈ primeProfileClockSubmodule c := by
  constructor
  · exact primeProfileClockClass_mem_of_carrier_mem_differentialAdjoin
      c hcsupport hc f hfsupport
  · exact carrier_mem_differentialAdjoin_of_primeProfileClockClass_mem
      c hcsupport f hfsupport

/-- **Exact embedded-field order law, pivot target form.**  Inclusion in a field generated by a
clock-free target family is exactly inclusion of the complete prime-clock submodules.  The source
family itself need not be free. -/
theorem primeProfile_differentialAdjoin_le_iff_clockSubmodule_le
    {I J : Type*} [Nonempty J]
    (c : I -> ArithmeticFunction ℂ) (d : J -> ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (hdsupport : ∀ j, PrimeProfileSupportedOnPositivePrimePowers (d j))
    (hd : PrimeProfileClockIndependent d) :
    GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (c i))) ≤
      GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun j => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (d j))) ↔
      primeProfileClockSubmodule c ≤ primeProfileClockSubmodule d := by
  constructor
  · intro hfield
    rw [primeProfileClockSubmodule, Submodule.span_le]
    intro q hq
    obtain ⟨ik, rfl⟩ := hq
    apply primeProfileClockClass_mem_of_carrier_mem_differentialAdjoin
      d hdsupport hd
      (primeProfileRotatedLogJet ik.2 (c ik.1))
      (primeProfileRotatedLogJet_supportedOnPositivePrimePowers
        (c ik.1) (hcsupport ik.1) ik.2)
    apply hfield
    have hjet :
        GaloisForLFunctions.differentialJet ik.2
            (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
              (c ik.1)) ∈
          GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
            (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
              arithmeticFunctionFractionField (c i))) :=
      GaloisForLFunctions.differentialJet_mem_differentialAdjoin
        finitePrimeCoefficientField (Set.mem_range_self ik.1) ik.2
    simpa only [differentialJet_algebraMap_primeProfileRotatedLogJet] using hjet
  · intro hmodule
    unfold GaloisForLFunctions.differentialAdjoin
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨x, ⟨i, rfl⟩, n, rfl⟩
    rw [differentialJet_algebraMap_primeProfileRotatedLogJet]
    change algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primeProfileRotatedLogJet n (c i)) ∈
      GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun j => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (d j)))
    apply carrier_mem_differentialAdjoin_of_primeProfileClockClass_mem
      d hdsupport (primeProfileRotatedLogJet n (c i))
      (primeProfileRotatedLogJet_supportedOnPositivePrimePowers
        (c i) (hcsupport i) n)
    apply hmodule
    apply Submodule.subset_span
    exact ⟨(i, n), rfl⟩

/-- **Exact embedded-field equality law.**  Two clock-free positive-prime-power pivot families
generate the same embedded differential field exactly when they generate the same prime-clock
submodule. -/
theorem primeProfile_differentialAdjoin_eq_iff_clockSubmodule_eq
    {I J : Type*} [Nonempty I] [Nonempty J]
    (c : I -> ArithmeticFunction ℂ) (d : J -> ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (hdsupport : ∀ j, PrimeProfileSupportedOnPositivePrimePowers (d j))
    (hc : PrimeProfileClockIndependent c)
    (hd : PrimeProfileClockIndependent d) :
    GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (c i))) =
      GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun j => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (d j))) ↔
      primeProfileClockSubmodule c = primeProfileClockSubmodule d := by
  constructor
  · intro hfield
    apply le_antisymm
    · exact (primeProfile_differentialAdjoin_le_iff_clockSubmodule_le
        c d hcsupport hdsupport hd).mp hfield.le
    · exact (primeProfile_differentialAdjoin_le_iff_clockSubmodule_le
        d c hdsupport hcsupport hc).mp hfield.ge
  · intro hmodule
    apply le_antisymm
    · exact (primeProfile_differentialAdjoin_le_iff_clockSubmodule_le
        c d hcsupport hdsupport hd).mpr hmodule.le
    · exact (primeProfile_differentialAdjoin_le_iff_clockSubmodule_le
        d c hdsupport hcsupport hc).mpr hmodule.ge

/-- Reindex the clock jets of a sum of source families as the sum of their clock-jet families. -/
theorem primeProfileClockIndependent_sumElim_iff
    {I H : Type*} (c : I -> ArithmeticFunction ℂ)
    (g : H -> ArithmeticFunction ℂ) :
    PrimeProfileClockIndependent (Sum.elim c g) ↔
      LinearIndependent ℂ
        (Sum.elim (primeProfileClockJetFamily c) (primeProfileClockJetFamily g)) := by
  let e := Equiv.sumProdDistrib I H Nat
  have hfamily : primeProfileClockJetFamily (Sum.elim c g) =
      (Sum.elim (primeProfileClockJetFamily c) (primeProfileClockJetFamily g)) ∘ e := by
    funext z
    rcases z with ⟨i | h, n⟩ <;> rfl
  rw [PrimeProfileClockIndependent, hfamily]
  exact linearIndependent_equiv e

/-- **Relative prime-clock differential matroid, pivot form.**  If the old sources freely
generate their clock submodule, then a new family is differentially independent over the old
differential field exactly when its full clock orbit is independent in the quotient by that
submodule.  This is the precise `ℂ[X]`-module quotient law; it distinguishes field membership
from differential algebraicity. -/
theorem differentialIndependent_fractionPrimeProfiles_relative_iff_clockQuotientIndependent
    {I H : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype H] [DecidableEq H] [Nonempty H]
    (c : I -> ArithmeticFunction ℂ) (g : H -> ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (hgsupport : ∀ h, PrimeProfileSupportedOnPositivePrimePowers (g h))
    (hc : PrimeProfileClockIndependent c) :
    GaloisForLFunctions.DifferentialIndependent
        (GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (c i))))
        (fun h => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (g h)) ↔
      PrimeProfileRelativeClockIndependent c g := by
  let x : I -> arithmeticFunctionFractionField := fun i =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (c i)
  let y : H -> arithmeticFunctionFractionField := fun h =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g h)
  have hx : GaloisForLFunctions.DifferentialIndependent
      finitePrimeCoefficientField x :=
    (differentialIndependent_fractionPrimeProfiles_iff_clockIndependent
      c hcsupport).mpr hc
  have hsumSupport : ∀ z,
      PrimeProfileSupportedOnPositivePrimePowers (Sum.elim c g z) := by
    intro z
    rcases z with i | h
    · exact hcsupport i
    · exact hgsupport h
  have hclockSplit : PrimeProfileClockIndependent (Sum.elim c g) ↔
      PrimeProfileClockIndependent c ∧
        PrimeProfileRelativeClockIndependent c g := by
    rw [primeProfileClockIndependent_sumElim_iff,
      linearIndependent_sumElim_iff_quotient]
    rfl
  constructor
  · intro hrel
    have hswap : GaloisForLFunctions.DifferentialIndependent
        finitePrimeCoefficientField (Sum.elim y x) :=
      (GaloisForLFunctions.differentialIndependent_sumElim_right_iff y x).mpr
        ⟨hx, by simpa only [x, y] using hrel⟩
    have hcombined := hswap.comp (Equiv.sumComm I H) (Equiv.sumComm I H).injective
    have hfamily : (Sum.elim y x) ∘ (Equiv.sumComm I H) =
        (fun z => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (Sum.elim c g z)) := by
      funext z
      rcases z with i | h <;> rfl
    have hcombined' : GaloisForLFunctions.DifferentialIndependent
        finitePrimeCoefficientField
        (fun z => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (Sum.elim c g z)) := by
      rw [hfamily] at hcombined
      exact hcombined
    have hclockCombined : PrimeProfileClockIndependent (Sum.elim c g) :=
      (differentialIndependent_fractionPrimeProfiles_iff_clockIndependent
        (Sum.elim c g) hsumSupport).mp hcombined'
    exact (hclockSplit.mp hclockCombined).2
  · intro hquot
    have hclockCombined : PrimeProfileClockIndependent (Sum.elim c g) :=
      hclockSplit.mpr ⟨hc, hquot⟩
    have hcombined' : GaloisForLFunctions.DifferentialIndependent
        finitePrimeCoefficientField
        (fun z => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (Sum.elim c g z)) :=
      (differentialIndependent_fractionPrimeProfiles_iff_clockIndependent
        (Sum.elim c g) hsumSupport).mpr hclockCombined
    have hcombined : GaloisForLFunctions.DifferentialIndependent
        finitePrimeCoefficientField (Sum.elim x y) := by
      have hfamily : (fun z => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (Sum.elim c g z)) = Sum.elim x y := by
        funext z
        rcases z with i | h <;> rfl
      rw [hfamily] at hcombined'
      exact hcombined'
    have hswap := hcombined.comp (Equiv.sumComm H I) (Equiv.sumComm H I).injective
    have hfamily : (Sum.elim x y) ∘ (Equiv.sumComm H I) = Sum.elim y x := by
      funext z
      rcases z with h | i <;> rfl
    rw [hfamily] at hswap
    exact (GaloisForLFunctions.differentialIndependent_sumElim_right_iff y x).mp
      hswap |>.2

end

end GaloisForLFunctions.HTGeometry
