import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Degree-zero arithmetic rank quotient

This file formalizes the ordinary algebraic shadow of the multiplicative derived rank
quotient used in Deninger's arithmetic coefficient.  A surjective rank map identifies its
kernel quotient with the ordinary rational-Witt channel.  Any Frobenius/Verschiebung operation
commuting with rank preserves the kernel and descends to that quotient.

The higher `E∞` cell attachment is not encoded here; this file proves exactly its
degree-zero first-isomorphism and operation-descent consequences.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Degree-zero kernel of an arithmetic rank map. -/
abbrev deningerArithmeticRankKernel
    {R S : Type*} [CommRing R] [CommRing S] (rank : R →+* S) : Ideal R :=
  RingHom.ker rank

/-- Degree-zero multiplicative quotient by the exact rank kernel. -/
abbrev DeningerArithmeticRankQuotient
    {R S : Type*} [CommRing R] [CommRing S] (rank : R →+* S) :=
  R ⧸ deningerArithmeticRankKernel rank

/-- Surjective arithmetic rank identifies the exact kernel quotient with its ordinary
rational-Witt target. -/
def deningerArithmeticRankQuotientEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (rank : R →+* S) (hrank : Function.Surjective rank) :
    DeningerArithmeticRankQuotient rank ≃+* S :=
  RingHom.quotientKerEquivOfSurjective hrank

@[simp]
theorem deningerArithmeticRankQuotientEquiv_mk
    {R S : Type*} [CommRing R] [CommRing S]
    (rank : R →+* S) (hrank : Function.Surjective rank) (x : R) :
    deningerArithmeticRankQuotientEquiv rank hrank
        (Ideal.Quotient.mk (deningerArithmeticRankKernel rank) x) =
      rank x :=
  RingHom.quotientKerEquivOfSurjective_apply_mk hrank x

/-- An operation commuting with rank preserves the exact rank kernel. -/
theorem deningerArithmeticRankKernel_stable
    {R S : Type*} [CommRing R] [CommRing S]
    (rank : R →+* S) (sourceOp : R →+* R) (targetOp : S →+* S)
    (hcomm : rank.comp sourceOp = targetOp.comp rank) :
    deningerArithmeticRankKernel rank ≤
      (deningerArithmeticRankKernel rank).comap sourceOp := by
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  have hpoint := DFunLike.congr_fun hcomm x
  simpa [hx] using hpoint

/-- Frobenius/Verschiebung operation induced on the exact rank quotient. -/
def deningerArithmeticRankQuotientMap
    {R S : Type*} [CommRing R] [CommRing S]
    (rank : R →+* S) (sourceOp : R →+* R) (targetOp : S →+* S)
    (hcomm : rank.comp sourceOp = targetOp.comp rank) :
    DeningerArithmeticRankQuotient rank →+*
      DeningerArithmeticRankQuotient rank :=
  Ideal.quotientMap (deningerArithmeticRankKernel rank) sourceOp
    (deningerArithmeticRankKernel_stable rank sourceOp targetOp hcomm)

@[simp]
theorem deningerArithmeticRankQuotientMap_mk
    {R S : Type*} [CommRing R] [CommRing S]
    (rank : R →+* S) (sourceOp : R →+* R) (targetOp : S →+* S)
    (hcomm : rank.comp sourceOp = targetOp.comp rank) (x : R) :
    deningerArithmeticRankQuotientMap rank sourceOp targetOp hcomm
        (Ideal.Quotient.mk (deningerArithmeticRankKernel rank) x) =
      Ideal.Quotient.mk (deningerArithmeticRankKernel rank) (sourceOp x) := by
  exact Ideal.quotientMap_mk

/-- The first-isomorphism equivalence intertwines the descended source operation with the
ordinary target operation. -/
theorem deningerArithmeticRankQuotientEquiv_intertwines
    {R S : Type*} [CommRing R] [CommRing S]
    (rank : R →+* S) (hrank : Function.Surjective rank)
    (sourceOp : R →+* R) (targetOp : S →+* S)
    (hcomm : rank.comp sourceOp = targetOp.comp rank) (x : R) :
    deningerArithmeticRankQuotientEquiv rank hrank
        (deningerArithmeticRankQuotientMap rank sourceOp targetOp hcomm
          (Ideal.Quotient.mk (deningerArithmeticRankKernel rank) x)) =
      targetOp
        (deningerArithmeticRankQuotientEquiv rank hrank
          (Ideal.Quotient.mk (deningerArithmeticRankKernel rank) x)) := by
  simp only [deningerArithmeticRankQuotientMap_mk,
    deningerArithmeticRankQuotientEquiv_mk]
  exact DFunLike.congr_fun hcomm x

end

end GaloisForLFunctions.RHTower
