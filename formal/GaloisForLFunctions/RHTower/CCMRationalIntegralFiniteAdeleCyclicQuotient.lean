import GaloisForLFunctions.RHTower.CCMRationalProfiniteIntegerCyclicQuotient
import GaloisForLFunctions.RHTower.CCMRationalIntegralAdeleHaarIndex

/-!
# Cyclic quotients of rational integral finite adeles

The product-of-`p`-adics cyclic quotient law is transferred to the actual
compact open subgroup of the rational finite adele ring.  The transfer keeps
track of diagonal integers, so the resulting `ZMod N` equivalence is induced
by the literal adelic diagonal rather than by a cardinality-only surrogate.
-/

noncomputable section

open IsDedekindDomain
open scoped RestrictedProduct algebraMap Classical

namespace GaloisForLFunctions
namespace RHTower

/-- Additive identification of product-form profinite integers with the
actual integral finite-adele subgroup. -/
def ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles :
    CCMRationalProfiniteIntegers ≃+
      ccmRationalIntegralFiniteAdelesAddSubgroup :=
  ccmRationalIntegralPiPadicEquiv.symm.trans
    ccmRationalIntegralPiAddEquivIntegralFiniteAdeles

/-- Diagonal embedding of integers into integral finite adeles. -/
def ccmRationalIntegralFiniteAdeleDiagonal :
    ℤ →+ ccmRationalIntegralFiniteAdelesAddSubgroup where
  toFun m := ⟨algebraMap ℤ CCMRationalFiniteAdele m,
    fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers
      (K := ℚ) v m⟩
  map_zero' := by ext; simp
  map_add' m n := by ext; simp

/-- The profinite-integer equivalence preserves every diagonal integer. -/
theorem ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles_diagonal
    (m : ℤ) :
    ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles
        (ccmRationalProfiniteIntegerDiagonal m) =
      ccmRationalIntegralFiniteAdeleDiagonal m := by
  apply Subtype.ext
  apply RestrictedProduct.ext
  intro v
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
    Ring.toIntAlgebra _
  change ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm
      (m : ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) :
        v.adicCompletion ℚ) =
    algebraMap ℤ (v.adicCompletion ℚ) m
  rw [map_intCast]
  simp

/-- Diagonal integers in the quotient by multiplication by `N`. -/
def ccmRationalIntegralFiniteAdeleQuotientDiagonal (N : ℕ) :
    ℤ →+ ccmRationalIntegralFiniteAdelesAddSubgroup ⧸
      (nsmulAddMonoidHom N).range :=
  (QuotientAddGroup.mk' _).comp
    ccmRationalIntegralFiniteAdeleDiagonal

theorem ccmRationalIntegralFiniteAdeleQuotientDiagonal_natCast_eq_zero
    (N : ℕ) :
    ccmRationalIntegralFiniteAdeleQuotientDiagonal N (N : ℤ) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).2
  refine ⟨ccmRationalIntegralFiniteAdeleDiagonal 1, ?_⟩
  change N • ccmRationalIntegralFiniteAdeleDiagonal 1 =
    ccmRationalIntegralFiniteAdeleDiagonal (N : ℤ)
  simpa using
    (map_nsmul ccmRationalIntegralFiniteAdeleDiagonal N (1 : ℤ)).symm

/-- Diagonal congruence map into the actual integral finite-adele quotient. -/
def ccmRationalZModToIntegralFiniteAdeleQuotient (N : ℕ) :
    ZMod N →+ ccmRationalIntegralFiniteAdelesAddSubgroup ⧸
      (nsmulAddMonoidHom N).range :=
  ZMod.lift N
    ⟨ccmRationalIntegralFiniteAdeleQuotientDiagonal N,
      ccmRationalIntegralFiniteAdeleQuotientDiagonal_natCast_eq_zero N⟩

/-- The actual diagonal congruence map is injective. -/
theorem ccmRationalZModToIntegralFiniteAdeleQuotient_injective
    (N : ℕ) (hN : N ≠ 0) :
    Function.Injective
      (ccmRationalZModToIntegralFiniteAdeleQuotient N) := by
  rw [ccmRationalZModToIntegralFiniteAdeleQuotient,
    ZMod.lift_injective]
  intro m hm
  have hmemH : ccmRationalIntegralFiniteAdeleDiagonal m ∈
      (nsmulAddMonoidHom
        (α := ccmRationalIntegralFiniteAdelesAddSubgroup) N).range :=
    (QuotientAddGroup.eq_zero_iff _).mp hm
  obtain ⟨x, hx⟩ := hmemH
  have hmemK : ccmRationalProfiniteIntegerDiagonal m ∈
      (nsmulAddMonoidHom
        (α := CCMRationalProfiniteIntegers) N).range := by
    refine ⟨ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles.symm x,
      ?_⟩
    change N •
        ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles.symm x =
      ccmRationalProfiniteIntegerDiagonal m
    apply ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles.injective
    rw [map_nsmul, AddEquiv.apply_symm_apply]
    change N • x =
      ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles
        (ccmRationalProfiniteIntegerDiagonal m)
    rw [ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles_diagonal]
    exact hx
  have hqzero :
      ccmRationalProfiniteIntegerQuotientDiagonal N m = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 hmemK
  apply ccmRationalZModToProfiniteIntegerQuotient_injective N hN
  simpa [ccmRationalZModToProfiniteIntegerQuotient] using hqzero

/-- **Actual integral-adele cyclic quotient law.** The quotient by `N` is
`ZMod N`, induced by literal diagonal integers. -/
noncomputable def ccmRationalZModEquivIntegralFiniteAdeleQuotient
    (N : ℕ) (hN : N ≠ 0) :
    ZMod N ≃+ ccmRationalIntegralFiniteAdelesAddSubgroup ⧸
      (nsmulAddMonoidHom N).range := by
  letI : Finite (ccmRationalIntegralFiniteAdelesAddSubgroup ⧸
      (nsmulAddMonoidHom N).range) := by
    apply Nat.finite_of_card_ne_zero
    rw [← AddSubgroup.index_eq_card,
      ccmRationalIntegralFiniteAdelesNSMul_index hN]
    exact hN
  apply AddEquiv.ofBijective
    (ccmRationalZModToIntegralFiniteAdeleQuotient N)
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨ccmRationalZModToIntegralFiniteAdeleQuotient_injective N hN, ?_⟩
  rw [Nat.card_zmod, ← AddSubgroup.index_eq_card,
    ccmRationalIntegralFiniteAdelesNSMul_index hN]

/-- Opaque surjectivity boundary for the literal diagonal congruence map.
Downstream arguments can use this theorem without unfolding the cardinality
construction of the additive equivalence. -/
theorem ccmRationalZModToIntegralFiniteAdeleQuotient_surjective
    (N : ℕ) (hN : N ≠ 0) :
    Function.Surjective
      (ccmRationalZModToIntegralFiniteAdeleQuotient N) := by
  let e := ccmRationalZModEquivIntegralFiniteAdeleQuotient N hN
  intro y
  obtain ⟨r, hr⟩ := e.surjective y
  exact ⟨r, hr⟩

end RHTower
end GaloisForLFunctions
