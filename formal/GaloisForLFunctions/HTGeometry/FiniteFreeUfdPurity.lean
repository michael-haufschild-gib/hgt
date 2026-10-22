import GaloisForLFunctions.HTGeometry.FiniteFreeDiscriminant
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Purity of the branch locus for finite free algebras over a UFD

Let `A` be a unique factorization domain and `B` a finite free `A`-algebra. This module proves a
purity statement for unramifiedness: if `B` is formally unramified after localizing at every
principal prime `(p)` of `A`, and the discriminant of a basis is nonzero (for instance because the
generic fibre over `Frac A` is formally unramified), then `B` is formally unramified over `A`.
The argument factors the discriminant: a non-unit nonzero discriminant has a prime factor `p`,
and its image in `A_(p)` must be a unit by the local hypothesis, which is impossible.

## Main results

- `discr_ne_zero_of_fraction_formallyUnramified`: for an injective finite free extension of domains
  with formally unramified generic fibre, the discriminant of every basis is nonzero.
- `formallyUnramified_of_discr_nonzero_of_prime_localizations`: over a UFD, nonzero discriminant
  plus formal unramifiedness at every principal prime localization implies `B` is formally
  unramified over `A`.
- `formallyUnramified_of_fraction_formallyUnramified_of_prime_localizations`: over a UFD, formally
  unramified generic fibre plus formal unramifiedness at every principal prime localization implies
  `B` is formally unramified over `A`.

## Hypotheses

No analytic inputs. The theorems are implications whose substantive algebraic hypotheses are:
formal unramifiedness of the generic fibre `Localization (algebraMapSubmonoid B A⁰)` over
`FractionRing A` (an instance argument), formal unramifiedness of `B_(p)` over `A_(p)` for every
prime element `p` (the argument `hprime`), and, in the middle theorem, `discr A b ≠ 0`.
-/

open scoped TensorProduct

namespace Algebra


open nonZeroDivisors

universe u v w

/-- Let `A ⊆ B` be domains with `B` finite free over `A`. Assuming the generic fibre (`B` localized
at the nonzero elements of `A`) is formally unramified over `Frac A`, the discriminant of every
basis of `B` over `A` is nonzero. -/
theorem discr_ne_zero_of_fraction_formallyUnramified
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [Module.Free A B] [Module.Finite A B]
    [FormallyUnramified (FractionRing A)
      (Localization (Algebra.algebraMapSubmonoid B A⁰))]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A B) : discr A b ≠ 0 := by
  let BF := Localization (Algebra.algebraMapSubmonoid B A⁰)
  have hM : Algebra.algebraMapSubmonoid B A⁰ ≤ B⁰ :=
    Submonoid.map_le_of_le_comap _ <|
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective A B))
  letI : IsDomain BF :=
    IsLocalization.isDomain_of_le_nonZeroDivisors BF hM
  let e : FractionRing A ⊗[A] B ≃ₐ[FractionRing A] BF :=
    Localization.tensorRightAlgEquiv A⁰ B
  let bF : Module.Basis ι (FractionRing A) BF :=
    (b.baseChange (FractionRing A)).map e.toLinearEquiv
  letI : Module.Free (FractionRing A) BF := Module.Free.of_basis bF
  have hunit : IsUnit (discr (FractionRing A) bF) :=
    isUnit_discr_of_formallyUnramified bF
  have hbase : discr (FractionRing A) bF =
      algebraMap A (FractionRing A) (discr A b) := by
    calc
      discr (FractionRing A) bF =
          discr (FractionRing A) (b.baseChange (FractionRing A)) := by
        rw [discr_eq_discr_of_algEquiv (b.baseChange (FractionRing A)) e]
        rfl
      _ = algebraMap A (FractionRing A) (discr A b) := by
        rw [discr_def, traceMatrix_baseChange, ← RingHom.map_det, ← discr_def]
  intro hzero
  rw [hbase, hzero, map_zero] at hunit
  exact not_isUnit_zero hunit

/-- Over a UFD `A`, a finite free algebra `B` with basis `b` is formally unramified, assuming
`hdiscr : discr A b ≠ 0` and `hprime`: `B_(p)` is formally unramified over `A_(p)` for every prime
element `p`. -/
theorem formallyUnramified_of_discr_nonzero_of_prime_localizations
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A B) (hdiscr : discr A b ≠ 0)
    (hprime : ∀ (p : A) (hp : Prime p),
      let _ : (Ideal.span {p}).IsPrime :=
        (Ideal.span_singleton_prime hp.ne_zero).mpr hp
      FormallyUnramified
        (Localization.AtPrime (Ideal.span {p}))
        (Localization (Algebra.algebraMapSubmonoid B
          (Ideal.span {p}).primeCompl))) :
    FormallyUnramified A B := by
  apply formallyUnramified_of_isUnit_discr b
  by_contra hunit
  obtain ⟨p, hpirreducible, hpdiv⟩ :=
    WfDvdMonoid.exists_irreducible_factor hunit hdiscr
  have hpprime : Prime p :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hpirreducible
  let P : Ideal A := Ideal.span {p}
  letI hP : P.IsPrime := by
    dsimp only [P]
    exact (Ideal.span_singleton_prime hpprime.ne_zero).mpr hpprime
  let Ap := Localization.AtPrime P
  let Bp := Localization (Algebra.algebraMapSubmonoid B P.primeCompl)
  let e : Ap ⊗[A] B ≃ₐ[Ap] Bp :=
    Localization.tensorRightAlgEquiv P.primeCompl B
  let bp : Module.Basis ι Ap Bp :=
    (b.baseChange Ap).map e.toLinearEquiv
  letI : Module.Free Ap Bp := Module.Free.of_basis bp
  haveI : FormallyUnramified Ap Bp := hprime p hpprime
  have hbpunit : IsUnit (discr Ap bp) :=
    isUnit_discr_of_formallyUnramified bp
  have hbase : discr Ap bp = algebraMap A Ap (discr A b) := by
    calc
      discr Ap bp = discr Ap (b.baseChange Ap) := by
        rw [discr_eq_discr_of_algEquiv (b.baseChange Ap) e]
        rfl
      _ = algebraMap A Ap (discr A b) := by
        rw [discr_def, traceMatrix_baseChange, ← RingHom.map_det, ← discr_def]
  rw [hbase] at hbpunit
  obtain ⟨c, hc⟩ := hpdiv
  have hpmapunit : IsUnit (algebraMap A Ap p) := by
    rw [hc, map_mul, IsUnit.mul_iff] at hbpunit
    exact hbpunit.1
  have hpmem : algebraMap A Ap p ∈ IsLocalRing.maximalIdeal Ap := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff Ap P]
    exact Ideal.mem_span_singleton_self p
  exact ((IsLocalRing.mem_maximalIdeal _).mp hpmem) hpmapunit

/-- Purity over a UFD: if `A ⊆ B` are domains with `B` finite free over the UFD `A`, the generic
fibre is formally unramified, and (`hprime`) `B_(p)` is formally unramified over `A_(p)` for every
prime element `p`, then `B` is formally unramified over `A`. -/
theorem formallyUnramified_of_fraction_formallyUnramified_of_prime_localizations
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B]
    [Module.Free A B] [Module.Finite A B]
    [FormallyUnramified (FractionRing A)
      (Localization (Algebra.algebraMapSubmonoid B A⁰))]
    (hprime : ∀ (p : A) (hp : Prime p),
      let _ : (Ideal.span {p}).IsPrime :=
        (Ideal.span_singleton_prime hp.ne_zero).mpr hp
      FormallyUnramified
        (Localization.AtPrime (Ideal.span {p}))
        (Localization (Algebra.algebraMapSubmonoid B
          (Ideal.span {p}).primeCompl))) :
    FormallyUnramified A B := by
  classical
  let b := Module.Free.chooseBasis A B
  exact formallyUnramified_of_discr_nonzero_of_prime_localizations b
    (discr_ne_zero_of_fraction_formallyUnramified b) hprime

end Algebra
