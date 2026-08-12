import GaloisForLFunctions.RHTower.DeningerRationalWittFieldIntersection
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Nilpotent kernel of the rational-Witt comparison

This module formalizes the nilpotent-kernel statements in Deninger 2025, Remark 1.3.  It defines
the actual reduced monoid algebra as the quotient ring `ℤ[A]/((0))` and descends the Teichmüller
comparison to its underlying additive group and the literal rational-Witt carrier.

If `a ≠ 0` and `a² = 0`, the class `2(a) - (2a)` is proved nonzero in the quotient and is killed
by the comparison.  In characteristic a prime `p`, if `a ≠ 0` and `a^p = 0`, then `[a]` is
nonzero, `p(a)` is nonzero, and `p[a] = 0`.  Consequently both the comparison and multiplication
by `p` on the rational-Witt additive group are noninjective.  All nonvanishing claims are proved
coefficientwise in the quotient; none are assumptions.
-/

namespace RHTower

noncomputable section

def deningerReducedMonoidAlgebraZeroAtom (A : Type*) [CommRing A] : MonoidAlgebra ℤ A :=
  MonoidAlgebra.single 0 1

def deningerReducedMonoidAlgebraZeroIdeal (A : Type*) [CommRing A] : Ideal (MonoidAlgebra ℤ A) :=
  Ideal.span {deningerReducedMonoidAlgebraZeroAtom A}

abbrev DeningerReducedMonoidAlgebra (A : Type*) [CommRing A] :=
  (MonoidAlgebra ℤ A) ⧸ deningerReducedMonoidAlgebraZeroIdeal A

noncomputable def deningerRationalWittOmegaLift
    (A : Type*) [CommRing A] :
    MonoidAlgebra ℤ A →+ Additive (DeningerRationalWittAdditive A) :=
  (Finsupp.liftAddHom (α := A) (M := ℤ)
    (N := Additive (DeningerRationalWittAdditive A))
    (fun a => zmultiplesHom (Additive (DeningerRationalWittAdditive A))
      (Additive.ofMul (deningerRationalWittTeichmuller a)))).comp
    MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

@[simp] theorem deningerRationalWittOmegaLift_single
    {A : Type*} [CommRing A] (a : A) (n : ℤ) :
    deningerRationalWittOmegaLift A (MonoidAlgebra.single a n) =
      n • Additive.ofMul (deningerRationalWittTeichmuller a) := by
  simp [deningerRationalWittOmegaLift]

@[simp] theorem deningerRationalWittTeichmuller_zero
    {A : Type*} [CommRing A] :
    deningerRationalWittTeichmuller (0 : A) = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (deningerRationalWittTeichmullerUnit (0 : A) :
    DeningerRationalWittLocalization A) = 1
  rw [deningerRationalWittTeichmullerUnit_val]
  simp [deningerRationalWittTeichmullerPolynomial]

@[simp] theorem deningerRationalWittOmegaLift_zeroAtom
    {A : Type*} [CommRing A] : deningerRationalWittOmegaLift A (deningerReducedMonoidAlgebraZeroAtom A) = 0 := by
  rw [deningerReducedMonoidAlgebraZeroAtom, deningerRationalWittOmegaLift_single]
  rw [one_smul]
  apply Additive.toMul.injective
  change deningerRationalWittTeichmuller (0 : A) = 1
  exact deningerRationalWittTeichmuller_zero

theorem deningerRationalWittOmegaLift_mul_zeroAtom
    {A : Type*} [CommRing A] (x : MonoidAlgebra ℤ A) :
    deningerRationalWittOmegaLift A (x * deningerReducedMonoidAlgebraZeroAtom A) = 0 := by
  induction x using MonoidAlgebra.induction with
  | zero => simp
  | single_add a n x _ha _hn ih =>
      rw [add_mul, map_add, ih, add_zero]
      simp [deningerReducedMonoidAlgebraZeroAtom]

theorem deningerReducedMonoidAlgebra_coeff_mul_zeroAtom_of_ne_zero
    {A : Type*} [CommRing A] (x : MonoidAlgebra ℤ A)
    {a : A} (ha : a ≠ 0) :
    (x * deningerReducedMonoidAlgebraZeroAtom A).coeff a = 0 := by
  induction x using MonoidAlgebra.induction with
  | zero => simp
  | single_add b n x _hb _hn ih =>
      rw [add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply, ih, add_zero]
      simp [deningerReducedMonoidAlgebraZeroAtom, ha]

noncomputable def deningerRationalWittOmega
    (A : Type*) [CommRing A] :
    DeningerReducedMonoidAlgebra A →+ Additive (DeningerRationalWittAdditive A) :=
  QuotientAddGroup.lift (deningerReducedMonoidAlgebraZeroIdeal A).toAddSubgroup (deningerRationalWittOmegaLift A) (by
    intro x hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hx
    rw [← hy]
    exact deningerRationalWittOmegaLift_mul_zeroAtom y)

@[simp] theorem deningerRationalWittOmega_mk_single
    {A : Type*} [CommRing A] (a : A) (n : ℤ) :
    deningerRationalWittOmega A (Ideal.Quotient.mk (deningerReducedMonoidAlgebraZeroIdeal A)
      (MonoidAlgebra.single a n)) =
      n • Additive.ofMul (deningerRationalWittTeichmuller a) := by
  exact deningerRationalWittOmegaLift_single a n

noncomputable def deningerSquareZeroKernelClass
    {A : Type*} [CommRing A] (a : A) : DeningerReducedMonoidAlgebra A :=
  Ideal.Quotient.mk (deningerReducedMonoidAlgebraZeroIdeal A)
    (2 • MonoidAlgebra.single a (1 : ℤ) -
      MonoidAlgebra.single (2 * a) (1 : ℤ))

theorem deningerSquareZeroKernelClass_ne_zero
    {A : Type*} [CommRing A] (a : A) (ha : a ≠ 0) :
    deningerSquareZeroKernelClass a ≠ 0 := by
  intro hz
  have hmem :
      2 • MonoidAlgebra.single a (1 : ℤ) -
          MonoidAlgebra.single (2 * a) (1 : ℤ) ∈ deningerReducedMonoidAlgebraZeroIdeal A := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
  have hcoeff := congrArg (fun z : MonoidAlgebra ℤ A => z.coeff a) hy
  rw [deningerReducedMonoidAlgebra_coeff_mul_zeroAtom_of_ne_zero y ha] at hcoeff
  have h2a : 2 * a ≠ a := by
    intro h
    have hz' := congrArg (fun z : A => z - a) h
    apply ha
    simpa [two_mul] using hz'
  simp [h2a] at hcoeff

theorem deningerRationalWittTeichmuller_mul_self_of_sq_zero
    {A : Type*} [CommRing A] (a : A) (ha2 : a ^ 2 = 0) :
    deningerRationalWittTeichmuller a * deningerRationalWittTeichmuller a =
      deningerRationalWittTeichmuller (2 * a) := by
  apply Subtype.ext
  apply Units.ext
  change (deningerRationalWittTeichmullerUnit a :
      DeningerRationalWittLocalization A) *
      deningerRationalWittTeichmullerUnit a =
    deningerRationalWittTeichmullerUnit (2 * a)
  rw [deningerRationalWittTeichmullerUnit_val, ← map_mul]
  congr 1
  simp only [deningerRationalWittTeichmullerPolynomial]
  ring_nf
  have hCa : (Polynomial.C a) ^ 2 = 0 := by
    rw [← map_pow, ha2, map_zero]
  rw [hCa]
  simp [map_mul]
  rw [map_ofNat]
  ac_rfl

theorem deningerSquareZeroKernelClass_mem_ker
    {A : Type*} [CommRing A] (a : A) (ha2 : a ^ 2 = 0) :
    deningerRationalWittOmega A (deningerSquareZeroKernelClass a) = 0 := by
  change deningerRationalWittOmegaLift A
      (2 • MonoidAlgebra.single a (1 : ℤ) -
        MonoidAlgebra.single (2 * a) (1 : ℤ)) = 0
  rw [map_sub, map_nsmul, deningerRationalWittOmegaLift_single, deningerRationalWittOmegaLift_single]
  simp only [one_smul]
  apply Additive.toMul.injective
  change (deningerRationalWittTeichmuller a) ^ 2 *
      (deningerRationalWittTeichmuller (2 * a))⁻¹ = 1
  rw [pow_two, deningerRationalWittTeichmuller_mul_self_of_sq_zero a ha2]
  simp

noncomputable def deningerReducedMonoidAlgebraAtom
    {A : Type*} [CommRing A] (a : A) : DeningerReducedMonoidAlgebra A :=
  Ideal.Quotient.mk (deningerReducedMonoidAlgebraZeroIdeal A) (MonoidAlgebra.single a (1 : ℤ))

theorem deningerReducedMonoidAlgebraAtom_nsmul_ne_zero
    {A : Type*} [CommRing A] (a : A) (ha : a ≠ 0)
    (n : ℕ) (hn : n ≠ 0) : n • deningerReducedMonoidAlgebraAtom a ≠ 0 := by
  intro hz
  have hz' : Ideal.Quotient.mk (deningerReducedMonoidAlgebraZeroIdeal A)
      (n • MonoidAlgebra.single a (1 : ℤ)) = 0 := by
    rw [map_nsmul]
    exact hz
  have hmem : n • MonoidAlgebra.single a (1 : ℤ) ∈ deningerReducedMonoidAlgebraZeroIdeal A :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz'
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
  have hcoeff := congrArg (fun z : MonoidAlgebra ℤ A => z.coeff a) hy
  rw [deningerReducedMonoidAlgebra_coeff_mul_zeroAtom_of_ne_zero y ha] at hcoeff
  simp at hcoeff
  exact hn (Int.ofNat_injective hcoeff.symm)

theorem deningerRationalWittOmega_atom_ne_zero
    {A : Type*} [CommRing A] (a : A) (ha : a ≠ 0) :
    deningerRationalWittOmega A (deningerReducedMonoidAlgebraAtom a) ≠ 0 := by
  intro hz
  have hz' : deningerRationalWittTeichmuller a = 1 := by
    have h := congrArg Additive.toMul hz
    simpa [deningerReducedMonoidAlgebraAtom] using h
  have hloc := congrArg
    (fun w : DeningerRationalWittAdditive A =>
      deningerRationalWittLocalizationToPowerSeries A (w.1 : _)) hz'
  have hcoeff := congrArg (PowerSeries.coeff 1) hloc
  simp [deningerRationalWittTeichmuller,
    deningerRationalWittTeichmullerUnit,
    deningerRationalWittTeichmullerPolynomial,
    deningerRationalWittLocalizationToPowerSeries,
    IsLocalization.lift_eq] at hcoeff
  exact ha hcoeff

@[simp] theorem deningerRationalWittOmega_atom
    {A : Type*} [CommRing A] (a : A) :
    deningerRationalWittOmega A (deningerReducedMonoidAlgebraAtom a) =
      Additive.ofMul (deningerRationalWittTeichmuller a) := by
  rw [deningerReducedMonoidAlgebraAtom, deningerRationalWittOmega_mk_single, one_smul]

theorem deningerRationalWittTeichmuller_pow_eq_one_of_pow_eq_zero
    {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime) [CharP A p]
    (a : A) (ha : a ^ p = 0) :
    deningerRationalWittTeichmuller a ^ p = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  apply Subtype.ext
  apply Units.ext
  change (deningerRationalWittTeichmullerUnit a :
      DeningerRationalWittLocalization A) ^ p = 1
  rw [deningerRationalWittTeichmullerUnit_val, ← map_pow]
  simp only [deningerRationalWittTeichmullerPolynomial, sub_eq_add_neg]
  rw [add_pow_char]
  have hbase : (Polynomial.C a * Polynomial.X) ^ p = 0 := by
    rw [mul_pow, ← map_pow, ha, map_zero, zero_mul]
  have hneg : (-(Polynomial.C a * Polynomial.X)) ^ p = 0 := by
    rw [neg_pow, hbase]
    simp
  rw [hneg]
  simp

theorem deningerPrimeNilpotentKernel
    {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime) [CharP A p]
    (a : A) (_ha : a ≠ 0) (hap : a ^ p = 0) :
    deningerRationalWittOmega A (p • deningerReducedMonoidAlgebraAtom a) = 0 := by
  rw [map_nsmul, deningerRationalWittOmega_atom]
  apply Additive.toMul.injective
  change deningerRationalWittTeichmuller a ^ p = 1
  exact deningerRationalWittTeichmuller_pow_eq_one_of_pow_eq_zero p hp a hap

theorem deningerSquareZeroKernelWitness
    {A : Type*} [CommRing A] (a : A) (ha : a ≠ 0) (ha2 : a ^ 2 = 0) :
    deningerSquareZeroKernelClass a ≠ 0 ∧
      deningerRationalWittOmega A (deningerSquareZeroKernelClass a) = 0 :=
  ⟨deningerSquareZeroKernelClass_ne_zero a ha,
    deningerSquareZeroKernelClass_mem_ker a ha2⟩

theorem deningerPrimeNilpotentOmega_not_injective
    {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime) [CharP A p]
    (a : A) (ha : a ≠ 0) (hap : a ^ p = 0) :
    ¬ Function.Injective (deningerRationalWittOmega A) := by
  intro hinj
  have hzero := deningerPrimeNilpotentKernel p hp a ha hap
  have hclass : p • deningerReducedMonoidAlgebraAtom a = 0 := by
    apply hinj
    simpa using hzero
  exact deningerReducedMonoidAlgebraAtom_nsmul_ne_zero a ha p hp.ne_zero hclass

theorem deningerPrimeNilpotentNsmul_not_injective
    {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime) [CharP A p]
    (a : A) (ha : a ≠ 0) (hap : a ^ p = 0) :
    ¬ Function.Injective
      (fun w : Additive (DeningerRationalWittAdditive A) => p • w) := by
  intro hinj
  have hzero : p • deningerRationalWittOmega A (deningerReducedMonoidAlgebraAtom a) = 0 := by
    rw [← map_nsmul]
    exact deningerPrimeNilpotentKernel p hp a ha hap
  have hatom : deningerRationalWittOmega A (deningerReducedMonoidAlgebraAtom a) = 0 := by
    apply hinj
    simpa using hzero
  exact deningerRationalWittOmega_atom_ne_zero a ha hatom

theorem deningerPrimeNilpotentKernelWitness
    {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime) [CharP A p]
    (a : A) (ha : a ≠ 0) (hap : a ^ p = 0) :
    deningerRationalWittOmega A (deningerReducedMonoidAlgebraAtom a) ≠ 0 ∧
      p • deningerReducedMonoidAlgebraAtom a ≠ 0 ∧
      deningerRationalWittOmega A (p • deningerReducedMonoidAlgebraAtom a) = 0 ∧
      ¬ Function.Injective (deningerRationalWittOmega A) ∧
      ¬ Function.Injective
        (fun w : Additive (DeningerRationalWittAdditive A) => p • w) :=
  ⟨deningerRationalWittOmega_atom_ne_zero a ha,
    deningerReducedMonoidAlgebraAtom_nsmul_ne_zero a ha p hp.ne_zero,
    deningerPrimeNilpotentKernel p hp a ha hap,
    deningerPrimeNilpotentOmega_not_injective p hp a ha hap,
    deningerPrimeNilpotentNsmul_not_injective p hp a ha hap⟩


end
end RHTower
