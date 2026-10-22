import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittSource
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeFiniteCyclotomicReductionSystem
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Algebraically closed rational-Witt source presentation

For a field `K`, the reduced monoid algebra of the multiplicative monoid is the group ring
`ℤ[Kˣ]`: the zero atom has been killed and all remaining atoms are units.  Deninger's comparison
sends the atom at `a` to the literal rational-Witt element `[a] = 1 - aT`.

This module constructs that map against the localized-polynomial source, rather than against an
abstract presentation.  It proves its surjectivity for every algebraically closed field by an
explicit normalized factorization: a polynomial with constant coefficient one is the product of
the factors `1 - r⁻¹T` over its nonzero roots.  Consequently every normalized rational function
`P/Q` is a quotient of finite products of Teichmüller atoms.

Injectivity, hence transport of Witt multiplication, remains logically separate: it is the
finite-support multiplicative-independence theorem for the factors `1-aT`.
-/

namespace RHTower

noncomputable section

open scoped BigOperators

/-- Additive comparison from the reduced monoid algebra `ℤ[Kˣ]` to the literal rational-Witt
carrier.  Addition of group-ring coefficients becomes multiplication of rational functions. -/
noncomputable def deningerRationalWittReducedMonoidAlgebraToAdditive
    (K : Type*) [Field K] :
    MonoidAlgebra ℤ Kˣ →+ Additive (DeningerRationalWittAdditive K) :=
  (Finsupp.liftAddHom (α := Kˣ) (M := ℤ)
    (N := Additive (DeningerRationalWittAdditive K))
    (fun a => zmultiplesHom (Additive (DeningerRationalWittAdditive K))
      (Additive.ofMul
        (deningerRationalWittTeichmuller (A := K) (a : K))))).comp
    MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

@[simp] theorem deningerRationalWittReducedMonoidAlgebraToAdditive_single
    {K : Type*} [Field K] (a : Kˣ) (n : ℤ) :
    deningerRationalWittReducedMonoidAlgebraToAdditive K
        (MonoidAlgebra.single a n) =
      n • Additive.ofMul
        (deningerRationalWittTeichmuller (A := K) (a : K)) := by
  simp [deningerRationalWittReducedMonoidAlgebraToAdditive]

/-- Finite sum of unit atoms in the reduced monoid algebra. -/
noncomputable def deningerRationalWittAtomSum
    {K : Type*} [Field K] (s : Multiset Kˣ) : MonoidAlgebra ℤ Kˣ :=
  (s.map fun a : Kˣ => MonoidAlgebra.single a (1 : ℤ)).sum

@[simp] theorem deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum
    {K : Type*} [Field K] (s : Multiset Kˣ) :
    deningerRationalWittReducedMonoidAlgebraToAdditive K
        (deningerRationalWittAtomSum s) =
      (s.map fun a : Kˣ => Additive.ofMul
        (deningerRationalWittTeichmuller (A := K) (a : K))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [deningerRationalWittAtomSum]
  | @cons a s ih =>
      rw [show deningerRationalWittAtomSum (a ::ₘ s) =
        MonoidAlgebra.single a 1 + deningerRationalWittAtomSum s by
          simp [deningerRationalWittAtomSum]]
      rw [map_add, deningerRationalWittReducedMonoidAlgebraToAdditive_single, ih]
      simp

theorem deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum_toMul
    {K : Type*} [Field K] (s : Multiset Kˣ) :
    Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive K
          (deningerRationalWittAtomSum s)) =
      (s.map fun a : Kˣ =>
        deningerRationalWittTeichmuller (A := K) (a : K)).prod := by
  simp [deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum]

/-- Exact factorization of a constant-term-one polynomial over an algebraically closed field into
literal Teichmüller polynomials. -/
theorem deningerPolynomial_eq_prod_teichmuller_of_isAlgClosed
    {K : Type*} [Field K] [IsAlgClosed K]
    (P : Polynomial K) (hP : P.coeff 0 = 1) :
    P = (P.roots.map fun r =>
      1 - Polynomial.C r⁻¹ * Polynomial.X).prod := by
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, Polynomial.coeff_zero] at hP
    exact zero_ne_one hP
  have hrs : ∀ r ∈ P.roots, r ≠ 0 := by
    intro r hr hr0
    subst r
    have hrEval : P.eval 0 = 0 := (Polynomial.mem_roots hP0).mp hr
    rw [← Polynomial.coeff_zero_eq_eval_zero, hP] at hrEval
    exact one_ne_zero hrEval
  have hc := (IsAlgClosed.splits P).coeff_zero_eq_leadingCoeff_mul_prod_roots
  rw [hP] at hc
  have hcard : P.roots.card = P.natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits P)
  have hprod0 : P.roots.prod ≠ 0 :=
    Multiset.prod_ne_zero (fun hz => hrs 0 hz rfl)
  have hsquare : (-1 : K) ^ P.natDegree * (-1 : K) ^ P.natDegree = 1 := by
    rcases neg_one_pow_eq_or K P.natDegree with hs | hs <;> simp [hs]
  have hscalar : (P.roots.map fun r => -r⁻¹).prod = P.leadingCoeff := by
    calc
      (P.roots.map fun r => -r⁻¹).prod =
          ((P.roots.map fun r => r⁻¹).map Neg.neg).prod := by
        rw [Multiset.map_map]
        rfl
      _ = (-1 : K) ^ P.roots.card * (P.roots.map fun r => r⁻¹).prod := by
        simpa using Multiset.prod_map_neg (P.roots.map fun r => r⁻¹)
      _ = (-1 : K) ^ P.natDegree * P.roots.prod⁻¹ := by
        rw [hcard, Multiset.prod_map_inv]
        simp
      _ = P.leadingCoeff := by
        calc
          (-1 : K) ^ P.natDegree * P.roots.prod⁻¹ =
              ((-1 : K) ^ P.natDegree * P.roots.prod⁻¹) * 1 := by rw [mul_one]
          _ = ((-1 : K) ^ P.natDegree * P.roots.prod⁻¹) *
              ((-1 : K) ^ P.natDegree * P.leadingCoeff * P.roots.prod) := by
            rw [← hc]
          _ = P.leadingCoeff := by
            field_simp [hprod0]
            rw [pow_two, hsquare, one_mul]
  have hfactor : ∀ r : K, r ≠ 0 →
      1 - Polynomial.C r⁻¹ * Polynomial.X =
        Polynomial.C (-r⁻¹) * (Polynomial.X - Polynomial.C r) := by
    intro r hr
    rw [mul_sub, ← Polynomial.C_mul]
    simp [hr]
    ring
  calc
    P = Polynomial.C P.leadingCoeff *
        (P.roots.map fun r => Polynomial.X - Polynomial.C r).prod :=
      (IsAlgClosed.splits P).eq_prod_roots
    _ = Polynomial.C (P.roots.map fun r => -r⁻¹).prod *
        (P.roots.map fun r => Polynomial.X - Polynomial.C r).prod := by rw [hscalar]
    _ = ((P.roots.map fun r => Polynomial.C (-r⁻¹)).prod) *
        (P.roots.map fun r => Polynomial.X - Polynomial.C r).prod := by
      rw [map_multiset_prod, Multiset.map_map]
      rfl
    _ = (P.roots.map fun r =>
        Polynomial.C (-r⁻¹) * (Polynomial.X - Polynomial.C r)).prod := by
      rw [Multiset.prod_map_mul]
    _ = (P.roots.map fun r =>
        1 - Polynomial.C r⁻¹ * Polynomial.X).prod := by
      congr 1
      apply Multiset.map_congr rfl
      intro r hr
      exact (hfactor r (hrs r hr)).symm

/-- Multiset of nonzero Teichmüller atoms obtained by inverting the roots of a normalized
polynomial. -/
noncomputable def deningerNormalizedPolynomialRootUnits
    {K : Type*} [Field K] (P : Polynomial K)
    (hP : P.coeff 0 = 1) : Multiset Kˣ :=
  P.roots.attach.map fun r =>
    Units.mk0 r.1⁻¹ (inv_ne_zero (by
      intro hr0
      have hP0 : P ≠ 0 := by
        intro h
        rw [h, Polynomial.coeff_zero] at hP
        exact zero_ne_one hP
      have hrEval : P.eval 0 = 0 :=
        (Polynomial.mem_roots hP0).mp (hr0 ▸ r.2)
      rw [← Polynomial.coeff_zero_eq_eval_zero, hP] at hrEval
      exact one_ne_zero hrEval))

@[simp] theorem deningerNormalizedPolynomialRootUnits_coe
    {K : Type*} [Field K] (P : Polynomial K)
    (hP : P.coeff 0 = 1) :
    (deningerNormalizedPolynomialRootUnits P hP).map
        (fun r : Kˣ => (r : K)) =
      P.roots.map fun r => r⁻¹ := by
  simp [deningerNormalizedPolynomialRootUnits]

theorem deningerPolynomial_eq_prod_normalizedRootUnits
    {K : Type*} [Field K] [IsAlgClosed K]
    (P : Polynomial K) (hP : P.coeff 0 = 1) :
    P = ((deningerNormalizedPolynomialRootUnits P hP).map fun r : Kˣ =>
      deningerRationalWittTeichmullerPolynomial (r : K)).prod := by
  calc
    P = (P.roots.map fun r =>
        1 - Polynomial.C r⁻¹ * Polynomial.X).prod :=
      deningerPolynomial_eq_prod_teichmuller_of_isAlgClosed P hP
    _ = ((P.roots.map fun r => r⁻¹).map fun a : K =>
        1 - Polynomial.C a * Polynomial.X).prod := by
      rw [Multiset.map_map]
      rfl
    _ = (((deningerNormalizedPolynomialRootUnits P hP).map
        fun r : Kˣ => (r : K)).map
        fun a : K => 1 - Polynomial.C a * Polynomial.X).prod := by
      rw [deningerNormalizedPolynomialRootUnits_coe P hP]
    _ = ((deningerNormalizedPolynomialRootUnits P hP).map fun r : Kˣ =>
        deningerRationalWittTeichmullerPolynomial (r : K)).prod := by
      rw [Multiset.map_map]
      simp only [Function.comp_apply,
        deningerRationalWittTeichmullerPolynomial]

theorem deningerRationalWitt_prod_teichmuller_val
    {K : Type*} [Field K] (s : Multiset Kˣ) :
    ((((s.map fun a : Kˣ =>
        deningerRationalWittTeichmuller (A := K) (a : K)).prod).1 :
          (DeningerRationalWittLocalization K)ˣ) :
      DeningerRationalWittLocalization K) =
      algebraMap (Polynomial K) (DeningerRationalWittLocalization K)
        ((s.map fun a : Kˣ =>
          deningerRationalWittTeichmullerPolynomial (a : K)).prod) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons,
        Multiset.map_cons, Multiset.prod_cons]
      change (deningerRationalWittTeichmullerUnit (a : K) :
          DeningerRationalWittLocalization K) *
          ((((s.map fun b : Kˣ =>
            deningerRationalWittTeichmuller (b : K)).prod).1 :
            (DeningerRationalWittLocalization K)ˣ) :
            DeningerRationalWittLocalization K) = _
      rw [deningerRationalWittTeichmullerUnit_val, ih, map_mul]

@[simp] theorem deningerRationalWittTeichmullerPolynomial_roots
    {K : Type*} [Field K] (a : Kˣ) :
    (deningerRationalWittTeichmullerPolynomial (a : K)).roots =
      {(a : K)⁻¹} := by
  rw [show deningerRationalWittTeichmullerPolynomial (a : K) =
      Polynomial.C (-(a : K)) * Polynomial.X + Polynomial.C 1 by
    simp [deningerRationalWittTeichmullerPolynomial]
    ring]
  rw [Polynomial.roots_C_mul_X_add_C]
  · congr 2
    field_simp [a.ne_zero]
  · exact neg_ne_zero.mpr a.ne_zero

/-- Roots recover the complete atom multiset of a finite Teichmüller product. -/
theorem deningerRationalWitt_prod_teichmullerPolynomial_roots
    {K : Type*} [Field K] (s : Multiset Kˣ) :
    ((s.map fun a : Kˣ =>
      deningerRationalWittTeichmullerPolynomial (a : K)).prod).roots =
      s.map fun a : Kˣ => (a : K)⁻¹ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha : deningerRationalWittTeichmullerPolynomial (a : K) ≠ 0 := by
        intro h
        have hc := congrArg (fun P : Polynomial K => P.coeff 0) h
        simp at hc
      have hs : (s.map fun b : Kˣ =>
          deningerRationalWittTeichmullerPolynomial (b : K)).prod ≠ 0 := by
        apply Multiset.prod_ne_zero
        intro hp
        obtain ⟨b, _, hb⟩ := Multiset.mem_map.mp hp
        have hc := congrArg (fun P : Polynomial K => P.coeff 0) hb
        simp at hc
      rw [Multiset.map_cons, Multiset.prod_cons,
        Polynomial.roots_mul (mul_ne_zero ha hs),
        deningerRationalWittTeichmullerPolynomial_roots, ih,
        Multiset.map_cons]
      rfl

/-- Finite Teichmüller atom multisets are separated by the literal rational-function carrier. -/
theorem deningerRationalWittAtomSum_comparison_injective
    {K : Type*} [Field K] :
    Function.Injective (fun s : Multiset Kˣ =>
      deningerRationalWittReducedMonoidAlgebraToAdditive K
        (deningerRationalWittAtomSum s)) := by
  intro s t hst
  have hmul := congrArg Additive.toMul hst
  rw [deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum_toMul,
    deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum_toMul] at hmul
  have hloc :
      algebraMap (Polynomial K) (DeningerRationalWittLocalization K)
          ((s.map fun a : Kˣ =>
            deningerRationalWittTeichmullerPolynomial (a : K)).prod) =
        algebraMap (Polynomial K) (DeningerRationalWittLocalization K)
          ((t.map fun a : Kˣ =>
            deningerRationalWittTeichmullerPolynomial (a : K)).prod) := by
    have hv := congrArg (fun z : DeningerRationalWittAdditive K =>
      (((z.1 : (DeningerRationalWittLocalization K)ˣ) :
        DeningerRationalWittLocalization K))) hmul
    simpa only [deningerRationalWitt_prod_teichmuller_val] using hv
  have hpoly :
      (s.map fun a : Kˣ =>
          deningerRationalWittTeichmullerPolynomial (a : K)).prod =
        (t.map fun a : Kˣ =>
          deningerRationalWittTeichmullerPolynomial (a : K)).prod :=
    IsLocalization.injective (DeningerRationalWittLocalization K)
      (deningerRationalWittDenominators_le_nonZeroDivisors K) hloc
  have hroots := congrArg Polynomial.roots hpoly
  rw [deningerRationalWitt_prod_teichmullerPolynomial_roots,
    deningerRationalWitt_prod_teichmullerPolynomial_roots] at hroots
  exact Multiset.map_injective
    (inv_injective.comp Units.val_injective) hroots

@[simp] theorem deningerRationalWittAtomSum_add
    {K : Type*} [Field K] (s t : Multiset Kˣ) :
    deningerRationalWittAtomSum (s + t) =
      deningerRationalWittAtomSum s + deningerRationalWittAtomSum t := by
  simp [deningerRationalWittAtomSum, Multiset.map_add]

@[simp] theorem deningerRationalWittAtomSum_replicate
    {K : Type*} [Field K] (a : Kˣ) (n : ℕ) :
    deningerRationalWittAtomSum (Multiset.replicate n a) =
      MonoidAlgebra.single a (n : ℤ) := by
  induction n with
  | zero => simp [deningerRationalWittAtomSum]
  | succ n ih =>
      rw [Multiset.replicate_succ]
      rw [show a ::ₘ Multiset.replicate n a =
        {a} + Multiset.replicate n a by rfl]
      rw [deningerRationalWittAtomSum_add, ih]
      simp [deningerRationalWittAtomSum, add_comm]

theorem deningerRationalWitt_single_eq_atomSum_sub_atomSum
    {K : Type*} [Field K] (a : Kˣ) (n : ℤ) :
    MonoidAlgebra.single a n =
      deningerRationalWittAtomSum (Multiset.replicate n.toNat a) -
        deningerRationalWittAtomSum
          (Multiset.replicate (-n).toNat a) := by
  rw [deningerRationalWittAtomSum_replicate,
    deningerRationalWittAtomSum_replicate]
  rw [← MonoidAlgebra.single_sub]
  rw [Int.toNat_sub_toNat_neg]

/-- Every integral group-ring element is a difference of two finite positive atom sums. -/
theorem deningerRationalWitt_exists_atomSum_sub_atomSum
    {K : Type*} [Field K] (x : MonoidAlgebra ℤ Kˣ) :
    ∃ s t : Multiset Kˣ,
      x = deningerRationalWittAtomSum s -
        deningerRationalWittAtomSum t := by
  have hrep : ∀ f : Kˣ →₀ ℤ,
      ∃ s t : Multiset Kˣ,
        MonoidAlgebra.coeffAddEquiv.symm f =
          deningerRationalWittAtomSum s -
            deningerRationalWittAtomSum t := by
    intro f
    induction f using Finsupp.induction with
    | zero =>
        exact ⟨0, 0, by simp [deningerRationalWittAtomSum]⟩
    | @single_add a n f ha hn ih =>
        obtain ⟨s, t, hst⟩ := ih
        have hsingle :
            MonoidAlgebra.coeffAddEquiv.symm (Finsupp.single a n) =
              MonoidAlgebra.single a n := by
          apply MonoidAlgebra.ext
          change MonoidAlgebra.coeffAddEquiv
              (MonoidAlgebra.coeffAddEquiv.symm (Finsupp.single a n)) =
            (MonoidAlgebra.single a n).coeff
          rw [AddEquiv.apply_symm_apply, MonoidAlgebra.coeff_single]
        refine ⟨Multiset.replicate n.toNat a + s,
          Multiset.replicate (-n).toNat a + t, ?_⟩
        rw [map_add, hsingle, hst, deningerRationalWittAtomSum_add,
          deningerRationalWittAtomSum_add,
          deningerRationalWitt_single_eq_atomSum_sub_atomSum a n]
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  simpa using hrep x.coeff

/-- The reduced-monoid-algebra comparison is injective over every field.  No algebraic-closure
hypothesis is required: unique factorization of the linear factors is detected by their roots. -/
theorem deningerRationalWittReducedMonoidAlgebraToAdditive_injective
    (K : Type*) [Field K] :
    Function.Injective
      (deningerRationalWittReducedMonoidAlgebraToAdditive K) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hmap0 :
      deningerRationalWittReducedMonoidAlgebraToAdditive K (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨s, t, hst⟩ :=
    deningerRationalWitt_exists_atomSum_sub_atomSum (x - y)
  rw [hst, map_sub] at hmap0
  have hatoms :
      deningerRationalWittReducedMonoidAlgebraToAdditive K
          (deningerRationalWittAtomSum s) =
        deningerRationalWittReducedMonoidAlgebraToAdditive K
          (deningerRationalWittAtomSum t) :=
    sub_eq_zero.mp hmap0
  have hst' : s = t :=
    deningerRationalWittAtomSum_comparison_injective hatoms
  rw [hst'] at hst
  simpa using hst

/-- Over every algebraically closed field, Teichmüller atoms span the literal rational-Witt
additive carrier.  This is the surjective half of Deninger's reduced-monoid-algebra comparison. -/
theorem deningerRationalWittReducedMonoidAlgebraToAdditive_surjective
    (K : Type*) [Field K] [IsAlgClosed K] :
    Function.Surjective
      (deningerRationalWittReducedMonoidAlgebraToAdditive K) := by
  intro w
  obtain ⟨P, Q, hQ, hP0, hQ0, hw⟩ :=
    deningerRationalWittAdditive_exists_normalized_fraction K w
  let sP := deningerNormalizedPolynomialRootUnits P hP0
  let sQ := deningerNormalizedPolynomialRootUnits Q hQ0
  refine ⟨deningerRationalWittAtomSum sP -
      deningerRationalWittAtomSum sQ, ?_⟩
  apply Additive.toMul.injective
  rw [map_sub]
  change Additive.toMul
      (deningerRationalWittReducedMonoidAlgebraToAdditive K
        (deningerRationalWittAtomSum sP)) *
      (Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive K
          (deningerRationalWittAtomSum sQ)))⁻¹ = w
  rw [deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum_toMul,
    deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum_toMul]
  let tP : DeningerRationalWittAdditive K :=
    (sP.map fun a : Kˣ =>
      deningerRationalWittTeichmuller (a : K)).prod
  let tQ : DeningerRationalWittAdditive K :=
    (sQ.map fun a : Kˣ =>
      deningerRationalWittTeichmuller (a : K)).prod
  change tP * tQ⁻¹ = w
  apply mul_right_cancel (b := tQ)
  rw [mul_assoc, inv_mul_cancel, mul_one]
  apply Subtype.ext
  apply Units.ext
  change ((((tP.1 : (DeningerRationalWittLocalization K)ˣ) :
        DeningerRationalWittLocalization K))) =
    (w.1 : DeningerRationalWittLocalization K) *
      (((tQ.1 : (DeningerRationalWittLocalization K)ˣ) :
        DeningerRationalWittLocalization K))
  change ((((sP.map fun a : Kˣ =>
        deningerRationalWittTeichmuller (a : K)).prod).1 :
        (DeningerRationalWittLocalization K)ˣ) :
        DeningerRationalWittLocalization K) =
    (w.1 : DeningerRationalWittLocalization K) *
      ((((sQ.map fun a : Kˣ =>
        deningerRationalWittTeichmuller (a : K)).prod).1 :
        (DeningerRationalWittLocalization K)ˣ) :
        DeningerRationalWittLocalization K)
  rw [deningerRationalWitt_prod_teichmuller_val,
    deningerRationalWitt_prod_teichmuller_val,
    ← deningerPolynomial_eq_prod_normalizedRootUnits P hP0,
    ← deningerPolynomial_eq_prod_normalizedRootUnits Q hQ0, hw]
  exact (IsLocalization.mk'_spec
    (DeningerRationalWittLocalization K) P ⟨Q, hQ⟩).symm

/-- Literal additive comparison is an equivalence over every algebraically closed field. -/
noncomputable def deningerRationalWittReducedMonoidAlgebraAddEquiv
    (K : Type*) [Field K] [IsAlgClosed K] :
    MonoidAlgebra ℤ Kˣ ≃+ Additive (DeningerRationalWittAdditive K) :=
  AddEquiv.ofBijective
    (deningerRationalWittReducedMonoidAlgebraToAdditive K)
    ⟨deningerRationalWittReducedMonoidAlgebraToAdditive_injective K,
      deningerRationalWittReducedMonoidAlgebraToAdditive_surjective K⟩

/-- Closed finite-field specialization: every literal rational Witt vector over the arithmetic
closure of `𝔽_p` is represented by a finite integral sum of nonzero Teichmüller atoms. -/
theorem deningerPrimeRationalWittReducedMonoidAlgebraToAdditive_surjective
    (p : Nat.Primes) :
    Function.Surjective
      (deningerRationalWittReducedMonoidAlgebraToAdditive
        (DeningerPrimeArithmeticClosure p)) :=
  deningerRationalWittReducedMonoidAlgebraToAdditive_surjective
    (DeningerPrimeArithmeticClosure p)

/-- Closed arithmetic-closure additive comparison equivalence. -/
noncomputable def deningerPrimeRationalWittReducedMonoidAlgebraAddEquiv
    (p : Nat.Primes) :
    MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ ≃+
      Additive (DeningerRationalWittAdditive
        (DeningerPrimeArithmeticClosure p)) :=
  deningerRationalWittReducedMonoidAlgebraAddEquiv
    (DeningerPrimeArithmeticClosure p)

end

end RHTower
