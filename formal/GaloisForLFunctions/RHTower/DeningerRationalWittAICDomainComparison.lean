import GaloisForLFunctions.RHTower.DeningerRationalWittBaseFieldDescent
import GaloisForLFunctions.RHTower.DeningerRationalWittAlgebraicallyClosedPresentation
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Rational Witt vectors over algebraically integrally closed domains

This module proves the domain comparison cited by Deninger as Proposition 1.1(a).  Let `A` be
an integrally closed domain whose fraction field is algebraically closed.  The comparison from the
reduced monoid algebra `ℤ[A⁰]` to the literal rational-Witt carrier is an additive equivalence,
and it induces the rational-Witt ring structure with multiplicative Teichmüller map.

The hard descent step is explicit.  If a polynomial over `A` has constant coefficient one, then
the inverse of every root in the fraction field is integral over `A`: it is a root of the monic
reverse polynomial.  Integral closedness puts these inverse roots back in `A`, while algebraic
closedness factors the polynomial.  This proves surjectivity on the actual localized-polynomial
carrier rather than replacing it by a presentation alias.
-/

namespace RHTower

noncomputable section

open scoped nonZeroDivisors

noncomputable def deningerRationalWittFractionUnitMap
    (A : Type*) [CommRing A] [IsDomain A] :
    A⁰ →* (FractionRing A)ˣ where
  toFun a := Units.mk0 (algebraMap A (FractionRing A) a.1)
    ((map_ne_zero_iff (algebraMap A (FractionRing A))
      (IsFractionRing.injective A (FractionRing A))).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp a.2))
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

theorem deningerRationalWittFractionUnitMap_injective
    (A : Type*) [CommRing A] [IsDomain A] :
    Function.Injective (deningerRationalWittFractionUnitMap A) := by
  intro a b hab
  apply Subtype.ext
  apply IsFractionRing.injective A (FractionRing A)
  exact congrArg Units.val hab

noncomputable def deningerAICRationalWittComparison
    (A : Type*) [CommRing A] [IsDomain A] :
    MonoidAlgebra ℤ A⁰ →+ Additive (DeningerRationalWittAdditive A) :=
  (Finsupp.liftAddHom (α := A⁰) (M := ℤ)
    (N := Additive (DeningerRationalWittAdditive A))
    (fun a => zmultiplesHom (Additive (DeningerRationalWittAdditive A))
      (Additive.ofMul
        (deningerRationalWittTeichmuller (A := A) (a : A))))).comp
    MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

@[simp] theorem deningerAICRationalWittComparison_single
    {A : Type*} [CommRing A] [IsDomain A] (a : A⁰) (n : ℤ) :
    deningerAICRationalWittComparison A (MonoidAlgebra.single a n) =
      n • Additive.ofMul
        (deningerRationalWittTeichmuller (A := A) (a : A)) := by
  simp [deningerAICRationalWittComparison]

theorem deningerAICRationalWittComparison_natural_fraction
    (A : Type*) [CommRing A] [IsDomain A]
    (x : MonoidAlgebra ℤ A⁰) :
    deningerRationalWittReducedMonoidAlgebraToAdditive (FractionRing A)
        (MonoidAlgebra.mapDomainRingHom ℤ (deningerRationalWittFractionUnitMap A) x) =
      Additive.ofMul
        (deningerRationalWittAdditiveMap
          (algebraMap A (FractionRing A))
          (Additive.toMul (deningerAICRationalWittComparison A x))) := by
  induction x using MonoidAlgebra.induction with
  | zero => simp
  | single_add a n x _ha _hn ih =>
      rw [map_add, map_add, map_add, ih]
      simp [deningerAICRationalWittComparison_single,
        deningerRationalWittReducedMonoidAlgebraToAdditive_single,
        deningerRationalWittAdditiveMap_teichmuller,
        deningerRationalWittFractionUnitMap]

theorem deningerAICRationalWittComparison_injective
    (A : Type*) [CommRing A] [IsDomain A] :
    Function.Injective (deningerAICRationalWittComparison A) := by
  intro x y hxy
  have hmap := congrArg
    (fun w : Additive (DeningerRationalWittAdditive A) =>
      Additive.ofMul
        (deningerRationalWittAdditiveMap
          (algebraMap A (FractionRing A)) (Additive.toMul w))) hxy
  rw [← deningerAICRationalWittComparison_natural_fraction,
    ← deningerAICRationalWittComparison_natural_fraction] at hmap
  have hdom := deningerRationalWittReducedMonoidAlgebraToAdditive_injective
    (FractionRing A) hmap
  exact MonoidAlgebra.mapDomain_injective (R := ℤ)
    (deningerRationalWittFractionUnitMap_injective A) hdom

theorem deningerAICInverseRoot_exists_base
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (P : Polynomial A) (hP : P.coeff 0 = 1)
    (r : FractionRing A)
    (hr : r ∈ (P.map (algebraMap A (FractionRing A))).roots) :
    ∃ a : A, algebraMap A (FractionRing A) a = r⁻¹ := by
  have hPm0 :
      (P.map (algebraMap A (FractionRing A))).coeff 0 = 1 := by simp [hP]
  have hPmne : P.map (algebraMap A (FractionRing A)) ≠ 0 := by
    intro hz
    have hc := congrArg
      (fun Q : Polynomial (FractionRing A) => Q.coeff 0) hz
    simp [hPm0] at hc
  have hr0 : r ≠ 0 := by
    intro hz
    subst r
    have he := (Polynomial.mem_roots hPmne).mp hr
    rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero, hPm0] at he
    exact one_ne_zero he
  have hPrevMonic : P.reverse.Monic := by
    rw [Polynomial.Monic, Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff_eq_coeff_zero]
    · exact hP
    · rw [hP]
      exact one_ne_zero
  have hrEval : Polynomial.eval₂ (algebraMap A (FractionRing A)) r
      P = 0 := by
    simpa [Polynomial.eval_map] using
      ((Polynomial.mem_roots hPmne).mp hr).eq_zero
  letI : Invertible r := invertibleOfNonzero hr0
  have hrevEval : Polynomial.eval₂ (algebraMap A (FractionRing A)) r⁻¹
      P.reverse = 0 := by
    rw [← invOf_eq_inv]
    exact (Polynomial.eval₂_reverse_eq_zero_iff
      (algebraMap A (FractionRing A)) r P).2 hrEval
  apply IsIntegrallyClosed.isIntegral_iff.mp
  exact ⟨P.reverse, hPrevMonic, hrevEval⟩

noncomputable def deningerAICRootAtomValue
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (P : Polynomial A) (hP : P.coeff 0 = 1)
    (r : {r : FractionRing A //
      r ∈ (P.map (algebraMap A (FractionRing A))).roots}) : A :=
  Classical.choose (deningerAICInverseRoot_exists_base A P hP r.1 r.2)

@[simp] theorem deningerAICRootAtomValue_map
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (P : Polynomial A) (hP : P.coeff 0 = 1)
    (r : {r : FractionRing A //
      r ∈ (P.map (algebraMap A (FractionRing A))).roots}) :
    algebraMap A (FractionRing A) (deningerAICRootAtomValue A P hP r) = r.1⁻¹ :=
  Classical.choose_spec (deningerAICInverseRoot_exists_base A P hP r.1 r.2)

noncomputable def deningerAICRootAtoms
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (P : Polynomial A) (hP : P.coeff 0 = 1) : Multiset A⁰ :=
  (P.map (algebraMap A (FractionRing A))).roots.attach.map fun r =>
    ⟨deningerAICRootAtomValue A P hP r,
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro ha
        have hm := deningerAICRootAtomValue_map A P hP r
        rw [ha, map_zero] at hm
        have hr0 : r.1 ≠ 0 := by
          intro hrz
          have hPm0 :
              (P.map (algebraMap A (FractionRing A))).coeff 0 = 1 := by
            simp [hP]
          have hPmne : P.map (algebraMap A (FractionRing A)) ≠ 0 := by
            intro hz
            have hc := congrArg
              (fun Q : Polynomial (FractionRing A) => Q.coeff 0) hz
            simp [hPm0] at hc
          have he := ((Polynomial.mem_roots hPmne).mp r.2).eq_zero
          have he0 :
              (P.map (algebraMap A (FractionRing A))).eval 0 = 0 := by
            simpa [hrz] using he
          rw [← Polynomial.coeff_zero_eq_eval_zero, hPm0] at he0
          exact one_ne_zero he0
        exact hr0 (inv_eq_zero.mp hm.symm))⟩

def deningerRationalWittNonzeroAtomPolynomial
    {A : Type*} [CommRing A] (s : Multiset A⁰) : Polynomial A :=
  (s.map fun a : A⁰ =>
    deningerRationalWittTeichmullerPolynomial (a : A)).prod

theorem deningerRationalWittNonzeroAtomPolynomial_map_fraction
    (A : Type*) [CommRing A] [IsDomain A] (s : Multiset A⁰) :
    (deningerRationalWittNonzeroAtomPolynomial s).map
        (algebraMap A (FractionRing A)) =
      deningerRationalWittAtomPolynomial
        (s.map (deningerRationalWittFractionUnitMap A)) := by
  simp only [deningerRationalWittNonzeroAtomPolynomial, deningerRationalWittAtomPolynomial,
    Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_apply]
  congr 1
  apply Multiset.map_congr rfl
  intro a _ha
  ext n
  simp [deningerRationalWittTeichmullerPolynomial,
    deningerRationalWittFractionUnitMap]

theorem deningerAICRootAtoms_map_fraction
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (P : Polynomial A) (hP : P.coeff 0 = 1) :
    (deningerAICRootAtoms A P hP).map (deningerRationalWittFractionUnitMap A) =
      deningerNormalizedPolynomialRootUnits
        (P.map (algebraMap A (FractionRing A))) (by simp [hP]) := by
  unfold deningerAICRootAtoms deningerNormalizedPolynomialRootUnits
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro r _hr
  apply Units.ext
  exact deningerAICRootAtomValue_map A P hP r

theorem deningerAICPolynomial_eq_nonzeroAtomPolynomial
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsAlgClosed (FractionRing A)]
    (P : Polynomial A) (hP : P.coeff 0 = 1) :
    P = deningerRationalWittNonzeroAtomPolynomial (deningerAICRootAtoms A P hP) := by
  apply Polynomial.map_injective
    (algebraMap A (FractionRing A)) (IsFractionRing.injective A (FractionRing A))
  rw [deningerRationalWittNonzeroAtomPolynomial_map_fraction,
    deningerAICRootAtoms_map_fraction]
  exact deningerPolynomial_eq_prod_normalizedRootUnits
    (P.map (algebraMap A (FractionRing A))) (by simp [hP])

@[simp] theorem deningerRationalWittNonzeroAtomPolynomial_coeff_zero
    {A : Type*} [CommRing A] (s : Multiset A⁰) :
    (deningerRationalWittNonzeroAtomPolynomial s).coeff 0 = 1 := by
  change Polynomial.constantCoeff
    ((s.map fun a : A⁰ =>
      deningerRationalWittTeichmullerPolynomial (a : A)).prod) = 1
  rw [map_multiset_prod]
  simp

noncomputable def deningerRationalWittNonzeroAtomSum
    {A : Type*} [CommRing A] (s : Multiset A⁰) :
    MonoidAlgebra ℤ A⁰ :=
  (s.map fun a : A⁰ => MonoidAlgebra.single a (1 : ℤ)).sum

@[simp] theorem deningerAICRationalWittComparison_atomSum
    {A : Type*} [CommRing A] [IsDomain A] (s : Multiset A⁰) :
    deningerAICRationalWittComparison A (deningerRationalWittNonzeroAtomSum s) =
      (s.map fun a : A⁰ => Additive.ofMul
        (deningerRationalWittTeichmuller (A := A) (a : A))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [deningerRationalWittNonzeroAtomSum]
  | @cons a s ih =>
      rw [show deningerRationalWittNonzeroAtomSum (a ::ₘ s) =
        MonoidAlgebra.single a 1 + deningerRationalWittNonzeroAtomSum s by
          simp [deningerRationalWittNonzeroAtomSum]]
      rw [map_add, deningerAICRationalWittComparison_single, ih]
      simp

theorem deningerAICRationalWittComparison_atomSum_toMul
    {A : Type*} [CommRing A] [IsDomain A] (s : Multiset A⁰) :
    Additive.toMul (deningerAICRationalWittComparison A (deningerRationalWittNonzeroAtomSum s)) =
      (s.map fun a : A⁰ =>
        deningerRationalWittTeichmuller (A := A) (a : A)).prod := by
  simp [deningerAICRationalWittComparison_atomSum]

theorem deningerRationalWittNonzeroProdTeichmuller_val
    {A : Type*} [CommRing A] (s : Multiset A⁰) :
    ((((s.map fun a : A⁰ =>
        deningerRationalWittTeichmuller (A := A) (a : A)).prod).1 :
          (DeningerRationalWittLocalization A)ˣ) :
      DeningerRationalWittLocalization A) =
      algebraMap (Polynomial A) (DeningerRationalWittLocalization A)
        (deningerRationalWittNonzeroAtomPolynomial s) := by
  induction s using Multiset.induction_on with
  | empty => simp [deningerRationalWittNonzeroAtomPolynomial]
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      change (deningerRationalWittTeichmullerUnit (a : A) :
          DeningerRationalWittLocalization A) *
          ((((s.map fun b : A⁰ =>
            deningerRationalWittTeichmuller (b : A)).prod).1 :
            (DeningerRationalWittLocalization A)ˣ) :
            DeningerRationalWittLocalization A) = _
      rw [deningerRationalWittTeichmullerUnit_val, ih, ← map_mul]
      simp [deningerRationalWittNonzeroAtomPolynomial]

theorem deningerRationalWittNormalizedPolynomial_nonzeroAtomPolynomial
    {A : Type*} [CommRing A] (s : Multiset A⁰) :
    deningerRationalWittNormalizedPolynomial
        (deningerRationalWittNonzeroAtomPolynomial s)
        (deningerRationalWittNonzeroAtomPolynomial_coeff_zero s) =
      (s.map fun a : A⁰ =>
        deningerRationalWittTeichmuller (A := A) (a : A)).prod := by
  apply Subtype.ext
  apply Units.ext
  change (deningerRationalWittNormalizedPolynomialUnit
      (deningerRationalWittNonzeroAtomPolynomial s) _ :
        DeningerRationalWittLocalization A) =
    ((((s.map fun a : A⁰ =>
      deningerRationalWittTeichmuller (A := A) (a : A)).prod).1 :
        (DeningerRationalWittLocalization A)ˣ) :
      DeningerRationalWittLocalization A)
  rw [deningerRationalWittNormalizedPolynomialUnit_val,
    deningerRationalWittNonzeroProdTeichmuller_val]

theorem deningerRationalWittNormalizedFraction_val
    {A : Type*} [CommRing A]
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    (((deningerRationalWittNormalizedFraction P Q hP hQ).1 :
        (DeningerRationalWittLocalization A)ˣ) :
      DeningerRationalWittLocalization A) =
      IsLocalization.mk' (DeningerRationalWittLocalization A) P
        (⟨Q, hQ⟩ : deningerRationalWittDenominators A) := by
  change (deningerRationalWittNormalizedPolynomialUnit P hP :
      DeningerRationalWittLocalization A) *
      ((deningerRationalWittNormalizedPolynomialUnit Q hQ)⁻¹ :
        (DeningerRationalWittLocalization A)ˣ) = _
  rw [deningerRationalWittNormalizedPolynomialUnit_val]
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
  rw [show algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Q =
      (deningerRationalWittNormalizedPolynomialUnit Q hQ :
        DeningerRationalWittLocalization A) from
    (deningerRationalWittNormalizedPolynomialUnit_val Q hQ).symm]
  rw [mul_assoc, Units.inv_mul, mul_one]

theorem deningerAICRationalWittComparison_surjective
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsAlgClosed (FractionRing A)] :
    Function.Surjective (deningerAICRationalWittComparison A) := by
  intro w
  obtain ⟨P, Q, hQmem, hP, hQ, hwval⟩ :=
    deningerRationalWittAdditive_exists_normalized_fraction A w
  let s := deningerAICRootAtoms A P hP
  let t := deningerAICRootAtoms A Q hQ
  have hPs : P = deningerRationalWittNonzeroAtomPolynomial s := by
    simpa [s] using deningerAICPolynomial_eq_nonzeroAtomPolynomial A P hP
  have hQt : Q = deningerRationalWittNonzeroAtomPolynomial t := by
    simpa [t] using deningerAICPolynomial_eq_nonzeroAtomPolynomial A Q hQ
  let x : MonoidAlgebra ℤ A⁰ :=
    deningerRationalWittNonzeroAtomSum s - deningerRationalWittNonzeroAtomSum t
  refine ⟨x, ?_⟩
  have hwfrac :
      w = deningerRationalWittNormalizedFraction P Q hP hQ := by
    apply Subtype.ext
    apply Units.ext
    rw [hwval, deningerRationalWittNormalizedFraction_val]
  rw [hwfrac]
  apply Additive.toMul.injective
  change Additive.toMul (deningerAICRationalWittComparison A x) =
    deningerRationalWittNormalizedFraction P Q hP hQ
  change Additive.toMul
      (deningerAICRationalWittComparison A
        (deningerRationalWittNonzeroAtomSum s - deningerRationalWittNonzeroAtomSum t)) = _
  rw [map_sub]
  change Additive.toMul (deningerAICRationalWittComparison A (deningerRationalWittNonzeroAtomSum s)) *
      (Additive.toMul (deningerAICRationalWittComparison A (deningerRationalWittNonzeroAtomSum t)))⁻¹ =
    deningerRationalWittNormalizedPolynomial P hP *
      (deningerRationalWittNormalizedPolynomial Q hQ)⁻¹
  rw [deningerAICRationalWittComparison_atomSum_toMul,
    deningerAICRationalWittComparison_atomSum_toMul,
    deningerRationalWittNormalizedPolynomial_congr hPs,
    deningerRationalWittNormalizedPolynomial_congr hQt,
    deningerRationalWittNormalizedPolynomial_nonzeroAtomPolynomial,
    deningerRationalWittNormalizedPolynomial_nonzeroAtomPolynomial] <;> simp

noncomputable def deningerAICRationalWittComparisonEquiv
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsAlgClosed (FractionRing A)] :
    MonoidAlgebra ℤ A⁰ ≃+
      Additive (DeningerRationalWittAdditive A) :=
  AddEquiv.ofBijective (deningerAICRationalWittComparison A)
    ⟨deningerAICRationalWittComparison_injective A, deningerAICRationalWittComparison_surjective A⟩

@[ext] structure DeningerAICRationalWittRing (A : Type*) [CommRing A] where
  additiveVal : Additive (DeningerRationalWittAdditive A)

noncomputable def deningerAICRationalWittRingCarrierEquiv
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsAlgClosed (FractionRing A)] :
    DeningerAICRationalWittRing A ≃ MonoidAlgebra ℤ A⁰ where
  toFun w := (deningerAICRationalWittComparisonEquiv A).symm w.additiveVal
  invFun x := ⟨deningerAICRationalWittComparisonEquiv A x⟩
  left_inv w := by ext; simp
  right_inv x := by simp

noncomputable instance deningerAICRationalWittRingCommRing
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsAlgClosed (FractionRing A)] : CommRing (DeningerAICRationalWittRing A) :=
  (deningerAICRationalWittRingCarrierEquiv A).commRing

noncomputable def deningerAICRationalWittRingEquiv
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsAlgClosed (FractionRing A)] :
    MonoidAlgebra ℤ A⁰ ≃+* DeningerAICRationalWittRing A :=
  (Equiv.ringEquiv (deningerAICRationalWittRingCarrierEquiv A)).symm

theorem deningerAICRationalWittRingEquiv_additiveVal
    {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsAlgClosed (FractionRing A)] (x : MonoidAlgebra ℤ A⁰) :
    (deningerAICRationalWittRingEquiv A x).additiveVal = deningerAICRationalWittComparison A x := by
  rfl

noncomputable def deningerAICRationalWittTeichmuller
    {A : Type*} [CommRing A] (a : A) : DeningerAICRationalWittRing A :=
  ⟨Additive.ofMul (deningerRationalWittTeichmuller a)⟩

theorem deningerAICRationalWittTeichmuller_nonzero
    {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsAlgClosed (FractionRing A)] (a : A⁰) :
    deningerAICRationalWittTeichmuller (a : A) =
      deningerAICRationalWittRingEquiv A (MonoidAlgebra.single a 1) := by
  apply DeningerAICRationalWittRing.ext
  rw [deningerAICRationalWittRingEquiv_additiveVal, deningerAICRationalWittComparison_single]
  change Additive.ofMul (deningerRationalWittTeichmuller (a : A)) =
    1 • Additive.ofMul (deningerRationalWittTeichmuller (a : A))
  simp

@[simp] theorem deningerAICRationalWittTeichmuller_zero
    {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsAlgClosed (FractionRing A)] :
    deningerAICRationalWittTeichmuller (0 : A) = 0 := by
  calc
    deningerAICRationalWittTeichmuller (0 : A) = deningerAICRationalWittRingEquiv A 0 := by
      apply DeningerAICRationalWittRing.ext
      rw [deningerAICRationalWittRingEquiv_additiveVal]
      change Additive.ofMul (deningerRationalWittTeichmuller (0 : A)) =
        Additive.ofMul 1
      congr 1
      apply Subtype.ext
      apply Units.ext
      change (deningerRationalWittTeichmullerUnit (0 : A) :
        DeningerRationalWittLocalization A) = 1
      rw [deningerRationalWittTeichmullerUnit_val]
      simp [deningerRationalWittTeichmullerPolynomial]
    _ = 0 := map_zero (deningerAICRationalWittRingEquiv A)

theorem deningerAICRationalWittTeichmuller_mul
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsAlgClosed (FractionRing A)] (a b : A) :
    deningerAICRationalWittTeichmuller a * deningerAICRationalWittTeichmuller b =
      deningerAICRationalWittTeichmuller (a * b) := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    simp
  let ua : A⁰ := ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩
  let ub : A⁰ := ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩
  change deningerAICRationalWittTeichmuller (ua : A) * deningerAICRationalWittTeichmuller (ub : A) =
    deningerAICRationalWittTeichmuller ((ua * ub : A⁰) : A)
  rw [deningerAICRationalWittTeichmuller_nonzero, deningerAICRationalWittTeichmuller_nonzero,
    deningerAICRationalWittTeichmuller_nonzero, ← map_mul,
    MonoidAlgebra.single_mul_single, one_mul]

theorem deningerAICRationalWittRing_additiveVal_add
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsAlgClosed (FractionRing A)] (x y : DeningerAICRationalWittRing A) :
    (x + y).additiveVal = x.additiveVal + y.additiveVal := by
  apply (deningerAICRationalWittComparisonEquiv A).symm.injective
  rw [map_add]
  change deningerAICRationalWittRingCarrierEquiv A (x + y) =
    deningerAICRationalWittRingCarrierEquiv A x + deningerAICRationalWittRingCarrierEquiv A y
  exact map_add (Equiv.ringEquiv (deningerAICRationalWittRingCarrierEquiv A)) x y

end
end RHTower

