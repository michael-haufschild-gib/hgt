import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittRing
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittBaseFieldDescent
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittFieldIntersection
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Canonical rational-Witt multiplication over arbitrary commutative rings

This module proves closure of normalized rational power series under canonical big-Witt
multiplication over every commutative ring, including rings with nilpotents. The polynomial
product is an explicit fixed-degree resultant. Its compatibility with big-Witt multiplication is
proved after splitting over an algebraically closed field, descended to a universal integer
polynomial ring, and then evaluated into the arbitrary target ring. Normalized-fraction
cross-products yield the literal rational-Witt subring and its canonical commutative-ring carrier.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

variable {A B K : Type*} [CommRing A] [CommRing B]

def deningerReciprocalBivariate (Q : Polynomial A) (n : ℕ) :
    Polynomial (Polynomial A) :=
  ((Q.map Polynomial.C).reflect n).scaleRoots Polynomial.X

def deningerWittTensorPolynomial (P Q : Polynomial A) (m n : ℕ) : Polynomial A :=
  (-1 : Polynomial A) ^ (m * n) *
    Polynomial.resultant (P.map Polynomial.C) (deningerReciprocalBivariate Q n) m n

def deningerLiftedAtom (a : Aˣ) : Polynomial (Polynomial A) :=
  1 - Polynomial.C (Polynomial.C (a : A)) * Polynomial.X

def deningerReciprocalAtom (b : Aˣ) : Polynomial (Polynomial A) :=
  Polynomial.X - Polynomial.C (Polynomial.C (b : A) * Polynomial.X)

@[simp] lemma deningerLiftedAtom_natDegree [Nontrivial A] (a : Aˣ) :
    (deningerLiftedAtom a).natDegree = 1 := by
  rw [deningerLiftedAtom, Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
  · simp
  · simp

@[simp] lemma deningerReciprocalAtom_natDegree [Nontrivial A] (b : Aˣ) :
    (deningerReciprocalAtom b).natDegree = 1 := by
  change (Polynomial.X - Polynomial.C (Polynomial.C (b : A) * Polynomial.X)).natDegree = 1
  exact Polynomial.natDegree_X_sub_C _

@[simp] lemma deningerRationalWittTeichmullerPolynomial_natDegree
    [Nontrivial A] (a : Aˣ) :
    (deningerRationalWittTeichmullerPolynomial (a : A)).natDegree = 1 := by
  rw [deningerRationalWittTeichmullerPolynomial,
    Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
  · simp
  · simp

lemma deninger_reflect_leadingCoeff_eq_one
    {R : Type*} [CommRing R] [Nontrivial R]
    (P : Polynomial R) (n : ℕ) (hdeg : P.natDegree ≤ n) (h0 : P.coeff 0 = 1) :
    (P.reflect n).leadingCoeff = 1 := by
  have hle : (P.reflect n).natDegree ≤ n := by
    refine (Polynomial.natDegree_reflect_le).trans ?_
    simp [hdeg]
  have hcoeff : (P.reflect n).coeff n = 1 := by
    simp [h0]
  have hdeg' : (P.reflect n).natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hcoeff])
  rw [Polynomial.leadingCoeff, hdeg', hcoeff]

@[simp] lemma deningerRationalWittAtomPolynomial_natDegree
    {K : Type*} [Field K] (s : Multiset Kˣ) :
    (deningerRationalWittAtomPolynomial s).natDegree = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp [deningerRationalWittAtomPolynomial]
  | @cons a s ih =>
      have hcons : deningerRationalWittAtomPolynomial (a ::ₘ s) =
          deningerRationalWittTeichmullerPolynomial (a : K) *
            deningerRationalWittAtomPolynomial s := by
        simp [deningerRationalWittAtomPolynomial]
      rw [hcons]
      change (deningerRationalWittTeichmullerPolynomial (a : K) *
          deningerRationalWittAtomPolynomial s).natDegree = _
      rw [Polynomial.natDegree_mul]
      · rw [deningerRationalWittTeichmullerPolynomial_natDegree, ih]
        simp [Nat.add_comm]
      · intro h
        have := congrArg (fun P : Polynomial K => P.coeff 0) h
        simp at this
      · intro h
        have := congrArg (fun P : Polynomial K => P.coeff 0) h
        rw [deningerRationalWittAtomPolynomial_coeff_zero] at this
        simp at this

lemma deninger_lift_atomPolynomial (s : Multiset Aˣ) :
    (deningerRationalWittAtomPolynomial s).map Polynomial.C =
      (s.map deningerLiftedAtom).prod := by
  simp only [deningerRationalWittAtomPolynomial, Polynomial.map_multiset_prod,
    Multiset.map_map, Function.comp_apply]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp [deningerLiftedAtom, deningerRationalWittTeichmullerPolynomial]

lemma deningerReciprocalBivariate_singleton (b : Aˣ) :
    deningerReciprocalBivariate (deningerRationalWittAtomPolynomial ({b} : Multiset Aˣ)) 1 =
      Polynomial.X - Polynomial.C (Polynomial.C (b : A) * Polynomial.X) := by
  ext (_ | _ | k) <;>
    simp [deningerReciprocalBivariate, deningerRationalWittAtomPolynomial,
      deningerRationalWittTeichmullerPolynomial]

lemma deninger_reciprocal_lifted_atom (b : Aˣ) :
    (((deningerRationalWittTeichmullerPolynomial (b : A)).map
        Polynomial.C).reflect 1).scaleRoots Polynomial.X = deningerReciprocalAtom b := by
  simpa [deningerReciprocalBivariate, deningerReciprocalAtom,
    deningerRationalWittAtomPolynomial] using deningerReciprocalBivariate_singleton b

lemma deninger_reciprocal_atomPolynomial
    {K : Type*} [Field K] (s : Multiset Kˣ) :
    deningerReciprocalBivariate (deningerRationalWittAtomPolynomial s) s.card =
      (s.map deningerReciprocalAtom).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [deningerReciprocalBivariate, deningerRationalWittAtomPolynomial]
  | @cons b s ih =>
      have hcons : deningerRationalWittAtomPolynomial (b ::ₘ s) =
          deningerRationalWittTeichmullerPolynomial (b : K) *
            deningerRationalWittAtomPolynomial s := by
        simp [deningerRationalWittAtomPolynomial]
      rw [hcons]
      simp only [Multiset.card_cons, deningerReciprocalBivariate]
      rw [Nat.add_comm s.card 1]
      have hbdeg :
          ((deningerRationalWittTeichmullerPolynomial (b : K)).map
              Polynomial.C).natDegree ≤ 1 := by
        simp
      have hsdeg :
          ((deningerRationalWittAtomPolynomial s).map Polynomial.C).natDegree ≤
            s.card := by
        simp
      rw [Polynomial.map_mul,
        Polynomial.reflect_mul _ _ (F := 1) (G := s.card)
          hbdeg hsdeg]
      rw [Polynomial.mul_scaleRoots']
      · change
          (((deningerRationalWittTeichmullerPolynomial (b : K)).map
              Polynomial.C).reflect 1).scaleRoots Polynomial.X *
            deningerReciprocalBivariate (deningerRationalWittAtomPolynomial s) s.card = _
        rw [ih, deninger_reciprocal_lifted_atom]
        simp
      · rw [deninger_reflect_leadingCoeff_eq_one _ _ hbdeg (by simp),
          deninger_reflect_leadingCoeff_eq_one _ _ hsdeg (by simp)]
        simp

lemma deninger_lift_singleton (a : Aˣ) :
    (deningerRationalWittAtomPolynomial ({a} : Multiset Aˣ)).map Polynomial.C =
      1 - Polynomial.C (Polynomial.C (a : A)) * Polynomial.X := by
  simpa [deningerLiftedAtom] using deninger_lift_atomPolynomial ({a} : Multiset Aˣ)

lemma deninger_resultant_linear (a b : Aˣ) :
    Polynomial.resultant
        (1 - Polynomial.C (Polynomial.C (a : A)) * Polynomial.X)
        (Polynomial.X - Polynomial.C (Polynomial.C (b : A) * Polynomial.X)) 1 1 =
      -(1 - Polynomial.C ((a : A) * (b : A)) * Polynomial.X) := by
  simp [Polynomial.resultant, Polynomial.sylvester, Matrix.det_fin_two, Fin.addCases,
    Polynomial.coeff_one]
  ring

def deningerPairAtoms {K : Type*} [CommRing K]
    (s t : Multiset Kˣ) : Multiset Kˣ :=
  s.bind fun a => t.map fun b => a * b

lemma deningerReciprocalAtom_ne_zero [Nontrivial A] (b : Aˣ) :
    deningerReciprocalAtom b ≠ 0 := by
  intro h
  have := congrArg (fun P : Polynomial (Polynomial A) => P.coeff 1) h
  simp [deningerReciprocalAtom] at this

lemma deningerLiftedAtom_ne_zero [Nontrivial A] (a : Aˣ) :
    deningerLiftedAtom a ≠ 0 := by
  intro h
  have := congrArg (fun P : Polynomial (Polynomial A) => P.coeff 1) h
  simp [deningerLiftedAtom, Polynomial.coeff_one] at this

@[simp] lemma deningerReciprocalAtoms_natDegree
    {K : Type*} [Field K] (t : Multiset Kˣ) :
    ((t.map deningerReciprocalAtom).prod).natDegree = t.card := by
  induction t using Multiset.induction_on with
  | empty => simp
  | @cons b t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons,
        Polynomial.natDegree_mul (deningerReciprocalAtom_ne_zero b)]
      · simp [ih, Nat.add_comm]
      · simp [deningerReciprocalAtom_ne_zero]

@[simp] lemma deningerLiftedAtoms_natDegree
    {K : Type*} [Field K] (s : Multiset Kˣ) :
    ((s.map deningerLiftedAtom).prod).natDegree = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons,
        Polynomial.natDegree_mul (deningerLiftedAtom_ne_zero a)]
      · simp [ih, Nat.add_comm]
      · simp [deningerLiftedAtom_ne_zero]

lemma deningerRationalWittAtomPolynomial_add
    {K : Type*} [CommRing K] (s t : Multiset Kˣ) :
    deningerRationalWittAtomPolynomial (s + t) =
      deningerRationalWittAtomPolynomial s * deningerRationalWittAtomPolynomial t := by
  simp [deningerRationalWittAtomPolynomial]

lemma deninger_resultant_liftedAtom_reciprocalAtoms
    {K : Type*} [Field K] (a : Kˣ) (t : Multiset Kˣ) :
    Polynomial.resultant (deningerLiftedAtom a) ((t.map deningerReciprocalAtom).prod)
        1 t.card =
      (-1 : Polynomial K) ^ t.card *
        deningerRationalWittAtomPolynomial (t.map fun b => a * b) := by
  induction t using Multiset.induction_on with
  | empty => simp [deningerRationalWittAtomPolynomial]
  | @cons b t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      simp only [Multiset.card_cons, Multiset.map_cons]
      rw [show t.card + 1 = 1 + t.card by omega]
      conv_lhs =>
        rw [← deningerReciprocalAtom_natDegree b, ← deningerReciprocalAtoms_natDegree t]
      rw [Polynomial.resultant_mul_right]
      · rw [deningerReciprocalAtom_natDegree, deningerReciprocalAtoms_natDegree]
        have hlin : Polynomial.resultant (deningerLiftedAtom a) (deningerReciprocalAtom b) 1 1 =
            -(1 - Polynomial.C ((a : K) * (b : K)) * Polynomial.X) := by
          simpa [deningerLiftedAtom, deningerReciprocalAtom] using deninger_resultant_linear a b
        rw [hlin, ih]
        simp only [deningerRationalWittAtomPolynomial, Multiset.prod_cons,
          Multiset.map_cons]
        simp only [deningerRationalWittTeichmullerPolynomial]
        simp only [map_mul, Units.val_mul]
        ring
      · simp

lemma deninger_resultant_liftedAtoms_reciprocalAtoms
    {K : Type*} [Field K] (s t : Multiset Kˣ) :
    Polynomial.resultant ((s.map deningerLiftedAtom).prod)
        ((t.map deningerReciprocalAtom).prod) s.card t.card =
      (-1 : Polynomial K) ^ (s.card * t.card) *
        deningerRationalWittAtomPolynomial (deningerPairAtoms s t) := by
  induction s using Multiset.induction_on with
  | empty => simp [deningerPairAtoms, deningerRationalWittAtomPolynomial]
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      simp only [Multiset.card_cons]
      rw [show s.card + 1 = 1 + s.card by omega]
      conv_lhs =>
        rw [← deningerLiftedAtom_natDegree a, ← deningerLiftedAtoms_natDegree s]
      rw [Polynomial.resultant_mul_left]
      · rw [deningerLiftedAtom_natDegree, deningerLiftedAtoms_natDegree,
          deninger_resultant_liftedAtom_reciprocalAtoms, ih]
        rw [show deningerPairAtoms (a ::ₘ s) t =
            (t.map fun b => a * b) + deningerPairAtoms s t by
          simp [deningerPairAtoms]]
        rw [deningerRationalWittAtomPolynomial_add]
        ring
      · simp

theorem deningerWittTensorPolynomial_atoms
    {K : Type*} [Field K] (s t : Multiset Kˣ) :
    deningerWittTensorPolynomial
        (deningerRationalWittAtomPolynomial s)
        (deningerRationalWittAtomPolynomial t) s.card t.card =
      deningerRationalWittAtomPolynomial (deningerPairAtoms s t) := by
  rw [deningerWittTensorPolynomial, deninger_lift_atomPolynomial,
    deninger_reciprocal_atomPolynomial,
    deninger_resultant_liftedAtoms_reciprocalAtoms]
  rw [← mul_assoc, ← pow_add]
  simp [← two_mul, pow_mul]

noncomputable def deningerNormalizedPolynomialBigWitt
    (P : Polynomial A) (hP : P.coeff 0 = 1) : DeningerBigWittRing A :=
  ⟨Additive.ofMul (deningerRationalWittToBigWittAdditive A
    (deningerRationalWittNormalizedPolynomial P hP))⟩

noncomputable def deningerRationalWittToBigWittAddHom :
    Additive (DeningerRationalWittAdditive A) →+ DeningerBigWittRing A where
  toFun w := ⟨Additive.ofMul (deningerRationalWittToBigWittAdditive A
    (Additive.toMul w))⟩
  map_zero' := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerRationalWittToBigWittAdditive A 1) =
      Additive.ofMul 1
    rw [map_one]
  map_add' x y := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerRationalWittToBigWittAdditive A
        (Additive.toMul x * Additive.toMul y)) =
      Additive.ofMul (deningerRationalWittToBigWittAdditive A (Additive.toMul x) *
        deningerRationalWittToBigWittAdditive A (Additive.toMul y))
    rw [map_mul]

lemma deningerRationalTeichmuller_to_bigWitt (a : A) :
    (⟨Additive.ofMul (deningerRationalWittToBigWittAdditive A
        (deningerRationalWittTeichmuller a))⟩ : DeningerBigWittRing A) =
      deningerBigWittRingTeichmuller a := by
  apply DeningerBigWittRing.ext
  change Additive.ofMul (deningerRationalWittToBigWittAdditive A
      (deningerRationalWittTeichmuller a)) =
    Additive.ofMul (deningerBigWittTeichCarrier a)
  congr 1
  apply Subtype.ext
  apply Units.ext
  change deningerRationalWittLocalizationToPowerSeries A
      ((deningerRationalWittTeichmuller a).1 : DeningerRationalWittLocalization A) =
    deningerBigWittSeries (deningerBigWittTeichCarrier a)
  rw [deningerBigWittSeries_teichCarrier]
  change deningerRationalWittLocalizationToPowerSeries A
      (deningerRationalWittTeichmullerUnit a : DeningerRationalWittLocalization A) =
    deningerBigWittFactor a 1
  rw [deningerRationalWittTeichmullerUnit_val]
  rw [deningerRationalWittLocalizationToPowerSeries, IsLocalization.lift_eq]
  apply PowerSeries.ext
  intro n
  simp [deningerRationalWittTeichmullerPolynomial, deningerBigWittFactor]

lemma deningerNormalizedAtomPolynomialBigWitt
    {K : Type*} [Field K] (s : Multiset Kˣ) :
    deningerNormalizedPolynomialBigWitt
        (deningerRationalWittAtomPolynomial s)
        (deningerRationalWittAtomPolynomial_coeff_zero s) =
      (s.map fun a : Kˣ => deningerBigWittRingTeichmuller (a : K)).sum := by
  rw [deningerNormalizedPolynomialBigWitt,
    deningerRationalWittNormalizedPolynomial_atomPolynomial]
  change deningerRationalWittToBigWittAddHom
      (Additive.ofMul ((s.map fun a : Kˣ =>
        deningerRationalWittTeichmuller (A := K) (a : K)).prod)) = _
  induction s using Multiset.induction_on with
  | empty => exact map_zero deningerRationalWittToBigWittAddHom
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
      have hadd : Additive.ofMul
          (deningerRationalWittTeichmuller (A := K) (a : K) *
            (s.map fun b : Kˣ => deningerRationalWittTeichmuller (A := K) (b : K)).prod) =
          Additive.ofMul (deningerRationalWittTeichmuller (A := K) (a : K)) +
            Additive.ofMul ((s.map fun b : Kˣ =>
              deningerRationalWittTeichmuller (A := K) (b : K)).prod) := rfl
      calc
        deningerRationalWittToBigWittAddHom (Additive.ofMul
            (deningerRationalWittTeichmuller (a : K) *
              (s.map fun b : Kˣ => deningerRationalWittTeichmuller (A := K) (b : K)).prod)) =
            deningerRationalWittToBigWittAddHom
              (Additive.ofMul (deningerRationalWittTeichmuller (a : K)) +
                Additive.ofMul ((s.map fun b : Kˣ =>
                  deningerRationalWittTeichmuller (A := K) (b : K)).prod)) :=
              congrArg deningerRationalWittToBigWittAddHom hadd
        _ = deningerBigWittRingTeichmuller (a : K) +
            (s.map fun b : Kˣ => deningerBigWittRingTeichmuller (b : K)).sum := by
              rw [map_add, ih]
              exact congrArg (· + (s.map fun b : Kˣ =>
                deningerBigWittRingTeichmuller (b : K)).sum)
                (deningerRationalTeichmuller_to_bigWitt (A := K) (a : K))

lemma deningerBigWittTeichmuller_mul_sum
    {K : Type*} [CommRing K] (a : Kˣ) (t : Multiset Kˣ) :
    deningerBigWittRingTeichmuller (a : K) *
        (t.map fun b : Kˣ => deningerBigWittRingTeichmuller (b : K)).sum =
      (t.map fun b : Kˣ => deningerBigWittRingTeichmuller ((a * b : Kˣ) : K)).sum := by
  induction t using Multiset.induction_on with
  | empty => simp
  | @cons b t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [mul_add, deningerBigWittRingTeichmuller_mul, ih]
      simp

lemma deningerBigWittTeichmuller_sum_mul_sum
    {K : Type*} [CommRing K] (s t : Multiset Kˣ) :
    (s.map fun a : Kˣ => deningerBigWittRingTeichmuller (a : K)).sum *
        (t.map fun b : Kˣ => deningerBigWittRingTeichmuller (b : K)).sum =
      ((deningerPairAtoms s t).map fun c : Kˣ =>
        deningerBigWittRingTeichmuller (c : K)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [deningerPairAtoms]
  | @cons a s ih =>
      have hp : deningerPairAtoms (a ::ₘ s) t =
          (t.map fun b : Kˣ => a * b) + deningerPairAtoms s t := by
        simp [deningerPairAtoms]
      rw [hp, Multiset.map_add, Multiset.sum_add]
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [add_mul, deningerBigWittTeichmuller_mul_sum, ih]
      simp [Multiset.map_map]

lemma deningerNormalizedPolynomialBigWitt_congr
    {P Q : Polynomial A} (hPQ : P = Q)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerNormalizedPolynomialBigWitt P hP =
      deningerNormalizedPolynomialBigWitt Q hQ := by
  subst Q
  rfl

lemma deningerWittTensorPolynomial_coeff_zero
    {K : Type*} [Field K] [IsAlgClosed K]
    (P Q : Polynomial K) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    (deningerWittTensorPolynomial P Q P.natDegree Q.natDegree).coeff 0 = 1 := by
  let s := deningerNormalizedPolynomialRootUnits P hP
  let t := deningerNormalizedPolynomialRootUnits Q hQ
  have hPs : P = deningerRationalWittAtomPolynomial s := by
    simpa only [s, deningerRationalWittAtomPolynomial] using
      deningerPolynomial_eq_prod_normalizedRootUnits P hP
  have hQt : Q = deningerRationalWittAtomPolynomial t := by
    simpa only [t, deningerRationalWittAtomPolynomial] using
      deningerPolynomial_eq_prod_normalizedRootUnits Q hQ
  rw [hPs, hQt, deningerRationalWittAtomPolynomial_natDegree,
    deningerRationalWittAtomPolynomial_natDegree,
    deningerWittTensorPolynomial_atoms]
  simp

theorem deningerWittTensorPolynomial_bigWitt_mul
    {K : Type*} [Field K] [IsAlgClosed K]
    (P Q : Polynomial K) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerNormalizedPolynomialBigWitt P hP * deningerNormalizedPolynomialBigWitt Q hQ =
      deningerNormalizedPolynomialBigWitt
        (deningerWittTensorPolynomial P Q P.natDegree Q.natDegree)
        (deningerWittTensorPolynomial_coeff_zero P Q hP hQ) := by
  let s := deningerNormalizedPolynomialRootUnits P hP
  let t := deningerNormalizedPolynomialRootUnits Q hQ
  have hPs : P = deningerRationalWittAtomPolynomial s := by
    simpa only [s, deningerRationalWittAtomPolynomial] using
      deningerPolynomial_eq_prod_normalizedRootUnits P hP
  have hQt : Q = deningerRationalWittAtomPolynomial t := by
    simpa only [t, deningerRationalWittAtomPolynomial] using
      deningerPolynomial_eq_prod_normalizedRootUnits Q hQ
  have hPbig := deningerNormalizedPolynomialBigWitt_congr hPs hP
    (deningerRationalWittAtomPolynomial_coeff_zero s)
  have hQbig := deningerNormalizedPolynomialBigWitt_congr hQt hQ
    (deningerRationalWittAtomPolynomial_coeff_zero t)
  have htensor : deningerWittTensorPolynomial P Q P.natDegree Q.natDegree =
      deningerRationalWittAtomPolynomial (deningerPairAtoms s t) := by
    rw [hPs, hQt, deningerRationalWittAtomPolynomial_natDegree,
      deningerRationalWittAtomPolynomial_natDegree,
      deningerWittTensorPolynomial_atoms]
  rw [hPbig, hQbig]
  have htensorBig := deningerNormalizedPolynomialBigWitt_congr htensor
    (deningerWittTensorPolynomial_coeff_zero P Q hP hQ)
    (deningerRationalWittAtomPolynomial_coeff_zero (deningerPairAtoms s t))
  rw [htensorBig]
  rw [deningerNormalizedAtomPolynomialBigWitt,
    deningerNormalizedAtomPolynomialBigWitt,
    deningerNormalizedAtomPolynomialBigWitt]
  exact deningerBigWittTeichmuller_sum_mul_sum s t

def deningerUniversalNormalizedPolynomial (i : Fin 2) (m : ℕ) :
    Polynomial (DeningerBigWittUniversalRing 2) :=
  1 + ∑ k ∈ Finset.range m,
    Polynomial.C (MvPolynomial.X (i, k)) * Polynomial.X ^ (k + 1)

@[simp] lemma deningerUniversalNormalizedPolynomial_coeff_zero (i : Fin 2) (m : ℕ) :
    (deningerUniversalNormalizedPolynomial i m).coeff 0 = 1 := by
  simp [deningerUniversalNormalizedPolynomial]

lemma deningerUniversalNormalizedPolynomial_natDegree_le (i : Fin 2) (m : ℕ) :
    (deningerUniversalNormalizedPolynomial i m).natDegree ≤ m := by
  rw [deningerUniversalNormalizedPolynomial]
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    simp only [Finset.mem_range] at hk
    refine (Polynomial.natDegree_mul_le).trans ?_
    simp
    omega

@[simp] lemma deningerUniversalNormalizedPolynomial_natDegree (i : Fin 2) (m : ℕ) :
    (deningerUniversalNormalizedPolynomial i m).natDegree = m := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (deningerUniversalNormalizedPolynomial_natDegree_le i m)
  cases m with
  | zero => simp [deningerUniversalNormalizedPolynomial]
  | succ m => simp [deningerUniversalNormalizedPolynomial, Polynomial.coeff_one]

def deningerUniversalNormalizedPolynomialEval
    (P Q : Polynomial A) : DeningerBigWittUniversalRing 2 →+* A :=
  MvPolynomial.eval₂Hom (Int.castRingHom A) (fun x =>
    if x.1 = (0 : Fin 2) then P.coeff (x.2 + 1) else Q.coeff (x.2 + 1))

lemma deningerUniversalNormalizedPolynomial_map_zero
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) :
    (deningerUniversalNormalizedPolynomial (0 : Fin 2) P.natDegree).map
        (deningerUniversalNormalizedPolynomialEval P Q) = P := by
  ext (_ | n)
  · simp [deningerUniversalNormalizedPolynomial, hP]
  · by_cases hn : n < P.natDegree
    · simp [deningerUniversalNormalizedPolynomial, deningerUniversalNormalizedPolynomialEval, hn,
        Polynomial.coeff_one]
    · have hcoeff : P.coeff (n + 1) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      simp [deningerUniversalNormalizedPolynomial, deningerUniversalNormalizedPolynomialEval, hn,
        hcoeff, Polynomial.coeff_one]

lemma deningerUniversalNormalizedPolynomial_map_one
    (P Q : Polynomial A) (hQ : Q.coeff 0 = 1) :
    (deningerUniversalNormalizedPolynomial (1 : Fin 2) Q.natDegree).map
        (deningerUniversalNormalizedPolynomialEval P Q) = Q := by
  ext (_ | n)
  · simp [deningerUniversalNormalizedPolynomial, hQ]
  · by_cases hn : n < Q.natDegree
    · simp [deningerUniversalNormalizedPolynomial, deningerUniversalNormalizedPolynomialEval, hn,
        Polynomial.coeff_one]
    · have hcoeff : Q.coeff (n + 1) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      simp [deningerUniversalNormalizedPolynomial, deningerUniversalNormalizedPolynomialEval, hn,
        hcoeff, Polynomial.coeff_one]

lemma deningerBigWittRingMap_injective
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (deningerBigWittRingMap f) := by
  intro x y hxy
  apply DeningerBigWittRing.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply PowerSeries.map_injective f hf
  exact congrArg (fun z : DeningerBigWittRing B =>
    deningerBigWittSeries (Additive.toMul z.additiveVal)) hxy

lemma deningerNormalizedPolynomialBigWitt_map
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (P : Polynomial A) (hP : P.coeff 0 = 1) :
    deningerBigWittRingMap f (deningerNormalizedPolynomialBigWitt P hP) =
      deningerNormalizedPolynomialBigWitt (P.map f) (by simp [hP]) := by
  apply DeningerBigWittRing.ext
  change Additive.ofMul (deningerBigWittMap f
      (deningerRationalWittToBigWittAdditive A
        (deningerRationalWittNormalizedPolynomial P hP))) =
    Additive.ofMul (deningerRationalWittToBigWittAdditive B
      (deningerRationalWittNormalizedPolynomial (P.map f) _))
  congr 1
  simpa only [deningerBigWittMap, deningerBigWittAdditiveMap,
    deningerRationalWittNormalizedPolynomial_map] using
      deningerRationalWittToBigWittAdditive_natural f
        (deningerRationalWittNormalizedPolynomial P hP)

lemma deningerReciprocalBivariate_map
    {A B : Type*} [CommRing A] [Nontrivial A] [CommRing B]
    (f : A →+* B) (Q : Polynomial A) (n : ℕ)
    (hQdeg : Q.natDegree ≤ n) (hQ0 : Q.coeff 0 = 1) :
    (deningerReciprocalBivariate Q n).map (Polynomial.mapRingHom f) =
      deningerReciprocalBivariate (Q.map f) n := by
  by_cases hB : Subsingleton B
  · letI : Subsingleton B := hB
    subsingleton
  haveI : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
  rw [deningerReciprocalBivariate, deningerReciprocalBivariate]
  rw [Polynomial.map_scaleRoots]
  · rw [← Polynomial.reflect_map]
    have hcomp : (Polynomial.mapRingHom f).comp Polynomial.C =
        Polynomial.C.comp f := by
      ext a
      simp
    congr 2
    · rw [Polynomial.map_map, Polynomial.map_map, hcomp]
    · simp
  · rw [deninger_reflect_leadingCoeff_eq_one _ _]
    · simp
    · rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]
      exact hQdeg
    · simp [hQ0]

lemma deningerWittTensorPolynomial_map
    {A B : Type*} [CommRing A] [Nontrivial A] [CommRing B]
    (f : A →+* B) (P Q : Polynomial A) (m n : ℕ)
    (hQdeg : Q.natDegree ≤ n) (hQ0 : Q.coeff 0 = 1) :
    (deningerWittTensorPolynomial P Q m n).map f =
      deningerWittTensorPolynomial (P.map f) (Q.map f) m n := by
  rw [deningerWittTensorPolynomial, deningerWittTensorPolynomial,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_one]
  congr 1
  change (Polynomial.mapRingHom f)
      (Polynomial.resultant (P.map Polynomial.C) (deningerReciprocalBivariate Q n) m n) = _
  rw [← Polynomial.resultant_map_map
    (P.map Polynomial.C) (deningerReciprocalBivariate Q n) m n
    (Polynomial.mapRingHom f)]
  rw [deningerReciprocalBivariate_map f Q n hQdeg hQ0]
  have hcomp : (Polynomial.mapRingHom f).comp Polynomial.C =
      Polynomial.C.comp f := by
    ext a
    simp
  congr 2
  rw [Polynomial.map_map, Polynomial.map_map, hcomp]

abbrev DeningerRationalWittUniversalRing := DeningerBigWittUniversalRing 2

abbrev DeningerRationalWittUniversalClosure :=
  AlgebraicClosure (FractionRing DeningerRationalWittUniversalRing)

noncomputable def deningerRationalWittUniversalEmbedding :
    DeningerRationalWittUniversalRing →+* DeningerRationalWittUniversalClosure :=
  (algebraMap (FractionRing DeningerRationalWittUniversalRing)
      DeningerRationalWittUniversalClosure).comp
    (algebraMap DeningerRationalWittUniversalRing
      (FractionRing DeningerRationalWittUniversalRing))

lemma deningerRationalWittUniversalEmbedding_injective :
    Function.Injective deningerRationalWittUniversalEmbedding := by
  intro x y hxy
  apply FaithfulSMul.algebraMap_injective DeningerRationalWittUniversalRing
    (FractionRing DeningerRationalWittUniversalRing)
  apply (algebraMap (FractionRing DeningerRationalWittUniversalRing)
    DeningerRationalWittUniversalClosure).injective
  exact hxy

lemma deningerWittTensorPolynomial_coeff_zero_universal
    (P Q : Polynomial DeningerRationalWittUniversalRing)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    (deningerWittTensorPolynomial P Q P.natDegree Q.natDegree).coeff 0 = 1 := by
  apply deningerRationalWittUniversalEmbedding_injective
  have hmap := deningerWittTensorPolynomial_map deningerRationalWittUniversalEmbedding
    P Q P.natDegree Q.natDegree
    le_rfl hQ
  have hPι : (P.map deningerRationalWittUniversalEmbedding).coeff 0 = 1 := by simp [hP]
  have hQι : (Q.map deningerRationalWittUniversalEmbedding).coeff 0 = 1 := by simp [hQ]
  have hdegP : (P.map deningerRationalWittUniversalEmbedding).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      deningerRationalWittUniversalEmbedding_injective P
  have hdegQ : (Q.map deningerRationalWittUniversalEmbedding).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      deningerRationalWittUniversalEmbedding_injective Q
  have hfield := deningerWittTensorPolynomial_coeff_zero
    (P.map deningerRationalWittUniversalEmbedding)
    (Q.map deningerRationalWittUniversalEmbedding) hPι hQι
  rw [hdegP, hdegQ] at hfield
  have hc := congrArg (fun R : Polynomial DeningerRationalWittUniversalClosure => R.coeff 0) hmap
  simpa [hfield] using hc

theorem deningerWittTensorPolynomial_bigWitt_mul_universal
    (P Q : Polynomial DeningerRationalWittUniversalRing)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerNormalizedPolynomialBigWitt P hP * deningerNormalizedPolynomialBigWitt Q hQ =
      deningerNormalizedPolynomialBigWitt
        (deningerWittTensorPolynomial P Q P.natDegree Q.natDegree)
        (deningerWittTensorPolynomial_coeff_zero_universal P Q hP hQ) := by
  apply deningerBigWittRingMap_injective deningerRationalWittUniversalEmbedding
    deningerRationalWittUniversalEmbedding_injective
  rw [map_mul, deningerNormalizedPolynomialBigWitt_map,
    deningerNormalizedPolynomialBigWitt_map,
    deningerNormalizedPolynomialBigWitt_map]
  have hPι : (P.map deningerRationalWittUniversalEmbedding).coeff 0 = 1 := by simp [hP]
  have hQι : (Q.map deningerRationalWittUniversalEmbedding).coeff 0 = 1 := by simp [hQ]
  have hdegP : (P.map deningerRationalWittUniversalEmbedding).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      deningerRationalWittUniversalEmbedding_injective P
  have hdegQ : (Q.map deningerRationalWittUniversalEmbedding).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      deningerRationalWittUniversalEmbedding_injective Q
  have hfield := deningerWittTensorPolynomial_bigWitt_mul
    (P.map deningerRationalWittUniversalEmbedding)
    (Q.map deningerRationalWittUniversalEmbedding) hPι hQι
  have hfixed0 :
      (deningerWittTensorPolynomial (P.map deningerRationalWittUniversalEmbedding)
        (Q.map deningerRationalWittUniversalEmbedding) P.natDegree Q.natDegree).coeff 0 = 1 := by
    simpa only [hdegP, hdegQ] using
      deningerWittTensorPolynomial_coeff_zero
        (P.map deningerRationalWittUniversalEmbedding)
        (Q.map deningerRationalWittUniversalEmbedding) hPι hQι
  have hpoly :
      deningerWittTensorPolynomial (P.map deningerRationalWittUniversalEmbedding)
          (Q.map deningerRationalWittUniversalEmbedding)
          (P.map deningerRationalWittUniversalEmbedding).natDegree
          (Q.map deningerRationalWittUniversalEmbedding).natDegree =
        deningerWittTensorPolynomial (P.map deningerRationalWittUniversalEmbedding)
          (Q.map deningerRationalWittUniversalEmbedding) P.natDegree Q.natDegree := by
    rw [hdegP, hdegQ]
  have hfield' :
      deningerNormalizedPolynomialBigWitt (P.map deningerRationalWittUniversalEmbedding) hPι *
          deningerNormalizedPolynomialBigWitt (Q.map deningerRationalWittUniversalEmbedding) hQι =
        deningerNormalizedPolynomialBigWitt
          (deningerWittTensorPolynomial (P.map deningerRationalWittUniversalEmbedding)
            (Q.map deningerRationalWittUniversalEmbedding) P.natDegree Q.natDegree)
          hfixed0 := by
    exact hfield.trans (deningerNormalizedPolynomialBigWitt_congr hpoly _ hfixed0)
  have hmap := deningerWittTensorPolynomial_map deningerRationalWittUniversalEmbedding
    P Q P.natDegree Q.natDegree
    le_rfl hQ
  have hout := deningerNormalizedPolynomialBigWitt_congr hmap
    (by simp [deningerWittTensorPolynomial_coeff_zero_universal P Q hP hQ])
    hfixed0
  rw [hout]
  exact hfield'

theorem deningerWittTensorPolynomial_coeff_zero_arbitrary
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    (deningerWittTensorPolynomial P Q P.natDegree Q.natDegree).coeff 0 = 1 := by
  let PU := deningerUniversalNormalizedPolynomial (0 : Fin 2) P.natDegree
  let QU := deningerUniversalNormalizedPolynomial (1 : Fin 2) Q.natDegree
  let ev := deningerUniversalNormalizedPolynomialEval P Q
  have hPU0 : PU.coeff 0 = 1 := by simp [PU]
  have hQU0 : QU.coeff 0 = 1 := by simp [QU]
  have hQUdeg : QU.natDegree ≤ Q.natDegree := by
    change (deningerUniversalNormalizedPolynomial (1 : Fin 2) Q.natDegree).natDegree ≤
      Q.natDegree
    exact deningerUniversalNormalizedPolynomial_natDegree_le (1 : Fin 2) Q.natDegree
  have hmap := deningerWittTensorPolynomial_map ev PU QU P.natDegree Q.natDegree
    hQUdeg hQU0
  have hPUmap : PU.map ev = P := by
    simpa [PU, ev] using deningerUniversalNormalizedPolynomial_map_zero P Q hP
  have hQUmap : QU.map ev = Q := by
    simpa [QU, ev] using deningerUniversalNormalizedPolynomial_map_one P Q hQ
  rw [hPUmap, hQUmap] at hmap
  have hPUdeg : PU.natDegree = P.natDegree := by simp [PU]
  have hQUdeg' : QU.natDegree = Q.natDegree := by simp [QU]
  have hU0actual := deningerWittTensorPolynomial_coeff_zero_universal PU QU hPU0 hQU0
  have hU0 :
      (deningerWittTensorPolynomial PU QU P.natDegree Q.natDegree).coeff 0 = 1 := by
    simpa only [hPUdeg, hQUdeg'] using hU0actual
  have hc := congrArg (fun R : Polynomial A => R.coeff 0) hmap
  calc
    (deningerWittTensorPolynomial P Q P.natDegree Q.natDegree).coeff 0 =
        (Polynomial.map ev
          (deningerWittTensorPolynomial PU QU P.natDegree Q.natDegree)).coeff 0 := hc.symm
    _ = ev ((deningerWittTensorPolynomial PU QU P.natDegree Q.natDegree).coeff 0) := by simp
    _ = ev 1 := congrArg ev hU0
    _ = 1 := map_one ev

theorem deningerWittTensorPolynomial_bigWitt_mul_arbitrary
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerNormalizedPolynomialBigWitt P hP * deningerNormalizedPolynomialBigWitt Q hQ =
      deningerNormalizedPolynomialBigWitt
        (deningerWittTensorPolynomial P Q P.natDegree Q.natDegree)
        (deningerWittTensorPolynomial_coeff_zero_arbitrary P Q hP hQ) := by
  let PU := deningerUniversalNormalizedPolynomial (0 : Fin 2) P.natDegree
  let QU := deningerUniversalNormalizedPolynomial (1 : Fin 2) Q.natDegree
  let ev := deningerUniversalNormalizedPolynomialEval P Q
  have hPU0 : PU.coeff 0 = 1 := by simp [PU]
  have hQU0 : QU.coeff 0 = 1 := by simp [QU]
  have hQUdeg : QU.natDegree ≤ Q.natDegree := by
    change (deningerUniversalNormalizedPolynomial (1 : Fin 2) Q.natDegree).natDegree ≤
      Q.natDegree
    exact deningerUniversalNormalizedPolynomial_natDegree_le (1 : Fin 2) Q.natDegree
  have hPUmap : PU.map ev = P := by
    simpa [PU, ev] using deningerUniversalNormalizedPolynomial_map_zero P Q hP
  have hQUmap : QU.map ev = Q := by
    simpa [QU, ev] using deningerUniversalNormalizedPolynomial_map_one P Q hQ
  have hmap := deningerWittTensorPolynomial_map ev PU QU P.natDegree Q.natDegree
    hQUdeg hQU0
  rw [hPUmap, hQUmap] at hmap
  have hPUdeg : PU.natDegree = P.natDegree := by simp [PU]
  have hQUdeg' : QU.natDegree = Q.natDegree := by simp [QU]
  have hUactual := deningerWittTensorPolynomial_bigWitt_mul_universal PU QU hPU0 hQU0
  have hU0 :
      (deningerWittTensorPolynomial PU QU P.natDegree Q.natDegree).coeff 0 = 1 := by
    simpa only [hPUdeg, hQUdeg'] using
      deningerWittTensorPolynomial_coeff_zero_universal PU QU hPU0 hQU0
  have hpoly :
      deningerWittTensorPolynomial PU QU PU.natDegree QU.natDegree =
        deningerWittTensorPolynomial PU QU P.natDegree Q.natDegree := by
    rw [hPUdeg, hQUdeg']
  have hU :
      deningerNormalizedPolynomialBigWitt PU hPU0 *
          deningerNormalizedPolynomialBigWitt QU hQU0 =
        deningerNormalizedPolynomialBigWitt
          (deningerWittTensorPolynomial PU QU P.natDegree Q.natDegree) hU0 :=
    hUactual.trans (deningerNormalizedPolynomialBigWitt_congr hpoly _ hU0)
  have hm := congrArg (deningerBigWittRingMap ev) hU
  rw [map_mul, deningerNormalizedPolynomialBigWitt_map,
    deningerNormalizedPolynomialBigWitt_map,
    deningerNormalizedPolynomialBigWitt_map] at hm
  have hPbig := deningerNormalizedPolynomialBigWitt_congr hPUmap (by simp [hPU0]) hP
  have hQbig := deningerNormalizedPolynomialBigWitt_congr hQUmap (by simp [hQU0]) hQ
  have hTbig := deningerNormalizedPolynomialBigWitt_congr hmap
    (by rw [Polynomial.coeff_map, hU0, map_one])
    (deningerWittTensorPolynomial_coeff_zero_arbitrary P Q hP hQ)
  rw [hPbig, hQbig, hTbig] at hm
  exact hm

lemma deningerRationalWittNormalizedPolynomial_mul
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerRationalWittNormalizedPolynomial (P * Q) (by simp [hP, hQ]) =
      deningerRationalWittNormalizedPolynomial P hP *
        deningerRationalWittNormalizedPolynomial Q hQ := by
  apply Subtype.ext
  apply Units.ext
  change (deningerRationalWittNormalizedPolynomialUnit (P * Q) _ :
      DeningerRationalWittLocalization A) =
    (deningerRationalWittNormalizedPolynomialUnit P hP :
      DeningerRationalWittLocalization A) *
      (deningerRationalWittNormalizedPolynomialUnit Q hQ :
        DeningerRationalWittLocalization A)
  rw [deningerRationalWittNormalizedPolynomialUnit_val,
    deningerRationalWittNormalizedPolynomialUnit_val,
    deningerRationalWittNormalizedPolynomialUnit_val, map_mul]

def deningerRationalBigWittElement
    (w : DeningerRationalWittAdditive A) : DeningerBigWittRing A :=
  deningerRationalWittToBigWittAddHom (Additive.ofMul w)

lemma deningerRationalBigWittElement_normalizedPolynomial
    (P : Polynomial A) (hP : P.coeff 0 = 1) :
    deningerRationalBigWittElement (deningerRationalWittNormalizedPolynomial P hP) =
      deningerNormalizedPolynomialBigWitt P hP := rfl

lemma deningerNormalizedPolynomialBigWitt_add
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerNormalizedPolynomialBigWitt (P * Q) (by simp [hP, hQ]) =
      deningerNormalizedPolynomialBigWitt P hP +
        deningerNormalizedPolynomialBigWitt Q hQ := by
  change deningerRationalWittToBigWittAddHom (Additive.ofMul
      (deningerRationalWittNormalizedPolynomial (P * Q) _)) = _
  rw [deningerRationalWittNormalizedPolynomial_mul P Q hP hQ]
  exact map_add deningerRationalWittToBigWittAddHom _ _

lemma deningerRationalBigWittElement_normalizedFraction
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerRationalBigWittElement
        (deningerRationalWittNormalizedFraction P Q hP hQ) =
      deningerNormalizedPolynomialBigWitt P hP -
        deningerNormalizedPolynomialBigWitt Q hQ := by
  change deningerRationalWittToBigWittAddHom (Additive.ofMul
      (deningerRationalWittNormalizedPolynomial P hP *
        (deningerRationalWittNormalizedPolynomial Q hQ)⁻¹)) = _
  change deningerRationalWittToBigWittAddHom
      (Additive.ofMul (deningerRationalWittNormalizedPolynomial P hP) -
        Additive.ofMul (deningerRationalWittNormalizedPolynomial Q hQ)) = _
  rw [map_sub]
  rfl

lemma deningerRationalWitt_eq_normalizedFraction_of_val
    (w : DeningerRationalWittAdditive A)
    (P Q : Polynomial A) (hQmem : Q ∈ deningerRationalWittDenominators A)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1)
    (hw : (w.1 : DeningerRationalWittLocalization A) =
      IsLocalization.mk' (DeningerRationalWittLocalization A) P ⟨Q, hQmem⟩) :
    w = deningerRationalWittNormalizedFraction P Q hP hQ := by
  apply Subtype.ext
  apply Units.ext
  rw [hw, deningerRationalWittNormalizedFraction_val]

theorem deningerRationalBigWittElement_mul_closed
    (w z : DeningerRationalWittAdditive A) :
    ∃ u : DeningerRationalWittAdditive A,
      deningerRationalBigWittElement u =
        deningerRationalBigWittElement w * deningerRationalBigWittElement z := by
  obtain ⟨P, Q, hQmem, hP, hQ, hw⟩ :=
    deningerRationalWittAdditive_exists_normalized_fraction A w
  obtain ⟨R, S, hSmem, hR, hS, hz⟩ :=
    deningerRationalWittAdditive_exists_normalized_fraction A z
  have hw' := deningerRationalWitt_eq_normalizedFraction_of_val
    w P Q hQmem hP hQ hw
  have hz' := deningerRationalWitt_eq_normalizedFraction_of_val
    z R S hSmem hR hS hz
  let PR := deningerWittTensorPolynomial P R P.natDegree R.natDegree
  let QS := deningerWittTensorPolynomial Q S Q.natDegree S.natDegree
  let PS := deningerWittTensorPolynomial P S P.natDegree S.natDegree
  let QR := deningerWittTensorPolynomial Q R Q.natDegree R.natDegree
  have hPR : PR.coeff 0 = 1 := by
    simpa [PR] using deningerWittTensorPolynomial_coeff_zero_arbitrary P R hP hR
  have hQS : QS.coeff 0 = 1 := by
    simpa [QS] using deningerWittTensorPolynomial_coeff_zero_arbitrary Q S hQ hS
  have hPS : PS.coeff 0 = 1 := by
    simpa [PS] using deningerWittTensorPolynomial_coeff_zero_arbitrary P S hP hS
  have hQR : QR.coeff 0 = 1 := by
    simpa [QR] using deningerWittTensorPolynomial_coeff_zero_arbitrary Q R hQ hR
  let N := PR * QS
  let D := PS * QR
  have hN : N.coeff 0 = 1 := by simp [N, hPR, hQS]
  have hD : D.coeff 0 = 1 := by simp [D, hPS, hQR]
  refine ⟨deningerRationalWittNormalizedFraction N D hN hD, ?_⟩
  rw [deningerRationalBigWittElement_normalizedFraction,
    deningerNormalizedPolynomialBigWitt_add PR QS hPR hQS,
    deningerNormalizedPolynomialBigWitt_add PS QR hPS hQR,
    hw', hz',
    deningerRationalBigWittElement_normalizedFraction,
    deningerRationalBigWittElement_normalizedFraction]
  have hPRmul := deningerWittTensorPolynomial_bigWitt_mul_arbitrary P R hP hR
  have hQSmul := deningerWittTensorPolynomial_bigWitt_mul_arbitrary Q S hQ hS
  have hPSmul := deningerWittTensorPolynomial_bigWitt_mul_arbitrary P S hP hS
  have hQRmul := deningerWittTensorPolynomial_bigWitt_mul_arbitrary Q R hQ hR
  change deningerNormalizedPolynomialBigWitt PR hPR +
        deningerNormalizedPolynomialBigWitt QS hQS -
        (deningerNormalizedPolynomialBigWitt PS hPS +
          deningerNormalizedPolynomialBigWitt QR hQR) = _
  rw [show deningerNormalizedPolynomialBigWitt PR hPR =
      deningerNormalizedPolynomialBigWitt P hP * deningerNormalizedPolynomialBigWitt R hR by
        simpa [PR] using hPRmul.symm,
    show deningerNormalizedPolynomialBigWitt QS hQS =
      deningerNormalizedPolynomialBigWitt Q hQ * deningerNormalizedPolynomialBigWitt S hS by
        simpa [QS] using hQSmul.symm,
    show deningerNormalizedPolynomialBigWitt PS hPS =
      deningerNormalizedPolynomialBigWitt P hP * deningerNormalizedPolynomialBigWitt S hS by
        simpa [PS] using hPSmul.symm,
    show deningerNormalizedPolynomialBigWitt QR hQR =
      deningerNormalizedPolynomialBigWitt Q hQ * deningerNormalizedPolynomialBigWitt R hR by
        simpa [QR] using hQRmul.symm]
  ring

theorem deningerRationalBigWittElement_injective :
    Function.Injective (deningerRationalBigWittElement (A := A)) := by
  intro w z hwz
  apply deningerRationalWittToBigWittAdditive_injective A
  have h := congrArg (fun x : DeningerBigWittRing A => x.additiveVal) hwz
  exact Additive.ofMul.injective h

noncomputable def deningerCanonicalRationalWittSubring :
    Subring (DeningerBigWittRing A) where
  carrier := Set.range (deningerRationalWittToBigWittAddHom (A := A))
  zero_mem' := by
    refine ⟨0, ?_⟩
    exact map_zero deningerRationalWittToBigWittAddHom
  add_mem' := by
    rintro x y ⟨w, rfl⟩ ⟨z, rfl⟩
    refine ⟨w + z, ?_⟩
    exact map_add deningerRationalWittToBigWittAddHom _ _
  neg_mem' := by
    rintro x ⟨w, rfl⟩
    refine ⟨-w, ?_⟩
    exact map_neg deningerRationalWittToBigWittAddHom _
  one_mem' := by
    refine ⟨Additive.ofMul (deningerRationalWittTeichmuller (1 : A)), ?_⟩
    change (⟨Additive.ofMul (deningerRationalWittToBigWittAdditive A
      (deningerRationalWittTeichmuller (1 : A)))⟩ : DeningerBigWittRing A) = 1
    rw [deningerRationalTeichmuller_to_bigWitt]
    simp
  mul_mem' := by
    rintro x y ⟨w, rfl⟩ ⟨z, rfl⟩
    obtain ⟨u, hu⟩ := deningerRationalBigWittElement_mul_closed
      (Additive.toMul w) (Additive.toMul z)
    exact ⟨Additive.ofMul u, hu⟩

@[ext] structure DeningerCanonicalRationalWittRing (A : Type*) [CommRing A] where
  additiveVal : Additive (DeningerRationalWittAdditive A)

def deningerCanonicalRationalWittWrapperEquiv :
    DeningerCanonicalRationalWittRing A ≃
      Additive (DeningerRationalWittAdditive A) where
  toFun := DeningerCanonicalRationalWittRing.additiveVal
  invFun := DeningerCanonicalRationalWittRing.mk
  left_inv w := by cases w; rfl
  right_inv _ := rfl

noncomputable def deningerCanonicalRationalWittAdditiveEquivSubring :
    Additive (DeningerRationalWittAdditive A) ≃
      deningerCanonicalRationalWittSubring (A := A) :=
  Equiv.ofInjective deningerRationalWittToBigWittAddHom (by
    intro w z hwz
    apply Additive.toMul.injective
    apply deningerRationalBigWittElement_injective
    exact hwz)

noncomputable def deningerCanonicalRationalWittCarrierEquiv :
    DeningerCanonicalRationalWittRing A ≃ deningerCanonicalRationalWittSubring (A := A) :=
  (deningerCanonicalRationalWittWrapperEquiv (A := A)).trans
    (deningerCanonicalRationalWittAdditiveEquivSubring (A := A))

noncomputable instance deningerCanonicalRationalWittRingCommRing :
    CommRing (DeningerCanonicalRationalWittRing A) :=
  (deningerCanonicalRationalWittCarrierEquiv (A := A)).commRing

noncomputable def deningerCanonicalRationalWittRingEquiv :
    DeningerCanonicalRationalWittRing A ≃+* deningerCanonicalRationalWittSubring (A := A) :=
  Equiv.ringEquiv (deningerCanonicalRationalWittCarrierEquiv (A := A))

noncomputable def deningerCanonicalRationalWittEmbedding :
    DeningerCanonicalRationalWittRing A →+* DeningerBigWittRing A :=
  (deningerCanonicalRationalWittSubring (A := A)).subtype.comp
    (deningerCanonicalRationalWittRingEquiv (A := A)).toRingHom

@[simp] theorem deningerCanonicalRationalWittEmbedding_apply
    (w : DeningerCanonicalRationalWittRing A) :
    deningerCanonicalRationalWittEmbedding w =
      deningerRationalBigWittElement (Additive.toMul w.additiveVal) := rfl

theorem deningerCanonicalRationalWittEmbedding_injective :
    Function.Injective (deningerCanonicalRationalWittEmbedding (A := A)) := by
  intro x y hxy
  apply (deningerCanonicalRationalWittRingEquiv (A := A)).injective
  apply Subtype.ext
  exact hxy

/-- Witt addition on the transferred carrier is literal multiplication of rational functions. -/
theorem deningerCanonicalRationalWittRing_additiveVal_add
    (x y : DeningerCanonicalRationalWittRing A) :
    (x + y).additiveVal = x.additiveVal + y.additiveVal := by
  apply Additive.toMul.injective
  apply deningerRationalBigWittElement_injective
  calc
    deningerRationalBigWittElement (Additive.toMul (x + y).additiveVal) =
        deningerCanonicalRationalWittEmbedding (x + y) := rfl
    _ = deningerCanonicalRationalWittEmbedding x +
        deningerCanonicalRationalWittEmbedding y :=
      map_add deningerCanonicalRationalWittEmbedding x y
    _ = deningerRationalWittToBigWittAddHom x.additiveVal +
        deningerRationalWittToBigWittAddHom y.additiveVal := rfl
    _ = deningerRationalWittToBigWittAddHom (x.additiveVal + y.additiveVal) :=
      (map_add deningerRationalWittToBigWittAddHom x.additiveVal y.additiveVal).symm
    _ = deningerRationalBigWittElement
        (Additive.toMul (x.additiveVal + y.additiveVal)) := rfl

noncomputable def deningerCanonicalRationalWittTeichmuller (a : A) :
    DeningerCanonicalRationalWittRing A :=
  ⟨Additive.ofMul (deningerRationalWittTeichmuller a)⟩

@[simp] theorem deningerCanonicalRationalWittEmbedding_teichmuller (a : A) :
    deningerCanonicalRationalWittEmbedding (deningerCanonicalRationalWittTeichmuller a) =
      deningerBigWittRingTeichmuller a := by
  exact deningerRationalTeichmuller_to_bigWitt a

@[simp] theorem deningerCanonicalRationalWittTeichmuller_mul (a b : A) :
    deningerCanonicalRationalWittTeichmuller a *
        deningerCanonicalRationalWittTeichmuller b =
      deningerCanonicalRationalWittTeichmuller (a * b) := by
  apply deningerCanonicalRationalWittEmbedding_injective
  rw [map_mul, deningerCanonicalRationalWittEmbedding_teichmuller,
    deningerCanonicalRationalWittEmbedding_teichmuller,
    deningerCanonicalRationalWittEmbedding_teichmuller,
    deningerBigWittRingTeichmuller_mul]

/-- Underlying coefficientwise map on canonical rational-Witt carriers. -/
noncomputable def deningerCanonicalRationalWittMapFun
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    DeningerCanonicalRationalWittRing A → DeningerCanonicalRationalWittRing B :=
  fun w => ⟨Additive.ofMul (deningerRationalWittAdditiveMap f
    (Additive.toMul w.additiveVal))⟩

theorem deningerCanonicalRationalWittEmbedding_mapFun
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (w : DeningerCanonicalRationalWittRing A) :
    deningerCanonicalRationalWittEmbedding
        (deningerCanonicalRationalWittMapFun f w) =
      deningerBigWittRingMap f (deningerCanonicalRationalWittEmbedding w) := by
  apply DeningerBigWittRing.ext
  change Additive.ofMul (deningerRationalWittToBigWittAdditive B
      (deningerRationalWittAdditiveMap f (Additive.toMul w.additiveVal))) =
    Additive.ofMul (deningerBigWittMap f
      (deningerRationalWittToBigWittAdditive A (Additive.toMul w.additiveVal)))
  congr 1
  simpa only [deningerBigWittMap, deningerBigWittAdditiveMap] using
    (deningerRationalWittToBigWittAdditive_natural f
      (Additive.toMul w.additiveVal)).symm

/-- Coefficientwise functoriality of canonical rational-Witt rings. -/
noncomputable def deningerCanonicalRationalWittMap
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    DeningerCanonicalRationalWittRing A →+* DeningerCanonicalRationalWittRing B where
  toFun := deningerCanonicalRationalWittMapFun f
  map_zero' := by
    apply deningerCanonicalRationalWittEmbedding_injective
    calc
      deningerCanonicalRationalWittEmbedding
          (deningerCanonicalRationalWittMapFun f 0) =
          deningerBigWittRingMap f (deningerCanonicalRationalWittEmbedding 0) :=
        deningerCanonicalRationalWittEmbedding_mapFun f 0
      _ = deningerBigWittRingMap f 0 := by rw [map_zero]
      _ = 0 := map_zero (deningerBigWittRingMap f)
      _ = deningerCanonicalRationalWittEmbedding 0 :=
        (map_zero deningerCanonicalRationalWittEmbedding).symm
  map_add' x y := by
    apply deningerCanonicalRationalWittEmbedding_injective
    calc
      deningerCanonicalRationalWittEmbedding
          (deningerCanonicalRationalWittMapFun f (x + y)) =
          deningerBigWittRingMap f (deningerCanonicalRationalWittEmbedding (x + y)) :=
        deningerCanonicalRationalWittEmbedding_mapFun f (x + y)
      _ = deningerBigWittRingMap f
          (deningerCanonicalRationalWittEmbedding x +
            deningerCanonicalRationalWittEmbedding y) := by rw [map_add]
      _ = deningerBigWittRingMap f (deningerCanonicalRationalWittEmbedding x) +
          deningerBigWittRingMap f (deningerCanonicalRationalWittEmbedding y) := by rw [map_add]
      _ = deningerCanonicalRationalWittEmbedding (deningerCanonicalRationalWittMapFun f x) +
          deningerCanonicalRationalWittEmbedding (deningerCanonicalRationalWittMapFun f y) := by
        rw [deningerCanonicalRationalWittEmbedding_mapFun,
          deningerCanonicalRationalWittEmbedding_mapFun]
      _ = deningerCanonicalRationalWittEmbedding
          (deningerCanonicalRationalWittMapFun f x +
            deningerCanonicalRationalWittMapFun f y) :=
        (map_add deningerCanonicalRationalWittEmbedding _ _).symm
  map_one' := by
    apply deningerCanonicalRationalWittEmbedding_injective
    calc
      deningerCanonicalRationalWittEmbedding
          (deningerCanonicalRationalWittMapFun f 1) =
          deningerBigWittRingMap f (deningerCanonicalRationalWittEmbedding 1) :=
        deningerCanonicalRationalWittEmbedding_mapFun f 1
      _ = deningerBigWittRingMap f 1 := by rw [map_one]
      _ = 1 := map_one (deningerBigWittRingMap f)
      _ = deningerCanonicalRationalWittEmbedding 1 :=
        (map_one deningerCanonicalRationalWittEmbedding).symm
  map_mul' x y := by
    apply deningerCanonicalRationalWittEmbedding_injective
    calc
      deningerCanonicalRationalWittEmbedding
          (deningerCanonicalRationalWittMapFun f (x * y)) =
          deningerBigWittRingMap f (deningerCanonicalRationalWittEmbedding (x * y)) :=
        deningerCanonicalRationalWittEmbedding_mapFun f (x * y)
      _ = deningerBigWittRingMap f
          (deningerCanonicalRationalWittEmbedding x *
            deningerCanonicalRationalWittEmbedding y) := by rw [map_mul]
      _ = deningerBigWittRingMap f (deningerCanonicalRationalWittEmbedding x) *
          deningerBigWittRingMap f (deningerCanonicalRationalWittEmbedding y) := by rw [map_mul]
      _ = deningerCanonicalRationalWittEmbedding (deningerCanonicalRationalWittMapFun f x) *
          deningerCanonicalRationalWittEmbedding (deningerCanonicalRationalWittMapFun f y) := by
        rw [deningerCanonicalRationalWittEmbedding_mapFun,
          deningerCanonicalRationalWittEmbedding_mapFun]
      _ = deningerCanonicalRationalWittEmbedding
          (deningerCanonicalRationalWittMapFun f x *
            deningerCanonicalRationalWittMapFun f y) :=
        (map_mul deningerCanonicalRationalWittEmbedding _ _).symm

@[simp] theorem deningerCanonicalRationalWittMap_teichmuller
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    deningerCanonicalRationalWittMap f (deningerCanonicalRationalWittTeichmuller a) =
      deningerCanonicalRationalWittTeichmuller (f a) := by
  apply DeningerCanonicalRationalWittRing.ext
  change Additive.ofMul (deningerRationalWittAdditiveMap f
      (deningerRationalWittTeichmuller a)) =
    Additive.ofMul (deningerRationalWittTeichmuller (f a))
  rw [deningerRationalWittAdditiveMap_teichmuller]

theorem deningerWittTensorPolynomial_singletons (a b : Aˣ) :
    deningerWittTensorPolynomial
        (deningerRationalWittAtomPolynomial ({a} : Multiset Aˣ))
        (deningerRationalWittAtomPolynomial ({b} : Multiset Aˣ)) 1 1 =
      deningerRationalWittAtomPolynomial ({a * b} : Multiset Aˣ) := by
  rw [deningerWittTensorPolynomial, deninger_lift_singleton,
    deningerReciprocalBivariate_singleton, deninger_resultant_linear]
  simp [deningerRationalWittAtomPolynomial,
    deningerRationalWittTeichmullerPolynomial]

end
end RHTower
