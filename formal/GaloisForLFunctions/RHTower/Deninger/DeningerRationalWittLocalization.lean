import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittCanonicalMultiplication
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Rational Witt vectors commute with localization

This module formalizes Deninger's localization theorem for rational Witt vectors over an
arbitrary commutative ring.  No reducedness, domain, or regularity assumption is imposed on the
coefficient ring or on the localization submonoid.

The hard identity is the literal Teichmüller dilation law

`[b] ⊙ f(T) = f(bT)`.

It is proved for normalized polynomials by splitting over an algebraic closure, descended through
a universal integer polynomial ring, and then extended to normalized fractions.  Finite
denominator clearing proves surjectivity after coefficient localization.  A separate finite
annihilator argument proves the kernel condition without assuming that coefficient localization
is injective; this is the step needed for rings with zero divisors and nilpotents.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

variable {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]

/-- Substitution `P(T) ↦ P(bT)`. -/
def deningerPolynomialDilation (b : A) (P : Polynomial A) : Polynomial A :=
  P.comp (Polynomial.C b * Polynomial.X)

@[simp] theorem deningerPolynomialDilation_coeff (b : A) (P : Polynomial A) (n : ℕ) :
    (deningerPolynomialDilation b P).coeff n = P.coeff n * b ^ n := by
  exact Polynomial.comp_C_mul_X_coeff

@[simp] theorem deningerPolynomialDilation_coeff_zero (b : A) (P : Polynomial A) :
    (deningerPolynomialDilation b P).coeff 0 = P.coeff 0 := by
  simp

@[simp] theorem deningerPolynomialDilation_map
    (f : A →+* B) (b : A) (P : Polynomial A) :
    (deningerPolynomialDilation b P).map f =
      deningerPolynomialDilation (f b) (P.map f) := by
  ext n
  simp [deningerPolynomialDilation]

lemma deningerWittTensorPolynomial_teichmuller_isAlgClosed
    {K : Type*} [Field K] [IsAlgClosed K]
    (b : K) (hb : b ≠ 0) (P : Polynomial K) (hP : P.coeff 0 = 1) :
    deningerWittTensorPolynomial
        (deningerRationalWittTeichmullerPolynomial b) P 1 P.natDegree =
      deningerPolynomialDilation b P := by
  let bu : Kˣ := Units.mk0 b hb
  let s := deningerNormalizedPolynomialRootUnits P hP
  have hbpoly : deningerRationalWittTeichmullerPolynomial b =
      deningerRationalWittAtomPolynomial ({bu} : Multiset Kˣ) := by
    simp [deningerRationalWittAtomPolynomial,
      deningerRationalWittTeichmullerPolynomial, bu]
  have hPs : P = deningerRationalWittAtomPolynomial s := by
    simpa only [s, deningerRationalWittAtomPolynomial] using
      deningerPolynomial_eq_prod_normalizedRootUnits P hP
  rw [hbpoly, hPs, deningerRationalWittAtomPolynomial_natDegree]
  change deningerWittTensorPolynomial
      (deningerRationalWittAtomPolynomial ({bu} : Multiset Kˣ))
      (deningerRationalWittAtomPolynomial s) ({bu} : Multiset Kˣ).card s.card = _
  rw [deningerWittTensorPolynomial_atoms]
  induction s using Multiset.induction_on with
  | empty => simp [deningerPairAtoms, deningerPolynomialDilation,
      deningerRationalWittAtomPolynomial]
  | @cons a s ih =>
      calc
        deningerRationalWittAtomPolynomial
            (deningerPairAtoms ({bu} : Multiset Kˣ) (a ::ₘ s)) =
            deningerRationalWittTeichmullerPolynomial ((bu * a : Kˣ) : K) *
              deningerRationalWittAtomPolynomial
                (deningerPairAtoms ({bu} : Multiset Kˣ) s) := by
                  simp [deningerPairAtoms, deningerRationalWittAtomPolynomial]
        _ = deningerRationalWittTeichmullerPolynomial ((bu * a : Kˣ) : K) *
              deningerPolynomialDilation b
                (deningerRationalWittAtomPolynomial s) := by rw [ih]
        _ = deningerPolynomialDilation b
              (deningerRationalWittTeichmullerPolynomial (a : K) *
                deningerRationalWittAtomPolynomial s) := by
                  simp only [deningerPolynomialDilation, Polynomial.comp,
                    Polynomial.eval₂_mul]
                  congr 1
                  ext (_ | _ | n) <;>
                    simp [deningerRationalWittTeichmullerPolynomial, bu,
                      Polynomial.coeff_one]
                  all_goals ring_nf
        _ = deningerPolynomialDilation b
              (deningerRationalWittAtomPolynomial (a ::ₘ s)) := by
                congr 1
                simp [deningerRationalWittAtomPolynomial]

/-- Universal evaluation carrying one independent Teichmüller coefficient and all positive
coefficients of one normalized polynomial to a prescribed target. -/
def deningerUniversalDilationEval (b : A) (P : Polynomial A) :
    DeningerRationalWittUniversalRing →+* A :=
  MvPolynomial.eval₂Hom (Int.castRingHom A) (fun x =>
    if x.1 = (0 : Fin 2) then b else P.coeff (x.2 + 1))

lemma deningerUniversalDilationEval_polynomial (b : A) (P : Polynomial A)
    (hP : P.coeff 0 = 1) :
    (deningerUniversalNormalizedPolynomial (1 : Fin 2) P.natDegree).map
        (deningerUniversalDilationEval b P) = P := by
  ext (_ | n)
  · simp [deningerUniversalNormalizedPolynomial, hP]
  · by_cases hn : n < P.natDegree
    · simp [deningerUniversalNormalizedPolynomial, deningerUniversalDilationEval, hn,
        Polynomial.coeff_one]
    · have hcoeff : P.coeff (n + 1) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      simp [deningerUniversalNormalizedPolynomial, deningerUniversalDilationEval, hn,
        hcoeff, Polynomial.coeff_one]

lemma deningerUniversalDilationEval_parameter (b : A) (P : Polynomial A) :
    deningerUniversalDilationEval b P
        (MvPolynomial.X ((0 : Fin 2), 0)) = b := by
  simp [deningerUniversalDilationEval]

/-- Fixed-degree resultant form of Teichmüller dilation, valid over every commutative ring. -/
theorem deningerWittTensorPolynomial_teichmuller_arbitrary
    (b : A) (P : Polynomial A) (hP : P.coeff 0 = 1) :
    deningerWittTensorPolynomial
        (deningerRationalWittTeichmullerPolynomial b) P 1 P.natDegree =
      deningerPolynomialDilation b P := by
  let bU : DeningerRationalWittUniversalRing :=
    MvPolynomial.X ((0 : Fin 2), 0)
  let PU := deningerUniversalNormalizedPolynomial (1 : Fin 2) P.natDegree
  let ι := deningerRationalWittUniversalEmbedding
  have hbU : bU ≠ 0 := by
    intro hz
    have hc := congrArg (MvPolynomial.coeff (Finsupp.single ((0 : Fin 2), 0) 1)) hz
    simp [bU] at hc
  have hιb : ι bU ≠ 0 := by
    intro hzero
    apply hbU
    apply deningerRationalWittUniversalEmbedding_injective
    simpa [ι] using hzero
  have hPU0 : PU.coeff 0 = 1 := by simp [PU]
  have hPUdeg : PU.natDegree = P.natDegree := by simp [PU]
  have hfield := deningerWittTensorPolynomial_teichmuller_isAlgClosed
    (ι bU) hιb (PU.map ι) (by simp [hPU0])
  have hbpolyMap :
      (deningerRationalWittTeichmullerPolynomial bU).map ι =
        deningerRationalWittTeichmullerPolynomial (ι bU) := by
    ext n
    simp [deningerRationalWittTeichmullerPolynomial]
  have hPUmapdeg : (PU.map ι).natDegree = PU.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      deningerRationalWittUniversalEmbedding_injective PU
  rw [hPUmapdeg, hPUdeg] at hfield
  have htensorMap := deningerWittTensorPolynomial_map ι
    (deningerRationalWittTeichmullerPolynomial bU) PU 1 P.natDegree
    (by simp [hPUdeg]) hPU0
  rw [hbpolyMap] at htensorMap
  have hdilationMap := deningerPolynomialDilation_map ι bU PU
  have hU :
      deningerWittTensorPolynomial
          (deningerRationalWittTeichmullerPolynomial bU) PU 1 P.natDegree =
        deningerPolynomialDilation bU PU := by
    apply Polynomial.map_injective ι deningerRationalWittUniversalEmbedding_injective
    rw [htensorMap, hdilationMap]
    exact hfield
  let ev := deningerUniversalDilationEval b P
  have hPUev : PU.map ev = P := by
    simpa [PU, ev] using deningerUniversalDilationEval_polynomial b P hP
  have hbev : ev bU = b := by
    simpa [bU, ev] using deningerUniversalDilationEval_parameter b P
  have hm := congrArg (Polynomial.map ev) hU
  have htensorEv := deningerWittTensorPolynomial_map ev
    (deningerRationalWittTeichmullerPolynomial bU) PU 1 P.natDegree
    (by simp [hPUdeg]) hPU0
  have hdilationEv := deningerPolynomialDilation_map ev bU PU
  have hbpolyEv :
      (deningerRationalWittTeichmullerPolynomial bU).map ev =
        deningerRationalWittTeichmullerPolynomial b := by
    ext n
    simp [deningerRationalWittTeichmullerPolynomial, hbev]
  rw [htensorEv, hdilationEv, hbpolyEv, hPUev, hbev] at hm
  exact hm

lemma deningerNormalizedTeichmullerPolynomialBigWitt (b : A) :
    deningerNormalizedPolynomialBigWitt
        (deningerRationalWittTeichmullerPolynomial b)
        (deningerRationalWittTeichmullerPolynomial_coeff_zero b) =
      deningerBigWittRingTeichmuller b := by
  rw [← deningerRationalTeichmuller_to_bigWitt b]
  apply DeningerBigWittRing.ext
  change Additive.ofMul (deningerRationalWittToBigWittAdditive A
      (deningerRationalWittNormalizedPolynomial
        (deningerRationalWittTeichmullerPolynomial b) _)) =
    Additive.ofMul (deningerRationalWittToBigWittAdditive A
      (deningerRationalWittTeichmuller b))
  congr 1

/-- Literal polynomial form of `[b] ⊙ P(T) = P(bT)` in the arbitrary-ring big-Witt ring. -/
theorem deningerBigWittTeichmuller_mul_normalizedPolynomial
    (b : A) (P : Polynomial A) (hP : P.coeff 0 = 1) :
    deningerBigWittRingTeichmuller b * deningerNormalizedPolynomialBigWitt P hP =
      deningerNormalizedPolynomialBigWitt (deningerPolynomialDilation b P)
        (by simp [hP]) := by
  by_cases hb : b = 0
  · subst b
    rw [deningerBigWittRingTeichmuller_zero, zero_mul]
    have hdilation : deningerPolynomialDilation (0 : A) P = 1 := by
      ext n
      cases n with
      | zero => simp [hP]
      | succ n =>
          rw [deningerPolynomialDilation_coeff]
          simp only [zero_pow (Nat.succ_ne_zero n), mul_zero,
            Polynomial.coeff_one, Nat.succ_ne_zero, if_false]
    rw [deningerNormalizedPolynomialBigWitt_congr hdilation]
    let x := deningerNormalizedPolynomialBigWitt (1 : Polynomial A) (by simp)
    have hadd := deningerNormalizedPolynomialBigWitt_add
      (1 : Polynomial A) (1 : Polynomial A) (by simp) (by simp)
    have hx : x = 0 := by
      apply add_left_cancel (a := x)
      simpa [x] using hadd.symm
    exact hx.symm
  ·
    have hdeg : (deningerRationalWittTeichmullerPolynomial b).natDegree = 1 := by
      rw [deningerRationalWittTeichmullerPolynomial,
        Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
      · simp [hb]
      · simp [hb]
    rw [← deningerNormalizedTeichmullerPolynomialBigWitt b,
      deningerWittTensorPolynomial_bigWitt_mul_arbitrary]
    apply deningerNormalizedPolynomialBigWitt_congr
    rw [hdeg]
    exact deningerWittTensorPolynomial_teichmuller_arbitrary b P hP

/-- A normalized polynomial regarded as an element of the canonical rational-Witt ring. -/
noncomputable def deningerCanonicalRationalWittNormalizedPolynomial
    (P : Polynomial A) (hP : P.coeff 0 = 1) :
    DeningerCanonicalRationalWittRing A :=
  ⟨Additive.ofMul (deningerRationalWittNormalizedPolynomial P hP)⟩

/-- A normalized polynomial quotient regarded as an element of the canonical rational-Witt ring. -/
noncomputable def deningerCanonicalRationalWittNormalizedFraction
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    DeningerCanonicalRationalWittRing A :=
  ⟨Additive.ofMul (deningerRationalWittNormalizedFraction P Q hP hQ)⟩

@[simp] theorem deningerCanonicalRationalWittEmbedding_normalizedPolynomial
    (P : Polynomial A) (hP : P.coeff 0 = 1) :
    deningerCanonicalRationalWittEmbedding
        (deningerCanonicalRationalWittNormalizedPolynomial P hP) =
      deningerNormalizedPolynomialBigWitt P hP := rfl

@[simp] theorem deningerCanonicalRationalWittEmbedding_normalizedFraction
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerCanonicalRationalWittEmbedding
        (deningerCanonicalRationalWittNormalizedFraction P Q hP hQ) =
      deningerNormalizedPolynomialBigWitt P hP -
        deningerNormalizedPolynomialBigWitt Q hQ := by
  exact deningerRationalBigWittElement_normalizedFraction P Q hP hQ

@[simp] theorem deningerCanonicalRationalWittMap_normalizedPolynomial
    (f : A →+* B) (P : Polynomial A) (hP : P.coeff 0 = 1) :
    deningerCanonicalRationalWittMap f
        (deningerCanonicalRationalWittNormalizedPolynomial P hP) =
      deningerCanonicalRationalWittNormalizedPolynomial (P.map f) (by simp [hP]) := by
  apply DeningerCanonicalRationalWittRing.ext
  change Additive.ofMul (deningerRationalWittAdditiveMap f
      (deningerRationalWittNormalizedPolynomial P hP)) =
    Additive.ofMul (deningerRationalWittNormalizedPolynomial (P.map f) _)
  rw [deningerRationalWittNormalizedPolynomial_map]

@[simp] theorem deningerCanonicalRationalWittMap_normalizedFraction
    (f : A →+* B) (P Q : Polynomial A)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerCanonicalRationalWittMap f
        (deningerCanonicalRationalWittNormalizedFraction P Q hP hQ) =
      deningerCanonicalRationalWittNormalizedFraction (P.map f) (Q.map f)
        (by simp [hP]) (by simp [hQ]) := by
  apply DeningerCanonicalRationalWittRing.ext
  change Additive.ofMul (deningerRationalWittAdditiveMap f
      (deningerRationalWittNormalizedFraction P Q hP hQ)) =
    Additive.ofMul (deningerRationalWittNormalizedFraction (P.map f) (Q.map f) _ _)
  rw [deningerRationalWittNormalizedFraction_map]

theorem deningerCanonicalRationalWitt_eq_normalizedFraction
    (w : DeningerCanonicalRationalWittRing A) :
    ∃ (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1),
      w = deningerCanonicalRationalWittNormalizedFraction P Q hP hQ := by
  obtain ⟨P, Q, hQmem, hP, hQ, hw⟩ :=
    deningerRationalWittAdditive_exists_normalized_fraction A
      (Additive.toMul w.additiveVal)
  refine ⟨P, Q, hP, hQ, ?_⟩
  apply DeningerCanonicalRationalWittRing.ext
  apply Additive.toMul.injective
  exact deningerRationalWitt_eq_normalizedFraction_of_val
    (Additive.toMul w.additiveVal) P Q hQmem hP hQ hw

/-- Deninger's formula `[b] ⊙ f(T)=f(bT)` for a normalized rational function, over every
commutative ring including rings with nilpotents. -/
theorem deningerCanonicalRationalWittTeichmuller_mul_normalizedFraction
    (b : A) (P Q : Polynomial A)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerCanonicalRationalWittTeichmuller b *
        deningerCanonicalRationalWittNormalizedFraction P Q hP hQ =
      deningerCanonicalRationalWittNormalizedFraction
        (deningerPolynomialDilation b P) (deningerPolynomialDilation b Q)
        (by simp [hP]) (by simp [hQ]) := by
  apply deningerCanonicalRationalWittEmbedding_injective
  rw [map_mul, deningerCanonicalRationalWittEmbedding_teichmuller,
    deningerCanonicalRationalWittEmbedding_normalizedFraction,
    deningerCanonicalRationalWittEmbedding_normalizedFraction, mul_sub,
    deningerBigWittTeichmuller_mul_normalizedPolynomial,
    deningerBigWittTeichmuller_mul_normalizedPolynomial]

/-- A common coefficient denominator clears a normalized polynomial after the weighted
substitution `T ↦ dT`.  Degree `n` receives `d^n`, which is precisely why one common ordinary
denominator suffices. -/
theorem deningerPolynomialDilation_commonDenom_mem_lifts
    (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    (P : Polynomial S) (hP : P.coeff 0 = 1) :
    deningerPolynomialDilation
        (algebraMap A S (IsLocalization.commonDenom M P.support P.coeff : A)) P ∈
      Polynomial.lifts (algebraMap A S) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  cases n with
  | zero =>
      refine ⟨1, ?_⟩
      simp [hP]
  | succ n =>
      by_cases hn : n + 1 ∈ P.support
      · let i : P.support := ⟨n + 1, hn⟩
        refine ⟨IsLocalization.integerMultiple M P.support P.coeff i *
            (IsLocalization.commonDenom M P.support P.coeff : A) ^ n, ?_⟩
        rw [map_mul, map_pow, IsLocalization.map_integerMultiple]
        rw [deningerPolynomialDilation_coeff, pow_succ']
        simp only [i, Submonoid.smul_def, Algebra.smul_def]
        ring
      · refine ⟨0, ?_⟩
        have hcoeff : P.coeff (n + 1) = 0 := by
          simpa [Polynomial.mem_support_iff] using hn
        simp [deningerPolynomialDilation_coeff, hcoeff]

/-- A normalized lift can be chosen with literal source constant coefficient one, even when the
coefficient-localization map has a kernel. -/
theorem deningerPolynomialDilation_exists_normalized_lift
    (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    (P : Polynomial S) (hP : P.coeff 0 = 1) :
    ∃ P₀ : Polynomial A, P₀.coeff 0 = 1 ∧
      P₀.map (algebraMap A S) =
        deningerPolynomialDilation
          (algebraMap A S (IsLocalization.commonDenom M P.support P.coeff : A)) P := by
  obtain ⟨L, hL⟩ := (Polynomial.mem_lifts _).mp
    (deningerPolynomialDilation_commonDenom_mem_lifts M P hP)
  let P₀ : Polynomial A := L.erase 0 + 1
  refine ⟨P₀, ?_, ?_⟩
  · simp [P₀]
  · ext n
    by_cases hn : n = 0
    · subst n
      simp [P₀, hP]
    · have hcoeffL :
          algebraMap A S (L.coeff n) =
            (deningerPolynomialDilation
              (algebraMap A S (IsLocalization.commonDenom M P.support P.coeff : A)) P).coeff n := by
          have hc := congrArg (fun R : Polynomial S => R.coeff n) hL
          simpa using hc
      simp [P₀, hn, hcoeffL]
      rw [Polynomial.coeff_one, if_neg hn]

theorem deningerPolynomialDilation_dilation (b c : A) (P : Polynomial A) :
    deningerPolynomialDilation b (deningerPolynomialDilation c P) =
      deningerPolynomialDilation (c * b) P := by
  ext n
  simp [deningerPolynomialDilation_coeff, mul_pow]
  ring

theorem deningerCanonicalRationalWittNormalizedFraction_congr
    {P Q R U : Polynomial A}
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1)
    (hR : R.coeff 0 = 1) (hU : U.coeff 0 = 1)
    (hPR : P = R) (hQU : Q = U) :
    deningerCanonicalRationalWittNormalizedFraction P Q hP hQ =
      deningerCanonicalRationalWittNormalizedFraction R U hR hU := by
  subst R
  subst U
  rfl

@[simp] theorem deningerCanonicalRationalWittTeichmuller_one :
    deningerCanonicalRationalWittTeichmuller (1 : A) = 1 := by
  apply deningerCanonicalRationalWittEmbedding_injective
  rw [deningerCanonicalRationalWittEmbedding_teichmuller,
    deningerBigWittRingTeichmuller_one, map_one]

/-- Multiplicative Teichmüller map used to transport a coefficient submonoid into the
rational-Witt ring. -/
noncomputable def deningerCanonicalRationalWittTeichmullerMonoidHom :
    A →* DeningerCanonicalRationalWittRing A where
  toFun a := deningerCanonicalRationalWittTeichmuller a
  map_one' := deningerCanonicalRationalWittTeichmuller_one
  map_mul' a b := (deningerCanonicalRationalWittTeichmuller_mul a b).symm

@[simp] theorem deningerCanonicalRationalWittTeichmullerMonoidHom_apply (a : A) :
    deningerCanonicalRationalWittTeichmullerMonoidHom a =
      deningerCanonicalRationalWittTeichmuller a := by
  simp [deningerCanonicalRationalWittTeichmullerMonoidHom]

/-- Deninger's denominator submonoid `[M]` inside the rational-Witt ring. -/
noncomputable def deningerCanonicalRationalWittDenominatorSubmonoid (M : Submonoid A) :
    Submonoid (DeningerCanonicalRationalWittRing A) :=
  M.map deningerCanonicalRationalWittTeichmullerMonoidHom

/-- Coefficientwise map supplies the base algebra structure for Deninger's localization theorem. -/
@[reducible] noncomputable def deningerCanonicalRationalWittCoefficientAlgebra
    [Algebra A S] :
    Algebra (DeningerCanonicalRationalWittRing A)
      (DeningerCanonicalRationalWittRing S) :=
  (deningerCanonicalRationalWittMap (algebraMap A S)).toAlgebra

noncomputable instance deningerCanonicalRationalWittCoefficientAlgebraInstance
    [Algebra A S] :
    Algebra (DeningerCanonicalRationalWittRing A)
      (DeningerCanonicalRationalWittRing S) :=
  deningerCanonicalRationalWittCoefficientAlgebra

@[simp] theorem deningerCanonicalRationalWittCoefficientAlgebra_algebraMap
    [Algebra A S] :
    @algebraMap (DeningerCanonicalRationalWittRing A)
        (DeningerCanonicalRationalWittRing S) _ _
        deningerCanonicalRationalWittCoefficientAlgebra =
      deningerCanonicalRationalWittMap (algebraMap A S) := rfl

/-- Equality after coefficient localization has one common annihilator for all coefficients of two
polynomials.  The proof multiplies finitely many annihilators and does not assume regularity of
the localization submonoid. -/
theorem deningerPolynomial_exists_common_annihilator_of_map_eq
    (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    (P Q : Polynomial A)
    (hmap : P.map (algebraMap A S) = Q.map (algebraMap A S)) :
    ∃ m : M, ∀ n : ℕ, (m : A) * (P.coeff n - Q.coeff n) = 0 := by
  classical
  have hcoeffMap (n : ℕ) :
      algebraMap A S (P.coeff n) = algebraMap A S (Q.coeff n) := by
    have hc := congrArg (fun R : Polynomial S => R.coeff n) hmap
    simpa using hc
  have hfinite (F : Finset ℕ) :
      ∃ m : M, ∀ n ∈ F, (m : A) * (P.coeff n - Q.coeff n) = 0 := by
    induction F using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | @insert n F hn ih =>
        obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) (hcoeffMap n)
        obtain ⟨m, hm⟩ := ih
        refine ⟨c * m, ?_⟩
        intro k hk
        rw [Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · calc
            ((c * m : M) : A) * (P.coeff k - Q.coeff k) =
                (m : A) * ((c : A) * P.coeff k - (c : A) * Q.coeff k) := by
                  simp only [Submonoid.coe_mul]
                  ring
            _ = 0 := by rw [hc, sub_self, mul_zero]
        · calc
            ((c * m : M) : A) * (P.coeff k - Q.coeff k) =
                (c : A) * ((m : A) * (P.coeff k - Q.coeff k)) := by
                  simp only [Submonoid.coe_mul]
                  ring
            _ = 0 := by rw [hm k hk, mul_zero]
  obtain ⟨m, hm⟩ := hfinite (P.support ∪ Q.support)
  refine ⟨m, fun n => ?_⟩
  by_cases hn : n ∈ P.support ∪ Q.support
  · exact hm n hn
  · have hnP : P.coeff n = 0 := by
      rw [Finset.mem_union, not_or] at hn
      simpa [Polynomial.mem_support_iff] using hn.1
    have hnQ : Q.coeff n = 0 := by
      rw [Finset.mem_union, not_or] at hn
      simpa [Polynomial.mem_support_iff] using hn.2
    simp [hnP, hnQ]

/-- Torsion-aware kernel clearing: equality after coefficient localization becomes literal
polynomial equality after one Teichmüller dilation. -/
theorem deningerPolynomialDilation_eq_of_map_eq
    (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1)
    (hmap : P.map (algebraMap A S) = Q.map (algebraMap A S)) :
    ∃ m : M,
      deningerPolynomialDilation (m : A) P =
        deningerPolynomialDilation (m : A) Q := by
  obtain ⟨m, hm⟩ :=
    deningerPolynomial_exists_common_annihilator_of_map_eq M P Q hmap
  refine ⟨m, ?_⟩
  ext n
  cases n with
  | zero => simp [hP, hQ]
  | succ n =>
      rw [deningerPolynomialDilation_coeff, deningerPolynomialDilation_coeff]
      have hmn := hm (n + 1)
      linear_combination (m : A) ^ n * hmn

theorem deningerCanonicalRationalWittNormalizedFraction_eq_zero_iff
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerCanonicalRationalWittNormalizedFraction P Q hP hQ = 0 ↔ P = Q := by
  constructor
  · intro hzero
    have hembed := congrArg (deningerCanonicalRationalWittEmbedding (A := A)) hzero
    rw [deningerCanonicalRationalWittEmbedding_normalizedFraction, map_zero] at hembed
    have hbig : deningerNormalizedPolynomialBigWitt P hP =
        deningerNormalizedPolynomialBigWitt Q hQ := sub_eq_zero.mp hembed
    have hrational :
        deningerRationalWittNormalizedPolynomial P hP =
          deningerRationalWittNormalizedPolynomial Q hQ := by
      apply deningerRationalWittToBigWittAdditive_injective A
      have hv := congrArg DeningerBigWittRing.additiveVal hbig
      exact Additive.ofMul.injective hv
    have hlocal := congrArg (fun w : DeningerRationalWittAdditive A =>
      ((w.1 : (DeningerRationalWittLocalization A)ˣ) :
        DeningerRationalWittLocalization A)) hrational
    change (deningerRationalWittNormalizedPolynomialUnit P hP :
        DeningerRationalWittLocalization A) =
      (deningerRationalWittNormalizedPolynomialUnit Q hQ :
        DeningerRationalWittLocalization A) at hlocal
    rw [deningerRationalWittNormalizedPolynomialUnit_val,
      deningerRationalWittNormalizedPolynomialUnit_val] at hlocal
    exact IsLocalization.injective (DeningerRationalWittLocalization A)
      (deningerRationalWittDenominators_le_nonZeroDivisors A) hlocal
  · intro hPQ
    subst Q
    apply deningerCanonicalRationalWittEmbedding_injective
    rw [deningerCanonicalRationalWittEmbedding_normalizedFraction, sub_self, map_zero]

/-- Kernel condition for Deninger's coefficientwise rational-Witt localization map.  It is stated
directly in the form required by `IsLocalization.exists_of_eq`. -/
theorem deningerCanonicalRationalWittCoefficientMap_exists_of_eq
    (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    {x y : DeningerCanonicalRationalWittRing A}
    (hxy : deningerCanonicalRationalWittMap (algebraMap A S) x =
      deningerCanonicalRationalWittMap (algebraMap A S) y) :
    ∃ c : deningerCanonicalRationalWittDenominatorSubmonoid M,
      (c : DeningerCanonicalRationalWittRing A) * x = c * y := by
  obtain ⟨P, Q, hP, hQ, hrep⟩ :=
    deningerCanonicalRationalWitt_eq_normalizedFraction (x - y)
  have hmapzero :
      deningerCanonicalRationalWittMap (algebraMap A S) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rw [hrep, deningerCanonicalRationalWittMap_normalizedFraction] at hmapzero
  have hPQmap : P.map (algebraMap A S) = Q.map (algebraMap A S) :=
    (deningerCanonicalRationalWittNormalizedFraction_eq_zero_iff
      (P.map (algebraMap A S)) (Q.map (algebraMap A S))
      (by simp [hP]) (by simp [hQ])).mp hmapzero
  obtain ⟨m, hm⟩ := deningerPolynomialDilation_eq_of_map_eq M P Q hP hQ hPQmap
  let c : deningerCanonicalRationalWittDenominatorSubmonoid M :=
    ⟨deningerCanonicalRationalWittTeichmuller (m : A), by
      exact ⟨m, m.prop, by
        simp [deningerCanonicalRationalWittTeichmullerMonoidHom]⟩⟩
  refine ⟨c, ?_⟩
  have hcsub : (c : DeningerCanonicalRationalWittRing A) * (x - y) = 0 := by
    change deningerCanonicalRationalWittTeichmuller (m : A) * (x - y) = 0
    rw [hrep, deningerCanonicalRationalWittTeichmuller_mul_normalizedFraction]
    exact (deningerCanonicalRationalWittNormalizedFraction_eq_zero_iff
      (deningerPolynomialDilation (m : A) P)
      (deningerPolynomialDilation (m : A) Q)
      (by simp [hP]) (by simp [hQ])).mpr hm
  rw [mul_sub, sub_eq_zero] at hcsub
  exact hcsub

/-- Every rational Witt vector over a coefficient localization is one Teichmüller denominator
away from a coefficientwise lift. -/
theorem deningerCanonicalRationalWittCoefficientMap_surj
    (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    (w : DeningerCanonicalRationalWittRing S) :
    ∃ x : DeningerCanonicalRationalWittRing A ×
        deningerCanonicalRationalWittDenominatorSubmonoid M,
      w * algebraMap (DeningerCanonicalRationalWittRing A)
          (DeningerCanonicalRationalWittRing S) x.2 =
        algebraMap (DeningerCanonicalRationalWittRing A)
          (DeningerCanonicalRationalWittRing S) x.1 := by
  obtain ⟨P, Q, hP, hQ, hrep⟩ :=
    deningerCanonicalRationalWitt_eq_normalizedFraction w
  let dP : M := IsLocalization.commonDenom M P.support P.coeff
  let dQ : M := IsLocalization.commonDenom M Q.support Q.coeff
  obtain ⟨LP, hLP0, hLPmap⟩ :=
    deningerPolynomialDilation_exists_normalized_lift M P hP
  obtain ⟨LQ, hLQ0, hLQmap⟩ :=
    deningerPolynomialDilation_exists_normalized_lift M Q hQ
  let m : M := dP * dQ
  let P₀ : Polynomial A := deningerPolynomialDilation (dQ : A) LP
  let Q₀ : Polynomial A := deningerPolynomialDilation (dP : A) LQ
  have hP₀ : P₀.coeff 0 = 1 := by simp [P₀, hLP0]
  have hQ₀ : Q₀.coeff 0 = 1 := by simp [Q₀, hLQ0]
  have hP₀map : P₀.map (algebraMap A S) =
      deningerPolynomialDilation (algebraMap A S (m : A)) P := by
    calc
      P₀.map (algebraMap A S) =
          deningerPolynomialDilation (algebraMap A S (dQ : A))
            (LP.map (algebraMap A S)) := by
              exact deningerPolynomialDilation_map (algebraMap A S) (dQ : A) LP
      _ = deningerPolynomialDilation (algebraMap A S (dQ : A))
            (deningerPolynomialDilation (algebraMap A S (dP : A)) P) := by
              rw [hLPmap]
      _ = deningerPolynomialDilation
            (algebraMap A S (dP : A) * algebraMap A S (dQ : A)) P :=
              deningerPolynomialDilation_dilation _ _ _
      _ = deningerPolynomialDilation (algebraMap A S (m : A)) P := by
              congr 2
              simp [m, dP, dQ]
  have hQ₀map : Q₀.map (algebraMap A S) =
      deningerPolynomialDilation (algebraMap A S (m : A)) Q := by
    calc
      Q₀.map (algebraMap A S) =
          deningerPolynomialDilation (algebraMap A S (dP : A))
            (LQ.map (algebraMap A S)) := by
              exact deningerPolynomialDilation_map (algebraMap A S) (dP : A) LQ
      _ = deningerPolynomialDilation (algebraMap A S (dP : A))
            (deningerPolynomialDilation (algebraMap A S (dQ : A)) Q) := by
              rw [hLQmap]
      _ = deningerPolynomialDilation
            (algebraMap A S (dQ : A) * algebraMap A S (dP : A)) Q :=
              deningerPolynomialDilation_dilation _ _ _
      _ = deningerPolynomialDilation (algebraMap A S (m : A)) Q := by
              congr 2
              simp [m, dP, dQ, mul_comm]
  let f := deningerCanonicalRationalWittNormalizedFraction P₀ Q₀ hP₀ hQ₀
  let c : deningerCanonicalRationalWittDenominatorSubmonoid M :=
    ⟨deningerCanonicalRationalWittTeichmuller (m : A), by
      exact ⟨m, m.prop, by
        simp [deningerCanonicalRationalWittTeichmullerMonoidHom]⟩⟩
  refine ⟨⟨f, c⟩, ?_⟩
  change w * deningerCanonicalRationalWittMap (algebraMap A S)
      (c : DeningerCanonicalRationalWittRing A) =
    deningerCanonicalRationalWittMap (algebraMap A S) f
  rw [hrep]
  change deningerCanonicalRationalWittNormalizedFraction P Q hP hQ *
      deningerCanonicalRationalWittMap (algebraMap A S)
        (deningerCanonicalRationalWittTeichmuller (m : A)) =
    deningerCanonicalRationalWittMap (algebraMap A S)
      (deningerCanonicalRationalWittNormalizedFraction P₀ Q₀ hP₀ hQ₀)
  rw [deningerCanonicalRationalWittMap_teichmuller,
    deningerCanonicalRationalWittMap_normalizedFraction, mul_comm,
    deningerCanonicalRationalWittTeichmuller_mul_normalizedFraction]
  exact deningerCanonicalRationalWittNormalizedFraction_congr
    (by simp [hP]) (by simp [hQ]) (by simp [hP₀]) (by simp [hQ₀])
    hP₀map.symm hQ₀map.symm

theorem deningerCanonicalRationalWittCoefficientMap_map_units
    (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    (c : deningerCanonicalRationalWittDenominatorSubmonoid M) :
    IsUnit (algebraMap (DeningerCanonicalRationalWittRing A)
      (DeningerCanonicalRationalWittRing S) c) := by
  obtain ⟨a, ha, hac⟩ := c.prop
  rw [← hac]
  change IsUnit (deningerCanonicalRationalWittMap (algebraMap A S)
    (deningerCanonicalRationalWittTeichmuller a))
  rw [deningerCanonicalRationalWittMap_teichmuller]
  exact (IsLocalization.map_units S ⟨a, ha⟩).map
    deningerCanonicalRationalWittTeichmullerMonoidHom

/-- Deninger Proposition 1.1: `W_rat(S)` is the localization of `W_rat(A)` at `[M]` whenever
`S` is the localization of `A` at `M`.  This instance is valid for arbitrary commutative rings,
including rings with nilpotents and localization submonoids containing zero divisors. -/
noncomputable instance deningerCanonicalRationalWitt_isLocalization
    (M : Submonoid A) [Algebra A S] [IsLocalization M S] :
    IsLocalization (deningerCanonicalRationalWittDenominatorSubmonoid M)
      (DeningerCanonicalRationalWittRing S) where
  map_units := deningerCanonicalRationalWittCoefficientMap_map_units M
  surj := deningerCanonicalRationalWittCoefficientMap_surj M
  exists_of_eq := by
    intro x y hxy
    apply deningerCanonicalRationalWittCoefficientMap_exists_of_eq (S := S) M
    exact hxy

/-- Algebra equivalence form of Deninger's Proposition 1.1. -/
noncomputable def deningerCanonicalRationalWittLocalizationAlgEquiv
    (M : Submonoid A) [Algebra A S] [IsLocalization M S] :
    Localization (deningerCanonicalRationalWittDenominatorSubmonoid M) ≃ₐ[
      DeningerCanonicalRationalWittRing A] DeningerCanonicalRationalWittRing S :=
  IsLocalization.algEquiv
    (deningerCanonicalRationalWittDenominatorSubmonoid M)
    (Localization (deningerCanonicalRationalWittDenominatorSubmonoid M))
    (DeningerCanonicalRationalWittRing S)

/-- Canonical ring equivalence in Deninger's Proposition 1.1. -/
noncomputable def deningerCanonicalRationalWittLocalizationEquiv
    (M : Submonoid A) [Algebra A S] [IsLocalization M S] :
    Localization (deningerCanonicalRationalWittDenominatorSubmonoid M) ≃+*
      DeningerCanonicalRationalWittRing S :=
  (deningerCanonicalRationalWittLocalizationAlgEquiv M).toRingEquiv

@[simp] theorem deningerCanonicalRationalWittLocalizationEquiv_algebraMap
    (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    (w : DeningerCanonicalRationalWittRing A) :
    deningerCanonicalRationalWittLocalizationEquiv M
        (algebraMap (DeningerCanonicalRationalWittRing A)
          (Localization (deningerCanonicalRationalWittDenominatorSubmonoid M)) w) =
      deningerCanonicalRationalWittMap (algebraMap A S) w := by
  exact (deningerCanonicalRationalWittLocalizationAlgEquiv M).commutes w

end
end RHTower
