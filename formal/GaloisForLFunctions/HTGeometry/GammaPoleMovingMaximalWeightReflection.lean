import GaloisForLFunctions.HTGeometry.GammaPoleCenterFrozenDiagonal
import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Maximal derivative-weight reflection for moving Gamma jets

The faithful symbolic Gamma profile has a conserved tri-grading, but that law
alone does not identify which moving Taylor orders contribute to a selected
scale diagonal.  This file supplies the missing associated-filtration law.

It proves that boundary derivative weight is submultiplicative, that the
`j`-th symbolic Gamma derivative is filtered by weight `j` and pure of inner
scale degree `-j`, and that moving polynomial coefficients agree with their
center-frozen values on inner degree zero.  These facts give the exact
moving-center reflection at maximal derivative weight.

The reflection closes under both weighted and ordinary homogeneous
decomposition.  Consequently every nonzero polynomial-coefficient finite jet
source has a surviving symbolic coefficient.  The symbolic and actual Gamma
moving-pole Laurent evaluations are therefore injective.
-/

open Polynomial LaurentPolynomial MvPolynomial

namespace GaloisForLFunctions

noncomputable section

def gammaPoleBoundaryDerivativeWeightNat : (ℕ →₀ ℕ) →+ ℕ :=
  Finsupp.weight fun k : ℕ => k + 1

def GammaPoleBoundaryFiltered (W : ℕ)
    (F : GammaPoleMovingJetSymbolic) : Prop :=
  ∀ a ∈ (gammaPoleTriFlatten F).support,
    gammaPoleBoundaryDerivativeWeightNat a.2 ≤ W

theorem GammaPoleBoundaryFiltered.zero (W : ℕ) :
    GammaPoleBoundaryFiltered W 0 := by
  intro a ha
  rw [map_zero] at ha
  exact (Finsupp.mem_support_iff.mp ha rfl).elim

theorem GammaPoleBoundaryFiltered.add {W : ℕ}
    {F G : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleBoundaryFiltered W F)
    (hG : GammaPoleBoundaryFiltered W G) :
    GammaPoleBoundaryFiltered W (F + G) := by
  intro a ha
  rw [map_add] at ha
  exact (Finset.mem_union.mp (Finsupp.support_add ha)).elim
    (hF a) (hG a)

theorem GammaPoleBoundaryFiltered.mono {V W : ℕ} (hVW : V ≤ W)
    {F : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleBoundaryFiltered V F) :
    GammaPoleBoundaryFiltered W F := by
  intro a ha
  exact (hF a ha).trans hVW

theorem GammaPoleBoundaryFiltered.mul {V W : ℕ}
    {F G : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleBoundaryFiltered V F)
    (hG : GammaPoleBoundaryFiltered W G) :
    GammaPoleBoundaryFiltered (V + W) (F * G) := by
  intro a ha
  rw [map_mul] at ha
  have ha' := AddMonoidAlgebra.support_mul
    (gammaPoleTriFlatten F) (gammaPoleTriFlatten G) ha
  rcases Finset.mem_add.mp ha' with ⟨x, hx, y, hy, rfl⟩
  change gammaPoleBoundaryDerivativeWeightNat (x.2 + y.2) ≤ V + W
  rw [map_add]
  exact Nat.add_le_add (hF x hx) (hG y hy)

theorem GammaPoleBoundaryFiltered.pow {W : ℕ}
    {F : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleBoundaryFiltered W F) (e : ℕ) :
    GammaPoleBoundaryFiltered (e * W) (F ^ e) := by
  induction e with
  | zero =>
      intro a ha
      rw [pow_zero, map_one] at ha
      have ha0 : a = 0 := by
        by_contra h
        apply Finsupp.mem_support_iff.mp ha
        rw [AddMonoidAlgebra.one_def]
        exact Finsupp.single_eq_of_ne h
      subst a
      simp [gammaPoleBoundaryDerivativeWeightNat]
  | succ e ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul hF

theorem GammaPoleBoundaryFiltered.sum {ι : Type*} {W : ℕ}
    (s : Finset ι) (F : ι → GammaPoleMovingJetSymbolic)
    (hF : ∀ i ∈ s, GammaPoleBoundaryFiltered W (F i)) :
    GammaPoleBoundaryFiltered W (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GammaPoleBoundaryFiltered.zero W
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hF i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem GammaPoleBoundaryFiltered.prod {ι : Type*}
    (s : Finset ι) (F : ι → GammaPoleMovingJetSymbolic) (w : ι → ℕ)
    (hF : ∀ i ∈ s, GammaPoleBoundaryFiltered (w i) (F i)) :
    GammaPoleBoundaryFiltered (∑ i ∈ s, w i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (GammaPoleBoundaryFiltered.pow
        (GammaPoleBoundaryFiltered.zero 0) 0)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (hF i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem gammaPoleBoundaryFiltered_monomial
    (q l : ℤ) (m : ℕ →₀ ℕ) (c : GammaPoleRationalBase) :
    GammaPoleBoundaryFiltered
      (gammaPoleBoundaryDerivativeWeightNat m)
      (LaurentPolynomial.C
          (LaurentPolynomial.C (MvPolynomial.monomial m c) *
            LaurentPolynomial.T l) *
        LaurentPolynomial.T q) := by
  intro a ha
  rw [gammaPoleTriFlatten_monomial] at ha
  by_cases hc : c = 0
  · exact (Finsupp.mem_support_iff.mp ha (by simp [hc])).elim
  · have haeq : a = ((q, l), m) := by
      simpa only [Finsupp.support_single _ hc,
        Finset.mem_singleton] using ha
    subst a
    exact le_rfl

@[simp] theorem gammaPoleBoundaryDerivativeWeightNat_boundaryExponent
    (k : ℕ) :
    gammaPoleBoundaryDerivativeWeightNat (gammaPoleBoundaryExponent k) = k := by
  rcases k with (_ | k)
  · simp [gammaPoleBoundaryExponent, gammaPoleBoundaryDerivativeWeightNat]
  · simp [gammaPoleBoundaryExponent, gammaPoleBoundaryDerivativeWeightNat,
      Finsupp.weight_single]

theorem gammaPoleBoundaryDerivativeWeight_eq_natCast (m : ℕ →₀ ℕ) :
    gammaPoleBoundaryDerivativeWeight m =
      (gammaPoleBoundaryDerivativeWeightNat m : ℤ) := by
  simp only [gammaPoleBoundaryDerivativeWeight,
    gammaPoleBoundaryDerivativeWeightNat, Finsupp.weight_apply]
  rw [Nat.cast_finsupp_sum]
  simp

theorem gammaPoleSymbolicMovingCoefficientLaurent_C_boundaryFiltered
    (c : ℂ) :
    GammaPoleBoundaryFiltered 0
      (gammaPoleSymbolicMovingCoefficientLaurent (Polynomial.C c)) := by
  simp [gammaPoleSymbolicMovingCoefficientLaurent,
    movingPoleTaylorLaurent, scaledTaylorAlgHom,
    polynomialDiagonalScaleAlgHom]
  simpa [gammaPoleRationalScaleDerivativeInclude,
    gammaPoleComplexScaleDerivativeInclude] using
    gammaPoleBoundaryFiltered_monomial 0 0 0 (RatFunc.C c)

theorem gammaPoleSymbolicMovingCoefficientLaurent_X_boundaryFiltered :
    GammaPoleBoundaryFiltered 0
      (gammaPoleSymbolicMovingCoefficientLaurent Polynomial.X) := by
  rw [gammaPoleSymbolicMovingCoefficientLaurent_X_eq]
  apply GammaPoleBoundaryFiltered.add
  · simpa [gammaPoleRationalScaleDerivativeInclude] using
      gammaPoleBoundaryFiltered_monomial 0 0 0 gammaPoleCenterRational
  · rw [gammaPoleSymbolicPhysicalScale, gammaPoleSymbolicScale]
    change GammaPoleBoundaryFiltered 0
      (LaurentPolynomial.C (-LaurentPolynomial.T 1) *
        LaurentPolynomial.T (-1))
    have h := gammaPoleBoundaryFiltered_monomial (-1) 1 0 (-1)
    have heq :
        (-LaurentPolynomial.T 1 : GammaPoleScaleDerivativeSymbolic) =
          LaurentPolynomial.C (MvPolynomial.monomial 0 (-1)) *
            LaurentPolynomial.T 1 := by
      simp
      exact (neg_one_mul
        (LaurentPolynomial.T 1 : GammaPoleScaleDerivativeSymbolic)).symm
    rw [heq]
    simpa using h

theorem gammaPoleSymbolicMovingCoefficientLaurent_boundaryFiltered
    (p : Polynomial ℂ) :
    GammaPoleBoundaryFiltered 0
      (gammaPoleSymbolicMovingCoefficientLaurent p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact hp.add hq
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial,
        map_mul, map_pow]
      simpa using
        (gammaPoleSymbolicMovingCoefficientLaurent_C_boundaryFiltered c).mul
          (gammaPoleSymbolicMovingCoefficientLaurent_X_boundaryFiltered.pow n)

theorem gammaPoleSymbolicDerivativeScale_eq_monomial (j : ℕ) :
    LaurentPolynomial.C (gammaPoleSymbolicDerivativeScale j) =
      LaurentPolynomial.C
          (LaurentPolynomial.C (MvPolynomial.monomial 0
            (RatFunc.C (-((-1 : ℂ) ^ j)))) *
            LaurentPolynomial.T (-(j : ℤ))) *
        LaurentPolynomial.T 0 := by
    rw [LaurentPolynomial.T_zero, mul_one]
    congr 1
    rw [gammaPoleSymbolicDerivativeScale]
    have hpowK :
        (-1 : GammaPoleRationalBase) ^ j = RatFunc.C ((-1 : ℂ) ^ j) := by
      calc
        (-1 : GammaPoleRationalBase) ^ j =
            (RatFunc.C (-1 : ℂ)) ^ j := by simp
        _ = RatFunc.C ((-1 : ℂ) ^ j) := by rw [map_pow]
    have hpow :
        (-1 : GammaPoleScaleDerivativeSymbolic) ^ j =
          LaurentPolynomial.C
            (MvPolynomial.C ((-1 : GammaPoleRationalBase) ^ j)) := by
      calc
        (-1 : GammaPoleScaleDerivativeSymbolic) ^ j =
            (gammaPoleRationalScaleDerivativeInclude
              (-1 : GammaPoleRationalBase)) ^ j := by
          simp [gammaPoleRationalScaleDerivativeInclude]
        _ = gammaPoleRationalScaleDerivativeInclude
            ((-1 : GammaPoleRationalBase) ^ j) := by rw [map_pow]
        _ = _ := rfl
    rw [hpow, hpowK]
    simp
    exact (neg_mul ((-1 : GammaPoleScaleDerivativeSymbolic) ^ j)
      (LaurentPolynomial.T (-(j : ℤ)))).symm
 
theorem gammaPoleSymbolicDerivativeScale_boundaryFiltered (j : ℕ) :
    GammaPoleBoundaryFiltered 0
      (LaurentPolynomial.C (gammaPoleSymbolicDerivativeScale j)) := by
  rw [gammaPoleSymbolicDerivativeScale_eq_monomial]
  simpa using gammaPoleBoundaryFiltered_monomial 0 (-(j : ℤ)) 0
    (RatFunc.C (-((-1 : ℂ) ^ j)))

theorem gammaPoleSymbolicRegularSummand_boundaryFiltered
    (j k : ℕ) :
    GammaPoleBoundaryFiltered k
      (Polynomial.toLaurent
        ((Polynomial.monomial (j - k)
          (MvPolynomial.C (gammaPoleUniversalRegularScalar j k) *
            MvPolynomial.X k)).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval)) := by
  rw [gammaPoleSymbolicRegularSummand_eq]
  simpa using gammaPoleBoundaryFiltered_monomial
    ((j - k : ℕ) : ℤ) 0 (gammaPoleBoundaryExponent k)
    (RatFunc.C (gammaPoleUniversalRegularScalar j k))

theorem gammaPoleSymbolicUniversalRegularLaurentProfile_boundaryFiltered
    (j : ℕ) :
    GammaPoleBoundaryFiltered j
      (Polynomial.toLaurent
        ((HTGeometry.universalSimplePoleRegularProfile j).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval)) := by
  change GammaPoleBoundaryFiltered j
    (Polynomial.toLaurent
      ((Polynomial.mapRingHom gammaPoleSymbolicUnitDerivativeBoundaryEval)
        (HTGeometry.universalSimplePoleRegularProfile j)))
  rw [HTGeometry.universalSimplePoleRegularProfile, map_sum, map_sum]
  apply GammaPoleBoundaryFiltered.sum
  intro k hk
  exact (gammaPoleSymbolicRegularSummand_boundaryFiltered j k).mono
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem gammaPoleSymbolicUniversalJetLaurentProfile_boundaryFiltered
    (j : ℕ) :
    GammaPoleBoundaryFiltered j
      (Polynomial.toLaurent
        ((HTGeometry.universalSimplePoleJetProfile j).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval)) := by
  rw [HTGeometry.universalSimplePoleJetProfile,
    Polynomial.map_mul, map_mul, Polynomial.map_X,
    Polynomial.toLaurent_X]
  have hT : GammaPoleBoundaryFiltered 0
      (LaurentPolynomial.T 1 : GammaPoleMovingJetSymbolic) := by
    simpa using gammaPoleBoundaryFiltered_monomial 1 0 0 1
  simpa using hT.mul
    (gammaPoleSymbolicUniversalRegularLaurentProfile_boundaryFiltered j)

theorem gammaPoleSymbolicDerivativeLaurentProfile_boundaryFiltered
    (j : ℕ) :
    GammaPoleBoundaryFiltered j
      (gammaPoleSymbolicDerivativeLaurentProfile j) := by
  rw [gammaPoleSymbolicDerivativeLaurentProfile]
  simpa using (gammaPoleSymbolicDerivativeScale_boundaryFiltered j).mul
    (gammaPoleSymbolicUniversalJetLaurentProfile_boundaryFiltered j)

/-- Weighted substitution preserves the boundary-weight filtration. -/
theorem gammaPoleBoundaryFiltered_eval₂_of_isWeightedHomogeneous
    {σ R : Type*} [CommSemiring R]
    {w : σ → ℕ} {W : ℕ} {P : MvPolynomial σ R}
    (hP : MvPolynomial.IsWeightedHomogeneous w P W)
    (f : R →+* GammaPoleMovingJetSymbolic)
    (g : σ → GammaPoleMovingJetSymbolic)
    (hf : ∀ r, GammaPoleBoundaryFiltered 0 (f r))
    (hg : ∀ i, GammaPoleBoundaryFiltered (w i) (g i)) :
    GammaPoleBoundaryFiltered W (MvPolynomial.eval₂ f g P) := by
  rw [MvPolynomial.eval₂_eq]
  apply GammaPoleBoundaryFiltered.sum
  intro m hm
  have hprod : GammaPoleBoundaryFiltered
      (∑ i ∈ m.support, m i * w i)
      (∏ i ∈ m.support, g i ^ m i) := by
    apply GammaPoleBoundaryFiltered.prod
    intro i hi
    simpa [mul_comm] using (hg i).pow (m i)
  have hterm := (hf (P.coeff m)).mul hprod
  have hweight : ∑ i ∈ m.support, m i * w i = W :=
    hP (MvPolynomial.mem_support_iff.mp hm)
  simpa [hweight] using hterm

/-- A source sector of derivative weight `W` has no symbolic boundary
monomial above weight `W`. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_boundaryFiltered
    {n W : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hW : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P W) :
    GammaPoleBoundaryFiltered W
      (gammaPoleSymbolicPolynomialJetLaurentEval n P) := by
  simpa only [gammaPoleSymbolicPolynomialJetLaurentEval] using
    gammaPoleBoundaryFiltered_eval₂_of_isWeightedHomogeneous hW
      gammaPoleSymbolicMovingCoefficientLaurent
      (fun j : Fin (n + 1) =>
        gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ))
      gammaPoleSymbolicMovingCoefficientLaurent_boundaryFiltered
      (fun j =>
        gammaPoleSymbolicDerivativeLaurentProfile_boundaryFiltered (j : ℕ))

theorem GammaPoleBoundaryFiltered.coeff_weight
    {W : ℕ} {F : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleBoundaryFiltered W F)
    {q l : ℤ} {m : ℕ →₀ ℕ}
    (hcoeff : MvPolynomial.coeff m ((F q) l) ≠ 0) :
    gammaPoleBoundaryDerivativeWeightNat m ≤ W := by
  apply hF ((q, l), m)
  rw [Finsupp.mem_support_iff]
  simpa using hcoeff

/-- Lower derivative-weight sectors cannot contribute to the joint maximal
particle/scale diagonal selected by a larger weight. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_coeff_eq_zero_of_weight_lt
    {n D V W : ℕ}
    {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D)
    (hV : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P V)
    (hVW : V < W) (m : ℕ →₀ ℕ) :
    MvPolynomial.coeff m
        ((gammaPoleSymbolicPolynomialJetLaurentEval n P (D : ℤ))
          (-(W : ℤ))) = 0 := by
  by_contra hcoeff
  have htri := gammaPoleSymbolicPolynomialJetLaurentEval_support_weight
    hD hcoeff
  have hfilter :=
    (gammaPoleSymbolicPolynomialJetLaurentEval_boundaryFiltered hV).coeff_weight
      hcoeff
  have hweightInt : gammaPoleBoundaryDerivativeWeight m = (W : ℤ) := by
    omega
  rw [gammaPoleBoundaryDerivativeWeight_eq_natCast] at hweightInt
  have hweightNat : gammaPoleBoundaryDerivativeWeightNat m = W := by
    exact_mod_cast hweightInt
  omega

/-- Exact purity in the signed factorial-scale coordinate. -/
def GammaPoleInnerPure (l : ℤ)
    (F : GammaPoleMovingJetSymbolic) : Prop :=
  ∀ a ∈ (gammaPoleTriFlatten F).support, a.1.2 = l

theorem GammaPoleInnerPure.zero (l : ℤ) :
    GammaPoleInnerPure l 0 := by
  intro a ha
  rw [map_zero] at ha
  exact (Finsupp.mem_support_iff.mp ha rfl).elim

theorem GammaPoleInnerPure.one :
    GammaPoleInnerPure 0 (1 : GammaPoleMovingJetSymbolic) := by
  intro a ha
  rw [map_one] at ha
  have ha0 : a = 0 := by
    by_contra h
    apply Finsupp.mem_support_iff.mp ha
    rw [AddMonoidAlgebra.one_def]
    exact Finsupp.single_eq_of_ne h
  subst a
  rfl

theorem GammaPoleInnerPure.add {l : ℤ}
    {F G : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleInnerPure l F)
    (hG : GammaPoleInnerPure l G) :
    GammaPoleInnerPure l (F + G) := by
  intro a ha
  rw [map_add] at ha
  exact (Finset.mem_union.mp (Finsupp.support_add ha)).elim
    (hF a) (hG a)

theorem GammaPoleInnerPure.mul {l r : ℤ}
    {F G : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleInnerPure l F)
    (hG : GammaPoleInnerPure r G) :
    GammaPoleInnerPure (l + r) (F * G) := by
  intro a ha
  rw [map_mul] at ha
  have ha' := AddMonoidAlgebra.support_mul
    (gammaPoleTriFlatten F) (gammaPoleTriFlatten G) ha
  rcases Finset.mem_add.mp ha' with ⟨x, hx, y, hy, rfl⟩
  change x.1.2 + y.1.2 = l + r
  rw [hF x hx, hG y hy]

theorem GammaPoleInnerPure.pow {l : ℤ}
    {F : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleInnerPure l F) (e : ℕ) :
    GammaPoleInnerPure ((e : ℤ) * l) (F ^ e) := by
  induction e with
  | zero => simpa using GammaPoleInnerPure.one
  | succ e ih =>
      rw [pow_succ, Nat.cast_succ]
      convert ih.mul hF using 1
      ring

theorem GammaPoleInnerPure.sum {ι : Type*} {l : ℤ}
    (s : Finset ι) (F : ι → GammaPoleMovingJetSymbolic)
    (hF : ∀ i ∈ s, GammaPoleInnerPure l (F i)) :
    GammaPoleInnerPure l (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GammaPoleInnerPure.zero l
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hF i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem GammaPoleInnerPure.prod {ι : Type*}
    (s : Finset ι) (F : ι → GammaPoleMovingJetSymbolic) (l : ι → ℤ)
    (hF : ∀ i ∈ s, GammaPoleInnerPure (l i) (F i)) :
    GammaPoleInnerPure (∑ i ∈ s, l i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GammaPoleInnerPure.one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (hF i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem gammaPoleInnerPure_monomial
    (q l : ℤ) (m : ℕ →₀ ℕ) (c : GammaPoleRationalBase) :
    GammaPoleInnerPure l
      (LaurentPolynomial.C
          (LaurentPolynomial.C (MvPolynomial.monomial m c) *
            LaurentPolynomial.T l) *
        LaurentPolynomial.T q) := by
  intro a ha
  rw [gammaPoleTriFlatten_monomial] at ha
  by_cases hc : c = 0
  · exact (Finsupp.mem_support_iff.mp ha (by simp [hc])).elim
  · have haeq : a = ((q, l), m) := by
      simpa only [Finsupp.support_single _ hc,
        Finset.mem_singleton] using ha
    subst a
    rfl

theorem gammaPoleSymbolicDerivativeScale_innerPure (j : ℕ) :
    GammaPoleInnerPure (-(j : ℤ))
      (LaurentPolynomial.C (gammaPoleSymbolicDerivativeScale j)) := by
  rw [gammaPoleSymbolicDerivativeScale_eq_monomial]
  simpa using gammaPoleInnerPure_monomial 0 (-(j : ℤ)) 0
    (RatFunc.C (-((-1 : ℂ) ^ j)))

theorem gammaPoleSymbolicRegularSummand_innerPure (j k : ℕ) :
    GammaPoleInnerPure 0
      (Polynomial.toLaurent
        ((Polynomial.monomial (j - k)
          (MvPolynomial.C (gammaPoleUniversalRegularScalar j k) *
            MvPolynomial.X k)).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval)) := by
  rw [gammaPoleSymbolicRegularSummand_eq]
  simpa using gammaPoleInnerPure_monomial
    ((j - k : ℕ) : ℤ) 0 (gammaPoleBoundaryExponent k)
    (RatFunc.C (gammaPoleUniversalRegularScalar j k))

theorem gammaPoleSymbolicUniversalRegularLaurentProfile_innerPure
    (j : ℕ) :
    GammaPoleInnerPure 0
      (Polynomial.toLaurent
        ((HTGeometry.universalSimplePoleRegularProfile j).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval)) := by
  change GammaPoleInnerPure 0
    (Polynomial.toLaurent
      ((Polynomial.mapRingHom gammaPoleSymbolicUnitDerivativeBoundaryEval)
        (HTGeometry.universalSimplePoleRegularProfile j)))
  rw [HTGeometry.universalSimplePoleRegularProfile, map_sum, map_sum]
  exact GammaPoleInnerPure.sum _ _ fun k _ =>
    gammaPoleSymbolicRegularSummand_innerPure j k

theorem gammaPoleSymbolicUniversalJetLaurentProfile_innerPure
    (j : ℕ) :
    GammaPoleInnerPure 0
      (Polynomial.toLaurent
        ((HTGeometry.universalSimplePoleJetProfile j).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval)) := by
  rw [HTGeometry.universalSimplePoleJetProfile,
    Polynomial.map_mul, map_mul, Polynomial.map_X,
    Polynomial.toLaurent_X]
  have hT : GammaPoleInnerPure 0
      (LaurentPolynomial.T 1 : GammaPoleMovingJetSymbolic) := by
    simpa using gammaPoleInnerPure_monomial 1 0 0 1
  simpa using hT.mul
    (gammaPoleSymbolicUniversalRegularLaurentProfile_innerPure j)

/-- Each symbolic derivative has exactly one signed factorial-scale degree. -/
theorem gammaPoleSymbolicDerivativeLaurentProfile_innerPure (j : ℕ) :
    GammaPoleInnerPure (-(j : ℤ))
      (gammaPoleSymbolicDerivativeLaurentProfile j) := by
  rw [gammaPoleSymbolicDerivativeLaurentProfile]
  simpa using (gammaPoleSymbolicDerivativeScale_innerPure j).mul
    (gammaPoleSymbolicUniversalJetLaurentProfile_innerPure j)

theorem gammaPoleSymbolicDerivativeMonomialProduct_innerPure
    {n W : ℕ} (α : Fin (n + 1) →₀ ℕ)
    (hα : ∑ j ∈ α.support, α j * (j : ℕ) = W) :
    GammaPoleInnerPure (-(W : ℤ))
      (∏ j ∈ α.support,
        gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ) ^ α j) := by
  have hprod := GammaPoleInnerPure.prod α.support
    (fun j : Fin (n + 1) =>
      gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ) ^ α j)
    (fun j : Fin (n + 1) =>
      (α j : ℤ) * (-(j : ℤ)))
    (fun j _ => (gammaPoleSymbolicDerivativeLaurentProfile_innerPure
      (j : ℕ)).pow (α j))
  have hαInt :
      (∑ j ∈ α.support, ((α j * (j : ℕ) : ℕ) : ℤ)) = (W : ℤ) := by
    exact_mod_cast hα
  have hsum :
      (∑ j ∈ α.support, (α j : ℤ) * (-(j : ℤ))) =
        -(W : ℤ) := by
    calc
      ∑ j ∈ α.support, (α j : ℤ) * (-(j : ℤ)) =
        -(∑ j ∈ α.support, ((α j * (j : ℕ) : ℕ) : ℤ)) := by
        simp only [mul_neg, Nat.cast_mul]
        rw [Finset.sum_neg_distrib]
      _ = -(W : ℤ) := by rw [hαInt]
  rw [← hsum]
  exact hprod

/-- Multiplying a zero-free inner slice by a pure inner-degree packet cannot
create the packet's inner degree. -/
theorem gammaPoleInnerZero_mul_eq_zero
    {A B : GammaPoleMovingJetSymbolic} {l : ℤ}
    (hA : ∀ q : ℤ, (A q) 0 = 0)
    (hB : GammaPoleInnerPure l B) (q : ℤ) :
    ((A * B) q) l = 0 := by
  ext m
  by_contra hcoeff
  have hsupp : ((q, l), m) ∈
      (gammaPoleTriFlatten (A * B)).support := by
    rw [Finsupp.mem_support_iff]
    change MvPolynomial.coeff m (((A * B) q) l) ≠ 0
    exact hcoeff
  rw [map_mul] at hsupp
  have hsupp' := AddMonoidAlgebra.support_mul
    (gammaPoleTriFlatten A) (gammaPoleTriFlatten B) hsupp
  rcases Finset.mem_add.mp hsupp' with ⟨x, hx, y, hy, hxy⟩
  have hinner := congrArg (fun a : GammaPoleTriIndex => a.1.2) hxy
  change x.1.2 + y.1.2 = l at hinner
  have hxinner : x.1.2 = 0 := by
    rw [hB y hy] at hinner
    omega
  have hxne : gammaPoleTriFlatten A x ≠ 0 :=
    Finsupp.mem_support_iff.mp hx
  apply hxne
  rcases x with ⟨⟨xq, xl⟩, xm⟩
  change xl = 0 at hxinner
  simp [gammaPoleTriFlatten_apply, hxinner, hA xq]

/-- Inner degree zero of the full moving Taylor coefficient is exactly its
center value; all nonzero Taylor orders occupy nonzero inner scale degree. -/
theorem gammaPoleSymbolicMovingCoefficientLaurent_inner_coeff_zero
    (p : Polynomial ℂ) (q : ℤ) :
    (gammaPoleSymbolicMovingCoefficientLaurent p q) 0 =
      if q = 0 then MvPolynomial.C (gammaPoleCenterRationalEval p) else 0 := by
  by_cases hq : q = 0
  · subst q
    simp [gammaPoleSymbolicMovingCoefficientLaurent_coeff_zero,
      gammaPoleRationalScaleDerivativeInclude]
  · rw [if_neg hq]
    ext m
    simp only [MvPolynomial.coeff_zero]
    by_contra hcoeff
    have hfilter :=
      (gammaPoleSymbolicMovingCoefficientLaurent_boundaryFiltered p).coeff_weight
        hcoeff
    have htri :=
      (gammaPoleSymbolicMovingCoefficientLaurent_trihomogeneous p).support_weight
        hcoeff
    have hweightNat : gammaPoleBoundaryDerivativeWeightNat m = 0 := by omega
    have hweightInt : gammaPoleBoundaryDerivativeWeight m = 0 := by
      rw [gammaPoleBoundaryDerivativeWeight_eq_natCast, hweightNat]
      rfl
    omega

theorem gammaPoleSymbolicMovingCoefficientLaurent_inner_coeff_zero_eq_center
    (p : Polynomial ℂ) (q : ℤ) :
    (gammaPoleSymbolicMovingCoefficientLaurent p q) 0 =
      (gammaPoleSymbolicCenterCoefficientInclude p q) 0 := by
  rw [gammaPoleSymbolicMovingCoefficientLaurent_inner_coeff_zero]
  change (if q = 0 then MvPolynomial.C (gammaPoleCenterRationalEval p) else 0) =
    ((LaurentPolynomial.C
      (gammaPoleRationalScaleDerivativeInclude
        (gammaPoleCenterRationalEval p)) : GammaPoleMovingJetSymbolic) q) 0
  by_cases hq : q = 0
  · subst q
    simp [gammaPoleRationalScaleDerivativeInclude]
  · rw [if_neg hq, LaurentPolynomial.C_apply, if_neg hq]
    rfl

theorem gammaPoleSymbolicMovingCoefficient_sub_center_inner_coeff_zero
    (p : Polynomial ℂ) (q : ℤ) :
    ((gammaPoleSymbolicMovingCoefficientLaurent p -
        gammaPoleSymbolicCenterCoefficientInclude p) q) 0 = 0 := by
  change (gammaPoleSymbolicMovingCoefficientLaurent p q) 0 -
      (gammaPoleSymbolicCenterCoefficientInclude p q) 0 = 0
  rw [gammaPoleSymbolicMovingCoefficientLaurent_inner_coeff_zero_eq_center]
  exact sub_self _

def gammaPoleOuterInnerCoefficient (q l : ℤ) :
    GammaPoleMovingJetSymbolic →+ MvPolynomial ℕ GammaPoleRationalBase where
  toFun F := (F q) l
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem gammaPoleOuterInnerCoefficient_apply
    (q l : ℤ) (F : GammaPoleMovingJetSymbolic) :
    gammaPoleOuterInnerCoefficient q l F = (F q) l := rfl

/-- **Moving-center maximal-weight reflection.** On a fixed derivative-weight
sector, the full moving Taylor evaluation and the frozen center evaluation
have identical coefficient at the sector's signed factorial-scale degree. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_inner_coeff_eq_center
    {n W : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hW : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P W) (q : ℤ) :
    (gammaPoleSymbolicPolynomialJetLaurentEval n P q) (-(W : ℤ)) =
      (gammaPoleSymbolicCenterJetLaurentEval n P q) (-(W : ℤ)) := by
  change gammaPoleOuterInnerCoefficient q (-(W : ℤ))
      (MvPolynomial.eval₂ gammaPoleSymbolicMovingCoefficientLaurent
      (fun j : Fin (n + 1) =>
        gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ)) P) =
    gammaPoleOuterInnerCoefficient q (-(W : ℤ))
      (MvPolynomial.eval₂ gammaPoleSymbolicCenterCoefficientInclude
      (fun j : Fin (n + 1) =>
        gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ)) P)
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro α hαSupport
  rw [← sub_eq_zero]
  change (((gammaPoleSymbolicMovingCoefficientLaurent (P.coeff α) *
      ∏ j ∈ α.support,
        gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ) ^ α j) -
    gammaPoleSymbolicCenterCoefficientInclude (P.coeff α) *
      ∏ j ∈ α.support,
        gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ) ^ α j) q)
          (-(W : ℤ)) = 0
  have hpure := gammaPoleSymbolicDerivativeMonomialProduct_innerPure α
    (hW (MvPolynomial.mem_support_iff.mp hαSupport))
  have hzero := gammaPoleInnerZero_mul_eq_zero
    (A := gammaPoleSymbolicMovingCoefficientLaurent (P.coeff α) -
      gammaPoleSymbolicCenterCoefficientInclude (P.coeff α))
    (B := ∏ j ∈ α.support,
      gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ) ^ α j)
    (gammaPoleSymbolicMovingCoefficient_sub_center_inner_coeff_zero
      (P.coeff α)) hpure q
  have hfactor :
      (gammaPoleSymbolicMovingCoefficientLaurent (P.coeff α) -
          gammaPoleSymbolicCenterCoefficientInclude (P.coeff α)) *
            (∏ j ∈ α.support,
              gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ) ^ α j) =
        gammaPoleSymbolicMovingCoefficientLaurent (P.coeff α) *
            (∏ j ∈ α.support,
              gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ) ^ α j) -
          gammaPoleSymbolicCenterCoefficientInclude (P.coeff α) *
            (∏ j ∈ α.support,
              gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ) ^ α j) := by
    ring
  rw [hfactor] at hzero
  exact hzero

/-- **Full moving nonlinear diagonal.** Polynomial motion of the pole center
does not alter the maximal derivative-weight diagonal. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_particle_derivative_coeff
    {n D W : ℕ}
    {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P W) :
    (gammaPoleSymbolicPolynomialJetLaurentEval n P (D : ℤ)) (-(W : ℤ)) =
      MvPolynomial.C (RatFunc.C ((-1 : ℂ) ^ (D + W))) *
        gammaPoleCenterBoundaryPolynomialEval n P := by
  rw [gammaPoleSymbolicPolynomialJetLaurentEval_inner_coeff_eq_center hW,
    gammaPoleSymbolicCenterJetLaurentEval_particle_derivative_coeff hD hW]

/-- The full moving maximal-weight diagonal of every nonzero bihomogeneous
source sector is nonzero. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_particle_derivative_coeff_ne_zero
    {n D W : ℕ}
    {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P W)
    (hP : P ≠ 0) :
    (gammaPoleSymbolicPolynomialJetLaurentEval n P (D : ℤ)) (-(W : ℤ)) ≠ 0 := by
  rw [gammaPoleSymbolicPolynomialJetLaurentEval_inner_coeff_eq_center hW]
  exact gammaPoleSymbolicCenterJetLaurentEval_particle_derivative_coeff_ne_zero
    hD hW hP

theorem isHomogeneous_weightedHomogeneousComponent
    {σ R : Type*} [CommSemiring R]
    {P : MvPolynomial σ R} {D : ℕ} (hD : P.IsHomogeneous D)
    (w : σ → ℕ) (W : ℕ) :
    (MvPolynomial.weightedHomogeneousComponent w W P).IsHomogeneous D := by
  intro m hm
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hm
  split at hm
  · exact hD hm
  · exact (hm rfl).elim

theorem weightedHomogeneousComponent_weightedTotalDegree_ne_zero
    {σ R : Type*} [CommSemiring R]
    (w : σ → ℕ) {P : MvPolynomial σ R} (hP : P ≠ 0) :
    MvPolynomial.weightedHomogeneousComponent w
      (P.weightedTotalDegree w) P ≠ 0 := by
  classical
  obtain ⟨m, hm, hweight⟩ :=
    Finset.sup_mem_of_nonempty (f := fun m : σ →₀ ℕ => Finsupp.weight w m)
      (MvPolynomial.support_nonempty.mpr hP)
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff m) hzero
  have hweight' : Finsupp.weight w m = P.weightedTotalDegree w := by
    simpa [MvPolynomial.weightedTotalDegree] using hweight
  rw [MvPolynomial.coeff_weightedHomogeneousComponent,
    if_pos hweight', MvPolynomial.coeff_zero] at hcoeff
  exact MvPolynomial.mem_support_iff.mp hm hcoeff

theorem sum_weightedHomogeneousComponent_range
    {σ R : Type*} [CommSemiring R]
    (w : σ → ℕ) (P : MvPolynomial σ R) :
    (∑ W ∈ Finset.range (P.weightedTotalDegree w + 1),
      MvPolynomial.weightedHomogeneousComponent w W P) = P := by
  classical
  ext m
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases hcoeff : MvPolynomial.coeff m P = 0
  · simp [hcoeff]
  · have hm : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff
    have hle := MvPolynomial.le_weightedTotalDegree w hm
    rw [Finset.sum_eq_single (Finsupp.weight w m)]
    · rw [if_pos rfl]
    · intro W hW hne
      rw [if_neg]
      exact Ne.symm hne
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))).elim

def gammaPoleSymbolicPolynomialJetOuterInnerCoefficient
    (n : ℕ) (q l : ℤ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+
      MvPolynomial ℕ GammaPoleRationalBase :=
  (gammaPoleOuterInnerCoefficient q l).comp
    (gammaPoleSymbolicPolynomialJetLaurentEval n).toAddMonoidHom

@[simp] theorem gammaPoleSymbolicPolynomialJetOuterInnerCoefficient_apply
    (n : ℕ) (q l : ℤ)
    (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    gammaPoleSymbolicPolynomialJetOuterInnerCoefficient n q l P =
      (gammaPoleSymbolicPolynomialJetLaurentEval n P q) l := rfl

theorem gammaPoleSymbolicPolynomialJetLaurentEval_inner_coeff_eq_zero_of_weight_lt
    {n D V W : ℕ}
    {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D)
    (hV : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P V)
    (hVW : V < W) :
    (gammaPoleSymbolicPolynomialJetLaurentEval n P (D : ℤ))
      (-(W : ℤ)) = 0 := by
  ext m
  exact gammaPoleSymbolicPolynomialJetLaurentEval_coeff_eq_zero_of_weight_lt
    hD hV hVW m

/-- Every nonzero particle-homogeneous source has a nonzero full moving
diagonal at the maximal derivative weight occurring in that source. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_maximalWeight_coeff_ne_zero
    {n D : ℕ}
    {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D) (hP : P ≠ 0) :
    let W := P.weightedTotalDegree gammaPoleSourceDerivativeWeight
    (gammaPoleSymbolicPolynomialJetLaurentEval n P (D : ℤ))
      (-(W : ℤ)) ≠ 0 := by
  let W := P.weightedTotalDegree gammaPoleSourceDerivativeWeight
  let Q := MvPolynomial.weightedHomogeneousComponent
    gammaPoleSourceDerivativeWeight W P
  have hQ : Q ≠ 0 := by
    exact weightedHomogeneousComponent_weightedTotalDegree_ne_zero
      gammaPoleSourceDerivativeWeight hP
  have hQD : Q.IsHomogeneous D := by
    exact isHomogeneous_weightedHomogeneousComponent hD
      gammaPoleSourceDerivativeWeight W
  have hQW : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight Q W := by
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous W P
  have hQdiag :
      gammaPoleSymbolicPolynomialJetOuterInnerCoefficient n
        (D : ℤ) (-(W : ℤ)) Q ≠ 0 := by
    exact gammaPoleSymbolicPolynomialJetLaurentEval_particle_derivative_coeff_ne_zero
      hQD hQW hQ
  have hsum := sum_weightedHomogeneousComponent_range
    gammaPoleSourceDerivativeWeight P
  change gammaPoleSymbolicPolynomialJetOuterInnerCoefficient n
      (D : ℤ) (-(W : ℤ)) P ≠ 0
  rw [← hsum, map_sum]
  rw [Finset.sum_eq_single W]
  · exact hQdiag
  · intro V hV hVW
    have hVlt : V < W := by
      have hVle : V ≤ W := Nat.le_of_lt_succ (Finset.mem_range.mp hV)
      omega
    exact gammaPoleSymbolicPolynomialJetLaurentEval_inner_coeff_eq_zero_of_weight_lt
      (isHomogeneous_weightedHomogeneousComponent hD
        gammaPoleSourceDerivativeWeight V)
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous V P)
      hVlt
  · intro hWnot
    exact (hWnot (Finset.mem_range.mpr (Nat.lt_succ_self W))).elim

def gammaPoleSymbolicPolynomialJetTriCoefficient
    (n : ℕ) (q l : ℤ) (m : ℕ →₀ ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+ GammaPoleRationalBase :=
  (MvPolynomial.coeffAddMonoidHom m).comp
    (gammaPoleSymbolicPolynomialJetOuterInnerCoefficient n q l)

@[simp] theorem gammaPoleSymbolicPolynomialJetTriCoefficient_apply
    (n : ℕ) (q l : ℤ) (m : ℕ →₀ ℕ)
    (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    gammaPoleSymbolicPolynomialJetTriCoefficient n q l m P =
      MvPolynomial.coeff m
        ((gammaPoleSymbolicPolynomialJetLaurentEval n P q) l) := rfl

/-- Every nonzero polynomial-coefficient differential source has a surviving
joint particle/scale coefficient.  The selected source sector is the top
ordinary homogeneous component followed by its top derivative-weight
component. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_leadingParticleMaximalWeight_coeff_ne_zero
    (n : ℕ) {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hP : P ≠ 0) :
    (gammaPoleSymbolicPolynomialJetLaurentEval n P (P.totalDegree : ℤ))
      (-(((MvPolynomial.homogeneousComponent P.totalDegree P).weightedTotalDegree
        gammaPoleSourceDerivativeWeight : ℕ) : ℤ)) ≠ 0 := by
  let D := P.totalDegree
  let H := MvPolynomial.homogeneousComponent D P
  have hH : H ≠ 0 := by
    simpa [D, H] using HTGeometry.homogeneousComponent_totalDegree_ne_zero hP
  have hHD : H.IsHomogeneous D := by
    exact MvPolynomial.homogeneousComponent_isHomogeneous D P
  let W := H.weightedTotalDegree gammaPoleSourceDerivativeWeight
  change (gammaPoleSymbolicPolynomialJetLaurentEval n P (D : ℤ))
    (-(W : ℤ)) ≠ 0
  have hHdiag :
      (gammaPoleSymbolicPolynomialJetLaurentEval n H (D : ℤ))
        (-(W : ℤ)) ≠ 0 := by
    exact gammaPoleSymbolicPolynomialJetLaurentEval_maximalWeight_coeff_ne_zero
      hHD hH
  obtain ⟨m, hm⟩ := MvPolynomial.exists_coeff_ne_zero hHdiag
  have hmweightEq : gammaPoleBoundaryDerivativeWeight m = (W : ℤ) := by
    have hmweight := gammaPoleSymbolicPolynomialJetLaurentEval_support_weight
      hHD hm
    omega
  have hsum :
      (∑ e ∈ Finset.range (D + 1),
        MvPolynomial.homogeneousComponent e P) = P := by
    simpa [D] using MvPolynomial.sum_homogeneousComponent P
  have hcoeffEq :
      gammaPoleSymbolicPolynomialJetTriCoefficient n
          (D : ℤ) (-(W : ℤ)) m P =
        gammaPoleSymbolicPolynomialJetTriCoefficient n
          (D : ℤ) (-(W : ℤ)) m H := by
    rw [← hsum, map_sum]
    rw [Finset.sum_eq_single D]
    · intro e he heD
      by_contra hecoeff
      change MvPolynomial.coeff m
        ((gammaPoleSymbolicPolynomialJetLaurentEval n
          (MvPolynomial.homogeneousComponent e P) (D : ℤ))
            (-(W : ℤ))) ≠ 0 at hecoeff
      have heweight := gammaPoleSymbolicPolynomialJetLaurentEval_support_weight
        (MvPolynomial.homogeneousComponent_isHomogeneous e P) hecoeff
      omega
    · intro hDnot
      exact (hDnot (Finset.mem_range.mpr (Nat.lt_succ_self D))).elim
  have hsourceCoeff :
      gammaPoleSymbolicPolynomialJetTriCoefficient n
        (D : ℤ) (-(W : ℤ)) m P ≠ 0 := by
    rw [hcoeffEq]
    exact hm
  intro hzero
  apply hsourceCoeff
  change MvPolynomial.coeff m
    ((gammaPoleSymbolicPolynomialJetLaurentEval n P (D : ℤ))
      (-(W : ℤ))) = 0
  rw [hzero]
  rfl

/-- Every nonzero polynomial-coefficient differential source has a surviving
symbolic moving-pole profile. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_ne_zero
    (n : ℕ) {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hP : P ≠ 0) :
    gammaPoleSymbolicPolynomialJetLaurentEval n P ≠ 0 := by
  have hdiag :=
    gammaPoleSymbolicPolynomialJetLaurentEval_leadingParticleMaximalWeight_coeff_ne_zero
      n hP
  intro hzero
  apply hdiag
  rw [hzero]
  rfl

/-- The faithful symbolic moving-pole jet substitution is injective for every
finite Gamma jet packet over polynomial coefficients. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_injective (n : ℕ) :
    Function.Injective (gammaPoleSymbolicPolynomialJetLaurentEval n) := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  by_contra hne
  have himage := gammaPoleSymbolicPolynomialJetLaurentEval_ne_zero n hne
  apply himage
  rw [map_sub, hPQ, sub_self]

/-- Actual Gamma germ Laurent evaluation inherits the symbolic injectivity. -/
theorem gammaPolePolynomialJetLaurentEval_injective (n : ℕ) :
    Function.Injective (gammaPolePolynomialJetLaurentEval n) := by
  intro P Q hPQ
  apply gammaPoleSymbolicPolynomialJetLaurentEval_injective n
  exact (gammaPolePolynomialJetLaurentEval_eq_iff_symbolic_eq n P Q).mp hPQ

end

end GaloisForLFunctions
