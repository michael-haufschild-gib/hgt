import GaloisForLFunctions.HTGeometry.GammaPoleScaleSeparatedTrace
import GaloisForLFunctions.HTGeometry.SimplePoleJetScaleSeparatedReesGrading

/-!
# The actual Gamma affine simple-pole horizon

The factorially scaled Gamma pole tower is obtained from the universal scale-separated tower by
setting the regular-unit value `U₀` to one and evaluating the remaining scale and derivative
coordinates as algebraically independent pole-index germs.  A priori that value specialization
could let different source-particle sectors cancel.

This module installs the missing reflection law.  A combined Rees grading assigns weight one to
the pole and scale variables and weight `k + 1` to the `k`th positive unit derivative.  A
homogeneous source sector of degree `d` then contributes at pole grade `q` in exact residual weight
`(n + 1) * d - q`.  At nonzero jet ceiling this separates the top particle sector, and after the
source is reduced to its constant and linear parts it makes every forbidden linear coefficient
survive dehomogenization.  The order-zero edge case is the canonical one-variable polynomial
isomorphism.

Consequently, at every finite jet ceiling, the actual Gamma profile has pole degree at most one if
and only if the source is affine in its undifferentiated coordinate.  This closes the finite
constant-coefficient Gamma value-reflection problem.  It does not perform the moving-pole Taylor
shift for coefficients in `ℂ[z]`, which remains the open global meromorphic-intersection step.
-/

open scoped BigOperators
open MvPolynomial Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Combined Rees weight: pole degree, moving scale, and derivative order. -/
def gammaScaleSeparatedProfileWeight : Option (Option ℕ) → ℕ
  | none => 1
  | some none => 1
  | some (some k) => k + 1

def dehomogenizedScaleSeparatedSimplePoleJetProfileMV (n : ℕ)
    (j : Fin (n + 1)) : MvPolynomial (Option (Option ℕ)) ℂ :=
  (MvPolynomial.optionEquivLeft ℂ (Option ℕ)).symm
    ((scaleSeparatedSimplePoleJetProfile n j).map scaleSeparatedPoleUnitDehomogenize)

theorem dehomogenizedScaleSeparatedSimplePoleJetProfileMV_eq_sum
    (n : ℕ) (j : Fin (n + 1)) :
    dehomogenizedScaleSeparatedSimplePoleJetProfileMV n j =
      ∑ k ∈ Finset.range ((j : ℕ) + 1),
        MvPolynomial.C (((j : ℕ).choose k : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - k) *
            ((((j : ℕ) - k).factorial : ℕ) : ℂ)) *
          MvPolynomial.X (some none) ^ (n - (j : ℕ)) *
          MvPolynomial.X none ^ ((j : ℕ) - k + 1) *
          (match k with
          | 0 => 1
          | l + 1 => MvPolynomial.X (some (some l))) := by
  rw [dehomogenizedScaleSeparatedSimplePoleJetProfileMV,
    scaleSeparatedSimplePoleJetProfile, universalSimplePoleJetProfile,
    universalSimplePoleRegularProfile]
  simp only [Polynomial.map_mul, Polynomial.map_C, map_mul]
  simp only [Polynomial.map_sum, map_sum]
  simp only [scaleSeparatedPoleUnitDehomogenize_X_none, map_pow]
  simp [← Polynomial.C_mul_X_pow_eq_monomial]
  generalize (MvPolynomial.X (some none) ^ (n - (j : ℕ)) :
    MvPolynomial (Option (Option ℕ)) ℂ) = A
  rw [Finset.mul_sum (Finset.range ((j : ℕ) + 1)) _
    (MvPolynomial.X none : MvPolynomial (Option (Option ℕ)) ℂ)]
  rw [Finset.mul_sum (Finset.range ((j : ℕ) + 1)) _ A]
  apply Finset.sum_congr rfl
  intro k hk
  rcases k with (_ | k)
  · simp [simplePoleBoundaryInclude, scaleSeparatedPoleUnitDehomogenize,
      natHeadDehomogenize]
    ring
  · simp [simplePoleBoundaryInclude, scaleSeparatedPoleUnitDehomogenize,
      natHeadDehomogenize]
    ring

theorem dehomogenizedScaleSeparatedSimplePoleJetProfileMV_isWeightedHomogeneous
    (n : ℕ) (j : Fin (n + 1)) :
    MvPolynomial.IsWeightedHomogeneous gammaScaleSeparatedProfileWeight
      (dehomogenizedScaleSeparatedSimplePoleJetProfileMV n j) (n + 1) := by
  rw [dehomogenizedScaleSeparatedSimplePoleJetProfileMV_eq_sum]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ ?_
  intro k hk
  have hkj : k ≤ (j : ℕ) := by
    simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hc := MvPolynomial.isWeightedHomogeneous_C gammaScaleSeparatedProfileWeight
    (((j : ℕ).choose k : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - k) *
      (((j : ℕ) - k).factorial : ℂ))
  have hS :=
    (MvPolynomial.isWeightedHomogeneous_X ℂ gammaScaleSeparatedProfileWeight
      (some none)).pow (n - (j : ℕ))
  have hT :=
    (MvPolynomial.isWeightedHomogeneous_X ℂ gammaScaleSeparatedProfileWeight none).pow
      ((j : ℕ) - k + 1)
  rcases k with (_ | k)
  · have hU := MvPolynomial.isWeightedHomogeneous_one ℂ
      gammaScaleSeparatedProfileWeight
    convert (((hc.mul hS).mul hT).mul hU) using 1 ;
      simp [gammaScaleSeparatedProfileWeight]
    omega
  · have hU :=
      MvPolynomial.isWeightedHomogeneous_X ℂ gammaScaleSeparatedProfileWeight
        (some (some k))
    convert (((hc.mul hS).mul hT).mul hU) using 1 ;
      simp [gammaScaleSeparatedProfileWeight]
    omega

/-- Flattened evaluation of a finite source after fixing the Gamma unit value. -/
def dehomogenizedScaleSeparatedSimplePoleProfileEvalMV (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Option (Option ℕ)) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (dehomogenizedScaleSeparatedSimplePoleJetProfileMV n)

theorem dehomogenizedScaleSeparatedSimplePoleProfileEvalMV_isWeightedHomogeneous
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d) :
    MvPolynomial.IsWeightedHomogeneous gammaScaleSeparatedProfileWeight
      (dehomogenizedScaleSeparatedSimplePoleProfileEvalMV n P) ((n + 1) * d) := by
  simpa [mul_comm] using isWeightedHomogeneous_eval₂_of_isHomogeneous_mul hP
    gammaScaleSeparatedProfileWeight
    (dehomogenizedScaleSeparatedSimplePoleJetProfileMV n)
    (dehomogenizedScaleSeparatedSimplePoleJetProfileMV_isWeightedHomogeneous n)

theorem optionEquivLeft_dehomogenizedScaleSeparatedSimplePoleProfileEvalMV
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.optionEquivLeft ℂ (Option ℕ)
        (dehomogenizedScaleSeparatedSimplePoleProfileEvalMV n P) =
      (finiteScaleSeparatedSimplePoleProfileEval n P).map
        scaleSeparatedPoleUnitDehomogenize := by
  let lhs : MvPolynomial (Fin (n + 1)) ℂ →+*
      Polynomial (MvPolynomial (Option ℕ) ℂ) :=
    (MvPolynomial.optionEquivLeft ℂ (Option ℕ)).toRingHom.comp
      (dehomogenizedScaleSeparatedSimplePoleProfileEvalMV n)
  let rhs : MvPolynomial (Fin (n + 1)) ℂ →+*
      Polynomial (MvPolynomial (Option ℕ) ℂ) :=
    (Polynomial.mapRingHom scaleSeparatedPoleUnitDehomogenize).comp
      (finiteScaleSeparatedSimplePoleProfileEval n)
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs, dehomogenizedScaleSeparatedSimplePoleProfileEvalMV,
        finiteScaleSeparatedSimplePoleProfileEval,
        scaleSeparatedPoleUnitDehomogenize, natHeadDehomogenize,
        GaloisForLFunctions.optionHeadDehomogenize]
    · intro j
      simp [lhs, rhs, dehomogenizedScaleSeparatedSimplePoleProfileEvalMV,
        finiteScaleSeparatedSimplePoleProfileEval,
        dehomogenizedScaleSeparatedSimplePoleJetProfileMV]
  exact RingHom.congr_fun h P

/-- Rees weight on the dehomogenized boundary: the scale has weight one and the derivative
`U_(k+1)` has weight `k+1`. -/
def gammaScaleSeparatedBoundaryReesWeight : Option ℕ → ℕ
  | none => 1
  | some k => k + 1

theorem dehomogenizedScaleSeparatedSimplePoleProfileEval_coeff_isWeightedHomogeneous
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d)
    (q : ℕ) :
    MvPolynomial.IsWeightedHomogeneous gammaScaleSeparatedBoundaryReesWeight
      (((finiteScaleSeparatedSimplePoleProfileEval n P).map
        scaleSeparatedPoleUnitDehomogenize).coeff q) ((n + 1) * d - q) := by
  have h := GaloisForLFunctions.optionEquivLeft_coeff_isWeightedHomogeneous
    gammaScaleSeparatedProfileWeight
    (dehomogenizedScaleSeparatedSimplePoleProfileEvalMV_isWeightedHomogeneous hP) q
  rw [optionEquivLeft_dehomogenizedScaleSeparatedSimplePoleProfileEvalMV] at h
  have hw : (fun o => gammaScaleSeparatedProfileWeight (some o)) =
      gammaScaleSeparatedBoundaryReesWeight := by
    funext o
    rcases o with (_ | k) <;> rfl
  rw [hw] at h
  simpa [gammaScaleSeparatedProfileWeight] using h

/-- For a nontrivial jet ceiling, the actual Gamma at-most-simple condition already bounds the
source particle degree by one. -/
theorem gammaScaleSeparatedSimplePoleProfileEval_totalDegree_le_one
    {n : ℕ} (hn : 1 ≤ n) (P : MvPolynomial (Fin (n + 1)) ℂ)
    (hprofile : (gammaScaleSeparatedSimplePoleProfileEval n P).natDegree ≤ 1) :
    P.totalDegree ≤ 1 := by
  by_cases hP0 : P = 0
  · simp [hP0]
  let D := P.totalDegree
  by_contra hD
  have hD2 : 2 ≤ D := by omega
  have hcoeff0 : (gammaScaleSeparatedSimplePoleProfileEval n P).coeff D = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hprofile (by omega))
  have hdehom0 : scaleSeparatedPoleUnitDehomogenize
      ((finiteScaleSeparatedSimplePoleProfileEval n P).coeff D) = 0 := by
    apply gammaPoleScaleAndUnitDerivativeEval_injective
    simpa [gammaScaleSeparatedSimplePoleProfileEval,
      gammaScaleSeparatedPoleBoundaryEval, Polynomial.coeff_map] using hcoeff0
  have hsum :
      (∑ e ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent e P) = P := by
    simpa [D] using MvPolynomial.sum_homogeneousComponent P
  have hcoeffsum :
      (∑ e ∈ Finset.range (D + 1),
        scaleSeparatedPoleUnitDehomogenize
          ((finiteScaleSeparatedSimplePoleProfileEval n
            (MvPolynomial.homogeneousComponent e P)).coeff D)) = 0 := by
    calc
      _ = scaleSeparatedPoleUnitDehomogenize
          ((finiteScaleSeparatedSimplePoleProfileEval n
            (∑ e ∈ Finset.range (D + 1),
              MvPolynomial.homogeneousComponent e P)).coeff D) := by simp
      _ = 0 := by rw [hsum, hdehom0]
  have hcomponent := congrArg
    (MvPolynomial.weightedHomogeneousComponent gammaScaleSeparatedBoundaryReesWeight (n * D))
    hcoeffsum
  rw [map_sum, map_zero] at hcomponent
  have hsingle :
      (∑ e ∈ Finset.range (D + 1),
        MvPolynomial.weightedHomogeneousComponent gammaScaleSeparatedBoundaryReesWeight (n * D)
          (scaleSeparatedPoleUnitDehomogenize
            ((finiteScaleSeparatedSimplePoleProfileEval n
              (MvPolynomial.homogeneousComponent e P)).coeff D))) =
        scaleSeparatedPoleUnitDehomogenize
          ((finiteScaleSeparatedSimplePoleProfileEval n
            (MvPolynomial.homogeneousComponent D P)).coeff D) := by
    rw [Finset.sum_eq_single D]
    · have htopWeight :=
        dehomogenizedScaleSeparatedSimplePoleProfileEval_coeff_isWeightedHomogeneous
          (n := n) (MvPolynomial.homogeneousComponent_isHomogeneous D P) D
      have htopWeight' : MvPolynomial.IsWeightedHomogeneous
          gammaScaleSeparatedBoundaryReesWeight
          (scaleSeparatedPoleUnitDehomogenize
            ((finiteScaleSeparatedSimplePoleProfileEval n
              (MvPolynomial.homogeneousComponent D P)).coeff D)) (n * D) := by
        simpa [Polynomial.coeff_map, Nat.add_mul] using htopWeight
      rw [MvPolynomial.weightedHomogeneousComponent_of_mem htopWeight', if_pos rfl]
    · intro e he heD
      have heDle : e ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp he)
      have heWeight :=
        dehomogenizedScaleSeparatedSimplePoleProfileEval_coeff_isWeightedHomogeneous
          (n := n) (MvPolynomial.homogeneousComponent_isHomogeneous e P) D
      have heWeight' : MvPolynomial.IsWeightedHomogeneous
          gammaScaleSeparatedBoundaryReesWeight
          (scaleSeparatedPoleUnitDehomogenize
            ((finiteScaleSeparatedSimplePoleProfileEval n
              (MvPolynomial.homogeneousComponent e P)).coeff D)) ((n + 1) * e - D) := by
        simpa [Polynomial.coeff_map] using heWeight
      rw [MvPolynomial.weightedHomogeneousComponent_of_mem heWeight', if_neg]
      intro hweight
      have htoppos : 0 < n * D := Nat.mul_pos (by omega) (by omega)
      have hsubpos : 0 < (n + 1) * e - D := by rwa [← hweight]
      have hle : D ≤ (n + 1) * e :=
        (Nat.sub_pos_iff_lt.mp hsubpos).le
      have hadd := congrArg (fun x : ℕ => x + D) hweight
      change n * D + D = ((n + 1) * e - D) + D at hadd
      rw [Nat.sub_add_cancel hle] at hadd
      have hleft : n * D + D = (n + 1) * D := by
        rw [Nat.add_mul, one_mul]
      rw [hleft] at hadd
      exact heD (Nat.mul_left_cancel (by omega) hadd).symm
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self D)) hnot
  have htop : MvPolynomial.homogeneousComponent D P ≠ 0 := by
    simpa [D] using homogeneousComponent_totalDegree_ne_zero hP0
  have htopHom := MvPolynomial.homogeneousComponent_isHomogeneous D P
  have htopTrace : scaleSeparatedPoleUnitDehomogenize
      ((finiteScaleSeparatedSimplePoleProfileEval n
        (MvPolynomial.homogeneousComponent D P)).coeff D) ≠ 0 := by
    rw [finiteScaleSeparatedSimplePoleProfileEval_coeff_particleNumber htopHom]
    exact scaleSeparatedPoleUnitDehomogenize_ne_zero_of_isWeightedHomogeneous
      (scaleSeparatedSimplePoleBoundaryTrace_isWeightedHomogeneous htopHom)
      (scaleSeparatedSimplePoleBoundaryTrace_ne_zero htop)
  rw [hsingle] at hcomponent
  exact htopTrace hcomponent

/-- For a nontrivial jet ceiling, the actual Gamma profile reflects the scale-separated
simple-pole bound.  The degree-zero source sector is harmless, while the Rees weight makes every
higher pole coefficient of the linear sector survive dehomogenization. -/
theorem finiteScaleSeparatedSimplePoleProfileEval_natDegree_le_one_of_gamma
    {n : ℕ} (hn : 1 ≤ n) (P : MvPolynomial (Fin (n + 1)) ℂ)
    (hprofile : (gammaScaleSeparatedSimplePoleProfileEval n P).natDegree ≤ 1) :
    (finiteScaleSeparatedSimplePoleProfileEval n P).natDegree ≤ 1 := by
  have hdegree := gammaScaleSeparatedSimplePoleProfileEval_totalDegree_le_one hn P hprofile
  let P₀ := MvPolynomial.homogeneousComponent 0 P
  let P₁ := MvPolynomial.homogeneousComponent 1 P
  have hdecomp : P₀ + P₁ = P := by
    have hsum := sum_homogeneousComponent_of_totalDegree_le (P := P) (N := 1) hdegree
    change MvPolynomial.homogeneousComponent 0 P +
      MvPolynomial.homogeneousComponent 1 P = P
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceAdd] using hsum
  have hP₀ : P₀.IsHomogeneous 0 :=
    MvPolynomial.homogeneousComponent_isHomogeneous 0 P
  have hP₁ : P₁.IsHomogeneous 1 :=
    MvPolynomial.homogeneousComponent_isHomogeneous 1 P
  have hscale₀ : (finiteScaleSeparatedSimplePoleProfileEval n P₀).natDegree ≤ 1 := by
    apply (finiteScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine P₀).2
    refine ⟨P₀.coeff 0, 0, ?_⟩
    rw [isHomogeneous_zero_eq_C_coeff_zero hP₀]
    simp
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro q hq
  have hgamma : (gammaScaleSeparatedSimplePoleProfileEval n P).coeff q = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hprofile hq)
  have hgamma₀Degree :
      (gammaScaleSeparatedSimplePoleProfileEval n P₀).natDegree ≤ 1 := by
    exact Polynomial.natDegree_map_le.trans hscale₀
  have hgamma₀ : (gammaScaleSeparatedSimplePoleProfileEval n P₀).coeff q = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hgamma₀Degree hq)
  have hgamma₁ : (gammaScaleSeparatedSimplePoleProfileEval n P₁).coeff q = 0 := by
    have hsum :
        (gammaScaleSeparatedSimplePoleProfileEval n P₀).coeff q +
          (gammaScaleSeparatedSimplePoleProfileEval n P₁).coeff q = 0 := by
      rw [← Polynomial.coeff_add, ← map_add, hdecomp, hgamma]
    rwa [hgamma₀, zero_add] at hsum
  have hdehom₁ : scaleSeparatedPoleUnitDehomogenize
      ((finiteScaleSeparatedSimplePoleProfileEval n P₁).coeff q) = 0 := by
    apply gammaPoleScaleAndUnitDerivativeEval_injective
    simpa [gammaScaleSeparatedSimplePoleProfileEval,
      gammaScaleSeparatedPoleBoundaryEval, Polynomial.coeff_map] using hgamma₁
  have hscale₁ : (finiteScaleSeparatedSimplePoleProfileEval n P₁).coeff q = 0 := by
    by_contra hne
    exact (scaleSeparatedPoleUnitDehomogenize_ne_zero_of_isWeightedHomogeneous
      (finiteScaleSeparatedSimplePoleProfileEval_coeff_isWeightedHomogeneous hP₁ q) hne) hdehom₁
  rw [← hdecomp, map_add, Polynomial.coeff_add,
    Polynomial.natDegree_le_iff_coeff_eq_zero.mp hscale₀ q hq, hscale₁, add_zero]

/-- **Actual Gamma affine horizon above jet order zero.**  At every nontrivial finite jet
ceiling, the factorially scaled Gamma pole model has degree at most one exactly for affine
polynomials in the undifferentiated carrier. -/
theorem gammaScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine_of_one_le
    {n : ℕ} (hn : 1 ≤ n) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (gammaScaleSeparatedSimplePoleProfileEval n P).natDegree ≤ 1 ↔
      ∃ a b : ℂ, P = MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0 := by
  constructor
  · intro h
    exact (finiteScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine P).1
      (finiteScaleSeparatedSimplePoleProfileEval_natDegree_le_one_of_gamma hn P h)
  · intro h
    have hscale :=
      (finiteScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine P).2 h
    exact Polynomial.natDegree_map_le.trans hscale

/-- At jet ceiling zero the actual Gamma profile is simply the canonical univariate polynomial,
with its complex coefficients embedded as constant germs. -/
theorem gammaScaleSeparatedSimplePoleProfileEval_zero_eq_map_uniqueAlgEquiv
    (P : MvPolynomial (Fin 1) ℂ) :
    gammaScaleSeparatedSimplePoleProfileEval 0 P =
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) P).map complexNatGerm := by
  let lhs : MvPolynomial (Fin 1) ℂ →+* Polynomial NatGerm :=
    gammaScaleSeparatedSimplePoleProfileEval 0
  let rhs : MvPolynomial (Fin 1) ℂ →+* Polynomial NatGerm :=
    (Polynomial.mapRingHom complexNatGerm).comp
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).toRingHom
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs, gammaScaleSeparatedSimplePoleProfileEval,
        finiteScaleSeparatedSimplePoleProfileEval,
        gammaScaleSeparatedPoleBoundaryEval,
        gammaPoleScaleAndUnitDerivativeEval, complexNatGerm]
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [lhs, rhs, gammaScaleSeparatedSimplePoleProfileEval,
        finiteScaleSeparatedSimplePoleProfileEval, scaleSeparatedSimplePoleJetProfile,
        universalSimplePoleJetProfile, universalSimplePoleRegularProfile,
        gammaScaleSeparatedPoleBoundaryEval, simplePoleBoundaryInclude,
        gammaPoleScaleAndUnitDerivativeEval,
        scaleSeparatedPoleUnitDehomogenize, natHeadDehomogenize,
        GaloisForLFunctions.optionHeadDehomogenize]
  exact RingHom.congr_fun h P

/-- At jet ceiling zero, the actual Gamma simple-pole bound already forces the source to be
affine in its unique coordinate. -/
theorem gammaScaleSeparatedSimplePoleProfileEval_zero_affine_of_natDegree_le_one
    (P : MvPolynomial (Fin 1) ℂ)
    (hprofile : (gammaScaleSeparatedSimplePoleProfileEval 0 P).natDegree ≤ 1) :
    ∃ a b : ℂ, P = MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0 := by
  have hinjective : Function.Injective complexNatGerm :=
    ratNatEval_injective.comp RatFunc.C_injective
  have hdegree : (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) P).natDegree ≤ 1 := by
    rw [gammaScaleSeparatedSimplePoleProfileEval_zero_eq_map_uniqueAlgEquiv,
      Polynomial.natDegree_map_eq_of_injective hinjective] at hprofile
    exact hprofile
  obtain ⟨b, a, hP⟩ :=
    Polynomial.exists_eq_X_add_C_of_natDegree_le_one hdegree
  refine ⟨a, b, ?_⟩
  apply (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).injective
  rw [hP]
  simp
  ring

/-- **Actual Gamma affine horizon.**  At every finite jet ceiling, the factorially scaled Gamma
pole model has degree at most one exactly for affine polynomials in the undifferentiated carrier.
Thus the actual analytic value specialization reflects, rather than merely preserves, the full
universal affine horizon. -/
theorem gammaScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (gammaScaleSeparatedSimplePoleProfileEval n P).natDegree ≤ 1 ↔
      ∃ a b : ℂ, P = MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0 := by
  constructor
  · intro h
    rcases n with (_ | n)
    · exact gammaScaleSeparatedSimplePoleProfileEval_zero_affine_of_natDegree_le_one P h
    · exact (gammaScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine_of_one_le
        (n := n + 1) (by omega) P).1 h
  · intro h
    have hscale :=
      (finiteScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine P).2 h
    exact Polynomial.natDegree_map_le.trans hscale

end

end GaloisForLFunctions.HTGeometry
