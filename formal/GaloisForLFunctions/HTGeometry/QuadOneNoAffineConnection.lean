import GaloisForLFunctions.HTGeometry.RationalOrderValuation
import GaloisForLFunctions.HTGeometry.RationalBackwardOrbit
import GaloisForLFunctions.HTGeometry.QuadraticNoInvariantDifferential

/-!
# The rational affine connection of `z ↦ z² + 1`

A normalizing shift of the orbifold descent at jet level two exists exactly when the *rational
affine connection* equation

`a(R(z)) · R'(z)² = R'(z) · a(z) − R''(z)`

has a rational solution.  For `R(z) = z² + 1` it reads `4z²·a(z²+1) = 2z·a(z) − 2`.

Here the equation is set up and its first obstruction is proved: a solution regular at both `0` and
at the critical value `1` is impossible.  The left side has order at least two at the origin,
because the substitution doubles the order at the critical value; the right side has order at most
zero there, because its constant term is nonzero while its other term has positive order.  Both are
order computations, the multiplicative one through `ratOrder_ratFuncSubstitution` and the additive
one through `min_le_ratOrder_add`.

The same two order computations, run at a point away from the critical point, transport a pole of a
solution both forward and backward along the map; that is the content of
`QuadOneAffineConnectionPoles`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- `z ↦ z² + 1` is not a constant. -/
theorem quadOne_not_isConst :
    ¬ ∃ c : ℂ, (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne) = RatFunc.C c :=
  not_isConst_algebraMap (by rw [natDegree_quadOne]; norm_num)

/-- The rational affine-connection equation `4z²·a(z²+1) = 2z·a(z) − 2` of `z ↦ z² + 1`. -/
def IsQuadOneAffineConnection (a : RatFunc ℂ) : Prop :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 4 * Polynomial.X ^ 2)
      * ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
          quadOne_not_isConst a
    = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) * a
      - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2)

theorem isQuadOneAffineConnection_def {a : RatFunc ℂ} (h : IsQuadOneAffineConnection a) :
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 4 * Polynomial.X ^ 2)
        * ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
            quadOne_not_isConst a
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) * a
        - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) := h

/-! ## Elementary nonvanishing -/

theorem quadOneLead_ne_zero : (Polynomial.C 4 * Polynomial.X ^ 2 : Polynomial ℂ) ≠ 0 := by
  intro h
  have hc := congrArg (fun p => Polynomial.coeff p 2) h
  simp at hc

theorem quadOneSlope_ne_zero : (Polynomial.C 2 * Polynomial.X : Polynomial ℂ) ≠ 0 := by
  intro h
  have hc := congrArg (fun p => Polynomial.coeff p 1) h
  simp at hc

theorem quadOneCurv_ne_zero : (Polynomial.C 2 : Polynomial ℂ) ≠ 0 := by
  intro h
  have hc := congrArg (fun p => Polynomial.coeff p 0) h
  simp at hc

/-- Substitution along `z ↦ z² + 1` preserves nonvanishing. -/
theorem quadOneSubst_ne_zero {a : RatFunc ℂ} (ha : a ≠ 0) :
    ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
      quadOne_not_isConst a ≠ 0 := by
  intro h
  refine ha ?_
  have hinj := (ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
    quadOne_not_isConst).injective (a₁ := a) (a₂ := 0)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_zero] at hinj
  exact hinj h

theorem ratOrder_neg {K : Type*} [Field K] {f : RatFunc K} (hf : f ≠ 0) (c : K) :
    ratOrder (-f) c = ratOrder f c := by
  have hneg : (-f) = RatFunc.C (-1 : K) * f := by
    rw [map_neg, map_one, neg_one_mul]
  rw [hneg, ratOrder_mul (by simp : (RatFunc.C (-1 : K)) ≠ 0) hf, ratOrder_C, zero_add]

/-! ## The obstruction at the critical orbit -/

theorem rootMultiplicity_quadOneLead_zero :
    rootMultiplicity (0 : ℂ) (Polynomial.C 4 * Polynomial.X ^ 2) = 2 := by
  rw [rootMultiplicity_mul quadOneLead_ne_zero,
    rootMultiplicity_eq_zero (by simp : ¬ (Polynomial.C (4 : ℂ)).IsRoot 0), zero_add,
    rootMultiplicity_pow Polynomial.X_ne_zero 2 0,
    show (Polynomial.X : Polynomial ℂ) = Polynomial.X - Polynomial.C 0 from by
      rw [map_zero, sub_zero],
    rootMultiplicity_X_sub_C_self]

theorem rootMultiplicity_quadOneSlope_zero :
    rootMultiplicity (0 : ℂ) (Polynomial.C 2 * Polynomial.X) = 1 := by
  rw [rootMultiplicity_mul quadOneSlope_ne_zero,
    rootMultiplicity_eq_zero (by simp : ¬ (Polynomial.C (2 : ℂ)).IsRoot 0), zero_add,
    show (Polynomial.X : Polynomial ℂ) = Polynomial.X - Polynomial.C 0 from by
      rw [map_zero, sub_zero],
    rootMultiplicity_X_sub_C_self]

/-- **No rational affine connection regular at the critical orbit.** -/
theorem quadOne_no_affine_connection_regular {a : RatFunc ℂ} (ha : a ≠ 0)
    (h0 : 0 ≤ ratOrder a 0) (h1 : 0 ≤ ratOrder a 1)
    (heq : IsQuadOneAffineConnection a) : False := by
  classical
  have heq' := isQuadOneAffineConnection_def heq
  have hdeg : quadOne.natDegree ≠ 0 := by rw [natDegree_quadOne]; norm_num
  have hA4 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 4 * Polynomial.X ^ 2) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero quadOneLead_ne_zero
  have hA2X : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero quadOneSlope_ne_zero
  have hA2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero quadOneCurv_ne_zero
  have hsub0 := quadOneSubst_ne_zero ha
  -- the left-hand side has order at least two at the origin
  have hLHS : ratOrder (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 4 * Polynomial.X ^ 2)
      * ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
        quadOne_not_isConst a) 0 = 2 + ratOrder a 1 * 2 := by
    have hval : quadOne.eval (0 : ℂ) = 1 := by rw [quadOne_eval]; ring
    rw [ratOrder_mul hA4 hsub0, ratOrder_algebraMap, rootMultiplicity_quadOneLead_zero,
      ratOrder_ratFuncSubstitution hdeg quadOne_not_isConst ha 0, rootMultiplicity_quadOne_crit,
      hval]
    norm_num
  -- the right-hand side has order at most zero at the origin
  set u : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) * a
    with hu
  set v : RatFunc ℂ := -algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) with hv
  have hu0 : u ≠ 0 := mul_ne_zero hA2X ha
  have hv0 : v ≠ 0 := by rw [hv]; exact neg_ne_zero.mpr hA2
  have hordu : ratOrder u 0 = 1 + ratOrder a 0 := by
    rw [hu, ratOrder_mul hA2X ha, ratOrder_algebraMap, rootMultiplicity_quadOneSlope_zero]
    norm_num
  have hordv : ratOrder v 0 = 0 := by
    rw [hv, ratOrder_neg hA2, ratOrder_algebraMap,
      rootMultiplicity_eq_zero (by simp : ¬ (Polynomial.C (2 : ℂ)).IsRoot 0)]
    norm_num
  have hsum : u + v = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 4 * Polynomial.X ^ 2)
      * ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
        quadOne_not_isConst a := by
    rw [heq', hu, hv]; ring
  have hsumne : u + v ≠ 0 := by rw [hsum]; exact mul_ne_zero hA4 hsub0
  have hvsum : v = (u + v) + (-u) := by ring
  have hmin := min_le_ratOrder_add hsumne (neg_ne_zero.mpr hu0) (by rw [← hvsum]; exact hv0) 0
  rw [← hvsum, hordv, ratOrder_neg hu0, hordu] at hmin
  have hordsum : ratOrder (u + v) 0 = 2 + ratOrder a 1 * 2 := by rw [hsum]; exact hLHS
  rw [hordsum] at hmin
  omega

end GaloisForLFunctions.HTGeometry
