import GaloisForLFunctions.HTGeometry.RationalOrderValuation
import GaloisForLFunctions.HTGeometry.RationalBackwardOrbit

/-!
# Rational affine connections of a polynomial map

An affine structure invariant under a map `R` is recorded by its connection coefficient
`a = ζ''/ζ'`, and invariance of the structure is the equation

`a(R(z)) · R'(z)² = R'(z) · a(z) − R''(z)`.

This is the obstruction that a normalizing shift of the orbifold descent at jet order two must
solve, and here it is analysed by the signed order of a rational function.

Two mechanisms drive the analysis, and both are order computations on the equation read at a point.
Away from the critical set the substitution neither ramifies nor contributes, so the equation says
that the order of `a` at `c` and its order at `R(c)` have the same sign: a pole travels forward and
backward along the map.  At a critical point of multiplicity `m` the substitution ramifies to order
`m + 1` and the square of the derivative contributes `2m`, while the curvature term `R''` vanishes
to order exactly `m − 1`; the deficit of one is irreconcilable, so `a` must have a pole either at
the critical point or at its image.

Together: a critical point whose critical value has an infinite forward orbit, or whose preimages
carry an infinite critical-free backward orbit, forbids any rational affine connection, because a
nonzero rational function has only finitely many zeros and poles.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- **The rational affine-connection equation** `a(R)·(R')² = R'·a − R''` of a polynomial map. -/
def IsAffineConnection (R : K[X])
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c) (a : RatFunc K) : Prop :=
  algebraMap K[X] (RatFunc K) (derivative R ^ (2 : ℕ))
      * ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a
    = algebraMap K[X] (RatFunc K) (derivative R) * a
      - algebraMap K[X] (RatFunc K) (derivative (derivative R))

omit [CharZero K] in
theorem isAffineConnection_def {R : K[X]}
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K}
    (h : IsAffineConnection R hR a) :
    algebraMap K[X] (RatFunc K) (derivative R ^ (2 : ℕ))
        * ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a
      = algebraMap K[X] (RatFunc K) (derivative R) * a
        - algebraMap K[X] (RatFunc K) (derivative (derivative R)) := h

/-! ## Basic nonvanishing -/

variable {R : K[X]} (hRdeg : R.natDegree ≠ 0)

include hRdeg in
theorem derivative_ne_zero_of_natDegree_ne_zero : derivative R ≠ 0 :=
  fun h => hRdeg (Polynomial.derivative_eq_zero.mp h)

omit [CharZero K] in
include hRdeg in
theorem sub_C_eval_ne_zero (c : K) : R - Polynomial.C (R.eval c) ≠ 0 := by
  intro h
  refine hRdeg ?_
  have : R = Polynomial.C (R.eval c) := by
    rwa [sub_eq_zero] at h
  rw [this, natDegree_C]

omit [CharZero K] in
theorem substitution_ne_zero
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K} (ha : a ≠ 0) :
    ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a ≠ 0 := by
  intro h
  refine ha ?_
  have hinj := (ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR).injective
    (a₁ := a) (a₂ := 0)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_zero] at hinj
  exact hinj h

theorem ratOrder_neg {f : RatFunc K} (hf : f ≠ 0) (c : K) : ratOrder (-f) c = ratOrder f c := by
  have hneg : (-f) = RatFunc.C (-1 : K) * f := by rw [map_neg, map_one, neg_one_mul]
  rw [hneg, ratOrder_mul (by simp : (RatFunc.C (-1 : K)) ≠ 0) hf, ratOrder_C, zero_add]

omit [CharZero K] in
/-- The order of a polynomial is never negative. -/
theorem ratOrder_algebraMap_nonneg (p : K[X]) (c : K) :
    0 ≤ ratOrder (algebraMap K[X] (RatFunc K) p) c := by
  rw [ratOrder_algebraMap]
  exact Int.natCast_nonneg _

/-! ## The two sides of the equation -/

/-- The right-hand side of the affine-connection equation, written as a sum. -/
def affineSide (R : K[X]) (a : RatFunc K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (derivative R) * a
    + -algebraMap K[X] (RatFunc K) (derivative (derivative R))

omit [CharZero K] in
theorem affineSide_eq_lhs
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K}
    (heq : IsAffineConnection R hR a) :
    affineSide R a = algebraMap K[X] (RatFunc K) (derivative R ^ (2 : ℕ))
      * ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a := by
  rw [affineSide, isAffineConnection_def heq]
  ring

include hRdeg in
theorem affineSide_ne_zero
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K} (ha : a ≠ 0)
    (heq : IsAffineConnection R hR a) : affineSide R a ≠ 0 := by
  rw [affineSide_eq_lhs heq]
  exact mul_ne_zero
    (algebraMap_ne_zero_of_ne_zero (pow_ne_zero 2 (derivative_ne_zero_of_natDegree_ne_zero hRdeg)))
    (substitution_ne_zero ha)

include hRdeg in
/-- **The order of the equation at a point.**  The substitution ramifies to the multiplicity of the
map, and the square of the derivative contributes twice its multiplicity. -/
theorem ratOrder_affineSide
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K} (ha : a ≠ 0)
    (heq : IsAffineConnection R hR a) (c : K) :
    ratOrder (affineSide R a) c
      = ratOrder a (R.eval c) * (rootMultiplicity c (R - Polynomial.C (R.eval c)) : ℤ)
        + 2 * (rootMultiplicity c (derivative R) : ℤ) := by
  have hRd := derivative_ne_zero_of_natDegree_ne_zero hRdeg
  have hAsq : algebraMap K[X] (RatFunc K) (derivative R ^ (2 : ℕ)) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (pow_ne_zero 2 hRd)
  rw [affineSide_eq_lhs heq, ratOrder_mul hAsq (substitution_ne_zero ha), ratOrder_algebraMap,
    rootMultiplicity_pow hRd 2 c, ratOrder_ratFuncSubstitution hRdeg hR ha c]
  push_cast
  ring

/-! ## The order of the two sides away from the critical set -/

include hRdeg in
theorem ratOrder_affineSide_of_deriv_ne_zero
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K} (ha : a ≠ 0)
    (heq : IsAffineConnection R hR a) {c : K} (hc : (derivative R).eval c ≠ 0) :
    ratOrder (affineSide R a) c = ratOrder a (R.eval c) := by
  have hmult : rootMultiplicity c (derivative R) = 0 :=
    rootMultiplicity_eq_zero (by exact hc)
  have hram : rootMultiplicity c (R - Polynomial.C (R.eval c)) = 1 := by
    refine rootMultiplicity_eq_one (sub_C_eval_ne_zero hRdeg c) (by simp) ?_
    rwa [derivative_sub, derivative_C, sub_zero]
  rw [ratOrder_affineSide hRdeg ha heq c, hmult, hram]
  norm_num

/-! ## The obstruction at a critical point -/

include hRdeg in
/-- At a critical point the derivative of the map vanishes to a positive order. -/
theorem rootMultiplicity_derivative_pos {c : K} (hcrit : (derivative R).eval c = 0) :
    0 < rootMultiplicity c (derivative R) :=
  (rootMultiplicity_pos (derivative_ne_zero_of_natDegree_ne_zero hRdeg)).mpr hcrit

include hRdeg in
/-- At a critical point the second derivative is nonzero: a nonzero constant has no root. -/
theorem derivative_derivative_ne_zero_of_crit {c : K} (hcrit : (derivative R).eval c = 0) :
    derivative (derivative R) ≠ 0 := by
  have hRd := derivative_ne_zero_of_natDegree_ne_zero hRdeg
  intro h
  have hdeg0 : (derivative R).natDegree = 0 := Polynomial.derivative_eq_zero.mp h
  refine hRd ?_
  have hC : derivative R = Polynomial.C ((derivative R).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdeg0
  rw [hC] at hcrit ⊢
  rw [eval_C] at hcrit
  rw [hcrit, map_zero]

include hRdeg in
/-- **The ramification of the map at a critical point.**  The map takes its critical value to one
order more than the vanishing order of its derivative. -/
theorem rootMultiplicity_sub_C_eval_eq {c : K} :
    rootMultiplicity c (R - Polynomial.C (R.eval c)) = rootMultiplicity c (derivative R) + 1 := by
  have hp0 : R - Polynomial.C (R.eval c) ≠ 0 := sub_C_eval_ne_zero hRdeg c
  have hproot : (R - Polynomial.C (R.eval c)).IsRoot c := by simp
  have hpos : 0 < rootMultiplicity c (R - Polynomial.C (R.eval c)) :=
    (rootMultiplicity_pos hp0).mpr hproot
  have hstep := Polynomial.derivative_rootMultiplicity_of_root hproot
  rw [derivative_sub, derivative_C, sub_zero] at hstep
  omega

include hRdeg in
/-- **The critical obstruction.**  A rational affine connection cannot be regular both at a critical
point and at its image: the substitution ramifies one order more than the curvature term vanishes. -/
theorem no_affine_connection_regular_at_critical
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K} (ha : a ≠ 0)
    (heq : IsAffineConnection R hR a) {c : K} (hcrit : (derivative R).eval c = 0)
    (h0 : 0 ≤ ratOrder a c) (h1 : 0 ≤ ratOrder a (R.eval c)) : False := by
  have hRd := derivative_ne_zero_of_natDegree_ne_zero hRdeg
  have hAd : algebraMap K[X] (RatFunc K) (derivative R) ≠ 0 := algebraMap_ne_zero_of_ne_zero hRd
  have hdd := derivative_derivative_ne_zero_of_crit hRdeg hcrit
  have hAdd : algebraMap K[X] (RatFunc K) (derivative (derivative R)) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero hdd
  have hm : 0 < rootMultiplicity c (derivative R) := rootMultiplicity_derivative_pos hRdeg hcrit
  have hram : rootMultiplicity c (R - Polynomial.C (R.eval c))
      = rootMultiplicity c (derivative R) + 1 := rootMultiplicity_sub_C_eval_eq hRdeg
  have hcurv : rootMultiplicity c (derivative (derivative R))
      = rootMultiplicity c (derivative R) - 1 :=
    Polynomial.derivative_rootMultiplicity_of_root (by exact hcrit)
  set u : RatFunc K := algebraMap K[X] (RatFunc K) (derivative R) * a with hu
  set v : RatFunc K := -algebraMap K[X] (RatFunc K) (derivative (derivative R)) with hv
  have hu0 : u ≠ 0 := mul_ne_zero hAd ha
  have hv0 : v ≠ 0 := by rw [hv]; exact neg_ne_zero.mpr hAdd
  have hordu : ratOrder u c = (rootMultiplicity c (derivative R) : ℤ) + ratOrder a c := by
    rw [hu, ratOrder_mul hAd ha, ratOrder_algebraMap]
  have hordv : ratOrder v c = ((rootMultiplicity c (derivative R) - 1 : ℕ) : ℤ) := by
    rw [hv, ratOrder_neg hAdd, ratOrder_algebraMap, hcurv]
  have hside := ratOrder_affineSide hRdeg ha heq c
  rw [hram] at hside
  have hsidege : 2 * (rootMultiplicity c (derivative R) : ℤ) ≤ ratOrder (affineSide R a) c := by
    rw [hside]
    have : 0 ≤ ratOrder a (R.eval c) * ((rootMultiplicity c (derivative R) + 1 : ℕ) : ℤ) :=
      mul_nonneg h1 (Int.natCast_nonneg _)
    linarith
  have hsumne : affineSide R a ≠ 0 := affineSide_ne_zero hRdeg ha heq
  have hvsum : v = affineSide R a + -u := by rw [affineSide, ← hu, ← hv]; ring
  have hmin := min_le_ratOrder_add hsumne (neg_ne_zero.mpr hu0) (by rw [← hvsum]; exact hv0) c
  rw [← hvsum, hordv, ratOrder_neg hu0, hordu] at hmin
  omega

omit [CharZero K] in
/-- The zero function is an affine connection only for a map with vanishing curvature term. -/
theorem derivative_derivative_eq_zero_of_isAffineConnection_zero
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    (h : IsAffineConnection R hR 0) : derivative (derivative R) = 0 := by
  have heq' := isAffineConnection_def h
  rw [map_zero, mul_zero, mul_zero, zero_sub, eq_comm, neg_eq_zero] at heq'
  exact (RatFunc.algebraMap_injective K) (by rw [heq', map_zero])

end

end GaloisForLFunctions.HTGeometry
