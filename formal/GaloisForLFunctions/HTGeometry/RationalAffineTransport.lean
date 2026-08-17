import GaloisForLFunctions.HTGeometry.RationalAffineConnection

/-!
# Affine transport equations for a polynomial map

Every step of the orbifold descent produces a functional equation of the single shape

`a(R(z)) · R'(z)^k = b(z) · a(z) + c(z)`

with `b, c` rational: the invariance of a `k`-differential is the case `c = 0` and `b` constant, the
rational affine connection is `k = 2`, `b = R'`, `c = −R''`, and the coefficient equations of a
normalizing shift at any jet level are the cases `b = 1`.

This module proves the transport law of that shape once and for all.  Away from the critical set,
and at points where `b` is a unit and `c` is regular, the equation says that the order of `a` at `p`
and its order at `R(p)` have the same sign, so a pole travels along the map in both directions; a
pole sitting on an injective critical-free orbit along which `b` stays a unit and `c` stays regular
is therefore impossible, because a nonzero rational function has only finitely many zeros and poles.

At a critical point the substitution ramifies, and the equation bounds the order of the left side by
the order of `c` whenever `a` is more regular than `c` there.  That inequality is what forces the
pole in the first place.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {R : K[X]}

/-- **The affine transport equation** `a(R)·(R')^k = b·a + c`. -/
def IsAffineTransport (R : K[X])
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c)
    (k : ℤ) (b c a : RatFunc K) : Prop :=
  ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a
      * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k
    = b * a + c

omit [CharZero K] in
theorem ratOrder_zero (p : K) : ratOrder (0 : RatFunc K) p = 0 := by
  rw [ratOrder, RatFunc.num_zero, RatFunc.denom_zero, rootMultiplicity_zero,
    rootMultiplicity_eq_zero (by simp : ¬ (1 : K[X]).IsRoot p)]
  norm_num

omit [CharZero K] in
theorem isAffineTransport_def
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (h : IsAffineTransport R hR k b c a) :
    ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a
        * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k
      = b * a + c := h

variable (hRdeg : R.natDegree ≠ 0)

include hRdeg in
/-- **The order of the left-hand side.**  The substitution ramifies to the local multiplicity of the
map and the power of the derivative contributes its own multiplicity. -/
theorem ratOrder_affineTransport_lhs
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c)
    {a : RatFunc K} (ha : a ≠ 0) (k : ℤ) (p : K) :
    ratOrder (ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a
        * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k) p
      = ratOrder a (R.eval p) * (rootMultiplicity p (R - Polynomial.C (R.eval p)) : ℤ)
        + k * (rootMultiplicity p (derivative R) : ℤ) := by
  have hRd := derivative_ne_zero_of_natDegree_ne_zero hRdeg
  have hAd : algebraMap K[X] (RatFunc K) (derivative R) ≠ 0 := algebraMap_ne_zero_of_ne_zero hRd
  rw [ratOrder_mul (substitution_ne_zero ha) (zpow_ne_zero k hAd), ratOrder_zpow hAd,
    ratOrder_algebraMap, ratOrder_ratFuncSubstitution hRdeg hR ha p]

include hRdeg in
/-- Away from the critical set the left-hand side has the order of `a` at the image point. -/
theorem ratOrder_affineTransport_lhs_of_deriv_ne_zero
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c)
    {a : RatFunc K} (ha : a ≠ 0) (k : ℤ) {p : K} (hp : (derivative R).eval p ≠ 0) :
    ratOrder (ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a
        * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k) p
      = ratOrder a (R.eval p) := by
  have hmult : rootMultiplicity p (derivative R) = 0 := rootMultiplicity_eq_zero (by exact hp)
  have hram : rootMultiplicity p (R - Polynomial.C (R.eval p)) = 1 := by
    refine rootMultiplicity_eq_one (sub_C_eval_ne_zero hRdeg p) (by simp) ?_
    rwa [derivative_sub, derivative_C, sub_zero]
  rw [ratOrder_affineTransport_lhs hRdeg hR ha k p, hmult, hram]
  norm_num

/-! ## Transport of poles -/

include hRdeg in
/-- **A pole travels forward.**  At a point off the critical set where `b` is a unit and `c` is
regular, a pole of `a` forces a pole at the image. -/
theorem affineTransport_pole_forward
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsAffineTransport R hR k b c a) {p : K} (hp : (derivative R).eval p ≠ 0)
    (hbp : ratOrder b p = 0) (hcp : 0 ≤ ratOrder c p) (hpole : ratOrder a p < 0) :
    ratOrder a (R.eval p) < 0 := by
  have hlhs := ratOrder_affineTransport_lhs_of_deriv_ne_zero hRdeg hR ha k hp
  rw [isAffineTransport_def heq] at hlhs
  have hba : ratOrder (b * a) p = ratOrder a p := by
    rw [ratOrder_mul hb ha, hbp, zero_add]
  have hsum : b * a + c ≠ 0 := by
    rw [← isAffineTransport_def heq]
    exact mul_ne_zero (substitution_ne_zero ha)
      (zpow_ne_zero k (algebraMap_ne_zero_of_ne_zero
        (derivative_ne_zero_of_natDegree_ne_zero hRdeg)))
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [add_zero, hba] at hlhs
    omega
  · have hsplit : b * a = (b * a + c) + -c := by ring
    have hmin := min_le_ratOrder_add hsum (neg_ne_zero.mpr hc0)
      (by rw [← hsplit]; exact mul_ne_zero hb ha) p
    rw [← hsplit, hba, ratOrder_neg hc0] at hmin
    omega

include hRdeg in
/-- **A pole travels backward.**  At a point off the critical set where `b` is a unit and `c` is
regular, every preimage of a pole is a pole. -/
theorem affineTransport_pole_backward
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsAffineTransport R hR k b c a) {p : K} (hp : (derivative R).eval p ≠ 0)
    (hbp : ratOrder b p = 0) (hcp : 0 ≤ ratOrder c p)
    (hpole : ratOrder a (R.eval p) < 0) : ratOrder a p < 0 := by
  by_contra hreg
  rw [not_lt] at hreg
  have hlhs := ratOrder_affineTransport_lhs_of_deriv_ne_zero hRdeg hR ha k hp
  rw [isAffineTransport_def heq] at hlhs
  have hba : ratOrder (b * a) p = ratOrder a p := by
    rw [ratOrder_mul hb ha, hbp, zero_add]
  have hsum : b * a + c ≠ 0 := by
    rw [← isAffineTransport_def heq]
    exact mul_ne_zero (substitution_ne_zero ha)
      (zpow_ne_zero k (algebraMap_ne_zero_of_ne_zero
        (derivative_ne_zero_of_natDegree_ne_zero hRdeg)))
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [add_zero, hba] at hlhs
    omega
  · have hmin := min_le_ratOrder_add (mul_ne_zero hb ha) hc0 hsum p
    rw [hba] at hmin
    omega

/-! ## Infinitely many poles -/

include hRdeg in
/-- **A pole on an injective critical-free backward orbit is impossible.** -/
theorem no_pole_of_backward_orbit_affineTransport
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsAffineTransport R hR k b c a) {q : ℕ → K} (hstep : ∀ n, R.eval (q (n + 1)) = q n)
    (hcrit : ∀ n, (derivative R).eval (q (n + 1)) ≠ 0)
    (hbq : ∀ n, ratOrder b (q (n + 1)) = 0) (hcq : ∀ n, 0 ≤ ratOrder c (q (n + 1)))
    (hinj : Function.Injective q) (hpole : ratOrder a (q 0) < 0) : False := by
  have horbit : ∀ n : ℕ, ratOrder a (q n) < 0 := by
    intro n
    induction n with
    | zero => exact hpole
    | succ n ih =>
        exact affineTransport_pole_backward hRdeg ha hb heq (hcrit n) (hbq n) (hcq n)
          (by rw [hstep n]; exact ih)
  have hsub : Set.range q ⊆ {z : K | ratOrder a z ≠ 0} := by
    rintro _ ⟨n, rfl⟩
    exact ne_of_lt (horbit n)
  exact (Set.infinite_range_of_injective hinj) ((finite_support_ratOrder ha).subset hsub)

include hRdeg in
/-- **A pole on an injective critical-free forward orbit is impossible.** -/
theorem no_pole_of_forward_orbit_affineTransport
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsAffineTransport R hR k b c a) {f : ℕ → K} (hstep : ∀ n, f (n + 1) = R.eval (f n))
    (hcrit : ∀ n, (derivative R).eval (f n) ≠ 0)
    (hbf : ∀ n, ratOrder b (f n) = 0) (hcf : ∀ n, 0 ≤ ratOrder c (f n))
    (hinj : Function.Injective f) (hpole : ratOrder a (f 0) < 0) : False := by
  have horbit : ∀ n : ℕ, ratOrder a (f n) < 0 := by
    intro n
    induction n with
    | zero => exact hpole
    | succ n ih =>
        have := affineTransport_pole_forward hRdeg ha hb heq (hcrit n) (hbf n) (hcf n) ih
        rwa [← hstep n] at this
  have hsub : Set.range f ⊆ {z : K | ratOrder a z ≠ 0} := by
    rintro _ ⟨n, rfl⟩
    exact ne_of_lt (horbit n)
  exact (Set.infinite_range_of_injective hinj) ((finite_support_ratOrder ha).subset hsub)

/-! ## The obstruction at a critical point -/

include hRdeg in
/-- **The critical inequality.**  Where `a` is strictly more regular than `c`, the order of the left
side at a critical point cannot exceed the order of `c` there. -/
theorem ratOrder_le_of_critical
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0) (hc0 : c ≠ 0)
    (heq : IsAffineTransport R hR k b c a) {p : K}
    (hreg : ratOrder c p < ratOrder b p + ratOrder a p) :
    ratOrder a (R.eval p) * (rootMultiplicity p (R - Polynomial.C (R.eval p)) : ℤ)
        + k * (rootMultiplicity p (derivative R) : ℤ) ≤ ratOrder c p := by
  have hlhs := ratOrder_affineTransport_lhs hRdeg hR ha k p
  rw [isAffineTransport_def heq] at hlhs
  have hba : ratOrder (b * a) p = ratOrder b p + ratOrder a p := ratOrder_mul hb ha p
  have hsum : b * a + c ≠ 0 := by
    rw [← isAffineTransport_def heq]
    exact mul_ne_zero (substitution_ne_zero ha)
      (zpow_ne_zero k (algebraMap_ne_zero_of_ne_zero
        (derivative_ne_zero_of_natDegree_ne_zero hRdeg)))
  have hsplit : c = (b * a + c) + -(b * a) := by ring
  have hmin := min_le_ratOrder_add hsum (neg_ne_zero.mpr (mul_ne_zero hb ha))
    (by rw [← hsplit]; exact hc0) p
  rw [← hsplit, ratOrder_neg (mul_ne_zero hb ha), hba] at hmin
  omega

/-! ## The rational affine connection as an affine transport -/

omit [CharZero K] in
/-- The affine-connection equation is the affine transport with `k = 2`, `b = R'`, `c = −R''`. -/
theorem isAffineTransport_of_isAffineConnection
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K}
    (h : IsAffineConnection R hR a) :
    IsAffineTransport R hR 2 (algebraMap K[X] (RatFunc K) (derivative R))
      (-(algebraMap K[X] (RatFunc K) (derivative (derivative R)))) a := by
  have hd := isAffineConnection_def h
  have hpow : ((algebraMap K[X] (RatFunc K) (derivative R)) ^ (2 : ℤ))
      = algebraMap K[X] (RatFunc K) (derivative R ^ 2) := by
    rw [map_pow, ← zpow_natCast]
    norm_num
  rw [IsAffineTransport, hpow, ← sub_eq_add_neg, ← hd]
  ring

theorem ratOrder_curvature_nonneg (p : K) :
    0 ≤ ratOrder (-(algebraMap K[X] (RatFunc K) (derivative (derivative R)))) p := by
  rcases eq_or_ne (derivative (derivative R)) 0 with hz | hz
  · rw [hz, map_zero, neg_zero, ratOrder_zero]
  · rw [ratOrder_neg (algebraMap_ne_zero_of_ne_zero hz)]
    exact ratOrder_algebraMap_nonneg _ p

include hRdeg in
/-- **A pole of an affine connection travels forward.** -/
theorem affine_pole_forward
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K} (ha : a ≠ 0)
    (heq : IsAffineConnection R hR a) {p : K} (hp : (derivative R).eval p ≠ 0)
    (hpole : ratOrder a p < 0) : ratOrder a (R.eval p) < 0 := by
  refine affineTransport_pole_forward hRdeg ha
    (algebraMap_ne_zero_of_ne_zero (derivative_ne_zero_of_natDegree_ne_zero hRdeg))
    (isAffineTransport_of_isAffineConnection heq) hp ?_ (ratOrder_curvature_nonneg p) hpole
  rw [ratOrder_algebraMap, rootMultiplicity_eq_zero (by exact hp), Nat.cast_zero]

include hRdeg in
/-- **A pole of an affine connection travels backward.** -/
theorem affine_pole_backward
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K} (ha : a ≠ 0)
    (heq : IsAffineConnection R hR a) {p : K} (hp : (derivative R).eval p ≠ 0)
    (hpole : ratOrder a (R.eval p) < 0) : ratOrder a p < 0 := by
  refine affineTransport_pole_backward hRdeg ha
    (algebraMap_ne_zero_of_ne_zero (derivative_ne_zero_of_natDegree_ne_zero hRdeg))
    (isAffineTransport_of_isAffineConnection heq) hp ?_ (ratOrder_curvature_nonneg p) hpole
  rw [ratOrder_algebraMap, rootMultiplicity_eq_zero (by exact hp), Nat.cast_zero]

include hRdeg in
/-- **A pole of an affine connection on an injective critical-free backward orbit is
impossible.** -/
theorem no_pole_of_backward_orbit
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K} (ha : a ≠ 0)
    (heq : IsAffineConnection R hR a) {q : ℕ → K} (hstep : ∀ n, R.eval (q (n + 1)) = q n)
    (hcrit : ∀ n, (derivative R).eval (q (n + 1)) ≠ 0) (hinj : Function.Injective q)
    (hpole : ratOrder a (q 0) < 0) : False := by
  refine no_pole_of_backward_orbit_affineTransport hRdeg ha
    (algebraMap_ne_zero_of_ne_zero (derivative_ne_zero_of_natDegree_ne_zero hRdeg))
    (isAffineTransport_of_isAffineConnection heq) hstep hcrit (fun n => ?_)
    (fun n => ratOrder_curvature_nonneg _) hinj hpole
  rw [ratOrder_algebraMap, rootMultiplicity_eq_zero (by exact hcrit n), Nat.cast_zero]

include hRdeg in
/-- **A pole of an affine connection on an injective critical-free forward orbit is impossible.** -/
theorem no_pole_of_forward_orbit
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c} {a : RatFunc K} (ha : a ≠ 0)
    (heq : IsAffineConnection R hR a) {f : ℕ → K} (hstep : ∀ n, f (n + 1) = R.eval (f n))
    (hcrit : ∀ n, (derivative R).eval (f n) ≠ 0) (hinj : Function.Injective f)
    (hpole : ratOrder a (f 0) < 0) : False := by
  refine no_pole_of_forward_orbit_affineTransport hRdeg ha
    (algebraMap_ne_zero_of_ne_zero (derivative_ne_zero_of_natDegree_ne_zero hRdeg))
    (isAffineTransport_of_isAffineConnection heq) hstep hcrit (fun n => ?_)
    (fun n => ratOrder_curvature_nonneg _) hinj hpole
  rw [ratOrder_algebraMap, rootMultiplicity_eq_zero (by exact hcrit n), Nat.cast_zero]

end

end GaloisForLFunctions.HTGeometry
