import GaloisForLFunctions.HTGeometry.PlaceUnivFactor

/-!
# Differentiating drops one degree at a place above infinity

In the coordinate model the peel rests on `TopDegLE.fpderiv_top`: differentiating in the newest
coordinate lowers the degree at infinity by one.  At a place of an algebraic extension the same
statement is a valuation inequality, and it holds for the same reason — a rational function of a
large element has its exact valuation read off the degrees, and the Wronskian numerator
`p'q − pq'` is one degree below the product `pq`.

The hypotheses are the ones the model supplies: the coefficients lie in a subfield on which the
place is trivial, the derivation kills that subfield, and the coordinate is differentiated to
something of unit size.

* `derivation_eval_of_coeff` — the chain rule for a polynomial the derivation does not move;
* `placeDegLE_eval_derivative_mul` — `p'(x)·q(x)` is one degree below `p(x)·q(x)`;
* `placeDegLE_wronskian` — the same for `p'q − pq'`;
* `valuation_derivation_mul_le` — **`v(D f)·v(x) ≤ v(f)` for `f = p(x)/q(x)`**.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

section ChainRule

variable {A : Type*} [CommRing A] [Algebra A K]

/-- **The chain rule for a polynomial whose coefficients the derivation kills.** -/
theorem derivation_eval_of_coeff (D : Derivation A K K) {p : Polynomial K}
    (hp : ∀ i, D (p.coeff i) = 0) (x : K) :
    D (p.eval x) = (Polynomial.derivative p).eval x * D x := by
  classical
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self p.natDegree) x, map_sum]
  have hterm : ∀ i ∈ Finset.range (p.natDegree + 1),
      D (p.coeff i * x ^ i) = ((i : K) * p.coeff i * x ^ (i - 1)) * D x := by
    intro i _
    rw [Derivation.leibniz, hp i, smul_zero, add_zero, Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, Finset.sum_range_succ']
  have hzero : ((0 : ℕ) : K) * p.coeff 0 * x ^ (0 - 1) = 0 := by
    simp
  rw [hzero, add_zero]
  have hdeg : (Polynomial.derivative p).natDegree < p.natDegree + 1 :=
    lt_of_le_of_lt (Polynomial.natDegree_derivative_le p) (by omega)
  rw [Polynomial.eval_eq_sum_range' hdeg x, Finset.sum_range_succ]
  have hlast : (Polynomial.derivative p).coeff p.natDegree * x ^ p.natDegree = 0 := by
    rw [Polynomial.coeff_derivative,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < p.natDegree + 1)]
    ring
  rw [hlast, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_derivative]
  push_cast
  ring

end ChainRule

/-- `p'(x)·q(x)` lies one degree below `p(x)·q(x)`. -/
theorem placeDegLE_eval_derivative_mul {F : Subfield K} (hF : PlaceTrivialOn v F)
    {p q : Polynomial K} (hp : CoeffsIn F p) (hq : CoeffsIn F q) {x : K}
    (hx : 1 ≤ v.valuation K x) :
    PlaceDegLE v ((v.valuation K x) ^ (p.natDegree + q.natDegree - 1))
      ((Polynomial.derivative p).eval x * q.eval x) := by
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · have hC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    have hd : Polynomial.derivative p = 0 := by
      rw [hC, Polynomial.derivative_C]
    rw [hd]
    simp only [Polynomial.eval_zero, zero_mul]
    exact placeDegLE_zero v _
  · have h1 : PlaceDegLE v ((v.valuation K x) ^ (p.natDegree - 1))
        ((Polynomial.derivative p).eval x) :=
      placeDegLE_eval_of_natDegree_le v hF hp.derivative hx (Polynomial.natDegree_derivative_le p)
    have h2 : PlaceDegLE v ((v.valuation K x) ^ q.natDegree) (q.eval x) :=
      placeDegLE_eval_of_natDegree_le v hF hq hx (le_refl _)
    have h := PlaceDegLE.mul v h1 h2
    rw [← pow_add] at h
    have heq : p.natDegree - 1 + q.natDegree = p.natDegree + q.natDegree - 1 := by omega
    rwa [heq] at h

/-- The Wronskian numerator lies one degree below the product. -/
theorem placeDegLE_wronskian {F : Subfield K} (hF : PlaceTrivialOn v F)
    {p q : Polynomial K} (hp : CoeffsIn F p) (hq : CoeffsIn F q) {x : K}
    (hx : 1 ≤ v.valuation K x) :
    PlaceDegLE v ((v.valuation K x) ^ (p.natDegree + q.natDegree - 1))
      ((Polynomial.derivative p).eval x * q.eval x
        - p.eval x * (Polynomial.derivative q).eval x) := by
  refine PlaceDegLE.sub v (placeDegLE_eval_derivative_mul v hF hp hq hx) ?_
  have h := placeDegLE_eval_derivative_mul v hF hq hp hx
  have hcomm : (Polynomial.derivative q).eval x * p.eval x
      = p.eval x * (Polynomial.derivative q).eval x := by ring
  rw [hcomm] at h
  have hsum : q.natDegree + p.natDegree - 1 = p.natDegree + q.natDegree - 1 := by omega
  rwa [hsum] at h

/-- **Differentiating a rational function of a large element drops one degree at the place.** -/
theorem valuation_derivation_mul_le {A : Type*} [CommRing A] [Algebra A K]
    (D : Derivation A K K) {F : Subfield K} (hF : PlaceTrivialOn v F)
    (hDF : ∀ a ∈ F, D a = 0) {x : K} (hx : 1 < v.valuation K x)
    (hDx : v.valuation K (D x) ≤ 1)
    {p q : Polynomial K} (hp : CoeffsIn F p) (hq : CoeffsIn F q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    v.valuation K (D (p.eval x / q.eval x)) * v.valuation K x
      ≤ v.valuation K (p.eval x / q.eval x) := by
  have hx1 : 1 ≤ v.valuation K x := le_of_lt hx
  have hx0 : v.valuation K x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hqx : q.eval x ≠ 0 := eval_ne_zero_of_valuation v hF hq hx hq0
  rcases Nat.eq_zero_or_pos (p.natDegree + q.natDegree) with hdeg0 | hdegpos
  · have hp' : p.natDegree = 0 := by omega
    have hq' : q.natDegree = 0 := by omega
    have hpe : p.eval x = p.coeff 0 := by
      conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hp']
      simp
    have hqe : q.eval x = q.coeff 0 := by
      conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hq']
      simp
    have hmem : p.eval x / q.eval x ∈ F := by
      rw [hpe, hqe]
      exact F.div_mem (hp 0) (hq 0)
    rw [hDF _ hmem, map_zero, zero_mul]
    exact zero_le
  have hDp : D (p.eval x) = (Polynomial.derivative p).eval x * D x :=
    derivation_eval_of_coeff D (fun i => hDF _ (hp i)) x
  have hDq : D (q.eval x) = (Polynomial.derivative q).eval x * D x :=
    derivation_eval_of_coeff D (fun i => hDF _ (hq i)) x
  have hquot : D (p.eval x / q.eval x)
      = ((Polynomial.derivative p).eval x * q.eval x
          - p.eval x * (Polynomial.derivative q).eval x) * D x / q.eval x ^ 2 := by
    rw [Derivation.leibniz_div D (p.eval x) (q.eval x), hDp, hDq]
    simp only [smul_eq_mul]
    field_simp
  have hnum : v.valuation K
      (((Polynomial.derivative p).eval x * q.eval x
        - p.eval x * (Polynomial.derivative q).eval x) * D x)
      ≤ (v.valuation K x) ^ (p.natDegree + q.natDegree - 1) := by
    have hDx' : PlaceDegLE v 1 (D x) := hDx
    have h := PlaceDegLE.mul v (placeDegLE_wronskian v hF hp hq hx1) hDx'
    rwa [mul_one] at h
  have hpx : v.valuation K (p.eval x) = (v.valuation K x) ^ p.natDegree :=
    valuation_eval_eq v hF hp hx hp0
  have hqv : v.valuation K (q.eval x) = (v.valuation K x) ^ q.natDegree :=
    valuation_eval_eq v hF hq hx hq0
  rw [hquot, map_div₀, map_div₀, map_pow, hqv, hpx]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (zero_lt_iff.mpr (pow_ne_zero _ (pow_ne_zero _ hx0)))
    (zero_lt_iff.mpr (pow_ne_zero _ hx0))]
  calc v.valuation K
        (((Polynomial.derivative p).eval x * q.eval x
          - p.eval x * (Polynomial.derivative q).eval x) * D x) * v.valuation K x
          * (v.valuation K x) ^ q.natDegree
      ≤ (v.valuation K x) ^ (p.natDegree + q.natDegree - 1) * v.valuation K x
          * (v.valuation K x) ^ q.natDegree := by
        exact mul_le_mul' (mul_le_mul' hnum (le_refl _)) (le_refl _)
    _ = (v.valuation K x) ^ p.natDegree * ((v.valuation K x) ^ q.natDegree) ^ 2 := by
        rw [← pow_succ, ← pow_add, ← pow_mul, ← pow_add]
        congr 1
        omega

end GaloisForLFunctions.HTGeometry
