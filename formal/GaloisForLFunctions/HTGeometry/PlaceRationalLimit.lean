import GaloisForLFunctions.HTGeometry.PlaceUnivFactor

/-!
# The value of a rational function at a place above infinity

A ratio of two polynomials of the same degree in a large element has the ratio of the leading
coefficients as its value at the place, and a ratio of strictly smaller degree has value zero.
Both are the place-level form of the coordinate model's value at infinity, and both come from the
same observation: the numerator of `p/q − a/b` is `b·p − a·q`, whose leading terms cancel.

* `CoeffsIn.leadingCoeff_mem`;
* `natDegree_leadingCombination_lt` — the cancellation;
* `placeLim_div_of_natDegree_eq` — **equal degrees: the value is the ratio of leading
  coefficients**;
* `placeLim_div_of_natDegree_lt` — **smaller degree: the value is zero**.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

theorem CoeffsIn.leadingCoeff_mem {F : Subfield K} {p : Polynomial K} (hp : CoeffsIn F p) :
    p.leadingCoeff ∈ F := hp p.natDegree

/-- The leading terms of `b·p − a·q` cancel when `p` and `q` have the same degree and `a`, `b` are
their leading coefficients. -/
theorem natDegree_leadingCombination_lt {p q : Polynomial K} (hdeg : p.natDegree = q.natDegree) :
    (Polynomial.C q.leadingCoeff * p - Polynomial.C p.leadingCoeff * q).natDegree
      ≤ p.natDegree - 1 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  rcases Nat.lt_or_ge N p.natDegree with hlt | hge
  · omega
  · rcases eq_or_lt_of_le hge with heq | hgt
    · have h1 : p.coeff N = p.leadingCoeff := by
        rw [← heq]
        rfl
      have h2 : q.coeff N = q.leadingCoeff := by
        rw [← heq, hdeg]
        rfl
      rw [h1, h2]
      ring
    · have h1 : p.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
      have h2 : q.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h1, h2]
      ring

/-- **Equal degrees: the value at the place is the ratio of the leading coefficients.** -/
theorem placeLim_div_of_natDegree_eq {F : Subfield K} (hF : PlaceTrivialOn v F)
    {p q : Polynomial K} (hp : CoeffsIn F p) (hq : CoeffsIn F q) (hq0 : q ≠ 0)
    (hdeg : p.natDegree = q.natDegree) {x : K} (hx : 1 < v.valuation K x) :
    PlaceLim v (v.valuation K x)⁻¹ (p.eval x / q.eval x)
      (p.leadingCoeff / q.leadingCoeff) := by
  have hx0 : v.valuation K x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hqx : q.eval x ≠ 0 := eval_ne_zero_of_valuation v hF hq hx hq0
  have hb : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
  set r : Polynomial K :=
    Polynomial.C q.leadingCoeff * p - Polynomial.C p.leadingCoeff * q with hr
  have hrc : CoeffsIn F r :=
    CoeffsIn.sub (CoeffsIn.const_mul hq.leadingCoeff_mem hp)
      (CoeffsIn.const_mul hp.leadingCoeff_mem hq)
  have hrdeg : r.natDegree ≤ p.natDegree - 1 := natDegree_leadingCombination_lt hdeg
  have hval : p.eval x / q.eval x - p.leadingCoeff / q.leadingCoeff
      = r.eval x / (q.leadingCoeff * q.eval x) := by
    rw [hr]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    field_simp
  rcases Nat.eq_zero_or_pos p.natDegree with hd0 | hdpos
  · have hqd0 : q.natDegree = 0 := by omega
    have hpc : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
    have hqc : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hqd0
    have hr0 : r = 0 := by
      have hpq : Polynomial.C q.leadingCoeff * p = Polynomial.C p.leadingCoeff * q := by
        conv_lhs => rw [hpc]
        conv_rhs => rw [hqc]
        simp only [Polynomial.leadingCoeff, hd0, hqd0]
        ring
      rw [hr, hpq, sub_self]
    rw [PlaceLim, hval, hr0]
    simp [PlaceDegLE]
  · obtain ⟨k, hk⟩ : ∃ k, p.natDegree = k + 1 := ⟨p.natDegree - 1, by omega⟩
    rw [PlaceLim, hval, PlaceDegLE, map_div₀, map_mul,
      hF _ hq.leadingCoeff_mem hb, one_mul, valuation_eval_eq v hF hq hx hq0, ← hdeg, hk,
      div_le_iff₀ (zero_lt_iff.mpr (pow_ne_zero _ hx0))]
    have hstep := placeDegLE_eval_of_natDegree_le v hF hrc (le_of_lt hx)
      (le_trans hrdeg (by omega : p.natDegree - 1 ≤ k))
    refine le_trans hstep (le_of_eq ?_)
    rw [pow_succ, ← mul_assoc, mul_right_comm, inv_mul_cancel₀ hx0, one_mul]

/-- **Strictly smaller degree: the value at the place is zero.** -/
theorem placeLim_div_of_natDegree_lt {F : Subfield K} (hF : PlaceTrivialOn v F)
    {p q : Polynomial K} (hp : CoeffsIn F p) (hq : CoeffsIn F q) (hq0 : q ≠ 0)
    (hdeg : p.natDegree < q.natDegree) {x : K} (hx : 1 < v.valuation K x) :
    PlaceLim v (v.valuation K x)⁻¹ (p.eval x / q.eval x) 0 := by
  have hx0 : v.valuation K x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  obtain ⟨k, hk⟩ : ∃ k, q.natDegree = k + 1 := ⟨q.natDegree - 1, by omega⟩
  rw [PlaceLim, sub_zero, PlaceDegLE, map_div₀, valuation_eval_eq v hF hq hx hq0, hk,
    div_le_iff₀ (zero_lt_iff.mpr (pow_ne_zero _ hx0))]
  have hstep := placeDegLE_eval_of_natDegree_le v hF hp (le_of_lt hx)
    (by omega : p.natDegree ≤ k)
  refine le_trans hstep (le_of_eq ?_)
  rw [pow_succ, ← mul_assoc, mul_right_comm, inv_mul_cancel₀ hx0, one_mul]

end GaloisForLFunctions.HTGeometry
