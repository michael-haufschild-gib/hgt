import GaloisForLFunctions.HTGeometry.PlaceLimit

/-!
# Univariate factors at a place

The coordinate model reads a factor `p(X_m)` of the cascade against the degree in `X_m`.  On an
algebraic extension that degree becomes a place, and the same three facts are needed: a polynomial
in a large element has valuation at most the expected power, exactly the expected power when the
element is strictly large, and the logarithmic factor `x·p'(x)/p(x)` has the degree of `p` as its
value at the place.

The coefficients are only required to lie in a subfield on which the place is trivial — that is the
place-level form of coordinate freeness, and by `placeFree_of_isIntegral` it is inherited by every
algebraic extension of the coefficient field.

* `CoeffsIn`, `CoeffsIn.derivative`, `CoeffsIn.X_mul`, `CoeffsIn.const_mul`, `CoeffsIn.sub`;
* `placeDegLE_eval_of_natDegree_le` — the expected power is an upper bound;
* `valuation_eval_eq` — **it is attained when the element is strictly large**;
* `placeDegLE_logFactor` — a logarithmic factor is small;
* `placeLim_mul_logFactor` — **the value of `x·p'(x)/p(x)` at the place is `deg p`**.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- Every coefficient lies in the subfield. -/
def CoeffsIn (F : Subfield K) (p : Polynomial K) : Prop := ∀ i, p.coeff i ∈ F

theorem CoeffsIn.derivative {F : Subfield K} {p : Polynomial K} (hp : CoeffsIn F p) :
    CoeffsIn F (Polynomial.derivative p) := by
  intro i
  rw [Polynomial.coeff_derivative]
  exact F.mul_mem (hp _) (F.add_mem (natCast_mem F i) F.one_mem)

theorem CoeffsIn.X_mul {F : Subfield K} {p : Polynomial K} (hp : CoeffsIn F p) :
    CoeffsIn F (Polynomial.X * p) := by
  intro i
  cases i with
  | zero => simp
  | succ j =>
      rw [Polynomial.coeff_X_mul]
      exact hp j

theorem CoeffsIn.const_mul {F : Subfield K} {a : K} (ha : a ∈ F) {p : Polynomial K}
    (hp : CoeffsIn F p) : CoeffsIn F (Polynomial.C a * p) := by
  intro i
  rw [Polynomial.coeff_C_mul]
  exact F.mul_mem ha (hp i)

theorem CoeffsIn.sub {F : Subfield K} {p q : Polynomial K} (hp : CoeffsIn F p)
    (hq : CoeffsIn F q) : CoeffsIn F (p - q) := by
  intro i
  rw [Polynomial.coeff_sub]
  exact F.sub_mem (hp i) (hq i)

theorem valuation_coeff_le_one {F : Subfield K} (hF : PlaceTrivialOn v F) {p : Polynomial K}
    (hp : CoeffsIn F p) (i : ℕ) : v.valuation K (p.coeff i) ≤ 1 := by
  rcases eq_or_ne (p.coeff i) 0 with h | h
  · rw [h, map_zero]
    exact zero_le_one
  · rw [hF _ (hp i) h]

/-- **A polynomial in a large element has at most the expected valuation.** -/
theorem placeDegLE_eval_of_natDegree_le {F : Subfield K} (hF : PlaceTrivialOn v F)
    {p : Polynomial K} (hp : CoeffsIn F p) {x : K} (hx : 1 ≤ v.valuation K x)
    {k : ℕ} (hk : p.natDegree ≤ k) :
    PlaceDegLE v ((v.valuation K x) ^ k) (p.eval x) := by
  rw [PlaceDegLE, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hk) x]
  refine Valuation.map_sum_le _ fun i hi => ?_
  rw [map_mul, map_pow]
  have h1 : v.valuation K (p.coeff i) ≤ 1 := valuation_coeff_le_one v hF hp i
  have h2 : (v.valuation K x) ^ i ≤ (v.valuation K x) ^ k :=
    pow_le_pow_right₀ hx (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  calc v.valuation K (p.coeff i) * (v.valuation K x) ^ i
      ≤ 1 * (v.valuation K x) ^ k := mul_le_mul' h1 h2
    _ = (v.valuation K x) ^ k := one_mul _

/-- **A nonzero polynomial in a strictly large element has exactly the expected valuation.** -/
theorem valuation_eval_eq {F : Subfield K} (hF : PlaceTrivialOn v F) {p : Polynomial K}
    (hp : CoeffsIn F p) {x : K} (hx : 1 < v.valuation K x) (hp0 : p ≠ 0) :
    v.valuation K (p.eval x) = (v.valuation K x) ^ p.natDegree := by
  classical
  have hx1 : 1 ≤ v.valuation K x := le_of_lt hx
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self _) x]
  refine valuation_sum_of_lt v (Finset.self_mem_range_succ p.natDegree) _ ?_ ?_
  · rw [map_mul, map_pow,
      hF _ (hp p.natDegree) (Polynomial.leadingCoeff_ne_zero.mpr hp0), one_mul]
  · intro i hi hne
    have hlt : i < p.natDegree :=
      lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
    rw [map_mul, map_pow]
    have h1 : v.valuation K (p.coeff i) ≤ 1 := valuation_coeff_le_one v hF hp i
    have h2 : (v.valuation K x) ^ i < (v.valuation K x) ^ p.natDegree :=
      pow_lt_pow_right₀ hx hlt
    calc v.valuation K (p.coeff i) * (v.valuation K x) ^ i
        ≤ 1 * (v.valuation K x) ^ i := mul_le_mul' h1 (le_refl _)
      _ = (v.valuation K x) ^ i := one_mul _
      _ < (v.valuation K x) ^ p.natDegree := h2

theorem eval_ne_zero_of_valuation {F : Subfield K} (hF : PlaceTrivialOn v F) {p : Polynomial K}
    (hp : CoeffsIn F p) {x : K} (hx : 1 < v.valuation K x) (hp0 : p ≠ 0) : p.eval x ≠ 0 := by
  intro hc
  have h := valuation_eval_eq v hF hp hx hp0
  rw [hc, map_zero] at h
  have hne : (v.valuation K x) ^ p.natDegree ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hx))
  exact hne h.symm

/-- **A logarithmic factor is small at the place.** -/
theorem placeDegLE_logFactor {F : Subfield K} (hF : PlaceTrivialOn v F) {p : Polynomial K}
    (hp : CoeffsIn F p) {x : K} (hx : 1 < v.valuation K x) (hdeg : 1 ≤ p.natDegree) :
    PlaceDegLE v (v.valuation K x)⁻¹ ((Polynomial.derivative p).eval x / p.eval x) := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hdeg
  have hx0 : v.valuation K x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hnum : v.valuation K ((Polynomial.derivative p).eval x)
      ≤ (v.valuation K x) ^ (p.natDegree - 1) :=
    placeDegLE_eval_of_natDegree_le v hF hp.derivative (le_of_lt hx)
      (le_trans (Polynomial.natDegree_derivative_le p) (le_refl _))
  have hden : v.valuation K (p.eval x) = (v.valuation K x) ^ p.natDegree :=
    valuation_eval_eq v hF hp hx hp0
  rw [PlaceDegLE, map_div₀, hden]
  rw [div_le_iff₀ (zero_lt_iff.mpr (pow_ne_zero _ hx0))]
  refine le_trans hnum (le_of_eq ?_)
  have hsplit : (v.valuation K x) ^ p.natDegree
      = (v.valuation K x) ^ (p.natDegree - 1) * v.valuation K x := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hsplit, mul_comm ((v.valuation K x) ^ (p.natDegree - 1)) (v.valuation K x),
    ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]

/-- **The value of `x·p'(x)/p(x)` at the place is the degree of `p`.**  This is the place-level
form of the residue the peel of the newest column reads off. -/
theorem placeLim_mul_logFactor {F : Subfield K} (hF : PlaceTrivialOn v F) {p : Polynomial K}
    (hp : CoeffsIn F p) {x : K} (hx : 1 < v.valuation K x) (hdeg : 1 ≤ p.natDegree) :
    PlaceLim v (v.valuation K x)⁻¹
      (x * (Polynomial.derivative p).eval x / p.eval x) ((p.natDegree : K)) := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hdeg
  have hx0 : v.valuation K x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hpx : p.eval x ≠ 0 := eval_ne_zero_of_valuation v hF hp hx hp0
  set r : Polynomial K :=
    Polynomial.X * Polynomial.derivative p - Polynomial.C ((p.natDegree : K)) * p with hr
  have hrc : CoeffsIn F r :=
    CoeffsIn.sub (CoeffsIn.X_mul hp.derivative)
      (CoeffsIn.const_mul (natCast_mem F p.natDegree) hp)
  have hrdeg : r.natDegree ≤ p.natDegree - 1 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    have hN' : p.natDegree ≤ N := by omega
    rw [hr, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    rcases eq_or_lt_of_le hN' with heq | hlt
    · rw [heq]
      push_cast
      ring
    · have h1 : p.coeff (M + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h1]
      ring
  have hval : x * (Polynomial.derivative p).eval x / p.eval x - ((p.natDegree : K))
      = r.eval x / p.eval x := by
    rw [hr]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    field_simp
  rw [PlaceLim, hval, PlaceDegLE, map_div₀,
    valuation_eval_eq v hF hp hx hp0, div_le_iff₀ (zero_lt_iff.mpr (pow_ne_zero _ hx0))]
  refine le_trans (placeDegLE_eval_of_natDegree_le v hF hrc (le_of_lt hx) hrdeg) (le_of_eq ?_)
  have hsplit : (v.valuation K x) ^ p.natDegree
      = (v.valuation K x) ^ (p.natDegree - 1) * v.valuation K x := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hsplit, mul_comm ((v.valuation K x) ^ (p.natDegree - 1)) (v.valuation K x),
    ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]

/-- The accuracy of the two limits above is below the unit level. -/
theorem inv_valuation_le_one {x : K} (hx : 1 < v.valuation K x) :
    (v.valuation K x)⁻¹ ≤ 1 := by
  rw [inv_le_one₀ (lt_trans zero_lt_one hx)]
  exact le_of_lt hx

end GaloisForLFunctions.HTGeometry
