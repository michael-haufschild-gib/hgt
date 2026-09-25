import GaloisForLFunctions.RHTower.RouteEFixedOrderSelectedFibreBoundary

open Set Finset
namespace RHTower
noncomputable section

/-- Mean-value form of a reciprocal-power edge. -/
theorem routeE_rpow_neg_difference_mvt
    {s x y : ℝ} (_hs : 0 < s) (hx : 0 < x) (hxy : x < y) :
    ∃ c ∈ Ioo x y,
      x ^ (-s) - y ^ (-s) = (y - x) * s * c ^ (-(s + 1)) := by
  let f : ℝ → ℝ := fun z => z ^ (-s)
  let f' : ℝ → ℝ := fun z => -s * z ^ (-(s + 1))
  have hd (z : ℝ) (hz : 0 < z) : HasDerivAt f (f' z) z := by
    have h := Real.hasDerivAt_rpow_const (x := z) (p := -s) (Or.inl hz.ne')
    simpa only [f, f', show -s - 1 = -(s + 1) by ring] using h
  have hc : ContinuousOn f (Icc x y) := by
    intro z hz
    exact (hd z (lt_of_lt_of_le hx hz.1)).continuousAt.continuousWithinAt
  have hder : ∀ z ∈ Ioo x y, HasDerivAt f (f' z) z := by
    intro z hz
    exact hd z (lt_trans hx hz.1)
  obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope f f' hxy hc hder
  refine ⟨c, hc, ?_⟩
  have hgap : 0 < y - x := sub_pos.mpr hxy
  rw [eq_div_iff hgap.ne'] at hsl
  dsimp [f, f'] at hsl
  nlinarith

theorem routeEFixedOrderDifference_mvt
    {r a b : ℝ} (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) :
    ∃ c ∈ Ioo (b + a) (b + 2 * a),
      routeEFixedOrderDifference r a b =
        r * a * c ^ (-(r + 1)) := by
  obtain ⟨c, hc, h⟩ := routeE_rpow_neg_difference_mvt
    hr (by linarith : 0 < b + a) (by linarith : b + a < b + 2 * a)
  refine ⟨c, hc, ?_⟩
  unfold routeEFixedOrderDifference
  convert h using 1 <;> ring

/-- Uniform first-order expansion of the real-order Route E edge, with a
quadratic error throughout the RH receiver interval `1 ≤ r ≤ 2`. -/
theorem routeEFixedOrderDifference_linearization
    {r a b : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2)
    (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ r * a * b ^ (-(r + 1)) - routeEFixedOrderDifference r a b ∧
      r * a * b ^ (-(r + 1)) - routeEFixedOrderDifference r a b ≤
        12 * a ^ (2 : ℕ) * b ^ (-(r + 2)) := by
  rcases eq_or_lt_of_le ha with rfl | ha0
  · simp [routeEFixedOrderDifference]
  obtain ⟨c, hc, hK⟩ := routeEFixedOrderDifference_mvt
    (r := r) (a := a) (b := b) (by linarith) ha0 hb
  have hbc : b < c := by linarith [hc.1]
  have hpow : c ^ (-(r + 1)) ≤ b ^ (-(r + 1)) :=
    Real.rpow_le_rpow_of_nonpos hb hbc.le (by linarith)
  constructor
  · rw [hK]
    have hmult := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ r * a)
    nlinarith
  · obtain ⟨z, hz, hdiff⟩ := routeE_rpow_neg_difference_mvt
      (s := r + 1) (x := b) (y := c)
      (by linarith : 0 < r + 1) hb hbc
    have hzpow : z ^ (-(r + 2)) ≤ b ^ (-(r + 2)) :=
      Real.rpow_le_rpow_of_nonpos hb hz.1.le (by linarith)
    have hcgap : c - b ≤ 2 * a := by linarith [hc.2]
    have hcoeff : 0 ≤ r * a * (r + 1) := by positivity
    have hzp : 0 ≤ z ^ (-(r + 2)) :=
      Real.rpow_nonneg (lt_trans hb hz.1).le _
    have hbp : 0 ≤ b ^ (-(r + 2)) := Real.rpow_nonneg hb.le _
    rw [hK]
    calc
      r * a * b ^ (-(r + 1)) - r * a * c ^ (-(r + 1)) =
          r * a * (b ^ (-(r + 1)) - c ^ (-(r + 1))) := by ring
      _ = r * a * ((c - b) * (r + 1) * z ^ (-(r + 2))) := by
        rw [hdiff]
        congr 1
        ring
      _ ≤ r * a * (2 * a * (r + 1) * z ^ (-(r + 2))) := by
        nlinarith [mul_le_mul_of_nonneg_right hcgap (mul_nonneg hcoeff hzp)]
      _ ≤ r * a * (2 * a * (r + 1) * b ^ (-(r + 2))) := by
        nlinarith [mul_le_mul_of_nonneg_left hzpow
          (by positivity : 0 ≤ r * a * (2 * a) * (r + 1))]
      _ ≤ 12 * a ^ (2 : ℕ) * b ^ (-(r + 2)) := by
        have hconst : 2 * r * (r + 1) ≤ 12 := by nlinarith
        have ht : 0 ≤ a ^ (2 : ℕ) * b ^ (-(r + 2)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hconst ht]

def routeEFixedOrderCofactorLinearMain
    (r a : ℝ) (q : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioo 0 q,
    c d * (r * a * (((q : ℝ) * (d : ℝ)) ^ (-(r + 1))))

/-- The physical denominator-cofactor completion has a uniform quadratic
linearization error. No arithmetic signs are assumed. -/
theorem abs_routeEFixedOrderCofactorFibre_sub_linearMain_le
    {r a : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) (ha : 0 ≤ a)
    {q : ℕ} (hq : 0 < q) (c : ℕ → ℝ) (hc : ∀ d, |c d| ≤ 1) :
    |routeEFixedOrderCofactorFibre r a q c -
      routeEFixedOrderCofactorLinearMain r a q c| ≤
        24 * a ^ (2 : ℕ) * (q : ℝ) ^ (-(r + 2)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlocal (d : ℕ) (hd : d ∈ Finset.Ioo 0 q) :
      |c d * routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ)) -
        c d * (r * a * (((q : ℝ) * (d : ℝ)) ^ (-(r + 1))))| ≤
        (12 * a ^ (2 : ℕ) * (q : ℝ) ^ (-(r + 2))) *
          (1 / (d : ℝ) ^ (2 : ℕ)) := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Ioo.mp hd).1
    have hd1 : (1 : ℝ) ≤ d := by
      exact_mod_cast (show 1 ≤ d by have := (Finset.mem_Ioo.mp hd).1; omega)
    have hlin := routeEFixedOrderDifference_linearization hr hr2 ha
      (mul_pos hq0 hd0)
    have hdm : (d : ℝ) ^ (-(r + 2)) ≤ (d : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
    have heq : ((q : ℝ) * (d : ℝ)) ^ (-(r + 2)) =
        (q : ℝ) ^ (-(r + 2)) * (d : ℝ) ^ (-(r + 2)) :=
      Real.mul_rpow hq0.le hd0.le
    have hdiff : |routeEFixedOrderDifference r a ((q : ℝ) * d) -
        r * a * (((q : ℝ) * d) ^ (-(r + 1)))| ≤
        12 * a ^ (2 : ℕ) * (((q : ℝ) * d) ^ (-(r + 2))) := by
      rw [abs_sub_comm, abs_of_nonneg hlin.1]
      exact hlin.2
    have hcoeff : |c d| *
        |routeEFixedOrderDifference r a ((q : ℝ) * d) -
          r * a * (((q : ℝ) * d) ^ (-(r + 1)))| ≤
        |routeEFixedOrderDifference r a ((q : ℝ) * d) -
          r * a * (((q : ℝ) * d) ^ (-(r + 1)))| := by
      simpa using mul_le_mul_of_nonneg_right (hc d)
        (abs_nonneg (routeEFixedOrderDifference r a ((q : ℝ) * d) -
          r * a * (((q : ℝ) * d) ^ (-(r + 1)))))
    have hbound : |c d| *
        |routeEFixedOrderDifference r a ((q : ℝ) * d) -
          r * a * (((q : ℝ) * d) ^ (-(r + 1)))| ≤
        12 * a ^ (2 : ℕ) * (((q : ℝ) * d) ^ (-(r + 2))) := by
      nlinarith [hcoeff, hdiff]
    calc
      _ = |c d| *
          |routeEFixedOrderDifference r a ((q : ℝ) * d) -
            r * a * (((q : ℝ) * d) ^ (-(r + 1)))| := by rw [← mul_sub, abs_mul]
      _ ≤ 12 * a ^ (2 : ℕ) * (((q : ℝ) * d) ^ (-(r + 2))) := hbound
      _ = (12 * a ^ (2 : ℕ) * (q : ℝ) ^ (-(r + 2))) *
          (d : ℝ) ^ (-(r + 2)) := by rw [heq]; ring
      _ ≤ (12 * a ^ (2 : ℕ) * (q : ℝ) ^ (-(r + 2))) *
          (d : ℝ) ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left hdm (by positivity)
      _ = (12 * a ^ (2 : ℕ) * (q : ℝ) ^ (-(r + 2))) *
          (1 / (d : ℝ) ^ (2 : ℕ)) := by
            rw [Real.rpow_neg hd0.le, Real.rpow_ofNat]
            ring
  have hsum : (∑ d ∈ Finset.Ioo 0 q, 1 / (d : ℝ) ^ (2 : ℕ)) ≤ 2 := by
    have h := sum_Ioo_inv_sq_le (α := ℝ) 0 q
    norm_num at h ⊢
    simpa only [one_div] using h
  unfold routeEFixedOrderCofactorFibre routeEFixedOrderCofactorLinearMain
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ Finset.Ioo 0 q,
        (c d * routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ)) -
          c d * (r * a * (((q : ℝ) * (d : ℝ)) ^ (-(r + 1)))))| ≤
      ∑ d ∈ Finset.Ioo 0 q,
        |c d * routeEFixedOrderDifference r a ((q : ℝ) * (d : ℝ)) -
          c d * (r * a * (((q : ℝ) * (d : ℝ)) ^ (-(r + 1))))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioo 0 q,
        (12 * a ^ (2 : ℕ) * (q : ℝ) ^ (-(r + 2))) *
          (1 / (d : ℝ) ^ (2 : ℕ)) := Finset.sum_le_sum hlocal
    _ = (12 * a ^ (2 : ℕ) * (q : ℝ) ^ (-(r + 2))) *
        (∑ d ∈ Finset.Ioo 0 q, 1 / (d : ℝ) ^ (2 : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ (12 * a ^ (2 : ℕ) * (q : ℝ) ^ (-(r + 2))) * 2 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 24 * a ^ (2 : ℕ) * (q : ℝ) ^ (-(r + 2)) := by ring

end
end RHTower
