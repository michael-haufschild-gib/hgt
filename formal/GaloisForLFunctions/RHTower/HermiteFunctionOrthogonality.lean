import GaloisForLFunctions.RHTower.ProlateHermiteRungWindowLimit

/-!
# Truncated orthogonality of the Hermite functions

Two Hermite functions at different rungs have an exactly computable truncated inner product: their
Wronskian `W = φ_m′φ_n − φ_mφ_n′` satisfies `W′ = 2(n − m)φ_mφ_n`, so

`∫_a^b φ_mφ_n = (W(b) − W(a)) / (2(n − m))` .

Every Hermite function and its derivative is a polynomial times `e^{−ξ²/2}`, so the Wronskian
vanishes at both ends of the line, and the full inner product is zero.  The identity is exact, so
it also gives the truncation error on a finite window with no estimate at all.

Mathlib carries the Hermite polynomials but no analysis of the Hermite functions; this is the
orthogonality half.
-/

open Filter Topology Set

noncomputable section

namespace RHTower

/-- Polynomials lose to a Gaussian at `+∞`. -/
theorem tendsto_polyEval_mul_gauss_atTop (p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => p.eval x * Real.exp (-(b * x ^ 2))) atTop (𝓝 0) := by
  have hterm : ∀ k ∈ Finset.range (p.natDegree + 1),
      Tendsto (fun x : ℝ => p.coeff k * (x ^ k * Real.exp (-(b * x ^ 2)))) atTop (𝓝 0) := by
    intro k _
    have h := (tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero k hb).const_mul (p.coeff k)
    simpa using h
  have hsum := tendsto_finsetSum (Finset.range (p.natDegree + 1)) hterm
  rw [Finset.sum_const_zero] at hsum
  refine hsum.congr ?_
  intro x
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Polynomials lose to a Gaussian at `−∞`. -/
theorem tendsto_polyEval_mul_gauss_atBot (p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => p.eval x * Real.exp (-(b * x ^ 2))) atBot (𝓝 0) := by
  have h := tendsto_polyEval_mul_gauss_atTop (p.comp (-Polynomial.X)) hb
  have hneg : Tendsto (fun x : ℝ => -x) atBot atTop := tendsto_neg_atBot_atTop
  refine (h.comp hneg).congr ?_
  intro x
  simp only [Function.comp_apply, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
    neg_neg]
  ring_nf

/-- The integer-coefficient form used by the Hermite functions. -/
theorem tendsto_aevalPoly_mul_gauss_atTop (p : Polynomial ℤ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => Polynomial.aeval x p * Real.exp (-(b * x ^ 2))) atTop (𝓝 0) := by
  have hmap : ∀ x : ℝ, Polynomial.aeval x p
      = (p.map (algebraMap ℤ ℝ)).eval x := by
    intro x
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  refine (tendsto_polyEval_mul_gauss_atTop (p.map (algebraMap ℤ ℝ)) hb).congr ?_
  intro x
  rw [hmap]

theorem tendsto_aevalPoly_mul_gauss_atBot (p : Polynomial ℤ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => Polynomial.aeval x p * Real.exp (-(b * x ^ 2))) atBot (𝓝 0) := by
  have hmap : ∀ x : ℝ, Polynomial.aeval x p
      = (p.map (algebraMap ℤ ℝ)).eval x := by
    intro x
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  refine (tendsto_polyEval_mul_gauss_atBot (p.map (algebraMap ℤ ℝ)) hb).congr ?_
  intro x
  rw [hmap]

theorem tendsto_probHermiteFun_atTop (n : ℕ) : Tendsto (probHermiteFun n) atTop (𝓝 0) := by
  refine (tendsto_aevalPoly_mul_gauss_atTop (Polynomial.hermite n)
    (by norm_num : (0 : ℝ) < 1 / 4)).congr ?_
  intro x
  rw [probHermiteFun]
  congr 2
  ring

theorem tendsto_probHermiteFun_atBot (n : ℕ) : Tendsto (probHermiteFun n) atBot (𝓝 0) := by
  refine (tendsto_aevalPoly_mul_gauss_atBot (Polynomial.hermite n)
    (by norm_num : (0 : ℝ) < 1 / 4)).congr ?_
  intro x
  rw [probHermiteFun]
  congr 2
  ring

theorem tendsto_deriv_probHermiteFun_atTop (n : ℕ) :
    Tendsto (deriv (probHermiteFun n)) atTop (𝓝 0) := by
  have h1 := tendsto_aevalPoly_mul_gauss_atTop (Polynomial.derivative (Polynomial.hermite n))
    (by norm_num : (0 : ℝ) < 1 / 4)
  have h2 := tendsto_aevalPoly_mul_gauss_atTop (Polynomial.X * Polynomial.hermite n)
    (by norm_num : (0 : ℝ) < 1 / 4)
  have h3 := (h1.sub (h2.const_mul (1 / 2 : ℝ)))
  rw [mul_zero, sub_zero] at h3
  refine h3.congr ?_
  intro x
  rw [deriv_probHermiteFun]
  simp only [probHermiteFun, map_mul, Polynomial.aeval_X]
  have hb : -((1 / 4 : ℝ) * x ^ 2) = -(x ^ 2 / 4) := by ring
  rw [hb]
  ring

theorem tendsto_deriv_probHermiteFun_atBot (n : ℕ) :
    Tendsto (deriv (probHermiteFun n)) atBot (𝓝 0) := by
  have h1 := tendsto_aevalPoly_mul_gauss_atBot (Polynomial.derivative (Polynomial.hermite n))
    (by norm_num : (0 : ℝ) < 1 / 4)
  have h2 := tendsto_aevalPoly_mul_gauss_atBot (Polynomial.X * Polynomial.hermite n)
    (by norm_num : (0 : ℝ) < 1 / 4)
  have h3 := (h1.sub (h2.const_mul (1 / 2 : ℝ)))
  rw [mul_zero, sub_zero] at h3
  refine h3.congr ?_
  intro x
  rw [deriv_probHermiteFun]
  simp only [probHermiteFun, map_mul, Polynomial.aeval_X]
  have hb : -((1 / 4 : ℝ) * x ^ 2) = -(x ^ 2 / 4) := by ring
  rw [hb]
  ring

theorem tendsto_sqrtTwo_mul_atTop : Tendsto (fun x : ℝ => Real.sqrt 2 * x) atTop atTop :=
  Filter.Tendsto.const_mul_atTop (Real.sqrt_pos.2 (by norm_num)) tendsto_id

theorem tendsto_sqrtTwo_mul_atBot : Tendsto (fun x : ℝ => Real.sqrt 2 * x) atBot atBot :=
  Filter.Tendsto.const_mul_atBot (Real.sqrt_pos.2 (by norm_num)) tendsto_id

theorem tendsto_hermiteFun_atTop (n : ℕ) : Tendsto (hermiteFun n) atTop (𝓝 0) :=
  (tendsto_probHermiteFun_atTop n).comp tendsto_sqrtTwo_mul_atTop

theorem tendsto_hermiteFun_atBot (n : ℕ) : Tendsto (hermiteFun n) atBot (𝓝 0) :=
  (tendsto_probHermiteFun_atBot n).comp tendsto_sqrtTwo_mul_atBot

theorem tendsto_deriv_hermiteFun_atTop (n : ℕ) :
    Tendsto (deriv (hermiteFun n)) atTop (𝓝 0) := by
  have h := ((tendsto_deriv_probHermiteFun_atTop n).comp
    tendsto_sqrtTwo_mul_atTop).const_mul (Real.sqrt 2)
  rw [mul_zero] at h
  rw [deriv_hermiteFun_eq]
  exact h

theorem tendsto_deriv_hermiteFun_atBot (n : ℕ) :
    Tendsto (deriv (hermiteFun n)) atBot (𝓝 0) := by
  have h := ((tendsto_deriv_probHermiteFun_atBot n).comp
    tendsto_sqrtTwo_mul_atBot).const_mul (Real.sqrt 2)
  rw [mul_zero] at h
  rw [deriv_hermiteFun_eq]
  exact h

/-- Wronskian of two Hermite functions. -/
def hermiteWronskian (m n : ℕ) (x : ℝ) : ℝ :=
  deriv (hermiteFun m) x * hermiteFun n x - hermiteFun m x * deriv (hermiteFun n) x

theorem hermiteWronskian_eq (m n : ℕ) :
    hermiteWronskian m n = fun x => deriv (hermiteFun m) x * hermiteFun n x
      - hermiteFun m x * deriv (hermiteFun n) x := rfl

/-- **The Wronskian differentiates to the product.**  This is the whole content of Hermite
orthogonality: the rung difference appears as the constant. -/
theorem hasDerivAt_hermiteWronskian (m n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteWronskian m n)
      (2 * ((n : ℝ) - (m : ℝ)) * (hermiteFun m x * hermiteFun n x)) x := by
  have h1 := ((hasDerivAt_deriv_hermiteFun m x).mul (hasDerivAt_hermiteFun n x)).sub
    ((hasDerivAt_hermiteFun m x).mul (hasDerivAt_deriv_hermiteFun n x))
  refine h1.congr_deriv ?_
  rw [hermiteRungP, hermiteRungP]
  ring

theorem continuous_hermiteFun (n : ℕ) : Continuous (hermiteFun n) :=
  (differentiable_hermiteFun n).continuous

theorem continuous_deriv_hermiteFun (n : ℕ) : Continuous (deriv (hermiteFun n)) :=
  (differentiable_deriv_hermiteFun n).continuous

theorem continuous_hermiteWronskian (m n : ℕ) : Continuous (hermiteWronskian m n) := by
  rw [hermiteWronskian_eq]
  exact ((continuous_deriv_hermiteFun m).mul (continuous_hermiteFun n)).sub
    ((continuous_hermiteFun m).mul (continuous_deriv_hermiteFun n))

/-- **Exact truncated orthogonality.**  On any interval the inner product of two Hermite functions
at different rungs is the Wronskian's increment, divided by twice the rung difference. -/
theorem integral_hermiteFun_mul_eq {m n : ℕ} (hmn : m ≠ n) (a b : ℝ) :
    (∫ x in a..b, hermiteFun m x * hermiteFun n x)
      = (hermiteWronskian m n b - hermiteWronskian m n a) / (2 * ((n : ℝ) - (m : ℝ))) := by
  have hnm : (n : ℝ) - (m : ℝ) ≠ 0 := by
    intro h
    exact hmn (Nat.cast_injective (sub_eq_zero.1 h)).symm
  have hne : (2 : ℝ) * ((n : ℝ) - (m : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero hnm
  have hcont : Continuous
      (fun x : ℝ => 2 * ((n : ℝ) - (m : ℝ)) * (hermiteFun m x * hermiteFun n x)) :=
    continuous_const.mul ((continuous_hermiteFun m).mul (continuous_hermiteFun n))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := hermiteWronskian m n)
    (f' := fun x => 2 * ((n : ℝ) - (m : ℝ)) * (hermiteFun m x * hermiteFun n x))
    (fun x _ => hasDerivAt_hermiteWronskian m n x) (hcont.intervalIntegrable a b)
  rw [intervalIntegral.integral_const_mul] at hFTC
  rw [eq_div_iff hne, mul_comm]
  exact hFTC

theorem tendsto_hermiteWronskian_atTop (m n : ℕ) :
    Tendsto (hermiteWronskian m n) atTop (𝓝 0) := by
  have h := ((tendsto_deriv_hermiteFun_atTop m).mul (tendsto_hermiteFun_atTop n)).sub
    ((tendsto_hermiteFun_atTop m).mul (tendsto_deriv_hermiteFun_atTop n))
  rw [mul_zero, sub_zero] at h
  rw [hermiteWronskian_eq]
  exact h

theorem tendsto_hermiteWronskian_atBot (m n : ℕ) :
    Tendsto (hermiteWronskian m n) atBot (𝓝 0) := by
  have h := ((tendsto_deriv_hermiteFun_atBot m).mul (tendsto_hermiteFun_atBot n)).sub
    ((tendsto_hermiteFun_atBot m).mul (tendsto_deriv_hermiteFun_atBot n))
  rw [mul_zero, sub_zero] at h
  rw [hermiteWronskian_eq]
  exact h

/-- **Orthogonality in the limit.**  Hermite functions at different rungs have vanishing symmetric
truncated inner products as the window grows. -/
theorem tendsto_integral_hermiteFun_mul {m n : ℕ} (hmn : m ≠ n) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, hermiteFun m x * hermiteFun n x) atTop (𝓝 0) := by
  have hW := (tendsto_hermiteWronskian_atTop m n).sub
    ((tendsto_hermiteWronskian_atBot m n).comp tendsto_neg_atTop_atBot)
  rw [sub_zero] at hW
  have hdiv := hW.div_const (2 * ((n : ℝ) - (m : ℝ)))
  rw [zero_div] at hdiv
  refine hdiv.congr ?_
  intro R
  rw [integral_hermiteFun_mul_eq hmn]
  simp [Function.comp_apply]

/-- A nonzero polynomial is nonzero somewhere in every nondegenerate open interval. -/
theorem exists_polyEval_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b, p.eval x ≠ 0 := by
  by_contra hcon
  rw [not_exists] at hcon
  refine hp (Polynomial.eq_zero_of_infinite_isRoot p ?_)
  refine Set.Infinite.mono ?_ (Set.Ioo_infinite hab)
  intro x hx
  have := hcon x
  rw [not_and, not_not] at this
  exact this hx

/-- The Hermite polynomial is nonzero, being monic. -/
theorem hermiteMap_ne_zero (n : ℕ) :
    (Polynomial.hermite n).map (algebraMap ℤ ℝ) ≠ 0 :=
  ((Polynomial.hermite_monic n).map (algebraMap ℤ ℝ)).ne_zero

/-- A Hermite function does not vanish identically on any nondegenerate interval. -/
theorem exists_hermiteFun_ne_zero (n : ℕ) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b, hermiteFun n x ≠ 0 := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨y, hy, hyne⟩ := exists_polyEval_ne_zero (hermiteMap_ne_zero n)
    (a := Real.sqrt 2 * a) (b := Real.sqrt 2 * b) (by nlinarith [hab, hs])
  refine ⟨y / Real.sqrt 2, ⟨?_, ?_⟩, ?_⟩
  · rw [lt_div_iff₀ hs, mul_comm]
    exact hy.1
  · rw [div_lt_iff₀ hs, mul_comm]
    exact hy.2
  · have hpt : Real.sqrt 2 * (y / Real.sqrt 2) = y := by
      field_simp
    show probHermiteFun n (Real.sqrt 2 * (y / Real.sqrt 2)) ≠ 0
    rw [hpt, probHermiteFun]
    have haeval : Polynomial.aeval y (Polynomial.hermite n)
        = ((Polynomial.hermite n).map (algebraMap ℤ ℝ)).eval y := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [haeval]
    exact mul_ne_zero hyne (Real.exp_ne_zero _)

/-- **The window mass of a Hermite function is positive.**  Every nondegenerate window carries
positive mass, because the Hermite polynomial has only finitely many roots. -/
theorem integral_hermiteFun_sq_pos (n : ℕ) {a b : ℝ} (hab : a < b) :
    0 < ∫ x in a..b, hermiteFun n x ^ 2 := by
  obtain ⟨x₀, hx₀, hne⟩ := exists_hermiteFun_ne_zero n hab
  have hcont : Continuous fun x : ℝ => hermiteFun n x ^ 2 := (continuous_hermiteFun n).pow 2
  have hnn : ∀ x : ℝ, 0 ≤ hermiteFun n x ^ 2 := fun x => sq_nonneg _
  -- a subinterval around `x₀` on which the square stays above a positive constant
  have hpos0 : 0 < hermiteFun n x₀ ^ 2 := by positivity
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ x, |x - x₀| < δ →
      hermiteFun n x₀ ^ 2 / 2 < hermiteFun n x ^ 2 := by
    have hc := hcont.continuousAt (x := x₀)
    have := hc.eventually (eventually_gt_nhds (by linarith : hermiteFun n x₀ ^ 2 / 2
      < hermiteFun n x₀ ^ 2))
    rw [Metric.eventually_nhds_iff] at this
    obtain ⟨δ, hδ, h⟩ := this
    exact ⟨δ, hδ, fun x hx => h (by rwa [Real.dist_eq])⟩
  set α : ℝ := max a (x₀ - δ / 2) with hα
  set β : ℝ := min b (x₀ + δ / 2) with hβ
  have hαx : α < x₀ := max_lt hx₀.1 (by linarith)
  have hxβ : x₀ < β := lt_min hx₀.2 (by linarith)
  have hαβ : α < β := lt_trans hαx hxβ
  have haα : a ≤ α := le_max_left _ _
  have hβb : β ≤ b := min_le_left _ _
  have hmid : 0 < ∫ x in α..β, hermiteFun n x ^ 2 := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable α β) (fun x hx => ?_) hαβ
    refine lt_trans (by linarith) (hball x ?_)
    rw [abs_lt]
    constructor
    · have : x₀ - δ / 2 ≤ α := le_max_right _ _
      have := hx.1
      linarith
    · have : β ≤ x₀ + δ / 2 := min_le_right _ _
      have := hx.2
      linarith
  have hsplit1 : (∫ x in a..α, hermiteFun n x ^ 2) + ∫ x in α..β, hermiteFun n x ^ 2
      = ∫ x in a..β, hermiteFun n x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hsplit2 : (∫ x in a..β, hermiteFun n x ^ 2) + ∫ x in β..b, hermiteFun n x ^ 2
      = ∫ x in a..b, hermiteFun n x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hleft : (0 : ℝ) ≤ ∫ x in a..α, hermiteFun n x ^ 2 :=
    intervalIntegral.integral_nonneg haα (fun x _ => hnn x)
  have hright : (0 : ℝ) ≤ ∫ x in β..b, hermiteFun n x ^ 2 :=
    intervalIntegral.integral_nonneg hβb (fun x _ => hnn x)
  linarith [hsplit1, hsplit2, hmid, hleft, hright]

end RHTower
