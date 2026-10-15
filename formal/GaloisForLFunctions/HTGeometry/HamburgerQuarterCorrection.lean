import GaloisForLFunctions.HTGeometry.HamburgerSquareSummable

/-!
# Hamburger's theta relation admits no quarter-power correction

Let `θ_a(x) = Σ_{n≥1} a_n e^{−π n² x}` with `Σ ‖a_n‖ n^{−2} < ∞`, and suppose that for every `x > 0`
`θ_a(x) = ε x^{−1/2} θ_b(1/x) + α + β x^{−1/2} + γ x^{−1/4}`.

**Theorem** (`quarter_eq_zero_of_coeffTheta_relation_of_sq`).  Then `γ = 0`.

In Dirichlet-series language the term `γ x^{−1/4}` would be a pole at `s = 1/2` of
`π^{−s/2}Γ(s/2) Σ a_n n^{−s}`; the theorem says the theta relation leaves no room for it.  With the
odd sign `ε = −1`, `b = a` it then follows from `coeff_eq_zero_of_odd_coeffTheta_relation_of_sq`
that `a = 0` (`coeff_eq_zero_of_odd_coeffTheta_relation_quarter_of_sq`).

**Proof.**  The Laplace transform against `e^{−π t² x}` turns the relation into
`H(t) = ε Σ b_n e^{−2π n t} + α/(π t) + β + γ q t^{−1/2}` for the Hamburger series
`H(t) = Σ a_n t / (π (n² + t²))`, with `q = Γ(3/4) π^{−3/4}`; both sides are holomorphic on
`Re t > 0`, so the identity holds there.  The dual series is `i`-periodic, hence
`H(t + i) − H(t) = α/π (1/(t+i) − 1/t) + γ q ((t+i)^{−1/2} − t^{−1/2})`.  For real `t ∈ (0, 1]` the
`n = 1` term of `H(t + i)` is `a₁/(2π t) + a₁/(2π (t + 2i))` and everything else is bounded, so
`c/t + γ q t^{−1/2}` is bounded on `(0, 1]` with `c = a₁/(2π) + α/π`.  Letting `t → 0` forces
`c = 0` and then `γ q = 0`.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The quarter constant `q = Γ(3/4) π^{−3/4}`. -/
def quarterConst : ℝ := Real.Gamma (3 / 4) * Real.pi ^ (-(3 / 4 : ℝ))

theorem quarterConst_pos : 0 < quarterConst :=
  mul_pos (Real.Gamma_pos_of_pos (by norm_num)) (Real.rpow_pos_of_pos Real.pi_pos _)

/-- `∫₀^∞ x^{−1/4} e^{−π t² x} dx = q t^{−3/2}`. -/
theorem integral_Ioi_rpow_neg_quarter_mul_exp {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), x ^ ((3 / 4 : ℝ) - 1) * Real.exp (-((Real.pi * t ^ 2) * x)) =
      quarterConst * t ^ (-(3 / 2 : ℝ)) := by
  have hr : 0 < Real.pi * t ^ 2 := by positivity
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr]
  have h1 : (1 / (Real.pi * t ^ 2)) ^ (3 / 4 : ℝ) =
      Real.pi ^ (-(3 / 4 : ℝ)) * t ^ (-(3 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos Real.pi_pos,
      Real.rpow_def_of_pos ht, ← Real.exp_add]
    congr 1
    rw [one_div, Real.log_inv, Real.log_mul Real.pi_pos.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  rw [h1, quarterConst]
  ring

/-- `t · t^{−3/2} = t^{−1/2}`. -/
theorem mul_rpow_neg_three_halves {t : ℝ} (ht : 0 < t) :
    t * t ^ (-(3 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) := by
  have := Real.rpow_add ht 1 (-(3 / 2 : ℝ))
  rw [Real.rpow_one] at this
  rw [← this]
  norm_num

/-! ## The Laplace identity with the quarter term -/

/-- **The Laplace identity on the positive axis.** -/
theorem hamburgerSeries_eq_quarter_ofReal (a b : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (hb : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    {ε α β γ : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        γ * (x : ℂ) ^ (-(1 / 4 : ℂ)))
    {t : ℝ} (ht : 0 < t) :
    hamburgerSeries a t =
      ε * ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) +
        α / (Real.pi * t) + β + γ * ((quarterConst : ℂ) * (t : ℂ) ^ (-(1 / 2 : ℂ))) := by
  set e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) with he_def
  have hB : 0 < Real.pi * t ^ 2 := by positivity
  have he_int : IntegrableOn e (Ioi 0) := (integrableOn_Ioi_exp_neg_mul hB).ofReal
  have hhe_eq : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x =
      ((x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [he_def, Complex.ofReal_mul, Complex.ofReal_cpow hx0.le]
    push_cast
    ring_nf
  have hqe_eq : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 4 : ℂ)) * e x =
      ((x ^ ((3 / 4 : ℝ) - 1) * Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [he_def, Complex.ofReal_mul, Complex.ofReal_cpow hx0.le]
    push_cast
    ring_nf
  have hhe_int : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hB
    have h' : IntegrableOn (fun x : ℝ => ((x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ)) (Ioi 0) := by
      have := Integrable.ofReal (𝕜 := ℂ) h
      simp only [Real.rpow_one, neg_mul] at this
      exact this
    exact IntegrableOn.congr_fun h' (fun x hx => (hhe_eq x hx).symm) measurableSet_Ioi
  have hqe_int : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 4 : ℂ)) * e x) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => x ^ ((3 / 4 : ℝ) - 1) *
        Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hB
    have h' : IntegrableOn (fun x : ℝ => ((x ^ ((3 / 4 : ℝ) - 1) *
        Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ)) (Ioi 0) := by
      have := Integrable.ofReal (𝕜 := ℂ) h
      simp only [Real.rpow_one, neg_mul] at this
      exact this
    exact IntegrableOn.congr_fun h' (fun x hx => (hqe_eq x hx).symm) measurableSet_Ioi
  have hD_int := integrableOn_dual_coeffTheta_mul_exp_of_sq b hb ht
  have hI0 : ∫ x in Ioi (0 : ℝ), e x = ((1 / (Real.pi * t ^ 2) : ℝ) : ℂ) := by
    rw [he_def, integral_complex_ofReal, integral_Ioi_exp_neg_mul hB]
  have hIh : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x = ((1 / t : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hhe_eq, integral_complex_ofReal,
      integral_Ioi_rpow_neg_half_mul_exp_neg_mul_sq ht]
  have hIq : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 4 : ℂ)) * e x =
      ((quarterConst * t ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hqe_eq, integral_complex_ofReal,
      integral_Ioi_rpow_neg_quarter_mul_exp ht]
  have hpt : ∀ x ∈ Ioi (0 : ℝ), coeffTheta a x * e x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x) +
        ((α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) +
          γ * ((x : ℂ) ^ (-(1 / 4 : ℂ)) * e x)) := by
    intro x hx
    rw [htheta x hx]
    ring
  have hsplit : ∫ x in Ioi (0 : ℝ), coeffTheta a x * e x =
      ε * (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x) +
        (α * ∫ x in Ioi (0 : ℝ), e x) +
          β * (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) +
            γ * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 4 : ℂ)) * e x := by
    have i1 := hD_int.const_mul ε
    have i2 := he_int.const_mul α
    have i3 := hhe_int.const_mul β
    have i4 := hqe_int.const_mul γ
    have h1 := integral_add i1 ((i2.add i3).add i4)
    have h2 := integral_add (i2.add i3) i4
    have h3 := integral_add i2 i3
    simp only [Pi.add_apply] at h1 h2 h3
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, h1, h2, h3, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul]
    ring
  have hL := (hasSum_integral_coeffTheta_mul_exp_of_sq a ha ht).tsum_eq
  have hD := (hasSum_integral_dual_coeffTheta_mul_exp_of_sq b hb ht).tsum_eq
  rw [hsplit, ← hD, hI0, hIh, hIq] at hL
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hham : hamburgerSeries a t = (t : ℂ) * ∑' n : ℕ,
      a (n + 1) / ((Real.pi * (((n : ℝ) + 1) ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    rw [hamburgerSeries, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  have hdual : ∑' n : ℕ, b (n + 1) *
      ((1 / t * Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t)) : ℝ) : ℂ) =
      (1 / (t : ℂ)) * ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  have hq : (t : ℂ) * ((quarterConst * t ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) =
      (quarterConst : ℂ) * (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
    have h := mul_rpow_neg_three_halves ht
    have e1 : (t : ℂ) ^ (-(1 / 2 : ℂ)) = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow ht.le]; push_cast; ring_nf
    rw [e1, ← h]
    push_cast
    ring
  rw [hham, hL, hdual]
  have e2 : (t : ℂ) * (ε * (1 / (t : ℂ) * ∑' n : ℕ, b (n + 1) *
        cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t))) +
      α * ((1 / (Real.pi * t ^ 2) : ℝ) : ℂ) + β * ((1 / t : ℝ) : ℂ) +
      γ * ((quarterConst * t ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) =
      ε * ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) +
        α / (Real.pi * t) + β + γ * ((t : ℂ) * ((quarterConst * t ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by
    push_cast
    field_simp
  rw [e2, hq]

/-! ## Holomorphy and periodicity -/

theorem differentiableOn_cpow_neg_half_re_pos :
    DifferentiableOn ℂ (fun t : ℂ => t ^ (-(1 / 2 : ℂ))) {t : ℂ | 0 < t.re} := fun _ ht =>
  (DifferentiableAt.cpow differentiableAt_id (differentiableAt_const _)
    (Complex.mem_slitPlane_iff.mpr (Or.inl ht))).differentiableWithinAt

/-- **The Laplace identity on the right half-plane.** -/
theorem hamburgerSeries_eq_quarter (a b : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (hb : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    {ε α β γ : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        γ * (x : ℂ) ^ (-(1 / 4 : ℂ)))
    {t : ℂ} (ht : 0 < t.re) :
    hamburgerSeries a t =
      ε * ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) +
        α / (Real.pi * t) + β + γ * ((quarterConst : ℂ) * t ^ (-(1 / 2 : ℂ))) := by
  set U : Set ℂ := {t : ℂ | 0 < t.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_rpow_two ha
    simpa using this
  have hf : AnalyticOnNhd ℂ (hamburgerSeries a) U :=
    (differentiableOn_hamburgerSeries ha2).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => ε * ∑' n : ℕ, b (n + 1) *
      cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) + α / (Real.pi * t) + β +
        γ * ((quarterConst : ℂ) * t ^ (-(1 / 2 : ℂ)))) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    refine ((((differentiableOn_expDualSeries (summable_sq_of_rpow_two hb)).const_mul ε).add
      ?_).add (differentiableOn_const _)).add
      ((differentiableOn_cpow_neg_half_re_pos.const_mul _).const_mul _)
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) fun t ht => ?_
    have ht' : 0 < t.re := ht
    refine mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) fun h => ?_
    rw [h, zero_re] at ht'
    exact lt_irrefl _ ht'
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), hamburgerSeries a z = ε * ∑' n : ℕ, b (n + 1) *
      cexp (-(2 * Real.pi * ((n : ℂ) + 1) * z)) + α / (Real.pi * z) + β +
        γ * ((quarterConst : ℂ) * z ^ (-(1 / 2 : ℂ))) := by
    set u : ℕ → ℂ := fun k => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ) with hu
    have hlim : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
        rw [add_zero] at h
        have h2 := (Complex.continuous_ofReal.tendsto 1).comp h
        rw [Complex.ofReal_one] at h2
        exact h2
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hu]
        intro h
        have h' : (1 + 1 / ((k : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    refine hlim.frequently (Frequently.of_forall fun k => ?_)
    have hk : (0 : ℝ) < 1 + 1 / ((k : ℝ) + 1) := by positivity
    exact hamburgerSeries_eq_quarter_ofReal a b ha hb htheta hk
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected
    h1U hfreq ht

/-- Under the quarter relation the Hamburger series is `i`-periodic up to the pole term and the
quarter term. -/
theorem hamburgerSeries_periodic_quarter (a b : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (hb : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    {ε α β γ : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        γ * (x : ℂ) ^ (-(1 / 4 : ℂ)))
    {t : ℂ} (ht : 0 < t.re) :
    hamburgerSeries a (t + I) - hamburgerSeries a t =
      α / (Real.pi * (t + I)) - α / (Real.pi * t) +
        γ * (quarterConst : ℂ) * ((t + I) ^ (-(1 / 2 : ℂ)) - t ^ (-(1 / 2 : ℂ))) := by
  have ht' : 0 < (t + I).re := by simpa using ht
  rw [hamburgerSeries_eq_quarter a b ha hb htheta ht',
    hamburgerSeries_eq_quarter a b ha hb htheta ht]
  have hper : ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * (t + I))) =
      ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) := by
    refine tsum_congr fun n => ?_
    rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (t + I)) =
      -(2 * Real.pi * ((n : ℂ) + 1) * t) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hper]
  ring

/-! ## Bounds near `t = 0` -/

/-- On real `t ∈ (0, 1]` the Hamburger series is bounded by `(1/π) Σ ‖a_n‖ n^{−2}`. -/
theorem norm_hamburgerSeries_ofReal_le {a : ℕ → ℂ}
    (ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) {t : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1) :
    ‖hamburgerSeries a t‖ ≤ (1 / Real.pi) * ∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have hb : ∀ n : ℕ, ‖a (n + 1) * (t : ℂ) / ((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 +
      (t : ℂ) ^ 2))‖ ≤ (1 / Real.pi) * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have hden : (((n + 1 : ℕ) : ℂ) ^ 2 + (t : ℂ) ^ 2) = ((((n + 1 : ℕ) : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hden, norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg ht.le, Real.norm_of_nonneg Real.pi_pos.le,
      Real.norm_of_nonneg (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    have h1 : ‖a (n + 1)‖ * t ≤ ‖a (n + 1)‖ := by
      nlinarith [norm_nonneg (a (n + 1))]
    have h2 : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 + t ^ 2 := by nlinarith
    calc ‖a (n + 1)‖ * t ≤ ‖a (n + 1)‖ := h1
      _ = (1 / Real.pi) * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
          (Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) := by
          field_simp
      _ ≤ (1 / Real.pi) * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
          (Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 + t ^ 2)) := by
          gcongr
  have hs : Summable fun n : ℕ => (1 / Real.pi) * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    ha2.mul_left _
  unfold hamburgerSeries
  calc ‖∑' n : ℕ, a (n + 1) * (t : ℂ) / ((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 + (t : ℂ) ^ 2))‖
      ≤ ∑' n : ℕ, (1 / Real.pi) * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) :=
        tsum_of_norm_bounded hs.hasSum hb
    _ = (1 / Real.pi) * ∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := tsum_mul_left

/-- On real `t ∈ (0, 1]`, `H(t + i) = a₁/(2π t) + D(t)` with `D` bounded by an explicit constant. -/
theorem norm_hamburgerSeries_add_I_sub_le {a : ℕ → ℂ}
    (ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) {t : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1) :
    ‖hamburgerSeries a ((t : ℂ) + I) - a 1 / (2 * Real.pi * t)‖ ≤
      ‖a 1‖ / (4 * Real.pi) +
        (8 / (3 * Real.pi)) * ∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  set z : ℂ := (t : ℂ) + I with hz
  set f : ℕ → ℂ := fun n => a (n + 1) * z / ((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 + z ^ 2))
    with hf
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hzn : ‖z‖ ≤ 2 := by
    rw [hz]
    calc ‖(t : ℂ) + I‖ ≤ ‖(t : ℂ)‖ + ‖I‖ := norm_add_le _ _
      _ ≤ 2 := by rw [Complex.norm_real, Complex.norm_I, Real.norm_of_nonneg ht.le]; linarith
  -- the tail terms
  have htail : ∀ n : ℕ, ‖f (n + 1)‖ ≤
      (8 / (3 * Real.pi)) * (‖a (n + 1 + 1)‖ / ((n + 1 + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    set m : ℝ := ((n + 1 + 1 : ℕ) : ℝ) with hm
    have hm2 : 2 ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hden : ‖(((n + 1 + 1 : ℕ) : ℂ) ^ 2 + z ^ 2)‖ ≥ (3 / 4) * m ^ 2 := by
      have e : (((n + 1 + 1 : ℕ) : ℂ) ^ 2 + z ^ 2) = ((m ^ 2 - 1 + t ^ 2 : ℝ) : ℂ) +
          ((2 * t : ℝ) : ℂ) * I := by
        rw [hz, hm]; push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [e]
      have hre : (3 / 4) * m ^ 2 ≤ m ^ 2 - 1 + t ^ 2 := by nlinarith
      calc (3 / 4) * m ^ 2 ≤ m ^ 2 - 1 + t ^ 2 := hre
        _ = |(((m ^ 2 - 1 + t ^ 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I).re| := by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
          rw [abs_of_nonneg (by nlinarith)]
        _ ≤ ‖((m ^ 2 - 1 + t ^ 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I‖ := Complex.abs_re_le_norm _
    simp only [hf]
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hπ.le]
    have hdpos : 0 < (3 / 4) * m ^ 2 := by positivity
    rw [div_le_iff₀ (mul_pos hπ (lt_of_lt_of_le hdpos hden))]
    calc ‖a (n + 1 + 1)‖ * ‖z‖ ≤ ‖a (n + 1 + 1)‖ * 2 :=
          mul_le_mul_of_nonneg_left hzn (norm_nonneg _)
      _ = (8 / (3 * Real.pi)) * (‖a (n + 1 + 1)‖ / m ^ 2) * (Real.pi * ((3 / 4) * m ^ 2)) := by
          field_simp; ring
      _ ≤ (8 / (3 * Real.pi)) * (‖a (n + 1 + 1)‖ / m ^ 2) *
          (Real.pi * ‖(((n + 1 + 1 : ℕ) : ℂ) ^ 2 + z ^ 2)‖) := by
          gcongr
  have hS : Summable fun n : ℕ => ‖a (n + 1 + 1)‖ / ((n + 1 + 1 : ℕ) : ℝ) ^ 2 :=
    (summable_nat_add_iff 1).mpr ha2
  have hstail : Summable fun n : ℕ => f (n + 1) :=
    Summable.of_norm_bounded (hS.mul_left _) htail
  have hsf : Summable f := (summable_nat_add_iff 1).mp hstail
  -- the `n = 1` term
  have hz2 : (1 : ℂ) + z ^ 2 = (t : ℂ) * ((t : ℂ) + 2 * I) := by
    rw [hz]; ring_nf; rw [Complex.I_sq]; ring
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have ht2 : (t : ℂ) + 2 * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hf0 : f 0 = a 1 / (2 * Real.pi * t) + a 1 / (2 * Real.pi * ((t : ℂ) + 2 * I)) := by
    have e1 : f 0 = a 1 * z / ((Real.pi : ℂ) * (1 + z ^ 2)) := by simp [hf]
    have h2π : (2 : ℂ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero hπ0
    rw [e1, hz2, hz, div_add_div _ _ (mul_ne_zero h2π ht0) (mul_ne_zero h2π ht2),
      div_eq_div_iff (mul_ne_zero hπ0 (mul_ne_zero ht0 ht2))
        (mul_ne_zero (mul_ne_zero h2π ht0) (mul_ne_zero h2π ht2))]
    ring
  have hH : hamburgerSeries a z = f 0 + ∑' n : ℕ, f (n + 1) := hsf.tsum_eq_zero_add
  rw [hH, hf0]
  have h2t : ‖(t : ℂ) + 2 * I‖ ≥ 2 := by
    calc (2 : ℝ) = |((t : ℂ) + 2 * I).im| := by simp
      _ ≤ ‖(t : ℂ) + 2 * I‖ := Complex.abs_im_le_norm _
  have hfirst : ‖a 1 / (2 * Real.pi * ((t : ℂ) + 2 * I))‖ ≤ ‖a 1‖ / (4 * Real.pi) := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hπ.le,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    nlinarith
  have hrest : ‖∑' n : ℕ, f (n + 1)‖ ≤
      (8 / (3 * Real.pi)) * ∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    calc ‖∑' n : ℕ, f (n + 1)‖ ≤ ∑' n : ℕ, (8 / (3 * Real.pi)) *
          (‖a (n + 1 + 1)‖ / ((n + 1 + 1 : ℕ) : ℝ) ^ 2) :=
          tsum_of_norm_bounded (hS.mul_left _).hasSum htail
      _ = (8 / (3 * Real.pi)) * ∑' n : ℕ, ‖a (n + 1 + 1)‖ / ((n + 1 + 1 : ℕ) : ℝ) ^ 2 :=
          tsum_mul_left
      _ ≤ (8 / (3 * Real.pi)) * ∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [ha2.tsum_eq_zero_add]
          have h0 : 0 ≤ ‖a (0 + 1)‖ / ((0 + 1 : ℕ) : ℝ) ^ 2 := by positivity
          linarith
  calc ‖a 1 / (2 * Real.pi * t) + a 1 / (2 * Real.pi * ((t : ℂ) + 2 * I)) +
        ∑' n : ℕ, f (n + 1) - a 1 / (2 * Real.pi * t)‖
      = ‖a 1 / (2 * Real.pi * ((t : ℂ) + 2 * I)) + ∑' n : ℕ, f (n + 1)‖ := by ring_nf
    _ ≤ ‖a 1 / (2 * Real.pi * ((t : ℂ) + 2 * I))‖ + ‖∑' n : ℕ, f (n + 1)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hfirst hrest

/-- `‖(t + i)^{−1/2}‖ ≤ 1` for real `t`. -/
theorem norm_cpow_neg_half_add_I_le (t : ℝ) : ‖((t : ℂ) + I) ^ (-(1 / 2 : ℂ))‖ ≤ 1 := by
  have hne : (t : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  rw [Complex.norm_cpow_of_ne_zero hne]
  have him : (-(1 / 2 : ℂ)).im = 0 := by simp
  have hre : (-(1 / 2 : ℂ)).re = -(1 / 2) := by simp
  rw [him, hre, mul_zero, Real.exp_zero, div_one]
  have h1 : 1 ≤ ‖(t : ℂ) + I‖ := by
    calc (1 : ℝ) = |((t : ℂ) + I).im| := by simp
      _ ≤ ‖(t : ℂ) + I‖ := Complex.abs_im_le_norm _
  exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)

/-! ## The quarter term vanishes -/

/-- A bounded combination `c/t + g t^{−1/2}` on `(0, 1]` has `c = 0` and `g = 0`. -/
theorem eq_zero_of_bounded_pole_add_half {c g : ℂ} {M : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖c / t + g * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤ M) :
    c = 0 ∧ g = 0 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (h 1 one_pos le_rfl)
  -- `‖c‖ ≤ √t (M + ‖g‖)`
  have hc : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖c‖ ≤ Real.sqrt t * (M + ‖g‖) := by
    intro t ht ht1
    have hs := Real.sqrt_pos.mpr ht
    have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    have hst : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
    have hrp : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
      rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have e : c = (t : ℂ) * (c / t + g * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) -
        g * ((Real.sqrt t : ℝ) : ℂ) := by
      rw [hrp, Complex.ofReal_inv]
      have hs0 : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      have htc : (t : ℂ) = (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) := by
        rw [← Complex.ofReal_mul, hsq]
      rw [htc]
      field_simp
      ring
    rw [e]
    calc ‖(t : ℂ) * (c / t + g * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) - g * ((Real.sqrt t : ℝ) : ℂ)‖
        ≤ ‖(t : ℂ) * (c / t + g * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ +
            ‖g * ((Real.sqrt t : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ t * M + ‖g‖ * Real.sqrt t := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ht.le,
            Real.norm_of_nonneg hs.le]
          gcongr
          exact h t ht ht1
      _ ≤ Real.sqrt t * M + ‖g‖ * Real.sqrt t := by
          have : t ≤ Real.sqrt t := by nlinarith
          gcongr
      _ = Real.sqrt t * (M + ‖g‖) := by ring
  have hc0 : c = 0 := by
    by_contra hne
    have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hne
    set K : ℝ := M + ‖g‖ + 1 with hK
    have hKpos : 0 < K := by have := norm_nonneg g; rw [hK]; linarith
    set t : ℝ := min 1 ((‖c‖ / (2 * K)) ^ 2) with htdef
    have ht : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have hsq : Real.sqrt t ≤ ‖c‖ / (2 * K) := by
      calc Real.sqrt t ≤ Real.sqrt ((‖c‖ / (2 * K)) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
        _ = ‖c‖ / (2 * K) := Real.sqrt_sq (by positivity)
    have h1 := hc t ht ht1
    have h2 : Real.sqrt t * (M + ‖g‖) ≤ ‖c‖ / (2 * K) * K := by
      have : M + ‖g‖ ≤ K := by rw [hK]; linarith
      exact mul_le_mul hsq this (by positivity) (by positivity)
    have h3 : ‖c‖ / (2 * K) * K = ‖c‖ / 2 := by field_simp
    linarith
  refine ⟨hc0, ?_⟩
  -- with `c = 0`, `‖g‖ ≤ M √t`
  have hg : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖g‖ ≤ M * Real.sqrt t := by
    intro t ht ht1
    have hs := Real.sqrt_pos.mpr ht
    have hrp : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
      rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
    have h1 := h t ht ht1
    rw [hc0, zero_div, zero_add, norm_mul, Complex.norm_real, hrp,
      Real.norm_of_nonneg (inv_nonneg.mpr hs.le)] at h1
    rw [mul_inv_le_iff₀ hs] at h1
    linarith
  by_contra hne
  have hpos : 0 < ‖g‖ := norm_pos_iff.mpr hne
  set t : ℝ := min 1 ((‖g‖ / (2 * (M + 1))) ^ 2) with htdef
  have ht : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hsq : Real.sqrt t ≤ ‖g‖ / (2 * (M + 1)) := by
    calc Real.sqrt t ≤ Real.sqrt ((‖g‖ / (2 * (M + 1))) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = ‖g‖ / (2 * (M + 1)) := Real.sqrt_sq (by positivity)
  have h1 := hg t ht ht1
  have h2 : M * Real.sqrt t ≤ (M + 1) * (‖g‖ / (2 * (M + 1))) := by
    exact mul_le_mul (by linarith) hsq (Real.sqrt_nonneg _) (by positivity)
  have h3 : (M + 1) * (‖g‖ / (2 * (M + 1))) = ‖g‖ / 2 := by field_simp
  linarith

/-- **No quarter correction.**  If `θ_a(x) = ε x^{−1/2} θ_b(1/x) + α + β x^{−1/2} + γ x^{−1/4}` for all
`x > 0`, then `γ = 0`. -/
theorem quarter_eq_zero_of_coeffTheta_relation_of_sq {a b : ℕ → ℂ} {ε α β γ : ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (hb : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        γ * (x : ℂ) ^ (-(1 / 4 : ℂ))) :
    γ = 0 := by
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_rpow_two ha
    simpa using this
  set S : ℝ := ∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set M : ℝ := ‖a 1‖ / (4 * Real.pi) + (8 / (3 * Real.pi)) * S + (1 / Real.pi) * S +
    ‖α‖ / Real.pi + ‖γ * (quarterConst : ℂ)‖ with hM
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖(a 1 / (2 * Real.pi) + α / Real.pi) / t + γ * (quarterConst : ℂ) *
        ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤ M := by
    intro t ht ht1
    have htre : 0 < ((t : ℂ)).re := by simpa using ht
    have hper := hamburgerSeries_periodic_quarter a b ha hb htheta htre
    have hD := norm_hamburgerSeries_add_I_sub_le ha2 ht ht1
    have hH := norm_hamburgerSeries_ofReal_le ha2 ht ht1
    have hcp : (t : ℂ) ^ (-(1 / 2 : ℂ)) = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow ht.le]; push_cast; ring_nf
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have htI : (t : ℂ) + I ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this
    -- rearrange the periodicity identity
    have e : (a 1 / (2 * Real.pi) + α / Real.pi) / t + γ * (quarterConst : ℂ) *
        ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        -(hamburgerSeries a ((t : ℂ) + I) - a 1 / (2 * Real.pi * t)) + hamburgerSeries a t +
          α / (Real.pi * ((t : ℂ) + I)) + γ * (quarterConst : ℂ) * ((t : ℂ) + I) ^ (-(1 / 2 : ℂ)) := by
      rw [← hcp]
      linear_combination hper
    rw [e]
    have hnI := norm_cpow_neg_half_add_I_le t
    have hα : ‖α / (Real.pi * ((t : ℂ) + I))‖ ≤ ‖α‖ / Real.pi := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hπ.le]
      apply div_le_div_of_nonneg_left (norm_nonneg _) hπ
      have h1 : 1 ≤ ‖(t : ℂ) + I‖ := by
        calc (1 : ℝ) = |((t : ℂ) + I).im| := by simp
          _ ≤ ‖(t : ℂ) + I‖ := Complex.abs_im_le_norm _
      nlinarith
    have hq : ‖γ * (quarterConst : ℂ) * ((t : ℂ) + I) ^ (-(1 / 2 : ℂ))‖ ≤
        ‖γ * (quarterConst : ℂ)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) hnI
    have n1 := norm_add_le (-(hamburgerSeries a ((t : ℂ) + I) - a 1 / (2 * Real.pi * t)) +
      hamburgerSeries a t + α / (Real.pi * ((t : ℂ) + I)))
      (γ * (quarterConst : ℂ) * ((t : ℂ) + I) ^ (-(1 / 2 : ℂ)))
    have n2 := norm_add_le (-(hamburgerSeries a ((t : ℂ) + I) - a 1 / (2 * Real.pi * t)) +
      hamburgerSeries a t) (α / (Real.pi * ((t : ℂ) + I)))
    have n3 := norm_add_le (-(hamburgerSeries a ((t : ℂ) + I) - a 1 / (2 * Real.pi * t)))
      (hamburgerSeries a t)
    rw [norm_neg] at n3
    rw [hM]
    linarith
  obtain ⟨-, hg⟩ := eq_zero_of_bounded_pole_add_half key
  have hq0 : (quarterConst : ℂ) ≠ 0 := by exact_mod_cast quarterConst_pos.ne'
  exact (mul_eq_zero.mp hg).resolve_right hq0

/-- **The odd relation with a quarter correction forces vanishing.**  If
`θ_a(x) = −x^{−1/2} θ_a(1/x) + α + β x^{−1/2} + γ x^{−1/4}` for all `x > 0`, then `γ = 0` and
`a_n = 0` for every `n ≥ 1`. -/
theorem coeff_eq_zero_of_odd_coeffTheta_relation_quarter_of_sq {a : ℕ → ℂ} {α β γ : ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      (-1) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        γ * (x : ℂ) ^ (-(1 / 4 : ℂ))) :
    γ = 0 ∧ ∀ n : ℕ, a (n + 1) = 0 := by
  have hγ := quarter_eq_zero_of_coeffTheta_relation_of_sq ha ha htheta
  refine ⟨hγ, fun n => coeff_eq_zero_of_odd_coeffTheta_relation_of_sq (α := α) (β := β) ha
    (fun x hx => ?_) n⟩
  rw [htheta x hx, hγ, zero_mul, add_zero]

end GaloisForLFunctions.HTGeometry
