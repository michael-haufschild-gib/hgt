import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard
import GaloisForLFunctions.HTGeometry.DirichletStripAlmostPeriodic

/-!
# The Gaussian-damped zeta series `F_τ(w) = Σ e^{−τ log²m} m^{−w}`

For `τ > 0` the damping `e^{−τ log²m}` beats every power of `m`, so

`F_τ(w) = Σ_{m ≥ 1} e^{−τ log² m} m^{−w}`

converges absolutely and locally uniformly on `ℂ`: `F_τ` is entire (`differentiable_gaussDirichlet`),
of order at most two (`norm_gaussDirichlet_le_exp`), almost periodic on every vertical strip
(`isStripAlmostPeriodic_gaussDirichlet`), and `F_τ(w) → 1` as `Re w → +∞` uniformly in `Im w`.

**`F_τ` has a zero** (`exists_gaussDirichlet_eq_zero`). Otherwise `F_τ = e^P` with a polynomial `P`
(zero-free entire functions of finite order). On the real axis every term is positive, so
`|F_τ(σ)| > 1` and `Re P(σ) > 0`, while `Re P(σ) → 0` as `σ → +∞`; a real polynomial that is
positive and tends to `0` does not exist.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The `n`-th term `e^{−τ log²(n+1)} (n+1)^{−w}`. -/
def gaussDirichletTerm (τ : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  ((Real.exp (-(τ * Real.log ((n : ℝ) + 1) ^ 2)) : ℝ) : ℂ) * (((n + 1 : ℕ) : ℂ) ^ (-w))

/-- `F_τ(w) = Σ_{m ≥ 1} e^{−τ log² m} m^{−w}`. -/
def gaussDirichlet (τ : ℝ) (w : ℂ) : ℂ := ∑' n : ℕ, gaussDirichletTerm τ n w

theorem norm_gaussDirichletTerm (τ : ℝ) (n : ℕ) (w : ℂ) :
    ‖gaussDirichletTerm τ n w‖ =
      Real.exp (-(τ * Real.log ((n : ℝ) + 1) ^ 2)) * ((n : ℝ) + 1) ^ (-w.re) := by
  rw [gaussDirichletTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
  push_cast
  rfl

/-- `e^{−τl² + Rl} ≤ e^{(R+2)²/(4τ)} e^{−2l}`. -/
theorem gauss_exponent_le {τ R l : ℝ} (hτ : 0 < τ) :
    -(τ * l ^ 2) + R * l ≤ (R + 2) ^ 2 / (4 * τ) - 2 * l := by
  have h : 0 ≤ τ * (l - (R + 2) / (2 * τ)) ^ 2 := by positivity
  have e : τ * (l - (R + 2) / (2 * τ)) ^ 2 =
      τ * l ^ 2 - (R + 2) * l + (R + 2) ^ 2 / (4 * τ) := by
    field_simp; ring
  linarith

theorem norm_gaussDirichletTerm_le {τ R : ℝ} (hτ : 0 < τ) (n : ℕ) {w : ℂ} (hw : -w.re ≤ R) :
    ‖gaussDirichletTerm τ n w‖ ≤
      Real.exp ((R + 2) ^ 2 / (4 * τ)) * (((n : ℝ) + 1) ^ 2)⁻¹ := by
  rw [norm_gaussDirichletTerm]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set l := Real.log ((n : ℝ) + 1)
  have hl : 0 ≤ l := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [Real.rpow_def_of_pos hn, ← Real.exp_add]
  have h2 : (((n : ℝ) + 1) ^ 2)⁻¹ = Real.exp (-(2 * l)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hn.le, Real.rpow_def_of_pos hn]
    congr 1; push_cast; ring
  rw [h2, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := gauss_exponent_le (R := R) (l := l) hτ
  have h3 : l * -w.re ≤ R * l := by nlinarith
  linarith

theorem summable_inv_succ_sq : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
  have h := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  have := (summable_nat_add_iff 1).mpr h
  simpa using this

theorem hasSum_inv_add_one_sq : HasSum (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, one_div, zero_pow two_ne_zero,
    inv_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
  exact h

theorem hasSum_inv_add_two_sq :
    HasSum (fun n : ℕ => (((n : ℝ) + 2) ^ 2)⁻¹) (Real.pi ^ 2 / 6 - 1) := by
  have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, one_div,
    zero_pow two_ne_zero, inv_zero, Nat.cast_one, one_pow, inv_one, zero_add,
    Nat.cast_add, Nat.cast_ofNat] at h
  exact h

theorem pi_sq_div_six_le_two : Real.pi ^ 2 / 6 ≤ 2 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

theorem summable_gaussDirichletTerm {τ : ℝ} (hτ : 0 < τ) (w : ℂ) :
    Summable (fun n => gaussDirichletTerm τ n w) := by
  refine Summable.of_norm_bounded (summable_inv_succ_sq.mul_left
    (Real.exp ((-w.re + 2) ^ 2 / (4 * τ)))) fun n => ?_
  exact norm_gaussDirichletTerm_le hτ n le_rfl

/-- **`F_τ` is entire.** -/
theorem differentiable_gaussDirichlet {τ : ℝ} (hτ : 0 < τ) : Differentiable ℂ (gaussDirichlet τ) := by
  intro w₀
  set R := ‖w₀‖ + 1
  have hU : IsOpen (Metric.ball w₀ 1) := Metric.isOpen_ball
  have hD : DifferentiableOn ℂ (gaussDirichlet τ) (Metric.ball w₀ 1) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (summable_inv_succ_sq.mul_left (Real.exp ((R + 2) ^ 2 / (4 * τ))))
      (fun n => ?_) hU (fun n w hw => norm_gaussDirichletTerm_le hτ n ?_)
    · intro w _
      unfold gaussDirichletTerm
      have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      exact (((differentiableAt_id.neg).const_cpow (Or.inl hn)).const_mul _).differentiableWithinAt
    · have h1 : ‖w - w₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
      have h2 : ‖w‖ ≤ ‖w₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' w w₀
        linarith
      have := neg_le_abs w.re
      linarith [Complex.abs_re_le_norm w]
  exact (hD w₀ (Metric.mem_ball_self one_pos)).differentiableAt (hU.mem_nhds (Metric.mem_ball_self one_pos))

theorem norm_gaussDirichlet_le {τ R : ℝ} (hτ : 0 < τ) {w : ℂ} (hw : -w.re ≤ R) :
    ‖gaussDirichlet τ w‖ ≤ Real.exp ((R + 2) ^ 2 / (4 * τ)) * 2 := by
  have hs := summable_inv_succ_sq
  refine (norm_tsum_le_tsum_norm (summable_gaussDirichletTerm hτ w).norm).trans ?_
  refine ((summable_gaussDirichletTerm hτ w).norm.tsum_le_tsum
    (fun n => norm_gaussDirichletTerm_le hτ n hw) (hs.mul_left _)).trans ?_
  rw [tsum_mul_left, hasSum_inv_add_one_sq.tsum_eq]
  gcongr
  exact pi_sq_div_six_le_two

/-- **Order at most two.** -/
theorem norm_gaussDirichlet_le_exp {τ : ℝ} (hτ : 0 < τ) (w : ℂ) :
    ‖gaussDirichlet τ w‖ ≤ Real.exp ((1 / τ + 1) * (1 + ‖w‖) ^ 2) := by
  have hR : -w.re ≤ ‖w‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm w)
  refine (norm_gaussDirichlet_le hτ hR).trans ?_
  have h2 : (2 : ℝ) ≤ Real.exp ((1 + ‖w‖) ^ 2) := by
    have h1 : (1 : ℝ) ≤ (1 + ‖w‖) ^ 2 := by nlinarith [norm_nonneg w]
    have := Real.add_one_le_exp ((1 + ‖w‖) ^ 2)
    linarith
  have h3 : (‖w‖ + 2) ^ 2 / (4 * τ) ≤ (1 + ‖w‖) ^ 2 / τ := by
    rw [div_le_div_iff₀ (by positivity) hτ]
    nlinarith [mul_nonneg hτ.le (show 0 ≤ 3 * ‖w‖ ^ 2 + 4 * ‖w‖ by positivity)]
  calc Real.exp ((‖w‖ + 2) ^ 2 / (4 * τ)) * 2
      ≤ Real.exp ((1 + ‖w‖) ^ 2 / τ) * Real.exp ((1 + ‖w‖) ^ 2) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; field_simp

/-! ## Behaviour to the right -/

theorem gaussDirichletTerm_zero (τ : ℝ) (w : ℂ) : gaussDirichletTerm τ 0 w = 1 := by
  simp [gaussDirichletTerm]

/-- `|F_τ(w) − 1| ≤ 2^{2 − Re w}` for `Re w ≥ 2`. -/
theorem norm_gaussDirichlet_sub_one_le {τ : ℝ} (hτ : 0 < τ) {w : ℂ} (hw : 2 ≤ w.re) :
    ‖gaussDirichlet τ w - 1‖ ≤ 2 ^ (2 - w.re) := by
  have hs := summable_gaussDirichletTerm hτ w
  rw [gaussDirichlet, hs.tsum_eq_zero_add, gaussDirichletTerm_zero, add_sub_cancel_left]
  have hs1 : Summable (fun n : ℕ => gaussDirichletTerm τ (n + 1) w) :=
    (summable_nat_add_iff 1).mpr hs
  have hb : ∀ n : ℕ, ‖gaussDirichletTerm τ (n + 1) w‖ ≤
      2 ^ (2 - w.re) * (((n : ℝ) + 2) ^ 2)⁻¹ := by
    intro n
    rw [norm_gaussDirichletTerm]
    have hn2 : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by linarith
    have he : Real.exp (-(τ * Real.log (((n + 1 : ℕ) : ℝ) + 1) ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have := sq_nonneg (Real.log (((n + 1 : ℕ) : ℝ) + 1)); nlinarith)
    have hsplit : (((n + 1 : ℕ) : ℝ) + 1) ^ (-w.re) =
        (((n + 1 : ℕ) : ℝ) + 1) ^ (2 - w.re) * ((((n + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hpos.le, ← Real.rpow_add hpos]
      congr 1; push_cast; ring
    have hpow : (((n + 1 : ℕ) : ℝ) + 1) ^ (2 - w.re) ≤ 2 ^ (2 - w.re) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith)
    have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
    rw [hsplit]
    calc Real.exp (-(τ * Real.log (((n + 1 : ℕ) : ℝ) + 1) ^ 2)) *
          ((((n + 1 : ℕ) : ℝ) + 1) ^ (2 - w.re) * ((((n + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹)
        ≤ 1 * (2 ^ (2 - w.re) * ((((n + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹) :=
          mul_le_mul he (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity)
            zero_le_one
      _ = 2 ^ (2 - w.re) * (((n : ℝ) + 2) ^ 2)⁻¹ := by rw [hcast, one_mul]
  have hsum2 := hasSum_inv_add_two_sq
  refine (norm_tsum_le_tsum_norm hs1.norm).trans ?_
  refine (hs1.norm.tsum_le_tsum hb (hsum2.summable.mul_left _)).trans ?_
  rw [tsum_mul_left, hsum2.tsum_eq]
  have h1 : Real.pi ^ 2 / 6 - 1 ≤ 1 := by linarith [pi_sq_div_six_le_two]
  have h2 : (0 : ℝ) ≤ 2 ^ (2 - w.re) := by positivity
  nlinarith

/-! ## Real values and the zero -/

theorem gaussDirichlet_ofReal_eq (τ σ : ℝ) :
    gaussDirichlet τ σ = ((∑' n : ℕ, Real.exp (-(τ * Real.log ((n : ℝ) + 1) ^ 2)) *
      ((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
  rw [gaussDirichlet, Complex.ofReal_tsum]
  congr 1; funext n
  rw [gaussDirichletTerm, Complex.ofReal_mul, Complex.ofReal_cpow (by positivity)]
  push_cast
  rfl

theorem one_lt_gaussDirichlet_ofReal {τ : ℝ} (hτ : 0 < τ) (σ : ℝ) :
    1 < ‖gaussDirichlet τ σ‖ := by
  set f : ℕ → ℝ := fun n => Real.exp (-(τ * Real.log ((n : ℝ) + 1) ^ 2)) * ((n : ℝ) + 1) ^ (-σ)
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hsum : Summable f := by
    have := (summable_gaussDirichletTerm hτ σ).norm
    refine this.congr fun n => ?_
    rw [norm_gaussDirichletTerm]; simp [f]
  have h2 := hsum.sum_le_tsum (Finset.range 2) (fun n _ => hf0 n)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h2
  have e0 : f 0 = 1 := by simp [f]
  have e1 : 0 < f 1 := by positivity
  rw [gaussDirichlet_ofReal_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg hf0)]
  change 1 < ∑' n, f n
  linarith

/-- The real polynomial of real parts: `Q(σ) = Re P(σ)` for real `σ`. -/
def rePoly (P : Polynomial ℂ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff i).re * Polynomial.X ^ i

theorem eval_rePoly (P : Polynomial ℂ) (σ : ℝ) : (rePoly P).eval σ = (P.eval (σ : ℂ)).re := by
  rw [rePoly, Polynomial.eval_finsetSum, Polynomial.eval_eq_sum_range, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]

/-- **`F_τ` has a zero.** -/
theorem exists_gaussDirichlet_eq_zero {τ : ℝ} (hτ : 0 < τ) : ∃ w, gaussDirichlet τ w = 0 := by
  by_contra hno
  simp only [not_exists] at hno
  obtain ⟨P, hP⟩ := GaloisForLFunctions.HTGeometry.exists_polynomial_exp_of_ne_zero_of_growth
    (differentiable_gaussDirichlet hτ) hno (C := 1 / τ + 1) (d := 2) (by positivity)
    (norm_gaussDirichlet_le_exp hτ)
  have hnorm : ∀ σ : ℝ, ‖gaussDirichlet τ σ‖ = Real.exp ((rePoly P).eval σ) := by
    intro σ; rw [hP, Complex.norm_exp, eval_rePoly]
  have hpos : ∀ σ : ℝ, 0 < (rePoly P).eval σ := by
    intro σ
    have := one_lt_gaussDirichlet_ofReal hτ σ
    rw [hnorm] at this
    exact Real.one_lt_exp_iff.mp this
  -- `Re P(σ) → 0`
  have hlim : Tendsto (fun σ : ℝ => (rePoly P).eval σ) atTop (𝓝 0) := by
    have hnorm_lim : Tendsto (fun σ : ℝ => ‖gaussDirichlet τ σ‖) atTop (𝓝 1) := by
      have h2 : Tendsto (fun σ : ℝ => (2 : ℝ) ^ (2 - σ)) atTop (𝓝 0) := by
        have : Tendsto (fun σ : ℝ => 2 - σ) atTop atBot :=
          (tendsto_atBot_add_const_left atTop (2 : ℝ) tendsto_neg_atTop_atBot).congr
            (fun σ => by ring)
        have h3 := Real.tendsto_exp_atBot.comp (this.atBot_mul_const (Real.log_pos one_lt_two))
        refine h3.congr fun σ => ?_
        rw [Function.comp, Real.rpow_def_of_pos two_pos, mul_comm]
      refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall
        fun σ => norm_nonneg _) ((eventually_ge_atTop 2).mono fun σ hσ => ?_) h2)
      rw [Real.norm_eq_abs]
      have h := abs_norm_sub_norm_le (gaussDirichlet τ σ) 1
      rw [norm_one] at h
      refine h.trans ?_
      have := norm_gaussDirichlet_sub_one_le hτ (w := σ) (by simpa using hσ)
      simpa using this
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hnorm_lim
    rw [Real.log_one] at this
    refine this.congr fun σ => ?_
    simp only [Function.comp, hnorm, Real.log_exp]
  by_cases hdeg : 0 < (rePoly P).degree
  · have h := (rePoly P).abs_tendsto_atTop hdeg
    have h' := hlim.abs
    rw [abs_zero] at h'
    exact not_tendsto_nhds_of_tendsto_atTop h 0 h'
  · have hC := Polynomial.eq_C_of_degree_le_zero (not_lt.mp hdeg)
    have hconst : ∀ σ : ℝ, (rePoly P).eval σ = (rePoly P).coeff 0 := by
      intro σ; rw [hC]; simp
    have h0 : (rePoly P).coeff 0 = 0 := by
      have := hlim.congr (fun σ => hconst σ)
      exact tendsto_nhds_unique tendsto_const_nhds this
    have := hpos 0
    rw [hconst, h0] at this
    exact lt_irrefl 0 this

/-! ## Almost periodicity -/

/-- `F_τ` is almost periodic on every vertical strip. -/
theorem isStripAlmostPeriodic_gaussDirichlet {τ : ℝ} (hτ : 0 < τ) (σ R : ℝ) :
    GaloisForLFunctions.IsStripAlmostPeriodic (gaussDirichlet τ) σ R := by
  refine GaloisForLFunctions.isStripAlmostPeriodic_dirichlet
    (fun k => ((Real.exp (-(τ * Real.log ((k : ℝ) + 1) ^ 2)) : ℝ) : ℂ))
    (fun k => Real.log ((k : ℝ) + 1)) _ fun r _ ε hε => ?_
  set K := Real.exp ((|σ| + |r| + 2) ^ 2 / (4 * τ))
  have htail := tendsto_sum_nat_add (fun n : ℕ => K * (((n : ℝ) + 1) ^ 2)⁻¹)
  obtain ⟨n, hn⟩ := (htail.eventually (eventually_le_nhds hε)).exists
  refine ⟨n, fun z hz => ?_⟩
  have hterm : ∀ k : ℕ, ((Real.exp (-(τ * Real.log ((k : ℝ) + 1) ^ 2)) : ℝ) : ℂ) *
      Complex.exp (-(Real.log ((k : ℝ) + 1) : ℂ) * z) = gaussDirichletTerm τ k z := by
    intro k
    rw [gaussDirichletTerm, Complex.cpow_def_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero k)]
    congr 2
    rw [show (((k + 1 : ℕ) : ℂ)) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
    ring
  simp_rw [hterm]
  have hs := summable_gaussDirichletTerm hτ z
  rw [gaussDirichlet, ← hs.sum_add_tsum_nat_add n, add_sub_cancel_left]
  have hre : -z.re ≤ |σ| + |r| := by
    have : |z.re - σ| ≤ r := hz
    have h1 := abs_le.mp this
    have h2 := le_abs_self r
    have h3 := neg_abs_le σ
    linarith [h1.1]
  have hb : ∀ k : ℕ, ‖gaussDirichletTerm τ (k + n) z‖ ≤ K * ((((k + n : ℕ) : ℝ) + 1) ^ 2)⁻¹ :=
    fun k => norm_gaussDirichletTerm_le hτ (k + n) hre
  have hsK : Summable (fun k : ℕ => K * ((((k + n : ℕ) : ℝ) + 1) ^ 2)⁻¹) :=
    (summable_nat_add_iff n).mpr (summable_inv_succ_sq.mul_left K)
  have hs1 : Summable (fun k : ℕ => gaussDirichletTerm τ (k + n) z) :=
    (summable_nat_add_iff n).mpr hs
  refine (norm_tsum_le_tsum_norm hs1.norm).trans ((hs1.norm.tsum_le_tsum hb hsK).trans ?_)
  exact hn

end

end RHTower
