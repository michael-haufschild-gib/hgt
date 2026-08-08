import GaloisForLFunctions.HTGeometry.PolynomialShiftHT
import GaloisForLFunctions.HTGeometry.ZetaMomentFunctionalEquation

/-!
# The formal zeta-moment series is hypertranscendental off the real axis

The exact functional-equation identity writes the coefficients `(-1)ⁿ ζ(-αn)` as

`C · Λⁿ · Γ(1 + αn) · (ζ(1 + αn)(1 - qⁿ))`.

Two exponentially small corrections remain.  The subdominant sine branch contributes `‖q‖ =
exp(-π|Im α|) < 1`, and the Dirichlet tail contributes `‖ζ(1 + αn) - 1‖ ≤ 2·2^{-n Re α}`.  Both are
below `exp(-c n)` for `c` half the smaller of the two rates, so past a finite index the coefficients
satisfy the complex factorial slope hypothesis exactly.

Correcting the finitely many initial coefficients changes the series by a polynomial, which the jet
translation absorbs.  Hence for `Re α > 0` and `Im α ≠ 0` the series `∑ (-1)ⁿ ζ(-αn) zⁿ` satisfies
no nonzero algebraic differential equation over `ℂ(z)`.
-/

open Complex Filter Topology MvPolynomial PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The size of the subdominant branch -/

/-- The subdominant sine branch has modulus `exp(-π|Im α|)`. -/
theorem norm_zetaMomentQ (α : ℂ) : ‖zetaMomentQ α‖ = Real.exp (-(Real.pi * |α.im|)) := by
  rw [zetaMomentQ, Complex.norm_exp, branchSign]
  split_ifs with h
  · rw [abs_of_pos h]
    simp [Complex.mul_re, Complex.mul_im]
  · rw [abs_of_nonpos (not_lt.mp h)]
    simp [Complex.mul_re, Complex.mul_im]

theorem norm_zetaMomentQ_le_one (α : ℂ) : ‖zetaMomentQ α‖ ≤ 1 := by
  rw [norm_zetaMomentQ]
  refine Real.exp_le_one_iff.mpr ?_
  have : (0 : ℝ) ≤ Real.pi * |α.im| := by positivity
  linarith

/-! ## The joint exponential rate -/

/-- The smaller of the Dirichlet-tail rate and the subdominant-branch rate. -/
def zetaMomentRate (α : ℂ) : ℝ := min (α.re * Real.log 2) (Real.pi * |α.im|)

theorem zetaMomentRate_pos {α : ℂ} (hre : 0 < α.re) (him : α.im ≠ 0) :
    0 < zetaMomentRate α := by
  refine lt_min (mul_pos hre (Real.log_pos (by norm_num))) ?_
  exact mul_pos Real.pi_pos (abs_pos.mpr him)

theorem zetaMomentRate_le_log {α : ℂ} : zetaMomentRate α ≤ α.re * Real.log 2 := min_le_left _ _

theorem zetaMomentRate_le_branch {α : ℂ} : zetaMomentRate α ≤ Real.pi * |α.im| := min_le_right _ _

/-! ## The relative error is exponentially small -/

/-- The subdominant branch, raised to the `n`-th power. -/
theorem norm_zetaMomentQ_pow_le (α : ℂ) (n : ℕ) :
    ‖zetaMomentQ α ^ n‖ ≤ Real.exp (-(zetaMomentRate α * (n : ℝ))) := by
  rw [norm_pow, norm_zetaMomentQ, ← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hle : zetaMomentRate α ≤ Real.pi * |α.im| := zetaMomentRate_le_branch
  nlinarith

/-- The Dirichlet tail on the ray. -/
theorem norm_zeta_rayPoint_sub_one_le {α : ℂ} {n : ℕ} (hn : 1 ≤ (n : ℝ) * α.re) :
    ‖riemannZeta (rayPoint α n) - 1‖ ≤ 2 * Real.exp (-(zetaMomentRate α * (n : ℝ))) := by
  have hre2 : 2 ≤ (rayPoint α n).re := by
    rw [rayPoint_re]
    linarith
  have hz := norm_riemannZeta_sub_one_le_rpow hre2
  have hsplit : (2 : ℝ) ^ (-(rayPoint α n).re)
      = (2 : ℝ) ^ (-(1 : ℝ)) * (2 : ℝ) ^ (-((n : ℝ) * α.re)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [rayPoint_re]
    ring
  have hhalf : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg_one]
    norm_num
  have hexp : (2 : ℝ) ^ (-((n : ℝ) * α.re))
      = Real.exp (Real.log 2 * (-((n : ℝ) * α.re))) :=
    Real.rpow_def_of_pos (by norm_num) _
  have hrate : Real.log 2 * (-((n : ℝ) * α.re)) ≤ -(zetaMomentRate α * (n : ℝ)) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hle : zetaMomentRate α ≤ α.re * Real.log 2 := zetaMomentRate_le_log
    nlinarith
  rw [hsplit, hhalf, hexp] at hz
  have hmono : Real.exp (Real.log 2 * (-((n : ℝ) * α.re)))
      ≤ Real.exp (-(zetaMomentRate α * (n : ℝ))) := Real.exp_le_exp.mpr hrate
  have hpos : (0 : ℝ) ≤ Real.exp (-(zetaMomentRate α * (n : ℝ))) := le_of_lt (Real.exp_pos _)
  nlinarith [Real.exp_pos (Real.log 2 * (-((n : ℝ) * α.re)))]

/-- **The relative error of the zeta-moment coefficients is exponentially small.** -/
theorem norm_zetaMomentErr_sub_one_le {α : ℂ} {n : ℕ} (hn : 1 ≤ (n : ℝ) * α.re) :
    ‖zetaMomentErr α n - 1‖ ≤ 5 * Real.exp (-(zetaMomentRate α * (n : ℝ))) := by
  set E : ℝ := Real.exp (-(zetaMomentRate α * (n : ℝ))) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hq := norm_zetaMomentQ_pow_le α n
  have hz := norm_zeta_rayPoint_sub_one_le hn
  have hqle1 : ‖zetaMomentQ α ^ n‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_zetaMomentQ_le_one α)
  have hval : zetaMomentErr α n - 1
      = (riemannZeta (rayPoint α n) - 1) * (1 - zetaMomentQ α ^ n) - zetaMomentQ α ^ n := by
    rw [zetaMomentErr]
    ring
  rw [hval]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul]
  have hfac : ‖(1 : ℂ) - zetaMomentQ α ^ n‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_one]
    linarith
  have hstep : ‖riemannZeta (rayPoint α n) - 1‖ * ‖(1 : ℂ) - zetaMomentQ α ^ n‖
      ≤ (2 * E) * 2 := by
    refine mul_le_mul hz hfac (norm_nonneg _) ?_
    positivity
  linarith

/-! ## Past a finite index the factorial slope hypothesis holds -/

/-- The error bound with a strictly smaller rate, valid eventually. -/
theorem eventually_norm_zetaMomentErr_sub_one_le {α : ℂ} (hre : 0 < α.re) (him : α.im ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      ‖zetaMomentErr α n - 1‖ ≤ Real.exp (-(zetaMomentRate α / 2) * (n : ℝ)) := by
  have hd : 0 < zetaMomentRate α := zetaMomentRate_pos hre him
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * α.re := by
    have hto : Tendsto (fun n : ℕ => α.re * (n : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hre hcast
    filter_upwards [hto.eventually_ge_atTop 1] with n hn
    linarith [hn]
  have h2 : ∀ᶠ n : ℕ in atTop, Real.log 5 ≤ zetaMomentRate α / 2 * (n : ℝ) := by
    have hto : Tendsto (fun n : ℕ => zetaMomentRate α / 2 * (n : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by linarith : (0 : ℝ) < zetaMomentRate α / 2) hcast
    exact hto.eventually_ge_atTop _
  filter_upwards [h1, h2] with n hn1 hn2
  refine le_trans (norm_zetaMomentErr_sub_one_le hn1) ?_
  have hlog : (5 : ℝ) ≤ Real.exp (zetaMomentRate α / 2 * (n : ℝ)) := by
    have h5 : (5 : ℝ) = Real.exp (Real.log 5) := (Real.exp_log (by norm_num)).symm
    rw [h5]
    exact Real.exp_le_exp.mpr hn2
  have hfac : Real.exp (-(zetaMomentRate α * (n : ℝ)))
      * Real.exp (zetaMomentRate α / 2 * (n : ℝ))
      = Real.exp (-(zetaMomentRate α / 2) * (n : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpos : 0 < Real.exp (-(zetaMomentRate α * (n : ℝ))) := Real.exp_pos _
  calc 5 * Real.exp (-(zetaMomentRate α * (n : ℝ)))
      ≤ Real.exp (zetaMomentRate α / 2 * (n : ℝ)) * Real.exp (-(zetaMomentRate α * (n : ℝ))) := by
        exact mul_le_mul_of_nonneg_right hlog (le_of_lt hpos)
    _ = Real.exp (-(zetaMomentRate α / 2) * (n : ℝ)) := by rw [mul_comm]; exact hfac

/-- The zeta-moment coefficients with the first `n₀` terms replaced by the exact factorial model. -/
def zetaMomentTrunc (α : ℂ) (n₀ n : ℕ) : ℂ :=
  if n < n₀ then slopeModel α (zetaMomentLam α) (zetaMomentConst α) n else zetaMomentCoeff α n

/-- **The truncated zeta-moment sequence has a complex factorial slope.** -/
theorem exists_zetaMomentTrunc_factorialSlope {α : ℂ} (hre : 0 < α.re) (him : α.im ≠ 0) :
    ∃ (n₀ : ℕ) (c : ℝ),
      FactorialSlope (zetaMomentTrunc α n₀) α (zetaMomentLam α) (zetaMomentConst α) c := by
  obtain ⟨n₁, hn₁⟩ :=
    Filter.eventually_atTop.mp (eventually_norm_zetaMomentErr_sub_one_le hre him)
  refine ⟨max n₁ 1, zetaMomentRate α / 2, hre, zetaMomentConst_ne_zero α,
    zetaMomentLam_ne_zero α, by linarith [zetaMomentRate_pos hre him], ?_⟩
  intro n
  by_cases hlt : n < max n₁ 1
  · rw [zetaMomentTrunc, if_pos hlt, slopeModel, sub_self, norm_zero]
    positivity
  · have hge : max n₁ 1 ≤ n := not_lt.mp hlt
    have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) hge
    have hnne : n ≠ 0 := by
      have := le_trans (le_max_right _ _) hge
      omega
    rw [zetaMomentTrunc, if_neg hlt, zetaMomentCoeff_eq hre hnne]
    set M : ℂ := zetaMomentConst α * zetaMomentLam α ^ n * Complex.Gamma (rayPoint α n) with hM
    have hrewrite : M * zetaMomentErr α n - M = M * (zetaMomentErr α n - 1) := by ring
    rw [hrewrite, norm_mul, mul_comm (Real.exp (-(zetaMomentRate α / 2) * (n : ℝ))) ‖M‖]
    exact mul_le_mul_of_nonneg_left (hn₁ n hn1) (norm_nonneg _)

/-! ## The zeta-moment hypertranscendence theorem -/

/-- **The formal zeta-moment series is hypertranscendental for every nonreal factorial slope.**
For `Re α > 0` and `Im α ≠ 0` the series `∑ (-1)ⁿ ζ(-αn) zⁿ` satisfies no nonzero algebraic
differential equation with polynomial coefficients. -/
theorem zetaMoment_aeval_formalJets_ne_zero {α : ℂ} (hre : 0 < α.re) (him : α.im ≠ 0)
    (m : ℕ) (P : MvPolynomial (Fin (m + 2)) ℂ) (hP : P ≠ 0) :
    aeval (formalJetsOver m (PowerSeries.mk (zetaMomentCoeff α))) P ≠ 0 := by
  obtain ⟨n₀, c, hyp⟩ := exists_zetaMomentTrunc_factorialSlope hre him
  have hg : ∀ Q : MvPolynomial (Fin (m + 2)) ℂ, Q ≠ 0 →
      aeval (formalJetsOver m (PowerSeries.mk (zetaMomentTrunc α n₀))) Q ≠ 0 :=
    fun Q hQ => aeval_formalJets_ne_zero hyp him m Q hQ
  refine aeval_formalJets_ne_zero_of_polySeries_sub ?_ hg P hP
  refine ⟨n₀, fun n hn => ?_⟩
  rw [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk, zetaMomentTrunc,
    if_neg (not_lt.mpr hn), sub_self]

end

end GaloisForLFunctions.HTGeometry
