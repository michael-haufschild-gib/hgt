import GaloisForLFunctions.StripBochnerWeilForcing.PositiveDefiniteSectionsAreCompletelyMonotone
import GaloisForLFunctions.StripBochnerWeilForcing.StripReflectionRigidity
import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveMeasureRigidityFromTheBareFunctionalEquation
import GaloisForLFunctions.RHTower.DigammaLeLog
import GaloisForLFunctions.RHTower.WeilDilationCriticalLineShift

/-!
# The simple-pole class is `ζ`

**Theorem** (`completedPositiveSystem_one_one_eq_zeta`). Every completed positive system of pole
budget `κ = 1` and degree `d = 1` is a real multiple of `ζ`: `F = Kζ` on `Re s > 1`, `K ≠ 0`.

**Proof.**
* `G = −F'/F` has positive-definite vertical sections, so its even derivatives are nonnegative on
  `(1, ∞)`. Hadamard positivity `Re Λ'/Λ ≥ 0` (`sum_orbit_resolvent_le_re_logDeriv`) and
  `Re ψ(y) ≤ log y` bound `G(x) ≤ 4√x`, which forces the odd derivatives to be nonpositive. So
  `F/F(2)` is completely monotone on `(1, ∞)`, and by Bernstein–Widder `F/F(2) = ∫ u^{−s} dμ` on
  `Re s > 5/4` with `μ ≥ 0` carried by `[1, ∞)` (`exists_dirichletMeasure_of_posDef_sections`).
* Write `Λ/F(2) = c₀ + s(s − 1)P(s)` with `P` entire, and `h(s) = Γ_ℝ(s) − 2/s` extended across
  `0` (`gammaℝReg`). Then `E = P + (c₀/2)(h(s) − h(s − 1))` is holomorphic and of finite order on
  `−1/2 ≤ Re s ≤ 3/2`, and `Γ_ℝ(s) D_μ(s) = E(s) − (c₀/2)Γ_ℝ(s) + (c₀/2)Γ_ℝ(s − 1)` on
  `Re s = 3/2` and, by `Λ(1 − s) = Λ(s)`, on `Re s = −1/2`.
* Positive-measure rigidity from the bare functional equation
  (`measure_eq_of_completed_functional_equation_of_finiteOrder`) gives `μ = m Σ_{k ≥ 1} δ_k`, so
  `F = F(2) m ζ` on `Re s > 5/4`, hence on `Re s > 1`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.StripBochnerWeilForcing

open MultiplicativePositivityGeometry GaloisForLFunctions.HTGeometry

/-! ## 1. The regularized Gamma factor `Γ_ℝ(s) − 2/s` -/

/-- `k(s) = π^{−s/2} Γ(1 + s/2)`, so that `Γ_ℝ(s) = 2 k(s)/s`. -/
def gammaℝNum (s : ℂ) : ℂ := (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (1 + s / 2)

theorem differentiableOn_gammaℝNum : DifferentiableOn ℂ gammaℝNum {s : ℂ | -2 < s.re} := by
  intro s hs
  have hs' : -2 < s.re := hs
  have hG : DifferentiableAt ℂ Complex.Gamma (1 + s / 2) := by
    refine Complex.differentiableAt_Gamma _ fun m hm => ?_
    have h := congrArg Complex.re hm
    simp only [Complex.add_re, Complex.one_re, Complex.div_re, Complex.neg_re,
      Complex.natCast_re] at h
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    norm_num at h
    nlinarith
  have hpow : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  exact (hpow.mul (hG.comp s (by fun_prop))).differentiableWithinAt

theorem gammaℝNum_zero : gammaℝNum 0 = 1 := by
  simp [gammaℝNum]

/-- The regularized Gamma factor `h(s) = 2 (k(s) − k(0))/s`, equal to `Γ_ℝ(s) − 2/s` off `0`. -/
def gammaℝReg (s : ℂ) : ℂ := 2 * dslope gammaℝNum 0 s

theorem differentiableOn_gammaℝReg : DifferentiableOn ℂ gammaℝReg {s : ℂ | -2 < s.re} := by
  have hU : {s : ℂ | -2 < s.re} ∈ 𝓝 (0 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  exact ((differentiableOn_dslope hU).mpr differentiableOn_gammaℝNum).const_mul 2

theorem gammaℝReg_eq {s : ℂ} (hs : s ≠ 0) : gammaℝReg s = Complex.Gammaℝ s - 2 / s := by
  unfold gammaℝReg
  rw [dslope_of_ne _ hs, slope_def_field, gammaℝNum_zero, sub_zero, gammaℝNum,
    Complex.Gammaℝ_def]
  have hs2 : s / 2 ≠ 0 := div_ne_zero hs two_ne_zero
  rw [add_comm (1 : ℂ) (s / 2), Complex.Gamma_add_one _ hs2]
  field_simp

/-! ## 2. Bounds on the strip -/

theorem exists_bound_gammaℝReg :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, -3 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖gammaℝReg s‖ ≤ B := by
  have hpi := Real.pi_pos
  -- On the unit ball, by continuity.
  have hcont : ContinuousOn gammaℝReg (Metric.closedBall (0 : ℂ) 1) := by
    refine differentiableOn_gammaℝReg.continuousOn.mono fun s hs => ?_
    have h1 := Complex.abs_re_le_norm s
    rw [Metric.mem_closedBall, dist_zero_right] at hs
    show -2 < s.re
    linarith [abs_le.mp (h1.trans hs)]
  obtain ⟨B₁, hB₁⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont
  -- Real Gamma is bounded on `[1/4, 7/4]`.
  have hΓc : ContinuousOn Real.Gamma (Icc (1 / 4 : ℝ) (7 / 4)) := fun x hx =>
    (Real.differentiableAt_Gamma fun m hm => by
      have : (0 : ℝ) < x := by linarith [hx.1]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith).continuousAt.continuousWithinAt
  obtain ⟨B₂, hB₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hΓc
  refine ⟨max (max B₁ 0) (2 * (Real.pi ^ (3 / 4 : ℝ) * max B₂ 0 + 1)), by positivity,
    fun s h1 h2 => ?_⟩
  by_cases hs : ‖s‖ ≤ 1
  · have := hB₁ s (by rw [Metric.mem_closedBall, dist_zero_right]; exact hs)
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  · push Not at hs
    have hs0 : s ≠ 0 := fun h => by rw [h, norm_zero] at hs; linarith
    have hk : ‖gammaℝNum s‖ ≤ Real.pi ^ (3 / 4 : ℝ) * max B₂ 0 := by
      unfold gammaℝNum
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpi]
      have hre : (-s / 2).re = -s.re / 2 := by simp
      have hz : 0 < (1 + s / 2).re := by simp; linarith
      have hΓ := norm_Gamma_le_Gamma_re hz
      have hzre : (1 + s / 2).re = 1 + s.re / 2 := by simp
      rw [hzre] at hΓ
      have hmem : 1 + s.re / 2 ∈ Icc (1 / 4 : ℝ) (7 / 4) := ⟨by linarith, by linarith⟩
      have hb := (hB₂ _ hmem)
      rw [Real.norm_eq_abs] at hb
      have hpow : Real.pi ^ (-s.re / 2) ≤ Real.pi ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      rw [hre]
      exact mul_le_mul hpow (hΓ.trans ((le_abs_self _).trans (hb.trans (le_max_left _ _))))
        (norm_nonneg _) (by positivity)
    unfold gammaℝReg
    rw [dslope_of_ne _ hs0, slope_def_field, gammaℝNum_zero, sub_zero, norm_mul, norm_div,
      RCLike.norm_ofNat]
    have h3 : ‖gammaℝNum s - 1‖ ≤ ‖gammaℝNum s‖ + 1 := by
      refine (norm_sub_le _ _).trans ?_
      simp
    calc 2 * (‖gammaℝNum s - 1‖ / ‖s‖) ≤ 2 * (‖gammaℝNum s - 1‖ / 1) := by
          gcongr
      _ ≤ 2 * (Real.pi ^ (3 / 4 : ℝ) * max B₂ 0 + 1) := by rw [div_one]; gcongr; linarith
      _ ≤ _ := le_max_right _ _

/-- `C (1 + x) log(2 + x) ≤ K + x³` for `x ≥ 0`. -/
theorem orderOne_le_cube {C : ℝ} (hC : 0 < C) :
    ∃ K : ℝ, ∀ x : ℝ, 0 ≤ x → C * (1 + x) * Real.log (2 + x) ≤ K + x ^ 3 := by
  refine ⟨2 * C + 8 * C ^ 3, fun x hx => ?_⟩
  have hlog : Real.log (2 + x) ≤ 1 + x := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + x by linarith)
    linarith
  have h1 : C * (1 + x) * Real.log (2 + x) ≤ C * (1 + x) * (1 + x) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2 : 2 * C * x ^ 2 ≤ x ^ 3 + 8 * C ^ 3 := by
    rcases le_or_gt (2 * C) x with h | h
    · nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h), pow_pos hC 3]
    · have : x ^ 2 ≤ 4 * C ^ 2 := by nlinarith
      nlinarith
  nlinarith [sq_nonneg (1 - x)]

/-! ## 3. The real axis and the growth of `−F'/F` -/

namespace CompletedPositiveSystem

variable {κ d : ℕ} {F Λ : ℂ → ℂ}

theorem im_Λ_ofReal (hS : CompletedPositiveSystem κ d F Λ) (x : ℝ) : (Λ x).im = 0 := by
  have h := hS.conj_Λ (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

theorem Gammaℝ_ofReal' (x : ℝ) :
    Complex.Gammaℝ (x : ℂ) = ((Real.pi ^ (-x / 2) * Real.Gamma (x / 2) : ℝ) : ℂ) := by
  rw [Complex.Gammaℝ_def, show -(x : ℂ) / 2 = ((-x / 2 : ℝ) : ℂ) by push_cast; ring,
    show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal]
  push_cast
  ring

/-- `F` is real on `(1, ∞)`. -/
theorem im_F_ofReal (hS : CompletedPositiveSystem κ d F Λ) {x : ℝ} (hx : 1 < x) :
    (F x).im = 0 := by
  have hcomp := hS.completed_eq (x : ℂ) (by simpa using hx)
  set D : ℝ := (x * (x - 1)) ^ κ * (Real.pi ^ (-x / 2) * Real.Gamma (x / 2)) ^ d with hD
  have hDpos : 0 < D := by
    have : 0 < x * (x - 1) := by nlinarith
    have : 0 < Real.Gamma (x / 2) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  have hDc : ((x : ℂ) * ((x : ℂ) - 1)) ^ κ * Complex.Gammaℝ (x : ℂ) ^ d = (D : ℂ) := by
    rw [Gammaℝ_ofReal', hD]
    push_cast
    ring
  rw [hDc] at hcomp
  have h := congrArg Complex.im hcomp
  rw [im_Λ_ofReal hS, Complex.im_ofReal_mul] at h
  have := mul_eq_zero.mp h.symm
  rcases this with h0 | h0
  · linarith
  · exact h0

/-- **Growth of `−F'/F` on the real axis** for `κ = d = 1`: `Re(−F'/F)(x) ≤ 4√x` for `x ≥ 2`, from
Hadamard positivity of `Re Λ'/Λ` and `Re ψ ≤ log`. -/
theorem re_neg_logDeriv_le_sqrt (hS : CompletedPositiveSystem 1 1 F Λ) {x : ℝ} (hx : 2 ≤ x) :
    (-logDeriv F (x : ℂ)).re ≤ 4 * Real.sqrt x := by
  have hx1 : 1 < (x : ℂ).re := by simp; linarith
  have hΛ : 0 ≤ (logDeriv Λ (x : ℂ)).re := by
    have h := sum_orbit_resolvent_le_re_logDeriv hS (r := 0) Fin.elim0 Fin.elim0
      (fun ℓ => Fin.elim0 ℓ) (fun ℓ => Fin.elim0 ℓ) (fun ℓ => Fin.elim0 ℓ) hx1
    simpa using h
  have hΓ : (logDeriv Complex.Gammaℝ (x : ℂ)).re ≤ Real.log x := by
    rw [RHTower.logDeriv_Gammaℝ_eq_gammaRLogDeriv (by simp; linarith), RHTower.gammaRLogDeriv]
    have hd := RHTower.re_digamma_le_log (y := x / 2) (by linarith)
    have e : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.sub_re, Complex.div_ofNat_re, Complex.div_ofNat_re, Complex.ofReal_re]
    have hlog2 : Real.log (x / 2) ≤ Real.log x :=
      Real.log_le_log (by linarith) (by linarith)
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hrat : ((1 : ℂ) * (1 / (x : ℂ) + 1 / ((x : ℂ) - 1))).re ≤ 3 / 2 := by
    have e : (1 : ℂ) * (1 / (x : ℂ) + 1 / ((x : ℂ) - 1)) = ((1 / x + 1 / (x - 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.ofReal_re]
    have h1 : 1 / x ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have h2 : 1 / (x - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hsqrt : Real.log x ≤ 2 * Real.sqrt x := by
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have h := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt (by linarith)] at h
    linarith
  have hs1 : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [hS.neg_logDeriv_F_eq hx1]
  simp only [Nat.cast_one, Complex.sub_re, Complex.add_re, one_mul] at hrat ⊢
  linarith

end CompletedPositiveSystem

/-! ## 4. The class collapse -/

theorem integral_cpow_neg_sum_dirac {s : ℂ} (hs : 1 < s.re) :
    ∫ u : ℝ, (u : ℂ) ^ (-s) ∂(Measure.sum fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) =
      riemannZeta s := by
  have hsmul : (Measure.sum fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) =
      Measure.sum (fun k : ℕ => (1 : ℝ≥0∞) • Measure.dirac ((k : ℝ) + 1)) := by
    congr 1; ext k : 1; simp
  rw [hsmul, integral_sum_dirac (fun _ => ENNReal.one_ne_top),
    zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  refine tsum_congr fun k => ?_
  rw [ENNReal.toReal_one, one_smul, Complex.cpow_neg, one_div]
  push_cast
  rfl

/-- **The `κ = 1` class collapse.** Every completed positive system of pole budget `1` and degree
`1` is a nonzero real multiple of `ζ` on `Re s > 1`. -/
theorem completedPositiveSystem_one_one_eq_zeta {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem 1 1 F Λ) :
    ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * riemannZeta s := by
  have hpi := Real.pi_pos
  set U : Set ℂ := {s : ℂ | 1 < s.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  -- Normalize by `F(2)`, which is real and nonzero.
  have h2 : (1 : ℝ) < 2 := by norm_num
  set c : ℝ := (F ((2 : ℝ) : ℂ)).re with hcdef
  have hF2 : F ((2 : ℝ) : ℂ) = (c : ℂ) :=
    Complex.ext (by simp [hcdef]) (by rw [Complex.ofReal_im]; exact hS.im_F_ofReal h2)
  have hc : c ≠ 0 := by
    intro h0
    apply hS.ne_zero_F ((2 : ℝ) : ℂ) (by simp)
    rw [hF2, h0, Complex.ofReal_zero]
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  set F₁ : ℂ → ℂ := fun s => F s / (c : ℂ) with hF₁def
  have hF₁d : DifferentiableOn ℂ F₁ U := hS.diffOn_F.div_const _
  have hF₁0 : ∀ s : ℂ, 1 < s.re → F₁ s ≠ 0 := fun s hs =>
    div_ne_zero (hS.ne_zero_F s hs) hcC
  have hF₁real : ∀ x : ℝ, 1 < x → (F₁ x).im = 0 := by
    intro x hx
    simp only [hF₁def, Complex.div_ofReal_im, hS.im_F_ofReal hx, zero_div]
  have hF₁two : (F₁ ((2 : ℝ) : ℂ)).re = 1 := by
    simp only [hF₁def, hF2, div_self hcC, Complex.one_re]
  have hF₁pos : ∀ x : ℝ, 1 < x → 0 < (F₁ x).re := by
    intro x hx
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousOn (fun y : ℝ => (F₁ y).re) (uIcc 2 x) := by
      intro y hy
      have hy1 : 1 < y := by
        rcases le_total 2 x with h | h
        · rw [uIcc_of_le h] at hy; linarith [hy.1]
        · rw [uIcc_of_ge h] at hy; linarith [hy.1]
      have hyU : (y : ℂ) ∈ U := by simpa [hUdef] using hy1
      have hFy : ContinuousAt F₁ (y : ℂ) :=
        ((hF₁d _ hyU).differentiableAt (hU.mem_nhds hyU)).continuousAt
      exact (Complex.continuous_re.continuousAt.comp
        (hFy.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
    have hmem : (0 : ℝ) ∈ uIcc ((F₁ ((2 : ℝ) : ℂ)).re) ((F₁ x).re) := by
      rw [hF₁two]; exact ⟨min_le_of_right_le hneg, le_max_of_le_left zero_le_one⟩
    obtain ⟨y, hy, hy0⟩ := intermediate_value_uIcc hcont hmem
    have hy1 : 1 < y := by
      rcases le_total 2 x with h | h
      · rw [uIcc_of_le h] at hy; linarith [hy.1]
      · rw [uIcc_of_ge h] at hy; linarith [hy.1]
    apply hF₁0 (y : ℂ) (by simpa using hy1)
    exact Complex.ext (by simpa using hy0) (by simpa using hF₁real y hy1)
  have hlog : ∀ s : ℂ, 1 < s.re → logDeriv F₁ s = logDeriv F s := by
    intro s hs
    rw [logDeriv_apply, logDeriv_apply, hF₁def, deriv_div_const]
    field_simp
  have hpd₁ : ∀ σ : ℝ, 1 < σ →
      IsPosDef fun u : ℝ => (-logDeriv F₁ ((σ : ℂ) + (u : ℂ) * I)).re := by
    intro σ hσ
    have h := (hS.posDef_neg_logDeriv hσ).posDef
    have e : (fun u : ℝ => (-logDeriv F₁ ((σ : ℂ) + (u : ℂ) * I)).re) =
        fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re := by
      funext u
      rw [hlog _ (by simpa using hσ)]
    rw [e]
    exact h
  have hgrowth₁ : ∀ x : ℝ, 2 ≤ x → (-logDeriv F₁ (x : ℂ)).re ≤ 4 * Real.sqrt x := by
    intro x hx
    rw [hlog _ (by simp; linarith)]
    exact hS.re_neg_logDeriv_le_sqrt hx
  obtain ⟨μ, hμ1, hrep⟩ := exists_dirichletMeasure_of_posDef_sections (a := 1) (b := 5 / 4)
    (by norm_num) hF₁d hF₁0 hF₁real hF₁pos hpd₁ hgrowth₁
  -- The inverse-`3/2` moment.
  have hae1 : ∀ᵐ u ∂μ, (1 : ℝ) ≤ u :=
    ArithmeticPositiveDuality.ae_one_le_of_measure_Iio_one_eq_zero hμ1
  have hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) μ := by
    have h := (hrep (3 / 2 : ℂ) (by norm_num)).1
    refine h.norm.congr ?_
    filter_upwards [hae1] with u hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    norm_num
  -- The completed function divided by `F(2)`, and its entire part.
  set Λ₁ : ℂ → ℂ := fun s => Λ s / (c : ℂ) with hΛ₁def
  have hΛ₁d : Differentiable ℂ Λ₁ := hS.entire_Λ.div_const _
  have hsym₁ : ∀ s, Λ₁ (1 - s) = Λ₁ s := fun s => by simp only [hΛ₁def, hS.sym_Λ]
  have hcomp₁ : ∀ s : ℂ, 1 < s.re → Λ₁ s = s * (s - 1) * Complex.Gammaℝ s * F₁ s := by
    intro s hs
    simp only [hΛ₁def, hF₁def, hS.completed_eq s hs, pow_one]
    field_simp
  set c₀ : ℂ := Λ₁ 0 with hc₀
  set P : ℂ → ℂ := dslope (dslope Λ₁ 0) 1 with hPdef
  have hPd : Differentiable ℂ P := by
    have h1 : DifferentiableOn ℂ (dslope Λ₁ 0) univ :=
      (differentiableOn_dslope Filter.univ_mem).mpr hΛ₁d.differentiableOn
    have h2 := (differentiableOn_dslope (c := (1 : ℂ)) Filter.univ_mem).mpr h1
    exact fun z => (h2 z (mem_univ z)).differentiableAt Filter.univ_mem
  have hΛP : ∀ s, Λ₁ s = c₀ + s * (s - 1) * P s := by
    intro s
    have hD1 : dslope Λ₁ 0 1 = 0 := by
      rw [dslope_of_ne _ one_ne_zero, slope_def_field, sub_zero, div_one]
      have := hsym₁ 0
      rw [sub_zero] at this
      rw [this, sub_self]
    have e1 := sub_smul_dslope Λ₁ 0 s
    have e2 := sub_smul_dslope (dslope Λ₁ 0) 1 s
    rw [hD1, sub_zero, smul_eq_mul] at e2
    rw [sub_zero, smul_eq_mul, ← e2] at e1
    rw [hc₀, hPdef]
    linear_combination -e1
  -- The holomorphic remainder `E`.
  set E : ℂ → ℂ := fun s => P s + c₀ / 2 * (gammaℝReg s - gammaℝReg (s - 1)) with hEdef
  have hstrip : ∀ s ∈ GaloisForLFunctions.HTGeometry.verticalStrip (-1 / 2) (3 / 2), -1 / 2 ≤ s.re ∧ s.re ≤ 3 / 2 :=
    fun s hs => hs
  have hEd : DifferentiableOn ℂ E (GaloisForLFunctions.HTGeometry.verticalStrip (-1 / 2) (3 / 2)) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have hg1 : DifferentiableAt ℂ gammaℝReg s :=
      (differentiableOn_gammaℝReg s (by show -2 < s.re; linarith)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by show -2 < s.re; linarith))
    have hg2 : DifferentiableAt ℂ gammaℝReg (s - 1) :=
      (differentiableOn_gammaℝReg (s - 1) (by show -2 < (s - 1).re; simp; linarith))
        |>.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by show -2 < (s - 1).re; simp; linarith))
    exact ((hPd s).add ((hg1.sub (hg2.comp s (differentiableAt_id.sub_const 1))).const_mul
      _)).differentiableWithinAt
  have hEid : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      E s + ((-c₀ / 2) * Complex.Gammaℝ s + (c₀ / 2) * Complex.Gammaℝ (s - 1)) =
        Λ₁ s / (s * (s - 1)) := by
    intro s hs0 hs1
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    simp only [hEdef]
    rw [gammaℝReg_eq hs0, gammaℝReg_eq hs1', hΛP s]
    field_simp
    ring
  -- Finite order on the strip.
  obtain ⟨Cl, hCl, hΛbound⟩ := hS.orderOne_Λ
  obtain ⟨K₁, hK₁⟩ := orderOne_le_cube hCl
  obtain ⟨Bh, hBh0, hBh⟩ := exists_bound_gammaℝReg
  obtain ⟨BP, hBP⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn
    hPd.continuous.continuousOn
  set C₀ : ℝ := max BP 0 + ‖c₀‖ + Real.exp K₁ / |c| + ‖c₀‖ * Bh with hC₀
  have hfin : ∀ s ∈ GaloisForLFunctions.HTGeometry.verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C₀ * Real.exp (‖s‖ ^ (3 : ℝ)) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have hexp1 : 1 ≤ Real.exp (‖s‖ ^ (3 : ℝ)) := Real.one_le_exp (by positivity)
    have hΛ₁b : ‖Λ₁ s‖ ≤ Real.exp K₁ / |c| * Real.exp (‖s‖ ^ (3 : ℝ)) := by
      rw [hΛ₁def, norm_div, Complex.norm_real, Real.norm_eq_abs]
      have hb := hΛbound s
      have hk := hK₁ ‖s‖ (norm_nonneg s)
      have hpow : ‖s‖ ^ (3 : ℝ) = ‖s‖ ^ 3 := by exact_mod_cast Real.rpow_natCast ‖s‖ 3
      rw [div_mul_eq_mul_div, le_div_iff₀ (abs_pos.mpr hc), div_mul_cancel₀ _
        (abs_pos.mpr hc).ne', ← Real.exp_add, hpow]
      exact hb.trans (Real.exp_le_exp.mpr (by unfold HTGeometry.orderOneWeight; linarith))
    have hPb : ‖P s‖ ≤ max BP 0 + ‖c₀‖ + ‖Λ₁ s‖ := by
      by_cases hs2 : ‖s‖ ≤ 2
      · have := hBP s (by rw [Metric.mem_closedBall, dist_zero_right]; exact hs2)
        have := norm_nonneg c₀
        have := norm_nonneg (Λ₁ s)
        linarith [le_max_left BP 0]
      · push Not at hs2
        have hs0 : s ≠ 0 := fun h => by rw [h, norm_zero] at hs2; linarith
        have hs1 : 1 ≤ ‖s - 1‖ := by
          have := norm_sub_norm_le s 1
          rw [norm_one] at this
          linarith
        have hden : 1 ≤ ‖s * (s - 1)‖ := by
          rw [norm_mul]; nlinarith
        have hPs : P s = (Λ₁ s - c₀) / (s * (s - 1)) := by
          rw [hΛP s]
          field_simp [hs0, sub_ne_zero.mpr (show s ≠ 1 from fun h => by
            rw [h, norm_one] at hs2; linarith)]
          ring
        rw [hPs, norm_div]
        calc ‖Λ₁ s - c₀‖ / ‖s * (s - 1)‖ ≤ ‖Λ₁ s - c₀‖ / 1 :=
              div_le_div_of_nonneg_left (norm_nonneg _) zero_lt_one hden
          _ ≤ ‖Λ₁ s‖ + ‖c₀‖ := by rw [div_one]; exact norm_sub_le _ _
          _ ≤ max BP 0 + ‖c₀‖ + ‖Λ₁ s‖ := by linarith [le_max_right BP 0]
    have hgb : ‖c₀ / 2 * (gammaℝReg s - gammaℝReg (s - 1))‖ ≤ ‖c₀‖ * Bh := by
      have hb1 := hBh s (by linarith) (by linarith)
      have hb2 := hBh (s - 1) (by simp; linarith) (by simp; linarith)
      rw [norm_mul, norm_div, RCLike.norm_ofNat]
      calc ‖c₀‖ / 2 * ‖gammaℝReg s - gammaℝReg (s - 1)‖ ≤ ‖c₀‖ / 2 * (Bh + Bh) := by
            gcongr
            exact (norm_sub_le _ _).trans (add_le_add hb1 hb2)
        _ = ‖c₀‖ * Bh := by ring
    calc ‖E s‖ ≤ ‖P s‖ + ‖c₀ / 2 * (gammaℝReg s - gammaℝReg (s - 1))‖ := norm_add_le _ _
      _ ≤ (max BP 0 + ‖c₀‖ + Real.exp K₁ / |c| * Real.exp (‖s‖ ^ (3 : ℝ))) + ‖c₀‖ * Bh := by
          linarith
      _ ≤ C₀ * Real.exp (‖s‖ ^ (3 : ℝ)) := by
          have hBP0 : 0 ≤ max BP 0 := le_max_right _ _
          have hc0 : 0 ≤ ‖c₀‖ := norm_nonneg _
          have hq : 0 ≤ Real.exp K₁ / |c| := by positivity
          rw [hC₀]
          nlinarith [mul_le_mul_of_nonneg_left hexp1 hBP0, mul_le_mul_of_nonneg_left hexp1 hc0,
            mul_le_mul_of_nonneg_left hexp1 (mul_nonneg hc0 hBh0)]
  -- The functional equation on the two edges.
  have hR : ∀ s : ℂ, s.re = 3 / 2 → Complex.Gammaℝ s * ArithmeticPositiveDuality.measureDirichlet μ s =
      E s + ((-c₀ / 2) * Complex.Gammaℝ s + (c₀ / 2) * Complex.Gammaℝ (s - 1)) := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    rw [hEid s hs0 hs1, ArithmeticPositiveDuality.measureDirichlet,
      ← (hrep s (by rw [hs]; norm_num)).2, hcomp₁ s (by rw [hs]; norm_num)]
    field_simp [hs0, sub_ne_zero.mpr hs1]
  have hL : ∀ s : ℂ, s.re = -1 / 2 →
      Complex.Gammaℝ (1 - s) * ArithmeticPositiveDuality.measureDirichlet μ (1 - s) =
        E s + ((-c₀ / 2) * Complex.Gammaℝ s + (c₀ / 2) * Complex.Gammaℝ (s - 1)) := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    have h1s : (1 - s).re = 3 / 2 := by simp [hs]; norm_num
    rw [hEid s hs0 hs1, ArithmeticPositiveDuality.measureDirichlet,
      ← (hrep (1 - s) (by rw [h1s]; norm_num)).2, ← hsym₁ s,
      hcomp₁ (1 - s) (by rw [h1s]; norm_num)]
    have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    field_simp [hs0, sub_ne_zero.mpr hs1, hs1']
    ring
  obtain ⟨-, -, hm, hμeq⟩ :=
    ArithmeticPositiveDuality.measure_eq_of_completed_functional_equation_of_finiteOrder
      hμ1 hmom hEd hfin hR hL
  set m : ℝ := -2 * (-c₀ / 2).re with hmdef
  -- `F₁ = m ζ` on `Re s > 5/4`.
  have hF₁ζ : ∀ s : ℂ, 5 / 4 < s.re → F₁ s = (m : ℂ) * riemannZeta s := by
    intro s hs
    rw [(hrep s hs).2, hμeq, integral_smul_measure, ENNReal.toReal_ofReal hm,
      integral_cpow_neg_sum_dirac (by linarith), Complex.real_smul]
  have hm0 : m ≠ 0 := by
    intro h0
    have h := hF₁ζ ((2 : ℝ) : ℂ) (by norm_num)
    rw [h0, Complex.ofReal_zero, zero_mul] at h
    have := hF₁two
    rw [h, Complex.zero_re] at this
    norm_num at this
  -- Analytic continuation to `Re s > 1`.
  refine ⟨c * m, mul_ne_zero hc hm0, ?_⟩
  have hfa : AnalyticOnNhd ℂ F U := hS.diffOn_F.analyticOnNhd hU
  have hga : AnalyticOnNhd ℂ (fun s => ((c * m : ℝ) : ℂ) * riemannZeta s) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hU
    intro s hs
    have hs1 : s ≠ 1 := fun h => by
      have : (1 : ℝ) < s.re := hs
      rw [h, Complex.one_re] at this
      exact lt_irrefl _ this
    exact ((differentiableAt_riemannZeta hs1).const_mul _).differentiableWithinAt
  have h2U : ((2 : ℝ) : ℂ) ∈ U := by simp [hUdef]
  have hev : ∀ᶠ z in 𝓝 ((2 : ℝ) : ℂ), F z = ((c * m : ℝ) : ℂ) * riemannZeta z := by
    have hopen : IsOpen {z : ℂ | 5 / 4 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show ((2 : ℝ) : ℂ) ∈ {z : ℂ | 5 / 4 < z.re} by
      simp; norm_num)] with z hz
    have h := hF₁ζ z hz
    rw [hF₁def] at h
    simp only at h
    rw [div_eq_iff hcC] at h
    rw [h]
    push_cast
    ring
  have heq := hfa.eqOn_of_preconnected_of_frequently_eq hga
    (convex_halfSpace_re_gt 1).isPreconnected h2U
    (eventually_nhdsWithin_of_eventually_nhds hev).frequently
  intro s hs
  exact heq hs

/-- Real nonzero multiples of `ζ`, completed by `K · 2ξ`, are completed positive systems of pole
budget `1` and degree `1`. -/
theorem completedPositiveSystem_real_mul_zeta {K : ℝ} (hK : K ≠ 0) :
    CompletedPositiveSystem 1 1 (fun s => (K : ℂ) * riemannZeta s)
      (fun s => (K : ℂ) * (2 * RHTower.xi s)) := by
  have hZ := completedPositiveSystem_riemannZeta
  have hKC : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  have hlog : ∀ s : ℂ, logDeriv (fun s => (K : ℂ) * riemannZeta s) s = logDeriv riemannZeta s := by
    intro s
    rw [logDeriv_apply, logDeriv_apply, deriv_const_mul_field']
    by_cases h : riemannZeta s = 0
    · simp [h]
    · field_simp
  exact
    { degree_pos := le_rfl
      diffOn_F := hZ.diffOn_F.const_mul _
      ne_zero_F := fun s hs => mul_ne_zero hKC (hZ.ne_zero_F s hs)
      posDef_neg_logDeriv := fun {σ} hσ => by
        simp only [hlog]
        exact hZ.posDef_neg_logDeriv hσ
      entire_Λ := hZ.entire_Λ.const_mul _
      orderOne_Λ := OrderOneEnvelope.const_mul _ hZ.orderOne_Λ
      sym_Λ := fun s => by simp only [hZ.sym_Λ s]
      conj_Λ := fun s => by
        rw [map_mul, Complex.conj_ofReal, hZ.conj_Λ s]
      completed_eq := fun s hs => by
        rw [hZ.completed_eq s hs]
        ring }

/-- **The pole-budget-one class is `ℝ^× · ζ`.** A completed positive system of pole budget `1` has
degree `1` (`5d < 9κ`) and `F = Kζ` on `Re s > 1` with `K` real and nonzero; conversely every such
`Kζ` is one. -/
theorem completedPositiveSystem_one_iff {d : ℕ} {F Λ : ℂ → ℂ} :
    CompletedPositiveSystem 1 d F Λ →
      d = 1 ∧ ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * riemannZeta s := by
  intro hS
  have h1 := hS.degree_pos
  have h2 := five_mul_degree_lt_nine_mul_poleOrder hS
  have hd : d = 1 := by omega
  subst hd
  exact ⟨rfl, completedPositiveSystem_one_one_eq_zeta hS⟩

/-- The completion of a pole-budget-one system is `K · 2ξ` on all of `ℂ`. -/
theorem completedPositiveSystem_one_Λ_eq {d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem 1 d F Λ) :
    ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, Λ s = K * (2 * RHTower.xi s) := by
  obtain ⟨hd, K, hK, hF⟩ := completedPositiveSystem_one_iff hS
  subst hd
  refine ⟨K, hK, fun s => ?_⟩
  have hZ := completedPositiveSystem_riemannZeta
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have hev : Λ =ᶠ[𝓝 (2 : ℂ)] fun z => (K : ℂ) * (2 * RHTower.xi z) := by
    filter_upwards [hopen.mem_nhds h2] with z hz
    rw [hS.completed_eq z hz, hF z hz, hZ.completed_eq z hz]
    ring
  have heq := (hS.entire_Λ.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    ((hZ.entire_Λ.const_mul (K : ℂ)).differentiableOn.analyticOnNhd isOpen_univ)
    isPreconnected_univ (mem_univ _) hev
  exact heq (mem_univ s)

/-- **No pole-budget-one system is zero-free.** Every completed positive system of pole budget `1`
vanishes at critical points `1/2 + it` of arbitrarily large height (Hardy). -/
theorem completedPositiveSystem_one_critical_zeros {d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem 1 d F Λ) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ Λ (1 / 2 + (t : ℂ) * I) = 0 := by
  obtain ⟨K, -, hΛ⟩ := completedPositiveSystem_one_Λ_eq hS
  obtain ⟨t, ht, hXi⟩ := RHTower.exists_Xi_zero_gt T
  refine ⟨t, ht, ?_⟩
  set s : ℂ := 1 / 2 + (t : ℂ) * I
  have hs0 : s ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp [s] at this
  have hs1 : s ≠ 1 := fun h => by
    have := congrArg Complex.re h
    simp [s] at this
  rw [hΛ, RHTower.xi_eq_half_mul hs0 hs1, RHTower.completedRiemannZeta_critical_eq_Xi, hXi]
  simp

end GaloisForLFunctions.StripBochnerWeilForcing
