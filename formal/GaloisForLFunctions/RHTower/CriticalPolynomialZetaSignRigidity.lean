import GaloisForLFunctions.RHTower.ZetaConvexityBound

/-!
# Sign rigidity of critical Dirichlet polynomials against `ζ`

For every real `κ`, the Cesàro mean `(1/T) ∫_8^T ζ(1/2+iy) e^{iκy} dy` tends to `m^{-1/2}` when
`κ = log m` for a positive integer `m`, and to `0` otherwise (`tendsto_twisted_zeta_first_moment`).
The proof moves the segment to `Re s = 3/2` through the rectangle, with horizontal edges controlled by
the convexity bound for `ζ`.

Consequence (`critDirPoly_eq_zero_of_re_mul_conj_zeta_nonpos`): if
`E(y) = Σ_{n ∈ N} e(n) n^{-1/2-iy}` with all `n ≥ 2` satisfies
`Re(E(y) · conj ζ(1/2+iy)) ≤ 0` for all `y ≥ 8`, then `e = 0` on `N`. The mean of `E · conj ζ`
against the nonnegative weight `|M_D(y)(1 + c a^{-iy})|²`, with `M_D` the Möbius polynomial of
`D = K!`, isolates the coefficient `e(a)` by strong induction on `a`.
-/

open Complex MeasureTheory Filter Topology Set intervalIntegral
open scoped Interval

noncomputable section

namespace RHTower

/-- `∫_a^b e^{iδy} dy`, evaluated. -/
theorem integral_cexp_ofReal_mul_I (δ a b : ℝ) :
    ∫ y in a..b, cexp ((δ : ℂ) * y * I) =
      if δ = 0 then ((b - a : ℝ) : ℂ) else (cexp (δ * b * I) - cexp (δ * a * I)) / (δ * I) := by
  split_ifs with hδ
  · subst hδ; simp
  · have hc : ((δ : ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hδ) I_ne_zero
    have h := integral_exp_mul_complex (a := a) (b := b) hc
    have hfun : (fun y : ℝ => cexp ((δ : ℂ) * y * I)) = fun y : ℝ => cexp ((δ : ℂ) * I * y) := by
      funext y; ring_nf
    rw [hfun, h]
    ring_nf

/-- The Cesàro mean of `e^{iδy}` over `[8, T]` tends to `[δ = 0]`. -/
theorem tendsto_integral_cexp_div (δ : ℝ) :
    Tendsto (fun T : ℝ => (∫ y in (8 : ℝ)..T, cexp ((δ : ℂ) * y * I)) / T) atTop
      (𝓝 (if δ = 0 then (1 : ℂ) else 0)) := by
  split_ifs with hδ
  · subst hδ
    have h0 : Tendsto (fun T : ℝ => (1 - 8 / T : ℝ)) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := (8 : ℝ))).div_atTop tendsto_id)
      simpa using this
    have hlim : Tendsto (fun T : ℝ => ((1 - 8 / T : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp h0
      simpa [Function.comp_def] using this
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    rw [integral_cexp_ofReal_mul_I, if_pos rfl]
    push_cast
    field_simp
  · have hbound : ∀ T : ℝ, ‖∫ y in (8 : ℝ)..T, cexp ((δ : ℂ) * y * I)‖ ≤ 2 / |δ| := by
      intro T
      rw [integral_cexp_ofReal_mul_I, if_neg hδ, norm_div, norm_mul, norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      gcongr
      calc ‖cexp (δ * T * I) - cexp (δ * 8 * I)‖ ≤ ‖cexp (δ * T * I)‖ + ‖cexp (δ * 8 * I)‖ :=
            norm_sub_le _ _
        _ = 2 := by
          rw [show ((δ : ℂ) * T * I) = ((δ * T : ℝ) : ℂ) * I by push_cast; ring,
            show ((δ : ℂ) * 8 * I) = ((δ * 8 : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
          norm_num
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun T : ℝ => (2 / |δ|) / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    exact div_le_div_of_nonneg_right (hbound T) hT.le

open scoped Classical in
/-- The weight of the frequency `κ` in the twisted first moment of `ζ`: `m^{-1/2}` if
`κ = log m` for a positive integer `m`, and `0` otherwise. -/
def zetaFreqWeight (κ : ℝ) : ℂ :=
  ∑' m : ℕ, if 1 ≤ m ∧ Real.log m = κ then (((m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0

/-- The `m`-th term of `ζ(3/2+iy) e^{κ(1+iy)}`. -/
def rightEdgeTerm (κ : ℝ) (m : ℕ) (y : ℝ) : ℂ :=
  cexp κ * cexp ((κ : ℂ) * y * I) * (1 / (m : ℂ) ^ ((3 / 2 : ℂ) + y * I))

theorem rightEdgeTerm_zero (κ y : ℝ) : rightEdgeTerm κ 0 y = 0 := by
  have h : ((3 / 2 : ℂ) + y * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  simp [rightEdgeTerm, Complex.zero_cpow h]

theorem rightEdgeTerm_eq {κ : ℝ} {m : ℕ} (hm : 1 ≤ m) (y : ℝ) :
    rightEdgeTerm κ m y =
      cexp κ * (((m : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((κ - Real.log m : ℝ) : ℂ) * y * I) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpow : (m : ℂ) ^ ((3 / 2 : ℂ) + y * I) =
      (((m : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * cexp ((Real.log m : ℂ) * y * I) := by
    rw [Complex.cpow_add _ _ hm0, Complex.cpow_def_of_ne_zero hm0 (y * I)]
    congr 1
    · rw [Complex.ofReal_cpow hmr]; push_cast; ring_nf
    · congr 1
      rw [show (Complex.log (m : ℂ)) = (Real.log m : ℂ) by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hmr] ]
      ring
  have hrpos : (0 : ℝ) < (m : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hm) _
  have hne2 : (((m : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  rw [rightEdgeTerm, hpow, Real.rpow_neg hmr, Complex.ofReal_inv, Complex.ofReal_sub,
    show ((κ : ℂ) - (Real.log m : ℂ)) * y * I = (κ : ℂ) * y * I - (Real.log m : ℂ) * y * I by ring,
    Complex.exp_sub]
  field_simp

theorem norm_rightEdgeTerm_le (κ : ℝ) (m : ℕ) (y : ℝ) :
    ‖rightEdgeTerm κ m y‖ ≤ Real.exp κ * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; rw [rightEdgeTerm_zero]; simp
  · rw [rightEdgeTerm_eq h, norm_mul, norm_mul, Complex.norm_exp_ofReal, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _),
      show ((((κ - Real.log m : ℝ) : ℂ) * y * I)) = (((κ - Real.log m) * y : ℝ) : ℂ) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem summable_rightEdgeBound (κ : ℝ) :
    Summable fun m : ℕ => Real.exp κ * (m : ℝ) ^ (-(3 / 2 : ℝ)) :=
  (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _

theorem continuous_rightEdgeTerm (κ : ℝ) (m : ℕ) : Continuous (rightEdgeTerm κ m) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    have : rightEdgeTerm κ 0 = fun _ => 0 := funext (rightEdgeTerm_zero κ)
    rw [this]; exact continuous_const
  · have : rightEdgeTerm κ m = fun y : ℝ => cexp κ * (((m : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        cexp (((κ - Real.log m : ℝ) : ℂ) * (y : ℂ) * I) := funext (rightEdgeTerm_eq h)
    rw [this]; fun_prop

theorem hasSum_rightEdgeTerm (κ y : ℝ) :
    HasSum (fun m => rightEdgeTerm κ m y)
      (riemannZeta ((3 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2))) := by
  have hre : 1 < ((3 / 2 : ℂ) + y * I).re := by simp; norm_num
  have hsum : Summable fun m : ℕ => rightEdgeTerm κ m y :=
    Summable.of_norm_bounded (summable_rightEdgeBound κ) (fun m => norm_rightEdgeTerm_le κ m y)
  have heq : riemannZeta ((3 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2)) =
      ∑' m, rightEdgeTerm κ m y := by
    rw [zeta_eq_tsum_one_div_nat_cpow hre]
    simp only [rightEdgeTerm]
    rw [← tsum_mul_right]
    congr 1; funext m
    rw [show (κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2) = (κ : ℂ) + (κ : ℂ) * y * I by ring,
      Complex.exp_add]
    ring
  rw [heq]; exact hsum.hasSum

/-- The right-edge integral is the sum of the termwise integrals. -/
theorem hasSum_integral_rightEdgeTerm (κ T : ℝ) :
    HasSum (fun m => ∫ y in (8 : ℝ)..T, rightEdgeTerm κ m y)
      (∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
        cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2))) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m _ => Real.exp κ * (m : ℝ) ^ (-(3 / 2 : ℝ))) (fun m => ?_) (fun m => ?_) ?_ ?_ ?_
  · exact (continuous_rightEdgeTerm κ m).aestronglyMeasurable
  · exact Eventually.of_forall fun y _ => norm_rightEdgeTerm_le κ m y
  · exact Eventually.of_forall fun y _ => summable_rightEdgeBound κ
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun y _ => hasSum_rightEdgeTerm κ y

/-- The termwise integral on the right edge. -/
theorem integral_rightEdgeTerm {κ : ℝ} {m : ℕ} (hm : 1 ≤ m) (T : ℝ) :
    ∫ y in (8 : ℝ)..T, rightEdgeTerm κ m y =
      cexp κ * (((m : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ y in (8 : ℝ)..T, cexp (((κ - Real.log m : ℝ) : ℂ) * y * I) := by
  simp_rw [rightEdgeTerm_eq hm]
  rw [intervalIntegral.integral_const_mul]

/-- The Cesàro mean of the right-edge integral. -/
theorem tendsto_rightEdge_div (κ : ℝ) :
    Tendsto (fun T : ℝ => (∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
        cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2))) / T) atTop (𝓝 (zetaFreqWeight κ)) := by
  have hrewrite : ∀ T : ℝ, (∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
        cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2))) / T =
      ∑' m, (∫ y in (8 : ℝ)..T, rightEdgeTerm κ m y) / T := by
    intro T
    rw [(hasSum_integral_rightEdgeTerm κ T).tsum_eq.symm, tsum_div_const]
  simp_rw [hrewrite]
  have hg : zetaFreqWeight κ = ∑' m : ℕ,
      (if m = 0 then (0 : ℂ) else cexp κ * (((m : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        (if κ - Real.log m = 0 then (1 : ℂ) else 0)) := by
    unfold zetaFreqWeight
    congr 1; funext m
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have hm1 : 1 ≤ m := h
      have hm0 : m ≠ 0 := by omega
      have hmpos : (0 : ℝ) < m := by exact_mod_cast h
      by_cases hk : Real.log m = κ
      · have hc1 : (1 ≤ m ∧ Real.log m = κ) := ⟨hm1, hk⟩
        have hc2 : κ - Real.log m = 0 := by rw [hk]; ring
        rw [if_pos hc1, if_neg hm0, if_pos hc2, mul_one, ← Complex.ofReal_exp,
          show Real.exp κ = m by rw [← hk, Real.exp_log hmpos], ← Complex.ofReal_mul]
        congr 1
        rw [show (-(1 / 2 : ℝ)) = 1 + (-(3 / 2)) by norm_num, Real.rpow_add hmpos, Real.rpow_one]
      · have hc1 : ¬(1 ≤ m ∧ Real.log m = κ) := fun h' => hk h'.2
        have hc2 : ¬(κ - Real.log m = 0) := by intro h'; apply hk; linarith
        rw [if_neg hc1, if_neg hm0, if_neg hc2, mul_zero]
  rw [hg]
  refine tendsto_tsum_of_dominated_convergence (summable_rightEdgeBound κ) (fun m => ?_) ?_
  · rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp only [rightEdgeTerm_zero, intervalIntegral.integral_zero, zero_div, if_true]
      exact tendsto_const_nhds
    · rw [if_neg (by omega)]
      simp_rw [integral_rightEdgeTerm h, mul_div_assoc]
      exact (tendsto_integral_cexp_div (κ - Real.log m)).const_mul _
  · filter_upwards [eventually_ge_atTop (8 : ℝ)] with T hT m
    have hTpos : (0 : ℝ) < T := by linarith
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos, div_le_iff₀ hTpos]
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (8 : ℝ)) (b := T) (f := rightEdgeTerm κ m) (C := Real.exp κ * (m : ℝ) ^ (-(3 / 2 : ℝ)))
      (fun y _ => norm_rightEdgeTerm_le κ m y)
    rw [abs_of_nonneg (by linarith)] at h1
    have h2 : 0 ≤ Real.exp κ * (m : ℝ) ^ (-(3 / 2 : ℝ)) :=
      mul_nonneg (Real.exp_pos κ).le (Real.rpow_nonneg (Nat.cast_nonneg m) _)
    nlinarith

/-- `ζ(s) e^{κ(s − 1/2)}`. -/
def expTwistedZeta (κ : ℝ) (s : ℂ) : ℂ := riemannZeta s * cexp ((κ : ℂ) * (s - 1 / 2))

theorem differentiableOn_twistedZeta_rect (κ : ℝ) {T : ℝ} (hT : 8 ≤ T) :
    DifferentiableOn ℂ (expTwistedZeta κ) ([[(1 / 2 : ℝ), (3 / 2 : ℝ)]] ×ℂ [[(8 : ℝ), T]]) := by
  intro s hs
  have him : 8 ≤ s.im := by
    have h2 := hs.2
    simp only [Set.mem_preimage] at h2
    rw [Set.uIcc_of_le hT] at h2
    exact h2.1
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at him; simp at him; linarith
  exact ((differentiableAt_riemannZeta hs1).mul (by fun_prop)).differentiableWithinAt

theorem exists_norm_twistedZeta_horizontal_le (κ : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 8 ≤ T →
    ‖∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + T * I)‖ ≤ C * T ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_riemannZeta_le_convexity (η := 1 / 2) (by norm_num)
    (by norm_num)
  refine ⟨C * Real.exp |κ|, by positivity, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := 3 / 2)
    (f := fun x : ℝ => expTwistedZeta κ (x + T * I)) (C := C * Real.exp |κ| * T ^ (1 / 2 : ℝ)) ?_
  · calc _ ≤ C * Real.exp |κ| * T ^ (1 / 2 : ℝ) * |(3 / 2 : ℝ) - 1 / 2| := h
      _ = C * Real.exp |κ| * T ^ (1 / 2 : ℝ) := by norm_num
  · intro x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hx1 : 1 / 2 < x := hx.1
    have hx2 : x ≤ 3 / 2 := hx.2
    rw [expTwistedZeta, norm_mul]
    have hz := hbound x T (by linarith) (by linarith) hT
    have hexp : ‖cexp ((κ : ℂ) * ((x : ℂ) + T * I - 1 / 2))‖ ≤ Real.exp |κ| := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : ((κ : ℂ) * ((x : ℂ) + T * I - 1 / 2)).re = κ * (x - 1 / 2) := by simp
      rw [hre]
      have h0 : 0 ≤ x - 1 / 2 := by linarith
      have h1 : x - 1 / 2 ≤ 1 := by linarith
      calc κ * (x - 1 / 2) ≤ |κ * (x - 1 / 2)| := le_abs_self _
        _ = |κ| * (x - 1 / 2) := by rw [abs_mul, abs_of_nonneg h0]
        _ ≤ |κ| * 1 := by gcongr
        _ = |κ| := mul_one _
    have hpow : T ^ ((1 + 1 / 2 - x) / 2) ≤ T ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    calc ‖riemannZeta ((x : ℂ) + T * I)‖ * ‖cexp ((κ : ℂ) * ((x : ℂ) + T * I - 1 / 2))‖
        ≤ (C * T ^ ((1 + 1 / 2 - x) / 2)) * Real.exp |κ| := by
          gcongr
      _ ≤ (C * T ^ (1 / 2 : ℝ)) * Real.exp |κ| := by gcongr
      _ = C * Real.exp |κ| * T ^ (1 / 2 : ℝ) := by ring

/-- **Twisted first moment of `ζ` on the critical line.**  For every real `κ`,
`(1/T) ∫_8^T ζ(1/2+iy) e^{iκy} dy → m^{-1/2}` if `κ = log m` for a positive integer `m`, and
`→ 0` otherwise. -/
theorem tendsto_twisted_zeta_first_moment (κ : ℝ) :
    Tendsto (fun T : ℝ => (∫ y in (8 : ℝ)..T,
        riemannZeta ((1 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * y * I)) / T)
      atTop (𝓝 (zetaFreqWeight κ)) := by
  obtain ⟨C, hC, hH⟩ := exists_norm_twistedZeta_horizontal_le κ
  have hcauchy : ∀ T : ℝ, 8 ≤ T →
      ∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * y * I) =
        (∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
          cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2))) +
        ((∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + 8 * I)) -
          (∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + T * I))) / I := by
    intro T hT
    have hre1 : ((1 / 2 : ℂ) + 8 * I).re = 1 / 2 := by simp
    have hre2 : ((3 / 2 : ℂ) + T * I).re = 3 / 2 := by simp
    have him1 : ((1 / 2 : ℂ) + 8 * I).im = 8 := by simp
    have him2 : ((3 / 2 : ℂ) + T * I).im = T := by simp
    have h := integral_boundary_rect_eq_zero_of_differentiableOn (expTwistedZeta κ)
      ((1 / 2 : ℂ) + 8 * I) ((3 / 2 : ℂ) + T * I) (by
        rw [hre1, hre2, him1, him2]; exact differentiableOn_twistedZeta_rect κ hT)
    rw [hre1, hre2, him1, him2] at h
    have hL : ∫ y in (8 : ℝ)..T, expTwistedZeta κ (((1 / 2 : ℝ) : ℂ) + y * I) =
        ∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * y * I) := by
      congr 1; funext y; simp only [expTwistedZeta]; push_cast; ring_nf
    have hR : ∫ y in (8 : ℝ)..T, expTwistedZeta κ (((3 / 2 : ℝ) : ℂ) + y * I) =
        ∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
          cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2)) := by
      congr 1; funext y; simp only [expTwistedZeta]; push_cast; ring_nf
    have h8 : ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + ((8 : ℝ) : ℂ) * I) =
        ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + 8 * I) := by push_cast; rfl
    rw [hL, hR, h8] at h
    rw [smul_eq_mul, smul_eq_mul] at h
    generalize (∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * y * I)) = L at h ⊢
    generalize (∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
      cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2))) = R at h ⊢
    generalize (∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + 8 * I)) = A at h ⊢
    generalize (∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + T * I)) = B at h ⊢
    have h' : I * L = I * R + (A - B) := by linear_combination -h
    calc L = (I * L) / I := by rw [mul_div_cancel_left₀ _ I_ne_zero]
      _ = (I * R + (A - B)) / I := by rw [h']
      _ = R + (A - B) / I := by rw [add_div, mul_div_cancel_left₀ _ I_ne_zero]
  have hdecomp : ∀ᶠ T : ℝ in atTop,
      (∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * y * I)) / T =
        (∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
          cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2))) / T +
        ((∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + 8 * I)) / I) / T -
        ((∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + T * I)) / I) / T := by
    filter_upwards [eventually_ge_atTop (8 : ℝ)] with T hT
    rw [hcauchy T hT]; ring
  refine Tendsto.congr' (EventuallyEq.symm hdecomp) ?_
  have h1 := tendsto_rightEdge_div κ
  have h2 : Tendsto (fun T : ℝ => ((∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + 8 * I)) / I)
      / (T : ℂ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun T : ℝ => ((T⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
      simpa [Function.comp_def] using this
    have := hinv.const_mul ((∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + 8 * I)) / I)
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun T => ?_)
    simp only [Complex.ofReal_inv, div_eq_mul_inv]
  have h3 : Tendsto (fun T : ℝ => ((∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + T * I)) / I)
      / (T : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun T : ℝ => C * T ^ (1 / 2 : ℝ) / T) atTop (𝓝 0) := by
      have : Tendsto (fun T : ℝ => C * T ^ (-(1 / 2) : ℝ)) atTop (𝓝 (C * 0)) :=
        (tendsto_rpow_neg_atTop (by norm_num)).const_mul C
      rw [mul_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [show (-(1 / 2) : ℝ) = (1 / 2) - 1 by norm_num, Real.rpow_sub_one hT.ne', mul_div_assoc]
    refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop (8 : ℝ)] with T hT
    have hTpos : (0 : ℝ) < T := by linarith
    rw [norm_div, norm_div, norm_I, div_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
    exact div_le_div_of_nonneg_right (hH T hT) hTpos.le
  have := (h1.add h2).sub h3
  simpa using this

/-- `zetaFreqWeight (log u − log w)` is `(u/w)^{-1/2}` when `w ∣ u`, and `0` otherwise. -/
theorem zetaFreqWeight_log_sub {u w : ℕ} (hu : 1 ≤ u) (hw : 1 ≤ w) :
    zetaFreqWeight (Real.log u - Real.log w) =
      if w ∣ u then ((((u / w : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0 := by
  have hupos : (0 : ℝ) < u := by exact_mod_cast hu
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw
  have key : ∀ m : ℕ, (1 ≤ m ∧ Real.log m = Real.log u - Real.log w) ↔ (w ∣ u ∧ m = u / w) := by
    intro m
    constructor
    · rintro ⟨hm, hlog⟩
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
      have h1 : Real.log ((m : ℝ) * w) = Real.log u := by
        rw [Real.log_mul hmpos.ne' hwpos.ne']; linarith
      have h2 : (m : ℝ) * w = u :=
        Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos hmpos hwpos)) (Set.mem_Ioi.mpr hupos) h1
      have h3 : m * w = u := by exact_mod_cast h2
      exact ⟨⟨m, by rw [← h3]; ring⟩, by rw [← h3, Nat.mul_div_cancel _ (by omega)]⟩
    · rintro ⟨⟨k, hk⟩, hm⟩
      have hk' : m = k := by rw [hm, hk, Nat.mul_div_cancel_left _ (by omega)]
      subst hk'
      have hmpos : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp at hk; omega
        · exact h
      refine ⟨hmpos, ?_⟩
      rw [hk]; push_cast
      rw [Real.log_mul hwpos.ne' (by exact_mod_cast (by omega : m ≠ 0))]; ring
  unfold zetaFreqWeight
  have hterm : ∀ m : ℕ, (if 1 ≤ m ∧ Real.log m = Real.log u - Real.log w then
      (((m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0) =
      if m = u / w then (if w ∣ u then ((((u / w : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0)
        else 0 := by
    intro m
    by_cases h1 : 1 ≤ m ∧ Real.log m = Real.log u - Real.log w
    · rw [if_pos h1]
      obtain ⟨hd, hm⟩ := (key m).mp h1
      rw [if_pos hm, if_pos hd, hm]
    · rw [if_neg h1]
      by_cases hm : m = u / w
      · rw [if_pos hm]
        by_cases hd : w ∣ u
        · exact absurd ((key m).mpr ⟨hd, hm⟩) h1
        · rw [if_neg hd]
      · rw [if_neg hm]
  simp_rw [hterm]
  rw [tsum_ite_eq]

/-- The Möbius polynomial `Σ_{d ∣ D} μ(d) d^{-1/2-iy}`. -/
def mobiusPoly (D : ℕ) (y : ℝ) : ℂ :=
  ∑ d ∈ D.divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
    ((((d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-((Real.log d : ℝ) : ℂ) * y * I))

theorem continuous_riemannZeta_criticalLine : Continuous fun y : ℝ => riemannZeta ((1 / 2 : ℂ) + y * I) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hs : ((1 / 2 : ℂ) + y * I) ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  exact ContinuousAt.comp (g := riemannZeta) (f := fun y : ℝ => (1 / 2 : ℂ) + (y : ℂ) * I)
    (differentiableAt_riemannZeta hs).continuousAt (by fun_prop)

/-- The twisted first moment of `ζ · M_D`. -/
theorem tendsto_zeta_mobiusPoly_moment (D : ℕ) (κ : ℝ) :
    Tendsto (fun T : ℝ => (∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) * mobiusPoly D y *
        cexp ((κ : ℂ) * y * I)) / T) atTop
      (𝓝 (∑ d ∈ D.divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
        ((((d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * zetaFreqWeight (κ - Real.log d)))) := by
  have hpt : ∀ y : ℝ, riemannZeta ((1 / 2 : ℂ) + y * I) * mobiusPoly D y * cexp ((κ : ℂ) * y * I) =
      ∑ d ∈ D.divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
        ((((d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (riemannZeta ((1 / 2 : ℂ) + y * I) *
          cexp (((κ - Real.log d : ℝ) : ℂ) * y * I))) := by
    intro y
    rw [mobiusPoly, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [show (((κ - Real.log d : ℝ) : ℂ) * y * I) = (κ : ℂ) * y * I + (-((Real.log d : ℝ) : ℂ) * y * I) by
      push_cast; ring, Complex.exp_add]
    ring
  have hint : ∀ T : ℝ, (∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) * mobiusPoly D y *
        cexp ((κ : ℂ) * y * I)) / T =
      ∑ d ∈ D.divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
        ((((d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) *
          cexp (((κ - Real.log d : ℝ) : ℂ) * y * I)) / T)) := by
    intro T
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum, Finset.sum_div]
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    · intro d _
      exact ((continuous_const.mul (continuous_const.mul (continuous_riemannZeta_criticalLine.mul
        (by fun_prop)))).intervalIntegrable _ _)
  simp_rw [hint]
  refine tendsto_finsetSum _ fun d _ => ?_
  exact ((tendsto_twisted_zeta_first_moment (κ - Real.log d)).const_mul _).const_mul _

/-- **Möbius collapse.**  If `u, w ≥ 1` have all prime factors `≤ K`, then
`Σ_{d ∣ K!} μ(d) d^{-1/2} zetaFreqWeight(log u − log w − log d) = [u = w]`. -/
theorem sum_mobius_zetaFreqWeight {K u w : ℕ} (hu : 1 ≤ u) (hw : 1 ≤ w)
    (hsm : ∀ p : ℕ, p.Prime → p ∣ u → p ≤ K) :
    ∑ d ∈ (Nat.factorial K).divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
        ((((d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * zetaFreqWeight (Real.log u - Real.log w - Real.log d)) =
      if u = w then 1 else 0 := by
  have hD : Nat.factorial K ≠ 0 := Nat.factorial_ne_zero K
  have hterm : ∀ d ∈ (Nat.factorial K).divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
      ((((d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * zetaFreqWeight (Real.log u - Real.log w - Real.log d)) =
      if w * d ∣ u then ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
        ((((u / w : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0 := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hwd : 1 ≤ w * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hlog : Real.log u - Real.log w - Real.log d = Real.log u - Real.log (w * d : ℕ) := by
      push_cast
      rw [Real.log_mul (by exact_mod_cast (by omega : w ≠ 0)) (by exact_mod_cast (by omega : d ≠ 0))]
      ring
    rw [hlog, zetaFreqWeight_log_sub hu hwd]
    split_ifs with hdiv
    · obtain ⟨m, hm⟩ := hdiv
      have hq : u / w = d * m := by
        rw [hm, mul_assoc, Nat.mul_div_cancel_left _ (by omega)]
      have hq2 : u / (w * d) = m := by rw [hm, Nat.mul_div_cancel_left _ (by positivity)]
      rw [hq, hq2]
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
      have hmpos : (0 : ℝ) < m := by
        have : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · subst h; simp at hm; omega
          · exact h
        exact_mod_cast this
      push_cast
      rw [Real.mul_rpow hdpos.le hmpos.le]
      push_cast
      ring
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  by_cases hwu : w ∣ u
  · obtain ⟨q, hq⟩ := hwu
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hq; omega
      · exact h
    have hfilter : (Nat.factorial K).divisors.filter (fun d => w * d ∣ u) =
        (Nat.gcd (Nat.factorial K) q).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, hq]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩
        refine ⟨Nat.dvd_gcd h1 (Nat.dvd_of_mul_dvd_mul_left (by omega) h2), ?_⟩
        exact Nat.gcd_ne_zero_left hD
      · rintro ⟨h1, _⟩
        exact ⟨⟨(Nat.dvd_gcd_iff.mp h1).1, hD⟩,
          Nat.mul_dvd_mul_left w (Nat.dvd_gcd_iff.mp h1).2⟩
    rw [hfilter, hq, Nat.mul_div_cancel_left _ (by omega), ← Finset.sum_mul]
    have hmob : ∑ d ∈ (Nat.gcd (Nat.factorial K) q).divisors,
        ((ArithmeticFunction.moebius d : ℝ) : ℂ) =
        if Nat.gcd (Nat.factorial K) q = 1 then 1 else 0 := by
      have h := congrArg (fun f : ArithmeticFunction ℤ => f (Nat.gcd (Nat.factorial K) q))
        ArithmeticFunction.moebius_mul_coe_zeta
      simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
      have h2 : ((∑ i ∈ (Nat.gcd (Nat.factorial K) q).divisors,
          (ArithmeticFunction.moebius i : ℤ) : ℤ) : ℂ) =
          (((if Nat.gcd (Nat.factorial K) q = 1 then 1 else 0 : ℤ)) : ℂ) := by rw [h]
      push_cast at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun d _ => ?_
      push_cast
      rfl
    rw [hmob]
    have hsmq : ∀ p : ℕ, p.Prime → p ∣ q → p ≤ K := fun p hp hpq =>
      hsm p hp (hq ▸ Dvd.dvd.mul_left hpq w)
    by_cases hq1 : q = 1
    · subst hq1
      simp
    · have hg : Nat.gcd (Nat.factorial K) q ≠ 1 := by
        obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq1
        intro hg1
        have hpd : p ∣ Nat.gcd (Nat.factorial K) q :=
          Nat.dvd_gcd ((hp.dvd_factorial).mpr (hsmq p hp hpq)) hpq
        rw [hg1] at hpd
        exact hp.one_lt.ne' (Nat.dvd_one.mp hpd)
      rw [if_neg hg, zero_mul, if_neg]
      intro h
      apply hq1
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < w) (h.trans (mul_one w).symm)
  · rw [if_neg (by rintro rfl; exact hwu (dvd_refl _))]
    apply Finset.sum_eq_zero
    intro d hd
    exact absurd (Dvd.dvd.trans (Dvd.intro d rfl) (Finset.mem_filter.mp hd).2) hwu

/-- A real Dirichlet polynomial on the critical line, `Σ_{n ∈ N} e(n) n^{-1/2-iy}`. -/
def critDirPoly (N : Finset ℕ) (e : ℕ → ℝ) (y : ℝ) : ℂ :=
  ∑ n ∈ N, (e n : ℂ) * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-((Real.log n : ℝ) : ℂ) * y * I))

theorem conj_cexp_neg_real_mul (L y : ℝ) :
    starRingEnd ℂ (cexp (-((L : ℝ) : ℂ) * y * I)) = cexp ((L : ℂ) * y * I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]

theorem continuous_mobiusPoly (D : ℕ) : Continuous (mobiusPoly D) := by
  unfold mobiusPoly
  exact continuous_finsetSum _ fun d _ => by fun_prop

/-- The conjugate of `P · M` as an explicit exponential sum. -/
theorem conj_critDirPoly_mul_mobiusPoly (N : Finset ℕ) (e : ℕ → ℝ) (D : ℕ) (y : ℝ) :
    starRingEnd ℂ (critDirPoly N e y * mobiusPoly D y) =
      ∑ n ∈ N, ∑ d ∈ D.divisors,
        ((e n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (ArithmeticFunction.moebius d : ℝ) *
          (d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          cexp (((Real.log n + Real.log d : ℝ) : ℂ) * y * I) := by
  rw [critDirPoly, mobiusPoly, Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, conj_cexp_neg_real_mul, conj_cexp_neg_real_mul,
    Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal]
  rw [show ((Real.log n + Real.log d : ℝ) : ℂ) * y * I =
    ((Real.log n : ℝ) : ℂ) * y * I + ((Real.log d : ℝ) : ℂ) * y * I by push_cast; ring,
    Complex.exp_add]
  push_cast
  ring

/-- `ζ(1/2+iy) M_D(y) e^{iκy}`. -/
def zetaMobiusTerm (D : ℕ) (κ y : ℝ) : ℂ :=
  riemannZeta ((1 / 2 : ℂ) + y * I) * mobiusPoly D y * cexp ((κ : ℂ) * y * I)

/-- The limit of the Cesàro mean of `zetaMobiusTerm`. -/
def zetaMobiusLimit (D : ℕ) (κ : ℝ) : ℂ :=
  ∑ d ∈ D.divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
    ((((d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * zetaFreqWeight (κ - Real.log d))

theorem continuous_zetaMobiusTerm (D : ℕ) (κ : ℝ) : Continuous (zetaMobiusTerm D κ) := by
  unfold zetaMobiusTerm
  exact (continuous_riemannZeta_criticalLine.mul (continuous_mobiusPoly D)).mul (by fun_prop)

theorem conj_one_add_mul_cexp (c L y : ℝ) :
    (1 + (c : ℂ) * cexp (-((L : ℝ) : ℂ) * y * I)) *
      starRingEnd ℂ (1 + (c : ℂ) * cexp (-((L : ℝ) : ℂ) * y * I)) =
      1 + (c : ℂ) ^ 2 + (c : ℂ) * cexp (-((L : ℝ) : ℂ) * y * I) + (c : ℂ) * cexp ((L : ℂ) * y * I) := by
  rw [map_add, map_one, map_mul, Complex.conj_ofReal, conj_cexp_neg_real_mul]
  have h : cexp (-((L : ℝ) : ℂ) * y * I) * cexp ((L : ℂ) * y * I) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  linear_combination (c : ℂ) ^ 2 * h

theorem integral_three_combo {f g h : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) (α β γ : ℂ) (a b : ℝ) :
    ∫ y in a..b, (α * f y + β * g y + γ * h y) =
      α * (∫ y in a..b, f y) + β * (∫ y in a..b, g y) + γ * (∫ y in a..b, h y) := by
  have i1 : IntervalIntegrable (fun y => α * f y) volume a b :=
    (continuous_const.mul hf).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun y => β * g y) volume a b :=
    (continuous_const.mul hg).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun y => γ * h y) volume a b :=
    (continuous_const.mul hh).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- The value of `zetaMobiusLimit` at a frequency `log u − log w`. -/
theorem zetaMobiusLimit_log_sub {K u w : ℕ} (hu : 1 ≤ u) (hw : 1 ≤ w)
    (hsm : ∀ p : ℕ, p.Prime → p ∣ u → p ≤ K) :
    zetaMobiusLimit (Nat.factorial K) (Real.log u - Real.log w) = if u = w then 1 else 0 :=
  sum_mobius_zetaFreqWeight hu hw hsm

/-- **No nonzero Dirichlet polynomial without constant term is dissipative against `ζ`.**
If `Re(E(1/2+iy) · conj ζ(1/2+iy)) ≤ 0` for all `y ≥ 8`, where `E = Σ_{n ∈ N} e(n) n^{-1/2-iy}` with
all `n ≥ 2`, then `e = 0` on `N`.

The mean of `E · conj ζ` against `|M_D(y)(1 + c a^{-iy})|²`, with `M_D` the Möbius polynomial of
`D = K!`, is computed by the twisted first moment of `ζ`: every frequency except `nd = a` has
vanishing weight, which leaves `c · a^{-1/2} · e(a)` once the smaller coefficients vanish. -/
theorem critDirPoly_eq_zero_of_re_mul_conj_zeta_nonpos {N : Finset ℕ} (hN : ∀ n ∈ N, 2 ≤ n)
    (e : ℕ → ℝ)
    (h : ∀ y : ℝ, 8 ≤ y →
      (critDirPoly N e y * starRingEnd ℂ (riemannZeta ((1 / 2 : ℂ) + y * I))).re ≤ 0) :
    ∀ n ∈ N, e n = 0 := by
  set K := N.sup id with hK
  have hNK : ∀ n ∈ N, n ≤ K := fun n hn => Finset.le_sup (f := id) hn
  set D := Nat.factorial K with hDdef
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro ha
  have ha2 := hN a ha
  have haK := hNK a ha
  set c : ℝ := e a with hc
  set La : ℝ := Real.log a with hLa
  set β : ℕ → ℕ → ℝ := fun n d => e n * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
    (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(1 / 2 : ℝ)) with hβ
  set Φ : ℝ → ℂ := fun y => ∑ n ∈ N, ∑ d ∈ D.divisors, (β n d : ℂ) *
    ((1 + (c : ℂ) ^ 2) * zetaMobiusTerm D (Real.log n + Real.log d) y +
      (c : ℂ) * zetaMobiusTerm D (Real.log n + Real.log d + La) y +
      (c : ℂ) * zetaMobiusTerm D (Real.log n + Real.log d - La) y) with hΦdef
  -- pointwise identity
  have hΦ : ∀ y : ℝ, Φ y = starRingEnd ℂ (critDirPoly N e y *
      starRingEnd ℂ (riemannZeta ((1 / 2 : ℂ) + y * I))) *
      ((‖mobiusPoly D y * (1 + (c : ℂ) * cexp (-((La : ℝ) : ℂ) * y * I))‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    set Z := riemannZeta ((1 / 2 : ℂ) + y * I)
    set M := mobiusPoly D y
    set Rr := (1 + (c : ℂ) * cexp (-((La : ℝ) : ℂ) * y * I))
    have hnorm : ((‖M * Rr‖ ^ 2 : ℝ) : ℂ) = (M * Rr) * starRingEnd ℂ (M * Rr) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hnorm]
    have hre : starRingEnd ℂ (critDirPoly N e y * starRingEnd ℂ Z) * ((M * Rr) * starRingEnd ℂ (M * Rr))
        = Z * M * starRingEnd ℂ (critDirPoly N e y * M) * (Rr * starRingEnd ℂ Rr) := by
      simp only [map_mul, Complex.conj_conj]; ring
    rw [hre, conj_critDirPoly_mul_mobiusPoly, conj_one_add_mul_cexp, hΦdef]
    simp only
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [zetaMobiusTerm]
    rw [show (((Real.log n + Real.log d + La : ℝ)) : ℂ) * y * I =
        ((Real.log n + Real.log d : ℝ) : ℂ) * y * I + (La : ℂ) * y * I by push_cast; ring,
      show (((Real.log n + Real.log d - La : ℝ)) : ℂ) * y * I =
        ((Real.log n + Real.log d : ℝ) : ℂ) * y * I + (-((La : ℝ) : ℂ) * y * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_add]
    ring
  -- sign
  have hsign : ∀ y : ℝ, 8 ≤ y → (Φ y).re ≤ 0 := by
    intro y hy
    rw [hΦ y, Complex.re_mul_ofReal, Complex.conj_re]
    exact mul_nonpos_of_nonpos_of_nonneg (h y hy) (by positivity)
  have hcont : ∀ κ : ℝ, Continuous (zetaMobiusTerm D κ) := continuous_zetaMobiusTerm D
  have hint : ∀ T : ℝ, (∫ y in (8 : ℝ)..T, Φ y) / T = ∑ n ∈ N, ∑ d ∈ D.divisors, (β n d : ℂ) *
      ((1 + (c : ℂ) ^ 2) * ((∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d) y) / T) +
        (c : ℂ) * ((∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d + La) y) / T) +
        (c : ℂ) * ((∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d - La) y) / T)) := by
    intro T
    simp only [hΦdef]
    rw [intervalIntegral.integral_finsetSum, Finset.sum_div]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_finsetSum, Finset.sum_div]
      · refine Finset.sum_congr rfl fun d _ => ?_
        rw [intervalIntegral.integral_const_mul,
          integral_three_combo (hcont _) (hcont _) (hcont _)]
        ring
      · intro d _
        exact (continuous_const.mul (((continuous_const.mul (hcont _)).add
          (continuous_const.mul (hcont _))).add (continuous_const.mul (hcont _)))).intervalIntegrable _ _
    · intro n _
      exact (continuous_finsetSum _ fun d _ => continuous_const.mul
        (((continuous_const.mul (hcont _)).add (continuous_const.mul (hcont _))).add
          (continuous_const.mul (hcont _)))).intervalIntegrable _ _
  set Lval : ℂ := ∑ n ∈ N, ∑ d ∈ D.divisors, (β n d : ℂ) *
      ((1 + (c : ℂ) ^ 2) * zetaMobiusLimit D (Real.log n + Real.log d) +
        (c : ℂ) * zetaMobiusLimit D (Real.log n + Real.log d + La) +
        (c : ℂ) * zetaMobiusLimit D (Real.log n + Real.log d - La)) with hLvaldef
  have hlim : Tendsto (fun T : ℝ => (∫ y in (8 : ℝ)..T, Φ y) / T) atTop (𝓝 Lval) := by
    simp_rw [hint]
    refine tendsto_finsetSum _ fun n _ => tendsto_finsetSum _ fun d _ => ?_
    refine Tendsto.const_mul _ ?_
    exact (((tendsto_zeta_mobiusPoly_moment D _).const_mul _).add
      ((tendsto_zeta_mobiusPoly_moment D _).const_mul _)).add
      ((tendsto_zeta_mobiusPoly_moment D _).const_mul _)
  -- smoothness of the relevant integers
  have hsmooth : ∀ n ∈ N, ∀ d ∈ D.divisors, ∀ p : ℕ, p.Prime → p ∣ n * d * a → p ≤ K := by
    intro n hn d hd p hp hpd
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · exact (Nat.le_of_dvd (by have := hN n hn; omega) h2).trans (hNK n hn)
      · exact (hp.dvd_factorial).mp (h2.trans (Nat.dvd_of_mem_divisors hd))
    · exact (Nat.le_of_dvd (by omega) h1).trans haK
  have hlogmul : ∀ n d : ℕ, 1 ≤ n → 1 ≤ d →
      Real.log n + Real.log d = Real.log (n * d : ℕ) - Real.log (1 : ℕ) := by
    intro n d hn hd
    push_cast
    rw [Real.log_mul (by exact_mod_cast (by omega : n ≠ 0)) (by exact_mod_cast (by omega : d ≠ 0)),
      Real.log_one]
    ring
  have hval : ∀ n ∈ N, ∀ d ∈ D.divisors,
      (1 + (c : ℂ) ^ 2) * zetaMobiusLimit D (Real.log n + Real.log d) +
        (c : ℂ) * zetaMobiusLimit D (Real.log n + Real.log d + La) +
        (c : ℂ) * zetaMobiusLimit D (Real.log n + Real.log d - La) =
      (c : ℂ) * (if n * d = a then 1 else 0) := by
    intro n hn d hd
    have hn1 : 1 ≤ n := by have := hN n hn; omega
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have ha1 : 1 ≤ a := by omega
    have hsm1 : ∀ p : ℕ, p.Prime → p ∣ n * d → p ≤ K := fun p hp hpd =>
      hsmooth n hn d hd p hp (hpd.trans (Dvd.intro a rfl))
    have hsm2 : ∀ p : ℕ, p.Prime → p ∣ n * d * a → p ≤ K := hsmooth n hn d hd
    have e1 : zetaMobiusLimit D (Real.log n + Real.log d) = 0 := by
      rw [hlogmul n d hn1 hd1, hDdef, zetaMobiusLimit_log_sub (Nat.one_le_iff_ne_zero.mpr
        (by positivity)) le_rfl hsm1, if_neg]
      intro h1; have h2 := Nat.eq_one_of_mul_eq_one_right h1; have := hN n hn; omega
    have e2 : zetaMobiusLimit D (Real.log n + Real.log d + La) = 0 := by
      have : Real.log n + Real.log d + La = Real.log (n * d * a : ℕ) - Real.log (1 : ℕ) := by
        rw [hLa]; push_cast
        rw [Real.log_mul (by positivity) (by exact_mod_cast (by omega : a ≠ 0)),
          Real.log_mul (by exact_mod_cast (by omega : n ≠ 0)) (by exact_mod_cast (by omega : d ≠ 0)),
          Real.log_one]
        ring
      rw [this, hDdef, zetaMobiusLimit_log_sub (Nat.one_le_iff_ne_zero.mpr (by positivity)) le_rfl hsm2,
        if_neg]
      intro h1
      have h2 := Nat.eq_one_of_mul_eq_one_right (Nat.eq_one_of_mul_eq_one_right h1)
      have := hN n hn
      omega
    have e3 : zetaMobiusLimit D (Real.log n + Real.log d - La) = if n * d = a then 1 else 0 := by
      have : Real.log n + Real.log d - La = Real.log (n * d : ℕ) - Real.log a := by
        rw [hLa]; push_cast
        rw [Real.log_mul (by exact_mod_cast (by omega : n ≠ 0)) (by exact_mod_cast (by omega : d ≠ 0))]
      rw [this, hDdef, zetaMobiusLimit_log_sub (Nat.one_le_iff_ne_zero.mpr (by positivity)) ha1 hsm1]
    rw [e1, e2, e3]; ring
  have hLval : Lval = ((c * (e a * (a : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) := by
    rw [hLvaldef]
    rw [Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun d hd => by rw [hval n hn d hd] ]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single 1]
      · simp [hβ]
        ring
      · intro d _ hd1
        have : a * d ≠ a := by
          intro h1
          apply hd1
          have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < a) (h1.trans (mul_one a).symm)
          exact this
        rw [if_neg this]; ring
      · intro h1; exact absurd (Nat.one_mem_divisors.mpr (Nat.factorial_ne_zero K)) h1
    · intro n hn hna
      apply Finset.sum_eq_zero
      intro d hd
      by_cases hnd : n * d = a
      · have hnlt : n < a := by
          have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
          have hle : n ≤ a := hnd ▸ Nat.le_mul_of_pos_right n hd1
          omega
        have hen : e n = 0 := ih n hnlt hn
        simp [hβ, hen]
      · rw [if_neg hnd]; ring
    · intro h1; exact absurd ha h1
  have hnonpos : ∀ᶠ T : ℝ in atTop, ((∫ y in (8 : ℝ)..T, Φ y) / T).re ≤ 0 := by
    filter_upwards [eventually_ge_atTop (8 : ℝ)] with T hT
    have hTpos : (0 : ℝ) < T := by linarith
    rw [Complex.div_ofReal_re]
    apply div_nonpos_of_nonpos_of_nonneg _ hTpos.le
    have hre : (∫ y in (8 : ℝ)..T, Φ y).re = ∫ y in (8 : ℝ)..T, (Φ y).re := by
      have hcontΦ : Continuous Φ := by
        simp only [hΦdef]
        exact continuous_finsetSum _ fun n _ => continuous_finsetSum _ fun d _ =>
          continuous_const.mul (((continuous_const.mul (hcont _)).add
            (continuous_const.mul (hcont _))).add (continuous_const.mul (hcont _)))
      exact (Complex.reCLM.intervalIntegral_comp_comm (hcontΦ.intervalIntegrable _ _)).symm
    rw [hre]
    have := intervalIntegral.integral_nonneg (μ := volume) (a := (8 : ℝ)) (b := T) (f := fun y => -(Φ y).re) hT
      (fun y hy => by have := hsign y hy.1; linarith)
    rw [intervalIntegral.integral_neg] at this
    linarith
  have hle : Lval.re ≤ 0 :=
    le_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim) hnonpos
  rw [hLval, Complex.ofReal_re, hc] at hle
  have hpos : (0 : ℝ) < (a : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < a)) _
  have hsq : e a * e a ≤ 0 := by
    by_contra hcon
    have hcon' : 0 < e a * e a := lt_of_not_ge hcon
    have : 0 < e a * (e a * (a : ℝ) ^ (-(1 / 2 : ℝ))) := by nlinarith
    linarith
  nlinarith [mul_self_nonneg (e a)]


end RHTower
