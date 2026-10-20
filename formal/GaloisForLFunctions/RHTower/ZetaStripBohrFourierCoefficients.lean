import GaloisForLFunctions.RHTower.CarlsonZetaMeanSquare
import GaloisForLFunctions.HTGeometry.WeylEquidistribution

/-!
# Bohr–Fourier coefficients of zeta on vertical lines of the strip

For `1/2 < σ < 1` the Dirichlet series of `ζ` does not converge on the line `Re s = σ`, but `ζ`
still has the Bohr–Fourier coefficients of that series: for every real frequency `λ`,

  `(1/T) ∫₀ᵀ ζ(σ + it) e^{iλt} dt → n^{-σ}` if `λ = log n` for some `n ≥ 1`, and `→ 0` otherwise

(`tendsto_zeta_line_mul_char_average_log`, `tendsto_zeta_line_mul_char_average_of_forall_ne`);
in particular the mean value of `ζ` on the line is `1` (`tendsto_zeta_line_average`).  Together with
Carlson's mean square `(1/T)∫₀ᵀ |ζ(σ+it)|² dt → Σ_{n ≥ 1} n^{-2σ}` (`carlson_zeta_meanSquare`),
this is Parseval's identity for the Besicovitch almost-periodic function `t ↦ ζ(σ + it)`.

The proof splits `ζ = head_M + (ζ − head_M)`.  The head times the character is a finite exponential
sum, whose Cesàro average is given by the Kronecker–Weyl theorem (`Weyl.trig_time_average`); the
tail's average is bounded, through `x ≤ a/2 + x²/(2a)`, by its Carlson mean square, which is at
most the tail mass `Σ_{n > M} n^{-2σ}`, arbitrarily small for large `M`.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

/-! ## 1. The head times a character is a finite exponential sum -/

/-- `head_M(σ + it) e^{iλt} = Σ_{n < M} (n+1)^{-σ} e^{i(λ − log(n+1)) t}`. -/
theorem zetaDirichletHead_mul_char_eq (M : ℕ) (σ t lam : ℝ) :
    zetaDirichletHead M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ)) =
      ∑ n : Fin M, (((((n : ℕ) : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) *
        Complex.exp (((lam - Real.log (((n : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I * (t : ℂ)) := by
  rw [zetaDirichletHead_eq_dirPoly, Sieve.dirPoly, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Kronecker–Weyl average of the head against a character. -/
theorem tendsto_average_zetaDirichletHead_mul_char (M : ℕ) (σ lam : ℝ) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
        zetaDirichletHead M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ))) atTop
      (𝓝 (∑ n ∈ (Finset.univ : Finset (Fin M)).filter
          (fun n : Fin M => lam - Real.log (((n : ℕ) : ℝ) + 1) = 0),
        (((((n : ℕ) : ℝ) + 1) ^ (-σ) : ℝ) : ℂ))) := by
  have h := Weyl.trig_time_average (Finset.univ : Finset (Fin M))
    (fun n : Fin M => lam - Real.log (((n : ℕ) : ℝ) + 1))
    (fun n : Fin M => (((((n : ℕ) : ℝ) + 1) ^ (-σ) : ℝ) : ℂ))
  refine h.congr' (Eventually.of_forall fun T => ?_)
  simp_rw [zetaDirichletHead_mul_char_eq]

/-- Among `n + 1 ≤ M`, only `n + 1 = n₀` has `log(n + 1) = log n₀`. -/
theorem filter_log_eq_singleton {M n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hM : n₀ ≤ M) :
    (Finset.univ : Finset (Fin M)).filter
      (fun n : Fin M => Real.log (n₀ : ℝ) - Real.log (((n : ℕ) : ℝ) + 1) = 0) =
      {⟨n₀ - 1, by omega⟩} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    have heq : Real.log (((n : ℕ) : ℝ) + 1) = Real.log (n₀ : ℝ) := by linarith
    have hpos : (0 : ℝ) < ((n : ℕ) : ℝ) + 1 := by positivity
    have hpos' : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀
    have hreal := Real.log_injOn_pos (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hpos') heq
    have h2 : (n : ℕ) + 1 = n₀ := by exact_mod_cast hreal
    exact Fin.ext (show (n : ℕ) = n₀ - 1 by omega)
  · intro h
    rw [h]
    have hcast : ((n₀ - 1 : ℕ) : ℝ) + 1 = n₀ := by exact_mod_cast Nat.sub_add_cancel hn₀
    show Real.log (n₀ : ℝ) - Real.log (((n₀ - 1 : ℕ) : ℝ) + 1) = 0
    rw [hcast, sub_self]

/-! ## 2. The tail average is controlled by the Carlson mean square -/

theorem norm_exp_real_mul_I_mul_real (lam t : ℝ) :
    ‖Complex.exp ((lam : ℂ) * I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- `x ≤ a/2 + x²/(2a)` for `a > 0`. -/
theorem real_le_half_add_sq_div {x a : ℝ} (ha : 0 < a) :
    x ≤ a / 2 + x ^ 2 / (2 * a) := by
  have h2a : (0 : ℝ) < 2 * a := by positivity
  calc x = 2 * a * x / (2 * a) := (mul_div_cancel_left₀ x h2a.ne').symm
    _ ≤ (a ^ 2 + x ^ 2) / (2 * a) :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (x - a)]) h2a.le
    _ = a / 2 + x ^ 2 / (2 * a) := by
        rw [add_div, sq a, mul_div_mul_right _ _ ha.ne']

/-- **Bohr–Fourier averages of `ζ`, general form.**  If the Kronecker–Weyl limit of the head
average stabilises to `L` for large `M`, the Cesàro average of `ζ(σ + it) e^{iλt}` tends to `L`. -/
theorem tendsto_zeta_line_mul_char_average_of_head {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    (lam : ℝ) {L : ℂ}
    (hL : ∀ᶠ M : ℕ in atTop, (∑ n ∈ (Finset.univ : Finset (Fin M)).filter
        (fun n : Fin M => lam - Real.log (((n : ℕ) : ℝ) + 1) = 0),
          (((((n : ℕ) : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)) = L) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
        riemannZeta ((σ : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ)))
      atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set a : ℝ := ε / 3 with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨M, hM1, hM2⟩ := (((tendsto_zetaCoefficientTailMass hσ).eventually
    (gt_mem_nhds (show 0 < a ^ 2 / 2 by positivity))).and hL).exists
  have hMa : zetaCoefficientTailMass M σ < a ^ 2 :=
    lt_of_lt_of_le hM1 (half_le_self (sq_nonneg a))
  have hhead := tendsto_average_zetaDirichletHead_mul_char M σ lam
  rw [hM2] at hhead
  have hcarl := carlson_zeta_tail_meanSquare M hσ hσ1
  filter_upwards [Metric.tendsto_nhds.mp hhead (ε / 3) (by positivity),
    hcarl.eventually (gt_mem_nhds hMa), eventually_gt_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hdec : ∀ t : ℝ,
      riemannZeta ((σ : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ)) =
        zetaDirichletTail M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ)) +
          zetaDirichletHead M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ)) := by
    intro t
    unfold zetaDirichletTail
    ring
  have hcT : Continuous fun t : ℝ =>
      zetaDirichletTail M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ)) :=
    (continuous_zetaDirichletTail M hσ1.ne).mul (by fun_prop)
  have hcH : Continuous fun t : ℝ =>
      zetaDirichletHead M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ)) :=
    (continuous_zetaDirichletHead M σ).mul (by fun_prop)
  have hsplit : (∫ t in (0 : ℝ)..T,
      riemannZeta ((σ : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ))) =
      (∫ t in (0 : ℝ)..T, zetaDirichletTail M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ))) +
        ∫ t in (0 : ℝ)..T, zetaDirichletHead M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ)) := by
    simp_rw [hdec]
    exact intervalIntegral.integral_add (hcT.intervalIntegrable _ _) (hcH.intervalIntegrable _ _)
  have hcont_tail : Continuous fun t => ‖zetaDirichletTail M σ t‖ :=
    (continuous_zetaDirichletTail M hσ1.ne).norm
  have htail_norm : ‖(T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      zetaDirichletTail M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ))‖ ≤
      T⁻¹ * ∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (intervalIntegral.norm_integral_le_integral_norm hT0.le).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [norm_mul, norm_exp_real_mul_I_mul_real, mul_one]
  have hamgm : (∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖) ≤
      T * (a / 2) + (∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖ ^ 2) / (2 * a) := by
    have hf : IntervalIntegrable (fun _ : ℝ => a / 2) volume 0 T :=
      continuous_const.intervalIntegrable _ _
    have hg : IntervalIntegrable (fun t => ‖zetaDirichletTail M σ t‖ ^ 2 / (2 * a)) volume 0 T :=
      ((hcont_tail.pow 2).div_const _).intervalIntegrable _ _
    have h1 : (∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖) ≤
        ∫ t in (0 : ℝ)..T, (a / 2 + ‖zetaDirichletTail M σ t‖ ^ 2 / (2 * a)) :=
      intervalIntegral.integral_mono_on hT0.le (hcont_tail.intervalIntegrable _ _) (hf.add hg)
        (fun t _ => real_le_half_add_sq_div ha0)
    rw [intervalIntegral.integral_add hf hg, intervalIntegral.integral_const,
      intervalIntegral.integral_div, smul_eq_mul, sub_zero] at h1
    exact h1
  have htail_small : T⁻¹ * (∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖) < a := by
    have e : T⁻¹ * (T * (a / 2) + (∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖ ^ 2) / (2 * a)) =
        a / 2 + ((∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖ ^ 2) / T) / (2 * a) := by
      rw [mul_add, inv_mul_cancel_left₀ hT0.ne']
      congr 1
      rw [← div_eq_inv_mul, div_div, div_div, mul_comm]
    have h2 : T⁻¹ * (∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖) ≤
        a / 2 + ((∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖ ^ 2) / T) / (2 * a) :=
      e ▸ mul_le_mul_of_nonneg_left hamgm (by positivity)
    have h3 : ((∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖ ^ 2) / T) / (2 * a) <
        a ^ 2 / (2 * a) := div_lt_div_of_pos_right hT2 (by positivity)
    have h4 : a ^ 2 / (2 * a) = a / 2 := by rw [sq, mul_div_mul_right _ _ ha0.ne']
    linarith
  rw [hsplit, mul_add, dist_eq_norm, add_sub_assoc]
  calc ‖(T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T,
          zetaDirichletTail M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ))) +
        ((T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T,
          zetaDirichletHead M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ))) - L)‖
      ≤ ‖(T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
          zetaDirichletTail M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ))‖ +
        ‖(T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T,
          zetaDirichletHead M σ t * Complex.exp ((lam : ℂ) * I * (t : ℂ))) - L‖ :=
        norm_add_le _ _
    _ < a + ε / 3 := by
        rw [dist_eq_norm] at hT1
        exact add_lt_add (lt_of_le_of_lt htail_norm htail_small) hT1
    _ ≤ ε := by rw [ha]; linarith

/-! ## 3. The coefficients -/

/-- **Bohr–Fourier coefficient at `log n₀`.**  For `1/2 < σ < 1` and `n₀ ≥ 1`,
`(1/T) ∫₀ᵀ ζ(σ + it) n₀^{it} dt → n₀^{-σ}`. -/
theorem tendsto_zeta_line_mul_char_average_log {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
        riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          Complex.exp ((Real.log (n₀ : ℝ) : ℂ) * I * (t : ℂ)))
      atTop (𝓝 (((n₀ : ℝ) ^ (-σ) : ℝ) : ℂ)) := by
  refine tendsto_zeta_line_mul_char_average_of_head hσ hσ1 (Real.log (n₀ : ℝ)) ?_
  filter_upwards [eventually_ge_atTop n₀] with M hM
  rw [filter_log_eq_singleton hn₀ hM, Finset.sum_singleton]
  have hcast : ((n₀ - 1 : ℕ) : ℝ) + 1 = n₀ := by exact_mod_cast Nat.sub_add_cancel hn₀
  show (((((n₀ - 1 : ℕ) : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) = (((n₀ : ℝ) ^ (-σ) : ℝ) : ℂ)
  rw [hcast]

/-- **Vanishing off the spectrum.**  If `λ` is not `log n` for any `n ≥ 1`, then
`(1/T) ∫₀ᵀ ζ(σ + it) e^{iλt} dt → 0`. -/
theorem tendsto_zeta_line_mul_char_average_of_forall_ne {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    {lam : ℝ} (hlam : ∀ n : ℕ, 1 ≤ n → lam ≠ Real.log (n : ℝ)) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
        riemannZeta ((σ : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ)))
      atTop (𝓝 0) := by
  refine tendsto_zeta_line_mul_char_average_of_head hσ hσ1 lam (Eventually.of_forall fun M => ?_)
  have hempty : (Finset.univ : Finset (Fin M)).filter
      (fun n : Fin M => lam - Real.log (((n : ℕ) : ℝ) + 1) = 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro n _ h
    have h' : lam = Real.log (((n : ℕ) + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact hlam ((n : ℕ) + 1) (by omega) h'
  rw [hempty, Finset.sum_empty]

/-- **The mean value of `ζ` on a line of the strip is `1`.** -/
theorem tendsto_zeta_line_average {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, riemannZeta ((σ : ℂ) + (t : ℂ) * I))
      atTop (𝓝 1) := by
  have h := tendsto_zeta_line_mul_char_average_log hσ hσ1 (n₀ := 1) le_rfl
  simpa using h

end RHTower
