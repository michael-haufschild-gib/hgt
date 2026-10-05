import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenInequality

/-!
# The mollified Balazard–Saias–Yor inequality and a Nyman–Beurling criterion

Let `M` be entire, bounded on `Re s ≥ ½`, with `M(1) ≠ 0`.  Jensen's inequality on the boundary
circle, applied to `G(w) M(s)` instead of `G(w)`, gives for every finite set `Z` of zeros of `ζ`
with `Re ρ > ½`

`Σ_{ρ ∈ Z} log (|ρ|/|1 - ρ|) + log |M(1)| ≤ (1/2π) ∫ log |ζ(½+it) M(½+it)| dt/(¼ + t²)`.

The weight `dt/(2π(¼ + t²))` is a probability measure, so concavity of the logarithm bounds the
right side by `½ log ((1/2π) ∫ |ζ M|² dt/(¼ + t²))`.  Hence

`Σ_{ρ ∈ Z} log (|ρ|/|1 - ρ|) ≤ ½ log ((1/2π) ∫ |ζ M|² dt/(¼ + t²) / |M(1)|²)`,

and the Riemann hypothesis follows if, for every `ε > 0`, some admissible `M` has
`(1/2π) ∫ |ζ M|² dt/(¼ + t²) ≤ (1 + ε) |M(1)|²`.
-/

open Complex Metric Real MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-- The critical-line weight `1/(¼ + t²)` is integrable with total mass `2π`. -/
theorem integrable_and_integral_criticalLine_weight :
    Integrable (fun t : ℝ => 1 / (1 / 4 + t ^ 2)) ∧ ∫ t : ℝ, 1 / (1 / 4 + t ^ 2) = 2 * π := by
  have key : (fun t : ℝ => 1 / (1 / 4 + t ^ 2)) = fun t => 4 * (1 + (2 * t) ^ 2)⁻¹ := by
    funext t; field_simp; ring
  rw [key]
  refine ⟨(integrable_inv_one_add_sq.comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)).const_mul 4, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) 2,
    integral_univ_inv_one_add_sq, smul_eq_mul]
  norm_num
  ring

/-- A function that is almost everywhere nonzero has positive weighted mean square. -/
theorem integral_sq_criticalLine_pos {F : ℝ → ℂ} (hF0 : ∀ᵐ t, F t ≠ 0)
    (hsq : Integrable (fun t : ℝ => ‖F t‖ ^ 2 / (1 / 4 + t ^ 2))) :
    0 < ∫ t : ℝ, ‖F t‖ ^ 2 / (1 / 4 + t ^ 2) := by
  set g : ℝ → ℝ := fun t => ‖F t‖ ^ 2 / (1 / 4 + t ^ 2) with hg
  rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun t => by
    simp only [hg]; positivity) hsq]
  rw [pos_iff_ne_zero]
  intro h0
  have h1 : ∀ᵐ t, t ∉ Function.support g := measure_eq_zero_iff_ae_notMem.mp h0
  have h2 : ∀ᵐ t : ℝ, False := (h1.and hF0).mono fun t ⟨ha, hb⟩ => by
    rw [Function.notMem_support] at ha
    have : 0 < g t := by
      simp only [hg]; have := norm_pos_iff.mpr hb; positivity
    exact this.ne' ha
  have : (volume : Measure ℝ) = 0 := ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp h2)
  exact NeZero.ne (volume : Measure ℝ) this

/-- **Concavity of the logarithm against the critical-line weight.**  If `F ≠ 0` almost
everywhere and both `log |F|` and `|F|²` are integrable against `dt/(¼ + t²)`, then
`(1/2π) ∫ log |F| dt/(¼ + t²) ≤ ½ log ((1/2π) ∫ |F|² dt/(¼ + t²))`. -/
theorem integral_log_norm_le_half_log_integral_sq {F : ℝ → ℂ} (hF0 : ∀ᵐ t, F t ≠ 0)
    (hlog : Integrable (fun t : ℝ => Real.log ‖F t‖ / (1 / 4 + t ^ 2)))
    (hsq : Integrable (fun t : ℝ => ‖F t‖ ^ 2 / (1 / 4 + t ^ 2))) :
    (2 * π)⁻¹ * ∫ t : ℝ, Real.log ‖F t‖ / (1 / 4 + t ^ 2)
      ≤ 1 / 2 * Real.log ((2 * π)⁻¹ * ∫ t : ℝ, ‖F t‖ ^ 2 / (1 / 4 + t ^ 2)) := by
  obtain ⟨hwint, hw⟩ := integrable_and_integral_criticalLine_weight
  have hπ : 0 < 2 * π := by positivity
  set g : ℝ → ℝ := fun t => ‖F t‖ ^ 2 / (1 / 4 + t ^ 2) with hg
  have hgpos : 0 < ∫ t, g t := integral_sq_criticalLine_pos hF0 hsq
  set c : ℝ := (2 * π)⁻¹ * ∫ t, g t with hc
  have hc0 : 0 < c := by positivity
  have hpt : ∀ᵐ t : ℝ, 2 * (Real.log ‖F t‖ / (1 / 4 + t ^ 2)) - Real.log c * (1 / (1 / 4 + t ^ 2))
      ≤ c⁻¹ * g t - 1 / (1 / 4 + t ^ 2) := by
    filter_upwards [hF0] with t ht
    have hn : 0 < ‖F t‖ := norm_pos_iff.mpr ht
    have hw0 : 0 < 1 / 4 + t ^ 2 := by positivity
    have hlog1 := Real.log_le_sub_one_of_pos (by positivity : 0 < ‖F t‖ ^ 2 / c)
    rw [Real.log_div (by positivity) hc0.ne', Real.log_pow] at hlog1
    push_cast at hlog1
    have := mul_le_mul_of_nonneg_right hlog1 (by positivity : 0 ≤ 1 / (1 / 4 + t ^ 2))
    simp only [hg]
    have e1 : (2 * Real.log ‖F t‖ - Real.log c) * (1 / (1 / 4 + t ^ 2))
        = 2 * (Real.log ‖F t‖ / (1 / 4 + t ^ 2)) - Real.log c * (1 / (1 / 4 + t ^ 2)) := by ring
    have e2 : (‖F t‖ ^ 2 / c - 1) * (1 / (1 / 4 + t ^ 2))
        = c⁻¹ * (‖F t‖ ^ 2 / (1 / 4 + t ^ 2)) - 1 / (1 / 4 + t ^ 2) := by
      field_simp
    rw [e1, e2] at this
    exact this
  have hI1 : Integrable (fun t : ℝ => 2 * (Real.log ‖F t‖ / (1 / 4 + t ^ 2))
      - Real.log c * (1 / (1 / 4 + t ^ 2))) :=
    (hlog.const_mul 2).sub (hwint.const_mul (Real.log c))
  have hI2 : Integrable (fun t : ℝ => c⁻¹ * g t - 1 / (1 / 4 + t ^ 2)) :=
    (hsq.const_mul c⁻¹).sub hwint
  have hint := integral_mono_ae hI1 hI2 hpt
  rw [integral_sub (hlog.const_mul 2) (hwint.const_mul (Real.log c)),
    integral_sub (hsq.const_mul c⁻¹) hwint, integral_const_mul, integral_const_mul,
    integral_const_mul, hw] at hint
  have hgc : ∫ t, g t = 2 * π * c := by rw [hc]; field_simp
  rw [show (∫ t, ‖F t‖ ^ 2 / (1 / 4 + t ^ 2)) = ∫ t, g t from rfl, hgc] at hint
  have hcc : c⁻¹ * (2 * π * c) = 2 * π := by field_simp
  rw [hcc] at hint
  have : 2 * ∫ t, Real.log ‖F t‖ / (1 / 4 + t ^ 2) ≤ Real.log c * (2 * π) := by linarith
  rw [inv_mul_le_iff₀ hπ]
  linarith

/-- The mollified disc function `G(w) M(1/(1 - w))`. -/
def mollifiedZetaDisc (M : ℂ → ℂ) (w : ℂ) : ℂ := zetaDisc w * M (halfPlaneOfDisc w)

theorem mollifiedZetaDisc_zero (M : ℂ → ℂ) : mollifiedZetaDisc M 0 = M 1 := by
  rw [mollifiedZetaDisc, zetaDisc_zero, one_mul, halfPlaneOfDisc, sub_zero, inv_one]

theorem differentiableOn_mollifiedZetaDisc {M : ℂ → ℂ} (hM : Differentiable ℂ M) :
    DifferentiableOn ℂ (mollifiedZetaDisc M) {1}ᶜ := by
  intro w hw
  have hne : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have h1 : DifferentiableWithinAt ℂ halfPlaneOfDisc {1}ᶜ w :=
    (((differentiableAt_const _).sub differentiableAt_id).inv hne).differentiableWithinAt
  exact (differentiableOn_zetaDisc w hw).mul ((hM _).comp_differentiableWithinAt w h1)

theorem measurable_mollifiedZetaDisc {M : ℂ → ℂ} (hM : Differentiable ℂ M) :
    Measurable (mollifiedZetaDisc M) :=
  measurable_zetaDisc.mul (hM.continuous.measurable.comp
    ((measurable_const.sub measurable_id).inv))

theorem exists_log_norm_mollifiedZetaDisc_le {M : ℂ → ℂ}
    (hMb : ∃ B : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → ‖M s‖ ≤ B) (hM1 : M 1 ≠ 0) :
    ∃ A : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 →
      Real.log ‖mollifiedZetaDisc M w‖ ≤ A - 2 * Real.log ‖1 - w‖ := by
  obtain ⟨A₀, hA₀, hA⟩ := exists_log_norm_zetaDisc_le
  obtain ⟨B, hB⟩ := hMb
  have hB0 : 0 < B := lt_of_lt_of_le (norm_pos_iff.mpr hM1) (hB 1 (by norm_num))
  refine ⟨A₀ + |Real.log B| + 2 * Real.log 2, fun w hw hw1 => ?_⟩
  have hne : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hn0 : 0 < ‖1 - w‖ := norm_pos_iff.mpr hne
  have hn2 : ‖1 - w‖ ≤ 2 := by
    calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hlog2 : Real.log ‖1 - w‖ ≤ Real.log 2 := Real.log_le_log hn0 hn2
  have habs := le_abs_self (Real.log B)
  have habs0 := abs_nonneg (Real.log B)
  rcases eq_or_ne (mollifiedZetaDisc M w) 0 with h0 | h0
  · rw [h0, norm_zero, Real.log_zero]
    linarith
  · rw [mollifiedZetaDisc] at h0 ⊢
    have hz : zetaDisc w ≠ 0 := left_ne_zero_of_mul h0
    have hm : M (halfPlaneOfDisc w) ≠ 0 := right_ne_zero_of_mul h0
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hm)]
    have h1 := hA w hw hw1
    have h2 : Real.log ‖M (halfPlaneOfDisc w)‖ ≤ Real.log B :=
      Real.log_le_log (norm_pos_iff.mpr hm) (hB _ (re_halfPlaneOfDisc_ge hw hw1))
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith


/-- `ζ(½ + it) M(½ + it) ≠ 0` for almost every `t`. -/
theorem ae_riemannZeta_mul_ne_zero {M : ℂ → ℂ} (hM : Differentiable ℂ M) (hM1 : M 1 ≠ 0) :
    ∀ᵐ t : ℝ, riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I) ≠ 0 := by
  have hne1 : ∀ t : ℝ, (1 / 2 : ℂ) + t * I ≠ 1 := by
    intro t h; have := congrArg Complex.re h; norm_num at this
  have hinj : Function.Injective (fun t : ℝ => (1 / 2 : ℂ) + t * I) := by
    intro a b hab
    have := congrArg Complex.im hab
    simpa using this
  have hzc := countable_setOf_eq_zero_of_differentiable
    (f := fun s => zetaEntire s * M s) (differentiable_zetaEntire.mul hM) (x := 1)
    (by simp only [zetaEntire_eval_one, one_mul]; exact hM1)
  have hcount : {t : ℝ | riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I) = 0}.Countable := by
    refine (hzc.preimage hinj).mono fun t ht => ?_
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at ht ⊢
    rw [zetaEntire_eq (hne1 t), mul_assoc, ht, mul_zero]
  exact measure_eq_zero_iff_ae_notMem.mp (hcount.measure_zero _)

/-- **The mollified Balazard–Saias–Yor inequality.**  For `M` entire, bounded on `Re s ≥ ½`, with
`M(1) ≠ 0`, and finitely many zeros `ρ` of `ζ` with `Re ρ > ½`,
`Σ log (|ρ|/|1 - ρ|) + log |M(1)| ≤ (1/2π) ∫ log |ζ(½+it) M(½+it)| dt/(¼ + t²)`. -/
theorem integrable_and_sum_log_add_le_integral_log_norm_zeta_mul {M : ℂ → ℂ}
    (hM : Differentiable ℂ M) (hMb : ∃ B : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → ‖M s‖ ≤ B)
    (hM1 : M 1 ≠ 0) {Z : Finset ℂ} (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re) :
    Integrable (fun t : ℝ =>
        Real.log ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)) ∧
      ∑ ρ ∈ Z, Real.log (‖ρ‖ / ‖1 - ρ‖) + Real.log ‖M 1‖
        ≤ (2 * π)⁻¹ * ∫ t : ℝ,
            Real.log ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) := by
  set U := Z.image (fun ρ : ℂ => 1 - ρ⁻¹) with hUdef
  have hU : ∀ u ∈ U, mollifiedZetaDisc M u = 0 ∧ ‖u‖ < 1 := by
    intro u hu
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨h1, _, h3⟩ := zetaDisc_one_sub_inv (hZ ρ hρ).1 (hZ ρ hρ).2
    exact ⟨by rw [mollifiedZetaDisc, h1, zero_mul], h3⟩
  obtain ⟨hci, hle⟩ := circleIntegrable_and_sum_log_add_le_circleAverage
    (differentiableOn_mollifiedZetaDisc hM) (measurable_mollifiedZetaDisc hM)
    (by rw [mollifiedZetaDisc_zero]; exact hM1) (exists_log_norm_mollifiedZetaDisc_le hMb hM1) hU
  rw [mollifiedZetaDisc_zero] at hle
  set H : ℝ → ℝ := fun t =>
    Real.log ‖zetaEntire (1 / 2 + t * I) * M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) with hH
  have hHeq : (fun t : ℝ => Real.log ‖mollifiedZetaDisc M (circleMap 0 1 (criticalLineAngle t))‖
      / (1 / 4 + t ^ 2)) = H := by
    funext t
    simp only [hH, mollifiedZetaDisc, zetaDisc, halfPlaneOfDisc_circleMap_criticalLineAngle]
  have hHint : Integrable H := by
    have := (circleIntegrable_iff_integrable_criticalLine _).mp hci
    rwa [hHeq] at this
  have hHavg : circleAverage (fun w => Real.log ‖mollifiedZetaDisc M w‖) 0 1
      = (2 * π)⁻¹ * ∫ t, H t := by
    rw [circleAverage_eq_integral_criticalLine, hHeq]
  obtain ⟨hWint, hW0⟩ := integrable_and_integral_log_criticalLine_weight
  have hne1 : ∀ t : ℝ, (1 / 2 : ℂ) + t * I ≠ 1 := by
    intro t h; have := congrArg Complex.re h; norm_num at this
  have hae : ∀ᵐ t : ℝ,
      Real.log ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)
        = H t - (1 / 2) * (Real.log (1 / 4 + t ^ 2) / (1 / 4 + t ^ 2)) := by
    filter_upwards [ae_riemannZeta_mul_ne_zero hM hM1] with t ht
    have hsub : (1 / 2 : ℂ) + t * I - 1 ≠ 0 := sub_ne_zero.mpr (hne1 t)
    have hfac : zetaEntire (1 / 2 + t * I) * M (1 / 2 + t * I)
        = ((1 / 2 : ℂ) + t * I - 1) * (riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)) := by
      rw [zetaEntire_eq (hne1 t)]; ring
    simp only [hH]
    rw [hfac, norm_mul ((1 / 2 : ℂ) + t * I - 1), Real.log_mul (norm_ne_zero_iff.mpr hsub)
      (norm_ne_zero_iff.mpr ht), norm_half_add_mul_I_sub_one, Real.log_sqrt (by positivity)]
    ring
  have hZint : Integrable (fun t : ℝ =>
      Real.log ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)) :=
    (hHint.sub (hWint.const_mul (1 / 2))).congr (hae.mono fun t ht => ht.symm)
  have hZeq : ∫ t : ℝ,
      Real.log ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)
        = ∫ t, H t := by
    rw [integral_congr_ae hae, integral_sub hHint (hWint.const_mul (1 / 2)), integral_const_mul,
      hW0, mul_zero, sub_zero]
  refine ⟨hZint, ?_⟩
  rw [hZeq, ← hHavg]
  have hsum : ∑ u ∈ U, Real.log (1 / ‖u‖) = ∑ ρ ∈ Z, Real.log (‖ρ‖ / ‖1 - ρ‖) := by
    rw [hUdef, Finset.sum_image]
    · refine Finset.sum_congr rfl fun ρ hρ => ?_
      obtain ⟨_, h2, _⟩ := zetaDisc_one_sub_inv (hZ ρ hρ).1 (hZ ρ hρ).2
      rw [h2, one_div_div]
    · intro a _ b _ hab
      have : a⁻¹ = b⁻¹ := by simpa using hab
      exact inv_injective this
  rw [← hsum]
  exact hle

/-- **Zero location from a mollified mean square.**  For `M` entire, bounded on `Re s ≥ ½`, with
`M(1) ≠ 0` and `|ζ M|²` integrable against `dt/(¼ + t²)`,
`Σ log (|ρ|/|1 - ρ|) ≤ ½ log ((1/2π) ∫ |ζ(½+it) M(½+it)|² dt/(¼ + t²)) - log |M(1)|`. -/
theorem sum_log_le_half_log_meanSquare_zeta_mul {M : ℂ → ℂ} (hM : Differentiable ℂ M)
    (hMb : ∃ B : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → ‖M s‖ ≤ B) (hM1 : M 1 ≠ 0)
    (hsq : Integrable (fun t : ℝ =>
      ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)))
    {Z : Finset ℂ} (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re) :
    ∑ ρ ∈ Z, Real.log (‖ρ‖ / ‖1 - ρ‖)
      ≤ 1 / 2 * Real.log ((2 * π)⁻¹ * ∫ t : ℝ,
          ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2))
        - Real.log ‖M 1‖ := by
  obtain ⟨hint, hle⟩ := integrable_and_sum_log_add_le_integral_log_norm_zeta_mul hM hMb hM1 hZ
  have hF0 := ae_riemannZeta_mul_ne_zero hM hM1
  have hconc := integral_log_norm_le_half_log_integral_sq
    (F := fun t : ℝ => riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)) hF0 hint hsq
  linarith

/-- **A Nyman–Beurling criterion in the Balazard–Saias–Yor form.**  If for every `ε > 0` some
entire `M`, bounded on `Re s ≥ ½`, with `M(1) ≠ 0`, satisfies
`(1/2π) ∫ |ζ(½+it) M(½+it)|² dt/(¼ + t²) ≤ (1 + ε) |M(1)|²`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_forall_mollified_meanSquare_le
    (h : ∀ ε : ℝ, 0 < ε → ∃ M : ℂ → ℂ, Differentiable ℂ M ∧
      (∃ B : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → ‖M s‖ ≤ B) ∧ M 1 ≠ 0 ∧
      Integrable (fun t : ℝ =>
        ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) ∧
      (2 * π)⁻¹ * ∫ t : ℝ,
          ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)
        ≤ (1 + ε) * ‖M 1‖ ^ 2) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro s hs hz
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hz
  have hlt : ‖1 - s‖ < ‖s‖ := by
    have h1 : ‖1 - s‖ ^ 2 < ‖s‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  have hpos0 : 0 < ‖1 - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hs1))
  set δ : ℝ := Real.log (‖s‖ / ‖1 - s‖) with hδ
  have hδ0 : 0 < δ := Real.log_pos (by rw [one_lt_div hpos0]; exact hlt)
  set ε : ℝ := Real.exp δ - 1 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith [Real.add_one_lt_exp hδ0.ne']
  obtain ⟨M, hM, hMb, hM1, hsq, hbound⟩ := h ε hε0
  have hmain := sum_log_le_half_log_meanSquare_zeta_mul hM hMb hM1 hsq
    (Z := {s}) (fun ρ hρ => by rw [Finset.mem_singleton] at hρ; subst hρ; exact ⟨hz, hs⟩)
  rw [Finset.sum_singleton, ← hδ] at hmain
  have hM1p : 0 < ‖M 1‖ := norm_pos_iff.mpr hM1
  have hcpos : 0 < (2 * π)⁻¹ * ∫ t : ℝ,
      ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2) :=
    mul_pos (by positivity) (integral_sq_criticalLine_pos
      (F := fun t : ℝ => riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I))
      (ae_riemannZeta_mul_ne_zero hM hM1) hsq)
  have hlogc := Real.log_le_log hcpos hbound
  have h1e : 1 + ε = Real.exp δ := by rw [hε]; ring
  have hx : (1 + ε) ≠ 0 := by linarith
  have hy : ‖M 1‖ ^ 2 ≠ 0 := by positivity
  rw [Real.log_mul hx hy, h1e, Real.log_exp, Real.log_pow] at hlogc
  push_cast at hlogc
  linarith

end

end RHTower
