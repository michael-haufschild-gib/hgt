import GaloisForLFunctions.TransHorizonIncidenceMechanics.OscillatingPrimePatternsReadTheCriticalZeros

/-!
# The endpoint `a = 1` and the complete phase diagram of oscillating prime patterns

For `a ∈ [−1, 1]` and `t₀ ∈ ℝ`, let `oscPattern a t₀` be the completely multiplicative pattern with
`f(p) = a cos(t₀ log p)` at the primes and `oscWeight a t₀ d = f(d) d^{-1/2}` its half-damped
weight. `OscillatingPrimePatternsReadTheCriticalZeros` established that `oscWeight a t₀` has bounded
receiver whenever `−1 ≤ a < 1` and `t₀ ≠ 0`. Here we resolve the critical endpoint `a = 1` at every
non-zero frequency `t₀ ≠ 0` and assemble the complete phase diagram on `[−1, 1] × ℝ`:

* **Height-shifted local pole obstruction (`not_receiverBounded_of_sq_norm_dirichletSeries_ge_at_height`).**
  If `c` is half-damped, `ζ(1/2 + it₀) ≠ 0` (`t₀ > 0`), and `|C(s)|² ≥ κ / |s − (1/2 + it₀)|` near
  `1/2 + it₀` on `Re s > 1/2`, then `¬ ReceiverBounded c`: integrating `|ζ(s)(C(s) − m)/s|²` along
  `t ∈ [t₀, t₀ + r]` on the line `Re s = 1/2 + u` yields a lower bound `κ' log((u + r)/u) − O(1)`
  that diverges as `u → 0⁺`.
* **Necessity at `a = 1` (`not_receiverBounded_oscWeight_one_of_zeta_ne_zero`).**
  At `a = 1`, `t₀ > 0`, the Euler lower bound `|F(w)| ≥ e^{-2S} |ζ(w − it₀)|^{1/2} |ζ(w + it₀)|^{1/2}`
  at `w = s + 1/2` combines the simple pole `|ζ(w − it₀)| ≥ 1/(2|s − (1/2 + it₀)|)` with the
  non-vanishing `ζ(1 + 2it₀) ≠ 0` on the line `Re = 1` to produce a `κ / |s − (1/2 + it₀)|`
  singularity of `|C(s)|²`. Hence `oscWeight 1 t₀` is unpaid whenever `ζ(1/2 + it₀) ≠ 0`.
* **Sufficiency at `a = 1` (`receiverBounded_oscWeight_one_of_zeta_eq_zero`).**
  Conversely, if `ζ(1/2 + it₀) = 0` (`t₀ > 0`), the mean-value theorem on the convex compact box
  `[1/2, 3/4] × [0, 2t₀ + 2]` gives `|ζ(s)| ≤ L |s − (1/2 + it₀)|`. Multiplying by the small-height
  bound `|C(s) − P| ≤ B |s − (1/2 + it₀)|^{-1/2} + |P|` cancels the singularity at `s = 1/2 + it₀`,
  making the boundary line integrand uniformly bounded on `(0, 2t₀ + 2]`; combined with the
  large-height bound on `t > 2t₀ + 2`, the line-energy criterion pays the receiver.
* **The complete phase diagram (`receiverBounded_oscWeight_iff`).**
  For every `a ∈ [−1, 1]` and `t₀ ∈ ℝ`,
  `ReceiverBounded (oscWeight a t₀) ↔ (t₀ = 0 ∧ a < 1/2) ∨ (t₀ ≠ 0 ∧ (a < 1 ∨ ζ(1/2 + it₀) = 0))`.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Non-vanishing of `ζ` in a neighbourhood and the height-shifted pole obstruction -/

/-- If `s₀ ≠ 1` and `ζ(s₀) ≠ 0`, then `|ζ(s)| ≥ |ζ(s₀)| / 2` on a disc around `s₀`. -/
theorem exists_norm_zeta_ge_near_of_ne_zero {s₀ : ℂ} (hs₀1 : s₀ ≠ 1)
    (hζ0 : riemannZeta s₀ ≠ 0) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ s : ℂ, ‖s - s₀‖ < r₁ → ‖riemannZeta s₀‖ / 2 ≤ ‖riemannZeta s‖ := by
  have hpos : 0 < ‖riemannZeta s₀‖ / 2 := half_pos (norm_pos_iff.mpr hζ0)
  have hcont : ContinuousAt riemannZeta s₀ := (differentiableAt_riemannZeta hs₀1).continuousAt
  obtain ⟨r₁, hr₁, hball⟩ := Metric.continuousAt_iff.mp hcont (‖riemannZeta s₀‖ / 2) hpos
  refine ⟨r₁, hr₁, fun s hs => ?_⟩
  have hd : ‖riemannZeta s - riemannZeta s₀‖ < ‖riemannZeta s₀‖ / 2 := by
    simpa [dist_eq_norm] using hball hs
  have htri : ‖riemannZeta s₀‖ - ‖riemannZeta s‖ ≤ ‖riemannZeta s - riemannZeta s₀‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le _ _
  linarith

/-- **A local `|s − (1/2 + it₀)|^{-1/2}` singularity at a non-zero of `ζ` is never paid.**
If `c` is half-damped, `t₀ > 0`, `ζ(1/2 + it₀) ≠ 0`, and `|C(s)|² ≥ κ / |s − (1/2 + it₀)|` for
`Re s > 1/2` in a neighbourhood of `1/2 + it₀`, then `¬ ReceiverBounded c`. -/
theorem not_receiverBounded_of_sq_norm_dirichletSeries_ge_at_height {K κ ρ₀ t₀ : ℝ} {c : ℕ → ℝ}
    (hc : DampedClass K (1 / 2) c) (ht₀ : 0 < t₀)
    (hζ0 : riemannZeta (1 / 2 + (t₀ : ℂ) * I) ≠ 0) (hκ : 0 < κ) (hρ₀ : 0 < ρ₀)
    (hlow : ∀ s : ℂ, 1 / 2 < s.re → ‖s - (1 / 2 + (t₀ : ℂ) * I)‖ < ρ₀ →
      κ / ‖s - (1 / 2 + (t₀ : ℂ) * I)‖ ≤ ‖weightDirichletSeries c s‖ ^ 2) :
    ¬ ReceiverBounded c := by
  rintro ⟨E, hE⟩
  set m : ℝ := ∑' d : ℕ, c d / d
  set s₀ : ℂ := 1 / 2 + (t₀ : ℂ) * I
  have hs₀1 : s₀ ≠ 1 := by
    intro h
    have := congr_arg Complex.re h
    simp [s₀] at this
  obtain ⟨r₁, hr₁, hζh⟩ := exists_norm_zeta_ge_near_of_ne_zero hs₀1 hζ0
  set δ₀ : ℝ := ‖riemannZeta s₀‖ / 2
  have hδ₀ : 0 < δ₀ := half_pos (norm_pos_iff.mpr hζ0)
  set r : ℝ := min (min ρ₀ r₁ / 4) (1 / 4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr4 : r ≤ 1 / 4 := min_le_right _ _
  have hrρ : 2 * r < ρ₀ := by
    have := min_le_left (min ρ₀ r₁ / 4) (1 / 4)
    have := min_le_left ρ₀ r₁
    linarith
  have hr1 : 2 * r < r₁ := by
    have := min_le_left (min ρ₀ r₁ / 4) (1 / 4)
    have := min_le_right ρ₀ r₁
    linarith
  set S₀ : ℝ := 1 + t₀ + r
  have hS₀ : 0 < S₀ := by positivity
  set α : ℝ := (δ₀ / S₀) ^ 2
  have hα : 0 < α := by positivity
  set κ' : ℝ := α * κ / 2
  have hκ' : 0 < κ' := by positivity
  -- pointwise lower bound on the segment `t ∈ [t₀, t₀ + r]`
  have hpt : ∀ u t : ℝ, 0 < u → u ≤ r → t₀ ≤ t → t ≤ t₀ + r →
      κ' * (u + (t - t₀))⁻¹ - α * m ^ 2 ≤ lineIntegrand c m (1 / 2 + u) t := by
    intro u t hu hur htt₀ htr
    set s : ℂ := (((1 / 2 + u : ℝ)) : ℂ) + (t : ℂ) * I
    have hs2 : s - s₀ = (u : ℂ) + ((t - t₀ : ℝ) : ℂ) * I := by
      simp only [s, s₀]; push_cast; ring
    have hτ0 : 0 ≤ t - t₀ := by linarith
    have hτr : t - t₀ ≤ r := by linarith
    have hnorm_ut : ‖(u : ℂ) + ((t - t₀ : ℝ) : ℂ) * I‖ ≤ u + (t - t₀) := by
      have := Complex.norm_le_abs_re_add_abs_im ((u : ℂ) + ((t - t₀ : ℝ) : ℂ) * I)
      simpa [abs_of_pos hu, abs_of_nonneg hτ0] using this
    have hζs : δ₀ ≤ ‖riemannZeta s‖ := hζh s (by rw [hs2]; linarith)
    have hsre : s.re = 1 / 2 + u := by simp [s]
    have hsS₀ : ‖s‖ ≤ S₀ := by
      have := Complex.norm_le_abs_re_add_abs_im s
      have him : s.im = t := by simp [s]
      rw [hsre, him, abs_of_pos (by linarith), abs_of_pos (by linarith)] at this
      simp only [S₀]
      linarith
    have hs0 : 0 < ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rw [hsre, abs_of_pos (by linarith)] at this
      linarith
    have hP2 : κ / (u + (t - t₀)) ≤ ‖weightDirichletSeries c s‖ ^ 2 := by
      have h := hlow s (by rw [hsre]; linarith) (by rw [hs2]; linarith)
      rw [hs2] at h
      exact le_trans (div_le_div_of_nonneg_left hκ.le (by linarith) hnorm_ut) h
    set P := ‖weightDirichletSeries c s‖
    set Y := ‖weightDirichletSeries c s - (m : ℂ)‖
    have hPY : P ≤ Y + |m| := by
      have h := norm_sub_norm_le (weightDirichletSeries c s) (m : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at h
      linarith
    have hY0 : 0 ≤ Y := norm_nonneg _
    have hP0 : 0 ≤ P := norm_nonneg _
    have hYP : P ^ 2 / 2 - m ^ 2 ≤ Y ^ 2 := by
      have h := pow_le_pow_left₀ hP0 hPY 2
      nlinarith [sq_nonneg (Y - |m|), sq_abs m]
    have hint : lineIntegrand c m (1 / 2 + u) t = (‖riemannZeta s‖ * Y / ‖s‖) ^ 2 := by
      simp only [lineIntegrand, norm_div, norm_mul]
      rfl
    rw [hint]
    have hquot : δ₀ / S₀ * Y ≤ ‖riemannZeta s‖ * Y / ‖s‖ := by
      rw [div_mul_eq_mul_div]
      exact div_le_div (mul_nonneg hδ₀.le hY0) (mul_le_mul_of_nonneg_right hζs hY0) hs0 hsS₀
    have hsq : α * Y ^ 2 ≤ (‖riemannZeta s‖ * Y / ‖s‖) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hquot 2
      simpa only [α, mul_pow] using h
    have hκe : κ' * (u + (t - t₀))⁻¹ = α * (κ / (u + (t - t₀)) / 2) := by
      simp only [κ', div_eq_mul_inv]; ring
    rw [hκe]
    nlinarith [mul_le_mul_of_nonneg_left hYP hα.le, mul_le_mul_of_nonneg_left hP2 hα.le]
  have hE0 : 0 ≤ E := by simpa [weightPronicEnergy] using hE 0
  have hup : ∀ u : ℝ, 0 < u → u ≤ r → ∫ t, lineIntegrand c m (1 / 2 + u) t ≤ 4 * Real.pi * E := by
    intro u hu hur
    have hσ : 1 / 2 < 1 / 2 + u := by linarith
    have hσ1 : 1 / 2 + u < 1 := by linarith
    have hid := sum_sq_mul_mellinCell_eq_lineEnergy hc hσ hσ1
    have hcap := tsum_sq_mul_mellinCell_le_of_energy (weightCenteredPrefix_zero c m) hσ.le hE
    have h : (1 / 2 + u) / Real.pi * ∫ t, lineIntegrand c m (1 / 2 + u) t ≤ 4 * (1 / 2 + u) * E :=
      hid.symm.le.trans hcap
    have hpi := Real.pi_pos
    rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at h
    nlinarith
  have hlowI : ∀ u : ℝ, 0 < u → u ≤ r →
      κ' * Real.log ((u + r) / u) - α * m ^ 2 * r ≤ ∫ t, lineIntegrand c m (1 / 2 + u) t := by
    intro u hu hur
    have hσ : 1 / 2 < 1 / 2 + u := by linarith
    have hσ1 : 1 / 2 + u < 1 := by linarith
    have hfi : Integrable (lineIntegrand c m (1 / 2 + u)) := integrable_lineEnergy hc hσ hσ1
    have hf0 : 0 ≤ᵐ[volume] lineIntegrand c m (1 / 2 + u) :=
      Eventually.of_forall fun t => by simp only [Pi.zero_apply, lineIntegrand]; positivity
    have hle : t₀ ≤ t₀ + r := by linarith
    have hinv : IntervalIntegrable (fun t : ℝ => (u + (t - t₀))⁻¹) volume t₀ (t₀ + r) := by
      refine ContinuousOn.intervalIntegrable
        ((continuousOn_const.add (continuousOn_id.sub continuousOn_const)).inv₀ ?_)
      intro t ht
      rw [uIcc_of_le hle] at ht
      have : 0 < u + (t - t₀) := by linarith [ht.1]
      exact this.ne'
    have hg : IntervalIntegrable (fun t : ℝ => κ' * (u + (t - t₀))⁻¹ - α * m ^ 2)
        volume t₀ (t₀ + r) :=
      (hinv.const_mul κ').sub intervalIntegrable_const
    have hval : ∫ t in t₀..(t₀ + r), (κ' * (u + (t - t₀))⁻¹ - α * m ^ 2) =
        κ' * Real.log ((u + r) / u) - α * m ^ 2 * r := by
      rw [intervalIntegral.integral_sub (hinv.const_mul κ') intervalIntegrable_const,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right (fun τ => (u + τ)⁻¹) t₀,
        sub_self, add_sub_cancel_left,
        intervalIntegral.integral_comp_add_left (fun x => x⁻¹),
        add_zero, integral_inv_of_pos hu (by linarith),
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    calc κ' * Real.log ((u + r) / u) - α * m ^ 2 * r
        = ∫ t in t₀..(t₀ + r), (κ' * (u + (t - t₀))⁻¹ - α * m ^ 2) := hval.symm
      _ ≤ ∫ t in t₀..(t₀ + r), lineIntegrand c m (1 / 2 + u) t :=
          intervalIntegral.integral_mono_on hle hg hfi.intervalIntegrable fun t ht =>
            hpt u t hu hur ht.1 ht.2
      _ = ∫ t in Ioc t₀ (t₀ + r), lineIntegrand c m (1 / 2 + u) t :=
          intervalIntegral.integral_of_le hle
      _ ≤ ∫ t, lineIntegrand c m (1 / 2 + u) t := setIntegral_le_integral hfi hf0
  set X : ℝ := (4 * Real.pi * E + α * m ^ 2 * r + 1) / κ'
  have hX : 0 < X := by
    have := Real.pi_pos
    positivity
  set u : ℝ := r * Real.exp (-X)
  have hu : 0 < u := by positivity
  have hur : u ≤ r := mul_le_of_le_one_right hr.le (Real.exp_le_one_iff.mpr (by linarith))
  have hlog : X ≤ Real.log ((u + r) / u) := by
    have hru : r / u = Real.exp X := by
      simp only [u]
      rw [div_mul_eq_div_div, div_self hr.ne', one_div, ← Real.exp_neg, neg_neg]
    calc X = Real.log (r / u) := by rw [hru, Real.log_exp]
      _ ≤ Real.log ((u + r) / u) :=
          Real.log_le_log (div_pos hr hu) (div_le_div_of_nonneg_right (by linarith) hu.le)
  have h1 := hlowI u hu hur
  have h2 := hup u hu hur
  have hκX : κ' * X = 4 * Real.pi * E + α * m ^ 2 * r + 1 := by
    simp only [X]; field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog hκ'.le]

/-! ### Necessity at `a = 1`: non-zeros of `ζ(1/2 + it₀)` obstruct the receiver -/

/-- **At `a = 1` and `t₀ > 0`, a non-zero of `ζ(1/2 + it₀)` makes the receiver unpaid.** -/
theorem not_receiverBounded_oscWeight_one_pos_of_zeta_ne_zero {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hζ0 : riemannZeta (1 / 2 + (t₀ : ℂ) * I) ≠ 0) :
    ¬ ReceiverBounded (oscWeight 1 t₀) := by
  set s₀ : ℂ := 1 / 2 + (t₀ : ℂ) * I
  set v₀ : ℂ := 1 + 2 * (t₀ : ℂ) * I
  have hv₀re : 1 ≤ v₀.re := by simp [v₀]
  have hv₀1 : v₀ ≠ 1 := by
    intro h
    have := congr_arg Complex.im h
    simp [v₀] at this
    linarith
  have hζv₀ : riemannZeta v₀ ≠ 0 := riemannZeta_ne_zero_of_one_le_re hv₀re
  obtain ⟨ρ₁, hρ₁, hnear1⟩ := exists_norm_zeta_ge_near_one
  obtain ⟨ρ₂, hρ₂, hnearv⟩ := exists_norm_zeta_ge_near_of_ne_zero hv₀1 hζv₀
  set c₀ : ℝ := ‖riemannZeta v₀‖ / 2
  have hc₀ : 0 < c₀ := half_pos (norm_pos_iff.mpr hζv₀)
  set E2m : ℝ := Real.exp (-(2 * primeSquareMass))
  have hE2m : 0 < E2m := Real.exp_pos _
  refine not_receiverBounded_of_sq_norm_dirichletSeries_ge_at_height
    (dampedClass_oscWeight (by norm_num) t₀) ht₀ hζ0
    (κ := E2m ^ 2 * (c₀ / 2)) (ρ₀ := min ρ₁ ρ₂) (by positivity) (lt_min hρ₁ hρ₂) ?_
  intro s hs hdist
  set w : ℂ := s + 1 / 2
  have hw : 1 < w.re := by simp [w]; linarith
  have hwm : w - (t₀ : ℂ) * I - 1 = s - s₀ := by simp only [w, s₀]; ring
  have hwp : w + (t₀ : ℂ) * I - v₀ = s - s₀ := by simp only [w, v₀, s₀]; ring
  have hwm1 : w - (t₀ : ℂ) * I ≠ 1 := by
    intro h
    have := congr_arg Complex.re h
    simp [w] at this
    linarith
  have hdpos : 0 < ‖s - s₀‖ := norm_pos_iff.mpr (by rw [← hwm]; exact sub_ne_zero.mpr hwm1)
  have h1 : 1 / (2 * ‖s - s₀‖) ≤ ‖riemannZeta (w - (t₀ : ℂ) * I)‖ := by
    have h := hnear1 (w - (t₀ : ℂ) * I) hwm1
      (by rw [hwm]; exact hdist.trans_le (min_le_left _ _))
    rwa [hwm] at h
  have h2 : c₀ ≤ ‖riemannZeta (w + (t₀ : ℂ) * I)‖ :=
    hnearv (w + (t₀ : ℂ) * I) (by rw [hwp]; exact hdist.trans_le (min_le_right _ _))
  have hprod : c₀ / (2 * ‖s - s₀‖) ≤
      ‖riemannZeta (w - (t₀ : ℂ) * I)‖ * ‖riemannZeta (w + (t₀ : ℂ) * I)‖ := by
    calc c₀ / (2 * ‖s - s₀‖) = 1 / (2 * ‖s - s₀‖) * c₀ := by ring
      _ ≤ ‖riemannZeta (w - (t₀ : ℂ) * I)‖ * ‖riemannZeta (w + (t₀ : ℂ) * I)‖ :=
          mul_le_mul h1 h2 hc₀.le (norm_nonneg _)
  have hlowF := (norm_oscSeries_le_ge (a := 1) (by norm_num) t₀ hw).2
  rw [ ← weightDirichletSeries_oscWeight 1 t₀ s] at hlowF
  have hsq := pow_le_pow_left₀ (by positivity) hlowF 2
  set Z := ‖riemannZeta (w - (t₀ : ℂ) * I)‖ * ‖riemannZeta (w + (t₀ : ℂ) * I)‖
  have hZ0 : 0 ≤ Z := by positivity
  have hZpow : (Z ^ ((1 : ℝ) / 2)) ^ 2 = Z := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0]
    norm_num
  calc E2m ^ 2 * (c₀ / 2) / ‖s - s₀‖
      = E2m ^ 2 * (c₀ / (2 * ‖s - s₀‖)) := by ring
    _ ≤ E2m ^ 2 * Z := mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    _ = (E2m * Z ^ ((1 : ℝ) / 2)) ^ 2 := by rw [mul_pow, hZpow]
    _ ≤ ‖weightDirichletSeries (oscWeight 1 t₀) s‖ ^ 2 := hsq

/-- **At `a = 1` and `t₀ ≠ 0`, a non-zero of `ζ(1/2 + it₀)` makes the receiver unpaid.** -/
theorem not_receiverBounded_oscWeight_one_of_zeta_ne_zero {t₀ : ℝ} (ht₀ : t₀ ≠ 0)
    (hζ0 : riemannZeta (1 / 2 + (t₀ : ℂ) * I) ≠ 0) :
    ¬ ReceiverBounded (oscWeight 1 t₀) := by
  rcases lt_or_gt_of_ne ht₀ with hneg | hpos
  · rw [← oscWeight_neg 1 t₀]
    refine not_receiverBounded_oscWeight_one_pos_of_zeta_ne_zero (by linarith) ?_
    have hconj : (1 / 2 : ℂ) + ((-t₀ : ℝ) : ℂ) * I =
        starRingEnd ℂ ((1 / 2 : ℂ) + (t₀ : ℂ) * I) := by
      simp [Complex.conj_ofReal]
      ring
    rw [hconj, riemannZeta_conj]
    exact map_ne_zero_iff (starRingEnd ℂ) (RingHom.injective _) |>.mpr hζ0
  · exact not_receiverBounded_oscWeight_one_pos_of_zeta_ne_zero hpos hζ0

/-! ### Sufficiency at `a = 1`: a critical zero at `1/2 + it₀` cancels the pole -/

/-- If `ζ(1/2 + it₀) = 0` (`t₀ > 0`), then `|ζ(s)| ≤ L |s − (1/2 + it₀)|` on the box
`1/2 ≤ Re s ≤ 3/4`, `0 ≤ Im s ≤ 2t₀ + 2`. -/
theorem exists_norm_zeta_le_mul_norm_sub_of_eq_zero {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hζ0 : riemannZeta (1 / 2 + (t₀ : ℂ) * I) = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 → 0 ≤ t → t ≤ 2 * t₀ + 2 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        L * ‖(σ : ℂ) + (t : ℂ) * I - (1 / 2 + (t₀ : ℂ) * I)‖ := by
  set T : ℝ := 2 * t₀ + 2
  set K : Set ℂ := (Icc (1 / 2 : ℝ) (3 / 4)) ×ℂ (Icc (0 : ℝ) T)
  have hKcomp : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKconv : Convex ℝ K := (convex_Icc (1 / 2 : ℝ) (3 / 4)).reProdIm (convex_Icc 0 T)
  have hne1 : ∀ z ∈ K, z ≠ 1 := fun z hz h => by
    have hre := ((Complex.mem_reProdIm.mp hz).1).2
    rw [h, one_re] at hre
    norm_num at hre
  have hcont : ContinuousOn (deriv riemannZeta) K := fun z hz => by
    have hana : AnalyticAt ℂ riemannZeta z :=
      DifferentiableOn.analyticAt
        (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt)
        (isOpen_compl_singleton.mem_nhds (hne1 z hz))
    exact hana.deriv.continuousAt.continuousWithinAt
  obtain ⟨L₀, hL₀⟩ := hKcomp.exists_bound_of_continuousOn hcont
  set L : ℝ := max L₀ 0
  refine ⟨L, le_max_right _ _, fun σ t hσ hσ' ht htT => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I
  set s₀ : ℂ := 1 / 2 + (t₀ : ℂ) * I
  have hsK : s ∈ K := by
    rw [Complex.mem_reProdIm]
    simp only [s, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    exact ⟨⟨hσ, hσ'⟩, ⟨ht, htT⟩⟩
  have hs₀K : s₀ ∈ K := by
    rw [Complex.mem_reProdIm]
    simp only [s₀, one_div, add_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self',
      mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
      add_im, inv_im, im_ofNat, neg_zero, zero_div, mul_im, zero_add]
    exact ⟨⟨le_rfl, by norm_num⟩, ⟨ht₀.le, by simp [T]; linarith⟩⟩
  have hlip := hKconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := riemannZeta) (f' := deriv riemannZeta) (C := L)
    (fun z hz => (differentiableAt_riemannZeta (hne1 z hz)).hasDerivAt.hasDerivWithinAt)
    (fun z hz => (hL₀ z hz).trans (le_max_left _ _)) hs₀K hsK
  rwa [hζ0, sub_zero] at hlip

/-- **At `a = 1` and `t₀ > 0`, a zero of `ζ(1/2 + it₀)` pays the receiver.** -/
theorem receiverBounded_oscWeight_one_pos_of_zeta_eq_zero {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hζ0 : riemannZeta (1 / 2 + (t₀ : ℂ) * I) = 0) :
    ReceiverBounded (oscWeight 1 t₀) := by
  obtain ⟨B, hB0, hBs⟩ := exists_norm_oscSeries_le_small (a := 1) (by norm_num) (by norm_num) ht₀
  obtain ⟨L, hL0, hLip⟩ := exists_norm_zeta_le_mul_norm_sub_of_eq_zero ht₀ hζ0
  set T : ℝ := 2 * t₀ + 2
  have hT : 2 ≤ T := by simp only [T]; linarith
  set P : ℝ := ∑' d : ℕ, oscWeight 1 t₀ d / d
  set E2 : ℝ := Real.exp (2 * primeSquareMass)
  set s₀ : ℂ := 1 / 2 + (t₀ : ℂ) * I
  set M₀ : ℝ := L * B * (T + 1) ^ (1 / 2 : ℝ) + L * (T + 1) * |P|
  have hM₀ : 0 ≤ M₀ := by positivity
  set A : ℝ := 4 * M₀ ^ 2
  have hA0 : 0 ≤ A := by positivity
  have hwre : ∀ σ t : ℝ, ((σ : ℂ) + (t : ℂ) * I + 1 / 2).re = σ + 1 / 2 := fun σ t => by simp
  have hwim : ∀ σ t : ℝ, ((σ : ℂ) + (t : ℂ) * I + 1 / 2).im = t := fun σ t => by simp
  have hg : IntegrableOn (fun _ : ℝ => A) (Ioc 0 T) := integrableOn_const (by simp)
  have hsmall : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < t → t ≤ T → t ≠ t₀ →
      lineIntegrand (oscWeight 1 t₀) P σ t ≤ A := by
    intro σ t hσ hσ' ht htT _
    set s : ℂ := (σ : ℂ) + (t : ℂ) * I
    set w : ℂ := s + 1 / 2
    have hF := hBs w (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; exact ht) (by rw [hwim]; exact htT)
    have hws₀ : w - (t₀ : ℂ) * I - 1 = s - s₀ := by simp only [w, s, s₀]; ring
    rw [hws₀] at hF
    set d : ℝ := ‖s - s₀‖
    have hd0 : 0 < d := by
      refine lt_of_lt_of_le ?_ (Complex.abs_re_le_norm (s - s₀))
      have hre : (s - s₀).re = σ - 1 / 2 := by simp [s, s₀]
      rw [hre, abs_of_pos (by linarith)]
      linarith
    have hdT : d ≤ T + 1 := by
      calc d ≤ |(s - s₀).re| + |(s - s₀).im| := Complex.norm_le_abs_re_add_abs_im (s - s₀)
        _ ≤ 1 + T := by
            have hre : (s - s₀).re = σ - 1 / 2 := by simp [s, s₀]
            have him : (s - s₀).im = t - t₀ := by simp [s, s₀]
            rw [hre, him, abs_of_pos (by linarith), abs_le]
            refine add_le_add (by linarith) ⟨by linarith, by linarith⟩
        _ = T + 1 := by ring
    have hC : ‖weightDirichletSeries (oscWeight 1 t₀) s - (P : ℂ)‖ ≤
        B * d ^ (-(1 / 2 : ℝ)) + |P| := by
      rw [weightDirichletSeries_oscWeight]
      refine (norm_sub_le _ _).trans (add_le_add hF (by rw [Complex.norm_real, Real.norm_eq_abs]))
    have hζs : ‖riemannZeta s‖ ≤ L * d := hLip σ t hσ.le hσ'.le ht.le htT
    have hd_mul : d * d ^ (-(1 / 2 : ℝ)) = d ^ (1 / 2 : ℝ) := by
      conv_lhs => rw [← Real.rpow_one d]
      rw [← Real.rpow_add hd0]
      norm_num
    have hd_half : d ^ (1 / 2 : ℝ) ≤ (T + 1) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hd0.le hdT (by norm_num)
    have hprod : ‖riemannZeta s‖ * ‖weightDirichletSeries (oscWeight 1 t₀) s - (P : ℂ)‖ ≤ M₀ := by
      calc ‖riemannZeta s‖ * ‖weightDirichletSeries (oscWeight 1 t₀) s - (P : ℂ)‖
          ≤ (L * d) * (B * d ^ (-(1 / 2 : ℝ)) + |P|) :=
            mul_le_mul hζs hC (norm_nonneg _) (by positivity)
        _ = L * B * (d * d ^ (-(1 / 2 : ℝ))) + L * d * |P| := by ring
        _ = L * B * d ^ (1 / 2 : ℝ) + L * d * |P| := by rw [hd_mul]
        _ ≤ L * B * (T + 1) ^ (1 / 2 : ℝ) + L * (T + 1) * |P| :=
            add_le_add (mul_le_mul_of_nonneg_left hd_half (by positivity))
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdT hL0) (abs_nonneg P))
    have hsn : σ ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s
      simp only [s, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      linarith [le_abs_self σ]
    have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖s‖ ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hden : 0 < ‖s‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
    simp only [lineIntegrand, norm_div, div_pow]
    rw [div_le_iff₀ hden]
    calc ‖riemannZeta s * (weightDirichletSeries (oscWeight 1 t₀) s - (P : ℂ))‖ ^ 2
        = (‖riemannZeta s‖ * ‖weightDirichletSeries (oscWeight 1 t₀) s - (P : ℂ)‖) ^ 2 := by
          rw [norm_mul]
      _ ≤ M₀ ^ 2 := pow_le_pow_left₀ (by positivity) hprod 2
      _ = A * (1 / 2) ^ 2 := by simp only [A]; ring
      _ ≤ A * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_left hs2 hA0
  have hlarge : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < t →
      ‖weightDirichletSeries (oscWeight 1 t₀) ((σ : ℂ) + (t : ℂ) * I) - (P : ℂ)‖ ≤
        (10 * E2 + |P|) * t ^ (1 / 4 : ℝ) := by
    intro σ t hσ hσ' ht
    rw [weightDirichletSeries_oscWeight]
    refine (norm_sub_le _ _).trans ?_
    have h := norm_oscSeries_le_large (a := 1) (by norm_num) (by norm_num) ht₀
      (w := (σ : ℂ) + (t : ℂ) * I + 1 / 2)
      (by rw [hwre]; linarith) (by rw [hwre]; linarith) (by rw [hwim]; exact ht)
    rw [hwim] at h
    have h1 : 1 ≤ t ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg P]
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_majorant hT hg hsmall hlarge
  exact ⟨3 * M / (4 * Real.pi),
    weightPronicEnergy_le_of_lineEnergy_le (dampedClass_oscWeight (by norm_num) t₀) hM⟩

/-- **At `a = 1` and `t₀ ≠ 0`, a zero of `ζ(1/2 + it₀)` pays the receiver.** -/
theorem receiverBounded_oscWeight_one_of_zeta_eq_zero {t₀ : ℝ} (ht₀ : t₀ ≠ 0)
    (hζ0 : riemannZeta (1 / 2 + (t₀ : ℂ) * I) = 0) :
    ReceiverBounded (oscWeight 1 t₀) := by
  rcases lt_or_gt_of_ne ht₀ with hneg | hpos
  · rw [← oscWeight_neg 1 t₀]
    refine receiverBounded_oscWeight_one_pos_of_zeta_eq_zero (by linarith) ?_
    have hconj : (1 / 2 : ℂ) + ((-t₀ : ℝ) : ℂ) * I =
        starRingEnd ℂ ((1 / 2 : ℂ) + (t₀ : ℂ) * I) := by
      simp [Complex.conj_ofReal]
      ring
    rw [hconj, riemannZeta_conj, hζ0, map_zero]
  · exact receiverBounded_oscWeight_one_pos_of_zeta_eq_zero hpos hζ0

/-! ### The endpoint equivalence and the complete phase diagram on `[−1, 1] × ℝ` -/

/-- **The endpoint `a = 1` reads the critical zeros**: for `t₀ ≠ 0`, the half-damped oscillating
weight `oscWeight 1 t₀` has bounded receiver iff `ζ(1/2 + it₀) = 0`. -/
theorem receiverBounded_oscWeight_one_iff {t₀ : ℝ} (ht₀ : t₀ ≠ 0) :
    ReceiverBounded (oscWeight 1 t₀) ↔ riemannZeta (1 / 2 + (t₀ : ℂ) * I) = 0 :=
  ⟨fun h => by_contra fun hne => not_receiverBounded_oscWeight_one_of_zeta_ne_zero ht₀ hne h,
   receiverBounded_oscWeight_one_of_zeta_eq_zero ht₀⟩

/-- **At zero frequency `t₀ = 0`, the threshold is `1/2`**: for `a ∈ [−1, 1]`, `oscWeight a 0`
has bounded receiver iff `a < 1/2`. -/
theorem receiverBounded_oscWeight_zero_iff {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1) :
    ReceiverBounded (oscWeight a 0) ↔ a < 1 / 2 := by
  rw [oscWeight_zero, receiverBounded_constantSign_iff_full ha ha1]

/-- **At every non-zero frequency `t₀ ≠ 0`, the threshold is `1` and the endpoint reads `ζ(1/2 + it₀)`**:
for `a ∈ [−1, 1]` and `t₀ ≠ 0`, `oscWeight a t₀` has bounded receiver iff `a < 1` or
`ζ(1/2 + it₀) = 0`. -/
theorem receiverBounded_oscWeight_of_ne_zero_iff {a t₀ : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1)
    (ht₀ : t₀ ≠ 0) :
    ReceiverBounded (oscWeight a t₀) ↔ a < 1 ∨ riemannZeta (1 / 2 + (t₀ : ℂ) * I) = 0 := by
  rcases lt_or_eq_of_le ha1 with hlt | rfl
  · exact ⟨fun _ => Or.inl hlt, fun _ => receiverBounded_oscWeight_of_lt_one ha hlt ht₀⟩
  · rw [receiverBounded_oscWeight_one_iff ht₀]
    exact ⟨Or.inr, fun h => h.resolve_left (lt_irrefl 1)⟩

/-- **The complete phase diagram of half-damped oscillating prime patterns on `[−1, 1] × ℝ`.**
For `a ∈ [−1, 1]` and `t₀ ∈ ℝ`, the weight `f_{a,t₀}(d) d^{-1/2}` with `f_{a,t₀}(p) = a cos(t₀ log p)`
has bounded receiver if and only if either `t₀ = 0` and `a < 1/2`, or `t₀ ≠ 0` and
(`a < 1` or `ζ(1/2 + it₀) = 0`). -/
theorem receiverBounded_oscWeight_iff {a t₀ : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1) :
    ReceiverBounded (oscWeight a t₀) ↔
      (t₀ = 0 ∧ a < 1 / 2) ∨ (t₀ ≠ 0 ∧ (a < 1 ∨ riemannZeta (1 / 2 + (t₀ : ℂ) * I) = 0)) := by
  rcases eq_or_ne t₀ 0 with rfl | ht₀
  · simp [receiverBounded_oscWeight_zero_iff ha ha1]
  · simp [ht₀, receiverBounded_oscWeight_of_ne_zero_iff ha ha1 ht₀]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.not_receiverBounded_of_sq_norm_dirichletSeries_ge_at_height
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.not_receiverBounded_oscWeight_one_of_zeta_ne_zero
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.receiverBounded_oscWeight_one_of_zeta_eq_zero
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.receiverBounded_oscWeight_one_iff
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.receiverBounded_oscWeight_of_ne_zero_iff
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.receiverBounded_oscWeight_iff
