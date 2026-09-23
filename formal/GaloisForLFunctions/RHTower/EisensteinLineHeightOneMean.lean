import GaloisForLFunctions.RHTower.EisensteinLineRealness
import GaloisForLFunctions.RHTower.XiLogDerivLineOneWindowLower

/-!
# The Maass–Selberg norm at height one and `Re (ξ'/ξ)`

At `Y = 1` the Maass–Selberg value of the truncated Eisenstein series on the line reads

  `Re msLineValue(t, 1) = Im(Λ(1+2it)²)/t + 4‖Λ(1+2it)‖²·(Re (ξ'/ξ)(1+2it) − 1/(1+4t²))`,

since `Λ(2it) = conj Λ(1+2it)`, `Λ'(1−2it) = conj Λ'(1+2it)`, and
`Λ'/Λ = ξ'/ξ − 1/s − 1/(s−1)`.  With `Re (ξ'/ξ)(1+2it) ≥ 1` for all large `t`
(`exists_re_logDeriv_xi_lineOne_ge`) this gives `Re msLineValue(t, 1) ≥ 3‖Λ(1+2it)‖²`.
-/

open Complex

namespace RHTower

noncomputable section

/-- `ξ'/ξ = 1/s + 1/(s−1) + Λ'/Λ` wherever `ξ s ≠ 0`, `s ≠ 0`, `s ≠ 1`. -/
theorem logDeriv_xi_eq_of_ne {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hxi : xi s ≠ 0) :
    logDeriv xi s = s⁻¹ + (s - 1)⁻¹ + logDeriv completedRiemannZeta s := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hopen : IsOpen {w : ℂ | w ≠ 0 ∧ w ≠ 1} := isOpen_ne.inter isOpen_ne
  have hev : xi =ᶠ[nhds s] fun w : ℂ => w * (w - 1) / 2 * completedRiemannZeta w :=
    Filter.eventually_of_mem (hopen.mem_nhds ⟨hs0, hs1⟩) fun w hw =>
      xi_eq_mul_completedRiemannZeta hw.1 hw.2
  rw [logDeriv_congr_of_eventuallyEq hev]
  have hpoly_ne : s * (s - 1) / 2 ≠ 0 := by
    apply div_ne_zero (mul_ne_zero hs0 hs1')
    norm_num
  have hLam_ne : completedRiemannZeta s ≠ 0 := by
    intro h
    apply hxi
    rw [xi_eq_mul_completedRiemannZeta hs0 hs1, h, mul_zero]
  have hpoly_diff : DifferentiableAt ℂ (fun w : ℂ => w * (w - 1) / 2) s :=
    (differentiableAt_id.mul (differentiableAt_id.sub_const 1)).div_const 2
  have hLam_diff : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs0 hs1
  rw [logDeriv_mul s hpoly_ne hLam_ne hpoly_diff hLam_diff]
  have hderiv : HasDerivAt (fun w : ℂ => w * (w - 1) / 2) ((1 * (s - 1) + s * 1) / 2) s :=
    ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2
  have hld : logDeriv (fun w : ℂ => w * (w - 1) / 2) s = s⁻¹ + (s - 1)⁻¹ := by
    rw [logDeriv_apply, hderiv.deriv]
    field_simp
  rw [hld]

/-- The Maass–Selberg value at height one: `(A² − Ā²)/(2it) + 2A·conj A' + 2Ā·A'` with
`A = Λ(1+2it)` and `A' = Λ'(1+2it)`. -/
theorem msLineValue_one {t : ℝ} (ht : 0 < t) :
    msLineValue t 1 =
      ((eisLineLambda t) ^ (2 : ℕ) - ((starRingEnd ℂ) (eisLineLambda t)) ^ (2 : ℕ)) / (2 * ((t : ℂ) * I)) +
        2 * eisLineLambda t *
          (starRingEnd ℂ) (deriv reflectedCompletedLambda (1 + 2 * ((t : ℂ) * I))) +
        2 * (starRingEnd ℂ) (eisLineLambda t) *
          deriv reflectedCompletedLambda (1 + 2 * ((t : ℂ) * I)) := by
  have hB : msB ((t : ℂ) * I) = (starRingEnd ℂ) (eisLineLambda t) :=
    reflectedCompletedLambda_two_mul_I_eq_conj ht.ne'
  have hA : msA ((t : ℂ) * I) = eisLineLambda t := rfl
  have hd1 : deriv reflectedCompletedLambda (1 - 2 * ((t : ℂ) * I)) =
      (starRingEnd ℂ) (deriv reflectedCompletedLambda (1 + 2 * ((t : ℂ) * I))) := by
    rw [← deriv_reflectedCompletedLambda_conj (by simp [ht.ne'])]
    congr 1
    rw [map_add, map_one, map_mul, map_ofNat, conj_I_mul]
    ring
  unfold msLineValue
  rw [hA, hB, hd1, Complex.ofReal_one, Complex.one_cpow, Complex.one_cpow, Complex.log_one]
  ring

/-- The Maass–Selberg value at height one is the real number
`Im(A²)/t + 4·Re(Ā·A')`. -/
theorem msLineValue_one_eq_ofReal {t : ℝ} (ht : 0 < t) :
    msLineValue t 1 = ((((eisLineLambda t) ^ (2 : ℕ)).im / t +
      4 * ((starRingEnd ℂ) (eisLineLambda t) *
        deriv reflectedCompletedLambda (1 + 2 * ((t : ℂ) * I))).re : ℝ) : ℂ) := by
  rw [msLineValue_one ht]
  set A := eisLineLambda t with hAdef
  set A' := deriv reflectedCompletedLambda (1 + 2 * ((t : ℂ) * I)) with hA'def
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have e1 : A ^ (2 : ℕ) - (starRingEnd ℂ) A ^ (2 : ℕ) = ((2 * (A ^ (2 : ℕ)).im : ℝ) : ℂ) * I := by
    rw [← map_pow, Complex.sub_conj]
  have e2 : 2 * A * (starRingEnd ℂ) A' + 2 * (starRingEnd ℂ) A * A' =
      ((2 * (2 * ((starRingEnd ℂ) A * A').re) : ℝ) : ℂ) := by
    have h : 2 * A * (starRingEnd ℂ) A' + 2 * (starRingEnd ℂ) A * A' =
        2 * ((starRingEnd ℂ) A * A' + (starRingEnd ℂ) ((starRingEnd ℂ) A * A')) := by
      rw [map_mul, Complex.conj_conj]
      ring
    rw [h, Complex.add_conj]
    push_cast
    ring
  calc (A ^ (2 : ℕ) - (starRingEnd ℂ) A ^ (2 : ℕ)) / (2 * ((t : ℂ) * I)) + 2 * A * (starRingEnd ℂ) A' +
        2 * (starRingEnd ℂ) A * A'
      = (A ^ (2 : ℕ) - (starRingEnd ℂ) A ^ (2 : ℕ)) / (2 * ((t : ℂ) * I)) +
        (2 * A * (starRingEnd ℂ) A' + 2 * (starRingEnd ℂ) A * A') := by ring
    _ = _ := by
      rw [e1, e2]
      push_cast
      field_simp
      ring

theorem msLineValue_one_re {t : ℝ} (ht : 0 < t) :
    (msLineValue t 1).re = ((eisLineLambda t) ^ (2 : ℕ)).im / t +
      4 * ((starRingEnd ℂ) (eisLineLambda t) *
        deriv reflectedCompletedLambda (1 + 2 * ((t : ℂ) * I))).re := by
  rw [msLineValue_one_eq_ofReal ht, Complex.ofReal_re]

/-- `Re(Ā·A') = ‖A‖²·(Re (ξ'/ξ)(1+2it) − 1/(1+4t²))` for `A = Λ(1+2it)`, `A' = Λ'(1+2it)`. -/
theorem conj_eisLineLambda_mul_deriv_re {t : ℝ} (ht : 0 < t) :
    ((starRingEnd ℂ) (eisLineLambda t) *
        deriv reflectedCompletedLambda (1 + 2 * ((t : ℂ) * I))).re =
      ‖eisLineLambda t‖ ^ (2 : ℕ) *
        ((logDeriv xi (1 + 2 * ((t : ℂ) * I))).re - 1 / (1 + 4 * t ^ (2 : ℕ))) := by
  set s : ℂ := 1 + 2 * ((t : ℂ) * I) with hsdef
  have hsim : s.im ≠ 0 := by simp [hsdef, ht.ne']
  have hsre : s.re = 1 := by simp [hsdef]
  have hs0 : s ≠ 0 := by
    intro h
    apply hsim
    rw [h, Complex.zero_im]
  have hs1 : s ≠ 1 := by
    intro h
    apply hsim
    rw [h, Complex.one_im]
  have hxi : xi s ≠ 0 := xi_ne_zero_of_one_le_re (by rw [hsre])
  have hA : eisLineLambda t = reflectedCompletedLambda s := rfl
  have hG : s.Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_im_ne_zero hsim
  have hAne : reflectedCompletedLambda s ≠ 0 := by
    rw [reflectedCompletedLambda_eq_completed hs0 hG]
    intro h
    apply hxi
    rw [xi_eq_mul_completedRiemannZeta hs0 hs1, h, mul_zero]
  have hderiv : deriv reflectedCompletedLambda s = deriv completedRiemannZeta s :=
    (reflectedCompletedLambda_eventuallyEq_completed hsim).deriv_eq
  have hlog : logDeriv completedRiemannZeta s =
      deriv reflectedCompletedLambda s / reflectedCompletedLambda s := by
    rw [logDeriv_apply, hderiv, reflectedCompletedLambda_eq_completed hs0 hG]
  have hprod : (starRingEnd ℂ) (reflectedCompletedLambda s) * deriv reflectedCompletedLambda s =
      ((Complex.normSq (reflectedCompletedLambda s) : ℝ) : ℂ) *
        (deriv reflectedCompletedLambda s / reflectedCompletedLambda s) := by
    rw [Complex.normSq_eq_conj_mul_self]
    field_simp
  have hlogdiv : deriv reflectedCompletedLambda s / reflectedCompletedLambda s =
      logDeriv xi s - s⁻¹ - (s - 1)⁻¹ := by
    rw [logDeriv_xi_eq_of_ne hs0 hs1 hxi, ← hlog]
    ring
  rw [hA, hprod, hlogdiv, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
  congr 1
  rw [Complex.sub_re, Complex.sub_re, Complex.inv_re, Complex.inv_re]
  have hns : Complex.normSq s = 1 + 4 * t ^ (2 : ℕ) := by
    rw [Complex.normSq_apply]
    simp [hsdef]
    ring
  have hns1 : Complex.normSq (s - 1) = 4 * t ^ (2 : ℕ) := by
    rw [Complex.normSq_apply]
    simp [hsdef]
    ring
  have hre1 : (s - 1).re = 0 := by simp [hsdef]
  rw [hns, hns1, hsre, hre1, zero_div]
  ring

/-- `Re msLineValue(t,1) ≥ ‖Λ(1+2it)‖²·(4 Re (ξ'/ξ)(1+2it) − 4/(1+4t²) − 1/t)`. -/
theorem msLineValue_one_re_ge {t : ℝ} (ht : 0 < t) :
    ‖eisLineLambda t‖ ^ (2 : ℕ) *
        (4 * (logDeriv xi (1 + 2 * ((t : ℂ) * I))).re - 4 / (1 + 4 * t ^ (2 : ℕ)) - 1 / t) ≤
      (msLineValue t 1).re := by
  rw [msLineValue_one_re ht, conj_eisLineLambda_mul_deriv_re ht]
  have him : -(‖eisLineLambda t‖ ^ (2 : ℕ)) ≤ ((eisLineLambda t) ^ (2 : ℕ)).im := by
    have h1 := Complex.abs_im_le_norm ((eisLineLambda t) ^ (2 : ℕ))
    rw [Complex.norm_pow] at h1
    have := neg_abs_le ((eisLineLambda t) ^ (2 : ℕ)).im
    linarith
  have hdiv : -(‖eisLineLambda t‖ ^ (2 : ℕ)) / t ≤ ((eisLineLambda t) ^ (2 : ℕ)).im / t :=
    div_le_div_of_nonneg_right him ht.le
  have e : ‖eisLineLambda t‖ ^ (2 : ℕ) *
      (4 * (logDeriv xi (1 + 2 * ((t : ℂ) * I))).re - 4 / (1 + 4 * t ^ (2 : ℕ)) - 1 / t) =
      -(‖eisLineLambda t‖ ^ (2 : ℕ)) / t + 4 * (‖eisLineLambda t‖ ^ (2 : ℕ) *
        ((logDeriv xi (1 + 2 * ((t : ℂ) * I))).re - 1 / (1 + 4 * t ^ (2 : ℕ)))) := by
    field_simp
    ring
  rw [e]
  linarith

/-- **`Re msLineValue(t,1) ≥ 3‖Λ(1+2it)‖²` for all large `t`.**  The bounded-window zero count
gives `Re (ξ'/ξ)(1+2it) ≥ 1` eventually, and the two correction terms are at most `1/4 + 1/16`. -/
theorem exists_msLineValue_one_re_ge :
    ∃ t₀ : ℝ, 16 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      3 * ‖eisLineLambda t‖ ^ (2 : ℕ) ≤ (msLineValue t 1).re := by
  obtain ⟨t₀, ht₀, h⟩ := exists_re_logDeriv_xi_lineOne_ge 1
  refine ⟨t₀, ht₀, fun t ht => ?_⟩
  have ht16 : (16 : ℝ) ≤ t := ht₀.trans ht
  have ht0 : 0 < t := by linarith
  have hre : 1 ≤ (logDeriv xi (1 + 2 * ((t : ℂ) * I))).re := by
    have := h t ht
    have e : (1 : ℂ) + 2 * ((t : ℂ) * I) = 1 + 2 * t * I := by ring
    rw [e]
    exact this
  refine le_trans ?_ (msLineValue_one_re_ge ht0)
  have hL : 0 ≤ ‖eisLineLambda t‖ ^ (2 : ℕ) := by positivity
  have h1 : 4 / (1 + 4 * t ^ (2 : ℕ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : 1 / t ≤ 1 / 16 := by
    rw [div_le_div_iff₀ ht0 (by norm_num)]
    linarith
  have h3 : 3 ≤ 4 * (logDeriv xi (1 + 2 * ((t : ℂ) * I))).re - 4 / (1 + 4 * t ^ (2 : ℕ)) - 1 / t := by
    linarith
  have := mul_le_mul_of_nonneg_left h3 hL
  linarith

/-- **The height-one truncated norm on the line is the scattering time delay.**  With
`s = 1 + 2it` and the reflection-paired Lorentzian terms
`(1 − β)/|s − ρ|² + β/|s − (1 − ρ)|²` over the zero copies,
`∫_𝒟 ‖Λ¹E*(·, ½+it)‖² = Im(Λ(s)²)/t + ‖Λ(s)‖²·(2·Σ_ρ Lorentzian − 4/(1+4t²))`. -/
theorem integral_norm_sq_height_one_eq_time_delay {t : ℝ} (ht : 0 < t) :
    ∫ z in ModularGroup.fd, ‖truncatedLineModel ((t : ℂ) * I) 1 z‖ ^ (2 : ℕ) =
      ((eisLineLambda t) ^ (2 : ℕ)).im / t + ‖eisLineLambda t‖ ^ (2 : ℕ) *
        (2 * ∑' q : XiZeroCopy, xiPairedResolventTerm (1 + 2 * ((t : ℂ) * I)) q -
          4 / (1 + 4 * t ^ (2 : ℕ))) := by
  rw [integral_norm_sq_truncatedLineModel_line ht le_rfl, msLineValue_one_re ht,
    conj_eisLineLambda_mul_deriv_re ht]
  have hs : xi (1 + 2 * ((t : ℂ) * I)) ≠ 0 := xi_ne_zero_of_one_le_re (by simp)
  rw [← two_mul_re_logDeriv_xi_eq_tsum_paired hs]
  ring

end

end RHTower
