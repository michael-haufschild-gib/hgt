import GaloisForLFunctions.RHTower.DQPTEtaDeriv
import GaloisForLFunctions.RHTower.DQPTPartialSumRate

/-!
# DQPT: the explicit bound on `ζ′(s)` in the critical strip

**Supplementary Note 6 (6.7)–(6.8)** of arXiv:2511.11199 (published Supplementary Note 8).
From `ζ(s) = η(s)/(1 − 2^{1−s})` one gets

`ζ′(s) = (η′(s)(1 − 2^{1−s}) − 2^{1−s} ln 2 · η(s)) / (1 − 2^{1−s})²`,

and hence, with `|η(s)| ≤ |s|/β` and `|η′(s)| ≤ |s|/β² + 1/β`,

`|ζ′(s)| ≤ (|s|/β² + 1/β)/(2^{1−β} − 1) + 2^{1−β} ln2 (|s|/β)/(2^{1−β} − 1)²`.

Together with `2^{1−β} − 1 ≥ ln 2·(1 − β)` this is the paper's
`Poly(|t|, |1−β|^{-1}, β^{-1})` conclusion, here in fully explicit form.

The displayed first denominator in the source, `|2^{1−β} − 1|·β`, should be
`|2^{1−β} − 1|·β²`; the corrected inequality is what is proved here.

Main results:
* `dqpt_log_two_mul_le_two_rpow_sub_one` — `ln2·(1−β) ≤ 2^{1−β} − 1`;
* `dqpt_zeta_deriv_identity` — `(1 − 2^{1−s})²·ζ′(s) = η′(s)(1 − 2^{1−s}) − 2^{1−s} ln2·η(s)`;
* `dqpt_norm_deriv_riemannZeta_le` — **Supplementary Note 6 (6.8)**;
* `dqpt_norm_deriv_riemannZeta_le_poly` — the explicit `Poly` form.
-/

namespace RHTower.DQPT

open Complex Filter Topology Set

noncomputable section

/-! ## The eta multiplier -/

theorem dqpt_norm_two_cpow (s : ℂ) : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
  have hb : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  rw [← hb, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), Complex.sub_re,
    Complex.one_re]

/-- `ln 2·(1 − β) ≤ 2^{1−β} − 1`: the tangent-line bound for the convex function `2^x`. -/
theorem dqpt_log_two_mul_le_two_rpow_sub_one (β : ℝ) :
    Real.log 2 * (1 - β) ≤ (2 : ℝ) ^ (1 - β) - 1 := by
  have hexp : (1 - β) * Real.log 2 + 1 ≤ Real.exp ((1 - β) * Real.log 2) := by
    simpa [add_comm] using Real.add_one_le_exp ((1 - β) * Real.log 2)
  have hrpow : (2 : ℝ) ^ (1 - β) = Real.exp ((1 - β) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  rw [hrpow]
  nlinarith [hexp]

theorem dqpt_two_rpow_sub_one_pos {β : ℝ} (hβ : β < 1) : 0 < (2 : ℝ) ^ (1 - β) - 1 := by
  have h : (1 : ℝ) < (2 : ℝ) ^ (1 - β) :=
    Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, by linarith⟩)
  linarith

/-- `2^{1−β} − 1 ≤ ‖1 − 2^{1−s}‖`: reverse triangle inequality. -/
theorem dqpt_two_rpow_sub_one_le_norm {s : ℂ} (hs1 : s.re < 1) :
    (2 : ℝ) ^ (1 - s.re) - 1 ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ := by
  have h := abs_norm_sub_norm_le (1 : ℂ) ((2 : ℂ) ^ (1 - s))
  rw [norm_one, dqpt_norm_two_cpow s] at h
  have hpos := dqpt_two_rpow_sub_one_pos hs1
  have habs : |(1 : ℝ) - (2 : ℝ) ^ (1 - s.re)| = (2 : ℝ) ^ (1 - s.re) - 1 := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [habs] at h
  exact h

/-! ## The eta/zeta derivative identity -/

theorem hasDerivAt_etaFactor (s : ℂ) :
    HasDerivAt (fun w : ℂ => 1 - (2 : ℂ) ^ (1 - w))
      ((2 : ℂ) ^ (1 - s) * ((Real.log 2 : ℝ) : ℂ)) s := by
  have haux : HasDerivAt (fun w : ℂ => 1 + -w) (-1 : ℂ) s := (hasDerivAt_neg s).const_add (1 : ℂ)
  have hone : HasDerivAt (fun w : ℂ => 1 - w) (-1 : ℂ) s := by
    refine haux.congr_of_eventuallyEq ?_
    filter_upwards with w
    ring
  have hcp := hone.const_cpow (c := (2 : ℂ)) (Or.inl (by norm_num))
  have hres := HasDerivAt.const_sub (1 : ℂ) hcp
  refine hres.congr_deriv ?_
  have hlog2 : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    have hb : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
    rw [← hb, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hlog2]
  ring

/-- **The `η′`/`ζ′` relation.**  `η′(s) = 2^{1−s} ln2·ζ(s) + (1 − 2^{1−s})·ζ′(s)`. -/
theorem dqpt_etaDeriv_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ∑' n : ℕ, dqptEtaTermDeriv s n
      = (2 : ℂ) ^ (1 - s) * ((Real.log 2 : ℝ) : ℂ) * riemannZeta s
        + (1 - (2 : ℂ) ^ (1 - s)) * deriv riemannZeta s := by
  have hU : IsOpen ({w : ℂ | 0 < w.re} \ {(1 : ℂ)}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hsU : s ∈ ({w : ℂ | 0 < w.re} \ {(1 : ℂ)}) := ⟨hs, by simpa using hs1⟩
  have heq : etaPair =ᶠ[nhds s] fun w : ℂ => (1 - (2 : ℂ) ^ (1 - w)) * riemannZeta w := by
    refine Filter.eventuallyEq_of_mem (hU.mem_nhds hsU) ?_
    intro w hw
    exact etaPair_eq w hw.1 (by simpa using hw.2)
  have hz : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have hprod := (hasDerivAt_etaFactor s).mul hz
  have heta := hasDerivAt_etaPair hs
  have heta' : HasDerivAt (fun w : ℂ => (1 - (2 : ℂ) ^ (1 - w)) * riemannZeta w)
      (∑' n : ℕ, dqptEtaTermDeriv s n) s := heta.congr_of_eventuallyEq heq.symm
  exact heta'.unique hprod

/-- **Supplementary Note 6 (6.7).**  `(1 − 2^{1−s})²·ζ′(s) = η′(s)(1 − 2^{1−s}) − 2^{1−s} ln2·η(s)`. -/
theorem dqpt_zeta_deriv_identity {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (1 - (2 : ℂ) ^ (1 - s)) ^ 2 * deriv riemannZeta s
      = (∑' n : ℕ, dqptEtaTermDeriv s n) * (1 - (2 : ℂ) ^ (1 - s))
        - (2 : ℂ) ^ (1 - s) * ((Real.log 2 : ℝ) : ℂ) * etaPair s := by
  have hrel := dqpt_etaDeriv_eq hs hs1
  have hpair := etaPair_eq s hs hs1
  rw [hpair]
  linear_combination ((2 : ℂ) ^ (1 - s) - 1) * hrel

/-! ## Supplementary Note 6 (6.8) -/

/-- **The explicit `ζ′` bound in the open critical strip.** -/
theorem dqpt_norm_deriv_riemannZeta_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ‖deriv riemannZeta s‖
      ≤ (‖s‖ / s.re ^ 2 + 1 / s.re) / ((2 : ℝ) ^ (1 - s.re) - 1)
        + (2 : ℝ) ^ (1 - s.re) * Real.log 2 * (‖s‖ / s.re)
            / ((2 : ℝ) ^ (1 - s.re) - 1) ^ 2 := by
  have hsne : s ≠ 1 := fun h => by rw [h] at hs1; simp at hs1
  have hd : 0 < (2 : ℝ) ^ (1 - s.re) - 1 := dqpt_two_rpow_sub_one_pos hs1
  have hDle : (2 : ℝ) ^ (1 - s.re) - 1 ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ :=
    dqpt_two_rpow_sub_one_le_norm hs1
  have hDpos : 0 < ‖1 - (2 : ℂ) ^ (1 - s)‖ := lt_of_lt_of_le hd hDle
  have hid := dqpt_zeta_deriv_identity hs0 hsne
  have hnormid : ‖1 - (2 : ℂ) ^ (1 - s)‖ ^ 2 * ‖deriv riemannZeta s‖
      ≤ ‖∑' n : ℕ, dqptEtaTermDeriv s n‖ * ‖1 - (2 : ℂ) ^ (1 - s)‖
        + (2 : ℝ) ^ (1 - s.re) * Real.log 2 * ‖etaPair s‖ := by
    have hlhs : ‖1 - (2 : ℂ) ^ (1 - s)‖ ^ 2 * ‖deriv riemannZeta s‖
        = ‖(1 - (2 : ℂ) ^ (1 - s)) ^ 2 * deriv riemannZeta s‖ := by
      rw [norm_mul, norm_pow]
    rw [hlhs, hid]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖(∑' n : ℕ, dqptEtaTermDeriv s n) * (1 - (2 : ℂ) ^ (1 - s))‖
        = ‖∑' n : ℕ, dqptEtaTermDeriv s n‖ * ‖1 - (2 : ℂ) ^ (1 - s)‖ := norm_mul _ _
    have h2 : ‖(2 : ℂ) ^ (1 - s) * ((Real.log 2 : ℝ) : ℂ) * etaPair s‖
        = (2 : ℝ) ^ (1 - s.re) * Real.log 2 * ‖etaPair s‖ := by
      rw [norm_mul, norm_mul, dqpt_norm_two_cpow s, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (Real.log_pos (by norm_num)))]
    rw [h1, h2]
  have hE : ‖∑' n : ℕ, dqptEtaTermDeriv s n‖ ≤ ‖s‖ / s.re ^ 2 + 1 / s.re :=
    dqpt_norm_etaPairDeriv_le hs0
  have hEta : ‖etaPair s‖ ≤ ‖s‖ / s.re := dqpt_norm_etaPair_le hs0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ (1 - s.re) := Real.rpow_pos_of_pos (by norm_num) _
  -- first term
  have hterm1 : ‖∑' n : ℕ, dqptEtaTermDeriv s n‖ * ‖1 - (2 : ℂ) ^ (1 - s)‖
      ≤ (‖s‖ / s.re ^ 2 + 1 / s.re) * ‖1 - (2 : ℂ) ^ (1 - s)‖ :=
    mul_le_mul_of_nonneg_right hE (le_of_lt hDpos)
  have hterm2 : (2 : ℝ) ^ (1 - s.re) * Real.log 2 * ‖etaPair s‖
      ≤ (2 : ℝ) ^ (1 - s.re) * Real.log 2 * (‖s‖ / s.re) :=
    mul_le_mul_of_nonneg_left hEta (by positivity)
  have hmain : ‖1 - (2 : ℂ) ^ (1 - s)‖ ^ 2 * ‖deriv riemannZeta s‖
      ≤ (‖s‖ / s.re ^ 2 + 1 / s.re) * ‖1 - (2 : ℂ) ^ (1 - s)‖
        + (2 : ℝ) ^ (1 - s.re) * Real.log 2 * (‖s‖ / s.re) := by linarith
  have hdiv : ‖deriv riemannZeta s‖
      ≤ (‖s‖ / s.re ^ 2 + 1 / s.re) / ‖1 - (2 : ℂ) ^ (1 - s)‖
        + (2 : ℝ) ^ (1 - s.re) * Real.log 2 * (‖s‖ / s.re) / ‖1 - (2 : ℂ) ^ (1 - s)‖ ^ 2 := by
    rw [div_add_div _ _ (ne_of_gt hDpos) (by positivity), le_div_iff₀ (by positivity)]
    have hexpand : ((‖s‖ / s.re ^ 2 + 1 / s.re) * ‖1 - (2 : ℂ) ^ (1 - s)‖ ^ 2
        + ‖1 - (2 : ℂ) ^ (1 - s)‖ * ((2 : ℝ) ^ (1 - s.re) * Real.log 2 * (‖s‖ / s.re)))
        = ‖1 - (2 : ℂ) ^ (1 - s)‖
          * ((‖s‖ / s.re ^ 2 + 1 / s.re) * ‖1 - (2 : ℂ) ^ (1 - s)‖
            + (2 : ℝ) ^ (1 - s.re) * Real.log 2 * (‖s‖ / s.re)) := by ring
    rw [hexpand]
    have hsq : ‖deriv riemannZeta s‖ * (‖1 - (2 : ℂ) ^ (1 - s)‖ * ‖1 - (2 : ℂ) ^ (1 - s)‖ ^ 2)
        = ‖1 - (2 : ℂ) ^ (1 - s)‖
          * (‖1 - (2 : ℂ) ^ (1 - s)‖ ^ 2 * ‖deriv riemannZeta s‖) := by ring
    rw [hsq]
    exact mul_le_mul_of_nonneg_left hmain (le_of_lt hDpos)
  refine hdiv.trans ?_
  have hn1 : (‖s‖ / s.re ^ 2 + 1 / s.re) / ‖1 - (2 : ℂ) ^ (1 - s)‖
      ≤ (‖s‖ / s.re ^ 2 + 1 / s.re) / ((2 : ℝ) ^ (1 - s.re) - 1) := by
    refine div_le_div_of_nonneg_left ?_ hd hDle
    positivity
  have hn2 : (2 : ℝ) ^ (1 - s.re) * Real.log 2 * (‖s‖ / s.re) / ‖1 - (2 : ℂ) ^ (1 - s)‖ ^ 2
      ≤ (2 : ℝ) ^ (1 - s.re) * Real.log 2 * (‖s‖ / s.re)
          / ((2 : ℝ) ^ (1 - s.re) - 1) ^ 2 := by
    refine div_le_div_of_nonneg_left ?_ (by positivity) ?_
    · positivity
    · exact pow_le_pow_left₀ (le_of_lt hd) hDle 2
  linarith

/-- **The `Poly(|t|, |1−β|^{-1}, β^{-1})` form.**  Using `2^{1−β} − 1 ≥ ln2·(1−β)` and
`2^{1−β} ≤ 2` on the open strip. -/
theorem dqpt_norm_deriv_riemannZeta_le_poly {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ‖deriv riemannZeta s‖
      ≤ (‖s‖ / s.re ^ 2 + 1 / s.re) / (Real.log 2 * (1 - s.re))
        + 2 * Real.log 2 * (‖s‖ / s.re) / (Real.log 2 * (1 - s.re)) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow : 0 < Real.log 2 * (1 - s.re) := by
    have : (0 : ℝ) < 1 - s.re := by linarith
    positivity
  have hge : Real.log 2 * (1 - s.re) ≤ (2 : ℝ) ^ (1 - s.re) - 1 :=
    dqpt_log_two_mul_le_two_rpow_sub_one s.re
  have hd : 0 < (2 : ℝ) ^ (1 - s.re) - 1 := dqpt_two_rpow_sub_one_pos hs1
  have hpow2le : (2 : ℝ) ^ (1 - s.re) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (1 : ℝ) - s.re ≤ 1 by linarith)
    simpa using h
  refine (dqpt_norm_deriv_riemannZeta_le hs0 hs1).trans ?_
  have h1 : (‖s‖ / s.re ^ 2 + 1 / s.re) / ((2 : ℝ) ^ (1 - s.re) - 1)
      ≤ (‖s‖ / s.re ^ 2 + 1 / s.re) / (Real.log 2 * (1 - s.re)) := by
    refine div_le_div_of_nonneg_left ?_ hlow hge
    positivity
  have h2 : (2 : ℝ) ^ (1 - s.re) * Real.log 2 * (‖s‖ / s.re)
        / ((2 : ℝ) ^ (1 - s.re) - 1) ^ 2
      ≤ 2 * Real.log 2 * (‖s‖ / s.re) / (Real.log 2 * (1 - s.re)) ^ 2 := by
    have hnum : (2 : ℝ) ^ (1 - s.re) * Real.log 2 * (‖s‖ / s.re)
        ≤ 2 * Real.log 2 * (‖s‖ / s.re) := by
      have hnn : (0 : ℝ) ≤ Real.log 2 * (‖s‖ / s.re) := by positivity
      nlinarith [hpow2le, hnn]
    have hden : (Real.log 2 * (1 - s.re)) ^ 2 ≤ ((2 : ℝ) ^ (1 - s.re) - 1) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hlow) hge 2
    have hstep1 : (2 : ℝ) ^ (1 - s.re) * Real.log 2 * (‖s‖ / s.re)
          / ((2 : ℝ) ^ (1 - s.re) - 1) ^ 2
        ≤ 2 * Real.log 2 * (‖s‖ / s.re) / ((2 : ℝ) ^ (1 - s.re) - 1) ^ 2 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    have hstep2 : 2 * Real.log 2 * (‖s‖ / s.re) / ((2 : ℝ) ^ (1 - s.re) - 1) ^ 2
        ≤ 2 * Real.log 2 * (‖s‖ / s.re) / (Real.log 2 * (1 - s.re)) ^ 2 := by
      refine div_le_div_of_nonneg_left ?_ (by positivity) hden
      positivity
    linarith
  linarith

end

end RHTower.DQPT
