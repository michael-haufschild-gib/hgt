import GaloisForLFunctions.FiniteFreeProbability.EulerFactorStability

/-!
# The half-log normalization of an Euler factor is sharp

The Euler factor `1 − q e^{−iℓw}` (`0 < q < 1`, `ℓ = log p`), translated by `e^{icw}`, has reversed
Jensen polynomials `R_d = (X + ic)^d − q (X − i(ℓ − c))^d`. For `c = ℓ/2` all roots lie in the open
lower half-plane at every degree (Hermite–Biehler stability). For every `c < ℓ/2` this fails: with
`r = q^{1/d}` and `d` even,

`x* = i (r(ℓ − c) − c)/(1 + r)`

is a root, and `Im x* > 0` as soon as `r > c/(ℓ − c)`, which holds for all large `d` because
`q^{1/d} → 1`. So `ℓ/2` is the least translation making the factor stable uniformly in the degree:
each prime forces the drift `(log p)/2`.
-/

open Polynomial Filter Topology Complex

namespace FiniteFreeProbability

noncomputable section

theorem jensenRev_translatedEulerFactor (d : ℕ) (q c ℓ : ℂ) :
    jensenRev d (expSeries c - PowerSeries.C q * expSeries (c - ℓ)) =
      (X + C c) ^ d - C q * (X + C (c - ℓ)) ^ d := by
  rw [jensenRev_sub, jensenRev_C_mul, expSeries, expSeries, jensenRev_exp, jensenRev_exp]

/-- The explicit upper root at even degree. -/
theorem isRoot_translatedEuler_even {q ℓ c : ℝ} (hq : 0 < q) {d : ℕ} (hd : Even d)
    (hd0 : d ≠ 0) :
    ((X + C (I * c)) ^ d - C (q : ℂ) * (X + C (I * c - I * ℓ)) ^ d).IsRoot
      (I * (((q ^ (1 / (d : ℝ)) * (ℓ - c) - c) / (1 + q ^ (1 / (d : ℝ))) : ℝ) : ℂ)) := by
  set r := q ^ (1 / (d : ℝ))
  have hr : 0 < r := Real.rpow_pos_of_pos hq _
  have hrd : r ^ d = q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, one_div, inv_mul_cancel₀ (by exact_mod_cast hd0),
      Real.rpow_one]
  have h1r : (1 + r : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1 + r) ≠ 0)
  have e1 : I * (((r * (ℓ - c) - c) / (1 + r) : ℝ) : ℂ) + I * c = I * (r * ℓ / (1 + r) : ℝ) := by
    push_cast; field_simp; ring
  have e2 : I * (((r * (ℓ - c) - c) / (1 + r) : ℝ) : ℂ) + (I * c - I * ℓ) =
      -(I * (ℓ / (1 + r) : ℝ)) := by
    push_cast; field_simp; ring
  simp only [IsRoot, eval_sub, eval_pow, eval_add, eval_X, eval_C, eval_mul]
  rw [e1, e2, hd.neg_pow, sub_eq_zero, mul_pow, mul_pow, ← mul_assoc, mul_comm (q : ℂ),
    mul_assoc]
  congr 1
  rw [show (r * ℓ / (1 + r) : ℝ) = r * (ℓ / (1 + r)) by ring, Complex.ofReal_mul, mul_pow,
    ← Complex.ofReal_pow, hrd]

/-- **Sharpness of the half-log normalization.** For `c < ℓ/2`, all large even degrees give the
translated Euler factor a reversed Jensen root in the open upper half-plane. -/
theorem eventually_exists_upper_root_translatedEuler {q ℓ c : ℝ} (hq : 0 < q) (hℓ : 0 < ℓ)
    (hc : c < ℓ / 2) :
    ∀ᶠ d : ℕ in atTop, Even d →
      ∃ x : ℂ, (jensenRev d (expSeries (I * c) - PowerSeries.C (q : ℂ) *
        expSeries (I * c - I * ℓ))).IsRoot x ∧ 0 < x.im := by
  have hlim : Tendsto (fun d : ℕ => q ^ (1 / (d : ℝ))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun d : ℕ => (1 : ℝ) / (d : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h := (Real.continuous_exp.tendsto _).comp (h0.const_mul (Real.log q))
    rw [mul_zero, Real.exp_zero] at h
    refine h.congr fun d => ?_
    simp [Real.rpow_def_of_pos hq]
  have hthr : c / (ℓ - c) < 1 := by rw [div_lt_one (by linarith)]; linarith
  filter_upwards [hlim.eventually (lt_mem_nhds hthr), eventually_gt_atTop 0] with d hd hd0 heven
  have hroot := isRoot_translatedEuler_even (ℓ := ℓ) (c := c) hq heven hd0.ne'
  refine ⟨I * (((q ^ (1 / (d : ℝ)) * (ℓ - c) - c) / (1 + q ^ (1 / (d : ℝ))) : ℝ) : ℂ), ?_, ?_⟩
  · rw [jensenRev_translatedEulerFactor]; exact hroot
  simp only [mul_im, I_re, I_im, one_mul, zero_add, ofReal_re, ofReal_im, mul_zero]
  have hr : 0 < q ^ (1 / (d : ℝ)) := Real.rpow_pos_of_pos hq _
  apply div_pos _ (by positivity)
  rw [div_lt_iff₀ (by linarith)] at hd
  linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eventually_exists_upper_root_translatedEuler
