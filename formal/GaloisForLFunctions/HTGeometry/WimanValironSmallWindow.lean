import GaloisForLFunctions.HTGeometry.WimanValironPolynomialBound

/-!
# Wiman--Valiron at a narrow logarithmic window

The corpus's packaged forms of the Wiman--Valiron estimate tie the sampling height to `8 ≤ H`, which
confines them to functions whose central index barely moves across a logarithmic window of width
eight — that is, to order zero.  The estimate itself does not need that: in
`exists_radius_point_wiman_valiron_bound` the height is free.

Taking the height inversely proportional to the sampling scale,

```text
K = 3 log s,   H = 2K/s,   L = 2s/H = s²/K,   h = H/2 = K/s,   N = ⌈2s⌉,
```

makes the tail rate `N/(4L)` satisfy `(N/(4L))(N+1) ≥ K`, so both geometric tails are below one, and
the mean-minus-mode factor `2Lh` collapses to `2s`.  What is left is

```text
‖ z f'(z)/f(z) − ν(r) ‖ ≤ 30 s^{3/2} · (1 + log(ν + 4s)/log s),
```

a bound in the sampling scale alone.  Since the spread `s` is a free target — it is what the
selection lemma is asked to achieve, not the actual rise of `ν` — this is the form that a Borel
selection can drive below `ε·ν(r)`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The two tail ratios are at most one once the sampling scale is large. -/
theorem wv_tail_ratios_le_one {N : ℕ} {L s K : ℝ} (hs : (100 : ℝ) ≤ s)
    (hK : K = 3 * Real.log s) (hL : L = s ^ 2 / K)
    (hN2 : 2 * s ≤ (N : ℝ)) (hN4 : (N : ℝ) ≤ 4 * s) :
    0 < 1 - Real.exp (-((N : ℝ) / (4 * L)))
      ∧ Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1) / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ≤ 1
      ∧ Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
          / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3 ≤ 1 := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hlog : Real.log 100 ≤ Real.log s := Real.log_le_log (by norm_num) hs
  have hlog100 : (4 : ℝ) ≤ Real.log 100 := by
    have h := Real.add_one_le_exp (4 : ℝ)
    have he : Real.exp 4 ≤ 100 := by
      have h2 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      calc Real.exp 4 = (Real.exp 1) ^ 4 := by
            rw [← Real.exp_nat_mul]; norm_num
        _ ≤ (2.7182818286 : ℝ) ^ 4 := by
            refine pow_le_pow_left₀ (Real.exp_pos 1).le h2 4
        _ ≤ 100 := by norm_num
    have := Real.log_le_log (Real.exp_pos 4) he
    rwa [Real.log_exp] at this
  have hK4 : (12 : ℝ) ≤ K := by rw [hK]; linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have hL0 : (0 : ℝ) < L := by rw [hL]; positivity
  set x : ℝ := (N : ℝ) / (4 * L) with hx
  have hxval : x = (N : ℝ) * K / (4 * s ^ 2) := by
    rw [hx, hL]
    field_simp
  have hxlow : K / (2 * s) ≤ x := by
    rw [hxval]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hN2 (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * s) hK0.le)]
  have hxhigh : x ≤ K / s := by
    rw [hxval]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hN4 (mul_nonneg hK0.le hs0.le)]
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hxlow
  -- the exponent of the power is at least K
  have hpow : Real.exp (-x) ^ (N + 1) ≤ Real.exp (-K) := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hNK : K ≤ ((N : ℝ) + 1) * x := by
      have h1 : (2 * s + 1) * (K / (2 * s)) ≤ ((N : ℝ) + 1) * x := by
        refine mul_le_mul (by linarith) hxlow (by positivity) (by linarith)
      have h2 : K ≤ (2 * s + 1) * (K / (2 * s)) := by
        rw [le_div_iff₀ (by positivity)] at *
        have : K * (2 * s) ≤ (2 * s + 1) * K := by nlinarith
        rw [mul_comm (2 * s + 1) (K / (2 * s)), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    push_cast
    nlinarith [hNK]
  -- the denominator is bounded below
  have hxK : K ≤ x * (2 * s) := (div_le_iff₀ (by positivity)).mp hxlow
  have hden : K / (2 * s + K) ≤ 1 - Real.exp (-x) := by
    refine le_trans ?_ (one_sub_exp_neg_ge hx0)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hxK]
  have hden0 : (0 : ℝ) < 1 - Real.exp (-x) := lt_of_lt_of_le (by positivity) hden
  have hexpK : Real.exp (-K) ≤ 1 / s ^ 3 := by
    rw [hK, ← Real.exp_log hs0]
    rw [Real.log_exp]
    rw [show -(3 * Real.log s) = Real.log (s ^ 3)⁻¹ by
      rw [Real.log_inv, Real.log_pow]; push_cast; ring]
    rw [Real.exp_log (by positivity)]
    rw [one_div]
    rw [Real.exp_log hs0]
  have hKs : K ≤ s := by
    set u : ℝ := Real.sqrt s with hu
    have hu2 : u ^ 2 = s := Real.sq_sqrt hs0.le
    have hu10 : (10 : ℝ) ≤ u := by
      rw [hu]
      have : Real.sqrt 100 ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
      rwa [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    have hupos : (0 : ℝ) < u := by linarith
    have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos
    have hhalf : Real.log s = 2 * Real.log u := by
      conv_lhs => rw [← hu2]
      rw [Real.log_pow]
      push_cast
      ring
    rw [hK, hhalf, ← hu2]
    nlinarith [hlogu, hu10]
  have hdenlow : K / (3 * s) ≤ 1 - Real.exp (-x) := by
    refine le_trans ?_ hden
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hKs, hK0, hs0]
  have hs3 : s ≤ s ^ 3 := by nlinarith [hs0, hs]
  have hK3 : (27 : ℝ) ≤ K ^ 3 := by
    have h : (12 : ℝ) ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ (by norm_num) hK4 3
    nlinarith [h]
  refine ⟨hden0, ?_, ?_⟩
  · rw [div_le_one hden0]
    refine le_trans hpow (le_trans hexpK ?_)
    refine le_trans ?_ hdenlow
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hK4, hs, hs3, hs0]
  · rw [div_le_one (by positivity)]
    refine le_trans hpow (le_trans hexpK ?_)
    have hcube : (K / (3 * s)) ^ 3 ≤ (1 - Real.exp (-x)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hdenlow 3
    refine le_trans ?_ hcube
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hK4, hs, hs0, hK3, pow_pos hs0 3]

set_option maxHeartbeats 2000000 in
/-- **The explicit Wiman--Valiron right-hand side, at a small window.**  With the sampling scale
tied to the spread by `K = 3 log s`, the bound collapses to `s^{3/2}` times a logarithmic ratio. -/
theorem wv_rhs_le {N : ℕ} {L h s K nu : ℝ} (hs : (100 : ℝ) ≤ s)
    (hK : K = 3 * Real.log s) (hL : L = s ^ 2 / K) (hh : h = K / s)
    (hN2 : 2 * s ≤ (N : ℝ)) (hN4 : (N : ℝ) ≤ 4 * s) (hnu : 0 ≤ nu) :
    (Real.sqrt (2 * (N : ℝ) + 1)
        + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
            / (1 - Real.exp (-((N : ℝ) / (4 * L))))))
        * (2 * L * h
          + 2 * Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) / h)
      + Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3))
          * (Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                / (1 - Real.exp (-((N : ℝ) / (4 * L)))))))
      ≤ 30 * (s * Real.sqrt s) * (1 + Real.log (nu + 4 * s) / Real.log s) := by
  obtain ⟨hden0, hQ1, hQ3⟩ := wv_tail_ratios_le_one hs hK hL hN2 hN4
  have hs0 : (0 : ℝ) < s := by linarith
  set u : ℝ := Real.sqrt s with hu
  have hu2 : u ^ 2 = s := Real.sq_sqrt hs0.le
  have hu10 : (10 : ℝ) ≤ u := by
    rw [hu]
    have h := Real.sqrt_le_sqrt hs
    rwa [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hupos : (0 : ℝ) < u := by linarith
  have hlogs : (4 : ℝ) ≤ Real.log s := by
    have hlog : Real.log 100 ≤ Real.log s := Real.log_le_log (by norm_num) hs
    have hlog100 : (4 : ℝ) ≤ Real.log 100 := by
      have he : Real.exp 4 ≤ 100 := by
        have h2 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
        calc Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le h2 4
          _ ≤ 100 := by norm_num
      have := Real.log_le_log (Real.exp_pos 4) he
      rwa [Real.log_exp] at this
    linarith
  have hK0 : (0 : ℝ) < K := by rw [hK]; linarith
  have hK12 : (12 : ℝ) ≤ K := by rw [hK]; linarith
  set Q₁ : ℝ := Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
    / (1 - Real.exp (-((N : ℝ) / (4 * L)))) with hQ1def
  set Q₃ : ℝ := Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
    / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3 with hQ3def
  have hQ1nn : 0 ≤ Q₁ := by rw [hQ1def]; positivity
  have hQ3nn : 0 ≤ Q₃ := by
    rw [hQ3def]
    exact div_nonneg (pow_nonneg (Real.exp_pos _).le _) (by positivity)
  -- the head factor
  have hroot : Real.sqrt (2 * (N : ℝ) + 1) ≤ 3 * u := by
    have hle : 2 * (N : ℝ) + 1 ≤ 9 * s := by nlinarith [hN4, hs]
    calc Real.sqrt (2 * (N : ℝ) + 1) ≤ Real.sqrt (9 * s) := Real.sqrt_le_sqrt hle
      _ = 3 * u := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 9), hu,
            show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hrootnn : (0 : ℝ) ≤ Real.sqrt (2 * (N : ℝ) + 1) := Real.sqrt_nonneg _
  have hA : Real.sqrt (2 * (N : ℝ) + 1) + 2 * Q₁ ≤ 3.2 * u := by nlinarith [hroot, hQ1, hu10]
  have hAnn : (0 : ℝ) ≤ Real.sqrt (2 * (N : ℝ) + 1) + 2 * Q₁ := by linarith
  -- the scale identity
  have hLh : 2 * L * h = 2 * s := by
    rw [hL, hh]
    field_simp
  -- the logarithm factor
  have hlogratio : (0 : ℝ) ≤ Real.log (nu + 4 * s) / Real.log s := by
    refine div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hhpos : (0 : ℝ) < h := by rw [hh]; positivity
  have hinvexp : 1 / (Real.exp h - 1) ≤ s := by
    have hexph : h ≤ Real.exp h - 1 := by
      have := Real.add_one_le_exp h
      linarith
    have hhs : (1 : ℝ) / h ≤ s := by
      rw [hh, one_div, inv_div]
      exact div_le_self hs0.le (by linarith)
    calc 1 / (Real.exp h - 1) ≤ 1 / h := by
          refine one_div_le_one_div_of_le hhpos hexph
      _ ≤ s := hhs
  have hinvnn : (0 : ℝ) ≤ 1 / (Real.exp h - 1) := by
    have h1 : (1 : ℝ) < Real.exp h := by
      have := Real.add_one_le_exp h
      linarith
    positivity
  have hlogarg : Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1))
      ≤ Real.log (nu + 4 * s) := by
    refine Real.log_le_log (by rw [hLh]; linarith) ?_
    rw [hLh]
    linarith
  have hBlog : 2 * Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) / h
      ≤ (2 / 3) * s * (Real.log (nu + 4 * s) / Real.log s) := by
    have hlogs0 : (0 : ℝ) < Real.log s := by linarith
    have hrw : 2 / 3 * s * (Real.log (nu + 4 * s) / Real.log s) * h
        = 2 * Real.log (nu + 4 * s) := by
      rw [hh, hK]
      field_simp
    rw [div_le_iff₀ hhpos, hrw]
    linarith [hlogarg]
  have hB : 2 * L * h + 2 * Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) / h
      ≤ 2 * s + (2 / 3) * s * (Real.log (nu + 4 * s) / Real.log s) := by
    linarith [hBlog, hLh]
  have hBnn : (0 : ℝ) ≤ 2 * s + (2 / 3) * s * (Real.log (nu + 4 * s) / Real.log s) := by
    have : (0 : ℝ) ≤ (2 / 3) * s * (Real.log (nu + 4 * s) / Real.log s) := by positivity
    linarith
  have hlogpos : (0 : ℝ) ≤ Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) := by
    refine Real.log_nonneg ?_
    rw [hLh]
    linarith
  have hLHSnn : (0 : ℝ)
      ≤ 2 * L * h + 2 * Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) / h := by
    have hpart : (0 : ℝ)
        ≤ 2 * Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) / h :=
      div_nonneg (by linarith) hhpos.le
    linarith [hLh, hs0]
  have hfirst : (Real.sqrt (2 * (N : ℝ) + 1) + 2 * Q₁)
      * (2 * L * h + 2 * Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) / h)
      ≤ (3.2 * u) * (2 * s + (2 / 3) * s * (Real.log (nu + 4 * s) / Real.log s)) :=
    mul_le_mul hA hB hLHSnn (by linarith)
  -- the second term
  have hC₂ : (N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
      + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Q₃) ≤ 55 * (s * s * u) := by
    have h1 : (N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1) ≤ (4 * s) ^ 2 * (3 * u) := by
      refine mul_le_mul ?_ hroot hrootnn (by positivity)
      nlinarith [hN4, hs0, Nat.cast_nonneg (α := ℝ) N]
    have h2 : 2 * (2 * ((N : ℝ) + 1) ^ 2 * Q₃) ≤ 4 * (4 * s + 1) ^ 2 := by
      have hsq : ((N : ℝ) + 1) ^ 2 ≤ (4 * s + 1) ^ 2 := by
        refine pow_le_pow_left₀ (by positivity) (by linarith) 2
      nlinarith [hQ3, hQ3nn, hsq]
    have h3 : 4 * (4 * s + 1) ^ 2 ≤ 7 * (s * s * u) := by nlinarith [hs, hu10, hu2, hs0]
    have h4 : (4 * s) ^ 2 * (3 * u) = 48 * (s * s * u) := by ring
    linarith
  have hC₂nn : (0 : ℝ) ≤ (N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
      + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Q₃) := by positivity
  have hsecond : Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
        + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Q₃))
      * (Real.sqrt (2 * (N : ℝ) + 1) + 2 * Q₁)) ≤ 21 * (s * u) := by
    have hprod : 2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
          + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Q₃))
        * (Real.sqrt (2 * (N : ℝ) + 1) + 2 * Q₁) ≤ (21 * (s * u)) ^ 2 := by
      have hstep : 2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Q₃))
          * (Real.sqrt (2 * (N : ℝ) + 1) + 2 * Q₁)
          ≤ 2 * (55 * (s * s * u)) * (3.2 * u) :=
        mul_le_mul (by linarith [hC₂]) hA hAnn (by positivity)
      have hcalc : 2 * (55 * (s * s * u)) * (3.2 * u) = 352 * (s * s * u ^ 2) := by ring
      have hval : 352 * (s * s * u ^ 2) = 352 * (s * s * s) := by rw [hu2]
      have hgoal : (21 * (s * u)) ^ 2 = 441 * (s * s * u ^ 2) := by ring
      rw [hgoal, hu2]
      have hsss : (0 : ℝ) ≤ s * s * s := by positivity
      linarith [hstep, hcalc, hval, hsss]
    calc Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Q₃))
          * (Real.sqrt (2 * (N : ℝ) + 1) + 2 * Q₁))
        ≤ Real.sqrt ((21 * (s * u)) ^ 2) := Real.sqrt_le_sqrt hprod
      _ = 21 * (s * u) := Real.sqrt_sq (by positivity)
  -- assemble
  have hsu : s * Real.sqrt s = s * u := by rw [hu]
  have hgoalrw : 2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
      / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3 = 2 * ((N : ℝ) + 1) ^ 2 * Q₃ := by
    rw [hQ3def]
    ring
  rw [hsu, hgoalrw]
  have hfinal : (3.2 * u) * (2 * s + (2 / 3) * s * (Real.log (nu + 4 * s) / Real.log s))
      + 21 * (s * u)
      ≤ 30 * (s * u) * (1 + Real.log (nu + 4 * s) / Real.log s) := by
    nlinarith [hlogratio, hupos, hs0, hu10]
  linarith [hfirst, hsecond, hfinal]

variable {a : ℕ → ℂ}

set_option maxHeartbeats 1000000 in
/-- **The Wiman--Valiron estimate at a logarithmic window of width `6 (log s)/s`.**  Choosing the
window inversely proportional to the sampling scale — the regime the `_polynomial` and `_scale`
wrappers exclude — the defect between the logarithmic derivative and the central index is at most
`30 s^{3/2}` times a logarithmic ratio. -/
theorem exists_radius_point_wiman_valiron_small_window
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d s : ℝ}
    (hcd : c ≤ d) (hs : (100 : ℝ) ≤ s)
    (hsmall : 2 * (2 * (3 * Real.log s) / s)
        * ((centralIndex a (Real.exp (d + 2 * (2 * (3 * Real.log s) / s))) : ℝ)
          - (centralIndex a (Real.exp c) : ℝ)) / s < d - c) :
    ∃ x ∈ Set.Icc (c + 2 * (3 * Real.log s) / s) (d + 2 * (3 * Real.log s) / s), ∃ z : ℂ,
      ‖z‖ = Real.exp x ∧ maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ 30 * (s * Real.sqrt s)
            * (1 + Real.log ((centralIndex a (Real.exp x) : ℝ) + 4 * s) / Real.log s) := by
  have hs0 : (0 : ℝ) < s := by linarith
  set K : ℝ := 3 * Real.log s with hKdef
  have hlogs : (4 : ℝ) ≤ Real.log s := by
    have hlog : Real.log 100 ≤ Real.log s := Real.log_le_log (by norm_num) hs
    have hlog100 : (4 : ℝ) ≤ Real.log 100 := by
      have he : Real.exp 4 ≤ 100 := by
        have h2 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
        calc Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le h2 4
          _ ≤ 100 := by norm_num
      have := Real.log_le_log (Real.exp_pos 4) he
      rwa [Real.log_exp] at this
    linarith
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; linarith
  set H : ℝ := 2 * K / s with hHdef
  have hH : (0 : ℝ) < H := by rw [hHdef]; positivity
  set N : ℕ := ⌈2 * s⌉₊ with hNdef
  have hN2 : 2 * s ≤ (N : ℝ) := Nat.le_ceil _
  have hN4 : (N : ℝ) ≤ 4 * s := by
    have h1 : (N : ℝ) < 2 * s + 1 := by
      rw [hNdef]
      exact Nat.ceil_lt_add_one (by positivity)
    linarith
  obtain ⟨x, hx, z, hz, hfz, hbound⟩ :=
    exists_radius_point_wiman_valiron_bound ha hn₀ hcd hH hs0 rfl rfl hsmall hN2 hN4
  refine ⟨x, hx, z, hz, hfz, le_trans hbound ?_⟩
  have hL : 2 * s / H = s ^ 2 / K := by
    rw [hHdef]
    field_simp
  have hh : H / 2 = K / s := by
    rw [hHdef]
    field_simp
  exact wv_rhs_le hs hKdef hL hh hN2 hN4 (Nat.cast_nonneg _)

end GaloisForLFunctions.HTGeometry
