import GaloisForLFunctions.RHTower.XiSliceMixedClassDetection
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The lowest nonvanishing slice coefficient is positive at every height

Let `c_n(t)` be the Taylor coefficients at `x = 0` of the slice `g_t(x) = ξ(½+x+it) ξ(½−x+it)`
(`xiSliceCoeff`).  If `Ξ` vanishes to order `k ≥ 0` at the real point `t`, write
`Ξ(z) = (z − t)^k h(z)` near `t` with `h(t) ≠ 0`.  Then

`g_t(x) = Ξ(t − ix) Ξ(t + ix) = x^{2k} · h(t − ix) h(t + ix)`

near `0`, so `c_n(t) = 0` for `n < 2k` and `c_{2k}(t) = h(t)² > 0`, since `h(t)` is real (`Ξ` is real
on `ℝ`).

**Theorem** (`exists_lowest_xiSliceCoeff_pos`).  At every real height `t` there is `k` with
`c_n(t) = 0` for `n < 2k` and `0 < c_{2k}(t)`.

The local form (`xiSliceCoeff_lowest_of_factor`) takes any factorization `Ξ(z) = (z − t)^k h(z)`
near `t` and returns `c_{2k}(t) = h(t)²`.

This is the only unconditional universal-in-`t` positivity of the slice coefficients: the first
nonvanishing coefficient is a square.  In the Eisenstein reading (`EisensteinSliceLSeries`) the
slice is the completed L-function of `E(·, ½+it)`, a product of a degree-one function and its
conjugate, so its lowest nonvanishing central derivative is a square at every height, while the
Riemann hypothesis concerns all the higher ones.
-/

open Complex Filter Topology
open scoped ComplexOrder Nat

namespace RHTower

noncomputable section

/-- **Leibniz rule against a monomial, local form.**  As `iteratedDeriv_pow_mul_zero`, with `G`
analytic at `0` only. -/
theorem iteratedDeriv_pow_mul_zero_of_analyticAt {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0) (k n : ℕ) :
    iteratedDeriv n (fun x => x ^ k * G x) 0 =
      if k ≤ n then ((n.choose k * k ! : ℕ) : ℂ) * iteratedDeriv (n - k) G 0 else 0 := by
  have hpow : ContDiffAt ℂ n (fun x : ℂ => x ^ k) 0 :=
    (by fun_prop : ContDiff ℂ n (fun x : ℂ => x ^ k)).contDiffAt
  have hGc : ContDiffAt ℂ n G 0 := hG.contDiffAt
  have e : (fun x => x ^ k * G x) = (fun x : ℂ => x ^ k) * G := rfl
  rw [e, iteratedDeriv_mul hpow hGc]
  have hd : ∀ i, iteratedDeriv i (fun x : ℂ => x ^ k) 0 = if i = k then (k ! : ℂ) else 0 := by
    intro i
    rw [iteratedDeriv_eq_iterate, iter_deriv_pow]
    split_ifs with hik
    · subst hik
      rw [Nat.sub_self, pow_zero, mul_one, ← Finset.prod_range_reflect]
      have e2 : ∀ j ∈ Finset.range i, ((i : ℂ) - ((i - 1 - j : ℕ) : ℂ)) = ((j + 1 : ℕ) : ℂ) := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [Finset.prod_congr rfl e2, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
    · rcases lt_or_gt_of_ne hik with h | h
      · rw [zero_pow (by omega), mul_zero]
      · rw [Finset.prod_eq_zero (i := k) (Finset.mem_range.mpr h) (by simp), zero_mul]
  simp_rw [hd]
  split_ifs with hkn
  · rw [Finset.sum_eq_single k]
    · simp only [if_true]
      push_cast
      ring
    · intro b _ hb
      simp [hb]
    · intro hk
      exact absurd (Finset.mem_range.mpr (by omega)) hk
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : i ≠ k := by
      have := Finset.mem_range.mp hi
      omega
    simp [this]

/-- `(−ix)^k (ix)^k = x^{2k}`, arranged for a product of two factors. -/
theorem neg_I_mul_pow_mul_I_mul_pow_sub {t : ℝ} {k : ℕ} (h : ℂ → ℂ) (x : ℂ) :
    ((t : ℂ) - I * x - t) ^ k * h ((t : ℂ) - I * x) * (((t : ℂ) + I * x - t) ^ k *
        h ((t : ℂ) + I * x)) = x ^ (2 * k) * (h ((t : ℂ) - I * x) * h ((t : ℂ) + I * x)) := by
  have e1 : (t : ℂ) - I * x - t = -(I * x) := by ring
  have e2 : (t : ℂ) + I * x - t = I * x := by ring
  have e3 : (-(I * x)) ^ k * (I * x) ^ k = x ^ (2 * k) := by
    rw [← mul_pow, show -(I * x) * (I * x) = x ^ 2 by ring_nf; rw [I_sq]; ring, ← pow_mul]
  rw [e1, e2]
  calc (-(I * x)) ^ k * h ((t : ℂ) - I * x) * ((I * x) ^ k * h ((t : ℂ) + I * x))
      = ((-(I * x)) ^ k * (I * x) ^ k) * (h ((t : ℂ) - I * x) * h ((t : ℂ) + I * x)) := by ring
    _ = x ^ (2 * k) * (h ((t : ℂ) - I * x) * h ((t : ℂ) + I * x)) := by rw [e3]

/-- **Slice coefficients at a zero of finite order.**  If `Ξ(z) = (z − t)^k h(z)` near the real
point `t`, with `h` analytic at `t` and `h(t) ≠ 0`, then `c_n(t) = 0` for `n < 2k` and
`c_{2k}(t) = h(t)² > 0`. -/
theorem xiSliceCoeff_lowest_of_factor {t : ℝ} {k : ℕ} {h : ℂ → ℂ} (hhan : AnalyticAt ℂ h t)
    (hh0 : h t ≠ 0) (hev : ∀ᶠ z in 𝓝 (t : ℂ), XiC z = (z - t) ^ k * h z) :
    (∀ n < 2 * k, xiSliceCoeff t n = 0) ∧ xiSliceCoeff t (2 * k) = h t * h t ∧
      0 < xiSliceCoeff t (2 * k) := by
  -- `h(t)` is real
  have hreal : (h (t : ℂ)).im = 0 := by
    have hmap : Tendsto (fun r : ℝ => ((t + r : ℝ) : ℂ)) (𝓝[≠] 0) (𝓝 (t : ℂ)) := by
      have h0 : Tendsto (fun r : ℝ => ((t + r : ℝ) : ℂ)) (𝓝 0) (𝓝 (t : ℂ)) := by
        have hc : Continuous (fun r : ℝ => ((t + r : ℝ) : ℂ)) := by fun_prop
        simpa using hc.tendsto (0 : ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun r : ℝ => (h ((t + r : ℝ) : ℂ)).im) (𝓝[≠] 0) (𝓝 (h (t : ℂ)).im) :=
      (continuous_im.tendsto _).comp (hhan.continuousAt.tendsto.comp hmap)
    have h2 : ∀ᶠ r in 𝓝[≠] (0 : ℝ), (h ((t + r : ℝ) : ℂ)).im = 0 := by
      filter_upwards [hmap.eventually hev, self_mem_nhdsWithin] with r hr hr0
      have hsub : ((t + r : ℝ) : ℂ) - (t : ℂ) = (r : ℂ) := by push_cast; ring
      rw [hsub] at hr
      have hrC : (r : ℂ) ^ k ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr hr0)
      have hq : h ((t + r : ℝ) : ℂ) = XiC ((t + r : ℝ) : ℂ) / (r : ℂ) ^ k := by
        rw [hr]; field_simp
      rw [hq, XiC_ofReal, ← ofReal_pow, ← ofReal_div, ofReal_im]
    have h3 : Tendsto (fun r : ℝ => (h ((t + r : ℝ) : ℂ)).im) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (h2.mono fun r hr => hr.symm)
    exact tendsto_nhds_unique h1 h3
  -- local factorization of the slice
  set H : ℂ → ℂ := fun x => h ((t : ℂ) - I * x) * h ((t : ℂ) + I * x) with hH
  have hHan : AnalyticAt ℂ H 0 := by
    have ha : AnalyticAt ℂ h ((t : ℂ) - I * 0) := by simpa using hhan
    have hb : AnalyticAt ℂ h ((t : ℂ) + I * 0) := by simpa using hhan
    have h1 : AnalyticAt ℂ (fun x => h ((t : ℂ) - I * x)) 0 :=
      AnalyticAt.comp (g := h) (f := fun x : ℂ => (t : ℂ) - I * x) ha (by fun_prop)
    have h2 : AnalyticAt ℂ (fun x => h ((t : ℂ) + I * x)) 0 :=
      AnalyticAt.comp (g := h) (f := fun x : ℂ => (t : ℂ) + I * x) hb (by fun_prop)
    exact h1.mul h2
  have hslice : xiSliceProduct t =ᶠ[𝓝 0] fun x => x ^ (2 * k) * H x := by
    have ta : Tendsto (fun x : ℂ => (t : ℂ) - I * x) (𝓝 0) (𝓝 (t : ℂ)) := by
      have hc : Continuous (fun x : ℂ => (t : ℂ) - I * x) := by fun_prop
      simpa using hc.tendsto (0 : ℂ)
    have tb : Tendsto (fun x : ℂ => (t : ℂ) + I * x) (𝓝 0) (𝓝 (t : ℂ)) := by
      have hc : Continuous (fun x : ℂ => (t : ℂ) + I * x) := by fun_prop
      simpa using hc.tendsto (0 : ℂ)
    filter_upwards [ta.eventually hev, tb.eventually hev] with x hxa hxb
    rw [xiSliceProduct_eq_XiC_mul, hxa, hxb]
    simp only [hH]
    rw [neg_I_mul_pow_mul_I_mul_pow_sub]
  have hcoef : ∀ n, iteratedDeriv n (xiSliceProduct t) 0
      = iteratedDeriv n (fun x => x ^ (2 * k) * H x) 0 := fun n => hslice.iteratedDeriv_eq n
  have hc2k : xiSliceCoeff t (2 * k) = h t * h t := by
    unfold xiSliceCoeff
    rw [hcoef, iteratedDeriv_pow_mul_zero_of_analyticAt hHan, if_pos le_rfl, Nat.sub_self,
      iteratedDeriv_zero, Nat.choose_self, one_mul]
    have hf : ((2 * k).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]
    simp only [hH, mul_zero, sub_zero, add_zero]
  refine ⟨fun n hn => ?_, hc2k, ?_⟩
  · unfold xiSliceCoeff
    rw [hcoef, iteratedDeriv_pow_mul_zero_of_analyticAt hHan, if_neg (by omega), mul_zero]
  · rw [hc2k]
    have hrealeq : h (t : ℂ) = ((h (t : ℂ)).re : ℂ) := Complex.ext (by simp) (by simp [hreal])
    have hre0 : (h (t : ℂ)).re ≠ 0 := by
      intro h0
      apply hh0
      rw [hrealeq, h0, ofReal_zero]
    rw [hrealeq, ← ofReal_mul]
    exact zero_lt_real.mpr (mul_self_pos.mpr hre0)

/-- **The lowest nonvanishing slice coefficient is positive at every height.** -/
theorem exists_lowest_xiSliceCoeff_pos (t : ℝ) :
    ∃ k : ℕ, (∀ n < 2 * k, xiSliceCoeff t n = 0) ∧ 0 < xiSliceCoeff t (2 * k) := by
  have hXan : AnalyticAt ℂ XiC (t : ℂ) := XiC_differentiable.analyticAt _
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (XiC_order_ne_top (t : ℂ))
  obtain ⟨h, hhan, hh0, hev⟩ := hXan.analyticOrderAt_eq_natCast.mp hk.symm
  obtain ⟨hlow, -, hpos⟩ :=
    xiSliceCoeff_lowest_of_factor hhan hh0 (hev.mono fun z hz => by rwa [smul_eq_mul] at hz)
  exact ⟨k, hlow, hpos⟩

end

end RHTower
