import Mathlib

/-!
# Convexity of the Jensen mass

For a sequence `c_k ≥ 0` put `m_d(t) = Σ_{k≤d} C(d,k) t^{d−k} c_k`; when `c` is the moment sequence of
a random variable `V`, this is `E (t + V)^d`, and `∂_t m_{d+1} = (d + 1) m_d`. As a polynomial in `t`
with nonnegative coefficients, `m_d` is log-convex in `log t` (weighted Jensen for `exp`):

`log m_{d+1}(t') ≥ log m_{d+1}(t) + log(t'/t) · t (d + 1) m_d(t)/m_{d+1}(t)`.

Convex functions converging to a differentiable limit have converging derivatives. So a first-order
law `(1/d) log m_d(θ ℓ_d) − log ℓ_d → log(1 + θ)` upgrades, with no concentration estimate, to the
ratio law `ℓ_{d+1} m_d(θ ℓ_{d+1})/m_{d+1}(θ ℓ_{d+1}) → 1/(1 + θ)`.
-/

open Filter Topology

namespace FiniteFreeProbability

noncomputable section

/-- `m_d(t) = Σ_{k≤d} C(d,k) t^{d−k} c_k`. -/
def jensenMass (c : ℕ → ℝ) (d : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d + 1), (d.choose k : ℝ) * t ^ (d - k) * c k

variable {c : ℕ → ℝ}

/-- `Σ_k (m + 1 − k) C(m+1,k) t^{m+1−k} c_k = (m + 1) t m_m(t)`. -/
theorem sum_weight_jensenMass (c : ℕ → ℝ) (m : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range (m + 1 + 1), ((m + 1 - k : ℕ) : ℝ) *
        (((m + 1).choose k : ℝ) * t ^ (m + 1 - k) * c k) =
      ((m : ℝ) + 1) * t * jensenMass c m t := by
  rw [Finset.sum_range_succ, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero, jensenMass,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hch : ((m.choose k : ℝ)) * ((m : ℝ) + 1) =
      (((m + 1).choose k : ℝ)) * ((m + 1 - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_mul_succ_eq m k
  rw [show m + 1 - k = (m - k) + 1 by omega, pow_succ]
  rw [show m + 1 - k = (m - k) + 1 by omega] at hch
  linear_combination (t ^ (m - k) * t * c k) * (-hch)

/-- **Log-convexity in `log t`.** -/
theorem log_jensenMass_ge (hc : ∀ k, 0 ≤ c k) (m : ℕ) {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t')
    (hpos : 0 < jensenMass c (m + 1) t) :
    Real.log (jensenMass c (m + 1) t) +
        Real.log (t' / t) * (t * ((m : ℝ) + 1) * jensenMass c m t / jensenMass c (m + 1) t) ≤
      Real.log (jensenMass c (m + 1) t') := by
  set M := jensenMass c (m + 1) t
  set b := Real.log (t' / t)
  have hq : 0 < t' / t := div_pos ht' ht
  set p : ℕ → ℝ := fun k => (((m + 1).choose k : ℝ) * t ^ (m + 1 - k) * c k) / M
  have hp0 : ∀ k ∈ Finset.range (m + 1 + 1), 0 ≤ p k := fun k _ =>
    div_nonneg (mul_nonneg (by positivity) (hc k)) hpos.le
  have hp1 : ∑ k ∈ Finset.range (m + 1 + 1), p k = 1 := by
    rw [← Finset.sum_div]
    exact div_self hpos.ne'
  have hj := convexOn_exp.map_sum_le (t := Finset.range (m + 1 + 1)) (w := p)
    (p := fun k => ((m + 1 - k : ℕ) : ℝ) * b) hp0 hp1 (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have hexp : ∀ k, Real.exp (((m + 1 - k : ℕ) : ℝ) * b) = (t' / t) ^ (m + 1 - k) := fun k => by
    rw [mul_comm, Real.exp_mul, Real.exp_log hq, Real.rpow_natCast]
  have hrhs : ∑ k ∈ Finset.range (m + 1 + 1), p k * Real.exp (((m + 1 - k : ℕ) : ℝ) * b) =
      jensenMass c (m + 1) t' / M := by
    rw [jensenMass, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hexp, div_pow]
    simp only [p]
    have ht0 : t ^ (m + 1 - k) ≠ 0 := pow_ne_zero _ ht.ne'
    field_simp
  have hlhs : ∑ k ∈ Finset.range (m + 1 + 1), p k * (((m + 1 - k : ℕ) : ℝ) * b) =
      b * (t * ((m : ℝ) + 1) * jensenMass c m t / M) := by
    have h := sum_weight_jensenMass c m t
    calc ∑ k ∈ Finset.range (m + 1 + 1), p k * (((m + 1 - k : ℕ) : ℝ) * b)
        = (b / M) * ∑ k ∈ Finset.range (m + 1 + 1), ((m + 1 - k : ℕ) : ℝ) *
            (((m + 1).choose k : ℝ) * t ^ (m + 1 - k) * c k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [p]
          ring
      _ = _ := by rw [h]; ring
  rw [hrhs, hlhs] at hj
  have hm' : 0 < jensenMass c (m + 1) t' / M := lt_of_lt_of_le (Real.exp_pos _) hj
  have hm'' : 0 < jensenMass c (m + 1) t' := by
    by_contra hneg
    push Not at hneg
    exact absurd hm' (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hneg hpos.le))
  have hlog := Real.log_le_log (Real.exp_pos _) hj
  rw [Real.log_exp, Real.log_div hm''.ne' hpos.ne'] at hlog
  linarith

/-- The slope at `0` of `h ↦ log(1 + θ e^h)`. -/
theorem tendsto_slope_log_one_add {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun h : ℝ => h⁻¹ * (Real.log (1 + θ * Real.exp h) - Real.log (1 + θ))) (𝓝[≠] 0)
      (𝓝 (θ / (1 + θ))) := by
  have hd : HasDerivAt (fun h : ℝ => Real.log (1 + θ * Real.exp h)) (θ / (1 + θ)) 0 := by
    have h1 : HasDerivAt (fun h : ℝ => 1 + θ * Real.exp h) (θ * Real.exp 0) 0 :=
      ((Real.hasDerivAt_exp 0).const_mul θ).const_add 1
    have h2 := h1.log (by rw [Real.exp_zero]; positivity)
    simpa using h2
  have := hasDerivAt_iff_tendsto_slope_zero.1 hd
  simpa [smul_eq_mul] using this

/-- **First-order law implies ratio law.** -/
theorem tendsto_ratio_of_tendsto_log (hc : ∀ k, 0 ≤ c k) {ℓ : ℕ → ℝ}
    (hℓ : ∀ᶠ d in atTop, 0 < ℓ d)
    (hlim : ∀ θ : ℝ, 0 < θ → Tendsto (fun d : ℕ =>
      Real.log (jensenMass c d (θ * ℓ d)) / d - Real.log (ℓ d)) atTop (𝓝 (Real.log (1 + θ))))
    (hpos : ∀ θ : ℝ, 0 < θ → ∀ᶠ d : ℕ in atTop, 0 < jensenMass c d (θ * ℓ d))
    {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun d : ℕ => ℓ (d + 1) * jensenMass c d (θ * ℓ (d + 1)) /
      jensenMass c (d + 1) (θ * ℓ (d + 1))) atTop (𝓝 (1 / (1 + θ))) := by
  set e : ℕ → ℝ := fun d => ℓ (d + 1) * jensenMass c d (θ * ℓ (d + 1)) /
      jensenMass c (d + 1) (θ * ℓ (d + 1))
  -- the convexity inequality at scale `θ`, for a fixed exponential tilt `h`
  have key : ∀ h : ℝ, ∀ᶠ d : ℕ in atTop,
      h * (θ * e d) ≤ (Real.log (jensenMass c (d + 1) (θ * Real.exp h * ℓ (d + 1))) / ((d + 1 : ℕ) : ℝ)
          - Real.log (ℓ (d + 1))) -
        (Real.log (jensenMass c (d + 1) (θ * ℓ (d + 1))) / ((d + 1 : ℕ) : ℝ)
          - Real.log (ℓ (d + 1))) := fun h => by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hℓ,
      (tendsto_add_atTop_nat 1).eventually (hpos θ hθ)] with d hd1 hd2
    have ht : 0 < θ * ℓ (d + 1) := mul_pos hθ hd1
    have ht' : 0 < θ * Real.exp h * ℓ (d + 1) := by positivity
    have hconv := log_jensenMass_ge hc d ht ht' hd2
    have hq : Real.log (θ * Real.exp h * ℓ (d + 1) / (θ * ℓ (d + 1))) = h := by
      rw [show θ * Real.exp h * ℓ (d + 1) / (θ * ℓ (d + 1)) = Real.exp h by
        field_simp, Real.log_exp]
    rw [hq] at hconv
    have hD : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    have hE : θ * ℓ (d + 1) * ((d : ℝ) + 1) * jensenMass c d (θ * ℓ (d + 1)) /
        jensenMass c (d + 1) (θ * ℓ (d + 1)) = ((d + 1 : ℕ) : ℝ) * (θ * e d) := by
      simp only [e]
      push_cast
      ring
    rw [hE] at hconv
    have hdiv : h * (θ * e d) ≤
        (Real.log (jensenMass c (d + 1) (θ * Real.exp h * ℓ (d + 1))) -
          Real.log (jensenMass c (d + 1) (θ * ℓ (d + 1)))) / ((d + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hD]
      linarith
    calc _ ≤ _ := hdiv
      _ = _ := by rw [sub_div]; ring
  -- the limit of the right side
  have hRHS : ∀ h : ℝ, Tendsto (fun d : ℕ =>
      (Real.log (jensenMass c (d + 1) (θ * Real.exp h * ℓ (d + 1))) / ((d + 1 : ℕ) : ℝ)
          - Real.log (ℓ (d + 1))) -
        (Real.log (jensenMass c (d + 1) (θ * ℓ (d + 1))) / ((d + 1 : ℕ) : ℝ)
          - Real.log (ℓ (d + 1)))) atTop
      (𝓝 (Real.log (1 + θ * Real.exp h) - Real.log (1 + θ))) := fun h =>
    ((hlim _ (by positivity)).comp (tendsto_add_atTop_nat 1)).sub
      ((hlim θ hθ).comp (tendsto_add_atTop_nat 1))
  have hslope := tendsto_slope_log_one_add hθ
  have hmain : Tendsto (fun d => θ * e d) atTop (𝓝 (θ / (1 + θ))) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · -- a negative tilt gives the lower bound
      have hneg := (hslope.mono_left (nhdsLT_le_nhdsNE (0 : ℝ))).eventually (lt_mem_nhds ha)
      obtain ⟨h, hh, hh0⟩ := (hneg.and self_mem_nhdsWithin).exists
      have hh0' : h < 0 := hh0
      have hbound : Real.log (1 + θ * Real.exp h) - Real.log (1 + θ) < a * h := by
        have := mul_lt_mul_of_neg_right hh hh0'
        rwa [mul_comm h⁻¹, mul_assoc, inv_mul_cancel₀ hh0'.ne, mul_one] at this
      filter_upwards [key h, (hRHS h).eventually (gt_mem_nhds hbound)] with d h1 h2
      have h3 := lt_of_le_of_lt h1 h2
      rw [mul_comm a h] at h3
      exact (mul_lt_mul_left_of_neg hh0').1 h3
    · -- a positive tilt gives the upper bound
      have hposs := (hslope.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))).eventually (gt_mem_nhds hb)
      obtain ⟨h, hh, hh0⟩ := (hposs.and self_mem_nhdsWithin).exists
      have hh0' : 0 < h := hh0
      have hbound : Real.log (1 + θ * Real.exp h) - Real.log (1 + θ) < b * h := by
        have := mul_lt_mul_of_pos_right hh hh0'
        rwa [mul_comm h⁻¹, mul_assoc, inv_mul_cancel₀ hh0'.ne', mul_one] at this
      filter_upwards [key h, (hRHS h).eventually (gt_mem_nhds hbound)] with d h1 h2
      have h3 := lt_of_le_of_lt h1 h2
      rw [mul_comm b h] at h3
      exact (mul_lt_mul_iff_right₀ hh0').1 h3
  have hfinal := hmain.const_mul θ⁻¹
  rw [← mul_div_assoc, inv_mul_cancel₀ hθ.ne'] at hfinal
  refine hfinal.congr fun d => ?_
  rw [← mul_assoc, inv_mul_cancel₀ hθ.ne', one_mul]

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.tendsto_ratio_of_tendsto_log
