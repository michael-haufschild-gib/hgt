import GaloisForLFunctions.RHTower.WeilLagFejerBlockExcursionRigidity

/-!
# Lattice excursions obey the level budget

Let `Φ(t) = Σ_i c_i e^{δ_i t} cos(m_i t)` be a lattice configuration. The weights are `c_i > 0`,
the frequencies `m_i ≥ 1` are integers, the rates lie in `[0, Θ]`, and the frequency moment
`μ_α = Σ c_i m_i^α` is finite for some `α > 0`. Let `v(T) = |{Φ > 0} ∩ (T, T + 2π]|`.

**Theorem** (`Admissible.sum_log_inv_excursion_le`). The excursions at the dyadic periods
`T_k = 2π 2^k` satisfy

`Σ_{k<n} log(1/v(T_k))/2^k ≤ (4πΘ + 4|log Σc| + 2|log μ_α − 2 log ¾|)/α + 2|log(π/(8e^{2πΘ}))|`.

Hence `v(T) ≤ e^{−f(T)T}` along `T_k` with `f ≥ 0` forces `Σ_k f(2π2^k) < ∞`
(`Admissible.summable_of_excursion_le`). This is the rigid side of the Paley–Wiener threshold
for every positive lattice configuration with a frequency moment, with no block structure.

**Proof.**
* *Period positivity* (`integral_weight_nonneg`). For `T ∈ 2πℤ`, `δ ≥ 0` and integer frequencies,
  `∫_T^{T+2π} e^{δt} cos(m't)(1 + cos(mt)) dt ≥ 0`, and it is at least `π e^{δT}` when `m' = m`.
  This uses the antiderivative `e^{δt}(δ cos at + a sin at)/(δ² + a²)`.
* *Frequency amplitudes* (`Admissible.freqAmp_le`). Weighting `Φ` by `1 + cos(kt)` over one period
  gives `π A_k(T) ≤ 2 A(T) e^{2πΘ} v(T)`. Here `A_k` is the amplitude at frequency `k` and `A` the
  total amplitude.
* *Share* (`Admissible.three_quarters_le_highFreq`). Summing over `k ≤ N = ⌊π/(8e^{2πΘ} v)⌋`, the
  frequencies `m > N` carry three quarters of `A(T)`.
* *Level budget* (`LevelBudget.sum_div_two_pow_le`, with sharpness `K_i = m_i^α` and rates `2πδ`):
  Markov and Cauchy–Schwarz in time give `Σ_k α log(N_k + 1)/2^k ≤ 4πΘ + C`.
-/

open MeasureTheory Set RHTower

noncomputable section

namespace RHTower.LatticeExcursion

/-- `d/dt [e^{δt}(δ cos at + a sin at)] = (δ² + a²) e^{δt} cos at`. -/
theorem hasDerivAt_expCos (δ a t : ℝ) :
    HasDerivAt (fun t => Real.exp (δ * t) * (δ * Real.cos (a * t) + a * Real.sin (a * t)))
      ((δ ^ 2 + a ^ 2) * (Real.exp (δ * t) * Real.cos (a * t))) t := by
  have h1 : HasDerivAt (fun t => Real.exp (δ * t)) (Real.exp (δ * t) * δ) t := by
    have := (hasDerivAt_id t).const_mul δ
    simpa using this.exp
  have h2 : HasDerivAt (fun t => Real.cos (a * t)) (-Real.sin (a * t) * a) t := by
    have := ((hasDerivAt_id t).const_mul a).cos
    simpa using this
  have h3 : HasDerivAt (fun t => Real.sin (a * t)) (Real.cos (a * t) * a) t := by
    have := ((hasDerivAt_id t).const_mul a).sin
    simpa using this
  have h4 := h1.mul ((h2.const_mul δ).add (h3.const_mul a))
  exact h4.congr_deriv (by simp only [Pi.add_apply]; ring)

/-- **Period integral.** For an integer `a`, `δ ≥ 0` and `T ∈ 2πℤ`,
`∫_T^{T+2π} e^{δt} cos(at) dt ≥ 0`, and it is at least `2π e^{δT}` when `a = 0`. -/
theorem integral_exp_mul_cos_period_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (a : ℤ) (j : ℤ) :
    0 ≤ ∫ t in (2 * Real.pi * j)..(2 * Real.pi * j + 2 * Real.pi),
      Real.exp (δ * t) * Real.cos (a * t) := by
  rcases eq_or_ne (δ ^ 2 + (a : ℝ) ^ 2) 0 with h0 | h0
  · have hδ0 : δ = 0 := by nlinarith [sq_nonneg δ, sq_nonneg (a : ℝ)]
    have ha0 : (a : ℝ) = 0 := by nlinarith [sq_nonneg δ, sq_nonneg (a : ℝ)]
    simp only [hδ0, ha0, zero_mul, Real.exp_zero, Real.cos_zero, mul_one,
      intervalIntegral.integral_const, smul_eq_mul]
    nlinarith [Real.pi_pos]
  · have hpos : 0 < δ ^ 2 + (a : ℝ) ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have hint : ∫ t in (2 * Real.pi * j)..(2 * Real.pi * j + 2 * Real.pi),
        (δ ^ 2 + (a : ℝ) ^ 2) * (Real.exp (δ * t) * Real.cos (a * t)) =
        Real.exp (δ * (2 * Real.pi * j + 2 * Real.pi)) *
            (δ * Real.cos (a * (2 * Real.pi * j + 2 * Real.pi)) +
              a * Real.sin (a * (2 * Real.pi * j + 2 * Real.pi))) -
          Real.exp (δ * (2 * Real.pi * j)) *
            (δ * Real.cos (a * (2 * Real.pi * j)) + a * Real.sin (a * (2 * Real.pi * j))) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_expCos δ a t)
        (by
          apply Continuous.intervalIntegrable
          fun_prop)
    rw [intervalIntegral.integral_const_mul] at hint
    have hc1 : Real.cos (a * (2 * Real.pi * j + 2 * Real.pi)) = 1 := by
      have : (a : ℝ) * (2 * Real.pi * j + 2 * Real.pi) = ((a * (j + 1) : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast; ring
      rw [this, Real.cos_int_mul_two_pi]
    have hs1 : Real.sin (a * (2 * Real.pi * j + 2 * Real.pi)) = 0 := by
      have : (a : ℝ) * (2 * Real.pi * j + 2 * Real.pi) = ((2 * a * (j + 1) : ℤ) : ℝ) * Real.pi := by
        push_cast; ring
      rw [this, Real.sin_int_mul_pi]
    have hc0 : Real.cos (a * (2 * Real.pi * j)) = 1 := by
      have : (a : ℝ) * (2 * Real.pi * j) = ((a * j : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
      rw [this, Real.cos_int_mul_two_pi]
    have hs0 : Real.sin (a * (2 * Real.pi * j)) = 0 := by
      have : (a : ℝ) * (2 * Real.pi * j) = ((2 * a * j : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [this, Real.sin_int_mul_pi]
    rw [hc1, hs1, hc0, hs0] at hint
    have hmono : Real.exp (δ * (2 * Real.pi * j)) ≤ Real.exp (δ * (2 * Real.pi * j + 2 * Real.pi)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have : 0 ≤ (δ ^ 2 + (a : ℝ) ^ 2) * ∫ t in (2 * Real.pi * j)..(2 * Real.pi * j + 2 * Real.pi),
        Real.exp (δ * t) * Real.cos (a * t) := by
      rw [hint]; nlinarith
    exact (mul_nonneg_iff_of_pos_left hpos).mp this

/-- `∫_T^{T+2π} e^{δt} dt ≥ 2π e^{δT}` for `δ ≥ 0`. -/
theorem integral_exp_period_ge {δ : ℝ} (hδ : 0 ≤ δ) (T : ℝ) :
    2 * Real.pi * Real.exp (δ * T) ≤ ∫ t in T..(T + 2 * Real.pi), Real.exp (δ * t) := by
  have hle : T ≤ T + 2 * Real.pi := by linarith [Real.pi_pos]
  have h := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => Real.exp (δ * T))
    (g := fun t => Real.exp (δ * t)) hle intervalIntegrable_const
    (by apply Continuous.intervalIntegrable; fun_prop)
    (fun t ht => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.1 hδ))
  rw [intervalIntegral.integral_const, smul_eq_mul, show T + 2 * Real.pi - T = 2 * Real.pi by ring]
    at h
  exact h

/-- **One weighted period.** For frequencies `m', m ≥ 1`, `δ ≥ 0` and `T = 2πj`,
`∫_T^{T+2π} e^{δt} cos(m't)(1 + cos(mt)) dt ≥ 0`, and it is at least `π e^{δT}` when `m' = m`. -/
theorem integral_weight_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (m' m : ℕ) (j : ℤ) :
    0 ≤ ∫ t in (2 * Real.pi * j)..(2 * Real.pi * j + 2 * Real.pi),
      Real.exp (δ * t) * Real.cos (m' * t) * (1 + Real.cos (m * t)) ∧
    (m' = m → Real.pi * Real.exp (δ * (2 * Real.pi * j)) ≤
      ∫ t in (2 * Real.pi * j)..(2 * Real.pi * j + 2 * Real.pi),
        Real.exp (δ * t) * Real.cos (m' * t) * (1 + Real.cos (m * t))) := by
  have e : (fun t => Real.exp (δ * t) * Real.cos (m' * t) * (1 + Real.cos (m * t))) =
      fun t => Real.exp (δ * t) * Real.cos (((m' : ℤ) : ℝ) * t) +
        (1 / 2) * (Real.exp (δ * t) * Real.cos ((((m' : ℤ) + m : ℤ) : ℝ) * t)) +
        (1 / 2) * (Real.exp (δ * t) * Real.cos ((((m' : ℤ) - m : ℤ) : ℝ) * t)) := by
    funext t
    push_cast
    have h1 := Real.cos_add (m' * t) (m * t)
    have h2 := Real.cos_sub (m' * t) (m * t)
    rw [show ((m' : ℝ) + m) * t = m' * t + m * t by ring,
      show ((m' : ℝ) - m) * t = m' * t - m * t by ring, h1, h2]
    ring
  have hc : ∀ a : ℤ, IntervalIntegrable (fun t => Real.exp (δ * t) * Real.cos (a * t)) volume
      (2 * Real.pi * j) (2 * Real.pi * j + 2 * Real.pi) := fun a => by
    apply Continuous.intervalIntegrable; fun_prop
  rw [e, intervalIntegral.integral_add ((hc _).add ((hc _).const_mul _)) ((hc _).const_mul _),
    intervalIntegral.integral_add (hc _) ((hc _).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have i1 := integral_exp_mul_cos_period_nonneg hδ (m' : ℤ) j
  have i2 := integral_exp_mul_cos_period_nonneg hδ ((m' : ℤ) + m) j
  have i3 := integral_exp_mul_cos_period_nonneg hδ ((m' : ℤ) - m) j
  refine ⟨by positivity, fun hm => ?_⟩
  have h0 : (((m' : ℤ) - m : ℤ) : ℝ) = 0 := by rw [hm]; simp
  have i4 := integral_exp_period_ge hδ (2 * Real.pi * j)
  rw [h0] at i3 ⊢
  simp only [zero_mul, Real.cos_zero, mul_one] at i3 ⊢
  linarith

/-! ## Lattice configurations -/

variable {ι : Type*} {c δ : ι → ℝ} {m : ι → ℕ} {Θ α : ℝ}

/-- The lattice lag function `Φ(t) = Σ_i c_i e^{δ_i t} cos(m_i t)`. -/
noncomputable def latticeLag (c δ : ι → ℝ) (m : ι → ℕ) (t : ℝ) : ℝ :=
  ∑' i, c i * Real.exp (δ i * t) * Real.cos (m i * t)

/-- Positive weights, frequencies `≥ 1`, rates in `[0, Θ]`, finite frequency moment of order `α`. -/
structure Admissible (c δ : ι → ℝ) (m : ι → ℕ) (Θ α : ℝ) : Prop where
  c_pos : ∀ i, 0 < c i
  m_pos : ∀ i, 1 ≤ m i
  δ_nonneg : ∀ i, 0 ≤ δ i
  δ_le : ∀ i, δ i ≤ Θ
  α_pos : 0 < α
  moment : Summable fun i => c i * (m i : ℝ) ^ α

theorem Admissible.one_le_rpow (h : Admissible c δ m Θ α) (i : ι) : 1 ≤ (m i : ℝ) ^ α :=
  Real.one_le_rpow (by exact_mod_cast h.m_pos i) h.α_pos.le

theorem Admissible.summable_c (h : Admissible c δ m Θ α) : Summable c :=
  Summable.of_nonneg_of_le (fun i => (h.c_pos i).le)
    (fun i => le_mul_of_one_le_right (h.c_pos i).le (h.one_le_rpow i)) h.moment

theorem Admissible.norm_term_le (h : Admissible c δ m Θ α) {R t : ℝ} (ht : |t| ≤ R) (i : ι) :
    ‖c i * Real.exp (δ i * t) * Real.cos (m i * t)‖ ≤ c i * Real.exp (Θ * R) := by
  have hR : 0 ≤ R := (abs_nonneg t).trans ht
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (h.c_pos i), abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (δ i * t) ≤ Real.exp (Θ * R) := by
    refine Real.exp_le_exp.mpr ?_
    calc δ i * t ≤ δ i * |t| := mul_le_mul_of_nonneg_left (le_abs_self t) (h.δ_nonneg i)
      _ ≤ δ i * R := mul_le_mul_of_nonneg_left ht (h.δ_nonneg i)
      _ ≤ Θ * R := mul_le_mul_of_nonneg_right (h.δ_le i) hR
  calc c i * Real.exp (δ i * t) * |Real.cos (m i * t)| ≤ c i * Real.exp (δ i * t) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity [h.c_pos i])
    _ ≤ c i * Real.exp (Θ * R) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left h1 (h.c_pos i).le

theorem Admissible.summable_term (h : Admissible c δ m Θ α) (t : ℝ) :
    Summable fun i => c i * Real.exp (δ i * t) * Real.cos (m i * t) :=
  Summable.of_norm_bounded (h.summable_c.mul_right (Real.exp (Θ * |t|)))
    (fun i => h.norm_term_le le_rfl i)

theorem Admissible.continuous_latticeLag (h : Admissible c δ m Θ α) :
    Continuous (latticeLag c δ m) := by
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  have hloc : ContinuousOn (latticeLag c δ m) (Icc (t₀ - 1) (t₀ + 1)) :=
    continuousOn_tsum (fun i => (by fun_prop :
      Continuous fun t : ℝ => c i * Real.exp (δ i * t) * Real.cos (m i * t)).continuousOn)
      (h.summable_c.mul_right (Real.exp (Θ * (|t₀| + 1)))) (fun i t ht => h.norm_term_le (by
        have h1 := abs_sub_abs_le_abs_sub t t₀
        have h2 : |t - t₀| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        linarith) i)
  exact (hloc t₀ ⟨by linarith, by linarith⟩).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

theorem Admissible.toLevel (h : Admissible c δ m Θ α) :
    (∀ i, 0 < c i) ∧ (∀ i, 1 ≤ (m i : ℝ) ^ α) ∧ (Summable fun i => c i * (m i : ℝ) ^ α) :=
  ⟨h.c_pos, h.one_le_rpow, h.moment⟩

/-- `Φ(t) ≤ A(T) e^{Θ(t−T)}` for `0 ≤ T ≤ t`, with `A(T) = Σ c e^{δT}`. -/
theorem Admissible.latticeLag_le (h : Admissible c δ m Θ α) {T t : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) :
    latticeLag c δ m t ≤ LevelBudget.level c δ T * Real.exp (Θ * (t - T)) := by
  have hs := LevelBudget.summable_level_term (K := fun i => (m i : ℝ) ^ α) h.c_pos h.one_le_rpow
    h.moment h.δ_le hT
  unfold latticeLag LevelBudget.level
  rw [← tsum_mul_right]
  refine (h.summable_term t).tsum_le_tsum (fun i => ?_) (hs.mul_right _)
  have hc := (h.c_pos i).le
  calc c i * Real.exp (δ i * t) * Real.cos (m i * t) ≤ c i * Real.exp (δ i * t) * 1 :=
        mul_le_mul_of_nonneg_left (Real.cos_le_one _) (by positivity)
    _ = c i * Real.exp (δ i * T) * Real.exp (δ i * (t - T)) := by
        rw [mul_one, mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ c i * Real.exp (δ i * T) * Real.exp (Θ * (t - T)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (h.δ_le i) (by linarith))) (by positivity)

/-- The excursion measure `|{Φ > 0} ∩ (T, T + 2π]|`. -/
noncomputable def excursion (c δ : ι → ℝ) (m : ι → ℕ) (T : ℝ) : ℝ :=
  (volume ({t | 0 < latticeLag c δ m t} ∩ Ioc T (T + 2 * Real.pi))).toReal

/-- The amplitude at frequency `k`: `A_k(T) = Σ_{m_i = k} c_i e^{δ_i T}`. -/
noncomputable def freqAmp (c δ : ι → ℝ) (m : ι → ℕ) (k : ℕ) (T : ℝ) : ℝ :=
  ∑' i, Set.indicator {i | m i = k} (fun i => c i * Real.exp (δ i * T)) i

theorem Admissible.Θ_nonneg [Nonempty ι] (h : Admissible c δ m Θ α) : 0 ≤ Θ :=
  (h.δ_nonneg (Classical.arbitrary ι)).trans (h.δ_le _)

/-- **Each frequency amplitude is bounded by the excursions.** For `T = 2πj`,
`π A_k(T) ≤ 2 A(T) e^{2πΘ} |{Φ > 0} ∩ (T, T + 2π]|`. -/
theorem Admissible.freqAmp_le [Countable ι] [Nonempty ι] (h : Admissible c δ m Θ α) (k j : ℕ) :
    Real.pi * freqAmp c δ m k (2 * Real.pi * j) ≤
      2 * LevelBudget.level c δ (2 * Real.pi * j) * Real.exp (2 * Real.pi * Θ) *
        excursion c δ m (2 * Real.pi * j) := by
  have hπ := Real.pi_pos
  have hΘ := h.Θ_nonneg
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 2 * Real.pi * j := ⟨_, rfl⟩
  rw [← hTdef]
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hle : T ≤ T + 2 * Real.pi := by linarith
  set F : ι → ℝ → ℝ := fun i t => c i * Real.exp (δ i * t) * Real.cos (m i * t) *
    (1 + Real.cos (k * t)) with hF
  set R : ℝ := T + 2 * Real.pi
  -- interchange of sum and integral
  have hsum : HasSum (fun i => ∫ t in T..(T + 2 * Real.pi), F i t)
      (∫ t in T..(T + 2 * Real.pi), latticeLag c δ m t * (1 + Real.cos (k * t))) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun i _ => 2 * (c i * Real.exp (Θ * R))) (fun i => ?_) (fun i => ?_) ?_ ?_ ?_
    · exact (by fun_prop : Continuous (F i)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Set.uIoc_of_le hle] at ht
      have htR : |t| ≤ R := by
        rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.2
      have h1 := h.norm_term_le htR i
      have h2 : ‖1 + Real.cos (k * t)‖ ≤ 2 := by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [Real.neg_one_le_cos (k * t),
          Real.cos_le_one (k * t)]
      calc ‖F i t‖ = ‖c i * Real.exp (δ i * t) * Real.cos (m i * t)‖ * ‖1 + Real.cos (k * t)‖ :=
            norm_mul _ _
        _ ≤ (c i * Real.exp (Θ * R)) * 2 :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity [h.c_pos i])
        _ = 2 * (c i * Real.exp (Θ * R)) := by ring
    · exact Filter.Eventually.of_forall fun t _ =>
        ((h.summable_c.mul_right (Real.exp (Θ * R))).mul_left 2)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun t _ => ?_
      exact ((h.summable_term t).hasSum.mul_right (1 + Real.cos (k * t)))
  -- each term is a nonnegative multiple of a weighted period integral
  have hterm : ∀ i, ∫ t in T..(T + 2 * Real.pi), F i t = c i *
      ∫ t in T..(T + 2 * Real.pi), Real.exp (δ i * t) * Real.cos (m i * t) * (1 + Real.cos (k * t)) := by
    intro i
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; simp only [hF]; ring
  have hj : T = 2 * Real.pi * ((j : ℤ) : ℝ) := by rw [hTdef]; push_cast; ring
  have hw := fun i => integral_weight_nonneg (h.δ_nonneg i) (m i) k (j : ℤ)
  -- lower bound
  have hlow : Real.pi * freqAmp c δ m k T ≤
      ∫ t in T..(T + 2 * Real.pi), latticeLag c δ m t * (1 + Real.cos (k * t)) := by
    rw [← hsum.tsum_eq]
    unfold freqAmp
    rw [← tsum_mul_left]
    have hs1 := (LevelBudget.summable_level_term (K := fun i => (m i : ℝ) ^ α) h.c_pos
      h.one_le_rpow h.moment h.δ_le hT0).indicator {i | m i = k}
    refine (hs1.mul_left _).tsum_le_tsum (fun i => ?_) hsum.summable
    rw [hterm i]
    by_cases hi : m i = k
    · rw [Set.indicator_of_mem (show i ∈ {i | m i = k} from hi)]
      have := (hw i).2 hi
      rw [← hj] at this
      have hc := (h.c_pos i).le
      nlinarith
    · rw [Set.indicator_of_notMem (show i ∉ {i | m i = k} from hi), mul_zero]
      have := (hw i).1
      rw [← hj] at this
      exact mul_nonneg (h.c_pos i).le this
  -- upper bound
  set E : Set ℝ := {t | 0 < latticeLag c δ m t} with hE
  have hEm : MeasurableSet E := (isOpen_lt continuous_const h.continuous_latticeLag).measurableSet
  set C : ℝ := 2 * LevelBudget.level c δ T * Real.exp (2 * Real.pi * Θ) with hC
  have hL0 := LevelBudget.level_pos (K := fun i => (m i : ℝ) ^ α) h.c_pos h.one_le_rpow h.moment
    h.δ_le hT0
  have hupp : ∫ t in T..(T + 2 * Real.pi), latticeLag c δ m t * (1 + Real.cos (k * t)) ≤
      ∫ t in T..(T + 2 * Real.pi), E.indicator (fun _ => C) t := by
    refine intervalIntegral.integral_mono_on hle
      (by apply Continuous.intervalIntegrable; exact h.continuous_latticeLag.mul (by fun_prop))
      ((intervalIntegrable_const (c := C)).mono_fun' (by
        exact (aestronglyMeasurable_const.indicator hEm)) (Filter.Eventually.of_forall fun t => by
          show ‖E.indicator (fun _ => C) t‖ ≤ C
          by_cases ht : t ∈ E
          · rw [Set.indicator_of_mem ht, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          · rw [Set.indicator_of_notMem ht, norm_zero]; positivity)) (fun t ht => ?_)
    have hcos0 : 0 ≤ 1 + Real.cos (k * t) := by linarith [Real.neg_one_le_cos (k * t)]
    by_cases hpos : t ∈ E
    · rw [Set.indicator_of_mem hpos]
      have hΦ := h.latticeLag_le hT0 ht.1
      have hexp : Real.exp (Θ * (t - T)) ≤ Real.exp (2 * Real.pi * Θ) :=
        Real.exp_le_exp.mpr (by nlinarith [ht.2])
      have hΦ0 : 0 < latticeLag c δ m t := hpos
      have hcos2 : 1 + Real.cos (k * t) ≤ 2 := by linarith [Real.cos_le_one (k * t)]
      calc latticeLag c δ m t * (1 + Real.cos (k * t)) ≤ latticeLag c δ m t * 2 :=
            mul_le_mul_of_nonneg_left hcos2 hΦ0.le
        _ ≤ (LevelBudget.level c δ T * Real.exp (2 * Real.pi * Θ)) * 2 :=
            mul_le_mul_of_nonneg_right (hΦ.trans (mul_le_mul_of_nonneg_left hexp hL0.le))
              (by norm_num)
        _ = C := by rw [hC]; ring
    · rw [Set.indicator_of_notMem hpos]
      have : latticeLag c δ m t ≤ 0 := by simpa [hE] using hpos
      exact mul_nonpos_of_nonpos_of_nonneg this hcos0
  have hind : ∫ t in T..(T + 2 * Real.pi), E.indicator (fun _ => C) t =
      C * excursion c δ m T := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.setIntegral_indicator hEm,
      MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
    unfold excursion
    rw [Set.inter_comm, Measure.real]
  calc Real.pi * freqAmp c δ m k T ≤ _ := hlow
    _ ≤ _ := hupp
    _ = C * excursion c δ m T := hind
    _ = _ := by rw [hC]

theorem Admissible.summable_amp (h : Admissible c δ m Θ α) {T : ℝ} (hT : 0 ≤ T) :
    Summable fun i => c i * Real.exp (δ i * T) :=
  LevelBudget.summable_level_term (K := fun i => (m i : ℝ) ^ α) h.c_pos h.one_le_rpow h.moment
    h.δ_le hT

/-- **Low frequencies are a small share.** For `T = 2πj` and every `N`,
`Σ_{m_i ≤ N} c_i e^{δ_i T} ≤ N (2/π) e^{2πΘ} A(T) |{Φ > 0} ∩ (T, T+2π]|`. -/
theorem Admissible.lowFreq_le [Countable ι] [Nonempty ι] (h : Admissible c δ m Θ α) (N j : ℕ) :
    ∑' i, Set.indicator {i | m i ≤ N} (fun i => c i * Real.exp (δ i * (2 * Real.pi * j))) i ≤
      N * (2 / Real.pi * Real.exp (2 * Real.pi * Θ) * LevelBudget.level c δ (2 * Real.pi * j) *
        excursion c δ m (2 * Real.pi * j)) := by
  classical
  have hT0 : (0 : ℝ) ≤ 2 * Real.pi * j := by positivity
  have hs := h.summable_amp hT0
  have hpt : ∀ i, Set.indicator {i | m i ≤ N} (fun i => c i * Real.exp (δ i * (2 * Real.pi * j))) i =
      ∑ k ∈ Finset.Icc 1 N, Set.indicator {i | m i = k}
        (fun i => c i * Real.exp (δ i * (2 * Real.pi * j))) i := by
    intro i
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_ite_eq]
    have h1 := h.m_pos i
    simp only [Finset.mem_Icc]
    by_cases hi : m i ≤ N
    · rw [if_pos hi, if_pos ⟨h1, hi⟩]
    · rw [if_neg hi, if_neg (fun h' => hi h'.2)]
  rw [tsum_congr hpt, Summable.tsum_finsetSum (fun k _ => hs.indicator _)]
  calc ∑ k ∈ Finset.Icc 1 N, freqAmp c δ m k (2 * Real.pi * j)
      ≤ ∑ _k ∈ Finset.Icc 1 N, 2 / Real.pi * Real.exp (2 * Real.pi * Θ) *
          LevelBudget.level c δ (2 * Real.pi * j) * excursion c δ m (2 * Real.pi * j) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hk := h.freqAmp_le k j
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
        linarith
    _ = _ := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp

/-- The excursion measure is positive at every period. -/
theorem Admissible.excursion_pos [Countable ι] [Nonempty ι] (h : Admissible c δ m Θ α) (j : ℕ) :
    0 < excursion c δ m (2 * Real.pi * j) := by
  have hT0 : (0 : ℝ) ≤ 2 * Real.pi * j := by positivity
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hk := h.freqAmp_le (m i₀) j
  have hpos : 0 < freqAmp c δ m (m i₀) (2 * Real.pi * j) := by
    refine lt_of_lt_of_le ?_ (((h.summable_amp hT0).indicator {i | m i = m i₀}).le_tsum i₀
      (fun i _ => Set.indicator_nonneg (fun i _ => (mul_pos (h.c_pos i) (Real.exp_pos _)).le) i))
    rw [Set.indicator_of_mem (show i₀ ∈ {i | m i = m i₀} from rfl)]
    exact mul_pos (h.c_pos i₀) (Real.exp_pos _)
  have hL := LevelBudget.level_pos (K := fun i => (m i : ℝ) ^ α) h.c_pos h.one_le_rpow h.moment
    h.δ_le hT0
  have hex0 : 0 ≤ excursion c δ m (2 * Real.pi * j) := ENNReal.toReal_nonneg
  rcases hex0.lt_or_eq with hlt | heq
  · exact hlt
  · rw [← heq, mul_zero] at hk
    nlinarith [Real.pi_pos]

/-- **High frequencies carry three quarters of the amplitude.** With `v` the excursion measure and
`N = ⌊π/(8e^{2πΘ} v)⌋`, the terms with `m_i > N` carry at least `¾ A(T)`. -/
theorem Admissible.three_quarters_le_highFreq [Countable ι] [Nonempty ι] (h : Admissible c δ m Θ α)
    (j : ℕ) :
    3 / 4 * LevelBudget.level c δ (2 * Real.pi * j) ≤
      ∑' i, Set.indicator {i | ⌊Real.pi / (8 * Real.exp (2 * Real.pi * Θ) *
        excursion c δ m (2 * Real.pi * j))⌋₊ < m i} (fun i => c i * Real.exp (δ i * (2 * Real.pi * j))) i := by
  classical
  have hT0 : (0 : ℝ) ≤ 2 * Real.pi * j := by positivity
  set v := excursion c δ m (2 * Real.pi * j) with hv
  set N := ⌊Real.pi / (8 * Real.exp (2 * Real.pi * Θ) * v)⌋₊ with hN
  have hs := h.summable_amp hT0
  have hv0 := h.excursion_pos j
  rw [← hv] at hv0
  have hsplit : LevelBudget.level c δ (2 * Real.pi * j) =
      ∑' i, Set.indicator {i | N < m i} (fun i => c i * Real.exp (δ i * (2 * Real.pi * j))) i +
      ∑' i, Set.indicator {i | m i ≤ N} (fun i => c i * Real.exp (δ i * (2 * Real.pi * j))) i := by
    unfold LevelBudget.level
    rw [← (hs.indicator _).tsum_add (hs.indicator _)]
    refine tsum_congr fun i => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hi : N < m i
    · rw [if_pos hi, if_neg (by omega), add_zero]
    · rw [if_neg hi, if_pos (by omega), zero_add]
  have hlow := h.lowFreq_le N j
  rw [← hv] at hlow
  have hNle : (N : ℝ) ≤ Real.pi / (8 * Real.exp (2 * Real.pi * Θ) * v) :=
    Nat.floor_le (by positivity)
  have hL := LevelBudget.level_pos (K := fun i => (m i : ℝ) ^ α) h.c_pos h.one_le_rpow h.moment
    h.δ_le hT0
  have hbound : (N : ℝ) * (2 / Real.pi * Real.exp (2 * Real.pi * Θ) *
      LevelBudget.level c δ (2 * Real.pi * j) * v) ≤ LevelBudget.level c δ (2 * Real.pi * j) / 4 := by
    have hpos : 0 ≤ 2 / Real.pi * Real.exp (2 * Real.pi * Θ) *
        LevelBudget.level c δ (2 * Real.pi * j) * v := by positivity
    calc (N : ℝ) * (2 / Real.pi * Real.exp (2 * Real.pi * Θ) *
          LevelBudget.level c δ (2 * Real.pi * j) * v)
        ≤ Real.pi / (8 * Real.exp (2 * Real.pi * Θ) * v) * (2 / Real.pi *
          Real.exp (2 * Real.pi * Θ) * LevelBudget.level c δ (2 * Real.pi * j) * v) :=
          mul_le_mul_of_nonneg_right hNle hpos
      _ = LevelBudget.level c δ (2 * Real.pi * j) / 4 := by
          field_simp; ring
  linarith

/-- **Lattice excursions obey the level budget.** For a lattice configuration with positive
weights, rates in `[0, Θ]` and finite frequency moment `μ_α = Σ c m^α`, the excursion measures
`v_k = |{Φ > 0} ∩ (2π2^k, 2π2^k + 2π]|` satisfy
`Σ_{k<n} log(1/v_k)/2^k ≤ (4πΘ + 4|log Σc| + 2|log μ_α − 2 log ¾|)/α + 2|log(π/(8e^{2πΘ}))|`. -/
theorem Admissible.sum_log_inv_excursion_le [Countable ι] [Nonempty ι] (h : Admissible c δ m Θ α)
    (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.log (1 / excursion c δ m (2 * Real.pi * 2 ^ k)) / 2 ^ k ≤
      (4 * Real.pi * Θ + 4 * |Real.log (∑' i, c i)| +
        2 * |Real.log (∑' i, c i * (m i : ℝ) ^ α) - 2 * Real.log (3 / 4)|) / α +
        2 * |Real.log (Real.pi / (8 * Real.exp (2 * Real.pi * Θ)))| := by
  classical
  have hα := h.α_pos
  set v : ℕ → ℝ := fun k => excursion c δ m (2 * Real.pi * 2 ^ k) with hvdef
  set N : ℕ → ℕ := fun k => ⌊Real.pi / (8 * Real.exp (2 * Real.pi * Θ) * v k)⌋₊ with hNdef
  set F : ℕ → ℝ := fun k => α * Real.log ((N k : ℝ) + 1) with hFdef
  -- the level budget with sharpness `m^α` and rescaled rates `2πδ`
  have hδ' : ∀ i, 2 * Real.pi * δ i ≤ 2 * Real.pi * Θ := fun i =>
    mul_le_mul_of_nonneg_left (h.δ_le i) (by positivity)
  have hδ0' : ∀ i, 0 ≤ 2 * Real.pi * δ i := fun i => by have := h.δ_nonneg i; positivity
  have hcast : ∀ k : ℕ, (2 * Real.pi * ((2 ^ k : ℕ) : ℝ)) = 2 * Real.pi * (2 : ℝ) ^ k := by
    intro k; push_cast; ring
  have hshare : ∀ k, 0 ≤ k → 3 / 4 * LevelBudget.level c (fun i => 2 * Real.pi * δ i) (2 ^ k) ≤
      LevelBudget.levelAbove c (fun i => (m i : ℝ) ^ α) (fun i => 2 * Real.pi * δ i)
        (Real.exp (F k)) (2 ^ k) := by
    intro k _
    have h3 := h.three_quarters_le_highFreq (2 ^ k)
    rw [hcast] at h3
    have e1 : LevelBudget.level c (fun i => 2 * Real.pi * δ i) (2 ^ k) =
        LevelBudget.level c δ (2 * Real.pi * 2 ^ k) := by
      unfold LevelBudget.level; congr 1; funext i; ring_nf
    have e2 : LevelBudget.levelAbove c (fun i => (m i : ℝ) ^ α) (fun i => 2 * Real.pi * δ i)
        (Real.exp (F k)) (2 ^ k) =
        ∑' i, Set.indicator {i | N k < m i} (fun i => c i * Real.exp (δ i * (2 * Real.pi * 2 ^ k))) i := by
      unfold LevelBudget.levelAbove
      refine tsum_congr fun i => ?_
      have hset : (Real.exp (F k) ≤ (m i : ℝ) ^ α) ↔ N k < m i := by
        rw [hFdef]
        simp only
        rw [mul_comm, Real.exp_mul, Real.exp_log (by positivity)]
        rw [Real.rpow_le_rpow_iff (by positivity) (Nat.cast_nonneg _) hα]
        constructor
        · intro hle; exact_mod_cast (show ((N k : ℕ) : ℝ) + 1 ≤ (m i : ℝ) from hle)
        · intro hlt; exact_mod_cast hlt
      simp only [Set.indicator_apply, Set.mem_setOf_eq, hset]
      split_ifs <;> ring_nf
    rw [e1, e2]
    simpa [hvdef, hNdef] using h3
  have hbud := LevelBudget.sum_div_two_pow_le (c := c) (K := fun i => (m i : ℝ) ^ α)
    (δ := fun i => 2 * Real.pi * δ i) h.c_pos h.one_le_rpow h.moment hδ' (η := 3 / 4)
    (by norm_num) hδ0' (F := F) (k₀ := 0) hshare n
  simp only [zero_add] at hbud
  have hlev0 : LevelBudget.level c (fun i => 2 * Real.pi * δ i) 0 = ∑' i, c i := by
    unfold LevelBudget.level; simp
  rw [hlev0] at hbud
  -- `F k ≥ α (log(π/(8e^{2πΘ})) + log(1/v_k))`
  set ℓ₀ : ℝ := Real.log (Real.pi / (8 * Real.exp (2 * Real.pi * Θ))) with hℓ₀
  have hF : ∀ k, α * (ℓ₀ + Real.log (1 / v k)) ≤ F k := by
    intro k
    have hv := h.excursion_pos (2 ^ k)
    rw [hcast] at hv
    have hx : 0 < Real.pi / (8 * Real.exp (2 * Real.pi * Θ) * v k) := by
      have : 0 < v k := hv
      positivity
    have hfl := Nat.lt_floor_add_one (Real.pi / (8 * Real.exp (2 * Real.pi * Θ) * v k))
    have hlog := Real.log_le_log hx hfl.le
    have e : Real.log (Real.pi / (8 * Real.exp (2 * Real.pi * Θ) * v k)) = ℓ₀ + Real.log (1 / v k) := by
      rw [hℓ₀, ← Real.log_mul (by positivity) (by have : 0 < v k := hv; positivity)]
      congr 1; field_simp
    rw [hFdef]
    simp only
    have := mul_le_mul_of_nonneg_left hlog hα.le
    rw [e] at this
    exact_mod_cast this
  have hgeo : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k ≤ 2 := sum_geometric_two_le n
  have hsum1 : ∑ k ∈ Finset.range n, α * (ℓ₀ + Real.log (1 / v k)) / 2 ^ k ≤
      2 * (2 * Real.pi * Θ) + 4 * |Real.log (∑' i, c i)| +
        2 * |Real.log (∑' i, c i * (m i : ℝ) ^ α) - 2 * Real.log (3 / 4)| :=
    (Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_right (hF k) (by positivity)).trans hbud
  set X := ∑ k ∈ Finset.range n, Real.log (1 / v k) / 2 ^ k with hX
  set S := ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k with hS
  have hsplit : ∑ k ∈ Finset.range n, α * (ℓ₀ + Real.log (1 / v k)) / 2 ^ k =
      α * ℓ₀ * S + α * X := by
    rw [hS, hX, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_div_pow]; field_simp
  rw [hsplit] at hsum1
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by positivity
  have hℓ : -(2 * |ℓ₀|) ≤ ℓ₀ * S := by
    have := neg_abs_le ℓ₀
    have h1 : -|ℓ₀| * S ≤ ℓ₀ * S := mul_le_mul_of_nonneg_right this hS0
    have h2 : |ℓ₀| * S ≤ |ℓ₀| * 2 := mul_le_mul_of_nonneg_left hgeo (abs_nonneg _)
    linarith
  set B := 4 * Real.pi * Θ + 4 * |Real.log (∑' i, c i)| +
    2 * |Real.log (∑' i, c i * (m i : ℝ) ^ α) - 2 * Real.log (3 / 4)| with hB
  have h1 : α * X ≤ B + α * (2 * |ℓ₀|) := by
    have e : 2 * (2 * Real.pi * Θ) + 4 * |Real.log (∑' i, c i)| +
        2 * |Real.log (∑' i, c i * (m i : ℝ) ^ α) - 2 * Real.log (3 / 4)| = B := by rw [hB]; ring
    rw [e] at hsum1
    have : α * (ℓ₀ * S) ≥ α * (-(2 * |ℓ₀|)) := mul_le_mul_of_nonneg_left hℓ hα.le
    nlinarith
  have hmain : X ≤ B / α + 2 * |ℓ₀| := by
    rw [div_add' _ _ _ hα.ne', le_div_iff₀ hα]
    linarith
  simpa [hvdef] using hmain

/-- **The Paley–Wiener converse for lattice configurations.** If `f ≥ 0` and the excursions at the
dyadic periods satisfy `|{Φ > 0} ∩ (T, T+2π]| ≤ e^{−f(T)T}`, `T = 2π2^k`, for all large `k`, then
`Σ_k f(2π2^k) < ∞`. -/
theorem Admissible.summable_of_excursion_le [Countable ι] [Nonempty ι] (h : Admissible c δ m Θ α)
    {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t)
    (hthin : ∀ᶠ k : ℕ in Filter.atTop, excursion c δ m (2 * Real.pi * 2 ^ k) ≤
      Real.exp (-(f (2 * Real.pi * 2 ^ k) * (2 * Real.pi * 2 ^ k)))) :
    Summable fun k : ℕ => f (2 * Real.pi * 2 ^ k) := by
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.mp hthin
  set g : ℕ → ℝ := fun k => Real.log (1 / excursion c δ m (2 * Real.pi * 2 ^ k)) / 2 ^ k with hg
  set B := (4 * Real.pi * Θ + 4 * |Real.log (∑' i, c i)| +
        2 * |Real.log (∑' i, c i * (m i : ℝ) ^ α) - 2 * Real.log (3 / 4)|) / α +
        2 * |Real.log (Real.pi / (8 * Real.exp (2 * Real.pi * Θ)))|
  have hlow : ∀ j, 2 * Real.pi * f (2 * Real.pi * 2 ^ (k₁ + j)) ≤ g (k₁ + j) := by
    intro j
    have hv := h.excursion_pos (2 ^ (k₁ + j))
    have hcast : (2 * Real.pi * ((2 ^ (k₁ + j) : ℕ) : ℝ)) = 2 * Real.pi * (2 : ℝ) ^ (k₁ + j) := by
      push_cast; ring
    rw [hcast] at hv
    have hle := hk₁ (k₁ + j) (by omega)
    have hlog : f (2 * Real.pi * 2 ^ (k₁ + j)) * (2 * Real.pi * 2 ^ (k₁ + j)) ≤
        Real.log (1 / excursion c δ m (2 * Real.pi * 2 ^ (k₁ + j))) := by
      rw [one_div, Real.log_inv, le_neg]
      calc Real.log (excursion c δ m (2 * Real.pi * 2 ^ (k₁ + j)))
          ≤ Real.log (Real.exp (-(f (2 * Real.pi * 2 ^ (k₁ + j)) * (2 * Real.pi * 2 ^ (k₁ + j))))) :=
            Real.log_le_log hv hle
        _ = _ := Real.log_exp _
    have hp : (0 : ℝ) < 2 ^ (k₁ + j) := by positivity
    simp only [hg]
    rw [le_div_iff₀ hp]
    linarith
  have hbound : ∀ n, ∑ j ∈ Finset.range n, 2 * Real.pi * f (2 * Real.pi * 2 ^ (k₁ + j)) ≤
      B + ∑ k ∈ Finset.range k₁, |g k| := by
    intro n
    have htot := h.sum_log_inv_excursion_le (k₁ + n)
    rw [Finset.sum_range_add] at htot
    have h1 : ∑ j ∈ Finset.range n, 2 * Real.pi * f (2 * Real.pi * 2 ^ (k₁ + j)) ≤
        ∑ j ∈ Finset.range n, g (k₁ + j) := Finset.sum_le_sum fun j _ => hlow j
    have h2 : -(∑ k ∈ Finset.range k₁, |g k|) ≤ ∑ k ∈ Finset.range k₁, g k := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_le_sum fun k _ => neg_abs_le _
    simp only [hg] at htot h1 h2 ⊢
    linarith
  have hshift : Summable fun j : ℕ => f (2 * Real.pi * 2 ^ (j + k₁)) := by
    refine summable_of_sum_range_le (fun j => hf0 _) (c := (B + ∑ k ∈ Finset.range k₁, |g k|) /
      (2 * Real.pi)) fun n => ?_
    rw [le_div_iff₀ (by positivity), Finset.sum_mul]
    have := hbound n
    calc ∑ j ∈ Finset.range n, f (2 * Real.pi * 2 ^ (j + k₁)) * (2 * Real.pi)
        = ∑ j ∈ Finset.range n, 2 * Real.pi * f (2 * Real.pi * 2 ^ (k₁ + j)) :=
          Finset.sum_congr rfl fun j _ => by rw [add_comm j k₁]; ring
      _ ≤ _ := this
  exact (summable_nat_add_iff k₁).mp hshift

end RHTower.LatticeExcursion
