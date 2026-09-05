import GaloisForLFunctions.RHTower.RiemannSiegelPhaseTorusLogMean

/-!
# Steinhaus torus log-means: prime cutoff versus size cutoff

The Steinhaus random multiplicative model puts independent uniform phases on the primes.  Its
expectation over `k` phases is the iterated unit-circle average `torusAverage k`.  Two exact facts:

* `torusAverage_log_norm_eulerProduct` — a **prime-truncated** random Euler product
  `∏_{j} (1 - r_j z_j)⁻¹` (`0 ≤ r_j < 1`, e.g. `r_j = p_j^{-σ}`) has torus log-mean exactly `0`:
  its geometric mean is `1` at every `σ > 0`, including the critical value `σ = 1/2`;
* `torusAverage_log_norm_three_pos` — the **size-truncated** Riemann–Siegel amplitude already at
  length three, `1 + z_2/√2 + z_3/√3`, has strictly positive torus log-mean: its geometric mean
  exceeds `1`.

Together with `circleAverage_log_norm_two_re_mul` (the AFE phase factor has geometric mean one),
this is the computation-free core of the 2026-09-05 finding: a sharp size cutoff creates a positive
log-mean that a prime cutoff does not, and on the critical line it is the Riemann–Siegel phase
`θ(t) − arg D(t)` that must undo it (the geometric mean of `|ζ|` is `1` under RH).
-/

open Real Complex

namespace RHTower

noncomputable section

/-- Iterated unit-circle average over `k` independent phases: the Steinhaus torus expectation. -/
def torusAverage : (k : ℕ) → ((Fin k → ℂ) → ℝ) → ℝ
  | 0, F => F Fin.elim0
  | k + 1, F => torusAverage k (fun z => circleAverage (fun w => F (Fin.snoc z w)) 0 1)

/-- All coordinates on the unit circle. -/
def OnTorus {k : ℕ} (z : Fin k → ℂ) : Prop := ∀ j, ‖z j‖ = 1

theorem onTorus_snoc {k : ℕ} {z : Fin k → ℂ} (hz : OnTorus z) {w : ℂ} (hw : ‖w‖ = 1) :
    OnTorus (Fin.snoc z w : Fin (k + 1) → ℂ) := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa [Fin.snoc_last] using hw
  · simpa [Fin.snoc_castSucc] using hz i

/-- The torus average only sees values on the torus. -/
theorem torusAverage_congr {k : ℕ} {F G : (Fin k → ℂ) → ℝ}
    (h : ∀ z, OnTorus z → F z = G z) : torusAverage k F = torusAverage k G := by
  induction k with
  | zero =>
    simp only [torusAverage]
    exact h _ (fun j => Fin.elim0 j)
  | succ k ih =>
    simp only [torusAverage]
    apply ih
    intro z hz
    apply Real.circleAverage_congr_sphere
    intro w hw
    have hw1 : ‖w‖ = 1 := by simpa using hw
    exact h _ (onTorus_snoc hz hw1)

/-- Torus average of a sum of single-phase functions plus a constant. -/
theorem torusAverage_sum_add_const {k : ℕ} (f : Fin k → ℂ → ℝ)
    (hf : ∀ j, CircleIntegrable (f j) 0 1) (c : ℝ) :
    torusAverage k (fun z => (∑ j, f j (z j)) + c) = (∑ j, circleAverage (f j) 0 1) + c := by
  induction k generalizing c with
  | zero => simp [torusAverage]
  | succ k ih =>
    simp only [torusAverage]
    have hinner : (fun z : Fin k → ℂ =>
        circleAverage (fun w => (∑ j : Fin (k + 1), f j ((Fin.snoc z w : Fin (k + 1) → ℂ) j)) + c) 0 1)
        = fun z => (∑ i : Fin k, f (Fin.castSucc i) (z i))
            + (c + circleAverage (f (Fin.last k)) 0 1) := by
      funext z
      have hsum : (fun w : ℂ => (∑ j : Fin (k + 1), f j ((Fin.snoc z w : Fin (k + 1) → ℂ) j)) + c)
          = (fun _ : ℂ => (∑ i : Fin k, f (Fin.castSucc i) (z i)) + c) + f (Fin.last k) := by
        funext w
        simp only [Pi.add_apply, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
        ring
      have h1 : CircleIntegrable (fun _ : ℂ => (∑ i : Fin k, f (Fin.castSucc i) (z i)) + c) 0 1 :=
        circleIntegrable_const _ _ _
      have h2 : CircleIntegrable (f (Fin.last k)) 0 1 := hf _
      rw [hsum, Real.circleAverage_add h1 h2, Real.circleAverage_const]
      ring
    rw [hinner, ih (f := fun i => f (Fin.castSucc i)) (c := c + circleAverage (f (Fin.last k)) 0 1)
      (fun i => hf _)]
    rw [Fin.sum_univ_castSucc (fun j => circleAverage (f j) 0 1)]
    ring

/-- Negation commutes with the unit-circle average. -/
theorem circleAverage_neg' (f : ℂ → ℝ) :
    circleAverage (fun z => -f z) 0 1 = -circleAverage f 0 1 := by
  simp [Real.circleAverage_def, intervalIntegral.integral_neg]

/-- Jensen's max identity on the unit circle with a scaled phase. -/
theorem circleAverage_log_norm_const_add_mul (a : ℂ) {R : ℝ} (hR : 0 < R) :
    circleAverage (fun z : ℂ => Real.log ‖a + (R : ℂ) * z‖) 0 1 = Real.log (max R ‖a‖) := by
  have key := Real.circleAverage_eq_circleAverage_zero_one
    (f := fun v : ℂ => Real.log ‖a + v‖) (c := (0 : ℂ)) (R := R)
  simp only [add_zero] at key
  rw [← key, circleAverage_log_norm_const_add a hR]

/-- Jensen on the unit circle for one Euler factor: `⨍ log ‖1 - r z‖ = 0` when `0 ≤ r ≤ 1`. -/
theorem circleAverage_log_norm_one_sub_mul {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    circleAverage (fun z : ℂ => Real.log ‖1 - (r : ℂ) * z‖) 0 1 = 0 := by
  rcases hr0.lt_or_eq with hr | hr
  · have hfun : (fun z : ℂ => Real.log ‖1 - (r : ℂ) * z‖)
        = fun z => Real.log ‖(-1 : ℂ) + (r : ℂ) * z‖ := by
      funext z
      rw [← norm_neg]
      congr 2
      ring
    rw [hfun, circleAverage_log_norm_const_add_mul (-1 : ℂ) hr]
    simp [max_eq_right hr1]
  · subst hr
    simp [Real.circleAverage_const]

/-- **Prime-truncated random Euler products have geometric mean one.**  For `0 ≤ r_j < 1` the
Steinhaus torus log-mean of `∏_j (1 - r_j z_j)⁻¹` vanishes. -/
theorem torusAverage_log_norm_eulerProduct {k : ℕ} (r : Fin k → ℝ) (hr0 : ∀ j, 0 ≤ r j)
    (hr1 : ∀ j, r j < 1) :
    torusAverage k (fun z => Real.log ‖∏ j, (1 - (r j : ℂ) * z j)⁻¹‖) = 0 := by
  have hcongr : torusAverage k (fun z => Real.log ‖∏ j, (1 - (r j : ℂ) * z j)⁻¹‖)
      = torusAverage k
          (fun z => (∑ j, (fun w : ℂ => -Real.log ‖1 - (r j : ℂ) * w‖) (z j)) + 0) := by
    apply torusAverage_congr
    intro z hz
    have hne : ∀ j, ‖1 - (r j : ℂ) * z j‖ ≠ 0 := by
      intro j
      have h1 : ‖(r j : ℂ) * z j‖ = r j := by
        rw [norm_mul, hz j, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 j)]
      have : 0 < ‖1 - (r j : ℂ) * z j‖ := by
        have := norm_sub_norm_le (1 : ℂ) ((r j : ℂ) * z j)
        rw [norm_one, h1] at this
        linarith [hr1 j]
      exact this.ne'
    simp only [add_zero]
    rw [norm_prod, Real.log_prod (fun j _ => by rw [norm_inv]; exact inv_ne_zero (hne j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [norm_inv, Real.log_inv]
  have hint : ∀ j, CircleIntegrable (fun w : ℂ => -Real.log ‖1 - (r j : ℂ) * w‖) 0 1 := by
    intro j
    have hmero : MeromorphicOn (fun w : ℂ => 1 - (r j : ℂ) * w) (Metric.sphere (0 : ℂ) |1|) :=
      (analyticOnNhd_const.sub (analyticOnNhd_const.mul analyticOnNhd_id)).meromorphicOn
    exact hmero.circleIntegrable_log_norm.neg
  rw [hcongr, torusAverage_sum_add_const _ hint 0]
  simp only [add_zero]
  apply Finset.sum_eq_zero
  intro j _
  rw [circleAverage_neg', circleAverage_log_norm_one_sub_mul (hr0 j) (hr1 j).le, neg_zero]

/-- One Jensen step for the length-three amplitude: averaging the phase of `3` gives
`log (max (1/√3) ‖1 + w/√2‖)`. -/
theorem circleAverage_log_norm_three_inner (a : ℂ) :
    circleAverage (fun w : ℂ => Real.log ‖a + w / (Real.sqrt 3 : ℂ)‖) 0 1
      = Real.log (max (1 / Real.sqrt 3) ‖a‖) := by
  have h3 : (0 : ℝ) < 1 / Real.sqrt 3 := by positivity
  have hfun : (fun w : ℂ => Real.log ‖a + w / (Real.sqrt 3 : ℂ)‖)
      = fun w => Real.log ‖a + ((1 / Real.sqrt 3 : ℝ) : ℂ) * w‖ := by
    funext w
    congr 3
    push_cast
    ring
  rw [hfun, circleAverage_log_norm_const_add_mul a h3]

/-- The length-two amplitude `‖1 + w/√2‖` is bounded below by `1 - 1/√2 > 0` on the circle. -/
theorem norm_one_add_div_sqrt_two_ge {w : ℂ} (hw : ‖w‖ = 1) :
    1 - 1 / Real.sqrt 2 ≤ ‖1 + w / (Real.sqrt 2 : ℂ)‖ := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hn : ‖w / (Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 := by
    rw [norm_div, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2]
  have htri := norm_add_le (1 + w / (Real.sqrt 2 : ℂ)) (-(w / (Real.sqrt 2 : ℂ)))
  rw [add_neg_cancel_right, norm_one, norm_neg, hn] at htri
  linarith

theorem one_sub_one_div_sqrt_two_pos : 0 < 1 - 1 / Real.sqrt 2 := by
  have : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_one (by positivity)]; exact this
  linarith

/-- **The size-truncated amplitude at length three has geometric mean `> 1`.** -/
theorem torusAverage_log_norm_three_pos :
    0 < torusAverage 2
      (fun z => Real.log ‖1 + z 0 / (Real.sqrt 2 : ℂ) + z 1 / (Real.sqrt 3 : ℂ)‖) := by
  have h2 : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  have hlow := one_sub_one_div_sqrt_two_pos
  -- reduce the two-phase average to one phase
  have hred : torusAverage 2
      (fun z => Real.log ‖1 + z 0 / (Real.sqrt 2 : ℂ) + z 1 / (Real.sqrt 3 : ℂ)‖)
      = circleAverage (fun w : ℂ =>
          Real.log (max (1 / Real.sqrt 3) ‖1 + w / (Real.sqrt 2 : ℂ)‖)) 0 1 := by
    simp only [torusAverage]
    congr 1
    funext w
    have hval : (fun w' : ℂ => Real.log ‖1 + (Fin.snoc (Fin.snoc Fin.elim0 w) w' : Fin 2 → ℂ) 0
          / (Real.sqrt 2 : ℂ) + (Fin.snoc (Fin.snoc Fin.elim0 w) w' : Fin 2 → ℂ) 1
          / (Real.sqrt 3 : ℂ)‖)
        = fun w' => Real.log ‖(1 + w / (Real.sqrt 2 : ℂ)) + w' / (Real.sqrt 3 : ℂ)‖ := by
      funext w'
      simp [Fin.snoc]
    rw [hval, circleAverage_log_norm_three_inner]
  rw [hred]
  set h : ℂ → ℝ := fun w => Real.log ‖1 + w / (Real.sqrt 2 : ℂ)‖ with hh
  set g : ℂ → ℝ := fun w => Real.log (max (1 / Real.sqrt 3) ‖1 + w / (Real.sqrt 2 : ℂ)‖) with hg
  -- the comparison function `h` has average zero
  have hhavg : circleAverage h 0 1 = 0 := by
    have hfun : h = fun w => Real.log ‖(1 : ℂ) + ((1 / Real.sqrt 2 : ℝ) : ℂ) * w‖ := by
      funext w
      simp only [hh]
      congr 3
      push_cast
      ring
    rw [hfun, circleAverage_log_norm_const_add_mul (1 : ℂ) h2]
    have : 1 / Real.sqrt 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact Real.one_le_sqrt.mpr (by norm_num)
    rw [norm_one, max_eq_right this, Real.log_one]
  -- integrability of both pieces
  have hhint : CircleIntegrable h 0 1 := by
    have hmero : MeromorphicOn (fun w : ℂ => 1 + w / (Real.sqrt 2 : ℂ))
        (Metric.sphere (0 : ℂ) |1|) :=
      (analyticOnNhd_const.add (analyticOnNhd_id.div analyticOnNhd_const
        (fun _ _ => by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'))).meromorphicOn
    exact hmero.circleIntegrable_log_norm
  -- the difference `g - h` is continuous and nonnegative on the circle, positive at `-1`
  have hφpos : ∀ θ : ℝ, 0 < ‖1 + circleMap 0 1 θ / (Real.sqrt 2 : ℂ)‖ := by
    intro θ
    have hw : ‖circleMap 0 1 θ‖ = 1 := by
      have := circleMap_mem_sphere (0 : ℂ) zero_le_one θ
      rwa [Metric.mem_sphere, dist_zero_right] at this
    have := norm_one_add_div_sqrt_two_ge hw
    linarith
  have hφcont : Continuous fun θ : ℝ => ‖1 + circleMap 0 1 θ / (Real.sqrt 2 : ℂ)‖ := by
    fun_prop
  have hdiffcont : Continuous fun θ : ℝ => (g - h) (circleMap 0 1 θ) := by
    show Continuous fun θ : ℝ => g (circleMap 0 1 θ) - h (circleMap 0 1 θ)
    simp only [hg, hh]
    refine Continuous.sub ?_ ?_
    · exact (continuous_const.max hφcont).log
        (fun θ => (lt_max_of_lt_right (hφpos θ)).ne')
    · exact hφcont.log (fun θ => (hφpos θ).ne')
  have hdiffint : CircleIntegrable (g - h) 0 1 := hdiffcont.intervalIntegrable _ _
  have hdiffnonneg : ∀ θ : ℝ, 0 ≤ (g - h) (circleMap 0 1 θ) := by
    intro θ
    simp only [Pi.sub_apply, hg, hh, sub_nonneg]
    exact Real.log_le_log (hφpos θ) (le_max_right _ _)
  have hdiffpos : 0 < (g - h) (circleMap 0 1 Real.pi) := by
    have hm1 : circleMap 0 1 Real.pi = -1 := by
      rw [circleMap_zero, Complex.ofReal_one, one_mul, Complex.exp_pi_mul_I]
    simp only [Pi.sub_apply, hg, hh, hm1, sub_pos]
    have hval : ‖(1 : ℂ) + (-1) / (Real.sqrt 2 : ℂ)‖ = 1 - 1 / Real.sqrt 2 := by
      have hcast : (1 : ℂ) + (-1) / (Real.sqrt 2 : ℂ) = ((1 - 1 / Real.sqrt 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlow]
    rw [hval]
    have hlt : 1 - 1 / Real.sqrt 2 < 1 / Real.sqrt 3 := by
      have hs2 : Real.sqrt 2 < 3 / 2 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hs3 : Real.sqrt 3 < 2 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hs2pos : (0 : ℝ) < Real.sqrt 2 := by positivity
      have hs3pos : (0 : ℝ) < Real.sqrt 3 := by positivity
      have h1 : (2 : ℝ) / 3 < 1 / Real.sqrt 2 := by
        rw [div_lt_div_iff₀ (by norm_num) hs2pos]; linarith
      have h2' : (1 : ℝ) / 2 < 1 / Real.sqrt 3 := by
        rw [div_lt_div_iff₀ (by norm_num) hs3pos]; linarith
      linarith
    rw [max_eq_left hlt.le]
    exact Real.log_lt_log hlow hlt
  -- assemble
  have hgint : CircleIntegrable g 0 1 := by
    have := hdiffint.add hhint
    simpa using this
  have hsplit : circleAverage g 0 1 = circleAverage (g - h) 0 1 + circleAverage h 0 1 := by
    rw [Real.circleAverage_sub hgint hhint]; ring
  rw [hsplit, hhavg, add_zero, Real.circleAverage_def, smul_eq_mul]
  apply mul_pos (by positivity)
  exact intervalIntegral.integral_pos (by positivity) hdiffcont.continuousOn
    (fun θ _ => hdiffnonneg θ) ⟨Real.pi, ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩, hdiffpos⟩

end

end RHTower
