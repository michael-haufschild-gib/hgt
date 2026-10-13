import GaloisForLFunctions.RHTower.BesselKZeroMoments
import GaloisForLFunctions.HTGeometry.ModularArcMinimumPrinciple

/-!
# No nonnegative decaying Whittaker combination on the modular bottom arc

For `c_n = 2π(n+1)` and real coefficients `a_n, b_n` (`n < N`), consider the decaying Whittaker sum

`v(u, y) = Σ_{n<N} K₀(c_n y) (a_n cos c_n u + b_n sin c_n u)`,

so that `√y · v = Σ (Whittaker functions √y K₀(2π|m|y) e^{2πimu}, m ≠ 0)` is a `Δ`-eigenfunction with
eigenvalue `−¼`.  Here `K₀ = kMoment 0`.

**Theorem** (`whittakerArc_coeff_eq_zero`).  If `v ≥ 0` on the bottom arc
`{u² + y² = 1, |u| ≤ ½}` of the standard fundamental domain of `SL₂(ℤ)`, then every `a_n` and `b_n`
vanishes.

Proof.  `v` solves `y(v_uu + v_yy) + v_y = 0`: mode by mode this is Bessel's modified equation
`x(K₂ − K₀) = K₁` (`kMoment_ode`) with `K₀' = −K₁`, `K₁' = −K₂`.  It is `1`-periodic
and decays as `y → ∞` (`K₀(x) ≤ e^{1−x}K₀(1)`, `kMoment_le_exp_mul`).  The minimum principle above the arc
(`nonneg_of_nonneg_on_modularArc`) gives `v(u, 2) ≥ 0` for every `u`.  But `v(·, 2)` has no
constant Fourier mode, so `∫₀¹ v(u, 2) du = 0`; hence `v(·, 2) ≡ 0`, and orthogonality of the
modes gives `K₀(2c_m) a_m / 2 = K₀(2c_m) b_m / 2 = 0` with `K₀ > 0`.

Consequently no nontrivial real combination of the nonconstant decaying Whittaker functions at the
spectral parameter `s = ½` is nonnegative on the bottom arc.  This is the Farkas dual of the
existence of a positive measure on the arc that annihilates them all.
-/

open MeasureTheory Set Filter Topology
open scoped Interval
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-- The frequency `c_n = 2π(n+1)`. -/
def arcFreq (n : ℕ) : ℝ := 2 * Real.pi * ((n : ℝ) + 1)

theorem arcFreq_pos (n : ℕ) : 0 < arcFreq n := by unfold arcFreq; positivity

theorem two_pi_le_arcFreq (n : ℕ) : 2 * Real.pi ≤ arcFreq n := by
  unfold arcFreq
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith [Real.pi_pos]

/-- The trigonometric factor `a cos c u + b sin c u`. -/
def arcTrig (a b : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  a n * Real.cos (arcFreq n * u) + b n * Real.sin (arcFreq n * u)

/-- Its `u`-derivative. -/
def arcTrigDeriv (a b : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  arcFreq n * (b n * Real.cos (arcFreq n * u) - a n * Real.sin (arcFreq n * u))

theorem hasDerivAt_arcTrig (a b : ℕ → ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (arcTrig a b n) (arcTrigDeriv a b n u) u := by
  have hc : HasDerivAt (fun s => arcFreq n * s) (arcFreq n) u := by
    simpa using (hasDerivAt_id u).const_mul (arcFreq n)
  have h := ((hc.cos).const_mul (a n)).add ((hc.sin).const_mul (b n))
  unfold arcTrig arcTrigDeriv
  exact h.congr_deriv (by ring)

theorem hasDerivAt_arcTrigDeriv (a b : ℕ → ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (arcTrigDeriv a b n) (-(arcFreq n ^ 2 * arcTrig a b n u)) u := by
  have hc : HasDerivAt (fun s => arcFreq n * s) (arcFreq n) u := by
    simpa using (hasDerivAt_id u).const_mul (arcFreq n)
  have h := (((hc.cos).const_mul (b n)).sub ((hc.sin).const_mul (a n))).const_mul (arcFreq n)
  unfold arcTrig arcTrigDeriv
  exact h.congr_deriv (by ring)

/-- The decaying Whittaker sum `v(u, y) = Σ K₀(c_n y) T_n(u)`. -/
def whittakerArcSum (N : ℕ) (a b : ℕ → ℝ) (u y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, kMoment 0 (arcFreq n * y) * arcTrig a b n u

/-- `K₀ > 0` on `(0, ∞)`. -/
theorem kMoment_zero_pos_of_pos {r : ℝ} (hr : 0 < r) : 0 < kMoment 0 r := by
  rw [kMoment_eq, setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (kIntegrand_nonneg 0 r)) (integrableOn_kIntegrand 0 hr)]
  have hs : Function.support (kIntegrand 0 r) ∩ Ioi 0 = Ioi 0 := by
    ext t
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    refine ⟨fun h => h.2, fun ht => ⟨?_, ht⟩⟩
    unfold kIntegrand
    exact (mul_pos (pow_pos (Real.cosh_pos t) 0) (Real.exp_pos _)).ne'
  rw [hs, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

theorem hasDerivAt_kMoment_comp (k : ℕ) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun s => kMoment k (arcFreq n * s))
      (-kMoment (k + 1) (arcFreq n * y) * arcFreq n) y := by
  have hc : HasDerivAt (fun s => arcFreq n * s) (arcFreq n) y := by
    simpa using (hasDerivAt_id y).const_mul (arcFreq n)
  exact (hasDerivAt_kMoment k (mul_pos (arcFreq_pos n) hy)).comp y hc

theorem whittakerArcSum_periodic (N : ℕ) (a b : ℕ → ℝ) (u y : ℝ) :
    whittakerArcSum N a b (u + 1) y = whittakerArcSum N a b u y := by
  unfold whittakerArcSum
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  unfold arcTrig arcFreq
  have e : 2 * Real.pi * ((n : ℝ) + 1) * (u + 1) =
      2 * Real.pi * ((n : ℝ) + 1) * u + ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
    push_cast; ring
  rw [e, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

/-- The Whittaker sum solves `y(v_uu + v_yy) + v_y = 0`. -/
theorem whittakerArcSum_eq (N : ℕ) (a b : ℕ → ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    y * ((∑ n ∈ Finset.range N,
          kMoment 0 (arcFreq n * y) * -(arcFreq n ^ 2 * arcTrig a b n u)) +
        ∑ n ∈ Finset.range N,
          kMoment 2 (arcFreq n * y) * arcFreq n ^ 2 * arcTrig a b n u) +
      ∑ n ∈ Finset.range N, -kMoment 1 (arcFreq n * y) * arcFreq n * arcTrig a b n u = 0 := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun n _ => ?_
  have hode : arcFreq n * y * kMoment 2 (arcFreq n * y) - kMoment 1 (arcFreq n * y) -
      arcFreq n * y * kMoment 0 (arcFreq n * y) = 0 := by
    linear_combination kMoment_ode (mul_pos (arcFreq_pos n) hy)
  have e : y * (kMoment 0 (arcFreq n * y) * -(arcFreq n ^ 2 * arcTrig a b n u) +
      kMoment 2 (arcFreq n * y) * arcFreq n ^ 2 * arcTrig a b n u) +
      -kMoment 1 (arcFreq n * y) * arcFreq n * arcTrig a b n u =
      arcFreq n * arcTrig a b n u * (arcFreq n * y * kMoment 2 (arcFreq n * y) -
        kMoment 1 (arcFreq n * y) - arcFreq n * y * kMoment 0 (arcFreq n * y)) := by
    ring
  rw [e, hode, mul_zero]

theorem continuousOn_whittakerArcSum (N : ℕ) (a b : ℕ → ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => whittakerArcSum N a b p.1 p.2) {p | 0 < p.2} := by
  unfold whittakerArcSum
  refine continuousOn_finsetSum _ fun n _ => ?_
  refine ContinuousOn.mul ?_ ?_
  · refine (continuousOn_kMoment 0).comp (by fun_prop) fun p hp => ?_
    exact mul_pos (arcFreq_pos n) hp
  · unfold arcTrig
    fun_prop

theorem abs_arcTrig_le (a b : ℕ → ℝ) (n : ℕ) (u : ℝ) : |arcTrig a b n u| ≤ |a n| + |b n| := by
  unfold arcTrig
  calc |a n * Real.cos (arcFreq n * u) + b n * Real.sin (arcFreq n * u)|
      ≤ |a n * Real.cos (arcFreq n * u)| + |b n * Real.sin (arcFreq n * u)| := abs_add_le _ _
    _ ≤ |a n| + |b n| := by
        rw [abs_mul, abs_mul]
        gcongr
        · exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
        · exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))

theorem whittakerArcSum_decay (N : ℕ) (a b : ℕ → ℝ) :
    ∀ ε > 0, ∃ Y, ∀ u y, Y ≤ y → |whittakerArcSum N a b u y| ≤ ε := by
  intro ε hε
  set C := ∑ n ∈ Finset.range N, (|a n| + |b n|) with hC
  set K := kMoment 0 1 with hK
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun n _ => by positivity
  have hK0 : 0 ≤ K := kMoment_nonneg 0 1
  have hlim : Tendsto (fun y : ℝ => Real.exp (1 - 2 * Real.pi * y) * K * C) atTop (𝓝 0) := by
    have h0 : Tendsto (fun y : ℝ => -(2 * Real.pi * y)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi))
    have h1 : Tendsto (fun y : ℝ => 1 - 2 * Real.pi * y) atTop atBot := by
      simpa [sub_eq_add_neg] using tendsto_atBot_add_const_left atTop 1 h0
    simpa using ((Real.tendsto_exp_atBot.comp h1).mul_const K).mul_const C
  obtain ⟨Y₀, hY₀⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨max Y₀ 1, fun u y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hyY : Y₀ ≤ y := le_trans (le_max_left _ _) hy
  unfold whittakerArcSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (hY₀ y hyY).le
  rw [hC, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hx : 1 ≤ arcFreq n * y := by
    have := two_pi_le_arcFreq n
    nlinarith [Real.pi_gt_three]
  have hdec : kMoment 0 (arcFreq n * y) ≤ Real.exp (1 - arcFreq n * y) * kMoment 0 1 := by
    have := kMoment_le_exp_mul 0 one_pos hx
    rwa [show -(arcFreq n * y - 1) = 1 - arcFreq n * y by ring] at this
  have hexp : Real.exp (1 - arcFreq n * y) ≤ Real.exp (1 - 2 * Real.pi * y) := by
    apply Real.exp_le_exp.mpr
    nlinarith [two_pi_le_arcFreq n]
  rw [abs_mul, abs_of_nonneg (kMoment_nonneg 0 _)]
  calc kMoment 0 (arcFreq n * y) * |arcTrig a b n u|
      ≤ (Real.exp (1 - 2 * Real.pi * y) * K) * (|a n| + |b n|) := by
        apply mul_le_mul _ (abs_arcTrig_le a b n u) (abs_nonneg _) (by positivity)
        exact hdec.trans (mul_le_mul_of_nonneg_right hexp hK0)
    _ = Real.exp (1 - 2 * Real.pi * y) * K * (|a n| + |b n|) := by ring

/-! ### Trigonometric orthogonality on `[0, 1]` -/

theorem integral_cos_two_pi_mul_int {k : ℤ} (hk : k ≠ 0) :
    ∫ u in (0 : ℝ)..1, Real.cos (2 * Real.pi * k * u) = 0 := by
  have hc : (2 * Real.pi * k : ℝ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    positivity
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos, mul_zero,
    mul_one, Real.sin_zero, sub_zero,
    show 2 * Real.pi * (k : ℝ) = ((2 * k : ℤ) : ℝ) * Real.pi by push_cast; ring,
    Real.sin_int_mul_pi, smul_zero]

theorem integral_sin_two_pi_mul_int (k : ℤ) :
    ∫ u in (0 : ℝ)..1, Real.sin (2 * Real.pi * k * u) = 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hc : (2 * Real.pi * k : ℝ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    positivity
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hc, integral_sin, mul_zero,
    mul_one, Real.cos_zero, show 2 * Real.pi * (k : ℝ) = (k : ℤ) * (2 * Real.pi) by ring,
    Real.cos_int_mul_two_pi, sub_self, smul_zero]

/-- `∫₀¹ T_n(u) cos(c_m u) du = a_m/2 · [n = m]` and `∫₀¹ T_n(u) sin(c_m u) du = b_m/2 · [n = m]`. -/
theorem integral_arcTrig_mul_cos (a b : ℕ → ℝ) (n m : ℕ) :
    ∫ u in (0 : ℝ)..1, arcTrig a b n u * Real.cos (arcFreq m * u) =
      if n = m then a m / 2 else 0 := by
  have hsum : ∀ u, arcTrig a b n u * Real.cos (arcFreq m * u) =
      a n / 2 * Real.cos (2 * Real.pi * ((n : ℤ) - m : ℤ) * u) +
      a n / 2 * Real.cos (2 * Real.pi * ((n : ℤ) + m + 2 : ℤ) * u) +
      b n / 2 * Real.sin (2 * Real.pi * ((n : ℤ) + m + 2 : ℤ) * u) +
      b n / 2 * Real.sin (2 * Real.pi * ((n : ℤ) - m : ℤ) * u) := by
    intro u
    unfold arcTrig arcFreq
    have e1 : 2 * Real.pi * (((n : ℤ) - m : ℤ) : ℝ) * u =
        2 * Real.pi * ((n : ℝ) + 1) * u - 2 * Real.pi * ((m : ℝ) + 1) * u := by push_cast; ring
    have e2 : 2 * Real.pi * (((n : ℤ) + m + 2 : ℤ) : ℝ) * u =
        2 * Real.pi * ((n : ℝ) + 1) * u + 2 * Real.pi * ((m : ℝ) + 1) * u := by push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add, Real.sin_add, Real.sin_sub]
    ring
  simp_rw [hsum]
  have hnm2 : ((n : ℤ) + m + 2 : ℤ) ≠ 0 := by omega
  have i1 : IntervalIntegrable (fun u => a n / 2 * Real.cos (2 * Real.pi * ((n : ℤ) - m : ℤ) * u))
      volume 0 1 := by apply Continuous.intervalIntegrable; fun_prop
  have i2 : IntervalIntegrable
      (fun u => a n / 2 * Real.cos (2 * Real.pi * ((n : ℤ) + m + 2 : ℤ) * u)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have i3 : IntervalIntegrable
      (fun u => b n / 2 * Real.sin (2 * Real.pi * ((n : ℤ) + m + 2 : ℤ) * u)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have i4 : IntervalIntegrable (fun u => b n / 2 * Real.sin (2 * Real.pi * ((n : ℤ) - m : ℤ) * u))
      volume 0 1 := by apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add ((i1.add i2).add i3) i4,
    intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_cos_two_pi_mul_int hnm2, integral_sin_two_pi_mul_int,
    integral_sin_two_pi_mul_int]
  split_ifs with h
  · subst h; simp
  · have : ((n : ℤ) - m : ℤ) ≠ 0 := by omega
    rw [integral_cos_two_pi_mul_int this]; ring

theorem integral_arcTrig_mul_sin (a b : ℕ → ℝ) (n m : ℕ) :
    ∫ u in (0 : ℝ)..1, arcTrig a b n u * Real.sin (arcFreq m * u) =
      if n = m then b m / 2 else 0 := by
  have hsum : ∀ u, arcTrig a b n u * Real.sin (arcFreq m * u) =
      a n / 2 * Real.sin (2 * Real.pi * ((n : ℤ) + m + 2 : ℤ) * u) -
      a n / 2 * Real.sin (2 * Real.pi * ((n : ℤ) - m : ℤ) * u) +
      b n / 2 * Real.cos (2 * Real.pi * ((n : ℤ) - m : ℤ) * u) -
      b n / 2 * Real.cos (2 * Real.pi * ((n : ℤ) + m + 2 : ℤ) * u) := by
    intro u
    unfold arcTrig arcFreq
    have e1 : 2 * Real.pi * (((n : ℤ) - m : ℤ) : ℝ) * u =
        2 * Real.pi * ((n : ℝ) + 1) * u - 2 * Real.pi * ((m : ℝ) + 1) * u := by push_cast; ring
    have e2 : 2 * Real.pi * (((n : ℤ) + m + 2 : ℤ) : ℝ) * u =
        2 * Real.pi * ((n : ℝ) + 1) * u + 2 * Real.pi * ((m : ℝ) + 1) * u := by push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add, Real.sin_add, Real.sin_sub]
    ring
  simp_rw [hsum]
  have hnm2 : ((n : ℤ) + m + 2 : ℤ) ≠ 0 := by omega
  have i1 : IntervalIntegrable
      (fun u => a n / 2 * Real.sin (2 * Real.pi * ((n : ℤ) + m + 2 : ℤ) * u)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have i2 : IntervalIntegrable (fun u => a n / 2 * Real.sin (2 * Real.pi * ((n : ℤ) - m : ℤ) * u))
      volume 0 1 := by apply Continuous.intervalIntegrable; fun_prop
  have i3 : IntervalIntegrable (fun u => b n / 2 * Real.cos (2 * Real.pi * ((n : ℤ) - m : ℤ) * u))
      volume 0 1 := by apply Continuous.intervalIntegrable; fun_prop
  have i4 : IntervalIntegrable
      (fun u => b n / 2 * Real.cos (2 * Real.pi * ((n : ℤ) + m + 2 : ℤ) * u)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub ((i1.sub i2).add i3) i4,
    intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_cos_two_pi_mul_int hnm2, integral_sin_two_pi_mul_int,
    integral_sin_two_pi_mul_int]
  split_ifs with h
  · subst h; simp
  · have : ((n : ℤ) - m : ℤ) ≠ 0 := by omega
    rw [integral_cos_two_pi_mul_int this]; ring

theorem integral_whittakerArcSum_mul_cos (N : ℕ) (a b : ℕ → ℝ) (y : ℝ) {m : ℕ} (hm : m < N) :
    ∫ u in (0 : ℝ)..1, whittakerArcSum N a b u y * Real.cos (arcFreq m * u) =
      kMoment 0 (arcFreq m * y) * (a m / 2) := by
  unfold whittakerArcSum
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun n _ => by
    unfold arcTrig; apply Continuous.intervalIntegrable; fun_prop]
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul, integral_arcTrig_mul_cos]
  rw [Finset.sum_eq_single m (fun n _ hn => by simp [hn]) (fun h => absurd (Finset.mem_range.mpr hm) h)]
  simp

theorem integral_whittakerArcSum_mul_sin (N : ℕ) (a b : ℕ → ℝ) (y : ℝ) {m : ℕ} (hm : m < N) :
    ∫ u in (0 : ℝ)..1, whittakerArcSum N a b u y * Real.sin (arcFreq m * u) =
      kMoment 0 (arcFreq m * y) * (b m / 2) := by
  unfold whittakerArcSum
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun n _ => by
    unfold arcTrig; apply Continuous.intervalIntegrable; fun_prop]
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul, integral_arcTrig_mul_sin]
  rw [Finset.sum_eq_single m (fun n _ hn => by simp [hn]) (fun h => absurd (Finset.mem_range.mpr hm) h)]
  simp

theorem integral_whittakerArcSum (N : ℕ) (a b : ℕ → ℝ) (y : ℝ) :
    ∫ u in (0 : ℝ)..1, whittakerArcSum N a b u y = 0 := by
  unfold whittakerArcSum
  rw [intervalIntegral.integral_finsetSum fun n _ => by
    unfold arcTrig; apply Continuous.intervalIntegrable; fun_prop]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have hk : ((n : ℤ) + 1 : ℤ) ≠ 0 := by omega
  have e : ∀ u, arcTrig a b n u = a n * Real.cos (2 * Real.pi * ((n : ℤ) + 1 : ℤ) * u) +
      b n * Real.sin (2 * Real.pi * ((n : ℤ) + 1 : ℤ) * u) := by
    intro u; unfold arcTrig arcFreq; push_cast; ring_nf
  simp_rw [e]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_cos_two_pi_mul_int hk, integral_sin_two_pi_mul_int]
  simp

/-- **No nonnegative decaying Whittaker combination on the modular arc.** -/
theorem whittakerArc_coeff_eq_zero (N : ℕ) (a b : ℕ → ℝ)
    (harc : ∀ u y, 0 < y → |u| ≤ 1 / 2 → u ^ 2 + y ^ 2 = 1 → 0 ≤ whittakerArcSum N a b u y)
    {m : ℕ} (hm : m < N) : a m = 0 ∧ b m = 0 := by
  have hnn : ∀ u, 0 ≤ whittakerArcSum N a b u 2 := fun u =>
    nonneg_of_nonneg_on_modularArc (v := whittakerArcSum N a b)
      (vu := fun u y => ∑ n ∈ Finset.range N,
        kMoment 0 (arcFreq n * y) * arcTrigDeriv a b n u)
      (vuu := fun u y => ∑ n ∈ Finset.range N,
        kMoment 0 (arcFreq n * y) * -(arcFreq n ^ 2 * arcTrig a b n u))
      (vy := fun u y => ∑ n ∈ Finset.range N,
        -kMoment 1 (arcFreq n * y) * arcFreq n * arcTrig a b n u)
      (vyy := fun u y => ∑ n ∈ Finset.range N,
        kMoment 2 (arcFreq n * y) * arcFreq n ^ 2 * arcTrig a b n u)
      (fun u y _ => HasDerivAt.fun_sum fun n _ =>
        (hasDerivAt_arcTrig a b n u).const_mul _)
      (fun u y _ => HasDerivAt.fun_sum fun n _ =>
        (hasDerivAt_arcTrigDeriv a b n u).const_mul _)
      (fun u y hy => HasDerivAt.fun_sum fun n _ =>
        (hasDerivAt_kMoment_comp 0 n hy).mul_const _)
      (fun u y hy => HasDerivAt.fun_sum fun n _ => by
        have h := ((hasDerivAt_kMoment_comp 1 n hy).neg.mul_const (arcFreq n)).mul_const
          (arcTrig a b n u)
        refine h.congr_deriv ?_
        ring)
      (fun u y hy => whittakerArcSum_eq N a b hy u)
      (continuousOn_whittakerArcSum N a b) (whittakerArcSum_periodic N a b)
      (whittakerArcSum_decay N a b) harc (by norm_num : (1 : ℝ) ≤ 2)
  have hcont : Continuous fun u => whittakerArcSum N a b u 2 := by
    unfold whittakerArcSum arcTrig; fun_prop
  have hae : ∀ᵐ u, u ∈ Ι (0 : ℝ) 1 → whittakerArcSum N a b u 2 = 0 := by
    have h := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
      (Eventually.of_forall fun u => hnn u) (hcont.intervalIntegrable 0 1)).mp
      (integral_whittakerArcSum N a b 2)
    rw [uIoc_of_le zero_le_one]
    exact (ae_restrict_iff' measurableSet_Ioc).mp h
  have hK := kMoment_zero_pos_of_pos (mul_pos (arcFreq_pos m) two_pos)
  have hcos := integral_whittakerArcSum_mul_cos N a b 2 hm
  have hsin := integral_whittakerArcSum_mul_sin N a b 2 hm
  have hc0 : ∫ u in (0 : ℝ)..1, whittakerArcSum N a b u 2 * Real.cos (arcFreq m * u) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
      (hae.mono fun u hu hmem => by rw [hu hmem, zero_mul])]
    simp
  have hs0 : ∫ u in (0 : ℝ)..1, whittakerArcSum N a b u 2 * Real.sin (arcFreq m * u) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
      (hae.mono fun u hu hmem => by rw [hu hmem, zero_mul])]
    simp
  rw [hc0] at hcos
  rw [hs0] at hsin
  constructor
  · have := hcos.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hK.ne'
    · linarith
  · have := hsin.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hK.ne'
    · linarith

end

end RHTower
