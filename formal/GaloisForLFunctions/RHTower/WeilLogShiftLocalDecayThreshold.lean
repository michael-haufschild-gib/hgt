import GaloisForLFunctions.RHTower.WeilLogShiftSubexponentialDomain

/-!
# The local exponential threshold and probe location

The paired log-kernel has critical exponential rate `2π exp(-|y|)`, equal to
`2π/m` at `y = log m`. Subcritical damping/growth guarantees convergence;
convergence forces every supercritical damping/growth bound. Pure exponential
weights above the rate diverge. The critical endpoint is left open.
-/

open Filter Topology Zeta23 Real

noncomputable section

namespace RHTower

open WeilExcess

/-- The critical exponential rate of the paired kernel at a real shift. -/
def logKernelCriticalRate (y : ℝ) : ℝ := 2 * π * exp (-|y|)

theorem logKernelCriticalRate_pos (y : ℝ) : 0 < logKernelCriticalRate y := by
  unfold logKernelCriticalRate
  positivity

/-- Integer-log probe location and critical damping are inversely proportional. -/
theorem logKernelCriticalRate_log_nat {m : ℕ} (hm : 1 ≤ m) :
    logKernelCriticalRate (log m) = 2 * π / m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [logKernelCriticalRate, abs_of_nonneg (log_natCast_nonneg m), exp_neg,
    exp_log hmpos, div_eq_mul_inv]

private theorem criticalRate_mul_exp_abs (y : ℝ) :
    logKernelCriticalRate y * exp |y| = 2 * π := by
  rw [logKernelCriticalRate, mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]

/-- Every positive rate below the critical rate gives a full paired-kernel
upper envelope on positive integer indices. -/
theorem exists_paired_logKernel_upper_of_lt_rate {y a : ℝ}
    (ha0 : 0 < a) (ha : a < logKernelCriticalRate y) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      riemannAutocorr (y + log n) + riemannAutocorr (y - log n) ≤ C * exp (-(a * n)) := by
  let c := a * exp |y| / 2
  have hc0 : 0 < c := by dsimp only [c]; positivity
  have hcπ : c < π := by
    have h := mul_lt_mul_of_pos_right ha (exp_pos |y|)
    rw [criticalRate_mul_exp_abs] at h
    dsimp only [c]
    linarith only [h]
  have hscale : 2 * c * exp (-|y|) = a := by
    dsimp only [c]
    calc 2 * (a * exp |y| / 2) * exp (-|y|) = a * (exp |y| * exp (-|y|)) := by ring
      _ = a := by rw [← exp_add, add_neg_cancel, exp_zero, mul_one]
  obtain ⟨C, hC0, hC⟩ := ExposingRayTail.autocorr_upper hc0 hcπ
  refine ⟨2 * C, by positivity, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbound (z : ℝ) (hz : log n - |y| ≤ |z|) :
      riemannAutocorr z ≤ C * exp (-(a * n)) := by
    have he := exp_le_exp.mpr hz
    rw [sub_eq_add_neg, exp_add, exp_log hnpos] at he
    have hrate : a * n ≤ 2 * c * exp |z| := by
      calc a * (n : ℝ) = (2 * c * exp (-|y|)) * n := by rw [hscale]
        _ = (2 * c) * ((n : ℝ) * exp (-|y|)) := by ring
        _ ≤ (2 * c) * exp |z| := mul_le_mul_of_nonneg_left he (by positivity)
    have hk := hC z
    change riemannAutocorr z ≤ _ at hk
    exact hk.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hrate)) hC0.le)
  have hp := hbound (y + log n) (by
    linarith only [neg_le_abs y, le_abs_self (y + log n)])
  have hm := hbound (y - log n) (by
    linarith only [le_abs_self y, neg_le_abs (y - log n)])
  linarith only [hp, hm]

/-- Every rate above the critical rate gives a positive lower envelope on the
paired-kernel tail at that same shift. -/
theorem exists_paired_logKernel_lower_of_rate_lt {y b : ℝ}
    (hb : logKernelCriticalRate y < b) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      D * exp (-(b * n)) ≤
        riemannAutocorr (y + log n) + riemannAutocorr (y - log n) := by
  let B := b * exp |y|
  have hB : 2 * π < B := by
    have h := mul_lt_mul_of_pos_right hb (exp_pos |y|)
    rw [criticalRate_mul_exp_abs] at h
    exact h
  have hscale : B * exp (-|y|) = b := by
    dsimp only [B]
    rw [mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one]
  obtain ⟨D, Y, hD, hbound⟩ := ExposingRayTail.autocorr_lower hB
  refine ⟨D, hD, eventually_atTop.mpr ⟨⌊exp (Y + |y|)⌋₊ + 1, fun n hn => ?_⟩⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (⌊exp (Y + |y|)⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hlog : Y + |y| < log n := (lt_log_iff_exp_lt hnpos).mpr
    ((Nat.lt_floor_add_one _).trans_le hnR)
  have hk := hbound (log n - |y|) (by linarith only [hlog])
  change D * exp (-(B * exp (log n - |y|))) ≤ riemannAutocorr (log n - |y|) at hk
  have heq : B * exp (log n - |y|) = b * n := by
    rw [sub_eq_add_neg, exp_add, exp_log hnpos]
    calc B * ((n : ℝ) * exp (-|y|)) = (B * exp (-|y|)) * n := by ring
      _ = b * n := by rw [hscale]
  rw [heq] at hk
  have hpair : riemannAutocorr (log n - |y|) ≤
      riemannAutocorr (y + log n) + riemannAutocorr (y - log n) := by
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy, show log n - y = -(y - log n) by ring, riemannAutocorr_neg]
      linarith only [riemannAutocorr_nonneg (y + log n)]
    · rw [abs_of_neg (lt_of_not_ge hy), sub_neg_eq_add, add_comm (log n) y]
      linarith only [riemannAutocorr_nonneg (y - log n)]
  exact hk.trans hpair

private theorem summable_damping_mono {v : ℕ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hs : Summable fun n => |v n| * exp (-(a * n))) :
    Summable fun n => |v n| * exp (-(b * n)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (exp_pos _).le) (fun n => ?_) hs
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply exp_le_exp.mpr
  exact neg_le_neg (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n))

/-- Summability at any damping rate below the local critical rate suffices
for the potential. The supplied damping rate need not be positive. -/
theorem summable_kernelPotential_of_damping_lt_rate {v : ℕ → ℝ} {y a : ℝ}
    (ha : a < logKernelCriticalRate y)
    (hs : Summable fun n => |v n| * exp (-(a * n))) :
    Summable fun n => v n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n)) := by
  let a' := max a (logKernelCriticalRate y / 2)
  have hr := logKernelCriticalRate_pos y
  have ha'0 : 0 < a' := (show 0 < logKernelCriticalRate y / 2 by positivity).trans_le
    (le_max_right _ _)
  have ha'r : a' < logKernelCriticalRate y := max_lt ha (by linarith only [hr])
  have hs' := summable_damping_mono (show a ≤ a' from le_max_left _ _) hs
  obtain ⟨C, hC, hupper⟩ := exists_paired_logKernel_upper_of_lt_rate ha'0 ha'r
  refine (hs'.mul_left C).of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have h := mul_le_mul_of_nonneg_left (hupper n hn) (abs_nonneg (v n))
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (add_nonneg (riemannAutocorr_nonneg (y + log n))
      (riemannAutocorr_nonneg (y - log n)))]
  nlinarith only [h]

/-- Potential convergence forces summability at every damping rate strictly
above the local critical rate, for arbitrary signed weights. -/
theorem summable_damping_of_kernelPotential_of_rate_lt {v : ℕ → ℝ} {y b : ℝ}
    (hb : logKernelCriticalRate y < b)
    (hs : Summable fun n => v n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n))) :
    Summable fun n => |v n| * exp (-(b * n)) := by
  obtain ⟨D, hD, hlower⟩ := exists_paired_logKernel_lower_of_rate_lt hb
  refine (hs.norm.mul_left (1 / D)).of_norm_bounded_eventually_nat ?_
  filter_upwards [hlower] with n hn
  have h := mul_le_mul_of_nonneg_left hn (abs_nonneg (v n))
  simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (exp_pos (-(b * n))),
    abs_of_nonneg (add_nonneg (riemannAutocorr_nonneg (y + log n))
      (riemannAutocorr_nonneg (y - log n)))]
  calc
    |v n| * exp (-(b * n)) ≤
        (|v n| * (riemannAutocorr (y + log n) + riemannAutocorr (y - log n))) / D :=
      (le_div_iff₀ hD).mpr (by nlinarith only [h])
    _ = _ := by ring

/-- Any pointwise exponential growth bound strictly below the critical rate
gives convergence at the specified shift. -/
theorem summable_kernelPotential_of_exponential_growth {v : ℕ → ℝ} {y ρ C : ℝ}
    (hρ : ρ < logKernelCriticalRate y) (hbound : ∀ n : ℕ, |v n| ≤ C * exp (ρ * n)) :
    Summable fun n => v n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n)) := by
  let a := (ρ + logKernelCriticalRate y) / 2
  have hρa : ρ < a := by dsimp only [a]; linarith only [hρ]
  have har : a < logKernelCriticalRate y := by dsimp only [a]; linarith only [hρ]
  apply summable_kernelPotential_of_damping_lt_rate har
  have hgeo : Summable fun n : ℕ => exp ((n : ℝ) * (ρ - a)) :=
    summable_exp_nat_mul_iff.mpr (by linarith only [hρa])
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (exp_pos _).le) (fun n => ?_) (hgeo.mul_left C)
  calc
    |v n| * exp (-(a * n)) ≤ (C * exp (ρ * n)) * exp (-(a * n)) :=
      mul_le_mul_of_nonneg_right (hbound n) (exp_pos _).le
    _ = C * exp ((n : ℝ) * (ρ - a)) := by
      rw [mul_assoc, ← exp_add, show ρ * (n : ℝ) + -(a * n) = (n : ℝ) * (ρ - a) by ring]

/-- Convergence at a single shift bounds coefficient growth at every rate
strictly above its critical rate. -/
theorem exponential_bound_of_summable_kernelPotential {v : ℕ → ℝ} {y b : ℝ}
    (hb : logKernelCriticalRate y < b)
    (hs : Summable fun n => v n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |v n| ≤ C * exp (b * n) := by
  have hd := summable_damping_of_kernelPotential_of_rate_lt hb hs
  let C := ∑' n, |v n| * exp (-(b * n))
  refine ⟨C, tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (exp_pos _).le), fun n => ?_⟩
  have ht := hd.le_tsum n (fun j _ => mul_nonneg (abs_nonneg (v j)) (exp_pos (-(b * j))).le)
  have heq : exp (-(b * n)) * exp (b * n) = 1 := by rw [← exp_add]; simp
  calc
    |v n| = (|v n| * exp (-(b * n))) * exp (b * n) := by rw [mul_assoc, heq, mul_one]
    _ ≤ C * exp (b * n) := mul_le_mul_of_nonneg_right ht (exp_pos _).le

/-- Pure exponential weights strictly above the critical rate diverge.
Together with the subcritical growth theorem this locates the sharp boundary;
no assertion is made at equality. -/
theorem not_summable_exponential_kernelPotential_of_rate_lt {y ρ : ℝ}
    (hρ : logKernelCriticalRate y < ρ) :
    ¬ Summable fun n : ℕ => exp (ρ * n) *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n)) := by
  intro hs
  let b := (logKernelCriticalRate y + ρ) / 2
  have hrb : logKernelCriticalRate y < b := by dsimp only [b]; linarith only [hρ]
  have hbρ : b < ρ := by dsimp only [b]; linarith only [hρ]
  have hd := summable_damping_of_kernelPotential_of_rate_lt hrb hs
  have hg : Summable fun n : ℕ => exp ((n : ℝ) * (ρ - b)) := by
    refine hd.congr fun n => ?_
    rw [abs_of_pos (exp_pos _), ← exp_add]
    congr 1
    ring
  have hneg := summable_exp_nat_mul_iff.mp hg
  linarith only [hbρ, hneg]

/-- Below the inverse probe-location rate, a normalized-deviation growth bound
gives the exact finite probe limit without a finite-excess assumption. -/
theorem tendsto_logShift_probe_of_subcritical_exponential_growth {lam : ℕ → ℝ}
    {m : ℕ} (hm : 1 ≤ m) {ρ C : ℝ} (hρ : ρ < 2 * π / m)
    (hbound : ∀ n : ℕ, |weilDeviation lam n| ≤ C * exp (ρ * n)) :
    Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference L (log m))
      (logShiftRiemannDifference L (log m)))).re) atTop
      (𝓝 (2 * (deviationPotential lam (log m) - deviationPotential lam 0))) := by
  have hle : 2 * π / (m : ℝ) ≤ 2 * π :=
    div_le_self (by positivity) (by exact_mod_cast hm)
  have hρ0 : ρ < logKernelCriticalRate 0 := by
    simpa only [logKernelCriticalRate, abs_zero, neg_zero, exp_zero, mul_one] using hρ.trans_le hle
  have hρm : ρ < logKernelCriticalRate (log m) := by
    rw [logKernelCriticalRate_log_nat hm]
    exact hρ
  exact tendsto_logShift_probe_of_summable_potential m
    (summable_kernelPotential_of_exponential_growth hρ0 hbound)
    (summable_kernelPotential_of_exponential_growth hρm hbound)

/-- With finite excess, a lower bound at one sufficiently large fixed probe
forces coefficient-growth bounds at every rate above `2π/m`. -/
theorem exponential_bound_of_logShift_probe_lower_bound {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) {m : ℕ} (hm : 4 ≤ log m)
    (hbounded : ∃ d : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      d ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (log m))
        (logShiftRiemannDifference k (log m)))).re)
    {b : ℝ} (hb : 2 * π / m < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |weilDeviation lam n| ≤ C * exp (b * n) := by
  have hm1 : 1 ≤ m := by
    by_contra h
    have hz : m = 0 := by omega
    subst m
    norm_num at hm
  have horigin := summable_deficit_origin_of_probe_bounded_below hexc hm hbounded
  have hs := summable_potential_of_probe_bounded_below hexc horigin m hbounded
  apply exponential_bound_of_summable_kernelPotential (y := log m) _ hs
  rwa [logKernelCriticalRate_log_nat hm1]

end RHTower
