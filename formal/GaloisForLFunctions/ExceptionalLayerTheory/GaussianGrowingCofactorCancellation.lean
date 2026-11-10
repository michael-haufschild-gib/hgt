import GaloisForLFunctions.ExceptionalLayerTheory.GaussianCofactorCorrelationBounds
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianGrowingMomentReduction

/-!
# Rapid cancellation between separated polynomial-sized cofactors

At exponential Gaussian scale and order `floor(κ t / log t)`, every
complete pair with cofactor ratio at least two decays faster than every
fixed height power. The estimate is uniform over polynomial cofactor
cutoffs and the rotating physical damping sector.
-/

open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Absolute pair cancellation with the lattice error still visible. -/
theorem norm_tsum_gaussianHigherPrimeMoment_pair_far_le {r : ℕ} (hr : r ≠ 0)
    {t W : ℝ} (ht : 1 ≤ t) {ε : ℂ} (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (hrot : ε.re * t ≤ |ε.im|)
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (hsep : 2 * k ≤ m)
    (hmW : (m : ℝ) ≤ W) (hkW : (k : ℝ) ≤ W) :
    ‖∑' d : ℕ, gaussianHigherPrimeMomentWeight r (1 / 2) t ε (m * (d + 1)) *
      (starRingEnd ℂ) (gaussianHigherPrimeMomentWeight r (1 / 2) t ε (k * (d + 1)))‖ ≤
      (4 * (r : ℝ) / t) ^ (2 * r) +
        (4 * (r : ℝ)) ^ (2 * r) * (2048 * (r : ℝ) ^ 3 * ε.re * t ^ 2 * W ^ 2) ^ r := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsepR : 2 * (k : ℝ) ≤ m := by exact_mod_cast hsep
  have hbase := norm_tsum_gaussianHigherPrimeMoment_pair_le hr ht hε hsector hm hk hmW hkW
  rw [mul_add, ← norm_gaussianCofactorCorrelationMain r t hε
    (zero_lt_one.trans_le hmR) (zero_lt_one.trans_le hkR)] at hbase
  exact hbase.trans (add_le_add
    (norm_gaussianCofactorCorrelationMain_le_order_ratio hr ht hε hmR hkR hsepR hrot)
    (mul_le_mul_of_nonneg_right (gaussianCofactorCorrelationScale_le_order hr ht hε hsector hmR hkR)
      (by positivity)))

private theorem eventually_polynomial_absorbed {a : ℝ} (ha : 0 < a) (C : ℝ) (n : ℕ) :
    ∀ᶠ t : ℝ in atTop, C * t ^ n * Real.exp (-a * t) ≤ 1 := by
  have hp : Tendsto (fun t : ℝ => t ^ n * Real.exp (-a * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) a ha
  have hh := hp.const_mul C
  simp only [mul_zero] at hh
  exact (hh.eventually_lt_const zero_lt_one).mono fun t ht => by
    simpa only [mul_assoc] using ht.le

private theorem eventually_order_ratio_le {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    ∀ᶠ t : ℝ in atTop,
      (4 * (gaussianGrowingMomentOrder κ t : ℝ) / t) ^ (2 * gaussianGrowingMomentOrder κ t) ≤
        1 / t ^ N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Tendsto (fun t : ℝ => (Real.log t) ^ 2 / t) atTop (𝓝 0) := by
    simpa only [one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 2 0 1 one_ne_zero
  have hsmall := hlog.const_mul (N : ℝ)
  simp only [mul_zero] at hsmall
  have hlarge := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (8 * κ)))
  filter_upwards [eventually_gaussianGrowingMomentOrder_bounds hκ,
    hsmall.eventually_lt_const (mul_pos hκ hlog2), hlarge,
    eventually_ge_atTop (1 : ℝ)] with t hr hs hl ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hl0 : 0 < Real.log t := zero_lt_one.trans_le ((le_max_left _ _).trans hl)
  have hlκ : 8 * κ ≤ Real.log t := (le_max_right _ _).trans hl
  have hrsmall : 8 * (gaussianGrowingMomentOrder κ t : ℝ) ≤ t := by
    apply (mul_le_mul_left hκ).mp
    have hh := mul_le_mul_of_nonneg_left hlκ (Nat.cast_nonneg (gaussianGrowingMomentOrder κ t))
    nlinarith only [hh, hr.2.2.2]
  have hratio : 4 * (gaussianGrowingMomentOrder κ t : ℝ) / t ≤ 1 / 2 :=
    (div_le_iff₀ ht0).mpr (by linarith only [hrsmall])
  have hs' : (N : ℝ) * (Real.log t) ^ 2 ≤ κ * Real.log 2 * t := by
    apply (div_le_iff₀ ht0).mp
    simpa only [mul_div_assoc] using hs.le
  have hlogbound : (N : ℝ) * Real.log t ≤
      2 * (gaussianGrowingMomentOrder κ t : ℝ) * Real.log 2 := by
    apply (mul_le_mul_right hl0).mp
    have hh := mul_le_mul_of_nonneg_right hr.2.2.1 hlog2.le
    nlinarith only [hh, hs']
  calc
    _ ≤ (1 / 2 : ℝ) ^ (2 * gaussianGrowingMomentOrder κ t) :=
      pow_le_pow_left₀ (by positivity) hratio _
    _ = Real.exp (-2 * (gaussianGrowingMomentOrder κ t : ℝ) * Real.log 2) := by
      rw [show -2 * (gaussianGrowingMomentOrder κ t : ℝ) * Real.log 2 =
        ((2 * gaussianGrowingMomentOrder κ t : ℕ) : ℝ) * (-Real.log 2) by push_cast; ring,
        Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rfl
    _ ≤ Real.exp (-(N : ℝ) * Real.log t) :=
      Real.exp_le_exp.mpr (by linarith only [hlogbound])
    _ = _ := by
      rw [show -(N : ℝ) * Real.log t = -((N : ℝ) * Real.log t) by ring,
        Real.exp_neg, Real.exp_nat_mul, Real.exp_log ht0]
      rfl

private theorem lattice_cost_le_exp {r J : ℕ} (hr : r ≠ 0) {a t α : ℝ}
    (ha : 0 < a) (ht : 1 ≤ t) (hα : 0 < α) (hrt : (r : ℝ) ≤ t)
    (hscale : α * Real.exp (a * t) ^ 2 = 2)
    (hsmall : 589824 * t ^ (2 * J + 13) * Real.exp (-a * t) ≤ 1) :
    (4 * (r : ℝ)) ^ (2 * r) *
      (2048 * (r : ℝ) ^ 3 * α * t ^ 2 * (3 * t ^ (J + 3)) ^ 2) ^ r ≤
      Real.exp (-a * t) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hαexp : α = 2 * Real.exp (-2 * a * t) := by
    rw [show α = 2 / Real.exp (a * t) ^ 2 from
      (eq_div_iff (pow_ne_zero 2 (Real.exp_pos _).ne')).mpr hscale]
    rw [show -2 * a * t = -(a * t + a * t) by ring,
      Real.exp_neg, Real.exp_add, pow_two, div_eq_mul_inv]
  have htPow : t ^ 5 * t ^ 2 * (t ^ (J + 3)) ^ 2 = t ^ (2 * J + 13) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  have hbase : 32768 * (r : ℝ) ^ 5 * α * t ^ 2 * (3 * t ^ (J + 3)) ^ 2 ≤
      Real.exp (-a * t) := by
    calc
      _ ≤ 32768 * t ^ 5 * α * t ^ 2 * (3 * t ^ (J + 3)) ^ 2 := by gcongr
      _ = 589824 * t ^ (2 * J + 13) * Real.exp (-2 * a * t) := by
        rw [hαexp]
        calc
          _ = 589824 * (t ^ 5 * t ^ 2 * (t ^ (J + 3)) ^ 2) * Real.exp (-2 * a * t) := by ring
          _ = _ := by rw [htPow]
      _ = (589824 * t ^ (2 * J + 13) * Real.exp (-a * t)) * Real.exp (-a * t) := by
        rw [show Real.exp (-2 * a * t) = Real.exp (-a * t) * Real.exp (-a * t) by
          rw [← Real.exp_add]
          congr 1
          ring]
        ring
      _ ≤ 1 * Real.exp (-a * t) := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
      _ = _ := one_mul _
  have he1 : Real.exp (-a * t) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
      (show -a * t ≤ 0 by nlinarith only [mul_pos ha ht0])
  have hpow : Real.exp (-a * t) ^ r ≤ Real.exp (-a * t) := by
    calc
      _ = Real.exp (-a * t) ^ (r - 1) * Real.exp (-a * t) := by
        rw [← pow_succ]
        congr 1
        omega
      _ ≤ 1 * Real.exp (-a * t) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (Real.exp_pos _).le he1) (Real.exp_pos _).le
      _ = _ := one_mul _
  calc
    _ = (32768 * (r : ℝ) ^ 5 * α * t ^ 2 * (3 * t ^ (J + 3)) ^ 2) ^ r := by
      rw [pow_mul, ← mul_pow]
      congr 1
      ring
    _ ≤ Real.exp (-a * t) ^ r := pow_le_pow_left₀ (by positivity) hbase r
    _ ≤ _ := hpow

/-- Every fixed inverse height power is gained on separated cofactor pairs,
uniformly up to polynomial cutoffs and over the rotating physical sector. -/
theorem eventually_gaussianGrowingCofactorPair_rapid_decay {a κ : ℝ}
    (ha : 0 < a) (hκ : 0 < κ) (J N : ℕ) :
    ∀ᶠ t : ℝ in atTop, ∀ ε : ℂ, 0 < ε.re → ‖ε‖ ≤ 4 * ε.re * t →
      ε.re * Real.exp (a * t) ^ 2 = 2 → ε.re * t ≤ |ε.im| →
      ∀ m k : ℕ, 0 < m → 0 < k → 2 * k ≤ m →
      (m : ℝ) ≤ 3 * t ^ (J + 3) → (k : ℝ) ≤ 3 * t ^ (J + 3) →
        ‖∑' d : ℕ,
          gaussianHigherPrimeMomentWeight (gaussianGrowingMomentOrder κ t) (1 / 2) t ε (m * (d + 1)) *
            (starRingEnd ℂ) (gaussianHigherPrimeMomentWeight (gaussianGrowingMomentOrder κ t)
              (1 / 2) t ε (k * (d + 1)))‖ ≤ 2 / t ^ N := by
  filter_upwards [eventually_gaussianGrowingMomentOrder_bounds hκ,
    eventually_order_ratio_le hκ N, eventually_polynomial_absorbed ha 589824 (2 * J + 13),
    eventually_polynomial_absorbed ha 1 N, eventually_ge_atTop (1 : ℝ)]
    with t hr hratio hpoly hpower ht ε hε hsector hscale hrot m k hm hk hsep hmW hkW
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hfar := norm_tsum_gaussianHigherPrimeMoment_pair_far_le hr.1 ht hε hsector hrot hm hk hsep hmW hkW
  have hcost := lattice_cost_le_exp hr.1 ha ht hε hr.2.1 hscale hpoly
  have hexp : Real.exp (-a * t) ≤ 1 / t ^ N := by
    apply (le_div_iff₀ (pow_pos ht0 N)).mpr
    simpa only [one_mul, mul_comm] using hpower
  nlinarith only [hfar, hratio, hcost, hexp]

#print axioms norm_tsum_gaussianHigherPrimeMoment_pair_far_le
#print axioms eventually_gaussianGrowingCofactorPair_rapid_decay

end GaloisForLFunctions.ExceptionalLayerTheory
