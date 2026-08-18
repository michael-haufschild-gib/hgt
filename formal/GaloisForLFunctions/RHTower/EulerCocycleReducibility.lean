import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

/-!
# The Euler cocycle is a bounded coboundary exactly on and above the critical line

Over the Kronecker flow on `𝕋^∞` the additive Euler cocycle is solved mode by mode: the observable
`g_σ` is supported on the axis modes `k·δ_p`, and the cohomological equation `D h = g_σ` has the
unique solution with Fourier coefficients

```text
ĥ(k δ_p) = i · p^{-kσ} / (k² log p),      |ĥ(k δ_p)|² = p^{-2kσ} / (k⁴ (log p)²).
```

By Parseval `h ∈ L²` is exactly summability of those squares, so the whole dynamical statement is
the convergence dichotomy of an explicit prime series — which is what this file proves.

* `summable_observableCoeffSq_iff` — the **observable** threshold: `Σ_p p^{-2σ}` converges iff
  `σ > 1/2` (strict);
* `summable_transferCoeffSq_iff` — the **transfer function** threshold: `Σ_p p^{-2σ}/(log p)²`
  converges iff `σ ≥ 1/2` (inclusive).  This is the card's named Tier-A target;
* `summable_transferModeSq_iff` — **Theorem 19a** in full: the complete transfer norm
  `Σ_p Σ_{k ≥ 1} p^{-2kσ}/(k⁴(log p)²)` converges iff `σ ≥ 1/2`.

Together the first two are the *sharp pinch* at `σ = 1/2`: there the observable has just left `L²`
(Selberg's `log log` fluctuations) while the transfer function is still in `L²`, so the cocycle is
still bounded.  The dividing `(log p)²` is the square of the mode frequency — the flow's generator
doing the smoothing.

The critical-line case reuses the corpus series `RHTower.burnolSummable_prime_one_div_mul_log_sq`
and Euler's divergence `RHTower.burnolNotSummable_prime_one_div`.
-/

noncomputable section

open Filter Topology Asymptotics

namespace RHTower.EulerCocycle

open RHTower

/-- The squared Fourier coefficient of the transfer function on the axis mode `δ_p`. -/
def transferCoeffSq (σ : ℝ) (p : Nat.Primes) : ℝ :=
  ((p : ℝ)) ^ (-(2 * σ)) / (Real.log p) ^ 2

/-- The squared Fourier coefficient of the Euler observable on the axis mode `δ_p`. -/
def observableCoeffSq (σ : ℝ) (p : Nat.Primes) : ℝ := ((p : ℝ)) ^ (-(2 * σ))

theorem two_le_prime (p : Nat.Primes) : 2 ≤ (p : ℕ) := p.2.two_le

theorem one_lt_prime_real (p : Nat.Primes) : (1 : ℝ) < (p : ℕ) := by
  exact_mod_cast lt_of_lt_of_le (by norm_num) (two_le_prime p)

theorem log_prime_pos (p : Nat.Primes) : 0 < Real.log (p : ℕ) := Real.log_pos (one_lt_prime_real p)

theorem tendsto_prime_cofinite_atTop :
    Tendsto (fun p : Nat.Primes => ((p : ℕ) : ℝ)) cofinite atTop := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := by
    intro a b hab
    exact Subtype.ext hab
  have h1 : Tendsto (fun p : Nat.Primes => (p : ℕ)) cofinite cofinite :=
    hinj.tendsto_cofinite
  rw [Nat.cofinite_eq_atTop] at h1
  exact tendsto_natCast_atTop_atTop.comp h1

/-- **The observable threshold.**  The Euler observable is square-summable exactly above the
critical line. -/
theorem summable_observableCoeffSq_iff (σ : ℝ) :
    Summable (observableCoeffSq σ) ↔ 1 / 2 < σ := by
  have hfun : observableCoeffSq σ = (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * σ))) := rfl
  rw [hfun, Nat.Primes.summable_rpow]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **The transfer-function threshold.**  The Euler transfer function is square-summable exactly on
and above the critical line — the threshold is inclusive. -/
theorem summable_transferCoeffSq_iff (σ : ℝ) :
    Summable (transferCoeffSq σ) ↔ 1 / 2 ≤ σ := by
  constructor
  · intro hsum
    by_contra hcon
    rw [not_le] at hcon
    -- below the line the terms dominate `1/p`
    have hdelta : 0 < 1 - 2 * σ := by linarith
    have hlog : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ 2 ≤ x ^ (1 - 2 * σ) := by
      have h1 : (fun r : ℝ => Real.log r) =o[atTop] fun r : ℝ => r ^ ((1 - 2 * σ) / 2) :=
        isLittleO_log_rpow_atTop (by linarith)
      have h2 : (fun r : ℝ => (Real.log r) ^ 2) =o[atTop] fun r : ℝ => r ^ (1 - 2 * σ) := by
        have hmul := h1.mul h1
        refine hmul.congr' ?_ ?_
        · filter_upwards with r
          ring
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
          rw [← Real.rpow_add hr]
          congr 1
          ring
      have h3 := h2.bound (by norm_num : (0 : ℝ) < 1)
      filter_upwards [h3, eventually_gt_atTop (0 : ℝ)] with r hr hrpos
      have hrp : (0 : ℝ) < r ^ (1 - 2 * σ) := Real.rpow_pos_of_pos hrpos _
      calc (Real.log r) ^ 2 ≤ ‖(Real.log r) ^ 2‖ := le_abs_self _
        _ ≤ 1 * ‖r ^ (1 - 2 * σ)‖ := hr
        _ = r ^ (1 - 2 * σ) := by
            rw [one_mul, Real.norm_eq_abs, abs_of_pos hrp]
    have hcomp : ∀ᶠ p : Nat.Primes in cofinite,
        1 / ((p : ℕ) : ℝ) ≤ transferCoeffSq σ p := by
      filter_upwards [tendsto_prime_cofinite_atTop.eventually hlog] with p hp
      have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
        have := one_lt_prime_real p
        linarith
      have hlogpos : 0 < Real.log ((p : ℕ) : ℝ) := log_prime_pos p
      have hrw : ((p : ℕ) : ℝ) ^ (-(2 * σ)) * ((p : ℕ) : ℝ)
          = ((p : ℕ) : ℝ) ^ (1 - 2 * σ) := by
        rw [show (1 : ℝ) - 2 * σ = -(2 * σ) + 1 by ring, Real.rpow_add hppos, Real.rpow_one]
      rw [transferCoeffSq, div_le_div_iff₀ hppos (by positivity), one_mul, hrw]
      exact hp
    have hbigO : (fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ)) =O[cofinite] (transferCoeffSq σ) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [hcomp] with p hp
      have hnn : (0 : ℝ) ≤ 1 / ((p : ℕ) : ℝ) := by positivity
      have hnn2 : (0 : ℝ) ≤ transferCoeffSq σ p := by
        rw [transferCoeffSq]
        have hlogpos : 0 < Real.log ((p : ℕ) : ℝ) := log_prime_pos p
        positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg hnn2, one_mul]
      exact hp
    exact burnolNotSummable_prime_one_div (summable_of_isBigO hsum hbigO)
  · intro hσ
    rcases eq_or_lt_of_le hσ with hhalf | hgt
    · -- the critical case is the corpus series
      refine burnolSummable_prime_one_div_mul_log_sq.congr (fun p => ?_)
      rw [transferCoeffSq, ← hhalf]
      have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
        have := one_lt_prime_real p
        linarith
      rw [show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
      field_simp
    · -- above the line the logarithm only helps
      have hbase : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * σ))) := by
        rw [Nat.Primes.summable_rpow]
        linarith
      have hscaled : Summable (fun p : Nat.Primes =>
          ((Real.log 2) ^ 2)⁻¹ * ((p : ℕ) : ℝ) ^ (-(2 * σ))) := hbase.mul_left _
      refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hscaled
      · rw [transferCoeffSq]
        have hlogpos : 0 < Real.log ((p : ℕ) : ℝ) := log_prime_pos p
        positivity
      · rw [transferCoeffSq]
        have hlogpos : 0 < Real.log ((p : ℕ) : ℝ) := log_prime_pos p
        have hlog2 : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast two_le_prime p)
        have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have hsq : (Real.log 2) ^ 2 ≤ (Real.log ((p : ℕ) : ℝ)) ^ 2 := by nlinarith
        have hnum : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg (by positivity) _
        rw [inv_mul_eq_div]
        gcongr

/-! ## The full transfer-function norm -/

/-- The squared Fourier coefficient of the transfer function on the axis mode `(k+1)·δ_p`. -/
def transferModeSq (σ : ℝ) (q : Nat.Primes × ℕ) : ℝ :=
  ((q.1 : ℕ) : ℝ) ^ (-(2 * ((q.2 : ℝ) + 1) * σ))
    / ((((q.2 : ℝ) + 1) ^ 4) * (Real.log ((q.1 : ℕ) : ℝ)) ^ 2)

theorem transferModeSq_nonneg (σ : ℝ) (q : Nat.Primes × ℕ) : 0 ≤ transferModeSq σ q := by
  rw [transferModeSq]
  have hlogpos : 0 < Real.log ((q.1 : ℕ) : ℝ) := log_prime_pos q.1
  positivity

theorem transferModeSq_zero (σ : ℝ) (p : Nat.Primes) :
    transferModeSq σ (p, 0) = transferCoeffSq σ p := by
  rw [transferModeSq, transferCoeffSq]
  norm_num

/-- The geometric majorant of one prime block. -/
def transferMajorant (p : Nat.Primes) (k : ℕ) : ℝ :=
  ((Real.log ((p : ℕ) : ℝ)) ^ 2)⁻¹ * (1 / ((p : ℕ) : ℝ)) ^ (k + 1)

theorem transferModeSq_le_majorant {σ : ℝ} (hσ : 1 / 2 ≤ σ) (p : Nat.Primes) (k : ℕ) :
    transferModeSq σ (p, k) ≤ transferMajorant p k := by
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := le_of_lt (one_lt_prime_real p)
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hlogpos : 0 < Real.log ((p : ℕ) : ℝ) := log_prime_pos p
  have hexp : -(2 * ((k : ℝ) + 1) * σ) ≤ -((k : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hpow : ((p : ℕ) : ℝ) ^ (-(2 * ((k : ℝ) + 1) * σ)) ≤ ((p : ℕ) : ℝ) ^ (-((k : ℝ) + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 hexp
  have hmaj : ((p : ℕ) : ℝ) ^ (-((k : ℝ) + 1)) = (1 / ((p : ℕ) : ℝ)) ^ (k + 1) := by
    rw [one_div, ← Real.rpow_natCast (((p : ℕ) : ℝ))⁻¹ (k + 1), ← Real.rpow_neg_one,
      ← Real.rpow_mul (le_of_lt hppos)]
    congr 1
    push_cast
    ring
  rw [transferModeSq, transferMajorant, ← hmaj, inv_mul_eq_div]
  have hk4 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    exact one_le_pow₀ hk1
  have hnum : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-(2 * ((k : ℝ) + 1) * σ)) :=
    Real.rpow_nonneg (le_of_lt hppos) _
  calc ((p : ℕ) : ℝ) ^ (-(2 * ((k : ℝ) + 1) * σ))
        / ((((k : ℝ) + 1) ^ 4) * (Real.log ((p : ℕ) : ℝ)) ^ 2)
      ≤ ((p : ℕ) : ℝ) ^ (-(2 * ((k : ℝ) + 1) * σ)) / (1 * (Real.log ((p : ℕ) : ℝ)) ^ 2) := by
        gcongr
    _ = ((p : ℕ) : ℝ) ^ (-(2 * ((k : ℝ) + 1) * σ)) / (Real.log ((p : ℕ) : ℝ)) ^ 2 := by
        rw [one_mul]
    _ ≤ ((p : ℕ) : ℝ) ^ (-((k : ℝ) + 1)) / (Real.log ((p : ℕ) : ℝ)) ^ 2 := by
        gcongr

theorem summable_transferMajorant (p : Nat.Primes) : Summable (transferMajorant p) := by
  have hr : ‖(1 / ((p : ℕ) : ℝ))‖ < 1 := by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast two_le_prime p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_lt_one (by linarith)]
    linarith
  have hgeom : Summable (fun k : ℕ => (1 / ((p : ℕ) : ℝ)) ^ (k + 1)) := by
    have := (summable_geometric_of_norm_lt_one hr).comp_injective (add_left_injective 1)
    exact this.congr (fun k => by simp)
  exact hgeom.mul_left _

theorem tsum_transferMajorant_le (p : Nat.Primes) :
    (∑' k : ℕ, transferMajorant p k) ≤ 2 / (((p : ℕ) : ℝ) * (Real.log ((p : ℕ) : ℝ)) ^ 2) := by
  have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast two_le_prime p
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hlogpos : 0 < Real.log ((p : ℕ) : ℝ) := log_prime_pos p
  have hr : ‖(1 / ((p : ℕ) : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one hppos]
    linarith
  have hsum : (∑' k : ℕ, (1 / ((p : ℕ) : ℝ)) ^ (k + 1))
      = (1 / ((p : ℕ) : ℝ)) * (1 - 1 / ((p : ℕ) : ℝ))⁻¹ := by
    have hg : (∑' k : ℕ, (1 / ((p : ℕ) : ℝ)) ^ k) = (1 - 1 / ((p : ℕ) : ℝ))⁻¹ :=
      tsum_geometric_of_norm_lt_one hr
    rw [← hg, ← tsum_mul_left]
    exact tsum_congr (fun k => by rw [pow_succ]; ring)
  simp only [transferMajorant]
  rw [tsum_mul_left, hsum]
  have hval : (1 / ((p : ℕ) : ℝ)) * (1 - 1 / ((p : ℕ) : ℝ))⁻¹
      = (((p : ℕ) : ℝ) - 1)⁻¹ := by
    field_simp
  rw [hval]
  have hlogsq : (0 : ℝ) < (Real.log ((p : ℕ) : ℝ)) ^ 2 := by positivity
  have hLHS : ((Real.log ((p : ℕ) : ℝ)) ^ 2)⁻¹ * (((p : ℕ) : ℝ) - 1)⁻¹
      = 1 / ((Real.log ((p : ℕ) : ℝ)) ^ 2 * (((p : ℕ) : ℝ) - 1)) := by
    rw [← mul_inv, one_div]
  rw [hLHS, div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ((p : ℕ) : ℝ) - 2) hlogsq.le]

set_option maxHeartbeats 800000 in
/-- **Theorem 19a.**  The Euler transfer function is square-summable — the additive cocycle is a
bounded `L²`-coboundary — exactly on and above the critical line. -/
theorem summable_transferModeSq_iff (σ : ℝ) :
    Summable (transferModeSq σ) ↔ 1 / 2 ≤ σ := by
  constructor
  · intro hsum
    rw [← summable_transferCoeffSq_iff]
    have hinj : Function.Injective (fun p : Nat.Primes => (p, 0)) := by
      intro a b hab
      exact (Prod.mk.injEq _ _ _ _ ▸ hab).1
    have := hsum.comp_injective hinj
    exact this.congr (fun p => transferModeSq_zero σ p)
  · intro hσ
    refine (summable_prod_of_nonneg (transferModeSq_nonneg σ)).mpr ⟨?_, ?_⟩
    · intro p
      exact Summable.of_nonneg_of_le (fun k => transferModeSq_nonneg σ (p, k))
        (fun k => transferModeSq_le_majorant hσ p k) (summable_transferMajorant p)
    · have hcomp : Summable (fun p : Nat.Primes =>
          2 / (((p : ℕ) : ℝ) * (Real.log ((p : ℕ) : ℝ)) ^ 2)) := by
        have := burnolSummable_prime_one_div_mul_log_sq.mul_left 2
        exact this.congr (fun p => by rw [mul_one_div])
      refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hcomp
      · exact tsum_nonneg (fun k => transferModeSq_nonneg σ (p, k))
      · refine le_trans ?_ (tsum_transferMajorant_le p)
        refine Summable.tsum_mono ?_ (summable_transferMajorant p)
          (fun k => transferModeSq_le_majorant hσ p k)
        exact Summable.of_nonneg_of_le (fun k => transferModeSq_nonneg σ (p, k))
          (fun k => transferModeSq_le_majorant hσ p k) (summable_transferMajorant p)

end RHTower.EulerCocycle
