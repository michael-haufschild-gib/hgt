import GaloisForLFunctions.RHTower.XiOrderedPrimeTraceClassRelocation
import GaloisForLFunctions.RHTower.Sieve.PrimeLogPowerTail
import GaloisForLFunctions.RHTower.PrimeDiagonalSingularValues
import GaloisForLFunctions.RHTower.TraceNormLimit

/-!
# Route-P two-step wild-saddle trace-class relocation

The smooth Riemann–von Mangoldt phase is an irregular exponential saddle. Writing its implicit
logarithmic coordinate as `u + log u = L`, two source-defined fixed-point steps
`u₁ = L - log L`, `u₂ = L - log u₁` leave an `ℓ¹` reciprocal defect. This module turns that
estimate into a target-free signed prime operator and proves its difference from the actual ordered
reciprocal-Xi operator is Schatten-1.

The result provides determinant-grade relocation, not determinant or spectral equality.
-/

open scoped BigOperators InnerProductSpace Nat.Prime
open Filter ContinuousLinearMap

namespace RHTower

noncomputable section

def routePTwoStepWildSaddleMass (n : ℕ) : ℝ :=
  max (Real.exp 3) ((n : ℝ) + 1 / 8)

def routePTwoStepWildSaddleLogPhase (n : ℕ) : ℝ :=
  Real.log (routePTwoStepWildSaddleMass n / Real.exp 1)

def routePTwoStepWildSaddleFirstPhase (n : ℕ) : ℝ :=
  routePTwoStepWildSaddleLogPhase n -
    Real.log (routePTwoStepWildSaddleLogPhase n)

def routePTwoStepWildSaddleSecondPhase (n : ℕ) : ℝ :=
  routePTwoStepWildSaddleLogPhase n -
    Real.log (routePTwoStepWildSaddleFirstPhase n)

def routePTwoStepWildSaddleReciprocal (n : ℕ) : ℝ :=
  routePTwoStepWildSaddleSecondPhase n /
    (2 * Real.pi * routePTwoStepWildSaddleMass n)

theorem routeKRVMQuantile_logPhase_pos (n : ℕ) :
    0 < Real.log (routeKRVMQuantile n / routeKRVMBase) := by
  apply Real.log_pos
  exact (lt_div_iff₀ routeKRVMBase_pos).2
    (by simpa using routeKRVMBase_lt_quantile n)

theorem routeKRVMQuantile_logPhase_mul_identity (n : ℕ) :
    routeKRVMQuantile n /
        (2 * Real.pi) *
          Real.log (routeKRVMQuantile n / routeKRVMBase) =
      (n : ℝ) + 1 / 8 := by
  have hcount := routeKSmoothRVMCount_quantile n
  rw [routeKSmoothRVMCount] at hcount
  linarith

theorem routeKRVMQuantile_reciprocal_eq_logPhase_div (n : ℕ) :
    (routeKRVMQuantile n)⁻¹ =
      Real.log (routeKRVMQuantile n / routeKRVMBase) /
        (2 * Real.pi * ((n : ℝ) + 1 / 8)) := by
  have hq : 0 < routeKRVMQuantile n :=
    routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)
  have hN : 0 < (n : ℝ) + 1 / 8 := by positivity
  have hid := routeKRVMQuantile_logPhase_mul_identity n
  field_simp [hq.ne', hN.ne', Real.pi_ne_zero] at hid ⊢
  nlinarith

theorem routeKRVMQuantile_logPhase_fixedPoint (n : ℕ) :
    let u := Real.log (routeKRVMQuantile n / routeKRVMBase)
    let N := (n : ℝ) + 1 / 8
    u + Real.log u = Real.log (N / Real.exp 1) := by
  dsimp
  let q := routeKRVMQuantile n
  let u := Real.log (q / routeKRVMBase)
  let N := (n : ℝ) + 1 / 8
  have hq : 0 < q := routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)
  have hratio : 0 < q / routeKRVMBase := div_pos hq routeKRVMBase_pos
  have hu : 0 < u := by
    dsimp [u]
    exact routeKRVMQuantile_logPhase_pos n
  have hN : 0 < N := by dsimp [N]; positivity
  have hqexp : q = routeKRVMBase * Real.exp u := by
    dsimp [u]
    rw [Real.exp_log hratio]
    field_simp [routeKRVMBase_pos.ne']
  have hid : q / (2 * Real.pi) * u = N := by
    simpa [q, u, N] using routeKRVMQuantile_logPhase_mul_identity n
  have hmul : u * Real.exp u = N / Real.exp 1 := by
    rw [hqexp, routeKRVMBase] at hid
    field_simp [Real.pi_ne_zero, Real.exp_ne_zero] at hid ⊢
    nlinarith [Real.exp_pos 1]
  calc
    u + Real.log u = Real.log u + Real.log (Real.exp u) := by
      rw [Real.log_exp]
      ring
    _ = Real.log (u * Real.exp u) := by
      rw [Real.log_mul hu.ne' (Real.exp_ne_zero u)]
    _ = Real.log (N / Real.exp 1) := by rw [hmul]

theorem routePTwoStepWildSaddleMass_pos (n : ℕ) :
    0 < routePTwoStepWildSaddleMass n := by
  exact (Real.exp_pos 3).trans_le (le_max_left _ _)

theorem routePTwoStepWildSaddleLogPhase_ge_two (n : ℕ) :
    2 ≤ routePTwoStepWildSaddleLogPhase n := by
  have hm : Real.exp 3 ≤ routePTwoStepWildSaddleMass n := le_max_left _ _
  have hmpos := routePTwoStepWildSaddleMass_pos n
  have hlogm : 3 ≤ Real.log (routePTwoStepWildSaddleMass n) := by
    calc
      3 = Real.log (Real.exp 3) := by rw [Real.log_exp]
      _ ≤ Real.log (routePTwoStepWildSaddleMass n) :=
        Real.strictMonoOn_log.monotoneOn (Real.exp_pos 3) hmpos hm
  rw [routePTwoStepWildSaddleLogPhase,
    Real.log_div hmpos.ne' (Real.exp_ne_zero 1), Real.log_exp]
  linarith

theorem log_le_half_self {v : ℝ} (hv : 0 < v) :
    Real.log v ≤ v / 2 := by
  have hw : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv.le
  have hwpos : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hlog : Real.log v = 2 * Real.log (Real.sqrt v) := by
    rw [Real.log_sqrt hv.le]
    ring
  have hstep : Real.log (Real.sqrt v) ≤ Real.sqrt v - 1 :=
    Real.log_le_sub_one_of_pos hwpos
  nlinarith [hlog.le, hlog.ge, hstep, sq_nonneg (Real.sqrt v - 2), hw]

theorem routePTwoStepWildSaddleFirstPhase_bounds (n : ℕ) :
    routePTwoStepWildSaddleLogPhase n / 2 ≤
        routePTwoStepWildSaddleFirstPhase n ∧
      routePTwoStepWildSaddleFirstPhase n ≤
        routePTwoStepWildSaddleLogPhase n := by
  have hL : 2 ≤ routePTwoStepWildSaddleLogPhase n :=
    routePTwoStepWildSaddleLogPhase_ge_two n
  have hLpos : 0 < routePTwoStepWildSaddleLogPhase n := by linarith
  constructor
  · rw [routePTwoStepWildSaddleFirstPhase]
    linarith [log_le_half_self hLpos]
  · rw [routePTwoStepWildSaddleFirstPhase]
    exact sub_le_self _ (Real.log_nonneg (by linarith))

theorem routePTwoStepWildSaddleFirstPhase_one_le (n : ℕ) :
    1 ≤ routePTwoStepWildSaddleFirstPhase n := by
  exact le_trans (by
      linarith [routePTwoStepWildSaddleLogPhase_ge_two n])
    (routePTwoStepWildSaddleFirstPhase_bounds n).1

theorem routePTwoStepWildSaddleSecondPhase_bounds (n : ℕ) :
    routePTwoStepWildSaddleFirstPhase n ≤
        routePTwoStepWildSaddleSecondPhase n ∧
      routePTwoStepWildSaddleSecondPhase n ≤
        routePTwoStepWildSaddleLogPhase n := by
  have hfirstPos : 0 < routePTwoStepWildSaddleFirstPhase n :=
    zero_lt_one.trans_le (routePTwoStepWildSaddleFirstPhase_one_le n)
  have hLpos : 0 < routePTwoStepWildSaddleLogPhase n :=
    (by linarith [routePTwoStepWildSaddleLogPhase_ge_two n])
  have hfirstLe := (routePTwoStepWildSaddleFirstPhase_bounds n).2
  have hlogLe : Real.log (routePTwoStepWildSaddleFirstPhase n) ≤
      Real.log (routePTwoStepWildSaddleLogPhase n) :=
    Real.strictMonoOn_log.monotoneOn hfirstPos hLpos hfirstLe
  constructor
  · rw [routePTwoStepWildSaddleSecondPhase]
    have hgap : routePTwoStepWildSaddleLogPhase n -
        routePTwoStepWildSaddleFirstPhase n =
          Real.log (routePTwoStepWildSaddleLogPhase n) := by
      rw [routePTwoStepWildSaddleFirstPhase]
      ring
    linarith
  · rw [routePTwoStepWildSaddleSecondPhase]
    exact sub_le_self _ (Real.log_nonneg
      (routePTwoStepWildSaddleFirstPhase_one_le n))

theorem routePTwoStepWildSaddleSecondPhase_nonneg (n : ℕ) :
    0 ≤ routePTwoStepWildSaddleSecondPhase n := by
  exact zero_le_one.trans
    ((routePTwoStepWildSaddleFirstPhase_one_le n).trans
      (routePTwoStepWildSaddleSecondPhase_bounds n).1)

theorem routePTwoStepWildSaddleReciprocal_nonneg (n : ℕ) :
    0 ≤ routePTwoStepWildSaddleReciprocal n := by
  exact div_nonneg (routePTwoStepWildSaddleSecondPhase_nonneg n)
    (mul_nonneg (by positivity) (routePTwoStepWildSaddleMass_pos n).le)

theorem routePTwoStepWildSaddleLogPhase_le_mass (n : ℕ) :
    routePTwoStepWildSaddleLogPhase n ≤
      routePTwoStepWildSaddleMass n := by
  have hm := routePTwoStepWildSaddleMass_pos n
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hratio : 0 < routePTwoStepWildSaddleMass n / Real.exp 1 := by positivity
  calc
    routePTwoStepWildSaddleLogPhase n =
        Real.log (routePTwoStepWildSaddleMass n / Real.exp 1) := rfl
    _ ≤ routePTwoStepWildSaddleMass n / Real.exp 1 - 1 :=
      Real.log_le_sub_one_of_pos hratio
    _ ≤ routePTwoStepWildSaddleMass n := by
      have hdiv : routePTwoStepWildSaddleMass n / Real.exp 1 ≤
          routePTwoStepWildSaddleMass n := by
        exact (div_le_iff₀ (Real.exp_pos 1)).2 (by nlinarith)
      linarith

theorem routePTwoStepWildSaddleReciprocal_le_one (n : ℕ) :
    routePTwoStepWildSaddleReciprocal n ≤ 1 := by
  have hm := routePTwoStepWildSaddleMass_pos n
  have hsecond := (routePTwoStepWildSaddleSecondPhase_bounds n).2
  have hphase := routePTwoStepWildSaddleLogPhase_le_mass n
  rw [routePTwoStepWildSaddleReciprocal, div_le_one (by positivity)]
  have htwoPi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc
    routePTwoStepWildSaddleSecondPhase n ≤
        routePTwoStepWildSaddleMass n := hsecond.trans hphase
    _ ≤ 2 * Real.pi * routePTwoStepWildSaddleMass n := by
      nlinarith

/-- Two logarithmic fixed-point steps approximate the positive wild saddle with summable-scale
error. -/
theorem twoStepLogFixedPoint_error {L u : ℝ}
    (hL : 2 ≤ L) (hu : 0 < u)
    (hfix : u + Real.log u = L) :
    let u₁ := L - Real.log L
    let u₂ := L - Real.log u₁
    0 ≤ u₂ - u ∧
      u₂ - u ≤ 4 * Real.log L / L ^ 2 := by
  dsimp
  have hLpos : 0 < L := by linarith
  have huOne : 1 < u := by
    by_contra hnot
    have hule : u ≤ 1 := le_of_not_gt hnot
    have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu.le hule
    linarith
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg huOne.le
  have huL : u ≤ L := by linarith
  have hloguL : Real.log u ≤ Real.log L :=
    Real.strictMonoOn_log.monotoneOn hu hLpos huL
  let u₁ : ℝ := L - Real.log L
  have hu₁Lower : L / 2 ≤ u₁ := by
    dsimp [u₁]
    linarith [log_le_half_self hLpos]
  have hu₁Pos : 0 < u₁ := by linarith
  have hu₁u : u₁ ≤ u := by
    dsimp [u₁]
    linarith
  have hdiffOne : u - u₁ = Real.log L - Real.log u := by
    dsimp [u₁]
    linarith
  have hlogRatio : Real.log L - Real.log u ≤ (L - u) / u := by
    calc
      Real.log L - Real.log u = Real.log (L / u) := by
        rw [Real.log_div hLpos.ne' hu.ne']
      _ ≤ L / u - 1 := Real.log_le_sub_one_of_pos (div_pos hLpos hu)
      _ = (L - u) / u := by field_simp [hu.ne']
  have hdiffOneBound : u - u₁ ≤ 2 * Real.log L / L := by
    rw [hdiffOne]
    apply hlogRatio.trans
    rw [div_le_div_iff₀ hu hLpos]
    have hgap : L - u = Real.log u := by linarith
    have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    have huHalf : L / 2 ≤ u := hu₁Lower.trans hu₁u
    rw [hgap]
    nlinarith [mul_nonneg hlogL0 (sub_nonneg.mpr huHalf)]
  have hdiffOne0 : 0 ≤ u - u₁ := sub_nonneg.mpr hu₁u
  have hlogDiff : Real.log u - Real.log u₁ ≤ (u - u₁) / u₁ := by
    calc
      Real.log u - Real.log u₁ = Real.log (u / u₁) := by
        rw [Real.log_div hu.ne' hu₁Pos.ne']
      _ ≤ u / u₁ - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hu hu₁Pos)
      _ = (u - u₁) / u₁ := by field_simp [hu₁Pos.ne']
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ 4 * Real.log L / L ^ 2 := by positivity
  have hquotBound : (u - u₁) / u₁ ≤
      4 * Real.log L / L ^ 2 := by
    rw [div_le_iff₀ hu₁Pos]
    apply hdiffOneBound.trans
    calc
      2 * Real.log L / L =
          (4 * Real.log L / L ^ 2) * (L / 2) := by
        field_simp [hLpos.ne']
        ring
      _ ≤ (4 * Real.log L / L ^ 2) * u₁ :=
        mul_le_mul_of_nonneg_left hu₁Lower hcoef
  have hsecondEq :
      (L - Real.log (L - Real.log L)) - u =
        Real.log u - Real.log u₁ := by
    dsimp [u₁]
    linarith
  rw [hsecondEq]
  constructor
  · exact sub_nonneg.mpr
      (Real.strictMonoOn_log.monotoneOn hu₁Pos hu hu₁u)
  · exact hlogDiff.trans hquotBound

theorem eventually_routePTwoStepWildSaddleMass_eq :
    ∀ᶠ n : ℕ in atTop,
      routePTwoStepWildSaddleMass n = (n : ℝ) + 1 / 8 := by
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1 / 8) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  filter_upwards [htop.eventually (eventually_ge_atTop (Real.exp 3))] with n hn
  exact max_eq_right hn

theorem eventually_routePTwoStepWildSaddleReciprocal_sub_rvm_bounds :
    ∀ᶠ n : ℕ in atTop,
      0 ≤ routePTwoStepWildSaddleReciprocal n -
          (routeKRVMQuantile n)⁻¹ ∧
      routePTwoStepWildSaddleReciprocal n -
          (routeKRVMQuantile n)⁻¹ ≤
        (4 * Real.log (Real.log (((n : ℝ) + 1 / 8) / Real.exp 1)) /
            Real.log (((n : ℝ) + 1 / 8) / Real.exp 1) ^ 2) /
          (2 * Real.pi * ((n : ℝ) + 1 / 8)) := by
  filter_upwards [eventually_routePTwoStepWildSaddleMass_eq] with n hmass
  let N : ℝ := (n : ℝ) + 1 / 8
  let L : ℝ := Real.log (N / Real.exp 1)
  let u : ℝ := Real.log (routeKRVMQuantile n / routeKRVMBase)
  let u₁ : ℝ := L - Real.log L
  let u₂ : ℝ := L - Real.log u₁
  have hN : 0 < N := by dsimp [N]; positivity
  have hL : 2 ≤ L := by
    simpa [routePTwoStepWildSaddleLogPhase, L, N, hmass] using
      routePTwoStepWildSaddleLogPhase_ge_two n
  have hu : 0 < u := by
    dsimp [u]
    exact routeKRVMQuantile_logPhase_pos n
  have hfix : u + Real.log u = L := by
    simpa [u, L, N] using routeKRVMQuantile_logPhase_fixedPoint n
  have herr : 0 ≤ u₂ - u ∧
      u₂ - u ≤ 4 * Real.log L / L ^ 2 := by
    simpa [u₁, u₂] using twoStepLogFixedPoint_error hL hu hfix
  have hsource : routePTwoStepWildSaddleReciprocal n =
      u₂ / (2 * Real.pi * N) := by
    simp [routePTwoStepWildSaddleReciprocal,
      routePTwoStepWildSaddleSecondPhase,
      routePTwoStepWildSaddleFirstPhase,
      routePTwoStepWildSaddleLogPhase, u₂, u₁, L, N, hmass]
  have hrvm : (routeKRVMQuantile n)⁻¹ =
      u / (2 * Real.pi * N) := by
    simpa [u, N] using routeKRVMQuantile_reciprocal_eq_logPhase_div n
  have hden : 0 < 2 * Real.pi * N := by positivity
  rw [hsource, hrvm]
  have hdiff : u₂ / (2 * Real.pi * N) - u / (2 * Real.pi * N) =
      (u₂ - u) / (2 * Real.pi * N) := by ring
  rw [hdiff]
  constructor
  · exact div_nonneg herr.1 hden.le
  · apply div_le_div_of_nonneg_right herr.2 hden.le


theorem summable_nthPrime_one_div_mul_sqrt_log :
    Summable (fun n : ℕ =>
      1 / (((Nat.nth Nat.Prime n : ℕ) : ℝ) *
        Real.sqrt (Real.log ((Nat.nth Nat.Prime n : ℕ) : ℝ)))) := by
  have hprime := Sieve.summable_primes_one_div_mul_log_rpow
    (s := (1 / 2 : ℝ)) (by norm_num)
  have hnat := nthPrimeEquiv.summable_iff.mpr hprime
  simpa [Function.comp_def, nthPrimeEquiv, nthPrimeSubtype,
    Real.sqrt_eq_rpow] using hnat

theorem eventually_nthPrime_le_two_mul_nat_log :
    ∀ᶠ n : ℕ in atTop,
      ((Nat.nth Nat.Prime n : ℕ) : ℝ) ≤
        2 * (n : ℝ) * Real.log (n : ℝ) := by
  have hden : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
    have hlogn : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    exact mul_ne_zero hn0 hlogn
  have hratio : Tendsto (fun n : ℕ =>
      ((Nat.nth Nat.Prime n : ℕ) : ℝ) /
        ((n : ℝ) * Real.log (n : ℝ))) atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hden).mp nth_prime_asymp
  filter_upwards [hratio.eventually_lt_const (by norm_num : (1 : ℝ) < 2),
      eventually_gt_atTop 1] with n hnratio hn
  have hdenpos : 0 < (n : ℝ) * Real.log (n : ℝ) := by
    exact mul_pos (by exact_mod_cast (Nat.zero_lt_of_lt hn))
      (Real.log_pos (by exact_mod_cast hn))
  have hle := (div_lt_iff₀ hdenpos).mp hnratio |>.le
  simpa [mul_assoc] using hle

theorem eventually_log_nthPrime_le_two_mul_log_nat :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((Nat.nth Nat.Prime n : ℕ) : ℝ) ≤
        2 * Real.log (n : ℝ) := by
  filter_upwards [tendsto_log_nthPrime_div.eventually_lt_const
      (by norm_num : (1 : ℝ) < 2), eventually_gt_atTop 1] with n hnratio hn
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  exact (div_lt_iff₀ hlogn).mp hnratio |>.le

def routePTwoStepWildSaddleRVMDefect (n : ℕ) : ℝ :=
  |routePTwoStepWildSaddleReciprocal n - (routeKRVMQuantile n)⁻¹|

theorem eventually_routePTwoStepWildSaddleRVMDefect_le_primeMajorant :
    ∀ᶠ n : ℕ in atTop,
      routePTwoStepWildSaddleRVMDefect n ≤
        128 * (1 / (((Nat.nth Nat.Prime n : ℕ) : ℝ) *
          Real.sqrt (Real.log ((Nat.nth Nat.Prime n : ℕ) : ℝ)))) := by
  have hnatTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [eventually_routePTwoStepWildSaddleReciprocal_sub_rvm_bounds,
      eventually_nthPrime_le_two_mul_nat_log,
      eventually_log_nthPrime_le_two_mul_log_nat,
      hnatTop.eventually (eventually_ge_atTop (Real.exp 3)),
      eventually_gt_atTop 1] with n hdef hpBound hlogpBound hnExp hn
  let N : ℝ := (n : ℝ) + 1 / 8
  let L : ℝ := Real.log (N / Real.exp 1)
  let p : ℝ := ((Nat.nth Nat.Prime n : ℕ) : ℝ)
  let logn : ℝ := Real.log (n : ℝ)
  let logp : ℝ := Real.log p
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hN : 0 < N := by dsimp [N]; positivity
  have hlogn : 0 < logn := by
    dsimp [logn]
    exact Real.log_pos (by exact_mod_cast hn)
  have hp : 0 < p := by
    dsimp [p]
    exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n).pos
  have hlogp : 0 < logp := by
    dsimp [logp, p]
    exact Real.log_pos (by
      exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n).two_le)
  have hLformula : L = Real.log N - 1 := by
    dsimp [L]
    rw [Real.log_div hN.ne' (Real.exp_ne_zero 1), Real.log_exp]
  have hlogNge : logn ≤ Real.log N := by
    apply Real.strictMonoOn_log.monotoneOn hnpos hN
    dsimp [N]
    linarith
  have hlognThree : 3 ≤ logn := by
    dsimp [logn]
    calc
      3 = Real.log (Real.exp 3) := by rw [Real.log_exp]
      _ ≤ Real.log (n : ℝ) :=
        Real.strictMonoOn_log.monotoneOn (Real.exp_pos 3) hnpos hnExp
  have hLHalf : logn / 2 ≤ L := by
    rw [hLformula]
    linarith
  have hL : 0 < L := by linarith
  have hLOne : 1 < L := by linarith
  have hsqrtL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsqrtLogn : 0 < Real.sqrt logn := Real.sqrt_pos.2 hlogn
  have hsqrtLogp : 0 < Real.sqrt logp := Real.sqrt_pos.2 hlogp
  have hsqrtLogpBound : Real.sqrt logp ≤ 2 * Real.sqrt logn := by
    have hlogpBound' : logp ≤ 2 * logn := by
      simpa [logp, logn, p] using hlogpBound
    nlinarith [Real.sq_sqrt hlogp.le, Real.sq_sqrt hlogn.le,
      Real.sqrt_nonneg logp, Real.sqrt_nonneg logn]
  have hsqrtLBound : Real.sqrt logn / 2 ≤ Real.sqrt L := by
    nlinarith [Real.sq_sqrt hlogn.le, Real.sq_sqrt hL.le,
      Real.sqrt_nonneg logn, Real.sqrt_nonneg L]
  have hpBound' : p ≤ 2 * (n : ℝ) * logn := by
    simpa [p, logn] using hpBound
  have hpSqrtBound : p * Real.sqrt logp ≤
      16 * N * (L * Real.sqrt L) := by
    have hnN : (n : ℝ) ≤ N := by dsimp [N]; linarith
    have hprimeSide : p * Real.sqrt logp ≤
        4 * N * (logn * Real.sqrt logn) := by
      calc
        p * Real.sqrt logp ≤
            (2 * (n : ℝ) * logn) * (2 * Real.sqrt logn) :=
          mul_le_mul hpBound' hsqrtLogpBound
            (Real.sqrt_nonneg _) (by positivity)
        _ ≤ 4 * N * (logn * Real.sqrt logn) := by
          nlinarith [mul_nonneg hlogn.le (Real.sqrt_nonneg logn)]
    have hlogSide : logn * Real.sqrt logn ≤
        4 * (L * Real.sqrt L) := by
      have hmul := mul_le_mul hLHalf hsqrtLBound
        (by positivity : 0 ≤ Real.sqrt logn / 2) hL.le
      nlinarith
    exact hprimeSide.trans (by
      nlinarith [mul_nonneg hN.le
        (mul_nonneg hL.le (Real.sqrt_nonneg L))])
  have hmajorInv : 1 / (N * (L * Real.sqrt L)) ≤
      16 / (p * Real.sqrt logp) := by
    rw [div_le_div_iff₀
      (mul_pos hN (mul_pos hL hsqrtL))
      (mul_pos hp hsqrtLogp)]
    simpa [mul_assoc] using hpSqrtBound
  have hlogLBound : Real.log L ≤ 2 * Real.sqrt L :=
    Real.log_le_two_mul_sqrt hLOne
  have hnumerator : 4 * Real.log L / L ^ 2 ≤
      8 / (L * Real.sqrt L) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hL) (mul_pos hL hsqrtL)]
    have hmul := mul_le_mul_of_nonneg_right
      (show 4 * Real.log L ≤ 8 * Real.sqrt L by linarith)
      (mul_nonneg hL.le (Real.sqrt_nonneg L))
    nlinarith [hmul, Real.sq_sqrt hL.le]
  have htwoPi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hrawMajor :
      (4 * Real.log L / L ^ 2) / (2 * Real.pi * N) ≤
        8 / (N * (L * Real.sqrt L)) := by
    calc
      (4 * Real.log L / L ^ 2) / (2 * Real.pi * N) ≤
          (8 / (L * Real.sqrt L)) / (2 * Real.pi * N) :=
        div_le_div_of_nonneg_right hnumerator (by positivity)
      _ ≤ 8 / (N * (L * Real.sqrt L)) := by
        field_simp [hN.ne', hL.ne', hsqrtL.ne', Real.pi_ne_zero]
        nlinarith [Real.pi_pos]
  have hdef' : 0 ≤ routePTwoStepWildSaddleReciprocal n -
      (routeKRVMQuantile n)⁻¹ := hdef.1
  rw [routePTwoStepWildSaddleRVMDefect, abs_of_nonneg hdef']
  calc
    routePTwoStepWildSaddleReciprocal n - (routeKRVMQuantile n)⁻¹ ≤
        (4 * Real.log L / L ^ 2) / (2 * Real.pi * N) := by
      simpa [L, N] using hdef.2
    _ ≤ 8 / (N * (L * Real.sqrt L)) := hrawMajor
    _ ≤ 128 * (1 / (p * Real.sqrt logp)) := by
      calc
        8 / (N * (L * Real.sqrt L)) =
            8 * (1 / (N * (L * Real.sqrt L))) := by ring
        _ ≤ 8 * (16 / (p * Real.sqrt logp)) :=
          mul_le_mul_of_nonneg_left hmajorInv (by norm_num)
        _ = 128 * (1 / (p * Real.sqrt logp)) := by
          rw [div_eq_mul_inv, one_div]
          ring
    _ = 128 * (1 / (((Nat.nth Nat.Prime n : ℕ) : ℝ) *
        Real.sqrt (Real.log ((Nat.nth Nat.Prime n : ℕ) : ℝ)))) := by
      rfl

theorem summable_routePTwoStepWildSaddleRVMDefect :
    Summable routePTwoStepWildSaddleRVMDefect := by
  have hmajor : Summable (fun n : ℕ =>
      128 * (1 / (((Nat.nth Nat.Prime n : ℕ) : ℝ) *
        Real.sqrt (Real.log ((Nat.nth Nat.Prime n : ℕ) : ℝ))))) :=
    summable_nthPrime_one_div_mul_sqrt_log.mul_left 128
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_routePTwoStepWildSaddleRVMDefect_le_primeMajorant]
    with n hn
  have hdefNonneg : 0 ≤ routePTwoStepWildSaddleRVMDefect n := by
    exact abs_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hdefNonneg]
  exact hn

/-- Explicit two-step wild-saddle reciprocal on the prime label. -/
def routePTwoStepWildSaddlePrimeReciprocal (p : Nat.Primes) : ℝ :=
  routePTwoStepWildSaddleReciprocal (routeKPrimeRVMIndex p)

theorem routePTwoStepWildSaddlePrimeReciprocal_nonneg (p : Nat.Primes) :
    0 ≤ routePTwoStepWildSaddlePrimeReciprocal p :=
  routePTwoStepWildSaddleReciprocal_nonneg _

theorem routePTwoStepWildSaddlePrimeReciprocal_le_one (p : Nat.Primes) :
    routePTwoStepWildSaddlePrimeReciprocal p ≤ 1 :=
  routePTwoStepWildSaddleReciprocal_le_one _

def routePTwoStepWildSaddleSignedMultiplier : RouteKSignedPrimeIndex → ℂ
  | Sum.inl p => (routePTwoStepWildSaddlePrimeReciprocal p : ℂ)
  | Sum.inr p => -(routePTwoStepWildSaddlePrimeReciprocal p : ℂ)

theorem norm_routePTwoStepWildSaddleSignedMultiplier_le_one
    (i : RouteKSignedPrimeIndex) :
    ‖routePTwoStepWildSaddleSignedMultiplier i‖ ≤ 1 := by
  cases i with
  | inl p =>
      simpa [routePTwoStepWildSaddleSignedMultiplier, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg
          (routePTwoStepWildSaddlePrimeReciprocal_nonneg p)] using
        routePTwoStepWildSaddlePrimeReciprocal_le_one p
  | inr p =>
      simpa [routePTwoStepWildSaddleSignedMultiplier, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
          (routePTwoStepWildSaddlePrimeReciprocal_nonneg p)] using
        routePTwoStepWildSaddlePrimeReciprocal_le_one p

/-- Target-free signed prime operator from two stationary-phase logarithmic iterations. -/
def routePTwoStepWildSaddleSignedOperator :
    RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert :=
  HTGeometry.ellTwoDiagonal routePTwoStepWildSaddleSignedMultiplier
    norm_routePTwoStepWildSaddleSignedMultiplier_le_one

theorem routePTwoStepWildSaddleSignedOperator_basis_inl (p : Nat.Primes) :
    routePTwoStepWildSaddleSignedOperator
        (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inl p)) =
      (routePTwoStepWildSaddlePrimeReciprocal p : ℂ) •
        HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inl p) := by
  simpa [routePTwoStepWildSaddleSignedOperator,
    routePTwoStepWildSaddleSignedMultiplier] using
    HTGeometry.ellTwoDiagonal_coordinateBasis
      routePTwoStepWildSaddleSignedMultiplier
      norm_routePTwoStepWildSaddleSignedMultiplier_le_one (Sum.inl p)

theorem routePTwoStepWildSaddleSignedOperator_basis_inr (p : Nat.Primes) :
    routePTwoStepWildSaddleSignedOperator
        (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inr p)) =
      -(routePTwoStepWildSaddlePrimeReciprocal p : ℂ) •
        HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inr p) := by
  simpa [routePTwoStepWildSaddleSignedOperator,
    routePTwoStepWildSaddleSignedMultiplier] using
    HTGeometry.ellTwoDiagonal_coordinateBasis
      routePTwoStepWildSaddleSignedMultiplier
      norm_routePTwoStepWildSaddleSignedMultiplier_le_one (Sum.inr p)

theorem routePTwoStepWildSaddleSignedOperator_selfAdjoint :
    ContinuousLinearMap.adjoint routePTwoStepWildSaddleSignedOperator =
      routePTwoStepWildSaddleSignedOperator := by
  rw [routePTwoStepWildSaddleSignedOperator,
    HTGeometry.adjoint_ellTwoDiagonal]
  ext f i
  rw [HTGeometry.ellTwoDiagonal_apply, HTGeometry.ellTwoDiagonal_apply]
  cases i <;> simp [routePTwoStepWildSaddleSignedMultiplier]

theorem summable_abs_routePTwoStepWildSaddlePrimeReciprocal_sub_rvm :
    Summable (fun p : Nat.Primes =>
      |routePTwoStepWildSaddlePrimeReciprocal p -
        routeKPrimeRVMReciprocal p|) := by
  have hnat : Summable (fun n : ℕ =>
      |routePTwoStepWildSaddleReciprocal n -
        (routeKRVMQuantile n)⁻¹|) := by
    exact summable_routePTwoStepWildSaddleRVMDefect.congr (fun n => rfl)
  apply nthPrimeEquiv.summable_iff.mp
  simpa [Function.comp_def, nthPrimeEquiv,
    routePTwoStepWildSaddlePrimeReciprocal,
    routeKPrimeRVMReciprocal,
    routeKPrimeRVMIndex_nthPrimeSubtype] using
    hnat

def routePTwoStepWildSaddleRVMCorrectionMultiplier :
    RouteKSignedPrimeIndex → ℝ
  | Sum.inl p => routePTwoStepWildSaddlePrimeReciprocal p -
      routeKPrimeRVMReciprocal p
  | Sum.inr p => -(routePTwoStepWildSaddlePrimeReciprocal p -
      routeKPrimeRVMReciprocal p)

theorem summable_abs_routePTwoStepWildSaddleRVMCorrectionMultiplier :
    Summable (fun i : RouteKSignedPrimeIndex =>
      |routePTwoStepWildSaddleRVMCorrectionMultiplier i|) := by
  apply Summable.sum
  · simpa [Function.comp_def,
      routePTwoStepWildSaddleRVMCorrectionMultiplier] using
      summable_abs_routePTwoStepWildSaddlePrimeReciprocal_sub_rvm
  · simpa [Function.comp_def,
      routePTwoStepWildSaddleRVMCorrectionMultiplier, abs_sub_comm] using
      summable_abs_routePTwoStepWildSaddlePrimeReciprocal_sub_rvm

def routePTwoStepWildSaddleRVMCorrection :
    RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert :=
  GaloisForLFunctions.HTGeometry.realSummableDiagonalOperator
    routePTwoStepWildSaddleRVMCorrectionMultiplier
    summable_abs_routePTwoStepWildSaddleRVMCorrectionMultiplier

theorem routePTwoStepWildSaddleRVMCorrection_memSchattenClass_one :
    MemSchattenClass 1 routePTwoStepWildSaddleRVMCorrection := by
  exact GaloisForLFunctions.HTGeometry.realSummableDiagonalOperator_memSchattenClass_one
    routePTwoStepWildSaddleRVMCorrectionMultiplier
    summable_abs_routePTwoStepWildSaddleRVMCorrectionMultiplier

theorem routePTwoStepWildSaddleSignedOperator_sub_routeKSignedPrimeRVMOperator :
    routePTwoStepWildSaddleSignedOperator - routeKSignedPrimeRVMOperator =
      routePTwoStepWildSaddleRVMCorrection := by
  apply ContinuousLinearMap.ext
  intro f
  rw [sub_apply]
  apply Subtype.ext
  funext i
  have hA : routePTwoStepWildSaddleSignedOperator f i =
      routePTwoStepWildSaddleSignedMultiplier i * f i := by
    rw [routePTwoStepWildSaddleSignedOperator,
      HTGeometry.ellTwoDiagonal_apply]
  have hQ : routeKSignedPrimeRVMOperator f i =
      routeKSignedPrimeRVMMultiplier i * f i := by
    rw [routeKSignedPrimeRVMOperator, HTGeometry.ellTwoDiagonal_apply]
  have hK : routePTwoStepWildSaddleRVMCorrection f i =
      (routePTwoStepWildSaddleRVMCorrectionMultiplier i : ℂ) * f i := by
    exact GaloisForLFunctions.HTGeometry.realSummableDiagonalOperator_apply
      routePTwoStepWildSaddleRVMCorrectionMultiplier
      summable_abs_routePTwoStepWildSaddleRVMCorrectionMultiplier f i
  change routePTwoStepWildSaddleSignedOperator f i -
      routeKSignedPrimeRVMOperator f i =
        routePTwoStepWildSaddleRVMCorrection f i
  rw [hA, hQ, hK]
  cases i <;>
    simp [routePTwoStepWildSaddleSignedMultiplier,
      routeKSignedPrimeRVMMultiplier,
      routePTwoStepWildSaddleRVMCorrectionMultiplier] <;> ring

theorem routePTwoStepWildSaddleSignedOperator_sub_routeKSignedPrimeRVMOperator_memSchattenClass_one :
    MemSchattenClass 1
      (routePTwoStepWildSaddleSignedOperator - routeKSignedPrimeRVMOperator) := by
  rw [routePTwoStepWildSaddleSignedOperator_sub_routeKSignedPrimeRVMOperator]
  exact routePTwoStepWildSaddleRVMCorrection_memSchattenClass_one

/-- The explicit source counterterm reaches actual reciprocal Xi modulo trace class. -/
theorem xiOrderedSignedPrimeOperator_sub_routePTwoStepWildSaddleSignedOperator_memSchattenClass_one :
    MemSchattenClass 1
      (xiOrderedSignedPrimeOperator - routePTwoStepWildSaddleSignedOperator) := by
  have hXR :=
    xiOrderedSignedPrimeOperator_sub_routeKSignedPrimeRVMOperator_memSchattenClass_one
  have hSR :=
    routePTwoStepWildSaddleSignedOperator_sub_routeKSignedPrimeRVMOperator_memSchattenClass_one
  have hmem := hXR.one_sub hSR
  have heq : xiOrderedSignedPrimeOperator -
      routePTwoStepWildSaddleSignedOperator =
        (xiOrderedSignedPrimeOperator - routeKSignedPrimeRVMOperator) -
          (routePTwoStepWildSaddleSignedOperator -
            routeKSignedPrimeRVMOperator) := by
    abel
  rw [heq]
  exact hmem

/-- Two wild-saddle logarithmic iterations are sufficient for determinant-grade Xi relocation. -/
theorem routeP_twoStepWildSaddle_traceClassXiRelocation :
    Summable routePTwoStepWildSaddleRVMDefect ∧
    MemSchattenClass 1
      (routePTwoStepWildSaddleSignedOperator - routeKSignedPrimeRVMOperator) ∧
    MemSchattenClass 1
      (xiOrderedSignedPrimeOperator -
        routePTwoStepWildSaddleSignedOperator) ∧
    ContinuousLinearMap.adjoint routePTwoStepWildSaddleSignedOperator =
      routePTwoStepWildSaddleSignedOperator := by
  exact ⟨summable_routePTwoStepWildSaddleRVMDefect,
    routePTwoStepWildSaddleSignedOperator_sub_routeKSignedPrimeRVMOperator_memSchattenClass_one,
    xiOrderedSignedPrimeOperator_sub_routePTwoStepWildSaddleSignedOperator_memSchattenClass_one,
    routePTwoStepWildSaddleSignedOperator_selfAdjoint⟩


end

end RHTower
