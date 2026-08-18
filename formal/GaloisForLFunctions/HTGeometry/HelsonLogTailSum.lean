import GaloisForLFunctions.HTGeometry.EulerLogTail
import GaloisForLFunctions.HTGeometry.HelsonEulerMultipliable

/-!
# The absolutely convergent layer of the Helson Euler logarithm

For a phase bounded by one, the Euler logarithm of the Helson zeta splits as

```text
log Z_χ(s)  =  ∑_p χ(p) p^{-s}  +  ∑_p logTail (χ(p) p^{-s}) .
```

The first layer is conditionally convergent and only past the abscissa `1/2`; the second is
**absolutely** convergent on the whole half plane `Re s > 1/2`, because `‖logTail z‖ = O(‖z‖²)` and
`∑_p p^{-2σ}` converges there.  So the tail layer is a genuine holomorphic function on
`Re s > 1/2` for *every* phase, with no probabilistic input at all, and the whole randomness of the
Euler logarithm sits in the prime layer.

The uniform constant is elementary: for `σ ≥ 1/2` and a prime `p`, `p^{-σ} ≤ 2^{-1/2} ≤ 3/4`, so
`1 - ‖z‖ ≥ 1/4` and `‖logTail z‖ ≤ 2 ‖z‖²`.
-/

noncomputable section

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- `2^{-1/2} ≤ 3/4`. -/
theorem rpow_two_neg_half_le : (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 4 := by
  have hpos : (0:ℝ) < (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hsq : ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ (2 : ℕ) = 1 / 2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2) : ℝ)) 2,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  nlinarith [hpos, hsq]

/-- On the closed half plane `Re s ≥ 1/2` a prime power is at most `3/4` in norm. -/
theorem norm_prime_cpow_le_three_quarters (p : Nat.Primes) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 3 / 4 := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  rw [hnorm]
  calc ((p : ℕ) : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ ≤ 3 / 4 := rpow_two_neg_half_le

/-- The quadratic tail bound on the half plane, with the uniform constant `2`. -/
theorem norm_logTail_prime_le {χ : Nat.Primes → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1) (p : Nat.Primes)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖logTail (χ p * ((p : ℕ) : ℂ) ^ (-s))‖ ≤ 2 * (((p : ℕ) : ℝ) ^ (-(2 * s.re))) := by
  set z : ℂ := χ p * ((p : ℕ) : ℂ) ^ (-s) with hz
  have hpn : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  have hzn : ‖z‖ ≤ ((p : ℕ) : ℝ) ^ (-s.re) := by
    rw [hz, norm_mul, hpn]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (hχ p)
  have hz34 : ‖z‖ ≤ 3 / 4 := le_trans hzn (by
    rw [← hpn]; exact norm_prime_cpow_le_three_quarters p hs)
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz34 (by norm_num)
  refine le_trans (norm_logTail_le hz1) ?_
  have hden : (1 : ℝ) / 4 ≤ 1 - ‖z‖ := by linarith
  have hnn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have hsq : ‖z‖ ^ 2 ≤ (((p : ℕ) : ℝ) ^ (-s.re)) ^ 2 := by
    exact pow_le_pow_left₀ hnn hzn 2
  have hpow : (((p : ℕ) : ℝ) ^ (-s.re)) ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by
    rw [← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul (by positivity)]
    norm_num
    ring_nf
  have hdiv : ‖z‖ ^ 2 / (2 * (1 - ‖z‖)) ≤ ‖z‖ ^ 2 / (2 * (1 / 4)) := by
    refine div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  calc ‖z‖ ^ 2 / (2 * (1 - ‖z‖)) ≤ ‖z‖ ^ 2 / (2 * (1 / 4)) := hdiv
    _ = 2 * ‖z‖ ^ 2 := by ring
    _ ≤ 2 * (((p : ℕ) : ℝ) ^ (-s.re)) ^ 2 := by linarith
    _ = 2 * (((p : ℕ) : ℝ) ^ (-(2 * s.re))) := by rw [hpow]

/-! ### The tail layer as a holomorphic function -/

/-- The absolutely convergent layer of the Helson Euler logarithm. -/
def helsonLogTail (χ : Nat.Primes → ℂ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, logTail (χ p * ((p : ℕ) : ℂ) ^ (-s))

theorem summable_prime_rpow_neg_two {x : ℝ} (hx : 1 / 2 < x) :
    Summable fun p : Nat.Primes => (2 : ℝ) * (((p : ℕ) : ℝ) ^ (-(2 * x))) :=
  (summable_prime_rpow_neg (by linarith)).mul_left 2

theorem summable_helsonLogTail {χ : Nat.Primes → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    Summable fun p : Nat.Primes => logTail (χ p * ((p : ℕ) : ℂ) ^ (-s)) :=
  Summable.of_norm_bounded (summable_prime_rpow_neg_two hs)
    fun p => norm_logTail_prime_le hχ p hs.le

/-- Each tail term is holomorphic past the half line. -/
theorem differentiableOn_logTail_prime {χ : Nat.Primes → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1)
    (p : Nat.Primes) :
    DifferentiableOn ℂ (fun s => logTail (χ p * ((p : ℕ) : ℂ) ^ (-s)))
      {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hs' : (1:ℝ) / 2 < s.re := hs
  have hpne : (((p : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr p.2.ne_zero
  have hz : DifferentiableAt ℂ (fun s : ℂ => χ p * ((p : ℕ) : ℂ) ^ (-s)) s :=
    (DifferentiableAt.const_cpow (differentiable_id.neg s) (Or.inl hpne)).const_mul _
  have hnorm : ‖χ p * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ 3 / 4 := by
    rw [norm_mul]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hχ p))
      (norm_prime_cpow_le_three_quarters p hs'.le)
  have hslit : (1 - χ p * ((p : ℕ) : ℂ) ^ (-s)) ∈ Complex.slitPlane := by
    left
    have hre : (χ p * ((p : ℕ) : ℂ) ^ (-s)).re ≤ ‖χ p * ((p : ℕ) : ℂ) ^ (-s)‖ :=
      Complex.re_le_norm _
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hlog : DifferentiableAt ℂ
      (fun s : ℂ => -Complex.log (1 - χ p * ((p : ℕ) : ℂ) ^ (-s))) s := by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => 1 - χ p * ((p : ℕ) : ℂ) ^ (-s)) s :=
      (differentiableAt_const 1).sub hz
    exact ((Complex.differentiableAt_log hslit).comp s h1).neg
  exact ((hlog.sub hz).differentiableWithinAt)

/-- **The tail layer is holomorphic on the whole half plane `Re s > 1/2`, for every phase.** -/
theorem differentiableOn_helsonLogTail {χ : Nat.Primes → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1) :
    DifferentiableOn ℂ (helsonLogTail χ) {s : ℂ | 1 / 2 < s.re} := by
  intro s₁ hs₁
  have hs₁' : (1:ℝ) / 2 < s₁.re := hs₁
  set x : ℝ := (1 / 2 + s₁.re) / 2 with hxdef
  have hx : 1 / 2 < x := by rw [hxdef]; linarith
  have hxs : x < s₁.re := by rw [hxdef]; linarith
  set V : Set ℂ := {s : ℂ | x < s.re} with hVdef
  have hVopen : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVmem : s₁ ∈ V := hxs
  have hVsub : V ⊆ {s : ℂ | 1 / 2 < s.re} := fun s hs => lt_trans hx hs
  have huni : TendstoUniformlyOn
      (fun t : Finset Nat.Primes => fun s => ∑ p ∈ t, logTail (χ p * ((p : ℕ) : ℂ) ^ (-s)))
      (helsonLogTail χ) atTop V := by
    refine tendstoUniformlyOn_tsum (u := fun p : Nat.Primes =>
      (2 : ℝ) * (((p : ℕ) : ℝ) ^ (-(2 * x)))) (summable_prime_rpow_neg_two hx) ?_
    intro p s hsV
    have hsre : x < s.re := hsV
    refine le_trans (norm_logTail_prime_le hχ p (by linarith)) ?_
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
    have : ((p : ℕ) : ℝ) ^ (-(2 * s.re)) ≤ ((p : ℕ) : ℝ) ^ (-(2 * x)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    linarith
  have hdiff : DifferentiableOn ℂ (helsonLogTail χ) V := by
    refine (huni.tendstoLocallyUniformlyOn).differentiableOn ?_ hVopen
    filter_upwards with t
    have hfun : (fun s : ℂ => ∑ p ∈ t, logTail (χ p * ((p : ℕ) : ℂ) ^ (-s)))
        = ∑ p ∈ t, fun s : ℂ => logTail (χ p * ((p : ℕ) : ℂ) ^ (-s)) := by
      funext s
      simp
    rw [hfun]
    exact DifferentiableOn.sum fun p _ => (differentiableOn_logTail_prime hχ p).mono hVsub
  exact (hdiff.differentiableAt (hVopen.mem_nhds hVmem)).differentiableWithinAt


/-! ### The cube-root remainder -/

theorem norm_neg_log_le {w : ℂ} (hw : ‖w‖ ≤ 3 / 4) : ‖-Complex.log (1 - w)‖ ≤ 3 * ‖w‖ := by
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hsplit : -Complex.log (1 - w) = w + logTail w := by
    rw [logTail]; ring
  have htail : ‖logTail w‖ ≤ ‖w‖ ^ 2 / (2 * (1 - ‖w‖)) := norm_logTail_le hw1
  have hden : (1 : ℝ) / 4 ≤ 1 - ‖w‖ := by linarith
  have hnn : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
  have h2 : ‖w‖ ^ 2 / (2 * (1 - ‖w‖)) ≤ 2 * ‖w‖ ^ 2 := by
    have hpos : (0:ℝ) < 2 * (1 - ‖w‖) := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg ‖w‖]
  rw [hsplit]
  calc ‖w + logTail w‖ ≤ ‖w‖ + ‖logTail w‖ := norm_add_le _ _
    _ ≤ ‖w‖ + 2 * ‖w‖ ^ 2 := by linarith
    _ ≤ 3 * ‖w‖ := by nlinarith

/-- The cube-root remainder of the Helson Euler logarithm. -/
def helsonCubeLog (χ : Nat.Primes → ℂ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - (χ p * ((p : ℕ) : ℂ) ^ (-s)) ^ 3)

theorem norm_cube_prime_le {χ : Nat.Primes → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1) (p : Nat.Primes) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    ‖(χ p * ((p : ℕ) : ℂ) ^ (-s)) ^ 3‖ ≤ ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hpn : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  have hzn : ‖χ p * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-s.re) := by
    rw [norm_mul, hpn]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (hχ p)
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hcube : (((p : ℕ) : ℝ) ^ (-s.re)) ^ 3 = ((p : ℕ) : ℝ) ^ (-(3 * s.re)) := by
    rw [← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-s.re)) 3, ← Real.rpow_mul (by positivity)]
    norm_num
    ring_nf
  rw [norm_pow]
  calc ‖χ p * ((p : ℕ) : ℂ) ^ (-s)‖ ^ 3 ≤ (((p : ℕ) : ℝ) ^ (-s.re)) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) hzn 3
    _ = ((p : ℕ) : ℝ) ^ (-(3 * s.re)) := hcube
    _ ≤ ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)

theorem summable_helsonCubeLog {χ : Nat.Primes → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    Summable fun p : Nat.Primes => -Complex.log (1 - (χ p * ((p : ℕ) : ℂ) ^ (-s)) ^ 3) := by
  refine Summable.of_norm_bounded (g := fun p : Nat.Primes =>
    3 * (((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) ((summable_prime_rpow_neg (by norm_num)).mul_left 3)
    fun p => ?_
  have hb := norm_cube_prime_le hχ p hs
  have hb34 : ‖(χ p * ((p : ℕ) : ℂ) ^ (-s)) ^ 3‖ ≤ 3 / 4 := by
    refine le_trans hb ?_
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    calc ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) (by norm_num)
      _ ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      _ ≤ 3 / 4 := rpow_two_neg_half_le
  exact le_trans (norm_neg_log_le hb34) (by linarith)

/-- **The cube-root remainder is uniformly bounded on the closed half plane `Re s ≥ 1/2`.** -/
theorem norm_helsonCubeLog_le {χ : Nat.Primes → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    ‖helsonCubeLog χ s‖ ≤ 3 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hsum := summable_helsonCubeLog hχ hs
  have hmaj : Summable fun p : Nat.Primes => 3 * (((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (summable_prime_rpow_neg (by norm_num)).mul_left 3
  have hbound : ∀ p : Nat.Primes,
      ‖-Complex.log (1 - (χ p * ((p : ℕ) : ℂ) ^ (-s)) ^ 3)‖
        ≤ 3 * (((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
    intro p
    have hb := norm_cube_prime_le hχ p hs
    have hb34 : ‖(χ p * ((p : ℕ) : ℂ) ^ (-s)) ^ 3‖ ≤ 3 / 4 := by
      refine le_trans hb ?_
      have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
      calc ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) (by norm_num)
        _ ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
        _ ≤ 3 / 4 := rpow_two_neg_half_le
    exact le_trans (norm_neg_log_le hb34) (by linarith)
  have hnormsummable : Summable fun p : Nat.Primes =>
      ‖-Complex.log (1 - (χ p * ((p : ℕ) : ℂ) ^ (-s)) ^ 3)‖ :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound hmaj
  calc ‖helsonCubeLog χ s‖
      ≤ ∑' p : Nat.Primes, ‖-Complex.log (1 - (χ p * ((p : ℕ) : ℂ) ^ (-s)) ^ 3)‖ :=
        norm_tsum_le_tsum_norm hnormsummable
    _ ≤ ∑' p : Nat.Primes, 3 * (((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
        Summable.tsum_le_tsum hbound hnormsummable hmaj
    _ = 3 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := tsum_mul_left

/-- **The cube-root cancellation for the Helson tail layer.** -/
theorem helsonLogTail_cube {χ : Nat.Primes → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    helsonLogTail χ s + helsonLogTail (fun p => cubeRootUnit * χ p) s
        + helsonLogTail (fun p => cubeRootUnit ^ 2 * χ p) s = helsonCubeLog χ s := by
  have hχ1 : ∀ p, ‖cubeRootUnit * χ p‖ ≤ 1 := by
    intro p
    rw [norm_mul, norm_cubeRootUnit, one_mul]
    exact hχ p
  have hχ2 : ∀ p, ‖cubeRootUnit ^ 2 * χ p‖ ≤ 1 := by
    intro p
    rw [norm_mul, norm_pow, norm_cubeRootUnit, one_pow, one_mul]
    exact hχ p
  have h0 := summable_helsonLogTail hχ hs
  have h1 := summable_helsonLogTail hχ1 hs
  have h2 := summable_helsonLogTail hχ2 hs
  rw [helsonLogTail, helsonLogTail, helsonLogTail, helsonCubeLog,
    ← h0.tsum_add h1, ← (h0.add h1).tsum_add h2]
  refine tsum_congr fun p => ?_
  have hzn : ‖χ p * ((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    have hpn : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
    have : ‖χ p * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-s.re) := by
      rw [norm_mul, hpn]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (hχ p)
    have h34 : ((p : ℕ) : ℝ) ^ (-s.re) ≤ 3 / 4 := by
      have hpn' := norm_prime_cpow_le_three_quarters p hs.le
      rwa [hpn] at hpn'
    linarith
  have hassoc1 : cubeRootUnit * χ p * ((p : ℕ) : ℂ) ^ (-s)
      = cubeRootUnit * (χ p * ((p : ℕ) : ℂ) ^ (-s)) := by ring
  have hassoc2 : cubeRootUnit ^ 2 * χ p * ((p : ℕ) : ℂ) ^ (-s)
      = cubeRootUnit ^ 2 * (χ p * ((p : ℕ) : ℂ) ^ (-s)) := by ring
  rw [hassoc1, hassoc2]
  exact logTail_cube_sum hzn


/-! ### The Euler product as an exponential -/

theorem summable_prime_layer {χ : Nat.Primes → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes => χ p * ((p : ℕ) : ℂ) ^ (-s) := by
  refine Summable.of_norm_bounded (g := fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s.re))
    (summable_prime_rpow_neg hs) fun p => ?_
  have hpn : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  rw [norm_mul, hpn]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (hχ p)

/-- **The Helson Euler product is the exponential of its logarithm.** -/
theorem hasProd_helsonEuler_exp {χ : Nat.Primes → ℂ} (hχ : ∀ p, ‖χ p‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) {Gs : ℂ}
    (hG : HasSum (fun p : Nat.Primes => χ p * ((p : ℕ) : ℂ) ^ (-s)) Gs) :
    HasProd (fun p : Nat.Primes => (1 - χ p * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (Complex.exp (Gs + helsonLogTail χ s)) := by
  have hhalf : 1 / 2 < s.re := by linarith
  have hH : HasSum (fun p : Nat.Primes => logTail (χ p * ((p : ℕ) : ℂ) ^ (-s)))
      (helsonLogTail χ s) := (summable_helsonLogTail hχ hhalf).hasSum
  have hsum := hG.add hH
  have hrw : (fun p : Nat.Primes => χ p * ((p : ℕ) : ℂ) ^ (-s)
      + logTail (χ p * ((p : ℕ) : ℂ) ^ (-s)))
      = fun p : Nat.Primes => -Complex.log (1 - χ p * ((p : ℕ) : ℂ) ^ (-s)) := by
    funext p
    rw [logTail]
    ring
  rw [hrw] at hsum
  have hexp := hsum.cexp
  refine hexp.congr_fun fun p => ?_
  rw [Function.comp_apply]
  have hne : (1 : ℂ) - χ p * ((p : ℕ) : ℂ) ^ (-s) ≠ 0 :=
    one_sub_phase_prime_cpow_ne_zero hχ hs
  rw [Complex.exp_neg, Complex.exp_log hne]

end GaloisForLFunctions.HTGeometry

end

