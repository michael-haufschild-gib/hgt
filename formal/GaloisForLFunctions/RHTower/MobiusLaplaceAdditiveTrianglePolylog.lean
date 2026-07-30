import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangle

/-!
# Linear-polylog additive Möbius triangle source

This module upgrades the one-sided linear additive-triangle source to a fixed logarithmic loss.
The arithmetic condition remains finite and source-pure; its Abel transform is bounded at the
critical half-power scale with the square-root logarithmic exponent.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- One-sided linear-polylog cancellation in the cumulative additive Möbius triangle. -/
def MobiusAdditiveTriangleLinearPolylogUpperBound (q : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (mobiusAdditiveTriangle N).re ≤
      C * ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ (2 * q)

/-- A natural logarithm at discrete index `N` is controlled by the Laplace scale and the
dimensionless variable `N*x`. -/
theorem log_nat_add_two_le_laplaceScale {x : ℝ}
    (hx : 0 < x) (hxOne : x ≤ 1) (N : ℕ) :
    Real.log ((N : ℝ) + 2) ≤ 1 + |Real.log x| + (N : ℝ) * x := by
  have hNx : 0 ≤ (N : ℝ) * x := mul_nonneg (Nat.cast_nonneg N) hx.le
  have hlin : x * ((N : ℝ) + 2) ≤ 2 * ((N : ℝ) * x + 1) := by
    nlinarith
  have hexp : (N : ℝ) * x + 1 ≤ Real.exp ((N : ℝ) * x) :=
    Real.add_one_le_exp _
  have hprod : x * ((N : ℝ) + 2) ≤ 2 * Real.exp ((N : ℝ) * x) := by
    linarith
  have hdiv : (N : ℝ) + 2 ≤ (2 / x) * Real.exp ((N : ℝ) * x) := by
    rw [show (2 / x) * Real.exp ((N : ℝ) * x) =
      (2 * Real.exp ((N : ℝ) * x)) / x by field_simp]
    exact (le_div_iff₀ hx).2 (by simpa [mul_comm] using hprod)
  have hleftPos : 0 < (N : ℝ) + 2 := by positivity
  have hrightPos : 0 < (2 / x) * Real.exp ((N : ℝ) * x) :=
    mul_pos (div_pos (by norm_num) hx) (Real.exp_pos _)
  have hlog := Real.strictMonoOn_log.monotoneOn hleftPos hrightPos hdiv
  have hlogEq :
      Real.log ((2 / x) * Real.exp ((N : ℝ) * x)) =
        Real.log 2 - Real.log x + (N : ℝ) * x := by
    rw [Real.log_mul (div_ne_zero (by norm_num) hx.ne') (Real.exp_ne_zero _),
      Real.log_div (by norm_num) hx.ne', Real.log_exp]
  have hlogTwo : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    all_goals norm_num
  have hlogX : Real.log x ≤ 0 := Real.log_nonpos hx.le hxOne
  have habs : |Real.log x| = -Real.log x := abs_of_nonpos hlogX
  rw [hlogEq] at hlog
  rw [habs]
  linarith

/-- A polynomial moment can be absorbed by halving exponential decay. -/
theorem pow_mul_exp_neg_le_scaled_factorial (p : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ p * Real.exp (-y) ≤
      (p.factorial : ℝ) * 2 ^ p * Real.exp (-(y / 2)) := by
  have hhalf : 0 ≤ y / 2 := by positivity
  have hbase := pow_mul_exp_neg_le_factorial p hhalf
  calc
    y ^ p * Real.exp (-y) =
        (2 ^ p * (y / 2) ^ p) *
          (Real.exp (-(y / 2)) * Real.exp (-(y / 2))) := by
      rw [← Real.exp_add]
      congr 1
      · rw [← mul_pow]
        congr 1
        ring_nf
      · ring_nf
    _ = 2 ^ p * ((y / 2) ^ p * Real.exp (-(y / 2))) *
          Real.exp (-(y / 2)) := by ring_nf
    _ ≤ 2 ^ p * (p.factorial : ℝ) * Real.exp (-(y / 2)) := by
      gcongr
    _ = (p.factorial : ℝ) * 2 ^ p * Real.exp (-(y / 2)) := by ring_nf

/-- Summed scale-free polynomial moment bound. -/
theorem tsum_natSucc_mul_scaledMoment_exp_le (p : ℕ) {x : ℝ}
    (hx : 0 < x) (hxOne : x ≤ 1) :
    (∑' N : ℕ, ((N : ℝ) + 1) * ((N : ℝ) * x) ^ p *
      Real.exp (-((N : ℝ) * x))) ≤
      (p.factorial : ℝ) * 2 ^ p * 16 * x⁻¹ ^ 2 := by
  let K : ℝ := (p.factorial : ℝ) * 2 ^ p
  let r : ℝ := Real.exp (-(x / 2))
  have hrPos : 0 < r := Real.exp_pos _
  have hrLt : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hrAbs : |r| < 1 := by rw [abs_of_pos hrPos]; exact hrLt
  have hrNorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs] using hrAbs
  have hgeom : Summable (fun N : ℕ => r ^ N) :=
    summable_geometric_of_norm_lt_one hrNorm
  have hnat : Summable (fun N : ℕ => (N : ℝ) * r ^ N) := by
    simpa only [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrNorm
  have hsucc : Summable (fun N : ℕ => ((N : ℝ) + 1) * r ^ N) := by
    simpa only [add_mul, one_mul] using hnat.add hgeom
  have hright : Summable (fun N : ℕ =>
      K * ((N : ℝ) + 1) * Real.exp (-(((N : ℝ) * x) / 2))) := by
    have hmul := hsucc.mul_left K
    apply hmul.congr
    intro N
    have hexp : Real.exp (-(((N : ℝ) * x) / 2)) = r ^ N := by
      dsimp [r]
      rw [← Real.exp_nat_mul]
      congr 1
      ring_nf
    rw [hexp]
    ring_nf
  have hpoint (N : ℕ) :
      ((N : ℝ) + 1) * ((N : ℝ) * x) ^ p * Real.exp (-((N : ℝ) * x)) ≤
        K * ((N : ℝ) + 1) * Real.exp (-(((N : ℝ) * x) / 2)) := by
    have hmoment := pow_mul_exp_neg_le_scaled_factorial p
      (mul_nonneg (Nat.cast_nonneg N) hx.le)
    dsimp [K]
    nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) + 1 by positivity)
      (sub_nonneg.mpr hmoment)]
  have hleft : Summable (fun N : ℕ =>
      ((N : ℝ) + 1) * ((N : ℝ) * x) ^ p * Real.exp (-((N : ℝ) * x))) :=
    Summable.of_nonneg_of_le (fun N => by positivity) hpoint hright
  have hsumLe := Summable.tsum_le_tsum hpoint hleft hright
  have hrightEq :
      (∑' N : ℕ, K * ((N : ℝ) + 1) * Real.exp (-(((N : ℝ) * x) / 2))) =
        K * (1 - r)⁻¹ ^ 2 := by
    calc
      (∑' N : ℕ, K * ((N : ℝ) + 1) * Real.exp (-(((N : ℝ) * x) / 2))) =
          ∑' N : ℕ, K * (((N : ℝ) + 1) * r ^ N) := by
        apply tsum_congr
        intro N
        have hexp : Real.exp (-(((N : ℝ) * x) / 2)) = r ^ N := by
          dsimp [r]
          rw [← Real.exp_nat_mul]
          congr 1
          ring_nf
        rw [hexp]
        ring_nf
      _ = K * ∑' N : ℕ, ((N : ℝ) + 1) * r ^ N := hsucc.tsum_mul_left K
      _ = K * (1 - r)⁻¹ ^ 2 := by rw [tsum_natSucc_mul_pow_eq_inv_sq hrAbs]
  rw [hrightEq] at hsumLe
  have hxHalf : 0 < x / 2 := half_pos hx
  have hxHalfOne : x / 2 ≤ 1 := by linarith
  have hden := half_mul_le_one_sub_exp_neg hxHalf hxHalfOne
  have hdenPos : 0 < 1 - r := sub_pos.mpr hrLt
  have hinv : (1 - r)⁻¹ ≤ (x / 4)⁻¹ := by
    apply (inv_le_inv₀ hdenPos (by positivity)).2
    dsimp [r]
    linarith [hden]
  have hinvSq : (1 - r)⁻¹ ^ 2 ≤ (x / 4)⁻¹ ^ 2 := by
    gcongr
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    (∑' N : ℕ, ((N : ℝ) + 1) * ((N : ℝ) * x) ^ p *
        Real.exp (-((N : ℝ) * x))) ≤ K * (1 - r)⁻¹ ^ 2 := hsumLe
    _ ≤ K * (x / 4)⁻¹ ^ 2 := mul_le_mul_of_nonneg_left hinvSq hK
    _ = (p.factorial : ℝ) * 2 ^ p * 16 * x⁻¹ ^ 2 := by
      dsimp [K]
      field_simp
      ring_nf

/-- Absolute convergence of a linear-logarithmic exponential series at positive scale. -/
theorem summable_natSucc_mul_logPow_exp (p : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (fun N : ℕ => ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ p *
      Real.exp (-((N : ℝ) * x))) := by
  let a : ℕ := p + 1
  let D : ℝ := 2 ^ a * 2 ^ (a - 1)
  have ha : a ≠ 0 := by omega
  have h0 := summable_pow_mul_exp_neg 0 hx
  have haSum := summable_pow_mul_exp_neg a hx
  have hmajor : Summable (fun N : ℕ =>
      D * (((N : ℝ) ^ a + 1) * Real.exp (-((N : ℝ) * x)))) := by
    have hs : Summable (fun N : ℕ =>
        ((N : ℝ) ^ a + 1) * Real.exp (-((N : ℝ) * x))) := by
      simpa only [add_mul, one_mul, pow_zero] using haSum.add h0
    exact hs.mul_left D
  apply Summable.of_nonneg_of_le (fun N => by
    have hlog : 0 ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_nonneg (by
        have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith)
    positivity) (fun N => ?_) hmajor
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hlogPos : 0 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hlogLe : Real.log ((N : ℝ) + 2) ≤ (N : ℝ) + 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) + 2 by linarith)
    linarith
  have hfirst :
      ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ p ≤
        ((N : ℝ) + 2) ^ a := by
    calc
      ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ p ≤
          ((N : ℝ) + 2) * ((N : ℝ) + 2) ^ p :=
        mul_le_mul
          (by linarith : (N : ℝ) + 1 ≤ (N : ℝ) + 2)
          (pow_le_pow_left₀ hlogPos hlogLe p)
          (pow_nonneg hlogPos p) (by linarith)
      _ = ((N : ℝ) + 2) ^ a := by
        dsimp [a]
        rw [pow_succ]
        ring_nf
  have hshift : ((N : ℝ) + 2) ^ a ≤
      D * ((N : ℝ) ^ a + 1) := by
    have htwo : (N : ℝ) + 2 ≤ 2 * ((N : ℝ) + 1) := by linarith
    have hpow1 := pow_le_pow_left₀ (by positivity : 0 ≤ (N : ℝ) + 2) htwo a
    have hadd := add_pow_le hN zero_le_one a
    dsimp [D]
    calc
      ((N : ℝ) + 2) ^ a ≤ (2 * ((N : ℝ) + 1)) ^ a := hpow1
      _ = 2 ^ a * ((N : ℝ) + 1) ^ a := mul_pow _ _ _
      _ ≤ 2 ^ a * (2 ^ (a - 1) * ((N : ℝ) ^ a + 1 ^ a)) := by gcongr
      _ = 2 ^ a * 2 ^ (a - 1) * ((N : ℝ) ^ a + 1) := by ring_nf
  dsimp [D]
  calc
    ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ p *
        Real.exp (-((N : ℝ) * x)) ≤
        (2 ^ a * 2 ^ (a - 1) * ((N : ℝ) ^ a + 1)) *
          Real.exp (-((N : ℝ) * x)) :=
      mul_le_mul_of_nonneg_right (hfirst.trans hshift) (Real.exp_pos _).le
    _ = 2 ^ a * 2 ^ (a - 1) *
        (((N : ℝ) ^ a + 1) * Real.exp (-((N : ℝ) * x))) := by ring_nf

/-- Zeroth discrete exponential moment at critical scaling. -/
theorem tsum_natSucc_mul_exp_le {x : ℝ} (hx : 0 < x) (hxOne : x ≤ 1) :
    (∑' N : ℕ, ((N : ℝ) + 1) * Real.exp (-((N : ℝ) * x))) ≤
      4 * x⁻¹ ^ 2 := by
  let r : ℝ := Real.exp (-x)
  have hrPos : 0 < r := Real.exp_pos _
  have hrLt : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hrAbs : |r| < 1 := by rw [abs_of_pos hrPos]; exact hrLt
  have hsumEq :
      (∑' N : ℕ, ((N : ℝ) + 1) * Real.exp (-((N : ℝ) * x))) =
        (1 - r)⁻¹ ^ 2 := by
    calc
      (∑' N : ℕ, ((N : ℝ) + 1) * Real.exp (-((N : ℝ) * x))) =
          ∑' N : ℕ, ((N : ℝ) + 1) * r ^ N := by
        apply tsum_congr
        intro N
        congr 1
        dsimp [r]
        rw [← Real.exp_nat_mul]
        congr 1
        ring_nf
      _ = (1 - r)⁻¹ ^ 2 := tsum_natSucc_mul_pow_eq_inv_sq hrAbs
  rw [hsumEq]
  have hden := half_mul_le_one_sub_exp_neg hx hxOne
  have hdenPos : 0 < 1 - r := sub_pos.mpr hrLt
  have hinv : (1 - r)⁻¹ ≤ (x / 2)⁻¹ := by
    apply (inv_le_inv₀ hdenPos (half_pos hx)).2
    simpa [r] using hden
  have hinvSq : (1 - r)⁻¹ ^ 2 ≤ (x / 2)⁻¹ ^ 2 := by gcongr
  calc
    (1 - r)⁻¹ ^ 2 ≤ (x / 2)⁻¹ ^ 2 := hinvSq
    _ = 4 * x⁻¹ ^ 2 := by field_simp; norm_num

/-- Fixed logarithmic moments of the discrete exponential kernel have the expected
`x⁻² |log x|^p` scale. -/
theorem tsum_natSucc_mul_logPow_exp_le (p : ℕ) {x : ℝ}
    (hx : 0 < x) (hxOne : x ≤ 1) :
    (∑' N : ℕ, ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ p *
      Real.exp (-((N : ℝ) * x))) ≤
      2 ^ (p - 1) *
        (4 + (p.factorial : ℝ) * 2 ^ p * 16) *
        (1 + |Real.log x|) ^ p * x⁻¹ ^ 2 := by
  let A : ℝ := 1 + |Real.log x|
  let K : ℝ := 2 ^ (p - 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAp : 1 ≤ A ^ p := by
    have hAOne : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg (Real.log x)]
    exact one_le_pow₀ hAOne
  have hpoint (N : ℕ) :
      ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ p *
          Real.exp (-((N : ℝ) * x)) ≤
        K * (A ^ p * (((N : ℝ) + 1) * Real.exp (-((N : ℝ) * x))) +
          (((N : ℝ) + 1) * ((N : ℝ) * x) ^ p *
            Real.exp (-((N : ℝ) * x)))) := by
    have hlogPos : 0 ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_nonneg (by
        have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith)
    have hNx : 0 ≤ (N : ℝ) * x := mul_nonneg (Nat.cast_nonneg N) hx.le
    have hlog := log_nat_add_two_le_laplaceScale hx hxOne N
    have hpow : Real.log ((N : ℝ) + 2) ^ p ≤ (A + (N : ℝ) * x) ^ p :=
      pow_le_pow_left₀ hlogPos (by simpa [A, add_assoc] using hlog) p
    have hadd := add_pow_le hA hNx p
    dsimp [K]
    calc
      ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ p *
          Real.exp (-((N : ℝ) * x)) ≤
          ((N : ℝ) + 1) * (A + (N : ℝ) * x) ^ p *
            Real.exp (-((N : ℝ) * x)) := by gcongr
      _ ≤ ((N : ℝ) + 1) *
          (2 ^ (p - 1) * (A ^ p + ((N : ℝ) * x) ^ p)) *
            Real.exp (-((N : ℝ) * x)) := by gcongr
      _ = 2 ^ (p - 1) *
          (A ^ p * (((N : ℝ) + 1) * Real.exp (-((N : ℝ) * x))) +
            (((N : ℝ) + 1) * ((N : ℝ) * x) ^ p *
              Real.exp (-((N : ℝ) * x)))) := by ring_nf
  have hbase : Summable (fun N : ℕ =>
      ((N : ℝ) + 1) * Real.exp (-((N : ℝ) * x))) := by
    have h0 := summable_pow_mul_exp_neg 0 hx
    have h1 := summable_pow_mul_exp_neg 1 hx
    simpa only [pow_zero, one_mul, pow_one, add_mul] using h1.add h0
  have hmoment : Summable (fun N : ℕ =>
      ((N : ℝ) + 1) * ((N : ℝ) * x) ^ p *
        Real.exp (-((N : ℝ) * x))) := by
    have hp := summable_pow_mul_exp_neg p hx
    have hp1 := summable_pow_mul_exp_neg (p + 1) hx
    have hs := (hp1.add hp).mul_left (x ^ p)
    apply hs.congr
    intro N
    rw [mul_pow]
    ring
  have hmajor : Summable (fun N : ℕ =>
      K * (A ^ p * (((N : ℝ) + 1) * Real.exp (-((N : ℝ) * x))) +
        (((N : ℝ) + 1) * ((N : ℝ) * x) ^ p *
          Real.exp (-((N : ℝ) * x))))) := by
    exact ((hbase.mul_left (A ^ p)).add hmoment).mul_left K
  have hleft : Summable (fun N : ℕ =>
      ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ p *
        Real.exp (-((N : ℝ) * x))) :=
    Summable.of_nonneg_of_le (fun N => by
      have hlogNonneg : 0 ≤ Real.log ((N : ℝ) + 2) :=
        Real.log_nonneg (by
          have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith)
      positivity) hpoint hmajor
  have hsumLe := Summable.tsum_le_tsum hpoint hleft hmajor
  have hbaseLe := tsum_natSucc_mul_exp_le hx hxOne
  have hmomentLe := tsum_natSucc_mul_scaledMoment_exp_le p hx hxOne
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    (∑' N : ℕ, ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ p *
        Real.exp (-((N : ℝ) * x))) ≤
        ∑' N : ℕ, K *
          (A ^ p * (((N : ℝ) + 1) * Real.exp (-((N : ℝ) * x))) +
            (((N : ℝ) + 1) * ((N : ℝ) * x) ^ p *
              Real.exp (-((N : ℝ) * x)))) := hsumLe
    _ = K * (A ^ p *
          (∑' N : ℕ, ((N : ℝ) + 1) * Real.exp (-((N : ℝ) * x))) +
        (∑' N : ℕ, ((N : ℝ) + 1) * ((N : ℝ) * x) ^ p *
          Real.exp (-((N : ℝ) * x)))) := by
      have hinner := (hbase.mul_left (A ^ p)).add hmoment
      rw [hinner.tsum_mul_left K]
      congr 1
      rw [(hbase.mul_left (A ^ p)).tsum_add hmoment,
        hbase.tsum_mul_left (A ^ p)]
    _ ≤ K * (A ^ p * (4 * x⁻¹ ^ 2) +
          ((p.factorial : ℝ) * 2 ^ p * 16 * x⁻¹ ^ 2)) := by
      gcongr
    _ ≤ K * ((4 + (p.factorial : ℝ) * 2 ^ p * 16) *
          A ^ p * x⁻¹ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hK
      nlinarith [mul_nonneg
        (show 0 ≤ (p.factorial : ℝ) * 2 ^ p * 16 * x⁻¹ ^ 2 by positivity)
        (sub_nonneg.mpr hAp)]
    _ = 2 ^ (p - 1) *
        (4 + (p.factorial : ℝ) * 2 ^ p * 16) *
        (1 + |Real.log x|) ^ p * x⁻¹ ^ 2 := by
      dsimp [K, A]
      ring

/-- Generic one-sided Abel comparison: any summable upper majorant for the additive triangle
controls the real Laplace square. -/
theorem norm_sq_mobiusDiscreteLaplaceTransform_le_one_sub_exp_mul_tsum_of_triangleUpper
    (b : ℕ → ℝ)
    (hupper : ∀ N : ℕ, (mobiusAdditiveTriangle N).re ≤ b N)
    {x : ℝ} (hx : 0 < x)
    (hb : Summable (fun N : ℕ => b N * Real.exp (-((N : ℝ) * x)))) :
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      (1 - Real.exp (-x)) *
        ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := by
  let r : ℝ := Real.exp (-x)
  have hrPos : 0 < r := Real.exp_pos _
  have hrLt : r < 1 := by
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have htriangleC := summable_mobiusAdditiveTriangle_mul_exp_neg hx
  have htriangleR : Summable (fun N : ℕ =>
      (mobiusAdditiveTriangle N).re * r ^ N) := by
    have hmap := htriangleC.map Complex.reCLM Complex.reCLM.continuous
    convert hmap using 1
    funext N
    simpa [Function.comp_def, r] using
      (mobiusAdditiveTriangle_mul_exp_pow_re_eq x N).symm
  have hbPow : Summable (fun N : ℕ => b N * r ^ N) := by
    convert hb using 1
    funext N
    congr 1
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have htsumLe :
      (∑' N : ℕ, (mobiusAdditiveTriangle N).re * r ^ N) ≤
        ∑' N : ℕ, b N * r ^ N := by
    apply Summable.tsum_le_tsum (fun N => ?_) htriangleR hbPow
    exact mul_le_mul_of_nonneg_right (hupper N) (pow_nonneg hrPos.le N)
  have hleft :
      (mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x).re =
        ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 := by
    rw [Complex.mul_re, mobiusDiscreteLaplaceTransform_im_eq_zero hx,
      zero_mul, sub_zero, Complex.sq_norm, Complex.normSq_apply,
      mobiusDiscreteLaplaceTransform_im_eq_zero hx]
    ring
  have hright :
      ((1 - Complex.exp (-(x : ℂ))) *
        ∑' N : ℕ, mobiusAdditiveTriangle N * Complex.exp (-(x : ℂ)) ^ N).re =
      (1 - r) * ∑' N : ℕ, (mobiusAdditiveTriangle N).re * r ^ N := by
    rw [Complex.mul_re]
    have haRe : (1 - Complex.exp (-(x : ℂ))).re = 1 - r := by
      dsimp [r]
      rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by norm_num, Complex.exp_ofReal_re]
    have haIm : (1 - Complex.exp (-(x : ℂ))).im = 0 := by
      simp only [Complex.sub_im, Complex.one_im]
      rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by norm_num, Complex.exp_ofReal_im]
      ring
    rw [haRe, haIm, zero_mul, sub_zero, Complex.re_tsum htriangleC]
    congr 1
    apply tsum_congr
    intro N
    exact mobiusAdditiveTriangle_mul_exp_pow_re_eq x N
  have heq : ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 =
      (1 - r) * ∑' N : ℕ, (mobiusAdditiveTriangle N).re * r ^ N := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 =
          (mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x).re := hleft.symm
      _ = ((1 - Complex.exp (-(x : ℂ))) *
          ∑' N : ℕ, mobiusAdditiveTriangle N *
            Complex.exp (-(x : ℂ)) ^ N).re := by
        rw [mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_mul_tsum_additiveTriangle hx]
      _ = (1 - r) * ∑' N : ℕ,
          (mobiusAdditiveTriangle N).re * r ^ N := hright
  rw [heq]
  calc
    (1 - r) * (∑' N : ℕ, (mobiusAdditiveTriangle N).re * r ^ N) ≤
        (1 - r) * (∑' N : ℕ, b N * r ^ N) :=
      mul_le_mul_of_nonneg_left htsumLe (sub_nonneg.mpr hrLt.le)
    _ = (1 - Real.exp (-x)) *
        ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := by
      congr 1
      apply tsum_congr
      intro N
      congr 1
      dsimp [r]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Explicit constant in the linear-polylog Abel estimate. -/
def mobiusAdditiveTrianglePolylogAbelConstant (q : ℕ) : ℝ :=
  2 ^ (2 * q - 1) *
    (4 + ((2 * q).factorial : ℝ) * 2 ^ (2 * q) * 16)

/-- A one-sided linear-polylog triangle bound controls the square at the exact logarithmic scale. -/
theorem norm_sq_mobiusDiscreteLaplaceTransform_le_of_additiveTriangleLinearPolylogUpperBound
    {q : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hsource : ∀ N : ℕ, (mobiusAdditiveTriangle N).re ≤
      C * ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ (2 * q))
    {x : ℝ} (hx : 0 < x) (hxOne : x ≤ 1) :
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      C * mobiusAdditiveTrianglePolylogAbelConstant q *
        (1 + |Real.log x|) ^ (2 * q) * x⁻¹ := by
  let b : ℕ → ℝ := fun N =>
    C * ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ (2 * q)
  have hlogSum := summable_natSucc_mul_logPow_exp (2 * q) hx
  have hb : Summable (fun N : ℕ => b N * Real.exp (-((N : ℝ) * x))) := by
    have hmul := hlogSum.mul_left C
    apply hmul.congr
    intro N
    dsimp [b]
    ring
  have hsquare :=
    norm_sq_mobiusDiscreteLaplaceTransform_le_one_sub_exp_mul_tsum_of_triangleUpper
      b (by simpa only [b] using hsource) hx hb
  have hlogLe := tsum_natSucc_mul_logPow_exp_le (2 * q) hx hxOne
  have htsum :
      (∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x))) ≤
        C * (mobiusAdditiveTrianglePolylogAbelConstant q *
          (1 + |Real.log x|) ^ (2 * q) * x⁻¹ ^ 2) := by
    calc
      (∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x))) =
          C * ∑' N : ℕ, ((N : ℝ) + 1) *
            Real.log ((N : ℝ) + 2) ^ (2 * q) *
              Real.exp (-((N : ℝ) * x)) := by
        rw [← hlogSum.tsum_mul_left C]
        apply tsum_congr
        intro N
        dsimp [b]
        ring
      _ ≤ C * (2 ^ (2 * q - 1) *
          (4 + ((2 * q).factorial : ℝ) * 2 ^ (2 * q) * 16) *
          (1 + |Real.log x|) ^ (2 * q) * x⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hlogLe hC
      _ = C * (mobiusAdditiveTrianglePolylogAbelConstant q *
          (1 + |Real.log x|) ^ (2 * q) * x⁻¹ ^ 2) := by
        rw [mobiusAdditiveTrianglePolylogAbelConstant]
  have honeSub : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.one_sub_le_exp_neg x]
  calc
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
        (1 - Real.exp (-x)) *
          ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := hsquare
    _ ≤ x * (C * (mobiusAdditiveTrianglePolylogAbelConstant q *
        (1 + |Real.log x|) ^ (2 * q) * x⁻¹ ^ 2)) := by
      calc
        (1 - Real.exp (-x)) *
            (∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x))) ≤
            x * (∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x))) :=
          mul_le_mul_of_nonneg_right honeSub (tsum_nonneg fun N => by
          dsimp [b]
          have hlog : 0 ≤ Real.log ((N : ℝ) + 2) :=
            Real.log_nonneg (by
              have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
              linarith)
          positivity)
        _ ≤ x * (C * (mobiusAdditiveTrianglePolylogAbelConstant q *
            (1 + |Real.log x|) ^ (2 * q) * x⁻¹ ^ 2)) :=
          mul_le_mul_of_nonneg_left htsum hx.le
    _ = C * mobiusAdditiveTrianglePolylogAbelConstant q *
        (1 + |Real.log x|) ^ (2 * q) * x⁻¹ := by
      field_simp

theorem mobiusAdditiveTrianglePolylogAbelConstant_nonneg (q : ℕ) :
    0 ≤ mobiusAdditiveTrianglePolylogAbelConstant q := by
  rw [mobiusAdditiveTrianglePolylogAbelConstant]
  positivity

/-- **General one-sided additive-triangle source theorem.** A degree-`2q` logarithmic loss in the
finite triangle yields degree-`q` half-polylog Möbius--Laplace decay. -/
theorem mobiusAdditiveTriangleLinearPolylogUpperBound_implies_halfPolylogDecay
    {q : ℕ} (hupper : MobiusAdditiveTriangleLinearPolylogUpperBound q) :
    MobiusDiscreteLaplaceHalfPolylogDecay q := by
  rcases hupper with ⟨C, hC, hsource⟩
  let S : ℝ := C * mobiusAdditiveTrianglePolylogAbelConstant q
  let D : ℝ := (S + 1) * 2 ^ q
  have hS : 0 ≤ S := mul_nonneg hC (mobiusAdditiveTrianglePolylogAbelConstant_nonneg q)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, Real.exp (-1), hD, Real.exp_pos _, ?_⟩
  intro x hx hxDelta
  have hxOne : x ≤ 1 := by
    have hexpOne : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hlogLt : Real.log x < -1 := by
    have hmono := Real.strictMonoOn_log hx (Real.exp_pos (-1)) hxDelta
    simpa using hmono
  have hlogNeg : Real.log x < 0 := lt_trans hlogLt (by norm_num)
  have hL : 1 ≤ |Real.log x| := by
    rw [abs_of_neg hlogNeg]
    linarith
  have hsq :=
    norm_sq_mobiusDiscreteLaplaceTransform_le_of_additiveTriangleLinearPolylogUpperBound
      hC hsource hx hxOne
  have hpowLog :
      (1 + |Real.log x|) ^ (2 * q) ≤
        (2 * |Real.log x|) ^ (2 * q) := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hsq' : ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      S * (2 * |Real.log x|) ^ (2 * q) * x⁻¹ := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
          C * mobiusAdditiveTrianglePolylogAbelConstant q *
            (1 + |Real.log x|) ^ (2 * q) * x⁻¹ := hsq
      _ ≤ S * (2 * |Real.log x|) ^ (2 * q) * x⁻¹ := by
        dsimp [S]
        gcongr
  have hscaleEq :
      (2 * |Real.log x|) ^ (2 * q) =
        (2 ^ q * |Real.log x| ^ q) ^ 2 := by
    rw [show 2 * q = q * 2 by omega, pow_mul, mul_pow]
  have hrpowSq : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
    calc
      (x ^ (-(1 / 2 : ℝ))) ^ 2 =
          (x ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) :=
        (Real.rpow_natCast (x ^ (-(1 / 2 : ℝ))) 2).symm
      _ = x ^ (-(1 / 2 : ℝ) * 2) :=
        (Real.rpow_mul hx.le (-(1 / 2 : ℝ)) 2).symm
      _ = x ^ (-1 : ℝ) := by ring_nf
      _ = x⁻¹ := Real.rpow_neg_one x
  have hSle : S ≤ (S + 1) ^ 2 := by nlinarith [sq_nonneg S]
  have hscaleNonneg :
      0 ≤ (2 ^ q * |Real.log x| ^ q) ^ 2 * x⁻¹ := by positivity
  have htarget : ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      (S + 1) ^ 2 * ((2 ^ q * |Real.log x| ^ q) ^ 2 * x⁻¹) := by
    rw [hscaleEq] at hsq'
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
          S * (2 ^ q * |Real.log x| ^ q) ^ 2 * x⁻¹ := hsq'
      _ = S * ((2 ^ q * |Real.log x| ^ q) ^ 2 * x⁻¹) := by ring
      _ ≤ (S + 1) ^ 2 * ((2 ^ q * |Real.log x| ^ q) ^ 2 * x⁻¹) :=
        mul_le_mul_of_nonneg_right hSle hscaleNonneg
  have hboundSq :
      (D * mobiusLaplaceHalfPolylogKernel q x) ^ 2 =
        (S + 1) ^ 2 * ((2 ^ q * |Real.log x| ^ q) ^ 2 * x⁻¹) := by
    rw [mobiusLaplaceHalfPolylogKernel, Real.rpow_natCast]
    simp only [mul_pow]
    rw [hrpowSq]
    dsimp [D]
    ring
  have hnorm := norm_nonneg (mobiusDiscreteLaplaceTransform x)
  have hboundNonneg : 0 ≤ D * mobiusLaplaceHalfPolylogKernel q x := by
    apply mul_nonneg hD
    rw [mobiusLaplaceHalfPolylogKernel]
    positivity
  nlinarith

/-- Every one-sided linear-polylog additive-triangle source condition implies RH. -/
theorem mobiusAdditiveTriangleLinearPolylogUpperBound_implies_riemannHypothesis
    {q : ℕ} (hupper : MobiusAdditiveTriangleLinearPolylogUpperBound q) :
    RiemannHypothesis :=
  mobiusDiscreteLaplaceHalfPolylogDecay_implies_riemannHypothesis
    (mobiusAdditiveTriangleLinearPolylogUpperBound_implies_halfPolylogDecay hupper)

/-- The same source caps critical-line zero multiplicities by `q+1`. -/
theorem mobiusAdditiveTriangleLinearPolylogUpperBound_implies_RH_and_multiplicityCap
    {q : ℕ} (hupper : MobiusAdditiveTriangleLinearPolylogUpperBound q) :
    RiemannHypothesis ∧
      ∀ rho : ℂ, rho.re = 1 / 2 → riemannZeta rho = 0 →
        (analyticOrderAt riemannZeta rho).toNat ≤ q + 1 :=
  mobiusDiscreteLaplaceHalfPolylogDecay_implies_riemannHypothesis_and_multiplicityCap
    (mobiusAdditiveTriangleLinearPolylogUpperBound_implies_halfPolylogDecay hupper)

end

end RHTower
