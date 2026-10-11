import GaloisForLFunctions.RHTower.WeilLinearTwistQuantization

/-!
# Linear lock phases on sparse windows are quantized

Let `G` be a Herglotz producer for the weights `lam`.  Suppose that the lower-line lock is linear
only on a sequence of windows,

`G(1 − s) = κ_j e^{iη(−τ)} G(s)`,  `s = ½ + 2iτ`,  `−Y_j ≤ τ ≤ −X_j`,

with `X_j → ∞`, windows of super-polynomial length (`Y_j ≥ (1 + X_j)^p` eventually, for every
`p`), and bounded constants `κ_j`.  Outside the windows the lock is arbitrary.

**Theorem** (`windowed_linear_lock_quantization`).  Then `e^{−η/2}` is a natural number; in
particular `η ≤ 0` (`windowed_linear_lock_slope_nonpos`).

The global linear lock of `linear_twist_quantization` is the case of one window `[1, ∞)`.  Here the
lock phase may have any behaviour between the windows, so the non-integer spectral mass of the
producer need not have a density.

**Proof.**  Assume `e^{−η/2} ∉ ℕ`.
* Along every `ε → 0⁺`, the reflected radial integral `R(ε) = ε ∫_{t<0} φ*(t) k(2t, ε + i) dt`
  tends to `2β ≠ 0` (`tendsto_lower_reflected_radial`), and the fully twisted integral
  `L(ε) = ε ∫_{t<0} φ_η(t) k(2t, ε + i) dt` tends to `0` (`tendsto_twisted_far_nonres_profile`).
* On the `j`-th window `φ* = κ_j φ_η`.  Off the window both are `O((1 + |t|)^N)` and
  `‖k(2t, ε + i)‖ ≤ 3e^{−ε|t|}`.  With `ε_j = (1 + X_j)^{−(N+2)}` the part `−X_j < t < 0` costs
  `O(1/(1 + X_j))`, and the part `t < −Y_j` costs `O((1 + X_j)^{N(N+2)} e^{−(1+X_j)/2})`.
* So `R(ε_j) − κ_j L(ε_j) → 0` and `R(ε_j) → 0`, a contradiction.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- The kernel at `ε + i`: `‖k(2t, ε + i)‖ ≤ 3e^{−ε|t|}` for `0 < ε ≤ 1`. -/
theorem norm_pairKernel_eps_one_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) :
    ‖pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)‖ ≤ 3 * Real.exp (-(ε * |t|)) := by
  set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
  have hre : τ.re = ε := by simp [hτ]
  have him : τ.im = 1 := by simp [hτ]
  have hτre : 0 < τ.re := by rw [hre]; exact hε
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    rw [him, abs_one] at h; exact h
  have hτ2 : ‖τ‖ ≤ 2 := by
    have h := norm_add_le (ε : ℂ) (((1 : ℕ) : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Nat.cast_one, norm_one,
      Real.norm_eq_abs, abs_of_pos hε] at h
    rw [hτ]; linarith
  have hτ0 : 0 < ‖τ‖ := by linarith
  refine (norm_pairKernel_two_mul_le t hτre).trans ?_
  have h1 : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)
  have h2 : Real.exp (-((2 * (τ.re / ‖τ‖)) * |t|)) ≤ Real.exp (-(ε * |t|)) := by
    apply Real.exp_le_exp.mpr
    rw [hre]
    have hq : ε ≤ 2 * (ε / ‖τ‖) := by
      rw [le_div_iff₀' hτ0] at *
      rw [mul_div_assoc', le_div_iff₀ hτ0]; nlinarith
    nlinarith [abs_nonneg t]
  have h0 : 0 ≤ ‖τ‖ ^ (-(1 / 2 : ℝ)) := by positivity
  calc 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-((2 * (τ.re / ‖τ‖)) * |t|))
      ≤ 3 * 1 * Real.exp (-(ε * |t|)) := by gcongr
    _ = 3 * Real.exp (-(ε * |t|)) := by ring

/-- `(1 + x)^N e^{−εx} ≤ (2(N+1)/ε)^N e^{−εx/2}` for `x ≥ 0`, `0 < ε ≤ 1`. -/
theorem pow_mul_exp_le_half {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ N * Real.exp (-(ε * x)) ≤
      (2 * ((N : ℝ) + 1) / ε) ^ N * Real.exp (-(ε * x / 2)) := by
  set c : ℝ := 2 * ((N : ℝ) + 1) with hc
  have hc2 : 2 ≤ c := by rw [hc]; have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
  have hc0 : 0 < c := by linarith
  have hcε : 1 ≤ c / ε := by rw [le_div_iff₀ hε]; linarith
  have hlin : 1 + x ≤ c / ε * Real.exp (ε * x / c) := by
    have he := Real.add_one_le_exp (ε * x / c)
    have hx' : c / ε * (ε * x / c + 1) = x + c / ε := by field_simp; ring
    calc 1 + x ≤ x + c / ε := by linarith
      _ = c / ε * (ε * x / c + 1) := hx'.symm
      _ ≤ c / ε * Real.exp (ε * x / c) := by gcongr
  have hpow : (1 + x) ^ N ≤ (c / ε) ^ N * Real.exp (N * (ε * x / c)) := by
    rw [Real.exp_nat_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hlin N
  have hexp : Real.exp (N * (ε * x / c)) * Real.exp (-(ε * x)) ≤ Real.exp (-(ε * x / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hNc : (N : ℝ) / c ≤ 1 / 2 := by
      rw [div_le_iff₀ hc0, hc]; linarith
    have hεx : 0 ≤ ε * x := by positivity
    have : (N : ℝ) * (ε * x / c) = (N / c) * (ε * x) := by ring
    rw [this]; nlinarith
  calc (1 + x) ^ N * Real.exp (-(ε * x))
      ≤ (c / ε) ^ N * Real.exp (N * (ε * x / c)) * Real.exp (-(ε * x)) := by gcongr
    _ = (c / ε) ^ N * (Real.exp (N * (ε * x / c)) * Real.exp (-(ε * x))) := by ring
    _ ≤ (c / ε) ^ N * Real.exp (-(ε * x / 2)) := by gcongr

end

end AbelianTwist

end RHTower
