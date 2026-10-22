import GaloisForLFunctions.RHTower.RieszFunctionMellinCriterion
import GaloisForLFunctions.RHTower.Deninger.DeningerAbelSummation
import GaloisForLFunctions.RHTower.MobiusMertensEvenConvolutionExactOrder

/-!
# The Riesz exponent law

Let `Θ = sup {Re ρ : ζ(ρ) = 0}` and let `F(x) = x Σ_n μ(n) n^{-2} e^{-x/n²}` be Riesz's function.
Then `F` grows with exponent exactly `Θ/2`:

* if `|M(N)| ≤ C (N+1)^a`, then `F(x) = O(x^{(a+δ)/2})` for every `δ > 0` (Abel summation against
  the weights `h_x(1/n²)`, `h_x(u) = u e^{-xu}`, whose consecutive differences are
  `≪ x^{-2θ} n^{4θ-3}` for every `0 ≤ θ ≤ 1`);
* with Littlewood's `M(N) = O(N^{Θ+ε})` this gives `F(x) = O(x^b)` for every `b > Θ/2`;
* conversely `F(x) = O(x^b)` forces `Θ ≤ 2b` by the Mellin continuation of the Riesz series.

Hence `Θ = 2 inf {b : F(x) = O(x^b)}`, and `Θ = ½` is Riesz's criterion: RH holds if and only if
`Σ_{k ≥ 1} (-1)^{k+1} x^k / ((k-1)! ζ(2k)) = O(x^{1/4+ε})` for every `ε > 0`.
-/

open Filter Finset
open scoped Topology

namespace RHTower

noncomputable section

/-- Increment of the Riesz weight: for `0 ≤ v ≤ u`,
`|u e^{-xu} - v e^{-xv}| ≤ (u - v)(1 + xv) e^{-xv}`. -/
theorem abs_rieszExpWeight_sub_le {x u v : ℝ} (hx : 0 ≤ x) (hv : 0 ≤ v) (hvu : v ≤ u) :
    |rieszExpWeight x u - rieszExpWeight x v| ≤ (u - v) * ((1 + x * v) * Real.exp (-(x * v))) := by
  unfold rieszExpWeight
  set E1 := Real.exp (-(x * u))
  set E2 := Real.exp (-(x * v))
  have hE1 : 0 < E1 := Real.exp_pos _
  have hE2 : 0 < E2 := Real.exp_pos _
  have h12 : E1 ≤ E2 := Real.exp_le_exp.mpr (by nlinarith)
  have hlow : E2 * (1 - x * (u - v)) ≤ E1 := by
    have h := Real.add_one_le_exp (-(x * (u - v)))
    have hsplit : E1 = E2 * Real.exp (-(x * (u - v))) := by
      simp only [E1, E2]; rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    nlinarith
  have huv : 0 ≤ u - v := by linarith
  have hxv : 0 ≤ x * v := mul_nonneg hx hv
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg huv hE1.le, mul_nonneg hv (mul_nonneg hx huv),
      mul_nonneg (mul_nonneg huv hxv) hE2.le]
  · nlinarith [mul_nonneg huv hE2.le, mul_nonneg (mul_nonneg huv hxv) hE2.le]

/-- Interpolation between `(1 + y)e^{-y} ≤ 1` and `y²(1 + y)e^{-y} ≤ 8`. -/
theorem one_add_mul_exp_neg_le_rpow {y θ : ℝ} (hy : 0 < y) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 + y) * Real.exp (-y) ≤ 8 ^ θ * y ^ (-(2 * θ)) := by
  set A := (1 + y) * Real.exp (-y) with hA_def
  have hA0 : 0 < A := by positivity
  have hA1 : A ≤ 1 := by
    rw [hA_def, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith [Real.add_one_le_exp y]
  have hA8 : y ^ 2 * A ≤ 8 := by
    have h2 := Real.pow_div_factorial_le_exp y hy.le 2
    have h3 := Real.pow_div_factorial_le_exp y hy.le 3
    simp only [Nat.factorial] at h2 h3
    norm_num at h2 h3
    have hey : y ^ 2 * A * Real.exp y = y ^ 2 * (1 + y) := by
      rw [hA_def, mul_assoc, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero]; ring
    have hpos := Real.exp_pos y
    by_contra hcon
    push Not at hcon
    nlinarith [mul_lt_mul_of_pos_right hcon hpos]
  have hsplit : y ^ (2 * θ) * A = A ^ (1 - θ) * (y ^ 2 * A) ^ θ := by
    rw [Real.mul_rpow (by positivity) hA0.le, ← Real.rpow_natCast y 2, ← Real.rpow_mul hy.le]
    have : A = A ^ (1 - θ) * A ^ θ := by
      rw [← Real.rpow_add hA0, sub_add_cancel, Real.rpow_one]
    nth_rewrite 1 [this]
    push_cast
    ring
  have hbound : y ^ (2 * θ) * A ≤ 8 ^ θ := by
    rw [hsplit]
    calc A ^ (1 - θ) * (y ^ 2 * A) ^ θ ≤ 1 * 8 ^ θ := by
          gcongr
          · exact Real.rpow_le_one hA0.le hA1 (by linarith)
      _ = 8 ^ θ := one_mul _
  have hyθ : 0 < y ^ (2 * θ) := Real.rpow_pos_of_pos hy _
  rw [Real.rpow_neg hy.le, ← div_eq_mul_inv, le_div_iff₀ hyθ]
  linarith

/-- The consecutive-weight majorant: for `n ≥ 1`, `x > 0`, `0 ≤ θ ≤ 1`, `u = 1/n²`,
`v = 1/(n+1)²`: `(u - v)(1 + xv)e^{-xv} ≤ 3 · 128^θ x^{-2θ} n^{4θ-3}`. -/
theorem inv_sq_sub_mul_one_add_mul_exp_neg_le {x θ : ℝ} (hx : 0 < x) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    (((n : ℝ) ^ 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹) *
        ((1 + x * (((n : ℝ) + 1) ^ 2)⁻¹) * Real.exp (-(x * (((n : ℝ) + 1) ^ 2)⁻¹))) ≤
      3 * 128 ^ θ * x ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ - 3) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set u : ℝ := ((n : ℝ) ^ 2)⁻¹ with hu
  set v : ℝ := (((n : ℝ) + 1) ^ 2)⁻¹ with hv
  have hv0 : 0 < v := by positivity
  have hvu : v ≤ u := inv_anti₀ (by positivity) (by nlinarith)
  have h2 := one_add_mul_exp_neg_le_rpow (mul_pos hx hv0) hθ0 hθ1
  have hdiff : u - v ≤ 3 / (n : ℝ) ^ 3 := by
    have : u - v = (2 * (n : ℝ) + 1) / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) := by
      rw [hu, hv]; field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hn0 2, pow_pos hn0 3]
  have hvpow : v ^ (-(2 * θ)) = ((n : ℝ) + 1) ^ (4 * θ) := by
    rw [hv, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    ring_nf
  have hsucc : ((n : ℝ) + 1) ^ (4 * θ) ≤ 16 ^ θ * (n : ℝ) ^ (4 * θ) := by
    calc ((n : ℝ) + 1) ^ (4 * θ) ≤ (2 * (n : ℝ)) ^ (4 * θ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ = 16 ^ θ * (n : ℝ) ^ (4 * θ) := by
          rw [Real.mul_rpow (by norm_num) hn0.le, Real.rpow_mul (by norm_num)]
          norm_num
  have hxv : (x * v) ^ (-(2 * θ)) ≤ 16 ^ θ * x ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ) := by
    rw [Real.mul_rpow hx.le hv0.le, hvpow]
    have hxpos : 0 < x ^ (-(2 * θ)) := Real.rpow_pos_of_pos hx _
    nlinarith
  have hpow : (n : ℝ) ^ (4 * θ - 3) = (n : ℝ) ^ (4 * θ) / (n : ℝ) ^ 3 := by
    rw [show (4 * θ - 3) = 4 * θ - ((3 : ℕ) : ℝ) by norm_num, Real.rpow_sub_natCast hn0.ne']
  have h128 : (128 : ℝ) ^ θ = 8 ^ θ * 16 ^ θ := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have huv0 : 0 ≤ u - v := by linarith
  have h8 : 0 ≤ (8 : ℝ) ^ θ := Real.rpow_nonneg (by norm_num) _
  calc (u - v) * ((1 + x * v) * Real.exp (-(x * v)))
      ≤ (3 / (n : ℝ) ^ 3) * (8 ^ θ * (16 ^ θ * x ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ))) := by
        exact mul_le_mul hdiff (h2.trans (mul_le_mul_of_nonneg_left hxv h8))
          (by positivity) (by positivity)
    _ = 3 * 128 ^ θ * x ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ - 3) := by
        rw [hpow, h128]; field_simp

/-- Consecutive Riesz weights: for `n ≥ 1`, `x > 0` and `0 ≤ θ ≤ 1`,
`|h_x(1/n²) - h_x(1/(n+1)²)| ≤ 3 · 128^θ x^{-2θ} n^{4θ-3}`. -/
theorem abs_rieszExpWeight_succ_sub_le {x θ : ℝ} (hx : 0 < x) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    |rieszExpWeight x ((n : ℝ) ^ 2)⁻¹ - rieszExpWeight x (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹| ≤
      3 * 128 ^ θ * x ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ - 3) := by
  push_cast
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact (abs_rieszExpWeight_sub_le hx.le (by positivity)
    (inv_anti₀ (by positivity) (by nlinarith))).trans
    (inv_sq_sub_mul_one_add_mul_exp_neg_le hx hθ0 hθ1 hn)

/-- **Abel transfer of Mertens bounds, limit form.**  Let `|M(N)| ≤ C (N+1)^a`, let the partial
sums `Σ_{n ≤ N} μ(n) f(n)` tend to `L`, let the boundary terms `M(N) f(N)` tend to `0`, and let
`|f(n) - f(n+1)| ≤ D n^{-1-δ-a}` for `n ≥ 1`.  Then `|L| ≤ 2^a C D Σ_n n^{-1-δ}`. -/
theorem abs_le_of_tendsto_of_mertens_bound {a δ C D L : ℝ} {f : ℕ → ℝ} (ha : 0 ≤ a)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ a)
    (hlim : Tendsto (fun N : ℕ => ∑ n ∈ range (N + 1),
      (ArithmeticFunction.moebius n : ℝ) * f n) atTop (𝓝 L))
    (hbd : Tendsto (fun N : ℕ => |deningerPartialSum (fun n => (ArithmeticFunction.moebius n : ℝ))
      N * f N|) atTop (𝓝 0))
    (hinc : ∀ n : ℕ, 1 ≤ n → |f n - f (n + 1)| ≤ D * (n : ℝ) ^ (-1 - δ - a)) :
    |L| ≤ 2 ^ a * C * D * ∑' n : ℕ, (n : ℝ) ^ (-1 - δ) := by
  set S : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-1 - δ)
  have hSsum : Summable fun n : ℕ => (n : ℝ) ^ (-1 - δ) :=
    Real.summable_nat_rpow.mpr (by linarith)
  set c : ℝ := 2 ^ a * C * D
  have hc0 : 0 ≤ c := by positivity
  set μr : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ)
  have hA : ∀ n : ℕ, |deningerPartialSum μr n| = ‖mobiusMertensPartialSum n‖ := by
    intro n
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    congr 1
    simp [mobiusMertensPartialSum, mobiusComplexCoefficient, deningerPartialSum, μr]
  have hA0 : deningerPartialSum μr 0 = 0 := by simp [deningerPartialSum, μr]
  have hAbound : ∀ n : ℕ, 1 ≤ n → |deningerPartialSum μr n| ≤ 2 ^ a * C * (n : ℝ) ^ a := by
    intro n hn
    rw [hA]
    refine (hM n).trans ?_
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc C * ((n : ℝ) + 1) ^ a ≤ C * (2 * (n : ℝ)) ^ a := by
          gcongr; linarith
      _ = 2 ^ a * C * (n : ℝ) ^ a := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
  have hterm : ∀ n : ℕ, |deningerPartialSum μr n * (f n - f (n + 1))| ≤
      c * (n : ℝ) ^ (-1 - δ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hA0, zero_mul, abs_zero]; positivity
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_mul]
    calc |deningerPartialSum μr n| * |f n - f (n + 1)|
        ≤ (2 ^ a * C * (n : ℝ) ^ a) * (D * (n : ℝ) ^ (-1 - δ - a)) :=
          mul_le_mul (hAbound n hn) (hinc n hn) (abs_nonneg _) (by positivity)
      _ = c * ((n : ℝ) ^ a * (n : ℝ) ^ (-1 - δ - a)) := by ring
      _ = c * (n : ℝ) ^ (-1 - δ) := by
          rw [← Real.rpow_add hn0]; congr 2; ring
  have hP : ∀ N : ℕ, |∑ n ∈ range N, deningerPartialSum μr n * (f n - f (n + 1))| ≤ c * S := by
    intro N
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun n _ => hterm n).trans ?_)
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    exact hSsum.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hle : ∀ N : ℕ, |∑ n ∈ range (N + 1), μr n * f n| ≤
      |deningerPartialSum μr N * f N| + c * S := by
    intro N
    rw [deningerAbelSummation μr f N]
    exact (abs_add_le _ _).trans (by linarith [hP N])
  have hfin := le_of_tendsto_of_tendsto' hlim.abs (hbd.add_const _) hle
  rw [zero_add] at hfin
  exact hfin

/-- **Abel transfer of Mertens bounds.**  Let `|M(N)| ≤ C (N+1)^a` and let `f` be weights with
`|f(n)| ≤ n^{-2}` and `|f(n) - f(n+1)| ≤ D n^{-1-δ-a}` for `n ≥ 1`.  Then
`|Σ_n μ(n) f(n)| ≤ 2^a C D Σ_n n^{-1-δ}`: the boundary term `M(N) f(N) = O(1/N)` vanishes. -/
theorem abs_tsum_moebius_mul_le_of_mertens_bound {a δ C D : ℝ} {f : ℕ → ℝ} (ha : 0 ≤ a)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ a)
    (hsum : Summable fun n => (ArithmeticFunction.moebius n : ℝ) * f n)
    (hf : ∀ n : ℕ, 1 ≤ n → |f n| ≤ ((n : ℝ) ^ 2)⁻¹)
    (hinc : ∀ n : ℕ, 1 ≤ n → |f n - f (n + 1)| ≤ D * (n : ℝ) ^ (-1 - δ - a)) :
    |∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * f n| ≤
      2 ^ a * C * D * ∑' n : ℕ, (n : ℝ) ^ (-1 - δ) := by
  set μr : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ)
  have hbd : Tendsto (fun N : ℕ => |deningerPartialSum μr N * f N|) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hAN : |deningerPartialSum μr N| ≤ (N : ℝ) + 1 := by
      unfold deningerPartialSum
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ n ∈ range (N + 1), |μr n| ≤ ∑ _n ∈ range (N + 1), (1 : ℝ) :=
            sum_le_sum fun n _ => by
              simp only [μr]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        _ = (N : ℝ) + 1 := by simp
    rw [abs_mul]
    calc |deningerPartialSum μr N| * |f N| ≤ ((N : ℝ) + 1) * ((N : ℝ) ^ 2)⁻¹ :=
          mul_le_mul hAN (hf N hN) (abs_nonneg _) (by positivity)
      _ ≤ 2 / (N : ℝ) := by
          rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  exact abs_le_of_tendsto_of_mertens_bound ha hδ hC hD hM
    ((tendsto_add_atTop_iff_nat 1).mpr hsum.hasSum.tendsto_sum_nat) hbd hinc

/-- **Mertens bounds transfer to the Riesz series.**  If `|M(N)| ≤ C (N+1)^a` for all `N`, then
`|R(x)| ≤ K x^{(a+δ)/2 - 1}` for all `x > 0`, for any `δ > 0` with `a + δ ≤ 2`.  Abel summation
puts the weights `h_x(1/n²)` onto the Mertens sums; consecutive weights differ by
`≪ x^{-2θ} n^{4θ-3}` with `θ = (2 - a - δ)/4`, which leaves the summable `n^{-1-δ}`. -/
theorem abs_rieszSeries_le_of_mertens_bound {a δ C : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ)
    (haδ : a + δ ≤ 2) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → |rieszSeries x| ≤ K * x ^ ((a + δ) / 2 - 1) := by
  set θ : ℝ := (2 - a - δ) / 4 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  set S : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-1 - δ)
  have hS0 : 0 ≤ S := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨2 ^ a * C * (3 * 128 ^ θ) * S, by positivity, fun x hx => ?_⟩
  have h := abs_tsum_moebius_mul_le_of_mertens_bound (f := fun n => rieszExpWeight x
    ((n : ℝ) ^ 2)⁻¹) (D := 3 * 128 ^ θ * x ^ (-(2 * θ))) ha hδ hC (by positivity) hM
    (summable_rieszTerm hx.le) (fun n hn => ?_) (fun n hn => ?_)
  · calc |rieszSeries x| ≤ 2 ^ a * C * (3 * 128 ^ θ * x ^ (-(2 * θ))) * S := h
      _ = 2 ^ a * C * (3 * 128 ^ θ) * S * x ^ ((a + δ) / 2 - 1) := by
          rw [show -(2 * θ) = (a + δ) / 2 - 1 by rw [hθ]; ring]; ring
  · simp only [rieszExpWeight]
    have hu : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    rw [abs_mul, abs_of_pos hu, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(x * ((n : ℝ) ^ 2)⁻¹)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hx hu])
    calc ((n : ℝ) ^ 2)⁻¹ * Real.exp (-(x * ((n : ℝ) ^ 2)⁻¹)) ≤ ((n : ℝ) ^ 2)⁻¹ * 1 := by
          gcongr
      _ = ((n : ℝ) ^ 2)⁻¹ := mul_one _
  · have hd := abs_rieszExpWeight_succ_sub_le hx hθ0 hθ1 hn
    rw [show 4 * θ - 3 = -1 - δ - a by rw [hθ]; ring] at hd
    exact hd

/-- The Riesz function inherits the Mertens bound: `|F(x)| ≤ K x^{(a+δ)/2}` for `x > 0`. -/
theorem abs_rieszFunction_le_of_mertens_bound {a δ C : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ)
    (haδ : a + δ ≤ 2) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → |rieszFunction x| ≤ K * x ^ ((a + δ) / 2) := by
  obtain ⟨K, hK0, hK⟩ := abs_rieszSeries_le_of_mertens_bound ha hδ haδ hC hM
  refine ⟨K, hK0, fun x hx => ?_⟩
  rw [rieszFunction, abs_mul, abs_of_pos hx]
  calc x * |rieszSeries x| ≤ x * (K * x ^ ((a + δ) / 2 - 1)) :=
        mul_le_mul_of_nonneg_left (hK x hx) hx.le
    _ = K * x ^ ((a + δ) / 2) := by
        rw [Real.rpow_sub_one hx.ne']; field_simp

/-- **Upper half of the Riesz exponent law.**  `F(x) = O(x^b)` on `[1, ∞)` for every `b > Θ/2`. -/
theorem exists_rieszFunction_le_rpow_of_zetaZeroAbscissa_lt {b : ℝ}
    (hb : zetaZeroAbscissa < 2 * b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |rieszFunction x| ≤ C * x ^ b := by
  have hΘ := half_le_zetaZeroAbscissa
  have hΘ1 := zetaZeroAbscissa_le_one
  set b' : ℝ := min b (3 / 4) with hb'
  have hb'b : b' ≤ b := min_le_left _ _
  have hb'Θ : zetaZeroAbscissa < 2 * b' := by
    rcases le_total b (3 / 4) with h | h
    · rw [hb', min_eq_left h]; exact hb
    · rw [hb', min_eq_right h]; linarith
  set ε : ℝ := 2 * b' - zetaZeroAbscissa with hε
  have hε0 : 0 < ε := by linarith
  obtain ⟨C, hC0, hC⟩ := mobiusMertens_subpower_zetaZeroAbscissa (ε / 2) (by positivity)
  obtain ⟨K, hK0, hK⟩ := abs_rieszFunction_le_of_mertens_bound (a := zetaZeroAbscissa + ε / 2)
    (δ := ε / 2) (by linarith) (by positivity) (by linarith [min_le_right b (3 / 4)]) hC0 hC
  refine ⟨K, hK0, fun x hx => (hK x (by linarith)).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ?_) hK0
  linarith

/-- **The Riesz exponent law.**  The zeta zero abscissa is twice the growth exponent of the Riesz
function: `Θ = 2 inf {b : F(x) = O(x^b) on [1, ∞)}`. -/
theorem zetaZeroAbscissa_eq_two_mul_sInf_rieszFunction_exponents :
    zetaZeroAbscissa = 2 * sInf {b : ℝ | ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |rieszFunction x| ≤ C * x ^ b} := by
  set S := {b : ℝ | ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |rieszFunction x| ≤ C * x ^ b} with hS
  have hlow : ∀ b ∈ S, zetaZeroAbscissa / 2 ≤ b := fun b ⟨C, hC⟩ => by
    have := zetaZeroAbscissa_le_of_rieszFunction_le hC
    linarith
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, _, hC⟩ := exists_rieszFunction_le_rpow_of_zetaZeroAbscissa_lt
      (b := zetaZeroAbscissa / 2 + ε) (by linarith)
    exact ⟨C, hC⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨_, hlow⟩
  have hinf : sInf S = zetaZeroAbscissa / 2 := by
    refine le_antisymm ?_ (le_csInf hne hlow)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact csInf_le hbdd (hmem ε hε)
  rw [hinf]
  ring

/-- **Riesz's criterion.**  The Riemann hypothesis holds if and only if `F(x) = O(x^{1/4+ε})` for
every `ε > 0`. -/
theorem riemannHypothesis_iff_rieszFunction_le :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |rieszFunction x| ≤ C * x ^ (1 / 4 + ε) := by
  constructor
  · intro hRH ε hε
    have hΘ := zetaZeroAbscissa_eq_half_of_riemannHypothesis hRH
    obtain ⟨C, _, hC⟩ := exists_rieszFunction_le_rpow_of_zetaZeroAbscissa_lt
      (b := 1 / 4 + ε) (by rw [hΘ]; linarith)
    exact ⟨C, hC⟩
  · intro h
    refine riemannHypothesis_of_zetaZeroAbscissa_eq_half
      (le_antisymm ?_ half_le_zetaZeroAbscissa)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, hC⟩ := h (ε / 2) (by positivity)
    have := zetaZeroAbscissa_le_of_rieszFunction_le hC
    linarith

/-- **Riesz's criterion in Riesz's form.**  The Riemann hypothesis holds if and only if
`Σ_{k ≥ 0} (-1)^k x^{k+1} / (k! ζ(2k+2)) = O(x^{1/4+ε})` for every `ε > 0`. -/
theorem riemannHypothesis_iff_rieszPowerSeries_le :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖∑' k : ℕ, (-1) ^ k * (x : ℂ) ^ (k + 1) / ((k.factorial : ℂ) * riemannZeta (2 * k + 2))‖
        ≤ C * x ^ (1 / 4 + ε) := by
  have hnorm : ∀ x : ℝ, 1 ≤ x → ‖∑' k : ℕ, (-1) ^ k * (x : ℂ) ^ (k + 1) /
      ((k.factorial : ℂ) * riemannZeta (2 * k + 2))‖ = |rieszFunction x| := fun x hx => by
    rw [← rieszFunction_eq_tsum (by linarith), Complex.norm_real, Real.norm_eq_abs]
  rw [riemannHypothesis_iff_rieszFunction_le]
  refine forall₂_congr fun ε _ => exists_congr fun C => forall₂_congr fun x hx => ?_
  rw [hnorm x hx]

end

end RHTower
