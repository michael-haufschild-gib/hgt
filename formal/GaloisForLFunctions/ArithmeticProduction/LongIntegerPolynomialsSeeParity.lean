import GaloisForLFunctions.ArithmeticProduction.TheLengthPrecisionLaw
import GaloisForLFunctions.RHTower.LargeValues
import GaloisForLFunctions.HTGeometry.ThreeCircles
import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries
import GaloisForLFunctions.RHTower.ZetaPartialSumStrip
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount
import GaloisForLFunctions.RHTower.OffLineMomentCensusBridge

/-!
# Long integer polynomials see parity

Prime polynomials do not see parity at any height, and below the window no polynomial does.  Integer polynomials above the window do, and the mechanism is not the pole.

* **Integers** (`integral_norm_sq_integer_polynomial_le`).  At each height `T`, after removing the pole term, the second moment of `Σ_{n ≤ N} n^{−½−it}` is bounded uniformly in `N`.
* **Liouville and Möbius** (`eventually_not_uniform_liouville`, `eventually_not_uniform_moebius`).  At every large height, the second moment of `Σ_{n ≤ N} λ(n) n^{−½−it}` is unbounded in `N`, and so is that of `μ`.

So the uniform bound `sup_N ∫_T^{2T} |P_{a,N}|² < ∞` is true for the kernel `1` and false for its twist `λ`, at square-root scale, at every large height, unconditionally.  It separates a zero of `ζ` from a pole of `1/ζ`:
`ζ` is holomorphic at its zeros and `ζ(2s)/ζ(s)` is not.  This is parity away from the pole, and the only length at which it appears is unbounded.

**The mechanism** (`norm_le_of_uniform_second_moment`).  If `E(s) Σ a(n) n^{−s} = A(s)` on `Re s > 1` with `E = (s−1)ζ` and a uniform bound `B` holds on `[T, 2T]`, then

  `|A(½+x+iγ)| ≤ |E(½+x+iγ)| · √(10B + 26B/x)`.

Partial summation carries the bound to every line `Re s = ½ + x`, the Sobolev inequality makes it pointwise of size `√(B/x)`, and three circles carries the convergence from `Re s > 1` to `Re s > ½`.  At a zero of `ζ` on the line, `E` vanishes to first
order, so the right side tends to `0` as `x → 0`, while `A` does not.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower

/-- The polynomial `Σ_{n ≤ N} v(n) a(n) n^{−½−it}`. -/
def weightedPoly (a : ℕ → ℂ) (v : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (v n : ℂ) * (a n * ((n : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)))

private theorem continuous_term (a : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    Continuous fun t : ℝ => a n * ((n : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  have hne : ((n : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact_mod_cast this.ne'
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hne))

theorem continuous_weightedPoly (a : ℕ → ℂ) (v : ℕ → ℝ) (N : ℕ) : Continuous (weightedPoly a v N) := by
  unfold weightedPoly
  exact continuous_finsetSum _ fun n hn =>
    continuous_const.mul (continuous_term a (Finset.mem_Icc.mp hn).1)

/-- **Partial summation.** -/
theorem weightedPoly_eq_abel (a : ℕ → ℂ) (v : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    weightedPoly a v N t = (v N : ℂ) * linePoly a N t +
      ∑ m ∈ Finset.Ico 1 N, ((v m - v (m + 1) : ℝ) : ℂ) * linePoly a m t := by
  induction N, hN using Nat.le_induction with
  | base =>
      simp [weightedPoly, linePoly, edPoly]
  | succ N hN ih =>
      have h1 : weightedPoly a v (N + 1) t = weightedPoly a v N t +
          (v (N + 1) : ℂ) * (a (N + 1) * (((N + 1 : ℕ) : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))) := by
        unfold weightedPoly
        rw [Finset.sum_Icc_succ_top (by omega)]
      have h2 : linePoly a (N + 1) t = linePoly a N t +
          a (N + 1) * (((N + 1 : ℕ) : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
        unfold linePoly edPoly
        rw [Finset.sum_Icc_succ_top (by omega)]
      rw [h1, ih, h2, Finset.sum_Ico_succ_top hN]
      push_cast
      ring

/-- The `L²` norm of a finite combination, against the `ℓ¹` norm of its weights. -/
private theorem integral_norm_sq_sum_le (s : Finset ℕ) (w : ℕ → ℝ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) {T₁ T₂ B : ℝ} (hT : T₁ ≤ T₂)
    (hB : ∀ i ∈ s, (∫ t in T₁..T₂, ‖f i t‖ ^ 2) ≤ B) :
    (∫ t in T₁..T₂, ‖∑ i ∈ s, (w i : ℂ) * f i t‖ ^ 2) ≤ (∑ i ∈ s, |w i|) ^ 2 * B := by
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑ i ∈ s, |w i| := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hcont : Continuous fun t : ℝ => ‖∑ i ∈ s, (w i : ℂ) * f i t‖ ^ 2 :=
    (continuous_finsetSum _ fun i hi => continuous_const.mul (hf i hi)).norm.pow 2
  have hpt : ∀ t : ℝ, ‖∑ i ∈ s, (w i : ℂ) * f i t‖ ^ 2 ≤ W * ∑ i ∈ s, |w i| * ‖f i t‖ ^ 2 := by
    intro t
    have h1 : ‖∑ i ∈ s, (w i : ℂ) * f i t‖ ≤ ∑ i ∈ s, |w i| * ‖f i t‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => √|w i|) (fun i => √|w i| * ‖f i t‖)
    have h3 : ∑ i ∈ s, √|w i| * (√|w i| * ‖f i t‖) = ∑ i ∈ s, |w i| * ‖f i t‖ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
    have h4 : ∑ i ∈ s, √|w i| ^ 2 = W := by
      rw [hW]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Real.sq_sqrt (abs_nonneg _)
    have h5 : ∑ i ∈ s, (√|w i| * ‖f i t‖) ^ 2 = ∑ i ∈ s, |w i| * ‖f i t‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
    rw [h3, h4, h5] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hint : ∀ i ∈ s, IntervalIntegrable (fun t => |w i| * ‖f i t‖ ^ 2) volume T₁ T₂ := fun i hi =>
    (continuous_const.mul ((hf i hi).norm.pow 2)).intervalIntegrable _ _
  have hc2 : Continuous fun t : ℝ => W * ∑ i ∈ s, |w i| * ‖f i t‖ ^ 2 :=
    continuous_const.mul (continuous_finsetSum _ fun i hi =>
      continuous_const.mul ((hf i hi).norm.pow 2))
  have hmono : (∫ t in T₁..T₂, ‖∑ i ∈ s, (w i : ℂ) * f i t‖ ^ 2) ≤
      ∫ t in T₁..T₂, W * ∑ i ∈ s, |w i| * ‖f i t‖ ^ 2 :=
    intervalIntegral.integral_mono_on hT (hcont.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)
      (fun t _ => hpt t)
  rw [← hW]
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hint]
  have h6 : ∑ i ∈ s, (∫ t in T₁..T₂, |w i| * ‖f i t‖ ^ 2) ≤ ∑ i ∈ s, |w i| * B := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hB i hi) (abs_nonneg _)
  rw [← Finset.sum_mul, ← hW] at h6
  calc W * ∑ i ∈ s, (∫ t in T₁..T₂, |w i| * ‖f i t‖ ^ 2) ≤ W * (W * B) :=
        mul_le_mul_of_nonneg_left h6 hW0
    _ = _ := by rw [sq, mul_assoc]

private theorem sum_Ico_abs_sub_eq {v : ℕ → ℝ} (hmono : ∀ m, 1 ≤ m → v m ≤ v (m + 1)) {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Ico 1 N, |v m - v (m + 1)| = v N - v 1 := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, ih, abs_of_nonpos (by linarith [hmono N hN])]
      ring

private theorem norm_sq_add_le (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 := norm_add_le x y
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem integral_add_norm_sq_le {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) {T₁ T₂ B₁ B₂ : ℝ}
    (hT : T₁ ≤ T₂) (h1 : (∫ t in T₁..T₂, ‖f t‖ ^ 2) ≤ B₁) (h2 : (∫ t in T₁..T₂, ‖g t‖ ^ 2) ≤ B₂) :
    (∫ t in T₁..T₂, ‖f t + g t‖ ^ 2) ≤ 2 * B₁ + 2 * B₂ := by
  have hc1 : Continuous fun t : ℝ => ‖f t + g t‖ ^ 2 := (hf.add hg).norm.pow 2
  have hA : IntervalIntegrable (fun t : ℝ => 2 * ‖f t‖ ^ 2) volume T₁ T₂ :=
    (continuous_const.mul (hf.norm.pow 2)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun t : ℝ => 2 * ‖g t‖ ^ 2) volume T₁ T₂ :=
    (continuous_const.mul (hg.norm.pow 2)).intervalIntegrable _ _
  have hmono : (∫ t in T₁..T₂, ‖f t + g t‖ ^ 2) ≤ ∫ t in T₁..T₂, (2 * ‖f t‖ ^ 2 + 2 * ‖g t‖ ^ 2) :=
    intervalIntegral.integral_mono_on hT (hc1.intervalIntegrable _ _) (hA.add hB)
      (fun t _ => norm_sq_add_le (f t) (g t))
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add hA hB, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  linarith

/-- A monotone weight in `[0, 1]` costs a factor of `4`. -/
theorem integral_norm_sq_weightedPoly_le {a : ℕ → ℂ} {v : ℕ → ℝ} (hmono : ∀ m, 1 ≤ m → v m ≤ v (m + 1))
    (h0 : ∀ m, 1 ≤ m → 0 ≤ v m) (h1 : ∀ m, 1 ≤ m → v m ≤ 1) {N : ℕ} (hN : 1 ≤ N) {T₁ T₂ B : ℝ}
    (hT : T₁ ≤ T₂) (hB0 : 0 ≤ B) (hB : ∀ m, 1 ≤ m → (∫ t in T₁..T₂, ‖linePoly a m t‖ ^ 2) ≤ B) :
    (∫ t in T₁..T₂, ‖weightedPoly a v N t‖ ^ 2) ≤ 4 * B := by
  simp_rw [weightedPoly_eq_abel a v hN]
  have hTV : ∑ m ∈ Finset.Ico 1 N, |v m - v (m + 1)| ≤ 1 := by
    rw [sum_Ico_abs_sub_eq hmono hN]
    linarith [h1 N hN, h0 1 le_rfl]
  have hTV0 : 0 ≤ ∑ m ∈ Finset.Ico 1 N, |v m - v (m + 1)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hfirst : (∫ t in T₁..T₂, ‖(v N : ℂ) * linePoly a N t‖ ^ 2) ≤ B := by
    have hval : ∀ t, ‖(v N : ℂ) * linePoly a N t‖ ^ 2 = v N ^ 2 * ‖linePoly a N t‖ ^ 2 := by
      intro t
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp_rw [hval]
    rw [intervalIntegral.integral_const_mul]
    have h2 : v N ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ (h0 N hN) (h1 N hN) 2
      simpa using this
    have h3 := hB N hN
    have h4 : 0 ≤ ∫ t in T₁..T₂, ‖linePoly a N t‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT fun t _ => by positivity
    nlinarith
  have hsecond := integral_norm_sq_sum_le (Finset.Ico 1 N) (fun m => v m - v (m + 1))
    (fun m => linePoly a m) (fun m _ => continuous_linePoly a m) hT
    (fun m hm => hB m (Finset.mem_Ico.mp hm).1)
  have hsq : (∑ m ∈ Finset.Ico 1 N, |v m - v (m + 1)|) ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ hTV0 hTV 2
    simpa using this
  have hsecond' := hsecond.trans (mul_le_of_le_one_left hB0 hsq)
  have hcont2 : Continuous fun t : ℝ => ∑ m ∈ Finset.Ico 1 N, ((v m - v (m + 1) : ℝ) : ℂ) * linePoly a m t :=
    continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_linePoly a m)
  have h := integral_add_norm_sq_le (f := fun t => (v N : ℂ) * linePoly a N t) (continuous_const.mul
    (continuous_linePoly a N)) hcont2 hT hfirst hsecond'
  exact h.trans (le_of_eq (by ring))

/-! ### The shifted lines -/

private theorem cpow_natReal {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    ((n : ℝ) : ℂ) ^ z = Complex.exp ((Real.log n : ℂ) * z) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le]

private theorem cpow_shift {n : ℕ} (hn : 1 ≤ n) (x t : ℝ) :
    ((n : ℝ) : ℂ) ^ (-(((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I)) =
      (((n : ℝ) ^ (-x) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [cpow_natReal hn, cpow_natReal hn, Real.rpow_def_of_pos hpos, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The line `Re s = ½ + x` as a weighted polynomial. -/
theorem edPoly_shift_eq (a : ℕ → ℂ) (N : ℕ) (x t : ℝ) :
    edPoly a (Finset.Icc 1 N) (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I) =
      weightedPoly a (fun n => (n : ℝ) ^ (-x)) N t := by
  unfold edPoly weightedPoly
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [cpow_shift (Finset.mem_Icc.mp hn).1]
  ring

/-- The derivative in the height of the line. -/
theorem hasDerivAt_edPoly_shift (a : ℕ → ℂ) (N : ℕ) (x t : ℝ) :
    HasDerivAt (fun u : ℝ => edPoly a (Finset.Icc 1 N) (((1 / 2 + x : ℝ) : ℂ) + (u : ℂ) * I))
      (-I * weightedPoly a (fun n => Real.log n * (n : ℝ) ^ (-x)) N t) t := by
  unfold edPoly weightedPoly
  rw [Finset.mul_sum]
  refine HasDerivAt.fun_sum fun n hn => ?_
  have hn1 := (Finset.mem_Icc.mp hn).1
  obtain ⟨L, hL⟩ : ∃ L : ℂ, L = ((Real.log n : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℂ, σ = ((1 / 2 + x : ℝ) : ℂ) := ⟨_, rfl⟩
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) ((1 : ℝ) : ℂ) t := (hasDerivAt_id t).ofReal_comp
  have hlin := (hid.const_mul (-L * I)).add_const (-L * σ)
  have hexpd := hlin.cexp
  have hfun : (fun u : ℝ => a n * ((n : ℝ) : ℂ) ^ (-(((1 / 2 + x : ℝ) : ℂ) + (u : ℂ) * I))) =
      fun u : ℝ => a n * Complex.exp (-L * I * (u : ℂ) + -L * σ) := by
    funext u
    rw [cpow_natReal hn1, ← hL, ← hσ]
    congr 2
    ring
  rw [hfun]
  refine (hexpd.const_mul (a n)).congr_deriv ?_
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hexp : Complex.exp (-L * I * (t : ℂ) + -L * σ) =
      (((n : ℝ) ^ (-x) : ℝ) : ℂ) * Complex.exp (L * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    rw [Real.rpow_def_of_pos hpos, Complex.ofReal_exp, ← Complex.exp_add, hL, hσ]
    congr 1
    push_cast
    ring
  rw [hexp, cpow_natReal hn1, ← hL]
  beta_reduce
  push_cast
  rw [hL]
  push_cast
  ring

private theorem one_sub_rpow_mono {x : ℝ} (hx : 0 < x) (m : ℕ) (hm : 1 ≤ m) :
    1 - (m : ℝ) ^ (-x) ≤ 1 - ((m + 1 : ℕ) : ℝ) ^ (-x) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.rpow_le_rpow_of_nonpos hm0 (by push_cast; linarith : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ))
    (by linarith : -x ≤ 0)
  linarith

private theorem rpow_neg_mem {x : ℝ} (hx : 0 < x) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ (m : ℝ) ^ (-x) ∧ (m : ℝ) ^ (-x) ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact ⟨Real.rpow_nonneg (by linarith) _, Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)⟩

/-- `(1 + y) e^{−y}` is antitone on `y ≥ 0`, with values in `[0, 1]`. -/
private theorem one_add_mul_exp_neg_anti {y₁ y₂ : ℝ} (h1 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) :
    (1 + y₂) * Real.exp (-y₂) ≤ (1 + y₁) * Real.exp (-y₁) := by
  have h3 : 1 + (y₂ - y₁) ≤ Real.exp (y₂ - y₁) := by linarith [Real.add_one_le_exp (y₂ - y₁)]
  have h4 : 1 + y₂ ≤ (1 + y₁) * Real.exp (y₂ - y₁) := by
    have h5 := mul_le_mul_of_nonneg_left h3 (by linarith : 0 ≤ 1 + y₁)
    have h6 : 0 ≤ y₁ * (y₂ - y₁) := mul_nonneg h1 (by linarith)
    nlinarith
  have h7 := mul_le_mul_of_nonneg_right h4 (Real.exp_pos (-y₂)).le
  refine h7.trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The monotone part `1 − n^{−x}(1 + x log n)`. -/
private def secondWeight (x : ℝ) (n : ℕ) : ℝ := 1 - (n : ℝ) ^ (-x) * (1 + x * Real.log n)

private theorem secondWeight_eq {x : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    secondWeight x n = 1 - (1 + x * Real.log n) * Real.exp (-(x * Real.log n)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold secondWeight
  rw [Real.rpow_def_of_pos hpos]
  have h : Real.log n * -x = -(x * Real.log n) := by ring
  rw [h]
  ring

private theorem secondWeight_mono {x : ℝ} (hx : 0 < x) (m : ℕ) (hm : 1 ≤ m) :
    secondWeight x m ≤ secondWeight x (m + 1) := by
  rw [secondWeight_eq hm, secondWeight_eq (by omega)]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : Real.log m ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log hm0 (by push_cast; linarith)
  have h0 : 0 ≤ x * Real.log m := mul_nonneg hx.le (Real.log_nonneg (by exact_mod_cast hm))
  have h := one_add_mul_exp_neg_anti h0 (mul_le_mul_of_nonneg_left h1 hx.le)
  linarith

private theorem secondWeight_mem {x : ℝ} (hx : 0 < x) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ secondWeight x m ∧ secondWeight x m ≤ 1 := by
  rw [secondWeight_eq hm]
  have h0 : 0 ≤ x * Real.log m := mul_nonneg hx.le (Real.log_nonneg (by exact_mod_cast hm))
  have h1 := one_add_mul_exp_neg_anti le_rfl h0
  simp only [neg_zero, Real.exp_zero, add_zero, mul_one] at h1
  have h2 : 0 ≤ (1 + x * Real.log m) * Real.exp (-(x * Real.log m)) := by positivity
  constructor <;> linarith

/-- The shifted line inherits a uniform bound. -/
theorem integral_norm_sq_shift_le {a : ℕ → ℂ} {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) {T₁ T₂ B : ℝ}
    (hT : T₁ ≤ T₂) (hB0 : 0 ≤ B) (hB : ∀ m, 1 ≤ m → (∫ t in T₁..T₂, ‖linePoly a m t‖ ^ 2) ≤ B) :
    (∫ t in T₁..T₂, ‖weightedPoly a (fun n => (n : ℝ) ^ (-x)) N t‖ ^ 2) ≤ 10 * B := by
  have h1 := integral_norm_sq_weightedPoly_le (a := a) (v := fun n => 1 - (n : ℝ) ^ (-x))
    (one_sub_rpow_mono hx) (fun m hm => by linarith [(rpow_neg_mem hx hm).2])
    (fun m hm => by linarith [(rpow_neg_mem hx hm).1]) hN hT hB0 hB
  have hval : ∀ t, weightedPoly a (fun n => (n : ℝ) ^ (-x)) N t =
      linePoly a N t + (-1 : ℂ) * weightedPoly a (fun n => 1 - (n : ℝ) ^ (-x)) N t := by
    intro t
    have h2 : linePoly a N t = weightedPoly a (fun _ => 1) N t := by
      unfold linePoly edPoly weightedPoly
      refine Finset.sum_congr rfl fun n _ => ?_
      simp
    rw [h2]
    unfold weightedPoly
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  simp_rw [hval]
  have h3 : (∫ t in T₁..T₂, ‖(-1 : ℂ) * weightedPoly a (fun n => 1 - (n : ℝ) ^ (-x)) N t‖ ^ 2) ≤ 4 * B := by
    simpa using h1
  have h := integral_add_norm_sq_le (g := fun t => (-1 : ℂ) * weightedPoly a (fun n => 1 - (n : ℝ) ^ (-x)) N t)
    (continuous_linePoly a N) (continuous_const.mul (continuous_weightedPoly a _ N)) hT (hB N hN) h3
  exact h.trans (le_of_eq (by ring))

/-- The derivative on the shifted line costs `1/x²`. -/
theorem integral_norm_sq_shift_deriv_le {a : ℕ → ℂ} {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) {T₁ T₂ B : ℝ}
    (hT : T₁ ≤ T₂) (hB0 : 0 ≤ B) (hB : ∀ m, 1 ≤ m → (∫ t in T₁..T₂, ‖linePoly a m t‖ ^ 2) ≤ B) :
    (∫ t in T₁..T₂, ‖weightedPoly a (fun n => Real.log n * (n : ℝ) ^ (-x)) N t‖ ^ 2) ≤ 16 * B / x ^ 2 := by
  have h1 := integral_norm_sq_weightedPoly_le (a := a) (v := fun n => 1 - (n : ℝ) ^ (-x))
    (one_sub_rpow_mono hx) (fun m hm => by linarith [(rpow_neg_mem hx hm).2])
    (fun m hm => by linarith [(rpow_neg_mem hx hm).1]) hN hT hB0 hB
  have h2 := integral_norm_sq_weightedPoly_le (a := a) (v := secondWeight x)
    (secondWeight_mono hx) (fun m hm => (secondWeight_mem hx hm).1)
    (fun m hm => (secondWeight_mem hx hm).2) hN hT hB0 hB
  have hne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hval : ∀ t, weightedPoly a (fun n => Real.log n * (n : ℝ) ^ (-x)) N t =
      ((1 / x : ℝ) : ℂ) * (weightedPoly a (fun n => 1 - (n : ℝ) ^ (-x)) N t +
        (-1 : ℂ) * weightedPoly a (secondWeight x) N t) := by
    intro t
    unfold weightedPoly
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold secondWeight
    push_cast
    field_simp
    ring
  simp_rw [hval]
  have hnorm : ∀ t, ‖((1 / x : ℝ) : ℂ) * (weightedPoly a (fun n => 1 - (n : ℝ) ^ (-x)) N t +
      (-1 : ℂ) * weightedPoly a (secondWeight x) N t)‖ ^ 2 =
      (1 / x ^ 2) * ‖weightedPoly a (fun n => 1 - (n : ℝ) ^ (-x)) N t +
        (-1 : ℂ) * weightedPoly a (secondWeight x) N t‖ ^ 2 := by
    intro t
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    congr 1
    field_simp
  simp_rw [hnorm]
  rw [intervalIntegral.integral_const_mul]
  have h3 : (∫ t in T₁..T₂, ‖(-1 : ℂ) * weightedPoly a (secondWeight x) N t‖ ^ 2) ≤ 4 * B := by
    simpa using h2
  have h4 := integral_add_norm_sq_le (g := fun t => (-1 : ℂ) * weightedPoly a (secondWeight x) N t)
    (continuous_weightedPoly a _ N) (continuous_const.mul (continuous_weightedPoly a _ N)) hT h1 h3
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 1 / x ^ 2)
  refine h5.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The pointwise bound on a shifted line.** -/
theorem norm_sq_edPoly_shift_le {a : ℕ → ℂ} {x c B : ℝ} (hx : 0 < x) (hB0 : 0 ≤ B)
    (hB : ∀ m, 1 ≤ m → (∫ t in c..(c + 1), ‖linePoly a m t‖ ^ 2) ≤ B) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Icc c (c + 1)) :
    ‖edPoly a (Finset.Icc 1 N) (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ 10 * B + 26 * B / x := by
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℂ, F = fun u : ℝ => edPoly a (Finset.Icc 1 N) (((1 / 2 + x : ℝ) : ℂ) + (u : ℂ) * I) :=
    ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ → ℂ, W = weightedPoly a (fun n => Real.log n * (n : ℝ) ^ (-x)) N := ⟨_, rfl⟩
  have hFv : ∀ u, F u = weightedPoly a (fun n => (n : ℝ) ^ (-x)) N u := by
    intro u
    rw [hF]
    exact edPoly_shift_eq a N x u
  have hFc : Continuous F := by
    have : F = weightedPoly a (fun n => (n : ℝ) ^ (-x)) N := funext hFv
    rw [this]
    exact continuous_weightedPoly a _ N
  have hWc : Continuous W := by
    rw [hW]
    exact continuous_weightedPoly a _ N
  have hF'c : Continuous fun u => -I * W u := continuous_const.mul hWc
  have hderiv : ∀ y ∈ uIcc c (c + 1), HasDerivAt F (-I * W y) y := by
    intro y _
    rw [hF, hW]
    exact hasDerivAt_edPoly_shift a N x y
  have hc1 : c ≤ c + 1 := by linarith
  have hsob := sobolev_pointwise (f := F) (f' := fun u => -I * W u) (c := c) (δ := 1) one_pos hderiv
    ((continuous_const.mul (hFc.inner hF'c)).intervalIntegrable _ _)
    ((hFc.norm.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul (hFc.norm.mul hF'c.norm)).intervalIntegrable _ _) ht
  have hI1 : (∫ u in c..(c + 1), ‖F u‖ ^ 2) ≤ 10 * B := by
    simp_rw [hFv]
    exact integral_norm_sq_shift_le hx hN hc1 hB0 hB
  have hI2 : (∫ u in c..(c + 1), ‖W u‖ ^ 2) ≤ 16 * B / x ^ 2 := by
    rw [hW]
    exact integral_norm_sq_shift_deriv_le hx hN hc1 hB0 hB
  have hcross : (∫ u in c..(c + 1), 2 * (‖F u‖ * ‖-I * W u‖)) ≤
      1 / x * (∫ u in c..(c + 1), ‖F u‖ ^ 2) + x * ∫ u in c..(c + 1), ‖W u‖ ^ 2 := by
    have hA1 : IntervalIntegrable (fun u : ℝ => 1 / x * ‖F u‖ ^ 2) volume c (c + 1) :=
      (continuous_const.mul (hFc.norm.pow 2)).intervalIntegrable _ _
    have hA2 : IntervalIntegrable (fun u : ℝ => x * ‖W u‖ ^ 2) volume c (c + 1) :=
      (continuous_const.mul (hWc.norm.pow 2)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hA1 hA2]
    refine intervalIntegral.integral_mono_on hc1
      ((continuous_const.mul (hFc.norm.mul hF'c.norm)).intervalIntegrable _ _) (hA1.add hA2) fun u _ => ?_
    have hn : ‖-I * W u‖ = ‖W u‖ := by simp
    rw [hn]
    have h1 : (‖F u‖ - x * ‖W u‖) ^ 2 / x = 1 / x * ‖F u‖ ^ 2 + x * ‖W u‖ ^ 2 - 2 * (‖F u‖ * ‖W u‖) := by
      field_simp
      ring
    have h2 : 0 ≤ (‖F u‖ - x * ‖W u‖) ^ 2 / x := by positivity
    linarith
  have hgoal : ‖F t‖ ^ 2 ≤ 10 * B + 26 * B / x := by
    have h3 : 1 / x * (∫ u in c..(c + 1), ‖F u‖ ^ 2) ≤ 1 / x * (10 * B) :=
      mul_le_mul_of_nonneg_left hI1 (by positivity)
    have h4 : x * (∫ u in c..(c + 1), ‖W u‖ ^ 2) ≤ x * (16 * B / x ^ 2) :=
      mul_le_mul_of_nonneg_left hI2 hx.le
    have h5 : x * (16 * B / x ^ 2) = 16 * B / x := by
      field_simp
    have h6 : 1 / x * (10 * B) = 10 * B / x := by ring
    have h7 : 26 * B / x = 10 * B / x + 16 * B / x := by ring
    rw [one_div_one, one_mul] at hsob
    linarith
  rw [hF] at hgoal
  exact hgoal

/-! ### The partial sums in the half-plane of absolute convergence -/

/-- The tail of `Σ 1/n²`. -/
private def tailTwo (N : ℕ) : ℝ := (∑' n : ℕ, 1 / (n : ℝ) ^ 2) - ∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ) ^ 2

private theorem summable_one_div_sq : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
  Real.summable_one_div_nat_pow.mpr one_lt_two

private theorem tendsto_tailTwo : Tendsto tailTwo atTop (𝓝 0) := by
  have h := (tendsto_add_atTop_iff_nat 1).mpr summable_one_div_sq.hasSum.tendsto_sum_nat
  have h2 := (tendsto_const_nhds (x := ∑' n : ℕ, 1 / (n : ℝ) ^ 2)).sub h
  rw [sub_self] at h2
  exact h2

/-- On `Re s ≥ 2` the partial sums converge at a uniform rate. -/
private theorem norm_edPoly_sub_LSeries_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) {s : ℂ} (hs : 2 ≤ s.re) (N : ℕ) :
    ‖edPoly a (Finset.Icc 1 N) s - LSeries a s‖ ≤ tailTwo N := by
  have hterm : ∀ n : ℕ, ‖LSeries.term a s n‖ ≤ 1 / (n : ℝ) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn.ne', norm_div, Complex.norm_natCast_cpow_of_pos hn]
    have h1 : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hn1 hs
    have h2 : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h2] at h1
    exact div_le_div₀ (by norm_num) (ha n) (by positivity) h1
  have hsum : Summable (LSeries.term a s) :=
    Summable.of_norm_bounded summable_one_div_sq hterm
  have hlim := hsum.hasSum.tendsto_sum_nat
  have hlim2 : Tendsto (fun M : ℕ => edPoly a (Finset.Icc 1 N) s - ∑ n ∈ Finset.range M, LSeries.term a s n) atTop
      (𝓝 (edPoly a (Finset.Icc 1 N) s - LSeries a s)) := tendsto_const_nhds.sub hlim
  refine le_of_tendsto hlim2.norm ?_
  have hpart : edPoly a (Finset.Icc 1 N) s = ∑ n ∈ Finset.range (N + 1), LSeries.term a s n := by
    have h1 : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [h1, Finset.sum_insert (by simp), LSeries.term_zero, zero_add]
    unfold edPoly
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 := (Finset.mem_Icc.mp hn).1
    rw [LSeries.term_of_ne_zero (by omega), Complex.cpow_neg, div_eq_mul_inv]
    push_cast
    rfl
  filter_upwards [eventually_ge_atTop (N + 1)] with M hM
  have hcancel : ∀ A B : ℂ, A - (B + A) = -B := fun A B => by ring
  rw [hpart, ← Finset.sum_sdiff (Finset.range_subset_range.mpr hM), hcancel, norm_neg]
  have h1 : ‖∑ n ∈ Finset.range M \ Finset.range (N + 1), LSeries.term a s n‖ ≤
      ∑ n ∈ Finset.range M \ Finset.range (N + 1), 1 / (n : ℝ) ^ 2 :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => hterm n)
  refine h1.trans ?_
  have h2 := Finset.sum_sdiff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) (Finset.range_subset_range.mpr hM)
  have h3 : ∑ n ∈ Finset.range M, 1 / (n : ℝ) ^ 2 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
    summable_one_div_sq.sum_le_tsum _ fun n _ => by positivity
  unfold tailTwo
  linarith

/-! ### The mechanism -/

/-- **The mechanism.**  A uniform second-moment bound forces `|A| ≤ |E| √(10B + 26B/x)` on `Re s = ½ + x` at heights inside the window. -/
theorem norm_le_of_uniform_second_moment {A : ℂ → ℂ} {a' : ℕ → ℂ} (ha : ∀ n, ‖a' n‖ ≤ 1)
    (hA : ∀ s : ℂ, 1 / 2 < s.re → 0 < s.im → DifferentiableAt ℂ A s)
    (hEA : ∀ s : ℂ, 1 < s.re → zetaEntire s * LSeries a' s = A s) {T B γ x : ℝ}
    (hB : ∀ m, 1 ≤ m → (∫ t in T..(2 * T), ‖linePoly a' m t‖ ^ 2) ≤ B)
    (hγ1 : T + 3 ≤ γ) (hγ2 : γ ≤ 2 * T - 4) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ‖A (((1 / 2 + x : ℝ) : ℂ) + (γ : ℂ) * I)‖ ≤
      ‖zetaEntire (((1 / 2 + x : ℝ) : ℂ) + (γ : ℂ) * I)‖ * √(10 * B + 26 * B / x) := by
  have hT2 : T ≤ 2 * T := by linarith
  have hB0 : 0 ≤ B := (intervalIntegral.integral_nonneg hT2 fun t _ => by positivity).trans (hB 1 le_rfl)
  -- `L²` on every unit cell inside the window
  have hcell : ∀ u : ℝ, T ≤ u → u + 1 ≤ 2 * T → ∀ m, 1 ≤ m →
      (∫ t in u..(u + 1), ‖linePoly a' m t‖ ^ 2) ≤ B := by
    intro u hu1 hu2 m hm
    have hnn : ∀ t : ℝ, (0 : ℝ) ≤ ‖linePoly a' m t‖ ^ 2 := fun t => by positivity
    exact (intervalIntegral.integral_mono_interval (μ := volume) hu1 (by linarith) hu2
      (Filter.Eventually.of_forall hnn)
      (((continuous_linePoly a' m).norm.pow 2).intervalIntegrable _ _)).trans (hB m hm)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (3 : ℂ) + (γ : ℂ) * I := ⟨_, rfl⟩
  have hcre : c.re = 3 := by simp [hc]
  have hcim : c.im = γ := by simp [hc]
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℂ, s₀ = ((1 / 2 + x : ℝ) : ℂ) + (γ : ℂ) * I := ⟨_, rfl⟩
  rw [← hs₀]
  have hs₀c : ‖s₀ - c‖ = 5 / 2 - x := by
    have h1 : s₀ - c = ((-(5 / 2 - x) : ℝ) : ℂ) := by
      rw [hs₀, hc]
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith)]
  -- geometry of the discs
  have hgeo : ∀ {s : ℂ} {ρ : ℝ}, ‖s - c‖ ≤ ρ → 3 - ρ ≤ s.re ∧ γ - ρ ≤ s.im ∧ s.im ≤ γ + ρ := by
    intro s ρ h
    have h1 := (Complex.abs_re_le_norm (s - c)).trans h
    have h2 := (Complex.abs_im_le_norm (s - c)).trans h
    rw [Complex.sub_re, hcre] at h1
    rw [Complex.sub_im, hcim] at h2
    obtain ⟨h3, -⟩ := abs_le.mp h1
    obtain ⟨h4, h5⟩ := abs_le.mp h2
    exact ⟨by linarith, by linarith, by linarith⟩
  -- bounds on the discs
  have hzeta_cont : ContinuousOn zetaEntire (Metric.closedBall c 3) :=
    differentiable_zetaEntire.continuous.continuousOn
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall c 3).exists_bound_of_continuousOn hzeta_cont
  have hC₀0 : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ c (Metric.mem_closedBall_self (by norm_num)))
  have hA_cont : ContinuousOn A (Metric.closedBall c (5 / 2 - x / 2)) := by
    intro s hs
    have h1 := hgeo (s := s) (ρ := 5 / 2 - x / 2) (by simpa [dist_eq_norm] using hs)
    exact (hA s (by linarith [h1.1]) (by linarith [h1.2.1])).continuousAt.continuousWithinAt
  obtain ⟨C_A, hC_A⟩ := (isCompact_closedBall c (5 / 2 - x / 2)).exists_bound_of_continuousOn hA_cont
  have hC_A0 : 0 ≤ C_A := (norm_nonneg _).trans
    (hC_A c (Metric.mem_closedBall_self (by linarith)))
  obtain ⟨h, hh⟩ : ∃ h : ℕ → ℂ → ℂ, h = fun N s => zetaEntire s * edPoly a' (Finset.Icc 1 N) s - A s := ⟨_, rfl⟩
  have hdiff : ∀ N, DifferentiableOn ℂ (h N) (Metric.ball c (5 / 2 - x / 4)) := by
    intro N s hs
    have h1 := hgeo (s := s) (ρ := 5 / 2 - x / 4) (by
      have := Metric.mem_ball.mp hs
      rw [dist_eq_norm] at this
      exact this.le)
    have h2 : DifferentiableAt ℂ (edPoly a' (Finset.Icc 1 N)) s :=
      differentiable_edPoly a' (fun n hn => (Finset.mem_Icc.mp hn).1) s
    have h3 := hA s (by linarith [h1.1]) (by linarith [h1.2.1])
    rw [hh]
    exact (((differentiable_zetaEntire s).mul h2).sub h3).differentiableWithinAt
  -- the small circle
  have hsmall : ∀ N, ∀ z : ℂ, ‖z - c‖ = 1 → ‖h N z‖ ≤ C₀ * tailTwo N := by
    intro N z hz
    have h1 := hgeo (s := z) (ρ := 1) hz.le
    have h2 : 1 < z.re := by linarith [h1.1]
    have h3 : h N z = zetaEntire z * (edPoly a' (Finset.Icc 1 N) z - LSeries a' z) := by
      rw [hh]
      simp only
      rw [← hEA z h2]
      ring
    rw [h3, norm_mul]
    have h4 := norm_edPoly_sub_LSeries_le ha (s := z) (by linarith [h1.1]) N
    have h5 := hC₀ z (by
      rw [Metric.mem_closedBall, dist_eq_norm, hz]
      norm_num)
    exact mul_le_mul h5 h4 (norm_nonneg _) hC₀0
  -- the large circle
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = C₀ * √(10 * B + 26 * B / (x / 2)) + C_A := ⟨_, rfl⟩
  have hlarge : ∀ N, 1 ≤ N → ∀ z : ℂ, ‖z - c‖ = 5 / 2 - x / 2 → ‖h N z‖ ≤ M := by
    intro N hN z hz
    have h1 := hgeo (s := z) (ρ := 5 / 2 - x / 2) hz.le
    obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℝ, x₁ = z.re - 1 / 2 := ⟨_, rfl⟩
    have hx₁0 : x / 2 ≤ x₁ := by
      rw [hx₁]
      linarith [h1.1]
    have hx₁pos : 0 < x₁ := by linarith
    have hz' : z = ((1 / 2 + x₁ : ℝ) : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext
      · simp [hx₁]
      · simp
    have h2 := norm_sq_edPoly_shift_le (a := a') (x := x₁) (c := z.im) (B := B) (t := z.im) hx₁pos hB0
      (hcell z.im (by linarith [h1.2.1]) (by linarith [h1.2.2])) hN ⟨le_rfl, by linarith⟩
    rw [← hz'] at h2
    have h3 : 10 * B + 26 * B / x₁ ≤ 10 * B + 26 * B / (x / 2) := by
      have := div_le_div_of_nonneg_left (by positivity : 0 ≤ 26 * B) (by linarith : 0 < x / 2) hx₁0
      linarith
    have h4 : ‖edPoly a' (Finset.Icc 1 N) z‖ ≤ √(10 * B + 26 * B / (x / 2)) :=
      Real.le_sqrt_of_sq_le (h2.trans h3)
    have h5 := hC₀ z (by
      rw [Metric.mem_closedBall, dist_eq_norm, hz]
      linarith)
    have h6 := hC_A z (by
      rw [Metric.mem_closedBall, dist_eq_norm, hz])
    rw [hh, hM]
    simp only
    refine (norm_sub_le _ _).trans (add_le_add ?_ h6)
    rw [norm_mul]
    exact mul_le_mul h5 h4 (norm_nonneg _) hC₀0
  -- three circles at the target
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = (Real.log ‖s₀ - c‖ - Real.log 1) / (Real.log (5 / 2 - x / 2) - Real.log 1) :=
    ⟨_, rfl⟩
  have hω1 : ω < 1 := by
    rw [hω, Real.log_one, sub_zero, sub_zero, hs₀c]
    have h1 : Real.log (5 / 2 - x) < Real.log (5 / 2 - x / 2) :=
      Real.log_lt_log (by linarith) (by linarith)
    have h2 : 0 < Real.log (5 / 2 - x / 2) := Real.log_pos (by linarith)
    rw [div_lt_one h2]
    exact h1
  have hthree : ∀ N, 1 ≤ N → ‖h N s₀‖ ≤ (C₀ * tailTwo N) ^ (1 - ω) * M ^ ω := by
    intro N hN
    have h1 := HTGeometry.norm_le_of_three_circles_center (g := h N) (c := c) (r₁ := 1)
      (r₃ := 5 / 2 - x / 2) (R := 5 / 2 - x / 4) one_pos (by linarith) (by linarith) (hdiff N)
      (hsmall N) (hlarge N hN) (z := s₀) (by rw [hs₀c]; linarith) (by rw [hs₀c]; linarith)
    rw [← hω] at h1
    exact h1
  have htail0 : Tendsto (fun N => C₀ * tailTwo N) atTop (𝓝 0) := by
    simpa using tendsto_tailTwo.const_mul C₀
  have htail1 : Tendsto (fun N => (C₀ * tailTwo N) ^ (1 - ω) * M ^ ω) atTop (𝓝 0) := by
    have h1 := htail0.rpow_const (p := 1 - ω) (Or.inr (by linarith))
    rw [Real.zero_rpow (by linarith)] at h1
    simpa using h1.mul_const (M ^ ω)
  have hlimit : Tendsto (fun N => h N s₀) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ htail1
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact hthree N hN
  -- pass to the limit
  have hprod : Tendsto (fun N => zetaEntire s₀ * edPoly a' (Finset.Icc 1 N) s₀) atTop (𝓝 (A s₀)) := by
    have h1 := hlimit.add_const (A s₀)
    rw [zero_add] at h1
    refine h1.congr fun N => ?_
    rw [hh]
    simp
  refine le_of_tendsto hprod.norm ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h2 := norm_sq_edPoly_shift_le (a := a') (x := x) (c := γ) (B := B) (t := γ) hx0 hB0
    (hcell γ (by linarith) (by linarith)) hN ⟨le_rfl, by linarith⟩
  rw [← hs₀] at h2
  exact Real.le_sqrt_of_sq_le h2

/-! ### A zero of `ζ` obstructs the bound -/

/-- **A zero of `ζ` in the window obstructs every uniform bound**, when the numerator `A` does not vanish there. -/
theorem not_uniform_second_moment_of_zero {A : ℂ → ℂ} {a' : ℕ → ℂ} (ha : ∀ n, ‖a' n‖ ≤ 1)
    (hA : ∀ s : ℂ, 1 / 2 ≤ s.re → 0 < s.im → DifferentiableAt ℂ A s ∧ A s ≠ 0)
    (hEA : ∀ s : ℂ, 1 < s.re → zetaEntire s * LSeries a' s = A s) {T γ β : ℝ}
    (hβ : 1 / 2 ≤ β) (hβ1 : β < 1) (hz : riemannZeta ((β : ℂ) + (γ : ℂ) * I) = 0)
    (hγ1 : T + 3 ≤ γ) (hγ2 : γ ≤ 2 * T - 4) :
    ¬ ∃ B : ℝ, ∀ m, 1 ≤ m → (∫ t in T..(2 * T), ‖linePoly a' m t‖ ^ 2) ≤ B := by
  rintro ⟨B, hB⟩
  have hγ0 : 0 < γ := by linarith
  have hT2 : T ≤ 2 * T := by linarith
  have hB0 : 0 ≤ B := (intervalIntegral.integral_nonneg hT2 fun t _ => by positivity).trans (hB 1 le_rfl)
  have hAd : ∀ s : ℂ, 1 / 2 < s.re → 0 < s.im → DifferentiableAt ℂ A s :=
    fun s h1 h2 => (hA s h1.le h2).1
  have hcore := fun x (hx0 : 0 < x) (hx1 : x ≤ 1) =>
    norm_le_of_uniform_second_moment ha hAd hEA hB hγ1 hγ2 hx0 hx1
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℂ, φ = fun x => ((1 / 2 + x : ℝ) : ℂ) + (γ : ℂ) * I := ⟨_, rfl⟩
  have hφre : ∀ x, (φ x).re = 1 / 2 + x := fun x => by simp [hφ]
  have hφim : ∀ x, (φ x).im = γ := fun x => by simp [hφ]
  have hφne : ∀ x, φ x ≠ 1 := by
    intro x h
    have h1 := hφim x
    rw [h] at h1
    simp at h1
    linarith
  rcases eq_or_lt_of_le hβ with heq | hlt
  · -- a zero on the line: the numerator stays away from `0` and `E` vanishes to first order
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℂ, ρ = φ 0 := ⟨_, rfl⟩
    have hρz : zetaEntire ρ = 0 := by
      have h1 : ρ = (β : ℂ) + (γ : ℂ) * I := by
        rw [hρ, hφ, ← heq]
        simp
      rw [hρ, zetaEntire_eq (hφne 0), ← hρ, h1, hz, mul_zero]
    have hρA := hA ρ (by rw [hρ, hφre]; norm_num) (by rw [hρ, hφim]; exact hγ0)
    obtain ⟨C, hC0, hC⟩ := (differentiable_zetaEntire ρ).isBigO_sub.exists_pos
    have hδ : 0 < ‖A ρ‖ / 2 := by
      have := norm_pos_iff.mpr hρA.2
      positivity
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ‖A ρ‖ / 2 := ⟨_, rfl⟩
    rw [← hδdef] at hδ
    have hφc : Continuous φ := by
      rw [hφ]
      fun_prop
    have hφt : Tendsto φ (𝓝 0) (𝓝 ρ) := by
      rw [hρ]
      exact hφc.tendsto 0
    have h1 : ∀ᶠ x in 𝓝 (0 : ℝ), δ < ‖A (φ x)‖ := by
      have h2 := (hρA.1.continuousAt.tendsto.comp hφt).norm
      exact h2.eventually (lt_mem_nhds (by
        rw [hδdef]
        linarith [norm_pos_iff.mpr hρA.2]))
    have h2 : ∀ᶠ x in 𝓝 (0 : ℝ), ‖zetaEntire (φ x) - zetaEntire ρ‖ ≤ C * ‖φ x - ρ‖ :=
      hφt.eventually hC.bound
    have h3 : ∀ᶠ x in 𝓝 (0 : ℝ), C ^ 2 * (10 * B * x ^ 2 + 26 * B * x) < δ ^ 2 := by
      have hc : Continuous fun x : ℝ => C ^ 2 * (10 * B * x ^ 2 + 26 * B * x) := by fun_prop
      have h4 := hc.tendsto 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h4
      exact h4.eventually (gt_mem_nhds (by positivity))
    obtain ⟨x, ⟨⟨hx1, hx2, hx3⟩, hx4, hx5⟩⟩ :=
      (((h1.and (h2.and h3)).filter_mono nhdsWithin_le_nhds).and
        (Ioc_mem_nhdsGT (zero_lt_one' ℝ))).exists
    have hval := hcore x hx4 hx5
    rw [← show φ x = ((1 / 2 + x : ℝ) : ℂ) + (γ : ℂ) * I by rw [hφ]] at hval
    have hdist : ‖φ x - ρ‖ = x := by
      have h4 : φ x - ρ = (x : ℂ) := by
        rw [hρ, hφ]
        push_cast
        ring
      rw [h4, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx4]
    rw [hρz, sub_zero, hdist] at hx2
    obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = 10 * B + 26 * B / x := ⟨_, rfl⟩
    rw [← hZ] at hval
    have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
    have hle : δ ≤ C * x * √Z :=
      hx1.le.trans (hval.trans (mul_le_mul_of_nonneg_right hx2 (Real.sqrt_nonneg _)))
    have hsq : δ ^ 2 ≤ (C * x * √Z) ^ 2 := pow_le_pow_left₀ hδ.le hle 2
    have hexp : (C * x * √Z) ^ 2 = C ^ 2 * (10 * B * x ^ 2 + 26 * B * x) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hZ0, hZ]
      field_simp
    rw [hexp] at hsq
    exact absurd hx3 (not_lt.mpr hsq)
  · -- a zero right of the line: the left side vanishes
    have hx0 : 0 < β - 1 / 2 := by linarith
    have hval := hcore (β - 1 / 2) hx0 (by linarith)
    have hs : (((1 / 2 + (β - 1 / 2) : ℝ) : ℂ) + (γ : ℂ) * I) = (β : ℂ) + (γ : ℂ) * I := by
      congr 2
      ring
    rw [hs] at hval
    have hne1 : (β : ℂ) + (γ : ℂ) * I ≠ 1 := by
      intro h
      have h1 := congrArg Complex.im h
      simp at h1
      linarith
    rw [zetaEntire_eq hne1, hz, mul_zero, norm_zero, zero_mul] at hval
    have h2 := (hA ((β : ℂ) + (γ : ℂ) * I) (by simpa using hβ) (by simpa using hγ0)).2
    exact h2 (norm_le_zero_iff.mp hval)

/-- Every large window holds a zero of `ζ` with `β ≥ ½`. -/
theorem eventually_exists_zero_in_window :
    ∀ᶠ T : ℝ in atTop, ∃ β γ : ℝ, 1 / 2 ≤ β ∧ β < 1 ∧ T + 3 ≤ γ ∧ γ ≤ 2 * T - 4 ∧
      riemannZeta ((β : ℂ) + (γ : ℂ) * I) = 0 := by
  filter_upwards [eventually_zero_count_increment, eventually_ge_atTop (4000 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hcount hT hℓ
  have hT0 : 0 < T := by linarith
  have hpos : 0 < T * Real.log T := by positivity
  have hc := hcount (T + 3) (2 * T - 4) (by linarith) (by linarith) (by linarith) (by linarith)
  have hπ := Real.pi_pos
  have hlt : (xiPosZeroCount (T + 3) : ℝ) < xiPosZeroCount (2 * T - 4) := by
    by_contra hcon
    have h1 : (xiPosZeroCount (2 * T - 4) : ℝ) - xiPosZeroCount (T + 3) ≤ 0 := by linarith [not_lt.mp hcon]
    have h2 := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * Real.pi) h1
    linarith
  have hexists : ∃ z ∈ stripFinsetPos (2 * T - 4), T + 3 < z.im := by
    by_contra hcon
    have hsub : stripFinsetPos (2 * T - 4) ⊆ stripFinsetPos (T + 3) := by
      intro z hz
      have hle : z.im ≤ T + 3 := not_lt.mp fun h => hcon ⟨z, hz, h⟩
      obtain ⟨h1, h2, h3, -, h5⟩ := mem_stripFinsetPos.mp hz
      exact mem_stripFinsetPos.mpr ⟨h1, h2, h3, hle, h5⟩
    have hle : xiPosZeroCount (2 * T - 4) ≤ xiPosZeroCount (T + 3) :=
      Finset.sum_le_sum_of_subset hsub
    have hle' : (xiPosZeroCount (2 * T - 4) : ℝ) ≤ xiPosZeroCount (T + 3) := by exact_mod_cast hle
    linarith
  obtain ⟨z, hz, hzim⟩ := hexists
  have hzeta : ∀ w ∈ stripFinsetPos (2 * T - 4), riemannZeta w = 0 := by
    intro w hw
    obtain ⟨h1, h2, -, -, h5⟩ := mem_stripFinsetPos.mp hw
    have hne : w ≠ 1 := by
      intro h
      rw [h] at h2
      simp at h2
    exact (xi_eq_zero_iff_riemannZeta_of_re_pos h1 hne).mp h5
  by_cases hre : 1 / 2 ≤ z.re
  · obtain ⟨-, h2, -, h4, -⟩ := mem_stripFinsetPos.mp hz
    refine ⟨z.re, z.im, hre, h2, hzim.le, h4, ?_⟩
    rw [Complex.re_add_im]
    exact hzeta z hz
  · have hw := lineReflect_mem_stripFinsetPos hz
    obtain ⟨-, h2, -, h4, -⟩ := mem_stripFinsetPos.mp hw
    have him : (lineReflect z).im = z.im := by simp [lineReflect]
    refine ⟨(lineReflect z).re, (lineReflect z).im, ?_, h2, by rw [him]; exact hzim.le, h4, ?_⟩
    · rw [lineReflect_re]
      linarith [not_le.mp hre]
    · rw [Complex.re_add_im]
      exact hzeta _ hw

/-- The numerator of the Liouville series: `(s − 1) ζ(2s)`. -/
private theorem liouville_numerator {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : 0 < s.im) :
    DifferentiableAt ℂ (fun z : ℂ => (z - 1) * riemannZeta (2 * z)) s ∧
      (s - 1) * riemannZeta (2 * s) ≠ 0 := by
  have him : (2 * s).im = 2 * s.im := by simp [Complex.mul_im]
  have hne : 2 * s ≠ 1 := by
    intro h
    have h3 := congrArg Complex.im h
    rw [him] at h3
    simp at h3
    linarith
  have hne1 : s - 1 ≠ 0 := by
    intro h
    have h3 := congrArg Complex.im h
    simp at h3
    linarith
  have hre : 1 ≤ (2 * s).re := by
    simp [Complex.mul_re]
    linarith
  refine ⟨?_, mul_ne_zero hne1 (riemannZeta_ne_zero_of_one_le_re hre)⟩
  have h3 : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s :=
    DifferentiableAt.comp (f := fun z : ℂ => 2 * z) (g := riemannZeta) s
      (differentiableAt_riemannZeta hne) (by fun_prop)
  exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - 1) s).mul h3

/-- **At every large height the second moment of the Liouville polynomial is unbounded in the length.** -/
theorem eventually_not_uniform_liouville :
    ∀ᶠ T : ℝ in atTop, ¬ ∃ B : ℝ, ∀ m, 1 ≤ m →
      (∫ t in T..(2 * T), ‖linePoly (fun n => liouvilleC n) m t‖ ^ 2) ≤ B := by
  filter_upwards [eventually_exists_zero_in_window] with T hzero
  obtain ⟨β, γ, hβ, hβ1, hγ1, hγ2, hz⟩ := hzero
  refine not_uniform_second_moment_of_zero (A := fun z => (z - 1) * riemannZeta (2 * z))
    (a' := fun n => liouvilleC n) norm_liouvilleC_le_one (fun s h1 h2 => liouville_numerator h1 h2)
    ?_ hβ hβ1 hz hγ1 hγ2
  intro s hs
  have hne : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  rw [zetaEntire_eq hne]
  have h := LSeries_liouvilleC_mul_riemannZeta hs
  calc (s - 1) * riemannZeta s * LSeries (fun n => liouvilleC n) s
      = (s - 1) * (LSeries (fun n => liouvilleC n) s * riemannZeta s) := by ring
    _ = _ := by rw [h]

/-- **The same for the Möbius polynomial.** -/
theorem eventually_not_uniform_moebius :
    ∀ᶠ T : ℝ in atTop, ¬ ∃ B : ℝ, ∀ m, 1 ≤ m →
      (∫ t in T..(2 * T), ‖linePoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) m t‖ ^ 2) ≤ B := by
  filter_upwards [eventually_exists_zero_in_window] with T hzero
  obtain ⟨β, γ, hβ, hβ1, hγ1, hγ2, hz⟩ := hzero
  refine not_uniform_second_moment_of_zero (A := fun z => z - 1)
    (a' := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) ?_ (fun s _ h2 => ⟨by fun_prop, ?_⟩)
    ?_ hβ hβ1 hz hγ1 hγ2
  · intro n
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · intro h
    have h3 := congrArg Complex.im h
    simp at h3
    linarith
  · intro s hs
    have hne : s ≠ 1 := by
      intro h
      rw [h] at hs
      simp at hs
    rw [zetaEntire_eq hne]
    have h : LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s * riemannZeta s = 1 := by
      rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, mul_comm]
      exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
    calc (s - 1) * riemannZeta s * LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s
        = (s - 1) * (LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s * riemannZeta s) := by
          ring
      _ = _ := by rw [h, mul_one]

/-! ### The integers -/

/-- **The integer polynomial stays bounded.**  After removing the pole term, its second moment at the height `T` is at most `T(2+4T)²`, for every length. -/
theorem integral_norm_sq_integer_polynomial_le {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in T..(2 * T), ‖linePoly (fun _ => 1) N t -
        ((N : ℝ) : ℂ) ^ (1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) /
          (1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ^ 2) ≤ T * (2 + 4 * T) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNne : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℂ, w = fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := ⟨_, rfl⟩
  have hwre : ∀ t, (w t).re = 1 / 2 := fun t => by simp [hw]
  have hwim : ∀ t, (w t).im = t := fun t => by simp [hw]
  have hne1 : ∀ t, 1 - w t ≠ 0 := by
    intro t h
    have h1 := congrArg Complex.re h
    simp [hwre] at h1
    norm_num at h1
  have hnormeq : ∀ t, ‖1 - w t‖ = ‖w t‖ := by
    intro t
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hwre, hwim]
    ring
  have hpoint : ∀ t ∈ Set.uIcc T (2 * T), ‖linePoly (fun _ => 1) N t -
      ((N : ℝ) : ℂ) ^ (1 - w t) / (1 - w t)‖ ≤ 2 + 4 * T := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    have hne : w t ≠ 1 := by
      intro h
      exact hne1 t (by rw [h]; ring)
    have hline : linePoly (fun _ => 1) N t = ∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w t) := by
      unfold linePoly edPoly
      rw [hw]
      simp
    rw [hline, RHTower.sum_cpow_sub_pow_eq (by rw [hwre]; norm_num) hne hN]
    have hw0 : 0 < (w t).re := by rw [hwre]; norm_num
    have hint := integrableOn_Ioc_fract_cpow hw0 N
    have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioc (1 : ℝ) N)),
        ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w t - 1)‖ ≤ u ^ (-(3 / 2 : ℝ)) := by
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := by linarith [hu.1]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg u)]
      have hre : (-w t - 1).re = -(3 / 2 : ℝ) := by
        simp [hwre]
        norm_num
      rw [hre]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hu0.le _) (Int.fract_lt_one u).le
    have hrpow : IntegrableOn (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (Set.Ioc (1 : ℝ) N) := by
      have h1 : IntervalIntegrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) volume 1 N :=
        (ContinuousOn.intervalIntegrable fun u hu => by
          rw [Set.uIcc_of_le hN1] at hu
          exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hu.1]))).continuousWithinAt)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hN1).mp h1
    have hI : ‖∫ u in Set.Ioc (1 : ℝ) N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w t - 1)‖ ≤ 2 := by
      refine (norm_integral_le_of_norm_le hrpow hbound).trans ?_
      rw [← intervalIntegral.integral_of_le hN1, integral_rpow (Or.inr ⟨by norm_num, by
        rw [Set.uIcc_of_le hN1]
        exact fun h => by linarith [h.1]⟩), Real.one_rpow]
      have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-(3 / 2 : ℝ) + 1) := Real.rpow_nonneg hN0.le _
      norm_num at h2 ⊢
      linarith
    have hnw : ‖w t‖ ≤ 1 / 2 + 2 * T := by
      rw [hw]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by norm_num), Real.norm_of_nonneg (by linarith [ht.1])]
      linarith [ht.2]
    have hwne : w t ≠ 0 := by
      intro h
      have h1 := hwre t
      rw [h] at h1
      norm_num at h1
    have hratio : ‖-w t / (1 - w t)‖ = 1 := by
      rw [norm_div, norm_neg, hnormeq, div_self (norm_pos_iff.mpr hwne).ne']
    refine (norm_sub_le _ _).trans ?_
    rw [hratio, norm_mul]
    have h3 := mul_le_mul hnw hI (norm_nonneg _) (by linarith)
    linarith
  have hcont : Continuous fun t : ℝ => ‖linePoly (fun _ => 1) N t -
      ((N : ℝ) : ℂ) ^ (1 - w t) / (1 - w t)‖ ^ 2 := by
    have h1 : Continuous fun t : ℝ => ((N : ℝ) : ℂ) ^ (1 - w t) := by
      refine Continuous.const_cpow ?_ (Or.inl hNne)
      rw [hw]
      fun_prop
    have h2 : Continuous fun t : ℝ => 1 - w t := by
      rw [hw]
      fun_prop
    exact ((continuous_linePoly _ N).sub (h1.div h2 hne1)).norm.pow 2
  have hmono := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2 * T)
    (f := fun t : ℝ => ‖linePoly (fun _ => 1) N t - ((N : ℝ) : ℂ) ^ (1 - w t) / (1 - w t)‖ ^ 2)
    (C := (2 + 4 * T) ^ 2) (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hpoint t (by
          rw [Set.uIcc_of_le (by linarith)]
          exact ⟨ht.1.le, ht.2⟩)) 2)
  subst hw
  refine (le_abs_self _).trans ?_
  rw [Real.norm_eq_abs] at hmono
  refine hmono.trans (le_of_eq ?_)
  rw [abs_of_pos (by linarith)]
  ring

end GaloisForLFunctions.ArithmeticProduction
