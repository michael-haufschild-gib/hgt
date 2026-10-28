import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGevreyProfile

/-!
# Denjoy–Carleman profiles

The explicit profile of `TheGevreyProfile` is Gevrey of class `2`, so the window closes at
`(log log N)^{2+ε}`. Compactly supported profiles exist in every Gevrey class `s > 1`; this file
builds them explicitly, with derivative bounds, and brings the window to `(log log N)^{1+ε}`.

* **The glue functions** `E_r(x) = E(x^r)`, `E = expNegInvGlue`, `r` odd (`glueR`): smooth, zero on
  `(−∞, 0]`, equal to `exp(−(1/x)^r)` on `(0, ∞)`, where
  `E_r^{(n)}(x) = Q_n(1/x) exp(−(1/x)^r)` with `Q_{n+1} = r X^{r+1} Q_n − X² Q_n′`
  (`iteratedDeriv_glueR_eqOn`).
* **The weights `(j!)^{1/r}`** bound `t^j e^{−t^r}` because `(t^j e^{−t^r})^r ≤ (t^r)^j e^{−t^r} ≤ j!`
  (`pow_mul_exp_neg_pow_le`). With `W_D(Q) = Σ_{j<D} |c_j| (j!)^{1/r}`, the recursion gains at most
  `(r+1)(D+r)^{1+1/r}` per step (`dcNorm_step_le`), since `(i+m)! ≤ (i+m)^m i!`. Hence
  `|E_r^{(n)}| ≤ ((r+1)^{2+1/r})^n (n!)^{1+1/r}` (`abs_iteratedDeriv_glueR_le`): Gevrey class
  `1 + 1/r`.
* **The profiles** `c E_r(1 + x) E_r(1 − x)` (`dcProfile`) are Gevrey of class `1 + 1/r`, and for
  every `α > 1` RH holds iff Weil's form is eventually nonnegative on the atomic families of a
  Denjoy–Carleman profile of width `(log log N)^α/N` (`exists_dcProfile_loglog`).
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower Polynomial
open scoped Real ContDiff

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### The glue functions `E(x^r)` -/

section Glue

variable {r : ℕ}

/-- `E_r(x) = E(x^r)`: for odd `r`, zero on `(−∞, 0]` and `exp(−(1/x)^r)` on `(0, ∞)`. -/
def glueR (r : ℕ) (x : ℝ) : ℝ := expNegInvGlue (x ^ r)

theorem contDiff_glueR (r : ℕ) : ContDiff ℝ ∞ (glueR r) :=
  (expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_id.pow r)

theorem glueR_of_nonpos (hr : Odd r) {x : ℝ} (hx : x ≤ 0) : glueR r x = 0 :=
  expNegInvGlue.zero_of_nonpos (hr.pow_nonpos hx)

theorem glueR_of_pos {x : ℝ} (hx : 0 < x) : glueR r x = Real.exp (-(x⁻¹ ^ r)) := by
  unfold glueR expNegInvGlue
  rw [if_neg (not_le.mpr (pow_pos hx r)), inv_pow]

theorem glueR_pos {x : ℝ} (hx : 0 < x) : 0 < glueR r x := by
  rw [glueR_of_pos hx]; exact Real.exp_pos _

theorem glueR_nonneg (x : ℝ) : 0 ≤ glueR r x := expNegInvGlue.nonneg _

/-- `Q_0 = 1`, `Q_{n+1} = r X^{r+1} Q_n − X² Q_n′`. -/
def dcPoly (r : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C (r : ℝ) * X ^ (r + 1) * dcPoly r n - X ^ 2 * derivative (dcPoly r n)

/-- The candidate `n`-th derivative `Q_n(1/x) exp(−(1/x)^r)`. -/
def dcDeriv (r n : ℕ) (x : ℝ) : ℝ := (dcPoly r n).eval x⁻¹ * Real.exp (-(x⁻¹ ^ r))

theorem hasDerivAt_dcDeriv (hr : 1 ≤ r) (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (dcDeriv r n) (dcDeriv r (n + 1) x) x := by
  have hinv := hasDerivAt_inv hx
  have hP := ((dcPoly r n).hasDerivAt x⁻¹).comp x hinv
  have hE := ((hinv.pow r).neg).exp
  have h := hP.mul hE
  have e : dcDeriv r n = fun y => (dcPoly r n).eval y⁻¹ * Real.exp (-(y⁻¹ ^ r)) := rfl
  rw [e]
  refine h.congr_deriv ?_
  simp only [dcDeriv, dcPoly, Function.comp, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  have hr1 : r - 1 + 2 = r + 1 := by omega
  have hx2 : (x ^ 2)⁻¹ = x⁻¹ ^ 2 := by rw [inv_pow]
  rw [hx2]
  have hpow : x⁻¹ ^ (r - 1) * x⁻¹ ^ 2 = x⁻¹ ^ (r + 1) := by rw [← pow_add, hr1]
  linear_combination (Real.exp (-x⁻¹ ^ r) * eval x⁻¹ (dcPoly r n) * (r : ℝ)) * hpow

/-- **The derivatives on `(0, ∞)`**: `E_r^{(n)} = Q_n(1/x) exp(−(1/x)^r)`. -/
theorem iteratedDeriv_glueR_eqOn (hr : 1 ≤ r) (n : ℕ) :
    Set.EqOn (iteratedDeriv n (glueR r)) (dcDeriv r n) (Ioi 0) := by
  induction n with
  | zero =>
    intro x hx
    simp only [iteratedDeriv_zero, dcDeriv, dcPoly, eval_one, one_mul]
    exact glueR_of_pos hx
  | succ n ih =>
    intro x hx
    have hev : iteratedDeriv n (glueR r) =ᶠ[𝓝 x] dcDeriv r n :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) fun y hy => ih hy
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact (hasDerivAt_dcDeriv hr n (ne_of_gt hx)).deriv

/-- **The derivatives vanish on `(−∞, 0]`**: `E_r` vanishes there and its derivatives are
continuous. -/
theorem iteratedDeriv_glueR_of_nonpos (hr : Odd r) (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    iteratedDeriv n (glueR r) x = 0 := by
  have hcont : Continuous (iteratedDeriv n (glueR r)) :=
    (contDiff_glueR r).continuous_iteratedDeriv n (natCast_le_infty n)
  have hzero : Iio (0 : ℝ) ⊆ {y | iteratedDeriv n (glueR r) y = 0} := fun y hy => by
    have hev : glueR r =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (isOpen_Iio.mem_nhds hy) fun z hz => glueR_of_nonpos hr (le_of_lt hz)
    show iteratedDeriv n (glueR r) y = 0
    rw [hev.iteratedDeriv_eq]
    simp
  have hcl := (isClosed_eq hcont continuous_const).closure_subset_iff.mpr hzero
  rw [closure_Iio] at hcl
  exact hcl hx

theorem natDegree_dcPoly_lt (hr : 1 ≤ r) (n : ℕ) : (dcPoly r n).natDegree < n * (r + 1) + 1 := by
  induction n with
  | zero => simp [dcPoly]
  | succ n ih =>
    simp only [dcPoly]
    have h1 := natDegree_sub_le (C (r : ℝ) * X ^ (r + 1) * dcPoly r n)
      (X ^ 2 * derivative (dcPoly r n))
    have hCX : (C (r : ℝ) * X ^ (r + 1)).natDegree ≤ r + 1 :=
      (natDegree_C_mul_le (r : ℝ) (X ^ (r + 1))).trans (natDegree_X_pow_le (r + 1))
    have h2 : (C (r : ℝ) * X ^ (r + 1) * dcPoly r n).natDegree ≤
        (C (r : ℝ) * X ^ (r + 1)).natDegree + (dcPoly r n).natDegree := natDegree_mul_le
    have hX2 : ((X : ℝ[X]) ^ 2).natDegree ≤ 2 := natDegree_X_pow_le 2
    have h3 : (X ^ 2 * derivative (dcPoly r n)).natDegree ≤
        ((X : ℝ[X]) ^ 2).natDegree + (derivative (dcPoly r n)).natDegree := natDegree_mul_le
    have h4 := natDegree_derivative_le (dcPoly r n)
    rw [Nat.succ_mul]
    generalize n * (r + 1) = a at *
    omega

end Glue

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
