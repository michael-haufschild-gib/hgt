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
* **The weights `(j!)^{1/r}`** bound `t^j e^{−t^r}` because
  `(t^j e^{−t^r})^r ≤ (t^r)^j e^{−t^r} ≤ j!`
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

/-! ### The weights `(j!)^{1/r}` -/

section Weights

variable {r : ℕ}

/-- The weight `w_j = (j!)^{1/r}`. -/
def dcW (r j : ℕ) : ℝ := (j.factorial : ℝ) ^ ((r : ℝ)⁻¹)

/-- `W_D(Q) = Σ_{j<D} |c_j| (j!)^{1/r}`. -/
def dcNorm (r D : ℕ) (p : ℝ[X]) : ℝ := ∑ j ∈ Finset.range D, |p.coeff j| * dcW r j

theorem dcW_nonneg (r j : ℕ) : 0 ≤ dcW r j := by unfold dcW; positivity

theorem dcNorm_nonneg (r D : ℕ) (p : ℝ[X]) : 0 ≤ dcNorm r D p :=
  Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (dcW_nonneg r j)

/-- `t^j e^{−t^r} ≤ (j!)^{1/r}`: its `r`-th power is at most `(t^r)^j e^{−t^r} ≤ j!`. -/
theorem pow_mul_exp_neg_pow_le (hr : 1 ≤ r) {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    t ^ j * Real.exp (-(t ^ r)) ≤ dcW r j := by
  have hr0 : r ≠ 0 := by omega
  set y := t ^ j * Real.exp (-(t ^ r))
  have hy : 0 ≤ y := by positivity
  have htr : 0 ≤ t ^ r := pow_nonneg ht r
  have hyr : y ^ r ≤ (j.factorial : ℝ) := by
    have e : y ^ r = (t ^ r) ^ j * Real.exp ((r : ℝ) * (-(t ^ r))) := by
      simp only [y, mul_pow, ← pow_mul, Real.exp_nat_mul]
      ring_nf
    have h1 : Real.exp ((r : ℝ) * (-(t ^ r))) ≤ Real.exp (-(t ^ r)) := by
      rw [Real.exp_le_exp]
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    have h2 := Real.pow_div_factorial_le_exp (t ^ r) htr j
    have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
    rw [div_le_iff₀ hf] at h2
    have h3 : (t ^ r) ^ j * Real.exp (-(t ^ r)) ≤ (j.factorial : ℝ) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      linarith [mul_comm (Real.exp (t ^ r)) (j.factorial : ℝ)]
    rw [e]
    exact (mul_le_mul_of_nonneg_left h1 (pow_nonneg htr j)).trans h3
  rw [← Real.pow_rpow_inv_natCast hy hr0]
  exact Real.rpow_le_rpow (pow_nonneg hy r) hyr (by positivity)

/-- `|Q(t)| e^{−t^r} ≤ W_D(Q)` for `t ≥ 0` and `deg Q < D`. -/
theorem abs_eval_mul_exp_neg_pow_le (hr : 1 ≤ r) {p : ℝ[X]} {D : ℕ} (hD : p.natDegree < D)
    {t : ℝ} (ht : 0 ≤ t) : |p.eval t| * Real.exp (-(t ^ r)) ≤ dcNorm r D p := by
  rw [eval_eq_sum_range' hD, dcNorm]
  refine (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Real.exp_pos _).le).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, abs_pow, abs_of_nonneg ht, mul_assoc]
  exact mul_le_mul_of_nonneg_left (pow_mul_exp_neg_pow_le hr ht j) (abs_nonneg _)

theorem dcW_succ (r i : ℕ) : dcW r (i + 1) = ((i : ℝ) + 1) ^ ((r : ℝ)⁻¹) * dcW r i := by
  unfold dcW
  rw [Nat.factorial_succ, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  push_cast; ring_nf

/-- `w_{i+m} ≤ (i+m)^{m/r} w_i`, since `(i+m)! ≤ (i+m)^m i!`. -/
theorem dcW_add_le (r i m : ℕ) :
    dcW r (i + m) ≤ (((i + m : ℕ) : ℝ) ^ m) ^ ((r : ℝ)⁻¹) * dcW r i := by
  unfold dcW
  have h1 : (i + m).factorial ≤ i.factorial * (i + m) ^ m := by
    have := Nat.factorial_mul_descFactorial (n := i + m) (k := m) (by omega)
    rw [Nat.add_sub_cancel] at this
    rw [← this]
    exact Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
  have h2 : ((i + m).factorial : ℝ) ≤ (i.factorial : ℝ) * ((i + m : ℕ) : ℝ) ^ m := by
    exact_mod_cast h1
  calc ((i + m).factorial : ℝ) ^ ((r : ℝ)⁻¹) ≤ ((i.factorial : ℝ) * ((i + m : ℕ) : ℝ) ^ m) ^
        ((r : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h2 (by positivity)
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring

/-- `(x^{r+1})^{1/r} = x^{1 + 1/r}`. -/
theorem pow_succ_rpow_inv {x : ℝ} (hx : 0 ≤ x) (hr : 1 ≤ r) :
    (x ^ (r + 1)) ^ ((r : ℝ)⁻¹) = x ^ (1 + (r : ℝ)⁻¹) := by
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  field_simp

/-- The coefficients of `r X^{r+1} Q − X² Q′`:
`|q_j| ≤ r|c_{j−r−1}| [j ≥ r+1] + (j−1)|c_{j−1}| [j ≥ 2]`. -/
theorem abs_coeff_dcStep_le (p : ℝ[X]) (j : ℕ) :
    |(C (r : ℝ) * X ^ (r + 1) * p - X ^ 2 * derivative p).coeff j| ≤
      (if r + 1 ≤ j then (r : ℝ) * |p.coeff (j - (r + 1))| else 0) +
        (if 2 ≤ j then |p.coeff (j - 1)| * ((j : ℝ) - 1) else 0) := by
  rw [coeff_sub, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul']
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · split_ifs <;> simp [abs_mul]
  · split_ifs with h
    · rw [coeff_derivative, abs_mul, show j - 2 + 1 = j - 1 by omega]
      refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (abs_nonneg _)
      rw [abs_of_nonneg (by positivity), Nat.cast_sub h]
      ring
    · simp

/-- The shifted sum of the `r X^{r+1} Q` part. -/
theorem sum_dcStep_A (p : ℝ[X]) (D : ℕ) :
    ∑ j ∈ Finset.range (D + (r + 1)),
        (if r + 1 ≤ j then (r : ℝ) * |p.coeff (j - (r + 1))| else 0) * dcW r j =
      ∑ i ∈ Finset.range D, (r : ℝ) * |p.coeff i| * dcW r (i + (r + 1)) := by
  rw [add_comm D (r + 1), Finset.sum_range_add]
  rw [Finset.sum_eq_zero fun j hj => by
    rw [if_neg (by have := Finset.mem_range.mp hj; omega), zero_mul], zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_pos (by omega), show r + 1 + i - (r + 1) = i by omega, add_comm (r + 1) i]

/-- The shifted sum of the `X² Q′` part. -/
theorem sum_dcStep_B {p : ℝ[X]} {D : ℕ} (hD : p.natDegree < D) :
    ∑ j ∈ Finset.range (D + (r + 1)),
        (if 2 ≤ j then |p.coeff (j - 1)| * ((j : ℝ) - 1) else 0) * dcW r j =
      ∑ i ∈ Finset.range D, |p.coeff i| * (i : ℝ) * dcW r (i + 1) := by
  rw [show D + (r + 1) = D + r + 1 by omega, Finset.sum_range_succ']
  rw [if_neg (by omega), zero_mul, add_zero, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range r) fun k _ => by
    rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < D + k + 1 - 1)]
    split_ifs <;> simp, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [show i + 1 - 1 = i by omega]; push_cast; ring
  · have : i = 0 := by omega
    subst this; simp

/-- **One step of the recursion**: `W_{D+r+1}(r X^{r+1} Q − X² Q′) ≤ (r+1)(D+r)^{1+1/r} W_D(Q)`. -/
theorem dcNorm_step_le (hr : 1 ≤ r) {p : ℝ[X]} {D : ℕ} (hD : p.natDegree < D) :
    dcNorm r (D + (r + 1)) (C (r : ℝ) * X ^ (r + 1) * p - X ^ 2 * derivative p) ≤
      ((r : ℝ) + 1) * ((D : ℝ) + r) ^ (1 + (r : ℝ)⁻¹) * dcNorm r D p := by
  set s := 1 + (r : ℝ)⁻¹
  have hDr : (0 : ℝ) < (D : ℝ) + r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    positivity
  have hstep : dcNorm r (D + (r + 1)) (C (r : ℝ) * X ^ (r + 1) * p - X ^ 2 * derivative p) ≤
      ∑ i ∈ Finset.range D, ((r : ℝ) * |p.coeff i| * dcW r (i + (r + 1)) +
        |p.coeff i| * (i : ℝ) * dcW r (i + 1)) := by
    unfold dcNorm
    rw [Finset.sum_add_distrib, ← sum_dcStep_A p D, ← sum_dcStep_B hD, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_coeff_dcStep_le p j) (dcW_nonneg r j)
  refine hstep.trans ?_
  unfold dcNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hiD : i < D := Finset.mem_range.mp hi
  have hw := dcW_nonneg r i
  have hc := abs_nonneg (p.coeff i)
  -- the shift by `r + 1`
  have h1 : dcW r (i + (r + 1)) ≤ ((D : ℝ) + r) ^ s * dcW r i := by
    refine (dcW_add_le r i (r + 1)).trans (mul_le_mul_of_nonneg_right ?_ hw)
    rw [pow_succ_rpow_inv (by positivity) hr]
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    have : (i : ℝ) + 1 ≤ D := by exact_mod_cast hiD
    push_cast; linarith
  -- the shift by `1`
  have h2 : (i : ℝ) * dcW r (i + 1) ≤ ((D : ℝ) + r) ^ s * dcW r i := by
    rw [dcW_succ]
    have hiDr : (i : ℝ) ≤ (D : ℝ) + r := by
      have : (i : ℝ) + 1 ≤ D := by exact_mod_cast hiD
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    have hi1 : ((i : ℝ) + 1) ^ ((r : ℝ)⁻¹) ≤ ((D : ℝ) + r) ^ ((r : ℝ)⁻¹) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      have : (i : ℝ) + 1 ≤ D := by exact_mod_cast hiD
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    have hs : ((D : ℝ) + r) ^ s = ((D : ℝ) + r) * ((D : ℝ) + r) ^ ((r : ℝ)⁻¹) := by
      rw [Real.rpow_add hDr, Real.rpow_one]
    rw [hs]
    have := mul_le_mul hiDr hi1 (by positivity) hDr.le
    calc (i : ℝ) * (((i : ℝ) + 1) ^ ((r : ℝ)⁻¹) * dcW r i)
        = (i : ℝ) * ((i : ℝ) + 1) ^ ((r : ℝ)⁻¹) * dcW r i := by ring
      _ ≤ ((D : ℝ) + r) * ((D : ℝ) + r) ^ ((r : ℝ)⁻¹) * dcW r i :=
          mul_le_mul_of_nonneg_right this hw
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  calc (r : ℝ) * |p.coeff i| * dcW r (i + (r + 1)) + |p.coeff i| * (i : ℝ) * dcW r (i + 1)
      = (r : ℝ) * |p.coeff i| * dcW r (i + (r + 1)) + |p.coeff i| * ((i : ℝ) * dcW r (i + 1)) := by
        ring
    _ ≤ (r : ℝ) * |p.coeff i| * (((D : ℝ) + r) ^ s * dcW r i) +
        |p.coeff i| * (((D : ℝ) + r) ^ s * dcW r i) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 hc)
    _ = ((r : ℝ) + 1) * ((D : ℝ) + r) ^ s * (|p.coeff i| * dcW r i) := by ring

/-- `W(Q_n) ≤ ((r+1)^{2+1/r})^n (n!)^{1+1/r}`. -/
theorem dcNorm_dcPoly_le (hr : 1 ≤ r) (n : ℕ) :
    dcNorm r (n * (r + 1) + 1) (dcPoly r n) ≤
      (((r : ℝ) + 1) ^ (2 + (r : ℝ)⁻¹)) ^ n * (n.factorial : ℝ) ^ (1 + (r : ℝ)⁻¹) := by
  induction n with
  | zero => simp [dcNorm, dcPoly, dcW]
  | succ n ih =>
    have h := dcNorm_step_le hr (natDegree_dcPoly_lt hr n)
    rw [show n * (r + 1) + 1 + (r + 1) = (n + 1) * (r + 1) + 1 by ring] at h
    simp only [dcPoly]
    refine h.trans ?_
    have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have hD : ((n * (r + 1) + 1 : ℕ) : ℝ) + r = ((n : ℝ) + 1) * ((r : ℝ) + 1) := by
      push_cast; ring
    rw [hD, Real.mul_rpow (by positivity) hr1.le]
    have hK : ((r : ℝ) + 1) ^ (2 + (r : ℝ)⁻¹) =
        ((r : ℝ) + 1) * ((r : ℝ) + 1) ^ (1 + (r : ℝ)⁻¹) := by
      rw [show (2 : ℝ) + (r : ℝ)⁻¹ = 1 + (1 + (r : ℝ)⁻¹) by ring, Real.rpow_add hr1, Real.rpow_one]
    have hfac : ((n + 1).factorial : ℝ) ^ (1 + (r : ℝ)⁻¹) =
        ((n : ℝ) + 1) ^ (1 + (r : ℝ)⁻¹) * (n.factorial : ℝ) ^ (1 + (r : ℝ)⁻¹) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
      push_cast; ring
    have h0 := dcNorm_nonneg r (n * (r + 1) + 1) (dcPoly r n)
    calc ((r : ℝ) + 1) * (((n : ℝ) + 1) ^ (1 + (r : ℝ)⁻¹) * ((r : ℝ) + 1) ^ (1 + (r : ℝ)⁻¹)) *
          dcNorm r (n * (r + 1) + 1) (dcPoly r n)
        ≤ ((r : ℝ) + 1) * (((n : ℝ) + 1) ^ (1 + (r : ℝ)⁻¹) * ((r : ℝ) + 1) ^ (1 + (r : ℝ)⁻¹)) *
          ((((r : ℝ) + 1) ^ (2 + (r : ℝ)⁻¹)) ^ n * (n.factorial : ℝ) ^ (1 + (r : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ, hfac, hK]; ring

/-- **`E_r` is Gevrey of class `1 + 1/r`**: `|E_r^{(n)}| ≤ ((r+1)^{2+1/r})^n (n!)^{1+1/r}`. -/
theorem abs_iteratedDeriv_glueR_le (hr : Odd r) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (glueR r) x| ≤
      (((r : ℝ) + 1) ^ (2 + (r : ℝ)⁻¹)) ^ n * (n.factorial : ℝ) ^ (1 + (r : ℝ)⁻¹) := by
  have hr1 : 1 ≤ r := hr.pos
  rcases le_or_gt x 0 with hx | hx
  · rw [iteratedDeriv_glueR_of_nonpos hr n hx, abs_zero]; positivity
  · rw [iteratedDeriv_glueR_eqOn hr1 n hx]
    unfold dcDeriv
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (abs_eval_mul_exp_neg_pow_le hr1 (natDegree_dcPoly_lt hr1 n)
      (inv_nonneg.mpr hx.le)).trans (dcNorm_dcPoly_le hr1 n)

end Weights

/-! ### The Denjoy–Carleman profiles -/

section Profile

variable {r : ℕ}

/-- The bump `E_r(1 + x) E_r(1 − x)`, positive exactly on `(−1, 1)`. -/
def dcBump (r : ℕ) (x : ℝ) : ℝ := glueR r (1 + x) * glueR r (1 - x)

/-- The normalized Denjoy–Carleman profile of class `1 + 1/r`. -/
def dcProfile (r : ℕ) (x : ℝ) : ℝ := (∫ y, dcBump r y)⁻¹ * dcBump r x

theorem contDiff_dcBump (r : ℕ) : ContDiff ℝ ∞ (dcBump r) :=
  ((contDiff_glueR r).comp (contDiff_const.add contDiff_id)).mul
    ((contDiff_glueR r).comp (contDiff_const.sub contDiff_id))

theorem dcBump_vanishesOff (hr : Odd r) : VanishesOff (dcBump r) := by
  intro x hx
  unfold dcBump
  rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; norm_num at hx) with h | h
  · rw [abs_of_neg h] at hx
    rw [glueR_of_nonpos hr (by linarith), zero_mul]
  · rw [abs_of_pos h] at hx
    rw [glueR_of_nonpos hr (show 1 - x ≤ 0 by linarith), mul_zero]

theorem integral_dcBump_pos (hr : Odd r) : 0 < ∫ y, dcBump r y := by
  have hc : HasCompactSupport (dcBump r) := hasCompactSupport_of_vanishes (dcBump_vanishesOff hr)
  have hint : Integrable (dcBump r) :=
    (contDiff_dcBump r).continuous.integrable_of_hasCompactSupport hc
  have hnn : ∀ x, 0 ≤ dcBump r x := fun x => mul_nonneg (glueR_nonneg _) (glueR_nonneg _)
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hsub : Ioo (-1 : ℝ) 1 ⊆ Function.support (dcBump r) := fun x hx => by
    simp only [Function.mem_support]
    exact (mul_pos (glueR_pos (by linarith [hx.1])) (glueR_pos (by linarith [hx.2]))).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  norm_num

theorem contDiff_dcProfile (r : ℕ) : ContDiff ℝ ∞ (dcProfile r) :=
  contDiff_const.mul (contDiff_dcBump r)

theorem dcProfile_vanishesOff (hr : Odd r) : VanishesOff (dcProfile r) := fun x hx => by
  simp [dcProfile, dcBump_vanishesOff hr x hx]

theorem integral_dcProfile (hr : Odd r) : ∫ x, dcProfile r x = 1 := by
  unfold dcProfile
  rw [integral_const_mul, inv_mul_cancel₀ (integral_dcBump_pos hr).ne']

/-- **The bump is Gevrey of class `1 + 1/r`**:
`|(E_r(1+·)E_r(1−·))^{(q)}| ≤ (2K)^q (q!)^{1+1/r}`. -/
theorem abs_iteratedDeriv_dcBump_le (hr : Odd r) (q : ℕ) (x : ℝ) :
    |iteratedDeriv q (dcBump r) x| ≤
      (2 * ((r : ℝ) + 1) ^ (2 + (r : ℝ)⁻¹)) ^ q * (q.factorial : ℝ) ^ (1 + (r : ℝ)⁻¹) := by
  set K := ((r : ℝ) + 1) ^ (2 + (r : ℝ)⁻¹)
  set s := 1 + (r : ℝ)⁻¹
  have hs : 0 ≤ s := by positivity
  have hK : 0 ≤ K := by positivity
  have hE := contDiff_glueR r
  have h1 : ContDiff ℝ ∞ fun x => glueR r (1 + x) := hE.comp (contDiff_const.add contDiff_id)
  have h2 : ContDiff ℝ ∞ fun x => glueR r (1 - x) := hE.comp (contDiff_const.sub contDiff_id)
  have e : dcBump r = (fun x => glueR r (1 + x)) * fun x => glueR r (1 - x) := rfl
  rw [e, iteratedDeriv_mul (contDiffAt_of_smooth h1 q x) (contDiffAt_of_smooth h2 q x)]
  simp only [iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsum : ∑ l ∈ Finset.range (q + 1), (q.choose l : ℝ) = 2 ^ q := by
    exact_mod_cast Nat.sum_range_choose q
  calc ∑ l ∈ Finset.range (q + 1), |(q.choose l : ℝ) * iteratedDeriv l (glueR r) (1 + x) *
        ((-1 : ℝ) ^ (q - l) • iteratedDeriv (q - l) (glueR r) (1 - x))|
      ≤ ∑ l ∈ Finset.range (q + 1), (q.choose l : ℝ) * (K ^ q * (q.factorial : ℝ) ^ s) := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hlq : l ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
        rw [smul_eq_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          Nat.abs_cast]
        have a1 := abs_iteratedDeriv_glueR_le hr l (1 + x)
        have a2 := abs_iteratedDeriv_glueR_le hr (q - l) (1 - x)
        have hfac := factorial_rpow_mul_le hs hlq
        have hKq : K ^ l * K ^ (q - l) = K ^ q := by rw [← pow_add, Nat.add_sub_cancel' hlq]
        have hprod : |iteratedDeriv l (glueR r) (1 + x)| *
            |iteratedDeriv (q - l) (glueR r) (1 - x)| ≤ K ^ q * (q.factorial : ℝ) ^ s := by
          calc _ ≤ (K ^ l * (l.factorial : ℝ) ^ s) * (K ^ (q - l) * ((q - l).factorial : ℝ) ^ s) :=
                mul_le_mul a1 a2 (abs_nonneg _) (by positivity)
            _ = K ^ q * ((l.factorial : ℝ) ^ s * ((q - l).factorial : ℝ) ^ s) := by
                rw [← hKq]; ring
            _ ≤ K ^ q * (q.factorial : ℝ) ^ s := mul_le_mul_of_nonneg_left hfac (by positivity)
        calc (q.choose l : ℝ) * |iteratedDeriv l (glueR r) (1 + x)| *
              |iteratedDeriv (q - l) (glueR r) (1 - x)|
            = (q.choose l : ℝ) * (|iteratedDeriv l (glueR r) (1 + x)| *
              |iteratedDeriv (q - l) (glueR r) (1 - x)|) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (2 * K) ^ q * (q.factorial : ℝ) ^ s := by
        rw [← Finset.sum_mul, hsum, mul_pow]; ring

/-- **The profile is Gevrey of class `1 + 1/r`**: `‖φ_r^{(q)}‖₁ ≤ 2c (2K)^q (q!)^{1+1/r}`. -/
theorem integral_abs_iteratedDeriv_dcProfile_le (hr : Odd r) (q : ℕ) :
    ∫ t, |iteratedDeriv q (dcProfile r) t| ≤
      2 * (∫ y, dcBump r y)⁻¹ * (2 * ((r : ℝ) + 1) ^ (2 + (r : ℝ)⁻¹)) ^ q *
        (q.factorial : ℝ) ^ (1 + (r : ℝ)⁻¹) := by
  set c := (∫ y, dcBump r y)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (integral_dcBump_pos hr).le
  have he : iteratedDeriv q (dcProfile r) = fun t => c * iteratedDeriv q (dcBump r) t := by
    funext t
    exact iteratedDeriv_const_mul c (contDiffAt_of_smooth (contDiff_dcBump r) q t)
  have hvan : ∀ t, t ∉ Icc (-1 : ℝ) 1 → dcBump r t = 0 := fun t ht =>
    dcBump_vanishesOff hr t (by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  have hd : Continuous fun t => c * iteratedDeriv q (dcBump r) t :=
    continuous_const.mul ((contDiff_dcBump r).continuous_iteratedDeriv q (natCast_le_infty q))
  have hdR : SupportedIn 1 fun t => c * iteratedDeriv q (dcBump r) t := fun t ht => by
    show c * iteratedDeriv q (dcBump r) t = 0
    rw [iteratedDeriv_eq_zero_of_vanish hvan q (fun h => by
      have := abs_le.mpr ⟨h.1, h.2⟩; linarith), mul_zero]
  have hb : ∀ t, |c * iteratedDeriv q (dcBump r) t| ≤
      c * ((2 * ((r : ℝ) + 1) ^ (2 + (r : ℝ)⁻¹)) ^ q * (q.factorial : ℝ) ^ (1 + (r : ℝ)⁻¹)) :=
    fun t => by
      rw [abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (abs_iteratedDeriv_dcBump_le hr q t) hc
  rw [he]
  have := integral_abs_le_of_bound hd (hasCompactSupport_of_vanishes hdR) hb hdR zero_le_one
  linarith

end Profile

/-! ### The window `(log log N)^{1+ε}` -/

section Window

variable {r : ℕ}

/-- **The log-log overlap law for the Denjoy–Carleman profile of class `1 + 1/r`**: for odd `r`
and `α > 1 + 1/r`, RH holds iff for all large `N` Weil's form is nonnegative on the atomic families
of `φ_r` of width `(log log N)^α/N`. -/
theorem riemannHypothesis_iff_dcProfile_nonneg_loglog (hr : Odd r) {α : ℝ}
    (hα : 1 + (r : ℝ)⁻¹ < α) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / Real.log (Real.log N) ^ α) (dcProfile r))) :=
  riemannHypothesis_iff_atomicFamilies_nonneg_loglog (contDiff_dcProfile r)
    (dcProfile_vanishesOff hr) (integral_dcProfile hr) (by positivity) hα (by positivity)
    (integral_abs_iteratedDeriv_dcProfile_le hr)

/-- **The gauge for the Denjoy–Carleman profiles**: under Gevrey overlap growth of class `1 + 1/r`,
a bounded twist is seen iff it is not Weil positive. -/
theorem dcProfile_atomicFamilies_negative_iff (hr : Odd r) {lam : ℕ → ℝ}
    (hlam : ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n) {κ : ℕ → ℝ}
    (hκ : OverlapGrowthGevrey (1 + (r : ℝ)⁻¹) κ) :
    (∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw lam (atomicTest N x (dilate (κ N) (dcProfile r))) < 0) ↔ ¬ WeilPositiveFull lam :=
  atomicFamilies_negative_iff_of_gevrey hlam (contDiff_dcProfile r) (dcProfile_vanishesOff hr)
    (integral_dcProfile hr) (by positivity) (by positivity)
    (integral_abs_iteratedDeriv_dcProfile_le hr) hκ

/-- **The window `(log log N)^{1+ε}`**: for every `α > 1` there is an explicit smooth profile
`φ_r`, `r = 2⌈1/(α−1)⌉ + 1`, such that RH holds iff for all large `N` Weil's form is nonnegative
on its atomic families of width `(log log N)^α/N`. -/
theorem exists_dcProfile_loglog {α : ℝ} (hα : 1 < α) :
    ∃ r : ℕ, Odd r ∧ (RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / Real.log (Real.log N) ^ α)
        (dcProfile r)))) := by
  set m := ⌈(α - 1)⁻¹⌉₊
  refine ⟨2 * m + 1, odd_two_mul_add_one m, riemannHypothesis_iff_dcProfile_nonneg_loglog
    (odd_two_mul_add_one m) ?_⟩
  have hα1 : 0 < α - 1 := by linarith
  have hm : (α - 1)⁻¹ ≤ m := Nat.le_ceil _
  have hr : (α - 1)⁻¹ < ((2 * m + 1 : ℕ) : ℝ) := by
    push_cast; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hpos : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have : ((2 * m + 1 : ℕ) : ℝ)⁻¹ < α - 1 := by
    rw [inv_lt_comm₀ hpos hα1]; exact hr
  linarith

end Window

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
