import Mathlib

/-!
# Odd and even factorial series with geometric coefficients

For real coefficients with a geometric bound `|a_j| ≤ M R^j`, the series

```text
O_a(t) = Σ_j a_j t^{2j+1}/(2j+1)!,      E_a(t) = Σ_j a_j t^{2j}/(2j)!
```

converge absolutely at every real clock and satisfy `O_a' = E_a` and `E_a' = O_{a(·+1)}`; in
particular `O_a'' = O_{a(·+1)}`.  Termwise comparison of nonnegative coefficients transfers to
the series, and the geometric coefficients `c R^j` sum to the hyperbolic sine
`O_{cR^·}(t) = (c/√R) sinh(√R t)`.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The odd factorial series `Σ_j a_j t^{2j+1}/(2j+1)!`. -/
def oddFactorialSeries (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, a j * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)

/-- The even factorial series `Σ_j a_j t^{2j}/(2j)!`. -/
def evenFactorialSeries (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, a j * t ^ (2 * j) / ((2 * j).factorial : ℝ)

/-- A geometric coefficient bound. -/
def GeometricCoeffBound (a : ℕ → ℝ) (M R : ℝ) : Prop := ∀ j, |a j| ≤ M * R ^ j

theorem summable_geometric_div_factorial {M R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (k : ℕ) :
    Summable (fun j : ℕ => M * R ^ j * T ^ (2 * j + k) / ((2 * j + k).factorial : ℝ)) := by
  have hexp : Summable (fun n : ℕ => (Real.sqrt R * T + T) ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial _
  have hsub := hexp.comp_injective (i := fun j : ℕ => 2 * j + k)
    (by intro a b h; simp only at h; omega)
  refine (hsub.mul_left (|M| * (1 + 1 / (T + 1)) ^ k)).of_norm_bounded fun j => ?_
  simp only [Function.comp_apply, Real.norm_eq_abs]
  have hf : (0 : ℝ) < ((2 * j + k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [abs_div, abs_of_pos hf, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hR _),
    abs_of_nonneg (pow_nonneg hT _)]
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hf]
  have hsq : R ^ j * T ^ (2 * j) = (Real.sqrt R * T) ^ (2 * j) := by
    rw [mul_pow, pow_mul (Real.sqrt R) 2 j, Real.sq_sqrt hR]
  have h1 : (Real.sqrt R * T) ^ (2 * j) ≤ (Real.sqrt R * T + T) ^ (2 * j) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have h2 : T ^ k ≤ (Real.sqrt R * T + T) ^ k := pow_le_pow_left₀ hT (by nlinarith [Real.sqrt_nonneg R]) _
  have h1T : (1 : ℝ) ≤ 1 + 1 / (T + 1) := by
    have : 0 ≤ 1 / (T + 1) := by positivity
    linarith
  have hone : (1 : ℝ) ≤ (1 + 1 / (T + 1)) ^ k := one_le_pow₀ h1T
  calc |M| * R ^ j * T ^ (2 * j + k) = |M| * ((R ^ j * T ^ (2 * j)) * T ^ k) := by ring
    _ ≤ |M| * ((Real.sqrt R * T + T) ^ (2 * j) * (Real.sqrt R * T + T) ^ k) := by
        rw [hsq]; gcongr
    _ = |M| * 1 * (Real.sqrt R * T + T) ^ (2 * j + k) := by rw [pow_add]; ring
    _ ≤ |M| * (1 + 1 / (T + 1)) ^ k * (Real.sqrt R * T + T) ^ (2 * j + k) := by gcongr

theorem norm_oddEvenFactorialTerm_le {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R) {t T : ℝ}
    (ht : |t| ≤ T) (j k : ℕ) :
    ‖a j * t ^ (2 * j + k) / ((2 * j + k).factorial : ℝ)‖ ≤
      M * R ^ j * T ^ (2 * j + k) / ((2 * j + k).factorial : ℝ) := by
  have hf : (0 : ℝ) < ((2 * j + k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hf, abs_mul, abs_pow, div_le_div_iff_of_pos_right hf]
  exact mul_le_mul (ha j) (pow_le_pow_left₀ (abs_nonneg t) ht _) (by positivity)
    ((abs_nonneg _).trans (ha j))

theorem summable_oddFactorialSeries_term {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) (t : ℝ) :
    Summable (fun j : ℕ => a j * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) :=
  (summable_geometric_div_factorial (M := M) hR (abs_nonneg t) 1).of_norm_bounded
    fun j => norm_oddEvenFactorialTerm_le ha le_rfl j 1

theorem summable_evenFactorialSeries_term {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) (t : ℝ) :
    Summable (fun j : ℕ => a j * t ^ (2 * j) / ((2 * j).factorial : ℝ)) := by
  have h := (summable_geometric_div_factorial (M := M) hR (abs_nonneg t) 0).of_norm_bounded
    fun j => norm_oddEvenFactorialTerm_le ha le_rfl j 0
  simpa only [add_zero] using h

theorem GeometricCoeffBound.shift {a : ℕ → ℝ} {M R : ℝ}
    (ha : GeometricCoeffBound a M R) : GeometricCoeffBound (fun j => a (j + 1)) (M * R) R := by
  intro j
  have := ha (j + 1)
  rw [pow_succ] at this
  linarith [show M * R ^ j * R = M * R * R ^ j by ring]

/-- `O_a' = E_a`. -/
theorem hasDerivAt_oddFactorialSeries {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) (t : ℝ) :
    HasDerivAt (oddFactorialSeries a) (evenFactorialSeries a t) t := by
  set T := |t| + 1
  have hT : 0 ≤ T := by positivity
  have hderiv : ∀ (j : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) T →
      HasDerivAt (fun y => a j * y ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))
        (a j * y ^ (2 * j) / ((2 * j).factorial : ℝ)) y := by
    intro j y _
    have h := ((hasDerivAt_pow (2 * j + 1) y).const_mul (a j)).div_const
      ((2 * j + 1).factorial : ℝ)
    have hf : ((2 * j + 1).factorial : ℝ) = (2 * j + 1) * ((2 * j).factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hf0 : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have e : a j * (((2 * j + 1 : ℕ) : ℝ) * y ^ (2 * j + 1 - 1)) / ((2 * j + 1).factorial : ℝ) =
        a j * y ^ (2 * j) / ((2 * j).factorial : ℝ) := by
      rw [hf, Nat.add_sub_cancel]; push_cast; field_simp
    rw [e] at h
    exact h
  have hbound : ∀ (j : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) T →
      ‖a j * y ^ (2 * j) / ((2 * j).factorial : ℝ)‖ ≤
        M * R ^ j * T ^ (2 * j + 0) / ((2 * j + 0).factorial : ℝ) := by
    intro j y hy
    have hy' : |y| ≤ T := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy; exact hy.le
    simpa only [add_zero] using norm_oddEvenFactorialTerm_le ha hy' j 0
  have h := hasDerivAt_tsum_of_isPreconnected
    (summable_geometric_div_factorial (M := M) hR hT 0) Metric.isOpen_ball
    (convex_ball (0 : ℝ) T).isPreconnected hderiv hbound (Metric.mem_ball_self (by positivity))
    (summable_oddFactorialSeries_term hR ha 0)
    (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; simp only [T]; linarith)
  exact h

/-- `E_a' = O_{a(·+1)}`. -/
theorem hasDerivAt_evenFactorialSeries {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) (t : ℝ) :
    HasDerivAt (evenFactorialSeries a) (oddFactorialSeries (fun j => a (j + 1)) t) t := by
  set T := |t| + 1
  have hT : 0 ≤ T := by positivity
  have hsplit : evenFactorialSeries a = fun y => a 0 +
      ∑' j : ℕ, a (j + 1) * y ^ (2 * (j + 1)) / ((2 * (j + 1)).factorial : ℝ) := by
    funext y
    unfold evenFactorialSeries
    rw [(summable_evenFactorialSeries_term hR ha y).tsum_eq_zero_add]
    simp
  rw [hsplit]
  have ha' := ha.shift
  have hderiv : ∀ (j : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) T →
      HasDerivAt (fun y => a (j + 1) * y ^ (2 * (j + 1)) / ((2 * (j + 1)).factorial : ℝ))
        (a (j + 1) * y ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) y := by
    intro j y _
    have h := ((hasDerivAt_pow (2 * (j + 1)) y).const_mul (a (j + 1))).div_const
      ((2 * (j + 1)).factorial : ℝ)
    have hf : ((2 * (j + 1)).factorial : ℝ) = (2 * j + 2) * ((2 * j + 1).factorial : ℝ) := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ]; push_cast; ring
    have hf0 : ((2 * j + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have e : a (j + 1) * (((2 * (j + 1) : ℕ) : ℝ) * y ^ (2 * (j + 1) - 1)) /
        ((2 * (j + 1)).factorial : ℝ) = a (j + 1) * y ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) := by
      rw [hf, show 2 * (j + 1) - 1 = 2 * j + 1 by omega]; push_cast; field_simp
    rw [e] at h
    exact h
  have hbound : ∀ (j : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) T →
      ‖a (j + 1) * y ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)‖ ≤
        M * R * R ^ j * T ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) := by
    intro j y hy
    have hy' : |y| ≤ T := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy; exact hy.le
    exact norm_oddEvenFactorialTerm_le ha' hy' j 1
  have hs0 : Summable (fun j : ℕ =>
      a (j + 1) * (0 : ℝ) ^ (2 * (j + 1)) / ((2 * (j + 1)).factorial : ℝ)) := by
    simp
  have h := hasDerivAt_tsum_of_isPreconnected
    (summable_geometric_div_factorial (M := M * R) hR hT 1) Metric.isOpen_ball
    (convex_ball (0 : ℝ) T).isPreconnected hderiv hbound (Metric.mem_ball_self (by positivity))
    hs0 (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; simp only [T]; linarith)
  exact h.const_add (a 0)

/-- `O_a'' = O_{a(·+1)}`. -/
theorem iteratedDeriv_two_oddFactorialSeries {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) (t : ℝ) :
    iteratedDeriv 2 (oddFactorialSeries a) t = oddFactorialSeries (fun j => a (j + 1)) t := by
  have h1 : deriv (oddFactorialSeries a) = evenFactorialSeries a :=
    funext fun t => (hasDerivAt_oddFactorialSeries hR ha t).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, (hasDerivAt_evenFactorialSeries hR ha t).deriv]

theorem contDiff_two_oddFactorialSeries {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) : ContDiff ℝ 2 (oddFactorialSeries a) := by
  have hd : Differentiable ℝ (oddFactorialSeries a) := fun t =>
    (hasDerivAt_oddFactorialSeries hR ha t).differentiableAt
  have h1 : deriv (oddFactorialSeries a) = evenFactorialSeries a :=
    funext fun t => (hasDerivAt_oddFactorialSeries hR ha t).deriv
  have hd2 : Differentiable ℝ (evenFactorialSeries a) := fun t =>
    (hasDerivAt_evenFactorialSeries hR ha t).differentiableAt
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨hd, by simp, ?_⟩
  rw [h1, contDiff_one_iff_deriv]
  refine ⟨hd2, ?_⟩
  have h2 : deriv (evenFactorialSeries a) = oddFactorialSeries (fun j => a (j + 1)) :=
    funext fun t => (hasDerivAt_evenFactorialSeries hR ha t).deriv
  rw [h2]
  have hd3 : Differentiable ℝ (oddFactorialSeries fun j => a (j + 1)) := fun t =>
    (hasDerivAt_oddFactorialSeries hR (ha.shift) t).differentiableAt
  exact hd3.continuous

/-- Termwise comparison for nonnegative clocks. -/
theorem oddFactorialSeries_le_of_le {a b : ℕ → ℝ} {M R M' R' : ℝ} (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (ha : GeometricCoeffBound a M R) (hb : GeometricCoeffBound b M' R') (hab : ∀ j, a j ≤ b j)
    {t : ℝ} (ht : 0 ≤ t) : oddFactorialSeries a t ≤ oddFactorialSeries b t :=
  Summable.tsum_le_tsum (fun j => by gcongr; exact hab j)
    (summable_oddFactorialSeries_term hR ha t) (summable_oddFactorialSeries_term hR' hb t)

/-- Strict termwise comparison for positive clocks, from one strict coefficient. -/
theorem oddFactorialSeries_lt_of_le_of_lt {a b : ℕ → ℝ} {M R M' R' : ℝ} (hR : 0 ≤ R)
    (hR' : 0 ≤ R') (ha : GeometricCoeffBound a M R) (hb : GeometricCoeffBound b M' R')
    (hab : ∀ j, a j ≤ b j) {i : ℕ} (hi : a i < b i) {t : ℝ} (ht : 0 < t) :
    oddFactorialSeries a t < oddFactorialSeries b t :=
  Summable.tsum_lt_tsum (i := i) (fun j => by gcongr; exact hab j)
    (by
      have hf : (0 : ℝ) < ((2 * i + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hp : 0 < t ^ (2 * i + 1) := pow_pos ht _
      exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hi hp) hf)
    (summable_oddFactorialSeries_term hR ha t) (summable_oddFactorialSeries_term hR' hb t)

/-- Geometric coefficients sum to a hyperbolic sine: `Σ_j c R^j t^{2j+1}/(2j+1)! =
(c/√R) sinh(√R t)` for `R > 0`. -/
theorem oddFactorialSeries_geometric {c R : ℝ} (hR : 0 < R) (t : ℝ) :
    oddFactorialSeries (fun j => c * R ^ j) t = c / Real.sqrt R * Real.sinh (Real.sqrt R * t) := by
  have hs := Real.sinh_eq_tsum (Real.sqrt R * t)
  have hsR : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  unfold oddFactorialSeries
  rw [hs, ← tsum_mul_left]
  congr 1
  funext j
  show c * R ^ j * t ^ (2 * j + 1) / _ = _
  rw [mul_pow, pow_succ (Real.sqrt R), pow_mul (Real.sqrt R), Real.sq_sqrt hR.le]
  field_simp

end GaloisForLFunctions.HTGeometry
