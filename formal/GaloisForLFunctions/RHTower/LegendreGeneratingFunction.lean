import GaloisForLFunctions.RHTower.SemilocalDiagonalLegendre
import GaloisForLFunctions.RHTower.SemilocalJacobiMeixnerPollaczekGeneratingFunction
import GaloisForLFunctions.RHTower.ScalarPowerSeriesUniqueness

/-!
# The generating function of the Legendre polynomials

For the explicit Legendre polynomials `P_N` (`legendre`) we prove the three-term recurrence
`(N+2) P_{N+2} = (2N+3) x P_{N+1} − (N+1) P_N` coefficientwise, and the generating function

`Σ_N P_N(x) w^N = (1 − 2xw + w²)^{−1/2}`   (`|x| ≤ 1`, `‖w‖ < 1/4`)

by the ODE `(1 − 2xw + w²) A′ = (x − w) A`, its derivative recurrence at `0`
(coordinate Leibniz rules), and Cauchy's Taylor theorem.
-/

open Finset Complex
open scoped BigOperators

namespace RHTower

namespace LegendreBoost

open ScaledHypergeometric MeixnerPollaczek PowerSeriesUniqueness GaloisForLFunctions.HTGeometry

/-! ## The coefficient recurrence -/

/-- `c(n, k−1)` with `c(n, −1) = 0`. -/
noncomputable def legendreCoeffPrev (n k : ℕ) : ℝ := if k = 0 then 0 else legendreCoeff n (k - 1)

theorem legendreCoeff_recurrence (n k : ℕ) :
    ((n : ℝ) + 2) * legendreCoeff (n + 2) k =
      (2 * (n : ℝ) + 3) * legendreCoeff (n + 1) k - ((n : ℝ) + 1) * legendreCoeffPrev n k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- k = 0
    subst hk
    simp only [legendreCoeffPrev, if_true, mul_zero, sub_zero]
    unfold legendreCoeff
    rw [if_pos (show 2 * 0 ≤ n + 2 by omega), if_pos (show 2 * 0 ≤ n + 1 by omega)]
    simp only [mul_zero, Nat.sub_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
    rw [show 2 * (n + 2) = 2 * (n + 1) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      show n + 2 = n + 1 + 1 by ring, Nat.factorial_succ (n + 1), pow_succ, pow_succ]
    push_cast
    have h1 : ((2 * (n + 1)).factorial : ℝ) ≠ 0 := by exact_mod_cast (2 * (n + 1)).factorial_ne_zero
    have h2 : ((n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (n + 1).factorial_ne_zero
    have h3 : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
    ring
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [legendreCoeffPrev, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rcases lt_or_ge (n + 2) (2 * (k' + 1)) with hc | hc
    · -- all coefficients vanish
      rw [legendreCoeff_eq_zero_of_lt (by omega), legendreCoeff_eq_zero_of_lt (by omega),
        legendreCoeff_eq_zero_of_lt (by omega)]
      ring
    rcases lt_or_ge (n + 1) (2 * (k' + 1)) with hb | hb
    · -- 2k = n + 2 : n = 2k'
      have hn : n = 2 * k' := by omega
      subst hn
      rw [legendreCoeff_eq_zero_of_lt (N := 2 * k' + 1) (k := k' + 1) (by omega)]
      unfold legendreCoeff
      rw [if_pos (show 2 * (k' + 1) ≤ 2 * k' + 2 by omega), if_pos (show 2 * k' ≤ 2 * k' by omega)]
      rw [show 2 * (2 * k' + 2) - 2 * (k' + 1) = 2 * k' + 1 + 1 by omega,
        show 2 * k' + 2 - (k' + 1) = k' + 1 by omega, show 2 * k' + 2 - 2 * (k' + 1) = 0 by omega,
        show 2 * (2 * k') - 2 * k' = 2 * k' by omega, show 2 * k' - k' = k' by omega,
        show 2 * k' - 2 * k' = 0 by omega, Nat.factorial_succ, Nat.factorial_succ,
        Nat.factorial_succ k', pow_succ, pow_succ]
      push_cast
      have h1 : ((2 * k').factorial : ℝ) ≠ 0 := by exact_mod_cast (2 * k').factorial_ne_zero
      have h2 : (k'.factorial : ℝ) ≠ 0 := by exact_mod_cast k'.factorial_ne_zero
      have h3 : (2 : ℝ) ^ (2 * k') ≠ 0 := by positivity
      field_simp
      ring
    · -- generic case: n = 2k' + c + 1
      obtain ⟨c, rfl⟩ : ∃ c, n = 2 * k' + c + 1 := ⟨n - 2 * k' - 1, by omega⟩
      unfold legendreCoeff
      rw [if_pos (show 2 * (k' + 1) ≤ 2 * k' + c + 1 + 2 by omega),
        if_pos (show 2 * (k' + 1) ≤ 2 * k' + c + 1 + 1 by omega),
        if_pos (show 2 * k' ≤ 2 * k' + c + 1 by omega)]
      rw [show 2 * (2 * k' + c + 1 + 2) - 2 * (k' + 1) = 2 * (k' + c + 1) + 1 + 1 by omega,
        show 2 * k' + c + 1 + 2 - (k' + 1) = k' + c + 1 + 1 by omega,
        show 2 * k' + c + 1 + 2 - 2 * (k' + 1) = c + 1 by omega,
        show 2 * (2 * k' + c + 1 + 1) - 2 * (k' + 1) = 2 * (k' + c + 1) by omega,
        show 2 * k' + c + 1 + 1 - (k' + 1) = k' + c + 1 by omega,
        show 2 * k' + c + 1 + 1 - 2 * (k' + 1) = c by omega,
        show 2 * (2 * k' + c + 1) - 2 * k' = 2 * (k' + c + 1) by omega,
        show 2 * k' + c + 1 - k' = k' + c + 1 by omega,
        show 2 * k' + c + 1 - 2 * k' = c + 1 by omega,
        Nat.factorial_succ (2 * (k' + c + 1) + 1), Nat.factorial_succ (2 * (k' + c + 1)),
        Nat.factorial_succ (k' + c + 1), Nat.factorial_succ c, Nat.factorial_succ k',
        show 2 * k' + c + 1 + 2 = 2 * k' + c + 1 + 1 + 1 by ring, pow_succ, pow_succ]
      push_cast
      have h1 : ((2 * (k' + c + 1)).factorial : ℝ) ≠ 0 := by
        exact_mod_cast (2 * (k' + c + 1)).factorial_ne_zero
      have h2 : ((k' + c + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (k' + c + 1).factorial_ne_zero
      have h3 : (c.factorial : ℝ) ≠ 0 := by exact_mod_cast c.factorial_ne_zero
      have h4 : (k'.factorial : ℝ) ≠ 0 := by exact_mod_cast k'.factorial_ne_zero
      have h5 : (2 : ℝ) ^ (2 * k' + c + 1) ≠ 0 := by positivity
      field_simp
      ring

/-! ## The three-term recurrence -/

theorem legendre_zero (x : ℝ) : legendre 0 x = 1 := by
  simp [legendre, legendreCoeff]

theorem legendre_one (x : ℝ) : legendre 1 x = x := by
  unfold legendre
  rw [sum_range_succ, sum_range_one, legendreCoeff_eq_zero_of_lt (by norm_num : 1 < 2 * 1)]
  unfold legendreCoeff
  rw [if_pos (by norm_num)]
  norm_num [Nat.factorial]

/-- **Three-term recurrence:** `(n+2) P_{n+2} = (2n+3) x P_{n+1} − (n+1) P_n`. -/
theorem legendre_recurrence (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * legendre (n + 2) x =
      (2 * (n : ℝ) + 3) * x * legendre (n + 1) x - ((n : ℝ) + 1) * legendre n x := by
  have hA : legendre (n + 2) x = ∑ k ∈ range (n + 3), legendreCoeff (n + 2) k * x ^ (n + 2 - 2 * k) := rfl
  have hB : x * legendre (n + 1) x =
      ∑ k ∈ range (n + 3), legendreCoeff (n + 1) k * x ^ (n + 2 - 2 * k) := by
    unfold legendre
    rw [mul_sum, sum_range_succ _ (n + 2), legendreCoeff_eq_zero_of_lt (by omega), zero_mul, add_zero]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rcases le_or_gt (2 * k) (n + 1) with h | h
    · rw [show n + 2 - 2 * k = (n + 1 - 2 * k) + 1 by omega, pow_succ]
      ring
    · rw [legendreCoeff_eq_zero_of_lt (by omega)]
      ring
  have hC : legendre n x = ∑ k ∈ range (n + 3), legendreCoeffPrev n k * x ^ (n + 2 - 2 * k) := by
    unfold legendre
    rw [sum_range_succ' _ (n + 2)]
    simp only [legendreCoeffPrev, if_true, zero_mul, add_zero, Nat.succ_ne_zero, if_false,
      Nat.add_sub_cancel]
    rw [sum_range_succ _ (n + 1), legendreCoeff_eq_zero_of_lt (by omega), zero_mul, add_zero]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [show n + 2 - 2 * (k + 1) = n - 2 * k by omega]
  rw [show (2 * (n : ℝ) + 3) * x * legendre (n + 1) x =
    (2 * (n : ℝ) + 3) * (x * legendre (n + 1) x) by ring]
  rw [hA, hB, hC, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  have := legendreCoeff_recurrence n k
  linear_combination (x ^ (n + 2 - 2 * k)) * this

/-! ## The generating function -/

/-- `A(w) = (1 − 2xw + w²)^{−1/2}`. -/
noncomputable def legendreGen (x : ℝ) (w : ℂ) : ℂ :=
  (1 - 2 * (x : ℂ) * w + w ^ 2) ^ (-(1 / 2 : ℂ))

theorem re_legendreBase_pos {x : ℝ} (hx : |x| ≤ 1) {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    0 < (1 - 2 * (x : ℂ) * w + w ^ 2).re := by
  have h1 : |(2 * (x : ℂ) * w).re| ≤ 1 / 2 := by
    calc |(2 * (x : ℂ) * w).re| ≤ ‖2 * (x : ℂ) * w‖ := abs_re_le_norm _
      _ = 2 * |x| * ‖w‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]; norm_num
      _ ≤ 2 * 1 * (1 / 4) := by gcongr
      _ = 1 / 2 := by norm_num
  have h2 : |(w ^ 2).re| ≤ 1 / 16 := by
    calc |(w ^ 2).re| ≤ ‖w ^ 2‖ := abs_re_le_norm _
      _ = ‖w‖ ^ 2 := norm_pow _ _
      _ ≤ (1 / 4) ^ 2 := by gcongr
      _ = 1 / 16 := by norm_num
  simp only [add_re, sub_re, one_re]
  linarith [(abs_le.mp h1).2, (abs_le.mp h2).1]

theorem legendreBase_mem_slitPlane {x : ℝ} (hx : |x| ≤ 1) {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    1 - 2 * (x : ℂ) * w + w ^ 2 ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (re_legendreBase_pos hx hw))

theorem legendreBase_ne_zero {x : ℝ} (hx : |x| ≤ 1) {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    1 - 2 * (x : ℂ) * w + w ^ 2 ≠ 0 :=
  slitPlane_ne_zero (legendreBase_mem_slitPlane hx hw)

theorem hasDerivAt_legendreGen {x : ℝ} (hx : |x| ≤ 1) {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    HasDerivAt (legendreGen x)
      (legendreGen x w * ((x : ℂ) - w) / (1 - 2 * (x : ℂ) * w + w ^ 2)) w := by
  have hbase : HasDerivAt (fun z : ℂ => 1 - 2 * (x : ℂ) * z + z ^ 2) (-(2 * (x : ℂ)) + 2 * w) w := by
    have h1 : HasDerivAt (fun z : ℂ => 1 - 2 * (x : ℂ) * z) (-(2 * (x : ℂ))) w := by
      simpa using ((hasDerivAt_id w).const_mul (2 * (x : ℂ))).const_sub 1
    have h2 : HasDerivAt (fun z : ℂ => z ^ 2) (2 * w) w := by
      simpa using hasDerivAt_pow 2 w
    exact h1.add h2
  have h := hbase.cpow_const (c := -(1 / 2 : ℂ)) (legendreBase_mem_slitPlane hx hw)
  refine h.congr_deriv ?_
  have hne := legendreBase_ne_zero hx hw
  rw [cpow_sub _ _ hne, cpow_one]
  unfold legendreGen
  field_simp
  ring

theorem differentiableOn_legendreGen {x : ℝ} (hx : |x| ≤ 1) :
    DifferentiableOn ℂ (legendreGen x) (Metric.ball (0 : ℂ) (1 / 4)) := by
  intro w hw
  have hw' : ‖w‖ < 1 / 4 := by simpa using hw
  exact (hasDerivAt_legendreGen hx hw').differentiableAt.differentiableWithinAt

theorem legendreGen_ode {x : ℝ} (hx : |x| ≤ 1) {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    (1 - 2 * (x : ℂ) * w + w ^ 2) * deriv (legendreGen x) w = ((x : ℂ) - w) * legendreGen x w := by
  rw [(hasDerivAt_legendreGen hx hw).deriv]
  have hne := legendreBase_ne_zero hx hw
  field_simp

theorem contDiffAt_legendreGen {x : ℝ} (hx : |x| ≤ 1) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (legendreGen x) 0 :=
  ((differentiableOn_legendreGen hx).contDiffOn Metric.isOpen_ball).contDiffAt
    (Metric.ball_mem_nhds _ (by norm_num))

theorem contDiffAt_deriv_legendreGen {x : ℝ} (hx : |x| ≤ 1) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (deriv (legendreGen x)) 0 :=
  (((differentiableOn_legendreGen hx).deriv Metric.isOpen_ball).contDiffOn
    Metric.isOpen_ball).contDiffAt (Metric.ball_mem_nhds _ (by norm_num))

/-- `D_n = A^{(n)}(0)`. -/
noncomputable def legendreDerivative (x : ℝ) (n : ℕ) : ℂ := iteratedDeriv n (legendreGen x) 0

theorem legendreDerivative_zero (x : ℝ) : legendreDerivative x 0 = 1 := by
  unfold legendreDerivative
  rw [iteratedDeriv_zero]
  simp [legendreGen]

theorem legendreDerivative_one {x : ℝ} (hx : |x| ≤ 1) : legendreDerivative x 1 = x := by
  unfold legendreDerivative
  rw [iteratedDeriv_one, (hasDerivAt_legendreGen hx (by simp)).deriv]
  simp [legendreGen]

theorem iteratedDeriv_deriv_legendreGen (x : ℝ) (n : ℕ) :
    iteratedDeriv n (deriv (legendreGen x)) 0 = legendreDerivative x (n + 1) := by
  unfold legendreDerivative
  rw [iteratedDeriv_succ']

/-- **Derivative recurrence:** `D_{n+2} = (2n+3) x D_{n+1} − (n+1)² D_n`. -/
theorem legendreDerivative_recurrence {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    legendreDerivative x (n + 2) =
      (2 * (n : ℂ) + 3) * (x : ℂ) * legendreDerivative x (n + 1) -
        ((n : ℂ) + 1) ^ 2 * legendreDerivative x n := by
  set A := legendreGen x with hA
  set L : ℂ → ℂ := fun w => deriv A w - 2 * (x : ℂ) * (w * deriv A w) + w * (w * deriv A w) with hL
  set R : ℂ → ℂ := fun w => (x : ℂ) * A w - w * A w with hR
  have hLR : L =ᶠ[nhds (0 : ℂ)] R := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)] with w hw
    have hw' : ‖w‖ < 1 / 4 := by simpa using hw
    have := legendreGen_ode hx hw'
    simp only [hL, hR]
    linear_combination this
  have hcA : ∀ m : WithTop ℕ∞, ContDiffAt ℂ m A 0 := contDiffAt_legendreGen hx
  have hcA' : ∀ m : WithTop ℕ∞, ContDiffAt ℂ m (deriv A) 0 := contDiffAt_deriv_legendreGen hx
  have hkey := hLR.iteratedDeriv_eq (n + 1)
  have hleft : iteratedDeriv (n + 1) L 0 =
      legendreDerivative x (n + 2) - 2 * (x : ℂ) * ((n : ℂ) + 1) * legendreDerivative x (n + 1) +
        ((n : ℂ) + 1) * n * legendreDerivative x n := by
    have hsplit : L = (deriv A - fun w => 2 * (x : ℂ) * (w * deriv A w)) +
        fun w => w * (w * deriv A w) := by
      funext w; simp [hL]
    have hc1 : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) (fun w : ℂ => w * deriv A w) 0 :=
      contDiffAt_id.mul (hcA' _)
    have hc2 : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) (fun w : ℂ => 2 * (x : ℂ) * (w * deriv A w)) 0 :=
      contDiffAt_const.mul hc1
    have hc3 : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) (fun w : ℂ => w * (w * deriv A w)) 0 :=
      contDiffAt_id.mul hc1
    have hc0 : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞)
        (deriv A - fun w : ℂ => 2 * (x : ℂ) * (w * deriv A w)) 0 := (hcA' _).sub hc2
    rw [hsplit, iteratedDeriv_add hc0 hc3, iteratedDeriv_sub (hcA' _) hc2,
      iteratedDeriv_const_mul _ hc1, iteratedDeriv_id_mul_zero_succ_of_contDiffAt _ n (hcA' _),
      iteratedDeriv_id_mul_id_mul_zero _ hcA', iteratedDeriv_deriv_legendreGen,
      iteratedDeriv_deriv_legendreGen]
    cases n with
    | zero => simp
    | succ m =>
        rw [iteratedDeriv_deriv_legendreGen]
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
  have hright : iteratedDeriv (n + 1) R 0 =
      (x : ℂ) * legendreDerivative x (n + 1) - ((n : ℂ) + 1) * legendreDerivative x n := by
    have hsplit : R = (fun w => (x : ℂ) * A w) - fun w => w * A w := by
      funext w; simp [hR]
    have hc1 : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) (fun w : ℂ => (x : ℂ) * A w) 0 :=
      contDiffAt_const.mul (hcA _)
    have hc2 : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) (fun w : ℂ => w * A w) 0 :=
      contDiffAt_id.mul (hcA _)
    rw [hsplit, iteratedDeriv_sub hc1 hc2, iteratedDeriv_const_mul _ (hcA _),
      iteratedDeriv_id_mul_zero_succ_of_contDiffAt A n (hcA _)]
    unfold legendreDerivative
    push_cast
    ring
  rw [hleft, hright] at hkey
  linear_combination hkey

/-- `D_n = n! P_n(x)`. -/
theorem legendreDerivative_eq_factorial_mul_pair {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    legendreDerivative x n = (n.factorial : ℂ) * (legendre n x : ℂ) ∧
      legendreDerivative x (n + 1) = ((n + 1).factorial : ℂ) * (legendre (n + 1) x : ℂ) := by
  induction n with
  | zero =>
      exact ⟨by simp [legendreDerivative_zero, legendre_zero],
        by simp [legendreDerivative_one hx, legendre_one]⟩
  | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hfac : ((n + 1 + 1).factorial : ℂ) = ((n : ℂ) + 2) * ((n : ℂ) + 1) * (n.factorial : ℂ) := by
        rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
      have hfac1 : ((n + 1).factorial : ℂ) = ((n : ℂ) + 1) * (n.factorial : ℂ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hrec := legendre_recurrence n x
      have hrecC : ((n : ℂ) + 2) * (legendre (n + 2) x : ℂ) =
          (2 * (n : ℂ) + 3) * (x : ℂ) * (legendre (n + 1) x : ℂ) -
            ((n : ℂ) + 1) * (legendre n x : ℂ) := by
        have h := congrArg (fun y : ℝ => (y : ℂ)) hrec
        push_cast at h
        linear_combination h
      change legendreDerivative x (n + 2) = ((n + 1 + 1).factorial : ℂ) * (legendre (n + 2) x : ℂ)
      rw [legendreDerivative_recurrence hx, ih.2, ih.1, hfac, hfac1]
      linear_combination (-((n : ℂ) + 1) * (n.factorial : ℂ)) * hrecC

theorem legendreDerivative_eq_factorial_mul {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    legendreDerivative x n = (n.factorial : ℂ) * (legendre n x : ℂ) :=
  (legendreDerivative_eq_factorial_mul_pair hx n).1

/-- **Generating function of the Legendre polynomials:** for `|x| ≤ 1` and `‖w‖ < 1/4`,
`Σ_N P_N(x) w^N = (1 − 2xw + w²)^{−1/2}`. -/
theorem hasSum_legendreGen {x : ℝ} (hx : |x| ≤ 1) {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    HasSum (fun N : ℕ => (legendre N x : ℂ) * w ^ N) (legendreGen x w) := by
  have hmem : w ∈ Metric.ball (0 : ℂ) (1 / 4) := by simpa using hw
  have h := Complex.hasSum_taylorSeries_on_ball (differentiableOn_legendreGen hx) hmem
  refine h.congr_fun fun N => ?_
  rw [sub_zero, smul_eq_mul, smul_eq_mul]
  change (legendre N x : ℂ) * w ^ N = _ * (w ^ N * legendreDerivative x N)
  rw [legendreDerivative_eq_factorial_mul hx]
  have hf : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  field_simp

end LegendreBoost

end RHTower
