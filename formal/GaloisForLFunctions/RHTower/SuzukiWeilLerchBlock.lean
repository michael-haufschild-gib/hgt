import GaloisForLFunctions.RHTower.SuzukiExplicitScrewZeroSeries
import GaloisForLFunctions.RHTower.DigammaDifferenceSeries
import GaloisForLFunctions.RHTower.ZetaRealBound

/-!
# The archimedean Lerch block of Suzuki's function `𝔓_t`

Suzuki, *On the Hilbert space derived from the Weil distribution* (arXiv:2301.00421v3), equation
(1.6), contains the archimedean pair

```text
- (1/(2iz)) [ ψ(1/4 - iz/2) - ψ(1/4) ]
- (1/(2iz)) e^{-t/2} [ Φ(e^{-2t}, 1, (1/2)(1/2 - iz)) - Φ(e^{-2t}, 1, 1/4) ].
```

Neither Hurwitz--Lerch value converges separately at `t = 0`, but their difference does, for every
`t ≥ 0`.  This module therefore defines the *difference* as one absolutely convergent series

```text
suzukiLerchDiff t w = ∑_{n ≥ 0} e^{-2nt} ( (n + w)⁻¹ - (n + 1/4)⁻¹ ),
```

proves the exact factorization `suzukiLerchDiff t w = (1/4 - w) · suzukiLerchKernel t w` with

```text
suzukiLerchKernel t w = ∑_{n ≥ 0} e^{-2nt} / ((n + w)(n + 1/4)),
```

identifies `suzukiLerchKernel t (1/4) = 4 e^{t/2} · screwLerchTail t` with the corpus's Lerch tail,
proves the Gauss-series bridge `ψ(w) - ψ(1/4) = -suzukiLerchDiff 0 w`, and proves the kernel
continuous at the base point `1/4`.

The factorization removes the apparent `0/0` in both archimedean terms of (1.6): the whole
`1/(2iz)` prefactor cancels, leaving `(1/4)·suzukiLerchKernel` and no limit to take.

Everything here is unconditional.
-/

open Complex Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-- The `n`-th summand of Suzuki's regularized Hurwitz--Lerch difference. -/
def suzukiLerchDiffTerm (t : ℝ) (w : ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-(2 * n * t)) : ℂ) * (((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹)

/-- **Suzuki eq. (1.6), archimedean Lerch block.**  The regularized difference
`Φ(e^{-2t}, 1, w) - Φ(e^{-2t}, 1, 1/4)`, defined by its absolutely convergent series. -/
def suzukiLerchDiff (t : ℝ) (w : ℂ) : ℂ := ∑' n : ℕ, suzukiLerchDiffTerm t w n

/-- The `n`-th summand of the factored Lerch kernel. -/
def suzukiLerchKernelTerm (t : ℝ) (w : ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-(2 * n * t)) : ℂ) / (((n : ℂ) + w) * ((n : ℂ) + 1 / 4))

/-- The factored Lerch kernel `∑_n e^{-2nt}/((n+w)(n+1/4))`. -/
def suzukiLerchKernel (t : ℝ) (w : ℂ) : ℂ := ∑' n : ℕ, suzukiLerchKernelTerm t w n

/-- The shifted square series converges.  This is the corpus's shifted `p`-series
`GaloisForLFunctions.RHTower.summable_one_div_nat_add_one_rpow` at the natural exponent `2`. -/
theorem summable_one_div_nat_add_one_sq :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  refine (summable_one_div_nat_add_one_rpow (a := 2) (by norm_num)).congr fun n => ?_
  have hrw : ((n : ℝ) + 1) ^ (2 : ℝ) = ((n : ℝ) + 1) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast ((n : ℝ) + 1) 2]
    norm_num
  rw [hrw]

/-- A real-part lower bound for `‖n + w‖`, for an arbitrary complex `w` in the right half-plane.
(The corpus's `norm_vertical_add_nat_ge_re` is the special case of a fixed vertical line.) -/
theorem le_norm_nat_add {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    (n : ℝ) + w.re ≤ ‖(n : ℂ) + w‖ := by
  have h : |((n : ℂ) + w).re| ≤ ‖(n : ℂ) + w‖ := Complex.abs_re_le_norm _
  have hre : ((n : ℂ) + w).re = (n : ℝ) + w.re := by simp
  rw [hre] at h
  have hpos : 0 ≤ (n : ℝ) + w.re := by positivity
  rwa [abs_of_nonneg hpos] at h

/-- The base-point denominators never vanish. -/
theorem nat_add_quarter_ne_zero (n : ℕ) : ((n : ℂ) + 1 / 4) ≠ 0 := by
  intro h
  have : ((n : ℂ) + 1 / 4).re = 0 := by rw [h]; simp
  simp at this
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- On the right half-plane the shifted denominators never vanish. -/
theorem nat_add_ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) (n : ℕ) : ((n : ℂ) + w) ≠ 0 := by
  intro h
  have h2 : (0 : ℝ) < (n : ℝ) + w.re := by positivity
  have := le_norm_nat_add hw n
  rw [h] at this
  simp at this
  linarith

/-- Exact norm of the base-point denominator. -/
theorem norm_nat_add_quarter (n : ℕ) : ‖((n : ℂ) + 1 / 4)‖ = (n : ℝ) + 1 / 4 := by
  have h : ((n : ℂ) + 1 / 4) = (((n : ℝ) + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The exponential weight is bounded by one on the source half-line `t ≥ 0`. -/
theorem norm_exp_block_le {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ‖(Real.exp (-(2 * n * t)) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

/-- Uniform majorant for the kernel terms on a right half-plane `c ≤ Re w`. -/
theorem norm_suzukiLerchKernelTerm_le {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1)
    {w : ℂ} (hw : c ≤ w.re) (n : ℕ) :
    ‖suzukiLerchKernelTerm t w n‖ ≤ (4 / c) * (1 / ((n : ℝ) + 1) ^ 2) := by
  have hwre : 0 < w.re := lt_of_lt_of_le hc hw
  have hnorm1 : (n : ℝ) + c ≤ ‖(n : ℂ) + w‖ :=
    le_trans (by linarith [le_norm_nat_add hwre n]) (le_norm_nat_add hwre n)
  have hc1' : c * ((n : ℝ) + 1) ≤ (n : ℝ) + c := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hq1 : (1 / 4 : ℝ) * ((n : ℝ) + 1) ≤ (n : ℝ) + 1 / 4 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hden : (c / 4) * ((n : ℝ) + 1) ^ 2 ≤ ‖(n : ℂ) + w‖ * ‖((n : ℂ) + 1 / 4)‖ := by
    rw [norm_nat_add_quarter]
    calc (c / 4) * ((n : ℝ) + 1) ^ 2 = (c * ((n : ℝ) + 1)) * ((1 / 4 : ℝ) * ((n : ℝ) + 1)) := by
          ring
      _ ≤ ((n : ℝ) + c) * ((n : ℝ) + 1 / 4) :=
          mul_le_mul hc1' hq1 (by positivity) (by positivity)
      _ ≤ ‖(n : ℂ) + w‖ * ((n : ℝ) + 1 / 4) :=
          mul_le_mul_of_nonneg_right hnorm1 (by positivity)
  have hdpos : 0 < (c / 4) * ((n : ℝ) + 1) ^ 2 := by positivity
  rw [suzukiLerchKernelTerm, norm_div, norm_mul]
  rw [div_le_iff₀ (lt_of_lt_of_le hdpos hden)]
  calc ‖(Real.exp (-(2 * n * t)) : ℂ)‖ ≤ 1 := norm_exp_block_le ht n
    _ = (4 / c) * (1 / ((n : ℝ) + 1) ^ 2) * ((c / 4) * ((n : ℝ) + 1) ^ 2) := by field_simp
    _ ≤ (4 / c) * (1 / ((n : ℝ) + 1) ^ 2) * (‖(n : ℂ) + w‖ * ‖((n : ℂ) + 1 / 4)‖) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- The Lerch kernel converges absolutely on the right half-plane. -/
theorem summable_suzukiLerchKernelTerm {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : 0 < w.re) :
    Summable (suzukiLerchKernelTerm t w) := by
  set c : ℝ := min w.re 1 with hcdef
  have hc : 0 < c := lt_min hw one_pos
  refine Summable.of_norm_bounded (summable_one_div_nat_add_one_sq.mul_left (4 / c)) ?_
  intro n
  exact norm_suzukiLerchKernelTerm_le ht hc (min_le_right _ _) (min_le_left _ _) n

/-! ## The factorization -/

theorem suzukiLerchDiffTerm_eq {t : ℝ} {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    suzukiLerchDiffTerm t w n = (1 / 4 - w) * suzukiLerchKernelTerm t w n := by
  have h1 : ((n : ℂ) + w) ≠ 0 := nat_add_ne_zero_of_re_pos hw n
  have h2 : ((n : ℂ) + 1 / 4) ≠ 0 := nat_add_quarter_ne_zero n
  have key : ((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹
      = (1 / 4 - w) / (((n : ℂ) + w) * ((n : ℂ) + 1 / 4)) := by
    rw [inv_sub_inv h1 h2]
    congr 1
    ring
  rw [suzukiLerchDiffTerm, suzukiLerchKernelTerm, key]
  ring

/-- The Lerch difference converges absolutely on the right half-plane, for every `t`. -/
theorem summable_suzukiLerchDiffTerm {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : 0 < w.re) :
    Summable (suzukiLerchDiffTerm t w) := by
  refine ((summable_suzukiLerchKernelTerm ht hw).mul_left (1 / 4 - w)).congr fun n => ?_
  exact (suzukiLerchDiffTerm_eq hw n).symm

/-- **The factorization** `suzukiLerchDiff t w = (1/4 - w) · suzukiLerchKernel t w`.  It is this
identity that cancels the `1/(2iz)` prefactor of Suzuki eq. (1.6). -/
theorem suzukiLerchDiff_eq {t : ℝ} {w : ℂ} (hw : 0 < w.re) :
    suzukiLerchDiff t w = (1 / 4 - w) * suzukiLerchKernel t w := by
  rw [suzukiLerchDiff, suzukiLerchKernel, ← tsum_mul_left]
  exact tsum_congr fun n => suzukiLerchDiffTerm_eq hw n


/-! ## Value of the kernel at the base point -/

theorem suzukiLerchKernel_quarter (t : ℝ) :
    suzukiLerchKernel t (1 / 4) = ((4 * Real.exp (t / 2) * screwLerchTail t : ℝ) : ℂ) := by
  have hterm : ∀ n : ℕ, suzukiLerchKernelTerm t (1 / 4) n
      = ((4 * Real.exp (t / 2) *
          (Real.exp (-(lerchExp n * t)) / (lerchExp n) ^ 2) : ℝ) : ℂ) := by
    intro n
    have hq : ((n : ℂ) + 1 / 4) = (((n : ℝ) + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
    have hl : lerchExp n = 2 * n + 1 / 2 := rfl
    have hne : ((n : ℝ) + 1 / 4) ≠ 0 := by positivity
    rw [suzukiLerchKernelTerm, hq]
    rw [show (Real.exp (-(2 * (n : ℝ) * t)) : ℂ) = ((Real.exp (-(2 * (n : ℝ) * t)) : ℝ) : ℂ) from rfl]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_div]
    congr 1
    rw [hl]
    have hexp : Real.exp (-((2 * (n : ℝ) + 1 / 2) * t))
        = Real.exp (-(2 * (n : ℝ) * t)) * Real.exp (-(t / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp]
    have h2 : ((2 : ℝ) * n + 1 / 2) ^ 2 = 4 * ((n : ℝ) + 1 / 4) ^ 2 := by ring
    rw [h2]
    have hE : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    field_simp
    nlinarith [hE, Real.exp_pos (t/2), Real.exp_pos (-(2 * (n:ℝ) * t))]
  rw [suzukiLerchKernel]
  rw [show ((4 * Real.exp (t / 2) * screwLerchTail t : ℝ) : ℂ)
      = ((∑' k : ℕ, 4 * Real.exp (t / 2) *
          (Real.exp (-(lerchExp k * t)) / (lerchExp k) ^ 2) : ℝ) : ℂ) by
    rw [tsum_mul_left]; rfl]
  rw [Complex.ofReal_tsum]
  exact tsum_congr hterm

/-! ## The digamma bridge -/

theorem digamma_sub_quarter_eq {w : ℂ} (hw : 0 < w.re) :
    Complex.digamma w - Complex.digamma (1 / 4) = -suzukiLerchDiff 0 w := by
  have hq : (0 : ℝ) < ((1 : ℂ) / 4).re := by norm_num
  rw [digamma_sub_eq_tsum hq hw, suzukiLerchDiff, ← tsum_neg]
  refine tsum_congr fun n => ?_
  have h1 : ((n : ℂ) + w) ≠ 0 := nat_add_ne_zero_of_re_pos hw n
  have h2 : ((n : ℂ) + 1 / 4) ≠ 0 := nat_add_quarter_ne_zero n
  rw [suzukiLerchDiffTerm]
  simp only [mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul]
  rw [inv_eq_one_div, inv_eq_one_div]
  have e1 : (1 : ℂ) / 4 + (n : ℂ) = (n : ℂ) + 1 / 4 := by ring
  have e2 : w + (n : ℂ) = (n : ℂ) + w := by ring
  rw [e1, e2]
  ring


/-! ## Continuity of the kernel at the base point -/

/-- The second-order kernel `∑_n e^{-2nt}/((n+w)(n+1/4)^(2 : ℕ))`. -/
def suzukiLerchKernel2Term (t : ℝ) (w : ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-(2 * n * t)) : ℂ) / (((n : ℂ) + w) * ((n : ℂ) + 1 / 4) ^ 2)

/-- The second-order Lerch kernel `∑_n e^{-2nt}/((n+w)(n+1/4)^(2 : ℕ))`. -/
def suzukiLerchKernel2 (t : ℝ) (w : ℂ) : ℂ := ∑' n : ℕ, suzukiLerchKernel2Term t w n

/-- Uniform majorant for the second-order kernel terms. -/
theorem norm_suzukiLerchKernel2Term_le {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1)
    {w : ℂ} (hw : c ≤ w.re) (n : ℕ) :
    ‖suzukiLerchKernel2Term t w n‖ ≤ (16 / c) * (1 / ((n : ℝ) + 1) ^ 2) := by
  have hwre : 0 < w.re := lt_of_lt_of_le hc hw
  have hnorm1 : (n : ℝ) + c ≤ ‖(n : ℂ) + w‖ :=
    le_trans (by linarith [le_norm_nat_add hwre n]) (le_norm_nat_add hwre n)
  have hc1' : c * ((n : ℝ) + 1) ≤ (n : ℝ) + c := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hq1 : (1 / 4 : ℝ) * ((n : ℝ) + 1) ≤ (n : ℝ) + 1 / 4 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hden : (c / 16) * ((n : ℝ) + 1) ^ 2 ≤ ‖(n : ℂ) + w‖ * ‖((n : ℂ) + 1 / 4) ^ 2‖ := by
    rw [norm_pow, norm_nat_add_quarter]
    calc (c / 16) * ((n : ℝ) + 1) ^ 2
        = (c * ((n : ℝ) + 1)) * (((1 / 4 : ℝ) * ((n : ℝ) + 1)) * ((1 / 4 : ℝ) * ((n : ℝ) + 1)))
            / ((n : ℝ) + 1) := by
          field_simp; ring
      _ ≤ (c * ((n : ℝ) + 1)) * (((1 / 4 : ℝ) * ((n : ℝ) + 1)) * ((1 / 4 : ℝ) * ((n : ℝ) + 1))) := by
          apply div_le_self (by positivity)
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
      _ ≤ ((n : ℝ) + c) * (((n : ℝ) + 1 / 4) * ((n : ℝ) + 1 / 4)) := by
          apply mul_le_mul hc1' (mul_le_mul hq1 hq1 (by positivity) (by positivity))
            (by positivity) (by positivity)
      _ ≤ ‖(n : ℂ) + w‖ * (((n : ℝ) + 1 / 4) * ((n : ℝ) + 1 / 4)) :=
          mul_le_mul_of_nonneg_right hnorm1 (by positivity)
      _ = ‖(n : ℂ) + w‖ * ((n : ℝ) + 1 / 4) ^ 2 := by ring
  have hdpos : 0 < (c / 16) * ((n : ℝ) + 1) ^ 2 := by positivity
  rw [suzukiLerchKernel2Term, norm_div, norm_mul]
  rw [div_le_iff₀ (lt_of_lt_of_le hdpos hden)]
  calc ‖(Real.exp (-(2 * n * t)) : ℂ)‖ ≤ 1 := norm_exp_block_le ht n
    _ = (16 / c) * (1 / ((n : ℝ) + 1) ^ 2) * ((c / 16) * ((n : ℝ) + 1) ^ 2) := by field_simp
    _ ≤ (16 / c) * (1 / ((n : ℝ) + 1) ^ 2) * (‖(n : ℂ) + w‖ * ‖((n : ℂ) + 1 / 4) ^ 2‖) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- The second-order Lerch kernel converges absolutely. -/
theorem summable_suzukiLerchKernel2Term {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1)
    {w : ℂ} (hw : c ≤ w.re) :
    Summable (suzukiLerchKernel2Term t w) :=
  Summable.of_norm_bounded (summable_one_div_nat_add_one_sq.mul_left (16 / c))
    (fun n => norm_suzukiLerchKernel2Term_le ht hc hc1 hw n)

/-- A bound for the second-order kernel that is uniform on `c ≤ Re w`. -/
theorem norm_suzukiLerchKernel2_le {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1)
    {w : ℂ} (hw : c ≤ w.re) :
    ‖suzukiLerchKernel2 t w‖ ≤ (16 / c) * ∑' n : ℕ, (1 / ((n : ℝ) + 1) ^ 2) := by
  rw [suzukiLerchKernel2]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact (summable_suzukiLerchKernel2Term ht hc hc1 hw).norm
  · rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun n => norm_suzukiLerchKernel2Term_le ht hc hc1 hw n)
      (summable_suzukiLerchKernel2Term ht hc hc1 hw).norm
      (summable_one_div_nat_add_one_sq.mul_left (16 / c))

/-- Termwise first difference of the kernel against its base-point value. -/
theorem suzukiLerchKernelTerm_sub {t : ℝ} {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    suzukiLerchKernelTerm t w n - suzukiLerchKernelTerm t (1 / 4) n
      = (1 / 4 - w) * suzukiLerchKernel2Term t w n := by
  have h1 : ((n : ℂ) + w) ≠ 0 := nat_add_ne_zero_of_re_pos hw n
  have h2 : ((n : ℂ) + 1 / 4) ≠ 0 := nat_add_quarter_ne_zero n
  have hab : ((n : ℂ) + 1 / 4) - ((n : ℂ) + w) = 1 / 4 - w := by ring
  simp only [suzukiLerchKernelTerm, suzukiLerchKernel2Term]
  rw [← hab]
  set E : ℂ := (Real.exp (-(2 * (n : ℝ) * t)) : ℂ) with hE
  set a : ℂ := (n : ℂ) + w with ha
  set b : ℂ := (n : ℂ) + 1 / 4 with hb
  field_simp

/-- The Lerch kernel is Lipschitz at the base point, uniformly on `c ≤ Re w`. -/
theorem norm_suzukiLerchKernel_sub_quarter_le {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1)
    {w : ℂ} (hw : c ≤ w.re) :
    ‖suzukiLerchKernel t w - suzukiLerchKernel t (1 / 4)‖
      ≤ ((16 / c) * ∑' n : ℕ, (1 / ((n : ℝ) + 1) ^ 2)) * ‖w - 1 / 4‖ := by
  have hwre : 0 < w.re := lt_of_lt_of_le hc hw
  have hq : (0 : ℝ) < ((1 : ℂ) / 4).re := by norm_num
  have hsub : suzukiLerchKernel t w - suzukiLerchKernel t (1 / 4)
      = (1 / 4 - w) * suzukiLerchKernel2 t w := by
    rw [suzukiLerchKernel, suzukiLerchKernel, suzukiLerchKernel2, ← tsum_mul_left,
      ← Summable.tsum_sub (summable_suzukiLerchKernelTerm ht hwre)
        (summable_suzukiLerchKernelTerm ht hq)]
    exact tsum_congr fun n => suzukiLerchKernelTerm_sub hwre n
  rw [hsub, norm_mul]
  have hnorm : ‖(1 : ℂ) / 4 - w‖ = ‖w - 1 / 4‖ := by rw [← norm_neg]; ring_nf
  rw [hnorm, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_suzukiLerchKernel2_le ht hc hc1 hw) (norm_nonneg _)

/-- **Continuity of the Lerch kernel at the base point `1/4`.** -/
theorem continuousAt_suzukiLerchKernel_quarter {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (suzukiLerchKernel t) (1 / 4) := by
  set M : ℝ := (16 / (1 / 8 : ℝ)) * ∑' n : ℕ, (1 / ((n : ℝ) + 1) ^ 2) with hM
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hball : ∀ᶠ w : ℂ in 𝓝 (1 / 4 : ℂ),
      ‖suzukiLerchKernel t w - suzukiLerchKernel t (1 / 4)‖ ≤ M * ‖w - 1 / 4‖ := by
    have hopen : ∀ᶠ w : ℂ in 𝓝 (1 / 4 : ℂ), ‖w - 1 / 4‖ < 1 / 8 := by
      have := Metric.ball_mem_nhds (1 / 4 : ℂ) (by norm_num : (0:ℝ) < 1 / 8)
      filter_upwards [this] with w hw
      simpa [Complex.dist_eq] using hw
    filter_upwards [hopen] with w hw
    have hre : (1 / 8 : ℝ) ≤ w.re := by
      have h1 : |w.re - ((1 : ℂ) / 4).re| ≤ ‖w - 1 / 4‖ := by
        simpa using Complex.abs_re_le_norm (w - 1 / 4)
      have h2 : ((1 : ℂ) / 4).re = 1 / 4 := by norm_num
      rw [h2] at h1
      have := abs_le.mp (h1.trans hw.le)
      linarith [this.1]
    exact norm_suzukiLerchKernel_sub_quarter_le ht (by norm_num) (by norm_num) hre
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hball ?_
  have : Tendsto (fun w : ℂ => ‖w - 1 / 4‖) (𝓝 (1 / 4 : ℂ)) (𝓝 0) := by
    have hc : Continuous fun w : ℂ => ‖w - 1 / 4‖ := (continuous_id.sub continuous_const).norm
    simpa using hc.tendsto (1 / 4 : ℂ)
  simpa using this.const_mul M

end
end RHTower
