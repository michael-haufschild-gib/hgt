/-
Kernel-escalated quiet-crossing rigidity via an entire Gaussian weight.

The landed theorem `quiet_crossing_rigidity` pushes the Mellin contour of `F·E`
(`E = N/(s(s+1))` the entire Perron regularization) from `Re s = c` to `Re s = −M` and asks
the horizontal edges to vanish along a *quiet* sequence of heights `T_k` on which `‖F‖ ≤ q_k`
with `q_k = o(T_k²)`.  The kernel decay `‖E‖ = O(T_k^{-2})` is what makes `o(T_k²)` the exact
tolerance.

Inserting the **entire Gaussian weight** `W_λ(s) = exp(s²/λ)` (`λ > 0`) enlarges that tolerance.
On a horizontal line `Im s = ±T`, `‖W_λ(σ + iT)‖ = exp((σ² − T²)/λ)` contributes a factor
`exp(−T²/λ)` — super-polynomial decay — so the horizontal edges vanish whenever
`q_k·exp(−T_k²/λ) → 0`, a budget under which `q_k` may grow like `exp(T_k^{2}·o(1))`, vastly
larger than `o(T_k²)`.  Because `Re(s²) = σ² − t²`, the same weight decays like a Gaussian on
every vertical line (integrable against the `O(t^{-2})` kernel) while on `Re s = −M` it costs a
finite `exp(M²/λ)`.

The weight is removed by sending `λ → ∞`: `W_λ(s) → 1` pointwise, dominated on `Re s = c` by
`‖F·E‖·exp(c²)` (integrable), so the weighted contour integral converges to the weight-free one,
whose value is `π·aₙ`.  For this the quiet budget must hold at every escalation level `λ`, so the
hypothesis carries a single sequence `T_k, q_k` with `q_k·exp(−T_k²/λ) → 0` for **all** `λ > 0`
(equivalently `log q_k = o(T_k²)`) — a genuine weakening of `q_k = o(T_k²)`.

* `gaussWeight` — the entire weight `s ↦ exp(s²/λ)`; `gaussWeight_norm` gives
  `‖W_λ(s)‖ = exp((σ² − t²)/λ)`.
* `gaussian_weighted_contour_bound` — for a fixed `λ` and depth `M ≥ 2`, the weighted vertical
  integral on `Re s = c` is bounded by `4π·B·(n−½)^{1−M}·exp(M²/λ)`, obtained by shifting the
  contour to `Re s = −M` (horizontal edges vanish via `q_k·exp(−T_k²/λ) → 0`).
* `quiet_crossing_rigidity_gaussian` — a reflection carrier quiet under the escalated budget
  (`q_k·exp(−T_k²/λ) → 0` for every `λ > 0`) has `aₙ = 0` for all `n ≥ 2`.
-/
import Mathlib
import GaloisForLFunctions.RHTower.QuietCrossingRigidity

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set

noncomputable section

namespace RHTower

/-- The entire Gaussian weight `W_λ(s) = exp(s²/λ)` for a real escalation parameter `λ`.
On a vertical line `Re s = σ` it decays like `exp(−t²/λ)`; on a horizontal line `Im s = ±T` it
carries the super-polynomial factor `exp(−T²/λ)`. -/
def gaussWeight (lam : ℝ) (s : ℂ) : ℂ := Complex.exp (s ^ 2 / (lam : ℂ))

/-- The Gaussian weight is entire (a composition of `exp` with the entire map `s ↦ s²/λ`). -/
theorem gaussWeight_differentiable (lam : ℝ) : Differentiable ℂ (gaussWeight lam) := by
  unfold gaussWeight; fun_prop

/-- **Modulus of the weight.**  `‖exp(s²/λ)‖ = exp((Re s)² − (Im s)²)/λ)`, since
`Re(s²) = (Re s)² − (Im s)²` and `‖exp z‖ = exp (Re z)`. -/
theorem gaussWeight_norm (lam : ℝ) (s : ℂ) :
    ‖gaussWeight lam s‖ = Real.exp ((s.re ^ 2 - s.im ^ 2) / lam) := by
  have hre : (s ^ 2).re = s.re ^ 2 - s.im ^ 2 := by rw [sq, Complex.mul_re]; ring
  rw [gaussWeight, norm_exp, Complex.div_ofReal_re, hre]

/-- On any line the weight modulus is at most the value at `Im s = 0`:
`‖W_λ(s)‖ ≤ exp((Re s)²/λ)`, dropping the nonpositive `−(Im s)²/λ`. -/
theorem gaussWeight_norm_le_sq {lam : ℝ} (hlam : 0 < lam) (s : ℂ) :
    ‖gaussWeight lam s‖ ≤ Real.exp (s.re ^ 2 / lam) := by
  rw [gaussWeight_norm]
  apply Real.exp_le_exp.mpr
  gcongr
  nlinarith [sq_nonneg s.im]

/-! ### Local copies of the Perron-kernel estimates

The corresponding lemmas of `QuietCrossingRigidity` are file-private, so the pieces of kernel
bookkeeping are re-derived here. -/

/-- `t ↦ (c²+t²)⁻¹` is integrable for `c > 0` (a scaled Cauchy profile). -/
private theorem gwInvQuadIntegrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) := by
  have hc0 : c⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hc)
  have h1 : Integrable (fun t : ℝ => (1 + (c⁻¹ * t) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq).comp_mul_left' hc0
  have heq : (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) = fun t => (c ^ 2)⁻¹ * (1 + (c⁻¹ * t) ^ 2)⁻¹ := by
    funext t; rw [← mul_inv]; congr 1; field_simp
  rw [heq]; exact h1.const_mul _

/-- The denominator `(c+it)(c+it+1)` is nonzero for `c > 0`. -/
private theorem gwKernelDenNe {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (↑c + ↑t * I) * (↑c + ↑t * I + 1) ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.re h; simp at this; linarith

/-- The Perron kernel is continuous on the line `Re s = c > 0`. -/
private theorem gwKernelContinuous {c : ℝ} (hc : 0 < c) :
    Continuous (fun t : ℝ => ((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹) :=
  Continuous.inv₀ (by fun_prop) (gwKernelDenNe hc)

/-- `‖1/((c+it)(c+it+1))‖ ≤ (c²+t²)⁻¹` on the line `Re s = c > 0`. -/
private theorem gwKernelNormLe {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹‖ ≤ (c ^ 2 + t ^ 2)⁻¹ := by
  set A : ℂ := (↑c + ↑t * I) with hA
  set B : ℂ := (↑c + ↑t * I + 1) with hB
  have hAnorm : ‖A‖ = Real.sqrt (c ^ 2 + t ^ 2) := by rw [hA, Complex.norm_add_mul_I]
  have hApos : 0 < ‖A‖ := by rw [hAnorm]; apply Real.sqrt_pos.mpr; positivity
  have hBge : ‖A‖ ≤ ‖B‖ := by
    have hBnorm : ‖B‖ = Real.sqrt ((c + 1) ^ 2 + t ^ 2) := by
      rw [hB]
      have h : (↑c + ↑t * I + 1 : ℂ) = ↑(c + 1) + ↑t * I := by push_cast; ring
      rw [h, Complex.norm_add_mul_I]
    rw [hAnorm, hBnorm]; apply Real.sqrt_le_sqrt; nlinarith
  have hBpos : 0 < ‖B‖ := lt_of_lt_of_le hApos hBge
  rw [norm_inv, norm_mul, inv_le_inv₀ (mul_pos hApos hBpos) (by positivity)]
  calc c ^ 2 + t ^ 2 = ‖A‖ * ‖A‖ := by rw [hAnorm, Real.mul_self_sqrt (by positivity)]
    _ ≤ ‖A‖ * ‖B‖ := mul_le_mul_of_nonneg_left hBge (le_of_lt hApos)

/-- Kernel decay on a horizontal segment: at `x + t·I` with `|t| ≥ T > 0`,
`‖1/(s(s+1))‖ ≤ T^{-2}`. -/
private theorem gwKernelLineBound {t T : ℝ} (hT : 0 < T) (ht : T ≤ |t|) (x : ℝ) :
    ‖((↑x + ↑t * I) * (↑x + ↑t * I + 1))⁻¹‖ ≤ (T ^ 2)⁻¹ := by
  set s : ℂ := (↑x + ↑t * I : ℂ) with hs
  have him : s.im = t := by rw [hs]; simp
  have him1 : (s + 1).im = t := by rw [Complex.add_im, him, Complex.one_im, add_zero]
  have hA : T ≤ ‖s‖ := le_trans ht (by rw [← him]; exact Complex.abs_im_le_norm s)
  have hB : T ≤ ‖s + 1‖ := le_trans ht (by rw [← him1]; exact Complex.abs_im_le_norm (s + 1))
  have hge : T ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, sq]; exact mul_le_mul hA hB (le_of_lt hT) (le_trans hT.le hA)
  rw [norm_inv]; exact inv_anti₀ (by positivity) hge

/-- Kernel decay on the vertical line `Re s = −M` (`M > 1`): `‖1/(s(s+1))‖ ≤ ((M−1)²+y²)⁻¹`. -/
private theorem gwKernelLeftBound {M y : ℝ} (hM : 1 < M) :
    ‖((↑(-M) + ↑y * I) * (↑(-M) + ↑y * I + 1))⁻¹‖ ≤ ((M - 1) ^ 2 + y ^ 2)⁻¹ := by
  have hAnorm : ‖(↑(-M) + ↑y * I : ℂ)‖ = Real.sqrt ((-M) ^ 2 + y ^ 2) := Complex.norm_add_mul_I _ _
  have hBeq : (↑(-M) + ↑y * I + 1 : ℂ) = ↑(1 - M) + ↑y * I := by push_cast; ring
  have hBnorm : ‖(↑(-M) + ↑y * I + 1 : ℂ)‖ = Real.sqrt ((1 - M) ^ 2 + y ^ 2) := by
    rw [hBeq, Complex.norm_add_mul_I]
  have hden : (0 : ℝ) < (M - 1) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y, sq_nonneg (M - 1)]
  have hAge : Real.sqrt ((M - 1) ^ 2 + y ^ 2) ≤ ‖(↑(-M) + ↑y * I : ℂ)‖ := by
    rw [hAnorm]; apply Real.sqrt_le_sqrt; nlinarith
  have hBge : Real.sqrt ((M - 1) ^ 2 + y ^ 2) ≤ ‖(↑(-M) + ↑y * I + 1 : ℂ)‖ := by
    rw [hBnorm]; apply Real.sqrt_le_sqrt; nlinarith
  have hge : (M - 1) ^ 2 + y ^ 2 ≤ ‖(↑(-M) + ↑y * I) * (↑(-M) + ↑y * I + 1)‖ := by
    rw [norm_mul]
    calc (M - 1) ^ 2 + y ^ 2
        = Real.sqrt ((M - 1) ^ 2 + y ^ 2) * Real.sqrt ((M - 1) ^ 2 + y ^ 2) := by
          rw [Real.mul_self_sqrt hden.le]
      _ ≤ ‖(↑(-M) + ↑y * I : ℂ)‖ * ‖(↑(-M) + ↑y * I + 1 : ℂ)‖ :=
          mul_le_mul hAge hBge (Real.sqrt_nonneg _) (le_trans (Real.sqrt_nonneg _) hAge)
  rw [norm_inv]; exact inv_anti₀ hden hge

/-- Numerator bound on the line `Re s ≤ c` (needs `n ≥ 2` so all three bases exceed `1`):
`‖N(s)‖ ≤ 4·(n+½)^{c+1}`. -/
private theorem gwKink_c {n : ℕ} (hn : 2 ≤ n) {c : ℝ} (hc0 : 0 < c) (p : ℂ) (hpc : p.re ≤ c) :
    ‖perronKink n p‖ ≤ 4 * ((n : ℝ) + 1 / 2) ^ (c + 1) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxmpos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hxm1 : (1 : ℝ) ≤ (n : ℝ) - 1 / 2 := by linarith
  have hbase1p : (1 : ℝ) ≤ (n : ℝ) + 1 / 2 := by linarith
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hb := perronKink_norm_le hn1 p
  have hc1 : (0 : ℝ) ≤ c + 1 := by linarith
  have hpc1 : p.re + 1 ≤ c + 1 := by linarith
  have t1 : ((n : ℝ) + 1 / 2) ^ (p.re + 1) ≤ ((n : ℝ) + 1 / 2) ^ (c + 1) :=
    Real.rpow_le_rpow_of_exponent_le hbase1p hpc1
  have t2 : ((n : ℝ) - 1 / 2) ^ (p.re + 1) ≤ ((n : ℝ) + 1 / 2) ^ (c + 1) :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hxm1 hpc1)
      (Real.rpow_le_rpow hxmpos.le (by linarith) hc1)
  have t3 : ((n : ℝ)) ^ (p.re + 1) ≤ ((n : ℝ) + 1 / 2) ^ (c + 1) :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hnR1 hpc1)
      (Real.rpow_le_rpow (by linarith) (by linarith) hc1)
  linarith [hb, t1, t2, t3]

/-- Numerator bound on the line `Re s = −M`: `‖N(−M+iy)‖ ≤ 4·(n−½)^{1−M}` (negative-exponent
regime, `n ≥ 1`). -/
private theorem gwKink_M {n : ℕ} (hn : 1 ≤ n) (M : ℝ) (p : ℂ) (hM : 1 ≤ M) (hpre : p.re = -M) :
    ‖perronKink n p‖ ≤ 4 * ((n : ℝ) - 1 / 2) ^ (1 - M) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxmpos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hb := perronKink_norm_le hn p
  rw [hpre, show (-M + 1) = 1 - M by ring] at hb
  have hnp : (1 - M) ≤ 0 := by linarith
  have t1 : ((n : ℝ) + 1 / 2) ^ (1 - M) ≤ ((n : ℝ) - 1 / 2) ^ (1 - M) :=
    Real.rpow_le_rpow_of_nonpos hxmpos (by linarith) hnp
  have t3 : ((n : ℝ)) ^ (1 - M) ≤ ((n : ℝ) - 1 / 2) ^ (1 - M) :=
    Real.rpow_le_rpow_of_nonpos hxmpos (by linarith) hnp
  linarith [hb, t1, t3]

/-- **Gaussian-weighted contour bound.**  Let `F` be entire, bounded by `B` on the closed right
half-plane `Re s ≥ c` and (by reflection) on `Re s ≤ 1 − c`, and quiet along `T_k → ∞`:
`‖F(σ ± iT_k)‖ ≤ q_k` across `1 − c ≤ σ ≤ c`.  Fix an escalation level `λ > 0` under which
`q_k·exp(−T_k²/λ) → 0`.  Then for every depth `M ≥ 2` (with `c ≤ M`) the weighted vertical
integral of `F·E·W_λ` on `Re s = c` obeys

    ‖∫ F(c+it)·E(c+it)·W_λ(c+it) dt‖ ≤ 4π·B·(n−½)^{1−M}·exp(M²/λ).

Cauchy's theorem on the rectangle `[−M,c] × [−T_k,T_k]` shifts the contour to `Re s = −M`; the
horizontal edges are `≤ (B+q_k)·4(n+½)^{c+1}·T_k^{-2}·exp((M²−T_k²)/λ)` and vanish as `k → ∞`
because `q_k·exp(−T_k²/λ) → 0`, while the left edge is bounded by
`4π·B·(n−½)^{1−M}·exp(M²/λ)` using `‖W_λ(−M+iy)‖ ≤ exp(M²/λ)` and the kernel mass `≤ π`. -/
theorem gaussian_weighted_contour_bound
    {F : ℂ → ℂ} {c : ℝ} (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hF : Differentiable ℂ F) {n : ℕ} (hn : 2 ≤ n)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hFB : ∀ s : ℂ, c ≤ s.re → ‖F s‖ ≤ B)
    (hFleft : ∀ s : ℂ, s.re ≤ 1 - c → ‖F s‖ ≤ B)
    {T : ℕ → ℝ} {q : ℕ → ℝ} (hTtop : Tendsto T atTop atTop) (hTpos : ∀ k, 0 < T k)
    (hquietbd : ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
      ‖F (σ + (T k) * I)‖ ≤ q k ∧ ‖F (σ - (T k) * I)‖ ≤ q k)
    {lam : ℝ} (hlam : 0 < lam)
    (hedge : Tendsto (fun k => q k * Real.exp (-(T k) ^ 2 / lam)) atTop (nhds 0))
    {M : ℝ} (hM2 : 2 ≤ M) (hMc : c ≤ M) :
    ‖∫ t : ℝ, F (↑c + ↑t * I) * perronE n (↑c + ↑t * I) * gaussWeight lam (↑c + ↑t * I)‖
      ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - M) * Real.exp (M ^ 2 / lam) := by
  have hn1 : 1 ≤ n := by omega
  have hM1 : (1 : ℝ) < M := by linarith
  have hMle : -M ≤ 1 - c := by linarith
  have hMcle : -M ≤ c := by linarith
  have hxmpos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hqk0 : ∀ k, 0 ≤ q k := fun k =>
    le_trans (norm_nonneg _) (hquietbd k c (by linarith) le_rfl).1
  have hEdiff : Differentiable ℂ (perronE n) := perronE_differentiable hn1
  set Hf : ℂ → ℂ := fun s => F s * perronE n s * gaussWeight lam s with hHf
  have hHfp : ∀ p : ℂ, Hf p = F p * perronE n p * gaussWeight lam p := fun p => by simp only [hHf]
  have hHfdiff : Differentiable ℂ Hf := by
    rw [hHf]; exact (hF.mul hEdiff).mul (gaussWeight_differentiable lam)
  have hHfcont : Continuous Hf := hHfdiff.continuous
  -- The weighted integrand on `Re s = c` is integrable (Gaussian × `O(t^{-2})` kernel).
  have hRint : Integrable (fun t : ℝ => Hf (↑c + ↑t * I)) := by
    have hcont : Continuous (fun t : ℝ => Hf (↑c + ↑t * I)) := hHfcont.comp (by fun_prop)
    have hbd : ∀ t : ℝ, ‖Hf (↑c + ↑t * I)‖
        ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * B * Real.exp (c ^ 2 / lam)) * (c ^ 2 + t ^ 2)⁻¹ := by
      intro t
      have hre : (↑c + ↑t * I : ℂ).re = c := by simp
      rw [hHfp, norm_mul, norm_mul]
      have hF' : ‖F (↑c + ↑t * I)‖ ≤ B := hFB _ (le_of_eq hre.symm)
      have h0 : (↑c + ↑t * I : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
      have h1 : (↑c + ↑t * I : ℂ) ≠ -1 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
      have hE' : ‖perronE n (↑c + ↑t * I)‖ ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹ := by
        rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
        exact mul_le_mul (gwKink_c hn hc0 _ (le_of_eq hre)) (gwKernelNormLe hc0 t) (norm_nonneg _)
          (by positivity)
      have hW' : ‖gaussWeight lam (↑c + ↑t * I)‖ ≤ Real.exp (c ^ 2 / lam) := by
        have := gaussWeight_norm_le_sq hlam (↑c + ↑t * I); rwa [hre] at this
      calc ‖F (↑c + ↑t * I)‖ * ‖perronE n (↑c + ↑t * I)‖ * ‖gaussWeight lam (↑c + ↑t * I)‖
          ≤ B * ((4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹) * Real.exp (c ^ 2 / lam) :=
            mul_le_mul (mul_le_mul hF' hE' (norm_nonneg _) hB0) hW' (norm_nonneg _)
              (mul_nonneg hB0 (by positivity))
        _ = (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * B * Real.exp (c ^ 2 / lam)) * (c ^ 2 + t ^ 2)⁻¹ := by
            ring
    exact ((gwInvQuadIntegrable hc0).const_mul _).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hbd)
  -- Left-line domination and its integral bound.
  have hleftbd : ∀ y : ℝ, ‖Hf (↑(-M) + ↑y * I)‖
      ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - M) * B * Real.exp (M ^ 2 / lam)) * (((M - 1) ^ 2 + y ^ 2)⁻¹) := by
    intro y
    have hre : (↑(-M) + ↑y * I : ℂ).re = -M := by simp
    rw [hHfp, norm_mul, norm_mul]
    have hF' : ‖F (↑(-M) + ↑y * I)‖ ≤ B := hFleft _ (by rw [hre]; linarith)
    have h0 : (↑(-M) + ↑y * I : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
    have h1 : (↑(-M) + ↑y * I : ℂ) ≠ -1 := by
      intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
    have hE' : ‖perronE n (↑(-M) + ↑y * I)‖
        ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - M)) * (((M - 1) ^ 2 + y ^ 2)⁻¹) := by
      rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
      exact mul_le_mul (gwKink_M hn1 M _ hM1.le hre) (gwKernelLeftBound hM1) (norm_nonneg _)
        (by positivity)
    have hW' : ‖gaussWeight lam (↑(-M) + ↑y * I)‖ ≤ Real.exp (M ^ 2 / lam) := by
      have := gaussWeight_norm_le_sq hlam (↑(-M) + ↑y * I); rw [hre] at this; rwa [neg_sq] at this
    calc ‖F (↑(-M) + ↑y * I)‖ * ‖perronE n (↑(-M) + ↑y * I)‖ * ‖gaussWeight lam (↑(-M) + ↑y * I)‖
        ≤ B * ((4 * ((n : ℝ) - 1 / 2) ^ (1 - M)) * (((M - 1) ^ 2 + y ^ 2)⁻¹)) * Real.exp (M ^ 2 / lam) :=
          mul_le_mul (mul_le_mul hF' hE' (norm_nonneg _) hB0) hW' (norm_nonneg _)
            (mul_nonneg hB0 (by positivity))
      _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - M) * B * Real.exp (M ^ 2 / lam)) * (((M - 1) ^ 2 + y ^ 2)⁻¹) := by
          ring
  have hleftint : Integrable (fun y : ℝ => Hf (↑(-M) + ↑y * I)) := by
    have hcont : Continuous (fun y : ℝ => Hf (↑(-M) + ↑y * I)) := hHfcont.comp (by fun_prop)
    exact ((gwInvQuadIntegrable (show (0 : ℝ) < M - 1 from by linarith)).const_mul
      (4 * ((n : ℝ) - 1 / 2) ^ (1 - M) * B * Real.exp (M ^ 2 / lam))).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall hleftbd)
  have hqle : ∫ y : ℝ, ((M - 1) ^ 2 + y ^ 2)⁻¹ ≤ Real.pi := by
    rw [← integral_univ_inv_one_add_sq]
    refine integral_mono (gwInvQuadIntegrable (show (0 : ℝ) < M - 1 from by linarith))
      integrable_inv_one_add_sq (fun y => ?_)
    refine inv_anti₀ (by positivity) ?_
    nlinarith [sq_nonneg y]
  have hleftfull : ∫ y : ℝ, ‖Hf (↑(-M) + ↑y * I)‖
      ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - M) * Real.exp (M ^ 2 / lam) := by
    have hdomint : Integrable (fun y : ℝ =>
        (4 * ((n : ℝ) - 1 / 2) ^ (1 - M) * B * Real.exp (M ^ 2 / lam)) * (((M - 1) ^ 2 + y ^ 2)⁻¹)) :=
      (gwInvQuadIntegrable (show (0 : ℝ) < M - 1 from by linarith)).const_mul _
    have hCnn : (0 : ℝ) ≤ 4 * ((n : ℝ) - 1 / 2) ^ (1 - M) * B * Real.exp (M ^ 2 / lam) := by positivity
    calc ∫ y : ℝ, ‖Hf (↑(-M) + ↑y * I)‖
        ≤ ∫ y : ℝ, (4 * ((n : ℝ) - 1 / 2) ^ (1 - M) * B * Real.exp (M ^ 2 / lam)) *
            (((M - 1) ^ 2 + y ^ 2)⁻¹) :=
          integral_mono hleftint.norm hdomint hleftbd
      _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - M) * B * Real.exp (M ^ 2 / lam)) *
            ∫ y : ℝ, ((M - 1) ^ 2 + y ^ 2)⁻¹ := integral_const_mul _ _
      _ ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - M) * B * Real.exp (M ^ 2 / lam)) * Real.pi :=
          mul_le_mul_of_nonneg_left hqle hCnn
      _ = 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - M) * Real.exp (M ^ 2 / lam) := by ring
  have hleftk : ∀ k, ‖∫ y in (-(T k))..(T k), Hf (↑(-M) + ↑y * I)‖
      ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - M) * Real.exp (M ^ 2 / lam) := by
    intro k
    calc ‖∫ y in (-(T k))..(T k), Hf (↑(-M) + ↑y * I)‖
        ≤ ∫ y in (-(T k))..(T k), ‖Hf (↑(-M) + ↑y * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith [hTpos k])
      _ = ∫ y in Set.Ioc (-(T k)) (T k), ‖Hf (↑(-M) + ↑y * I)‖ :=
          intervalIntegral.integral_of_le (by linarith [hTpos k])
      _ ≤ ∫ y : ℝ, ‖Hf (↑(-M) + ↑y * I)‖ :=
          setIntegral_le_integral hleftint.norm (Eventually.of_forall (fun y => norm_nonneg _))
      _ ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - M) * Real.exp (M ^ 2 / lam) := hleftfull
  -- Horizontal-edge decay: the Gaussian kills `exp(−T_k²/λ)`.
  have hexp0 : Tendsto (fun k => Real.exp (-(T k) ^ 2 / lam)) atTop (nhds 0) := by
    have hTsq : Tendsto (fun k => (T k) ^ 2) atTop atTop := by
      simpa [pow_two] using hTtop.atTop_mul_atTop₀ hTtop
    have hdiv : Tendsto (fun k => (T k) ^ 2 / lam) atTop atTop := hTsq.atTop_div_const hlam
    have heq : (fun k => Real.exp (-(T k) ^ 2 / lam)) = fun k => (Real.exp ((T k) ^ 2 / lam))⁻¹ := by
      funext k; rw [neg_div, Real.exp_neg]
    rw [heq]; exact (Real.tendsto_exp_atTop.comp hdiv).inv_tendsto_atTop
  have hTinv : Tendsto (fun k => ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
    have hTsq : Tendsto (fun k => (T k) ^ 2) atTop atTop := by
      simpa [pow_two] using hTtop.atTop_mul_atTop₀ hTtop
    exact hTsq.inv_tendsto_atTop
  have hsum0 : Tendsto (fun k => (B + q k) * Real.exp (-(T k) ^ 2 / lam)) atTop (nhds 0) := by
    have h1 : Tendsto (fun k => B * Real.exp (-(T k) ^ 2 / lam)) atTop (nhds 0) := by
      simpa using hexp0.const_mul B
    simpa [add_mul] using h1.add hedge
  have hprod : Tendsto (fun k => ((B + q k) * Real.exp (-(T k) ^ 2 / lam)) * ((T k) ^ 2)⁻¹) atTop
      (nhds 0) := by simpa using hsum0.mul hTinv
  set d : ℕ → ℝ := fun k =>
    (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * Real.exp (M ^ 2 / lam) * (c + M)) *
      (((B + q k) * Real.exp (-(T k) ^ 2 / lam)) * ((T k) ^ 2)⁻¹) with hd
  have hd0 : Tendsto d atTop (nhds 0) := by
    simpa [hd] using hprod.const_mul (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * Real.exp (M ^ 2 / lam) * (c + M))
  -- Per-point edge bound: `‖H_λ(x+it)‖ ≤ (B+q_k)·(4(n+½)^{c+1}·T_k^{-2})·(exp(M²/λ)·exp(−T_k²/λ))`.
  have hedgePt : ∀ (k : ℕ) (t : ℝ), 0 < T k → |t| = T k →
      ∀ x : ℝ, -M ≤ x → x ≤ c → ‖F (↑x + ↑t * I)‖ ≤ B + q k →
      ‖Hf (↑x + ↑t * I)‖ ≤ (B + q k) *
        (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) *
        (Real.exp (M ^ 2 / lam) * Real.exp (-(T k) ^ 2 / lam)) := by
    intro k t hTk habs x hx1 hx2 hFbd
    have hre : (↑x + ↑t * I : ℂ).re = x := by simp
    have hsim : (↑x + ↑t * I : ℂ).im = t := by simp
    have h0 : (↑x + ↑t * I : ℂ) ≠ 0 := by
      intro hh; have := congrArg Complex.im hh; rw [hsim] at this; simp at this
      rw [this] at habs; simp at habs; linarith
    have h1 : (↑x + ↑t * I : ℂ) ≠ -1 := by
      intro hh; have := congrArg Complex.im hh; rw [hsim] at this; simp at this
      rw [this] at habs; simp at habs; linarith
    rw [hHfp, norm_mul, norm_mul]
    have hE' : ‖perronE n (↑x + ↑t * I)‖ ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * ((T k) ^ 2)⁻¹ := by
      rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
      exact mul_le_mul (gwKink_c hn hc0 _ ((le_of_eq hre).trans hx2))
        (gwKernelLineBound hTk (le_of_eq habs.symm) x) (norm_nonneg _) (by positivity)
    have hW' : ‖gaussWeight lam (↑x + ↑t * I)‖ ≤ Real.exp (M ^ 2 / lam) * Real.exp (-(T k) ^ 2 / lam) := by
      rw [gaussWeight_norm, hre, hsim, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ht2 : t ^ 2 = (T k) ^ 2 := by rw [← sq_abs, habs]
      have hx2M : x ^ 2 ≤ M ^ 2 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ M - x by linarith) (show (0 : ℝ) ≤ M + x by linarith)]
      rw [ht2, ← add_div]
      gcongr
      linarith
    calc ‖F (↑x + ↑t * I)‖ * ‖perronE n (↑x + ↑t * I)‖ * ‖gaussWeight lam (↑x + ↑t * I)‖
        ≤ (B + q k) * ((4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * ((T k) ^ 2)⁻¹) *
            (Real.exp (M ^ 2 / lam) * Real.exp (-(T k) ^ 2 / lam)) :=
          mul_le_mul (mul_le_mul hFbd hE' (norm_nonneg _) (by linarith [hB0, hqk0 k])) hW'
            (norm_nonneg _) (mul_nonneg (by linarith [hB0, hqk0 k]) (by positivity))
      _ = (B + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) *
            (Real.exp (M ^ 2 / lam) * Real.exp (-(T k) ^ 2 / lam)) := by ring
  have htop : ∀ k, ‖∫ x in (-M)..c, Hf (↑x + ↑(T k) * I)‖ ≤ d k := by
    intro k
    have hconst : ∀ x ∈ Set.uIoc (-M) c,
        ‖Hf (↑x + ↑(T k) * I)‖ ≤ (B + q k) *
          (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) *
          (Real.exp (M ^ 2 / lam) * Real.exp (-(T k) ^ 2 / lam)) := by
      intro x hx
      rw [Set.uIoc_of_le hMcle] at hx
      obtain ⟨hx1, hx2⟩ := hx
      refine hedgePt k (T k) (hTpos k) (abs_of_pos (hTpos k)) x (le_of_lt hx1) hx2 ?_
      rcases le_or_gt x (1 - c) with h | h
      · exact le_trans (hFleft _ (by simp; exact h)) (by linarith [hqk0 k])
      · exact le_trans (hquietbd k x (le_of_lt h) hx2).1 (by linarith [hB0])
    calc ‖∫ x in (-M)..c, Hf (↑x + ↑(T k) * I)‖
        ≤ ((B + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) *
            (Real.exp (M ^ 2 / lam) * Real.exp (-(T k) ^ 2 / lam))) * |c - -M| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hconst
      _ = d k := by simp only [hd]; rw [show c - -M = c + M by ring, abs_of_nonneg (by linarith)]; ring
  have hbot : ∀ k, ‖∫ x in (-M)..c, Hf (↑x + ↑(-(T k)) * I)‖ ≤ d k := by
    intro k
    have hconst : ∀ x ∈ Set.uIoc (-M) c,
        ‖Hf (↑x + ↑(-(T k)) * I)‖ ≤ (B + q k) *
          (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) *
          (Real.exp (M ^ 2 / lam) * Real.exp (-(T k) ^ 2 / lam)) := by
      intro x hx
      rw [Set.uIoc_of_le hMcle] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hpt : (↑x + ↑(-(T k)) * I : ℂ) = ↑x - ↑(T k) * I := by push_cast; ring
      refine hedgePt k (-(T k)) (hTpos k) (by rw [abs_neg, abs_of_pos (hTpos k)]) x (le_of_lt hx1) hx2 ?_
      rcases le_or_gt x (1 - c) with h | h
      · exact le_trans (hFleft _ (by simp; exact h)) (by linarith [hqk0 k])
      · rw [hpt]; exact le_trans (hquietbd k x (le_of_lt h) hx2).2 (by linarith [hB0])
    calc ‖∫ x in (-M)..c, Hf (↑x + ↑(-(T k)) * I)‖
        ≤ ((B + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) *
            (Real.exp (M ^ 2 / lam) * Real.exp (-(T k) ^ 2 / lam))) * |c - -M| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hconst
      _ = d k := by simp only [hd]; rw [show c - -M = c + M by ring, abs_of_nonneg (by linarith)]; ring
  -- Right vertical truncated integral converges to the full-line integral.
  have hrighttendsto : Tendsto (fun k => ∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)) atTop
      (nhds (∫ t : ℝ, Hf (↑c + ↑t * I))) :=
    intervalIntegral_tendsto_integral hRint (tendsto_neg_atBot_iff.mpr hTtop) hTtop
  have hnormtendsto : Tendsto (fun k => ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖) atTop
      (nhds ‖∫ t : ℝ, Hf (↑c + ↑t * I)‖) := hrighttendsto.norm
  -- Cauchy rectangle: right edge ≤ tops + bottom + left.
  have hrectbd : ∀ k, ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖
      ≤ (d k + d k) + 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - M) * Real.exp (M ^ 2 / lam) := by
    intro k
    set z : ℂ := ⟨-M, -(T k)⟩ with hz
    set w : ℂ := ⟨c, T k⟩ with hw
    have hrect := integral_boundary_rect_eq_zero_of_differentiableOn Hf z w hHfdiff.differentiableOn
    have hzre : z.re = -M := rfl
    have hzim : z.im = -(T k) := rfl
    have hwre : w.re = c := rfl
    have hwim : w.im = T k := rfl
    rw [hzre, hzim, hwre, hwim] at hrect
    simp only [smul_eq_mul] at hrect
    set Itop := ∫ x in (-M)..c, Hf (↑x + ↑(T k) * I) with hItop
    set Ibot := ∫ x in (-M)..c, Hf (↑x + ↑(-(T k)) * I) with hIbot
    set Ilft := ∫ y in (-(T k))..(T k), Hf (↑(-M) + ↑y * I) with hIlft
    have heqI : I * (∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)) = Itop - Ibot + I * Ilft := by
      linear_combination hrect
    have hInorm : ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖ = ‖Itop - Ibot + I * Ilft‖ := by
      rw [← heqI, norm_mul, Complex.norm_I, one_mul]
    rw [hInorm]
    have hb1 : ‖Itop - Ibot + I * Ilft‖ ≤ ‖Itop - Ibot‖ + ‖I * Ilft‖ := norm_add_le _ _
    have hb2 : ‖Itop - Ibot‖ ≤ ‖Itop‖ + ‖Ibot‖ := norm_sub_le _ _
    have hb3 : ‖I * Ilft‖ = ‖Ilft‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [hb3] at hb1
    have h3 : ‖Itop‖ ≤ d k := htop k
    have h4 : ‖Ibot‖ ≤ d k := hbot k
    have h5 : ‖Ilft‖ ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - M) * Real.exp (M ^ 2 / lam) := hleftk k
    linarith [hb1, hb2, h3, h4, h5]
  have hdb : Tendsto (fun k => (d k + d k) +
      4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - M) * Real.exp (M ^ 2 / lam)) atTop
      (nhds (4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - M) * Real.exp (M ^ 2 / lam))) := by
    simpa using (hd0.add hd0).add_const
      (4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - M) * Real.exp (M ^ 2 / lam))
  have hfinal := le_of_tendsto_of_tendsto' hnormtendsto hdb hrectbd
  simpa only [hHf] using hfinal

/-- **Kernel-escalated quiet-crossing rigidity.**  Let `F` be entire, agree with an absolutely
convergent Dirichlet series `L(s) = Σ aₘ m^{−s}` on `Re s ≥ c` (`½ ≤ c`), and satisfy the exact
reflection symmetry `F(s) = F(1−s)`.  Suppose a single sequence of heights `T_k → ∞` is quiet
across the closed strip `1 − c ≤ σ ≤ c`, `‖F(σ ± iT_k)‖ ≤ q_k`, with the **escalated budget**
`q_k·exp(−T_k²/λ) → 0` for *every* `λ > 0` (equivalently `log q_k = o(T_k²)`, allowing `q_k` to
grow like `exp(T_k^{2}·o(1))` — vastly beyond the `o(T_k²)` of the unweighted theorem).  Then
`aₙ = 0` for every `n ≥ 2`.

For each escalation level `λ = j`, the Gaussian weight `W_j(s) = exp(s²/j)` makes the horizontal
edges of the rectangle contour vanish (via `q_k·exp(−T_k²/j) → 0`), giving
`‖∫ F·E·W_j‖ ≤ 4π·B·(n−½)^{1−M}·exp(M²/j)` on `Re s = c`.  Sending `j → ∞`, the weight tends to
`1` and — dominated by `‖F·E‖·exp(c²)` — the weighted integral converges to `∫ F·E`, whence
`‖∫ F·E‖ ≤ 4π·B·(n−½)^{1−M}` for every depth `M`.  As `M → ∞` this forces `∫ F·E = 0`, and the
Mellin identity `½·aₙ = (1/2π)·∫ F·E` gives `aₙ = 0`. -/
theorem quiet_crossing_rigidity_gaussian {F : ℂ → ℂ} {a : ℕ → ℂ} {c : ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hF : Differentiable ℂ F) (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hsym : ∀ s : ℂ, F s = F (1 - s))
    (hquiet : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ),
      Filter.Tendsto T Filter.atTop Filter.atTop ∧ (∀ k, 0 < T k) ∧
      (∀ lam : ℝ, 0 < lam →
        Filter.Tendsto (fun k => q k * Real.exp (-(T k) ^ 2 / lam)) Filter.atTop (nhds 0)) ∧
      ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
        ‖F (σ + (T k) * Complex.I)‖ ≤ q k ∧ ‖F (σ - (T k) * Complex.I)‖ ≤ q k) :
    ∀ n : ℕ, 2 ≤ n → a n = 0 := by
  intro n hn2
  have hn1 : 1 ≤ n := by omega
  obtain ⟨T, q, hTtop, hTpos, hqbudget, hquietbd⟩ := hquiet
  obtain ⟨B, hB⟩ := lseries_bounded_on_halfplane hsum
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB ↑c (by rw [Complex.ofReal_re]))
  have hFB : ∀ s : ℂ, c ≤ s.re → ‖F s‖ ≤ B := fun s hs => by rw [hFeq s hs]; exact hB s hs
  have hFleft : ∀ s : ℂ, s.re ≤ 1 - c → ‖F s‖ ≤ B := by
    intro s hs; rw [hsym s]; exact hFB _ (by rw [Complex.sub_re, Complex.one_re]; linarith)
  have hEdiff : Differentiable ℂ (perronE n) := perronE_differentiable hn1
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hxmpos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hxmgt1 : (1 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  -- Weight-free integrability of `F·E` on `Re s = c` (dominating function for `λ → ∞`).
  have hRint0 : Integrable (fun t : ℝ => F (↑c + ↑t * I) * perronE n (↑c + ↑t * I)) := by
    have hcont : Continuous (fun t : ℝ => F (↑c + ↑t * I) * perronE n (↑c + ↑t * I)) :=
      (hF.continuous.comp (by fun_prop)).mul (hEdiff.continuous.comp (by fun_prop))
    have hbd : ∀ t : ℝ, ‖F (↑c + ↑t * I) * perronE n (↑c + ↑t * I)‖
        ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * B) * (c ^ 2 + t ^ 2)⁻¹ := by
      intro t
      have hre : (↑c + ↑t * I : ℂ).re = c := by simp
      rw [norm_mul]
      have hF' : ‖F (↑c + ↑t * I)‖ ≤ B := hFB _ (le_of_eq hre.symm)
      have h0 : (↑c + ↑t * I : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
      have h1 : (↑c + ↑t * I : ℂ) ≠ -1 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
      have hE' : ‖perronE n (↑c + ↑t * I)‖ ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹ := by
        rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
        exact mul_le_mul (gwKink_c hn2 hc0 _ (le_of_eq hre)) (gwKernelNormLe hc0 t) (norm_nonneg _)
          (by positivity)
      calc ‖F (↑c + ↑t * I)‖ * ‖perronE n (↑c + ↑t * I)‖
          ≤ B * ((4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹) :=
            mul_le_mul hF' hE' (norm_nonneg _) hB0
        _ = (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * B) * (c ^ 2 + t ^ 2)⁻¹ := by ring
    exact ((gwInvQuadIntegrable hc0).const_mul _).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hbd)
  set I0 : ℂ := ∫ t : ℝ, F (↑c + ↑t * I) * perronE n (↑c + ↑t * I) with hI0
  -- Uniform (over all `j`) domination of the weight on `Re s = c`.
  have hWle : ∀ (j : ℕ) (t : ℝ), ‖gaussWeight (j : ℝ) (↑c + ↑t * I)‖ ≤ Real.exp (c ^ 2) := by
    intro j t
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp only [Nat.cast_zero, gaussWeight, Complex.ofReal_zero, div_zero, Complex.exp_zero, norm_one]
      exact Real.one_le_exp (sq_nonneg c)
    · have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
      refine le_trans (gaussWeight_norm_le_sq hjpos _) ?_
      apply Real.exp_le_exp.mpr
      have hre : (↑c + ↑t * I : ℂ).re = c := by simp
      rw [hre, div_le_iff₀ hjpos]
      nlinarith [sq_nonneg c, (show (1 : ℝ) ≤ (j : ℝ) by exact_mod_cast hj)]
  -- The key `M`-indexed bound on the weight-free integral, via `λ → ∞`.
  have keyM : ∀ M : ℕ, 2 ≤ M → (c : ℝ) ≤ (M : ℝ) →
      ‖I0‖ ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
    intro M hM2 hMc
    have hM2R : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    -- Weighted bound at each escalation level `j ≥ 1`.
    have hbound_j : ∀ j : ℕ, 1 ≤ j →
        ‖∫ t : ℝ, F (↑c + ↑t * I) * perronE n (↑c + ↑t * I) * gaussWeight (j : ℝ) (↑c + ↑t * I)‖
          ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * Real.exp ((M : ℝ) ^ 2 / (j : ℝ)) := by
      intro j hj
      have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
      exact gaussian_weighted_contour_bound hc hc0 hF hn2 B hB0 hFB hFleft hTtop hTpos hquietbd
        hjpos (hqbudget (j : ℝ) hjpos) hM2R hMc
    -- Dominated convergence `∫ F·E·W_j → I0` as `j → ∞`.
    have hdom : Tendsto (fun j : ℕ =>
        ∫ t : ℝ, F (↑c + ↑t * I) * perronE n (↑c + ↑t * I) * gaussWeight (j : ℝ) (↑c + ↑t * I))
        atTop (nhds I0) := by
      have hmeas : ∀ j : ℕ, AEStronglyMeasurable
          (fun t : ℝ => F (↑c + ↑t * I) * perronE n (↑c + ↑t * I) * gaussWeight (j : ℝ) (↑c + ↑t * I))
          volume := by
        intro j
        exact (((hF.continuous.comp (by fun_prop)).mul (hEdiff.continuous.comp (by fun_prop))).mul
          ((gaussWeight_differentiable (j : ℝ)).continuous.comp (by fun_prop))).aestronglyMeasurable
      have hboundInt : Integrable
          (fun t : ℝ => ‖F (↑c + ↑t * I) * perronE n (↑c + ↑t * I)‖ * Real.exp (c ^ 2)) :=
        hRint0.norm.mul_const _
      have hdombd : ∀ j : ℕ, ∀ᵐ t : ℝ,
          ‖F (↑c + ↑t * I) * perronE n (↑c + ↑t * I) * gaussWeight (j : ℝ) (↑c + ↑t * I)‖
            ≤ ‖F (↑c + ↑t * I) * perronE n (↑c + ↑t * I)‖ * Real.exp (c ^ 2) := by
        intro j
        refine Eventually.of_forall (fun t => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hWle j t) (norm_nonneg _)
      have hptlim : ∀ᵐ t : ℝ, Tendsto (fun j : ℕ =>
          F (↑c + ↑t * I) * perronE n (↑c + ↑t * I) * gaussWeight (j : ℝ) (↑c + ↑t * I))
          atTop (nhds (F (↑c + ↑t * I) * perronE n (↑c + ↑t * I))) := by
        refine Eventually.of_forall (fun t => ?_)
        have hgw : Tendsto (fun j : ℕ => gaussWeight (j : ℝ) (↑c + ↑t * I)) atTop (nhds 1) := by
          have h0 : Tendsto (fun j : ℕ => (↑c + ↑t * I) ^ 2 / (((j : ℝ)) : ℂ)) atTop (nhds 0) := by
            rw [tendsto_zero_iff_norm_tendsto_zero]
            simp only [norm_div, Complex.norm_real, Real.norm_natCast]
            exact tendsto_const_div_atTop_nhds_zero_nat _
          have := (Complex.continuous_exp.tendsto 0).comp h0
          simpa [gaussWeight, Complex.exp_zero] using this
        have := hgw.const_mul (F (↑c + ↑t * I) * perronE n (↑c + ↑t * I))
        simpa using this
      have := tendsto_integral_of_dominated_convergence
        (fun t : ℝ => ‖F (↑c + ↑t * I) * perronE n (↑c + ↑t * I)‖ * Real.exp (c ^ 2))
        hmeas hboundInt hdombd hptlim
      rw [hI0]; exact this
    have hnorm : Tendsto (fun j : ℕ =>
        ‖∫ t : ℝ, F (↑c + ↑t * I) * perronE n (↑c + ↑t * I) * gaussWeight (j : ℝ) (↑c + ↑t * I)‖)
        atTop (nhds ‖I0‖) := hdom.norm
    have hbndlim : Tendsto (fun j : ℕ =>
        4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * Real.exp ((M : ℝ) ^ 2 / (j : ℝ)))
        atTop (nhds (4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))) := by
      have hexp1 : Tendsto (fun j : ℕ => Real.exp ((M : ℝ) ^ 2 / (j : ℝ))) atTop (nhds 1) := by
        have : Tendsto (fun j : ℕ => (M : ℝ) ^ 2 / (j : ℝ)) atTop (nhds 0) :=
          tendsto_const_div_atTop_nhds_zero_nat _
        simpa using (Real.continuous_exp.tendsto 0).comp this
      simpa using hexp1.const_mul (4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
    refine le_of_tendsto_of_tendsto hnorm hbndlim ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact hbound_j j hj
  -- `M → ∞` forces `I0 = 0`.
  have hMtendsto : Tendsto (fun M : ℕ => 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
      atTop (nhds 0) := by
    have hbase : Tendsto (fun M : ℕ => ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) atTop (nhds 0) := by
      have h1 : (fun M : ℕ => ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
          = fun M : ℕ => ((n : ℝ) - 1 / 2) * (((n : ℝ) - 1 / 2)⁻¹) ^ M := by
        funext M
        rw [Real.rpow_sub hxmpos, Real.rpow_one, Real.rpow_natCast, div_eq_mul_inv, inv_pow]
      rw [h1]
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ ((n : ℝ) - 1 / 2)⁻¹)
        (by rw [inv_lt_one_iff₀]; right; exact hxmgt1)
      simpa using this.const_mul ((n : ℝ) - 1 / 2)
    simpa using hbase.const_mul (4 * Real.pi * B)
  have hI0norm : ‖I0‖ ≤ 0 := by
    refine ge_of_tendsto hMtendsto ?_
    filter_upwards [eventually_ge_atTop (max 2 ⌈c⌉₊)] with M hM
    have hM2 : 2 ≤ M := le_trans (le_max_left _ _) hM
    have hMc : (c : ℝ) ≤ (M : ℝ) :=
      le_trans (Nat.le_ceil c) (by exact_mod_cast le_trans (le_max_right _ _) hM)
    exact keyM M hM2 hMc
  have hI00 : I0 = 0 := norm_eq_zero.mp (le_antisymm hI0norm (norm_nonneg _))
  -- Conclude via the Mellin identity `½·aₙ = (1/2π)·I0`.
  have hAn : a n * (1 / 2) = (1 / (2 * Real.pi) : ℝ) • I0 := by
    rw [hI0]; exact perronSecondDiff_integral hc0 hsum hF hFeq hn1
  rw [hI00, smul_zero] at hAn
  exact (mul_eq_zero.mp hAn).resolve_right (by norm_num)

end RHTower
