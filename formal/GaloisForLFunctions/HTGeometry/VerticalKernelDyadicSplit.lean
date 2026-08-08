import GaloisForLFunctions.HTGeometry.SmoothWeightMellin

/-!
# The vertical integral against a first-order kernel

A vertical integral `∫ F(t)·G(t) dt` in which `F` is a first moment that grows and `G` is a kernel
decaying like `C/|t|` is controlled by a *geometric* series rather than by the length of the range.
Split the range `[t₀, t₀·2^M]` at the dyadic heights `t₀·2^m`; on each block the kernel is at most
`C/(t₀·2^m)`, so the block contributes `C/(t₀2^m)` times the block moment.  If the block moment
grows like the square root of the height — the shape produced by a mean-value estimate for a
Dirichlet polynomial, whose bound is proportional to the square root of the number of cells — then
the `m`-th term carries the factor `(√2/2)^m` and the total is bounded independently of `M`, hence
independently of the height of the range.

The kernel of a smoothed Perron formula has exactly this decay: the Mellin bound for the smoothing
weight holds with any number of factors of `s`, and one factor already gives `‖W(s)‖ ≤ C/‖s‖` with
a constant proportional to `N^σ(N/H)` rather than to the `N^σ(N/H)²` forced by two factors.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Complex MeasureTheory Set

/-- The square root of a power of a nonnegative number is the power of its square root. -/
theorem sqrt_pow_nat {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    Real.sqrt (x ^ m) = Real.sqrt x ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- A partial geometric sum is bounded by the value of the whole series. -/
theorem sum_range_geom_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, r ^ m ≤ (1 - r)⁻¹ := by
  rw [← tsum_geometric_of_lt_one hr0 hr1]
  exact Summable.sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
    (hasSum_geometric_of_lt_one hr0 hr1).summable

/-- A finite sum whose terms decay geometrically is bounded independently of its length. -/
theorem sum_range_le_geometric {c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1) {u : ℕ → ℝ}
    {M : ℕ} (hu : ∀ m, m < M → u m ≤ c * r ^ m) :
    ∑ m ∈ Finset.range M, u m ≤ c * (1 - r)⁻¹ := by
  calc ∑ m ∈ Finset.range M, u m
      ≤ ∑ m ∈ Finset.range M, c * r ^ m :=
        Finset.sum_le_sum fun m hm => hu m (Finset.mem_range.1 hm)
    _ = c * ∑ m ∈ Finset.range M, r ^ m := by rw [Finset.mul_sum]
    _ ≤ c * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left (sum_range_geom_le_inv hr0 hr1 M) hc

/-- **The dyadic decomposition of a vertical integral against a decaying kernel.**  With `G` at most
`C/t` on `[t₀, ∞)` and `F` nonnegative, the integral over `[t₀, t₀·2^M]` is at most the sum over
dyadic blocks of `C/(t₀·2^m)` times the moment of `F` over the block: the kernel's decay is charged
once per block instead of being replaced by its size at the bottom of the range. -/
theorem integral_mul_kernel_le_sum_dyadic {F G : ℝ → ℝ} {C t₀ : ℝ} (ht₀ : 0 < t₀) (hC : 0 ≤ C)
    (hF : ∀ t, 0 ≤ F t) (hG : ∀ t, t₀ ≤ t → G t ≤ C / t) {M : ℕ}
    (hFint : ∀ m, m < M → IntervalIntegrable F volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)))
    (hFGint : ∀ m, m < M →
      IntervalIntegrable (fun t => F t * G t) volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1))) :
    (∫ t in t₀..(t₀ * 2 ^ M), F t * G t)
      ≤ ∑ m ∈ Finset.range M, (C / (t₀ * 2 ^ m)) * ∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t => F t * G t) (μ := volume) (a := fun m : ℕ => t₀ * 2 ^ m) (n := M) hFGint
  have h0 : t₀ * (2 : ℝ) ^ (0 : ℕ) = t₀ := by norm_num
  rw [h0] at hsplit
  rw [← hsplit]
  refine Finset.sum_le_sum fun m hm => ?_
  have hmM : m < M := Finset.mem_range.1 hm
  have hone : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hpos : 0 < t₀ * 2 ^ m := by positivity
  have hstep : (2 : ℝ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hle : t₀ * 2 ^ m ≤ t₀ * 2 ^ (m + 1) := mul_le_mul_of_nonneg_left hstep ht₀.le
  have hmono : ∀ t ∈ Set.Icc (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)),
      F t * G t ≤ F t * (C / (t₀ * 2 ^ m)) := by
    intro t ht
    have ht1 : t₀ * 2 ^ m ≤ t := ht.1
    have ht0 : t₀ ≤ t := le_trans (by nlinarith) ht1
    have hker : G t ≤ C / (t₀ * 2 ^ m) :=
      le_trans (hG t ht0) (div_le_div_of_nonneg_left hC hpos ht1)
    exact mul_le_mul_of_nonneg_left hker (hF t)
  calc (∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t * G t)
      ≤ ∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t * (C / (t₀ * 2 ^ m)) :=
        intervalIntegral.integral_mono_on hle (hFGint m hmM)
          ((hFint m hmM).mul_const _) hmono
    _ = (C / (t₀ * 2 ^ m)) * ∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t := by
        rw [intervalIntegral.integral_mul_const]; ring

/-- The `m`-th dyadic term of a square-root block moment against a `C/t` kernel is a constant times
`(√2/2)^m`. -/
theorem dyadic_sqrt_term_eq {C K t₀ : ℝ} (ht₀ : 0 < t₀) (m : ℕ) :
    (C / (t₀ * 2 ^ m)) * (K * Real.sqrt (t₀ * 2 ^ (m + 1)))
      = (C * K * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m := by
  have hs2 : Real.sqrt 2 ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    exact ne_of_gt this
  have hst : Real.sqrt t₀ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht₀)
  have hsqrt : Real.sqrt (t₀ * 2 ^ (m + 1))
      = Real.sqrt t₀ * (Real.sqrt 2 ^ m * Real.sqrt 2) := by
    rw [Real.sqrt_mul ht₀.le, pow_succ, Real.sqrt_mul (by positivity),
      sqrt_pow_nat (by norm_num : (0:ℝ) ≤ 2)]
  have ht : t₀ = Real.sqrt t₀ * Real.sqrt t₀ := (Real.mul_self_sqrt ht₀.le).symm
  rw [hsqrt, div_pow]
  rw [show t₀ * 2 ^ m = Real.sqrt t₀ * Real.sqrt t₀ * 2 ^ m by rw [← ht]]
  have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
  field_simp

/-- **The vertical integral is bounded independently of the height.**  If the moment of `F` over the
dyadic block ending at height `t₀·2^{m+1}` is at most `K` times the square root of that height — the
shape of a mean-value estimate for a Dirichlet polynomial — and the kernel decays like `C/t`, then

`∫_{t₀}^{t₀·2^M} F·G ≤ C·K·√2·(1 − √2/2)⁻¹/√t₀`

with no dependence on `M`.  The square-root growth of the moment is exactly half of the linear
growth of the range, so the kernel's first-order decay wins by a geometric factor per block. -/
theorem integral_mul_kernel_le_of_sqrt_block_moment {F G : ℝ → ℝ} {C K t₀ : ℝ} (ht₀ : 0 < t₀)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hF : ∀ t, 0 ≤ F t) (hG : ∀ t, t₀ ≤ t → G t ≤ C / t) {M : ℕ}
    (hFint : ∀ m, m < M → IntervalIntegrable F volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)))
    (hFGint : ∀ m, m < M →
      IntervalIntegrable (fun t => F t * G t) volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)))
    (hmom : ∀ m, m < M →
      (∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t) ≤ K * Real.sqrt (t₀ * 2 ^ (m + 1))) :
    (∫ t in t₀..(t₀ * 2 ^ M), F t * G t)
      ≤ (C * K * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹ := by
  have hs2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2lt : Real.sqrt 2 < 2 := by nlinarith
  refine le_trans (integral_mul_kernel_le_sum_dyadic ht₀ hC hF hG hFint hFGint) ?_
  refine sum_range_le_geometric (c := C * K * Real.sqrt 2 / Real.sqrt t₀)
    (r := Real.sqrt 2 / 2) (by positivity) (by positivity) (by linarith) ?_
  intro m hm
  have hkernel : (0 : ℝ) ≤ C / (t₀ * 2 ^ m) := by positivity
  calc (C / (t₀ * 2 ^ m)) * ∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t
      ≤ (C / (t₀ * 2 ^ m)) * (K * Real.sqrt (t₀ * 2 ^ (m + 1))) :=
        mul_le_mul_of_nonneg_left (hmom m hm) hkernel
    _ = (C * K * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m :=
        dyadic_sqrt_term_eq ht₀ m

/-- **The first-order decay of the smoothing kernel.**  The one-factor case of the Mellin bound for
the smoothing weight: `‖s‖·‖W(s)‖` is bounded on the line `Re s = σ`, so `‖W(σ+iy)‖ ≤ C/√(σ²+y²)`.
The constant is proportional to `N^σ(N/H)`, one power of `N/H` rather than the two forced by the
quadratic-decay case, so at `H = N/(log N)^k` it costs a logarithmic factor. -/
theorem exists_bound_mellin_smoothWeight_first_order {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ}
    (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
      ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I)‖
        ≤ C / Real.sqrt (σ ^ 2 + y ^ 2) := by
  obtain ⟨C, hC0, hbound⟩ := exists_bound_mellin_smoothWeight hN hH 0 σ
  refine ⟨C, hC0, fun y => ?_⟩
  have hre : ((σ : ℂ) + (y : ℝ) * I).re = σ := by simp
  have h := hbound ((σ : ℂ) + (y : ℝ) * I) (by rw [hre]; exact hσ) (by rw [hre])
  simp only [Finset.range_zero, Finset.prod_empty, mul_one] at h
  have hnorm : ‖(σ : ℂ) + (y : ℝ) * I‖ = Real.sqrt (σ ^ 2 + y ^ 2) :=
    Complex.norm_add_mul_I σ y
  have hpos : 0 < Real.sqrt (σ ^ 2 + y ^ 2) := by
    refine Real.sqrt_pos.2 ?_
    positivity
  rw [le_div_iff₀ hpos, mul_comm, ← hnorm]
  refine le_trans (le_of_eq ?_) h
  rw [mellin]
  simp [smul_eq_mul]

/-- The smoothing kernel decays like `C/|y|` in the height: on the line `Re s = σ` the bound
`C/√(σ²+y²)` is at most `C/|y|`. -/
theorem exists_bound_mellin_smoothWeight_height {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ}
    (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y →
      ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I)‖
        ≤ C / y := by
  obtain ⟨C, hC0, hbound⟩ := exists_bound_mellin_smoothWeight_first_order hN hH hσ
  refine ⟨C, hC0, fun y hy => ?_⟩
  refine (hbound y).trans ?_
  refine div_le_div_of_nonneg_left hC0 hy ?_
  calc y = Real.sqrt (y ^ 2) := by rw [Real.sqrt_sq hy.le]
    _ ≤ Real.sqrt (σ ^ 2 + y ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Complex MeasureTheory Set

/-- **The vertical integral against an affine block moment.**  A mean-square estimate whose bound is
`Q + κ·(height)` gives a block moment `K·√(height) + L·(height)`: the square-root part is charged a
geometric series by the kernel's decay, while the linear part is charged one constant per block, hence
`2CL` times the number of blocks.  The linear part is the only source of a logarithmic dependence on
the height of the range. -/
theorem integral_mul_kernel_le_of_affine_block_moment {F G : ℝ → ℝ} {C K L t₀ : ℝ} (ht₀ : 0 < t₀)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hF : ∀ t, 0 ≤ F t) (hG : ∀ t, t₀ ≤ t → G t ≤ C / t)
    {M : ℕ}
    (hFint : ∀ m, m < M → IntervalIntegrable F volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)))
    (hFGint : ∀ m, m < M →
      IntervalIntegrable (fun t => F t * G t) volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)))
    (hmom : ∀ m, m < M → (∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t)
      ≤ K * Real.sqrt (t₀ * 2 ^ (m + 1)) + L * (t₀ * 2 ^ (m + 1))) :
    (∫ t in t₀..(t₀ * 2 ^ M), F t * G t)
      ≤ (C * K * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹ + 2 * C * L * M := by
  have hs2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2lt : Real.sqrt 2 < 2 := by nlinarith
  refine le_trans (integral_mul_kernel_le_sum_dyadic ht₀ hC hF hG hFint hFGint) ?_
  have hbound : ∀ m ∈ Finset.range M,
      (C / (t₀ * 2 ^ m)) * ∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t
        ≤ (C * K * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m + 2 * C * L := by
    intro m hm
    have hker : (0 : ℝ) ≤ C / (t₀ * 2 ^ m) := by positivity
    have hlin : (C / (t₀ * 2 ^ m)) * (L * (t₀ * 2 ^ (m + 1))) = 2 * C * L := by
      have h2m : (t₀ : ℝ) * 2 ^ m ≠ 0 := by positivity
      field_simp
      ring
    calc (C / (t₀ * 2 ^ m)) * ∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t
        ≤ (C / (t₀ * 2 ^ m)) *
            (K * Real.sqrt (t₀ * 2 ^ (m + 1)) + L * (t₀ * 2 ^ (m + 1))) :=
          mul_le_mul_of_nonneg_left (hmom m (Finset.mem_range.1 hm)) hker
      _ = (C / (t₀ * 2 ^ m)) * (K * Real.sqrt (t₀ * 2 ^ (m + 1)))
            + (C / (t₀ * 2 ^ m)) * (L * (t₀ * 2 ^ (m + 1))) := by ring
      _ = (C * K * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m + 2 * C * L := by
          rw [dyadic_sqrt_term_eq ht₀ m, hlin]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hgeom : ∑ m ∈ Finset.range M,
      (C * K * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m
        ≤ (C * K * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹ :=
    sum_range_le_geometric (by positivity) (by positivity) (by linarith) fun m _ => le_rfl
  have hconst : (M : ℝ) * (2 * C * L) = 2 * C * L * M := by ring
  linarith

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Complex MeasureTheory Set

/-- **The vertical integral against a block moment of general affine-plus-constant shape.**  A block
moment `J + K√(height) + L·(height)` — the shape a product of two Dirichlet polynomials produces, each
with an affine mean square — is charged two geometric series and one constant per block. -/
theorem integral_mul_kernel_le_of_general_block_moment {F G : ℝ → ℝ} {C J K L t₀ : ℝ} (ht₀ : 0 < t₀)
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (hK : 0 ≤ K) (hF : ∀ t, 0 ≤ F t) (hG : ∀ t, t₀ ≤ t → G t ≤ C / t)
    {M : ℕ}
    (hFint : ∀ m, m < M → IntervalIntegrable F volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)))
    (hFGint : ∀ m, m < M →
      IntervalIntegrable (fun t => F t * G t) volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)))
    (hmom : ∀ m, m < M → (∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t)
      ≤ J + K * Real.sqrt (t₀ * 2 ^ (m + 1)) + L * (t₀ * 2 ^ (m + 1))) :
    (∫ t in t₀..(t₀ * 2 ^ M), F t * G t)
      ≤ 2 * (C * J / t₀)
          + (C * K * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹
          + 2 * C * L * M := by
  have hs2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2lt : Real.sqrt 2 < 2 := by nlinarith
  refine le_trans (integral_mul_kernel_le_sum_dyadic ht₀ hC hF hG hFint hFGint) ?_
  have hbound : ∀ m ∈ Finset.range M,
      (C / (t₀ * 2 ^ m)) * ∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t
        ≤ (C * J / t₀) * (1 / 2 : ℝ) ^ m
            + (C * K * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m + 2 * C * L := by
    intro m hm
    have hker : (0 : ℝ) ≤ C / (t₀ * 2 ^ m) := by positivity
    have h2m : (t₀ : ℝ) * 2 ^ m ≠ 0 := by positivity
    have hconst : (C / (t₀ * 2 ^ m)) * J = (C * J / t₀) * (1 / 2 : ℝ) ^ m := by
      rw [div_pow, one_pow]
      field_simp
    have hlin : (C / (t₀ * 2 ^ m)) * (L * (t₀ * 2 ^ (m + 1))) = 2 * C * L := by
      field_simp
      ring
    calc (C / (t₀ * 2 ^ m)) * ∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t
        ≤ (C / (t₀ * 2 ^ m)) *
            (J + K * Real.sqrt (t₀ * 2 ^ (m + 1)) + L * (t₀ * 2 ^ (m + 1))) :=
          mul_le_mul_of_nonneg_left (hmom m (Finset.mem_range.1 hm)) hker
      _ = (C / (t₀ * 2 ^ m)) * J + (C / (t₀ * 2 ^ m)) * (K * Real.sqrt (t₀ * 2 ^ (m + 1)))
            + (C / (t₀ * 2 ^ m)) * (L * (t₀ * 2 ^ (m + 1))) := by ring
      _ = (C * J / t₀) * (1 / 2 : ℝ) ^ m
            + (C * K * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m + 2 * C * L := by
          rw [hconst, dyadic_sqrt_term_eq ht₀ m, hlin]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have hgeom1 : ∑ m ∈ Finset.range M, (C * J / t₀) * (1 / 2 : ℝ) ^ m
      ≤ (C * J / t₀) * (1 - 1 / 2 : ℝ)⁻¹ :=
    sum_range_le_geometric (by positivity) (by norm_num) (by norm_num) fun m _ => le_rfl
  have hgeom2 : ∑ m ∈ Finset.range M,
      (C * K * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m
        ≤ (C * K * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹ :=
    sum_range_le_geometric (by positivity) (by positivity) (by linarith) fun m _ => le_rfl
  have hinv : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
  rw [hinv] at hgeom1
  have hconstM : (M : ℝ) * (2 * C * L) = 2 * C * L * M := by ring
  linarith

end GaloisForLFunctions.HTGeometry
end
