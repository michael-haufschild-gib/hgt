import Mathlib

/-!
# The Li coefficients as a Chebyshev kernel over the reciprocal seam

Under the functional-equation folding `ρ = 1/2 + w`, `ρ' = 1 - ρ = 1/2 - w`, the pair contribution
to the `n`-th Li coefficient is

`L_n(w) = [1 - (1 - 1/ρ)^n] + [1 - (1 - 1/ρ')^n] = 2 - (q^n + q^{-n})`,  `q = (w - 1/2)/(w + 1/2)`,

and in the reciprocal seam coordinate `y = -w^{-2}` one has `(q + q^{-1})/2 = (4 - y)/(4 + y)`.  Hence

`L_n(y) = 2 - 2·T_n((4 - y)/(4 + y))`

with `T_n` the Chebyshev polynomial of the first kind — an **exact rational Chebyshev kernel**, not a
finite triangular transform.  Its only singularity is at `y = -4`, it vanishes at the reciprocal
accumulation point `y = 0`, and for `n = 1` it is `4y/(4+y)`, whose Taylor coefficients
`(-1)^k/4^k` are **all nonzero**: every Li coefficient sees an infinite tail of reciprocal moments.

## Main results

* `liPairKernel_eq_chebyshev` — the exact FE-folded kernel identity;
* `liChebyshevKernel_zero` — the kernel vanishes at `y = 0`;
* `liChebyshevKernel_one`, `hasSum_liChebyshevKernel_one`, `liKernelOne_coeff_ne_zero` — the first
  kernel, its expansion `y - y²/4 + y³/16 - …` on `‖y‖ < 4`, and the non-vanishing of every
  coefficient;
* `analyticOnNhd_liChebyshevKernel` — analyticity away from the single pole `y = -4`;
* `tsum_liChebyshevKernel_one` — the Li coefficient as the absolutely convergent Chebyshev-kernel
  transform of **all** the reciprocal moments `T_k = Σ_j m_j y_j^k`.
-/

namespace GaloisForLFunctions

open Polynomial

/-- The FE-folded pair contribution to the `n`-th Li coefficient, in the seam coordinate
`ρ = 1/2 + w`, `ρ' = 1/2 - w`. -/
noncomputable def liPairKernel (n : ℕ) (w : ℂ) : ℂ :=
  (1 - (1 - (1 / 2 + w)⁻¹) ^ n) + (1 - (1 - (1 / 2 - w)⁻¹) ^ n)

/-- The Chebyshev kernel in the reciprocal seam coordinate `y = -w⁻²`. -/
noncomputable def liChebyshevKernel (n : ℕ) (y : ℂ) : ℂ :=
  2 - 2 * (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval ((4 - y) / (4 + y))

theorem two_mul_chebyshevT_eval_half_add_inv (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    2 * (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval ((z + z⁻¹) / 2) = z ^ n + (z⁻¹) ^ n := by
  have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  have hd := Polynomial.dickson_one_one_eval_add_inv z z⁻¹ hzz n
  rw [Polynomial.dickson_one_one_eq_chebyshev_T ℂ n] at hd
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_comp,
    Polynomial.eval_C, Polynomial.eval_X] at hd
  rw [← hd]
  congr 2
  rw [invOf_eq_inv]
  ring

/-- **The exact FE-folded Li kernel.**  In the reciprocal seam coordinate `y = -w⁻²` the paired Li
contribution of an FE zero pair is `2 − 2·T_n((4−y)/(4+y))`. -/
theorem liPairKernel_eq_chebyshev (n : ℕ) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1 / 2)
    (h2 : w ≠ -(1 / 2)) :
    liPairKernel n w = liChebyshevKernel n (-(w ^ (2 : ℕ))⁻¹) := by
  have hA : (1 / 2 + w) ≠ 0 := fun h => h2 (by linear_combination h)
  have hB : (1 / 2 - w) ≠ 0 := fun h => h1 (by linear_combination -h)
  have hwm : (w - 1 / 2) ≠ 0 := fun h => h1 (by linear_combination h)
  have hwp : (w + 1 / 2) ≠ 0 := fun h => h2 (by linear_combination h)
  have hw2 : (w : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 h0
  have hA2 : (1 : ℂ) + w * 2 ≠ 0 := fun h => hA (by linear_combination h / 2)
  have hB2 : (1 : ℂ) - w * 2 ≠ 0 := fun h => hB (by linear_combination h / 2)
  have hm2 : (w : ℂ) * 2 - 1 ≠ 0 := fun h => hwm (by linear_combination h / 2)
  have hp2 : (w : ℂ) * 2 + 1 ≠ 0 := fun h => hwp (by linear_combination h / 2)
  have h4 : (4 : ℂ) * w ^ (2 : ℕ) - 1 ≠ 0 := by
    intro h
    have hfac : (2 * w - 1) * (2 * w + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact h1 (by linear_combination h' / 2)
    · exact h2 (by linear_combination h' / 2)
  set q : ℂ := (w - 1 / 2) / (w + 1 / 2) with hq
  have hq0 : q ≠ 0 := div_ne_zero hwm hwp
  have hAinv : (1 / 2 + w) * (1 / 2 + w)⁻¹ = 1 := mul_inv_cancel₀ hA
  have hBinv : (1 / 2 - w) * (1 / 2 - w)⁻¹ = 1 := mul_inv_cancel₀ hB
  have hinv2 : (w : ℂ) ^ (2 : ℕ) * (w ^ (2 : ℕ))⁻¹ = 1 := mul_inv_cancel₀ hw2
  have e1 : 1 - (1 / 2 + w)⁻¹ = q := by
    rw [hq, eq_div_iff hwp]
    linear_combination -hAinv
  have e2 : 1 - (1 / 2 - w)⁻¹ = q⁻¹ := by
    rw [hq, inv_div, eq_div_iff hwm]
    linear_combination hBinv
  have hnumeq : (4 : ℂ) - -(w ^ (2 : ℕ))⁻¹ = (4 * w ^ (2 : ℕ) + 1) / w ^ (2 : ℕ) := by
    rw [eq_div_iff hw2]
    linear_combination hinv2
  have hdeneq : (4 : ℂ) + -(w ^ (2 : ℕ))⁻¹ = (4 * w ^ (2 : ℕ) - 1) / w ^ (2 : ℕ) := by
    rw [eq_div_iff hw2]
    linear_combination -hinv2
  have hL : (4 - -(w ^ (2 : ℕ))⁻¹) / (4 + -(w ^ (2 : ℕ))⁻¹) = (4 * w ^ (2 : ℕ) + 1) / (4 * w ^ (2 : ℕ) - 1) := by
    rw [hnumeq, hdeneq]
    field_simp
  have hR : (q + q⁻¹) / 2 = (4 * w ^ (2 : ℕ) + 1) / (4 * w ^ (2 : ℕ) - 1) := by
    rw [hq, inv_div, div_add_div _ _ hwp hwm, div_div,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero hwp hwm) two_ne_zero) h4]
    ring
  have hy : (4 - -(w ^ (2 : ℕ))⁻¹) / (4 + -(w ^ (2 : ℕ))⁻¹) = (q + q⁻¹) / 2 := by rw [hL, hR]
  rw [liPairKernel, liChebyshevKernel, e1, e2, hy,
    two_mul_chebyshevT_eval_half_add_inv n hq0]
  ring

theorem chebyshevT_eval_one (n : ℕ) : (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval 1 = 1 := by
  simp

/-- The kernel vanishes at the reciprocal accumulation point `y = 0`. -/
@[simp] theorem liChebyshevKernel_zero (n : ℕ) : liChebyshevKernel n 0 = 0 := by
  rw [liChebyshevKernel]
  norm_num [chebyshevT_eval_one]

/-- The first kernel in closed form: `L_1(y) = 4y/(4+y)`. -/
theorem liChebyshevKernel_one {y : ℂ} (hy : (4 : ℂ) + y ≠ 0) :
    liChebyshevKernel 1 y = 4 * y / (4 + y) := by
  rw [liChebyshevKernel]
  have hT : (Polynomial.Chebyshev.T ℂ (((1 : ℕ)) : ℤ)) = Polynomial.X := by
    norm_num [Polynomial.Chebyshev.T_one]
  rw [hT, Polynomial.eval_X, eq_div_iff hy]
  field_simp
  ring

/-- **The infinite reciprocal-moment expansion of the first Li kernel.**  On `‖y‖ < 4`,
`L_1(y) = Σ_{k ≥ 0} (−1)^k y^{k+1}/4^k = y − y²/4 + y³/16 − …`. -/
theorem hasSum_liChebyshevKernel_one {y : ℂ} (hy : ‖y‖ < 4) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k / 4 ^ k * y ^ (k + 1)) (liChebyshevKernel 1 y) := by
  have hy4 : (4 : ℂ) + y ≠ 0 := by
    intro h
    have hval : y = -4 := by linear_combination h
    rw [hval] at hy
    norm_num at hy
  have hr : ‖(-y / 4 : ℂ)‖ < 1 := by
    rw [norm_div, norm_neg]
    norm_num
    linarith [hy]
  have hgeo := hasSum_geometric_of_norm_lt_one hr
  have hsum : HasSum (fun k : ℕ => y * (-y / 4 : ℂ) ^ k) (y * (1 - (-y / 4))⁻¹) :=
    hgeo.mul_left y
  have heq : y * (1 - (-y / 4 : ℂ))⁻¹ = liChebyshevKernel 1 y := by
    rw [liChebyshevKernel_one hy4]
    rw [eq_div_iff hy4]
    have h1 : (1 : ℂ) - (-y / 4) = (4 + y) / 4 := by ring
    rw [h1, inv_div]
    field_simp
  have hfun : (fun k : ℕ => (-1 : ℂ) ^ k / 4 ^ k * y ^ (k + 1))
      = fun k : ℕ => y * (-y / 4 : ℂ) ^ k := by
    funext k
    have hp : ((-y / 4 : ℂ)) ^ k = (-1 : ℂ) ^ k * (y ^ k / 4 ^ k) := by
      rw [neg_div, neg_pow, div_pow]
    rw [hp]
    ring
  rw [hfun, ← heq]
  exact hsum

/-- Every Taylor coefficient of the first kernel is nonzero: the Li-to-reciprocal chart is an
**infinite** expansion, not a finite triangular transform. -/
theorem liKernelOne_coeff_ne_zero (k : ℕ) : ((-1 : ℂ) ^ k / 4 ^ k) ≠ 0 := by
  simp

theorem differentiableAt_liChebyshevKernel (n : ℕ) {y : ℂ} (hy : (4 : ℂ) + y ≠ 0) :
    DifferentiableAt ℂ (liChebyshevKernel n) y := by
  have hinner : DifferentiableAt ℂ (fun z : ℂ => (4 - z) / (4 + z)) y :=
    (((differentiableAt_const _).sub differentiableAt_id)).div
      ((differentiableAt_const _).add differentiableAt_id) hy
  have hpoly : DifferentiableAt ℂ
      (fun z : ℂ => (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval z) ((4 - y) / (4 + y)) :=
    (Polynomial.differentiable _).differentiableAt
  exact (differentiableAt_const _).sub (((hpoly.comp y hinner)).const_mul _)

/-- The kernel is analytic away from its single pole `y = −4`. -/
theorem analyticOnNhd_liChebyshevKernel (n : ℕ) :
    AnalyticOnNhd ℂ (liChebyshevKernel n) {y : ℂ | (4 : ℂ) + y ≠ 0} := by
  have hopen : IsOpen {y : ℂ | (4 : ℂ) + y ≠ 0} :=
    isOpen_ne.preimage (continuous_const.add continuous_id)
  refine DifferentiableOn.analyticOnNhd (fun y hy => ?_) hopen
  exact (differentiableAt_liChebyshevKernel n hy).differentiableWithinAt

set_option maxHeartbeats 1000000 in
/-- **The Li coefficient as an infinite reciprocal-moment sum.**  If the reciprocal atoms all lie in
a disc `‖y‖ ≤ r < 4` and the multiplicities are absolutely summable, then the first Li coefficient
is the absolutely convergent Chebyshev-kernel transform of *all* the reciprocal moments
`T_k = Σ_j m_j y_j^k`. -/
theorem tsum_liChebyshevKernel_one {ι : Type*} (m : ι → ℂ) (yv : ι → ℂ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 4) (hy : ∀ j, ‖yv j‖ ≤ r) (hm : Summable (fun j => ‖m j‖)) :
    ∑' j, m j * liChebyshevKernel 1 (yv j)
      = ∑' k : ℕ, ((-1 : ℂ) ^ k / 4 ^ k) * ∑' j, m j * (yv j) ^ (k + 1) := by
  have hbound : ∀ j (k : ℕ), ‖m j * ((-1 : ℂ) ^ k / 4 ^ k * (yv j) ^ (k + 1))‖
      ≤ ‖m j‖ * (r * (r / 4) ^ k) := by
    intro j k
    have hnorm : ‖((-1 : ℂ) ^ k / 4 ^ k * (yv j) ^ (k + 1))‖ = ‖yv j‖ ^ (k + 1) / 4 ^ k := by
      rw [norm_mul, norm_div, norm_pow, norm_pow, norm_pow, norm_neg, norm_one, one_pow]
      norm_num
      ring
    rw [norm_mul, hnorm]
    have h1 : ‖yv j‖ ^ (k + 1) ≤ r ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg _) (hy j) _
    have h2 : r * (r / 4) ^ k = r ^ (k + 1) / 4 ^ k := by rw [div_pow]; ring
    rw [h2]
    gcongr
  have hsummable : Summable (fun p : ι × ℕ =>
      m p.1 * ((-1 : ℂ) ^ p.2 / 4 ^ p.2 * (yv p.1) ^ (p.2 + 1))) := by
    have hg : Summable (fun k : ℕ => r * (r / 4) ^ k) := by
      refine Summable.mul_left r ?_
      exact summable_geometric_of_lt_one (by positivity)
        (by rw [div_lt_one (by norm_num : (0:ℝ) < 4)]; linarith)
    refine Summable.of_norm_bounded
      (g := fun p : ι × ℕ => ‖m p.1‖ * (r * (r / 4) ^ p.2)) ?_ (fun p => hbound p.1 p.2)
    exact hm.mul_of_nonneg hg (fun j => norm_nonneg _) (fun k => by positivity)
  have hleft : ∀ j, m j * liChebyshevKernel 1 (yv j)
      = ∑' k : ℕ, m j * ((-1 : ℂ) ^ k / 4 ^ k * (yv j) ^ (k + 1)) := by
    intro j
    have hnorm : ‖yv j‖ < 4 := lt_of_le_of_lt (hy j) hr
    have := (hasSum_liChebyshevKernel_one hnorm).mul_left (m j)
    exact this.tsum_eq.symm
  calc ∑' j, m j * liChebyshevKernel 1 (yv j)
      = ∑' j, ∑' k : ℕ, m j * ((-1 : ℂ) ^ k / 4 ^ k * (yv j) ^ (k + 1)) := tsum_congr hleft
    _ = ∑' (k : ℕ) (j : ι), m j * ((-1 : ℂ) ^ k / 4 ^ k * (yv j) ^ (k + 1)) :=
        hsummable.tsum_comm.symm
    _ = ∑' k : ℕ, ((-1 : ℂ) ^ k / 4 ^ k) * ∑' j, m j * (yv j) ^ (k + 1) := by
        refine tsum_congr fun k => ?_
        rw [← tsum_mul_left]
        exact tsum_congr fun j => by ring

end GaloisForLFunctions
