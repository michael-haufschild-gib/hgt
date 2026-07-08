/-
# The regularized Fredholm determinant of a Hilbert–Schmidt operator

Mathlib has no Fredholm-determinant theory.  This file builds the **regularized (Hilbert–Carleman)
determinant** `det₂(1 − zK)` of a Hilbert–Schmidt kernel `K` and proves the **Plemelj identity**
relating its logarithmic derivative to the resolvent trace:

  `det₂(1 − zK) = exp(−∑_{n≥2} zⁿ/n · tr(Kⁿ))`,   `logDeriv det₂(1 − zK) = −tr(K(1−zK)⁻¹ − K)`.

For a merely Hilbert–Schmidt (not trace-class) operator the ordinary Fredholm determinant `det(1 − zK)`
does not exist — `tr(K)` need not converge — but the *regularized* determinant does, because `tr(Kⁿ)`
converges for every `n ≥ 2` (`Kⁿ` is a composition of Hilbert–Schmidt operators, hence trace-class).
The exponent series `∑_{n≥2} zⁿ/n·tr(Kⁿ)` converges for `|z|·‖K‖_HS < 1`, and its termwise derivative is
exactly the regularized resolvent trace `HilbertSchmidt.resolventTrace K z = ∑_{n≥1} zⁿ·tr(K^(n+1))`.

This is the exact shape of the completed-`ζ` logarithmic derivative `logDeriv Λ(s) = tr((s − Θ)⁻¹)` that
the seam construction welds to: the determinant whose zeros are the eigenvalues of the seam generator.

Main results:
* `fredholmExp`, `fredholmExp_summable` — the det₂ exponent `∑_{n≥2} zⁿ/n·tr(Kⁿ)`, convergent for
  `|z|·‖K‖_HS < 1`.
* `hasDerivAt_fredholmExp` — **termwise differentiation**: `(fredholmExp K)′(z) = resolventTrace K z` on
  the disk `|z| < r` (any `r` with `r·‖K‖_HS < 1`), via `hasDerivAt_tsum_of_isPreconnected`.
* `fredholmDet K z = exp(−fredholmExp K z)` — the regularized determinant `det₂(1 − zK)`.
* `logDeriv_fredholmDet` — **the Plemelj identity** `logDeriv (fredholmDet K) z = −resolventTrace K z`.
-/
import GaloisForLFunctions.HilbertSchmidt
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecificLimits.Normed

open scoped BigOperators

namespace HilbertSchmidt

variable {ι : Type*}

/-- The **regularized-determinant exponent** `∑_{n≥2} zⁿ/n·tr(Kⁿ) = ∑ₙ z^(n+2)/(n+2)·tr(K^(n+2))`.
The Hilbert–Carleman determinant is `exp` of its negative. -/
noncomputable def fredholmExp (K : ι × ι → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * (∑' i, hsPow K (n + 1) (i, i))

/-- The exponent series converges for `|z|·‖K‖_HS < 1`: its terms are dominated by the geometric series
`(|z|·‖K‖_HS)^(n+2)`. -/
theorem fredholmExp_summable {K : ι × ι → ℂ} (hK : IsHS K) (z : ℂ) (hz : ‖z‖ * hsNorm K < 1) :
    Summable (fun n : ℕ => z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * (∑' i, hsPow K (n + 1) (i, i))) := by
  apply Summable.of_norm_bounded (g := fun n => (‖z‖ * hsNorm K) ^ (n + 2))
  · have h0 : 0 ≤ ‖z‖ * hsNorm K := mul_nonneg (norm_nonneg z) (hsNorm_nonneg K)
    exact ((summable_geometric_of_lt_one h0 hz).mul_left ((‖z‖ * hsNorm K) ^ 2)).congr
      (fun n => by rw [pow_add]; ring)
  · intro n
    rw [norm_mul, norm_div, norm_pow]
    have hle : ‖∑' i, hsPow K (n + 1) (i, i)‖ ≤ (hsNorm K) ^ (n + 2) := hsTrace_hsPow_norm_le hK n
    have hnorm2 : ‖((n + 2 : ℕ) : ℂ)‖ = ((n : ℝ) + 2) := by rw [Complex.norm_natCast]; push_cast; ring
    rw [hnorm2]
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hden : (1 : ℝ) ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    calc ‖z‖ ^ (n + 2) / ((n : ℝ) + 2) * ‖∑' i, hsPow K (n + 1) (i, i)‖
        ≤ ‖z‖ ^ (n + 2) * (hsNorm K) ^ (n + 2) :=
          mul_le_mul (div_le_self (pow_nonneg hz0 _) hden) hle (norm_nonneg _) (pow_nonneg hz0 _)
      _ = (‖z‖ * hsNorm K) ^ (n + 2) := by rw [mul_pow]

/-- The termwise derivative of the exponent series: `d/dz[z^(n+2)/(n+2)·tr(K^(n+2))] = z^(n+1)·tr(K^(n+2))`. -/
theorem hasDerivAt_fredholmExp_term {K : ι × ι → ℂ} (n : ℕ) (y : ℂ) :
    HasDerivAt (fun z : ℂ => z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * (∑' i, hsPow K (n + 1) (i, i)))
      (y ^ (n + 1) * (∑' i, hsPow K (n + 1) (i, i))) y := by
  have hp : HasDerivAt (fun z : ℂ => z ^ (n + 2)) (((n + 2 : ℕ) : ℂ) * y ^ (n + 1)) y := by
    simpa using hasDerivAt_pow (n + 2) y
  have h2 := (hp.div_const ((n + 2 : ℕ) : ℂ)).mul_const (∑' i, hsPow K (n + 1) (i, i))
  convert h2 using 1
  have hne : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **Termwise differentiation of the determinant exponent.**  On the disk `|z| < r` (for any `r` with
`r·‖K‖_HS < 1`), the exponent series is differentiable and its derivative is the resolvent trace:
`(fredholmExp K)′(z) = resolventTrace K z`.  The uniform geometric bound on the term derivatives lets the
sum be differentiated term by term (`hasDerivAt_tsum_of_isPreconnected`). -/
theorem hasDerivAt_fredholmExp {K : ι × ι → ℂ} (hK : IsHS K) (r : ℝ) (hr : r * hsNorm K < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    HasDerivAt (fun w => fredholmExp K w) (resolventTrace K z) z := by
  have hzr : ‖z‖ < r := by rwa [mem_ball_zero_iff] at hz
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg z) hzr
  have hL0 : 0 ≤ hsNorm K := hsNorm_nonneg K
  have hrL : 0 ≤ r * hsNorm K := mul_nonneg hr0.le hL0
  have husum : Summable (fun n : ℕ => hsNorm K * (r * hsNorm K) ^ (n + 1)) := by
    apply Summable.mul_left
    exact ((summable_geometric_of_lt_one hrL hr).mul_right (r * hsNorm K)).congr
      (fun n => by rw [pow_succ])
  apply hasDerivAt_tsum_of_isPreconnected husum Metric.isOpen_ball
    (convex_ball 0 r).isPreconnected (fun n y _ => hasDerivAt_fredholmExp_term n y) ?_ hz ?_ hz
  · intro n y hy
    have hyr : ‖y‖ < r := by rwa [mem_ball_zero_iff] at hy
    rw [norm_mul, norm_pow]
    have hcn : ‖∑' i, hsPow K (n + 1) (i, i)‖ ≤ hsNorm K ^ (n + 2) := hsTrace_hsPow_norm_le hK n
    have hyp : ‖y‖ ^ (n + 1) ≤ r ^ (n + 1) := by gcongr
    calc ‖y‖ ^ (n + 1) * ‖∑' i, hsPow K (n + 1) (i, i)‖
        ≤ r ^ (n + 1) * hsNorm K ^ (n + 2) :=
          mul_le_mul hyp hcn (norm_nonneg _) (pow_nonneg hr0.le _)
      _ = hsNorm K * (r * hsNorm K) ^ (n + 1) := by rw [mul_pow]; ring
  · apply fredholmExp_summable hK z
    calc ‖z‖ * hsNorm K ≤ r * hsNorm K := mul_le_mul_of_nonneg_right hzr.le hL0
      _ < 1 := hr

/-- The **regularized (Hilbert–Carleman) determinant** `det₂(1 − zK) = exp(−∑_{n≥2} zⁿ/n·tr(Kⁿ))`. -/
noncomputable def fredholmDet (K : ι × ι → ℂ) (z : ℂ) : ℂ := Complex.exp (- fredholmExp K z)

/-- **The Plemelj identity.**  The logarithmic derivative of the regularized Fredholm determinant is the
negative resolvent trace: `logDeriv (det₂(1 − ·K)) z = −resolventTrace K z` on `|z| < r`, `r·‖K‖_HS < 1`.
This is the infinite-dimensional analogue of `logDeriv Λ(s) = tr((s − Θ)⁻¹)`: the zeros of the
determinant are exactly the poles of the resolvent trace, the eigenvalues of the operator. -/
theorem logDeriv_fredholmDet {K : ι × ι → ℂ} (hK : IsHS K) (r : ℝ) (hr : r * hsNorm K < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    logDeriv (fun w => fredholmDet K w) z = - resolventTrace K z := by
  have hg : HasDerivAt (fun w => - fredholmExp K w) (- resolventTrace K z) z :=
    (hasDerivAt_fredholmExp hK r hr z hz).neg
  have hf : HasDerivAt (fun w => fredholmDet K w)
      (Complex.exp (- fredholmExp K z) * (- resolventTrace K z)) z := hg.cexp
  rw [logDeriv_apply, hf.deriv, fredholmDet, mul_comm, mul_div_assoc,
    div_self (Complex.exp_ne_zero _), mul_one]

/-- The regularized determinant never vanishes: it is a value of `Complex.exp`. -/
theorem fredholmDet_ne_zero (K : ι × ι → ℂ) (z : ℂ) : fredholmDet K z ≠ 0 := Complex.exp_ne_zero _

/-- The derivative of the determinant: `det₂′(z) = det₂(z)·(−resolventTrace K z)` on the disk. -/
theorem hasDerivAt_fredholmDet {K : ι × ι → ℂ} (hK : IsHS K) (r : ℝ) (hr : r * hsNorm K < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    HasDerivAt (fun w => fredholmDet K w) (fredholmDet K z * (- resolventTrace K z)) z :=
  (hasDerivAt_fredholmExp hK r hr z hz).neg.cexp

/-- The determinant is holomorphic on the disk `|z| < r` (`r·‖K‖_HS < 1`). -/
theorem fredholmDet_differentiableOn {K : ι × ι → ℂ} (hK : IsHS K) (r : ℝ) (hr : r * hsNorm K < 1) :
    DifferentiableOn ℂ (fun w => fredholmDet K w) (Metric.ball 0 r) :=
  fun z hz => (hasDerivAt_fredholmDet hK r hr z hz).differentiableAt.differentiableWithinAt

/-- **The determinant–L-function weld.**  Let `L` be holomorphic and nonvanishing on the disk `|z| < r`
(`r·‖K‖_HS < 1`).  If its logarithmic derivative matches the negative resolvent trace of `K`,
`logDeriv L = −resolventTrace K`, then the regularized Fredholm determinant `det₂(1 − zK)` equals `L` up
to a multiplicative constant: `det₂(1 − zK) = c·L(z)`.

This is the mechanical form of the Hilbert–Pólya weld: the hypothesis `logDeriv L = −resolventTrace K`
is exactly `logDeriv Λ(s) = tr((s − Θ)⁻¹)` (under the resolvent identification), and the conclusion is
that the determinant *is* the L-function `Λ` up to a constant.  The zeros of `det₂` are then the zeros of
`Λ`, i.e. the reciprocal eigenvalues `1/λ` of `K` — turning "the eigenvalues of `Θ` are the zeros of `Λ`"
into a consequence rather than an analogy.  (`fredholmDet` is `exp`, hence automatically nonvanishing, so
no nonvanishing hypothesis is needed on the determinant side.) -/
theorem fredholmDet_weld {K : ι × ι → ℂ} (hK : IsHS K) (r : ℝ) (hr : r * hsNorm K < 1)
    (L : ℂ → ℂ) (hLdiff : DifferentiableOn ℂ L (Metric.ball 0 r))
    (hLne : ∀ z ∈ Metric.ball (0 : ℂ) r, L z ≠ 0)
    (hmatch : ∀ z ∈ Metric.ball (0 : ℂ) r, logDeriv L z = - resolventTrace K z) :
    ∃ c, ∀ z ∈ Metric.ball (0 : ℂ) r, fredholmDet K z = c * L z := by
  have hderiv0 : Set.EqOn (deriv ((fun w => fredholmDet K w) / L)) 0 (Metric.ball 0 r) := by
    intro z hz
    have hLd : HasDerivAt L (deriv L z) z :=
      ((hLdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
    have hLderiv : deriv L z = L z * (- resolventTrace K z) := by
      have h := hmatch z hz
      rw [logDeriv_apply, div_eq_iff (hLne z hz)] at h
      rw [h]; ring
    have hg : HasDerivAt L (L z * (- resolventTrace K z)) z := hLderiv ▸ hLd
    have hf : HasDerivAt (fun w => fredholmDet K w) (fredholmDet K z * (- resolventTrace K z)) z :=
      hasDerivAt_fredholmDet hK r hr z hz
    have hd := (hf.div hg (hLne z hz)).deriv
    simp only [Pi.zero_apply]
    rw [hd]; ring
  obtain ⟨c, hc⟩ := Metric.isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball 0 r).isPreconnected
    ((fredholmDet_differentiableOn hK r hr).div hLdiff hLne) hderiv0
  refine ⟨c, fun z hz => ?_⟩
  have hcz := hc z hz
  rw [Pi.div_apply, div_eq_iff (hLne z hz)] at hcz
  exact hcz

end HilbertSchmidt
