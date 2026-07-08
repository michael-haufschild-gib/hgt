/-
# The Riemann zeta function as a trace-class Fredholm determinant

This file closes the determinant–L-function weld onto an object mathlib already defines: the **Riemann
zeta function** `riemannZeta`.  The regularized determinant `det₂(1 − zK)` of a countable diagonal
Hilbert–Schmidt operator is shown to be the infinite **Weierstrass product** over its eigenvalues,
`∏ᵢ (1 − z·gᵢ)·exp(z·gᵢ)`; stripping the Hilbert–Carleman correction with the trace gives the trace-class
determinant as the bare product `det₁(1 − zK) = ∏ᵢ (1 − z·gᵢ)`.  Specializing the eigenvalues to `gₚ = p^{−s}`
over the primes and evaluating at `z = 1`, the product is the inverse Euler product of `ζ`, and mathlib's
`riemannZeta_eulerProduct_hasProd` identifies it: for `Re s > 1`,

  `det₁(1 − diagMul (p ↦ p^{−s}))⁻¹ = riemannZeta s`.

So `ζ(s)` is the reciprocal of the characteristic Fredholm determinant of an explicit Hilbert–Schmidt
operator on `ℓ²(primes)` whose eigenvalues are `{p^{−s}}` — the L-function realized as a determinant, with
`logDeriv Λ = tr((s − Θ)⁻¹)` (via `logDeriv_fredholmDet`) a theorem for its Euler-product half.

The engine is the identity `det₂ = exp(−∑ᵢ (z·gᵢ + log(1 − z·gᵢ)))`: each summand is `−∑ₙ (z·gᵢ)^{n+2}/(n+2)`
(the log Taylor series), and the double series over `(eigenvalue, power)` is summed by Tonelli and turned
into the product by `HasSum.cexp` (`∏ exp = exp ∑`).

Main results:
* `hasSum_exponent_diagMul` — `∑ᵢ (z·gᵢ + log(1 − z·gᵢ)) = −fredholmExp K z` (the determinant exponent).
* `fredholmDet_tprod_diagMul` — `det₂(1 − z·diagMul g) = ∏ᵢ (1 − z·gᵢ)·exp(z·gᵢ)` (Weierstrass product).
* `fredholmDet1_tprod_diagMul` — `det₁(1 − z·diagMul g) = ∏ᵢ (1 − z·gᵢ)` (trace-class, bare product).
* `fredholmDet1_eq_inv_riemannZeta` — `det₁(1 − diagMul(p^{−s}))⁻¹ = riemannZeta s` for `Re s > 1`.
-/
import GaloisForLFunctions.FredholmDeterminantInfinite
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

open scoped BigOperators
open Complex

namespace HilbertSchmidt

variable {ι : Type*} [DecidableEq ι]

/-- The per-eigenvalue determinant exponent: `∑ₙ w^{n+2}/(n+2) = −(w + log(1 − w))` for `‖w‖ < 1`, the
log Taylor series `−log(1 − w) = ∑ₙ w^n/n` with the `n = 0, 1` terms removed. -/
theorem hasSum_peri (w : ℂ) (h : ‖w‖ < 1) :
    HasSum (fun n : ℕ => w ^ (n + 2) / ((n + 2 : ℕ) : ℂ)) (-(w + Complex.log (1 - w))) := by
  have hbase := Complex.hasSum_taylorSeries_neg_log h
  apply (hasSum_nat_add_iff (f := fun n : ℕ => w ^ n / (n : ℂ)) 2).mpr
  simpa [Finset.sum_range_succ] using hbase

/-- **The determinant exponent is a convergent sum over the eigenvalues:**
`∑ᵢ (z·gᵢ + log(1 − z·gᵢ)) = −fredholmExp (diagMul g) z` on `|z|·‖diagMul g‖_HS < 1`.  Each summand is
`−∑ₙ (z·gᵢ)^{n+2}/(n+2)`; the double series over eigenvalue index and power index is dominated by
`‖z‖^{n+2}·‖K‖_HS^n·‖gᵢ‖²` and summed by Tonelli (`HasSum.prod_fiberwise`, `Summable.tsum_comm`). -/
theorem hasSum_exponent_diagMul (g : ι → ℂ) (hs : Summable (fun i => ‖g i‖ ^ 2))
    (r : ℝ) (hr : r * hsNorm (diagMul g) < 1) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    HasSum (fun i => z * g i + Complex.log (1 - z * g i)) (- fredholmExp (diagMul g) z) := by
  set M := hsNorm (diagMul g) with hM
  have hM0 : 0 ≤ M := hsNorm_nonneg _
  have hzr : ‖z‖ < r := by rwa [mem_ball_zero_iff] at hz
  have hzM : ‖z‖ * M < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzr.le hM0) hr
  have hgle : ∀ i, ‖g i‖ ≤ M := fun i => norm_le_hsNorm_diagMul_infinite g hs i
  have hzgi : ∀ i, ‖z * g i‖ < 1 := fun i => by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hgle i) (norm_nonneg z)) hzM
  set G : ι → ℕ → ℂ := fun i n => (z * g i) ^ (n + 2) / ((n + 2 : ℕ) : ℂ) with hG
  have hgeom2 : Summable (fun n : ℕ => ‖z‖ ^ (n + 2) * M ^ n) := by
    have heq : (fun n : ℕ => ‖z‖ ^ (n + 2) * M ^ n) = fun n => ‖z‖ ^ 2 * (‖z‖ * M) ^ n := by
      funext n; rw [mul_pow]; ring
    rw [heq]; exact (summable_geometric_of_lt_one (by positivity) hzM).mul_left _
  have hF : Summable (fun p : ι × ℕ => ‖z‖ ^ (p.2 + 2) * M ^ p.2 * ‖g p.1‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun p => by positivity)]
    refine ⟨fun i => (hgeom2.mul_right (‖g i‖ ^ 2)).congr (fun n => by ring), ?_⟩
    have heq : (fun i => ∑' n : ℕ, ‖z‖ ^ (n + 2) * M ^ n * ‖g i‖ ^ 2)
        = fun i => (∑' n : ℕ, ‖z‖ ^ (n + 2) * M ^ n) * ‖g i‖ ^ 2 := by
      funext i; rw [← tsum_mul_right]
    rw [heq]; exact hs.mul_left _
  have hbound : ∀ p : ι × ℕ, ‖Function.uncurry G p‖ ≤ ‖z‖ ^ (p.2 + 2) * M ^ p.2 * ‖g p.1‖ ^ 2 := by
    intro p
    have h1 : ‖Function.uncurry G p‖ = ‖z * g p.1‖ ^ (p.2 + 2) / ((p.2 + 2 : ℕ) : ℝ) := by
      simp only [Function.uncurry, hG, norm_div, norm_pow, Complex.norm_natCast]
    rw [h1]
    have hden : (1 : ℝ) ≤ ((p.2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ p.2 + 2)
    calc ‖z * g p.1‖ ^ (p.2 + 2) / ((p.2 + 2 : ℕ) : ℝ)
        ≤ ‖z * g p.1‖ ^ (p.2 + 2) := div_le_self (by positivity) hden
      _ = ‖z‖ ^ (p.2 + 2) * ‖g p.1‖ ^ (p.2 + 2) := by rw [norm_mul, mul_pow]
      _ ≤ ‖z‖ ^ (p.2 + 2) * (M ^ p.2 * ‖g p.1‖ ^ 2) := by
          gcongr; rw [pow_add]; gcongr; exact hgle p.1
      _ = ‖z‖ ^ (p.2 + 2) * M ^ p.2 * ‖g p.1‖ ^ 2 := by ring
  have huncurry : Summable (Function.uncurry G) := hF.of_norm_bounded hbound
  have hfib : ∀ i, HasSum (fun n => Function.uncurry G (i, n))
      (-(z * g i + Complex.log (1 - z * g i))) := fun i => hasSum_peri (z * g i) (hzgi i)
  have hpf := huncurry.hasSum.prod_fiberwise hfib
  have hfe : (∑' p : ι × ℕ, Function.uncurry G p) = fredholmExp (diagMul g) z := by
    have key : (∑' p : ι × ℕ, Function.uncurry G p) = ∑' n : ℕ, ∑' i : ι, G i n :=
      (Summable.tsum_prod' huncurry (fun i => huncurry.prod_factor i)).trans
        (Summable.tsum_comm huncurry).symm
    rw [key, fredholmExp]
    apply tsum_congr; intro n
    rw [hsPow_diagMul, ← tsum_mul_left]
    apply tsum_congr; intro i
    simp only [hG, diagMul, if_true]; rw [mul_pow]; ring
  rw [hfe] at hpf; simpa using hpf.neg

/-- **The regularized determinant of a countable diagonal operator is the infinite Weierstrass product**
`det₂(1 − z·diagMul g) = ∏ᵢ (1 − z·gᵢ)·exp(z·gᵢ)` on `|z|·‖diagMul g‖_HS < 1`.  The factor `(1 − z·gᵢ)`
vanishes at the reciprocal eigenvalue `z = 1/gᵢ` and `exp(z·gᵢ)` is the Hilbert–Carleman regularization
making the product converge for a non-trace-class operator.  Proved from `∏ exp = exp ∑` applied to the
exponent identity `hasSum_exponent_diagMul`. -/
theorem fredholmDet_tprod_diagMul (g : ι → ℂ) (hs : Summable (fun i => ‖g i‖ ^ 2))
    (r : ℝ) (hr : r * hsNorm (diagMul g) < 1) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet (diagMul g) z = ∏' i, (1 - z * g i) * Complex.exp (z * g i) := by
  have hzr : ‖z‖ < r := by rwa [mem_ball_zero_iff] at hz
  have hzM : ‖z‖ * hsNorm (diagMul g) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzr.le (hsNorm_nonneg _)) hr
  have hzgi : ∀ i, ‖z * g i‖ < 1 := fun i => by
    rw [norm_mul]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (norm_le_hsNorm_diagMul_infinite g hs i) (norm_nonneg z)) hzM
  have hprod := (hasSum_exponent_diagMul g hs r hr z hz).cexp
  have hfun : (Complex.exp ∘ fun i => z * g i + Complex.log (1 - z * g i))
      = fun i => (1 - z * g i) * Complex.exp (z * g i) := by
    funext i
    have hne : (1 : ℂ) - z * g i ≠ 0 := by
      intro h
      have hlt := hzgi i
      rw [show z * g i = 1 from by linear_combination -h, norm_one] at hlt
      exact lt_irrefl 1 hlt
    simp only [Function.comp]; rw [Complex.exp_add, Complex.exp_log hne]; ring
  rw [hfun] at hprod
  rw [fredholmDet]; exact hprod.tprod_eq.symm

/-- The diagonal trace of a countable diagonal operator is the sum of its entries, `tr K = ∑ᵢ gᵢ`. -/
theorem hsTraceDiag_diagMul (g : ι → ℂ) : hsTraceDiag (diagMul g) = ∑' i, g i := by
  rw [hsTraceDiag]; apply tsum_congr; intro i; simp [diagMul]

/-- **The trace-class determinant of a countable diagonal operator is the bare product**, as a `HasProd`:
`det₁(1 − z·diagMul g) = ∏ᵢ (1 − z·gᵢ)` when `g` is additionally summable (trace-class).  The
Hilbert–Carleman `exp(z·gᵢ)` corrections cancel against `exp(−z·tr K)`; equivalently
`∑ᵢ log(1 − z·gᵢ) = −fredholmExp − z·tr K`, whose exponential is `det₁`. -/
theorem hasProd_fredholmDet1_diagMul (g : ι → ℂ) (hs2 : Summable (fun i => ‖g i‖ ^ 2))
    (hs1 : Summable g) (r : ℝ) (hr : r * hsNorm (diagMul g) < 1) (z : ℂ)
    (hz : z ∈ Metric.ball (0 : ℂ) r) :
    HasProd (fun i => 1 - z * g i) (fredholmDet1 (diagMul g) z) := by
  have hzr : ‖z‖ < r := by rwa [mem_ball_zero_iff] at hz
  have hzM : ‖z‖ * hsNorm (diagMul g) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzr.le (hsNorm_nonneg _)) hr
  have hne : ∀ i, (1 : ℂ) - z * g i ≠ 0 := fun i => by
    intro h
    have hlt : ‖z * g i‖ < 1 := by
      rw [norm_mul]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left (norm_le_hsNorm_diagMul_infinite g hs2 i) (norm_nonneg z)) hzM
    rw [show z * g i = 1 from by linear_combination -h, norm_one] at hlt; exact lt_irrefl 1 hlt
  have htr : HasSum (fun i => z * g i) (z * hsTraceDiag (diagMul g)) := by
    rw [hsTraceDiag_diagMul]; exact hs1.hasSum.mul_left z
  have hlog : HasSum (fun i => Complex.log (1 - z * g i))
      (-fredholmExp (diagMul g) z - z * hsTraceDiag (diagMul g)) :=
    ((hasSum_exponent_diagMul g hs2 r hr z hz).sub htr).congr_fun (fun i => by ring)
  have hprod := hlog.cexp
  have hfun : (Complex.exp ∘ fun i => Complex.log (1 - z * g i)) = fun i => 1 - z * g i := by
    funext i; simp only [Function.comp]; exact Complex.exp_log (hne i)
  rw [hfun] at hprod
  have hval : Complex.exp (-fredholmExp (diagMul g) z - z * hsTraceDiag (diagMul g))
      = fredholmDet1 (diagMul g) z := by rw [fredholmDet1, fredholmDet, ← Complex.exp_add]; ring_nf
  rwa [hval] at hprod

/-- The trace-class determinant as the bare product `det₁(1 − z·diagMul g) = ∏ᵢ (1 − z·gᵢ)`. -/
theorem fredholmDet1_tprod_diagMul (g : ι → ℂ) (hs2 : Summable (fun i => ‖g i‖ ^ 2))
    (hs1 : Summable g) (r : ℝ) (hr : r * hsNorm (diagMul g) < 1) (z : ℂ)
    (hz : z ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet1 (diagMul g) z = ∏' i, (1 - z * g i) :=
  (hasProd_fredholmDet1_diagMul g hs2 hs1 r hr z hz).tprod_eq.symm

/-- **The Riemann zeta function is the reciprocal of a trace-class Fredholm determinant.**
For `Re s > 1`, `det₁(1 − diagMul(p ↦ p^{−s}))⁻¹ = riemannZeta s`, where `diagMul(p ↦ p^{−s})` is the
finite-energy diagonal Hilbert–Schmidt operator on `ℓ²(primes)` with eigenvalues `{p^{−s}}`.  So `ζ(s)` is
the L-function realized as (the reciprocal of) the characteristic determinant of an explicit operator: the
determinant is the inverse Euler product `∏ₚ (1 − p^{−s})` and mathlib's Euler product
(`riemannZeta_eulerProduct_hasProd`) is its inverse `∏ₚ (1 − p^{−s})⁻¹ = ζ(s)`.  Requires the disk of
convergence `‖diagMul(p ↦ p^{−s})‖_HS < 1` (which holds once `Re s` is large enough). -/
theorem fredholmDet1_eq_inv_riemannZeta (s : ℂ) (hs : 1 < s.re) (r : ℝ)
    (hr : r * hsNorm (diagMul (fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s))) < 1)
    (hz1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet1 (diagMul (fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s))) 1 = (riemannZeta s)⁻¹ := by
  set g : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-s) with hg
  have hnorm : ∀ p : Nat.Primes, ‖g p‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
    intro p
    show ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re)
    rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast p.2.pos), neg_re]
  have hgp_lt : ∀ p : Nat.Primes, ‖g p‖ < 1 := fun p => by
    rw [hnorm]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
  have hsn : Summable (fun p : Nat.Primes => ‖g p‖) := by
    simp_rw [hnorm]; rw [Nat.Primes.summable_rpow]; linarith
  have hs1 : Summable g := Summable.of_norm hsn
  have hs2 : Summable (fun p : Nat.Primes => ‖g p‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun p => by positivity)
      (fun p => by rw [sq]; exact mul_le_of_le_one_right (norm_nonneg _) (hgp_lt p).le) hsn
  have hne : ∀ p : Nat.Primes, (1 : ℂ) - g p ≠ 0 := fun p => by
    intro h
    have hlt := hgp_lt p
    rw [show g p = 1 from by linear_combination -h, norm_one] at hlt
    exact lt_irrefl 1 hlt
  have hHP1 := hasProd_fredholmDet1_diagMul g hs2 hs1 r hr 1 hz1
  have hHP2 := riemannZeta_eulerProduct_hasProd hs
  have hdz : fredholmDet1 (diagMul g) 1 * riemannZeta s = 1 :=
    calc fredholmDet1 (diagMul g) 1 * riemannZeta s
        = (∏' p : Nat.Primes, (1 - g p)) * ∏' p : Nat.Primes, (1 - g p)⁻¹ := by
          rw [← hHP1.tprod_eq, ← hHP2.tprod_eq]; simp [hg, one_mul]
      _ = ∏' p : Nat.Primes, ((1 - g p) * (1 - g p)⁻¹) :=
          (Multipliable.tprod_mul (by simpa [one_mul] using hHP1.multipliable)
            (by simpa [hg] using hHP2.multipliable)).symm
      _ = ∏' _p : Nat.Primes, (1 : ℂ) := by
          apply tprod_congr; intro p; exact mul_inv_cancel₀ (hne p)
      _ = 1 := tprod_one
  rw [inv_eq_one_div, eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)]
  exact hdz

end HilbertSchmidt
