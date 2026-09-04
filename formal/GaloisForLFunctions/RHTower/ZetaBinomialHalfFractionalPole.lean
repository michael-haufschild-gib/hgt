import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfSelbergDelangeFactorization
import GaloisForLFunctions.RHTower.MobiusFixedCurrentVonMangoldt

/-!
# The fractional pole of the positive zeta half

The Dirichlet series `B(s)` of `zetaBinomialHalf` is the positive real square root of `ζ(s)`
on the real half-line `s > 1`.  Consequently

`sqrt(t) B(1+t) → 1` as `t → 0+`.

This is the exact order-`1/2` singular input for fractional Wiener--Ikehara.  Its proof uses only
absolute convergence, the already formalized coefficient identity `b * b = ζ`, positivity, and
the residue of the Riemann zeta function at one.
-/

open ArithmeticFunction Complex Filter Topology Set
open scoped BigOperators ArithmeticFunction.zeta ComplexOrder

noncomputable section

namespace RHTower

/-- On `Re s > 1`, the square of the zeta-half Dirichlet series is the Riemann zeta function. -/
theorem LSeries_zetaBinomialHalf_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries zetaBinomialHalf s * LSeries zetaBinomialHalf s = riemannZeta s := by
  have hb : LSeriesSummable zetaBinomialHalf s := LSeriesSummable_zetaBinomialHalf hs
  calc
    LSeries zetaBinomialHalf s * LSeries zetaBinomialHalf s =
        LSeries (fun n ↦ (zetaBinomialHalf * zetaBinomialHalf) n) s :=
      (ArithmeticFunction.LSeries_mul' hb hb).symm
    _ = LSeries (fun n ↦
        (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) n)) s := by
      congr 1
      funext n
      rw [zetaBinomialHalf_mul_self]
    _ = riemannZeta s := ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs

/-- The real-axis zeta-half `L`-value is nonnegative whenever its defining `tsum` is read. -/
theorem LSeries_zetaBinomialHalf_nonneg {x : ℝ} :
    0 ≤ LSeries zetaBinomialHalf (x : ℂ) := by
  rw [LSeries]
  apply tsum_nonneg
  intro n
  exact LSeries.term_nonneg (zetaBinomialHalf_apply_nonneg_complex n) x

/-- The normalized positive zeta half has the order-`1/2` pole constant one. -/
theorem tendsto_sqrt_mul_LSeries_zetaBinomialHalf_one_add :
    Tendsto
      (fun t : ℝ ↦ ((Real.sqrt t : ℝ) : ℂ) *
        LSeries zetaBinomialHalf ((1 + t : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 1) := by
  let x : ℝ → ℝ := fun t ↦
    Real.sqrt t * (LSeries zetaBinomialHalf ((1 + t : ℝ) : ℂ)).re
  have hsquare : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      x t ^ 2 =
        (((t : ℂ) * riemannZeta ((1 + t : ℝ) : ℂ))).re := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    have hs : 1 < (((1 + t : ℝ) : ℂ)).re := by
      simp
      linarith
    have hBnonneg := LSeries_zetaBinomialHalf_nonneg (x := 1 + t)
    have hBim : (LSeries zetaBinomialHalf ((1 + t : ℝ) : ℂ)).im = 0 :=
      (Complex.nonneg_iff.mp hBnonneg).2.symm
    have hsq := LSeries_zetaBinomialHalf_sq hs
    rw [Complex.ext_iff] at hsq
    have hsqre := hsq.1
    simp only [Complex.mul_re] at hsqre
    rw [hBim] at hsqre
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hsqre ⊢
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt ht0.le]
    nlinarith
  have hresC := tendsto_mul_riemannZeta_one_add_mul (c := 1) (by norm_num)
  have hres : Tendsto
      (fun t : ℝ ↦ (((t : ℂ) *
        riemannZeta ((1 + t : ℝ) : ℂ))).re)
      (𝓝[>] 0) (𝓝 1) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hresC
    simpa [Function.comp_def] using hre
  have hsqrtRes : Tendsto
      (fun t : ℝ ↦ Real.sqrt
        ((((t : ℂ) * riemannZeta ((1 + t : ℝ) : ℂ))).re))
      (𝓝[>] 0) (𝓝 1) := by
    simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hres
  have hx : Tendsto x (𝓝[>] 0) (𝓝 1) := by
    apply hsqrtRes.congr'
    filter_upwards [self_mem_nhdsWithin, hsquare] with t ht hsq
    have ht0 : 0 < t := ht
    have hs : 1 < (((1 + t : ℝ) : ℂ)).re := by
      simp
      linarith
    have hx0 : 0 ≤ x t := mul_nonneg (Real.sqrt_nonneg _)
      (Complex.nonneg_iff.mp (LSeries_zetaBinomialHalf_nonneg (x := 1 + t))).1
    rw [← hsq, Real.sqrt_sq hx0]
  have hxC : Tendsto (fun t ↦ ((x t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    change Tendsto (Complex.ofReal ∘ x) (𝓝[>] 0) (𝓝 (Complex.ofReal 1))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hx
  apply hxC.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have hs : 1 < (((1 + t : ℝ) : ℂ)).re := by
    simp
    linarith
  have hBim : (LSeries zetaBinomialHalf ((1 + t : ℝ) : ℂ)).im = 0 :=
    (Complex.nonneg_iff.mp (LSeries_zetaBinomialHalf_nonneg (x := 1 + t))).2.symm
  apply Complex.ext
  · simp [x]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hBim, mul_zero]

end RHTower
