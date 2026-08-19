import GaloisForLFunctions.HTGeometry.ArchimedeanLowestPowerDominance

/-!
# The bracket ratio of an archimedean quotient

Writing a `K_G`-element as a quotient of polynomials in `G` and dividing numerator and denominator
by their lowest nonzero coefficient leaves a quotient of two brackets `1 + Σ (coefficient)·G^k` with
`k > 0`.  The archimedean product decays exponentially on a vertical line while every coefficient
grows at most polynomially, so both brackets tend to one and so does their ratio.  This is the
analytic content of the lowest-power separation.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The bracket ratio tends to one.** -/
theorem tendsto_bracketRatio_archimedeanProduct {d : ℕ} (lam : Fin d → ℝ)
    (μ : Fin d → ℂ) (hlam : ∀ j, 0 < lam j) {σ : ℝ} (hσ : ∀ j, 0 < lam j * σ + (μ j).re)
    (α : ℝ) (hd : 0 < d) {Nn Nd : ℕ}
    (A : Fin Nn → ℝ → ℂ) (CA : Fin Nn → ℝ) (mA : Fin Nn → ℕ) (ku : Fin Nn → ℕ)
    (hCA : ∀ i, 0 ≤ CA i) (hku : ∀ i, 0 < ku i)
    (hA : ∀ i, ∀ᶠ t : ℝ in atTop, ‖A i t‖ ≤ CA i * t ^ mA i)
    (B : Fin Nd → ℝ → ℂ) (CB : Fin Nd → ℝ) (mB : Fin Nd → ℕ) (kv : Fin Nd → ℕ)
    (hCB : ∀ i, 0 ≤ CB i) (hkv : ∀ i, 0 < kv i)
    (hB : ∀ i, ∀ᶠ t : ℝ in atTop, ‖B i t‖ ≤ CB i * t ^ mB i) :
    Tendsto (fun t : ℝ =>
        (1 + ∑ i : Fin Nn, A i t * (archimedeanProductLine lam μ α σ t) ^ (ku i))
          / (1 + ∑ i : Fin Nd, B i t * (archimedeanProductLine lam μ α σ t) ^ (kv i)))
      atTop (nhds 1) := by
  have hnum := tendsto_one_add_polyGrowth_mul_archimedeanProduct_pow lam μ hlam hσ α hd
    A CA mA ku hCA hku hA
  have hden := tendsto_one_add_polyGrowth_mul_archimedeanProduct_pow lam μ hlam hσ α hd
    B CB mB kv hCB hkv hB
  have hdiv := hnum.div hden one_ne_zero
  simp only [Pi.div_def] at hdiv
  simpa using hdiv

/-- The archimedean product never vanishes on a vertical line in the range of the shifts. -/
theorem archimedeanProductLine_ne_zero {d : ℕ} (lam : Fin d → ℝ) (μ : Fin d → ℂ)
    {σ : ℝ} (hσ : ∀ j, 0 < lam j * σ + (μ j).re) (α t : ℝ) :
    archimedeanProductLine lam μ α σ t ≠ 0 := by
  rw [archimedeanProductLine]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  refine Complex.Gamma_ne_zero fun m hm => ?_
  have hre : ((lam j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ j).re
      = lam j * σ + (μ j).re := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hj := hσ j
  rw [hm] at hre
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith [hre ▸ hj]

/-- **The archimedean monomial valuation, with coefficients of prescribed boundary shape.**  A
`K_G`-element presented as a quotient of polynomials in `G`, normalized by the lowest power of `G`
occurring in numerator and denominator and by the boundary shapes of their coefficients, converges
to the quotient of the coefficient residues.  This is equation `(6)` on a vertical line. -/
theorem tendsto_archimedeanQuotient_valuation {d : ℕ} (lam : Fin d → ℝ)
    (μ : Fin d → ℂ) (hlam : ∀ j, 0 < lam j) {σ : ℝ} (hσ : ∀ j, 0 < lam j * σ + (μ j).re)
    (α : ℝ) (hd : 0 < d) {Nn Nd : ℕ}
    (A : Fin Nn → ℝ → ℂ) (CA : Fin Nn → ℝ) (mA : Fin Nn → ℕ) (ku : Fin Nn → ℕ)
    (hCA : ∀ i, 0 ≤ CA i) (hku : ∀ i, 0 < ku i)
    (hA : ∀ i, ∀ᶠ t : ℝ in atTop, ‖A i t‖ ≤ CA i * t ^ mA i)
    (B : Fin Nd → ℝ → ℂ) (CB : Fin Nd → ℝ) (mB : Fin Nd → ℕ) (kv : Fin Nd → ℕ)
    (hCB : ∀ i, 0 ≤ CB i) (hkv : ∀ i, 0 < kv i)
    (hB : ∀ i, ∀ᶠ t : ℝ in atTop, ‖B i t‖ ≤ CB i * t ^ mB i)
    (a b shapeA shapeB : ℝ → ℂ) {ca cb : ℂ} (hca : ca ≠ 0) (hcb : cb ≠ 0)
    (ha : Tendsto (fun t => a t / shapeA t) atTop (nhds ca))
    (hb : Tendsto (fun t => b t / shapeB t) atTop (nhds cb))
    (u0 v0 : ℕ) :
    Tendsto (fun t : ℝ =>
        ((a t * (1 + ∑ i : Fin Nn, A i t * (archimedeanProductLine lam μ α σ t) ^ (ku i))
              * (archimedeanProductLine lam μ α σ t) ^ u0)
            / (b t * (1 + ∑ i : Fin Nd, B i t * (archimedeanProductLine lam μ α σ t) ^ (kv i))
              * (archimedeanProductLine lam μ α σ t) ^ v0))
          * ((archimedeanProductLine lam μ α σ t) ^ v0 * shapeB t)
          / ((archimedeanProductLine lam μ α σ t) ^ u0 * shapeA t))
      atTop (nhds (ca / cb)) := by
  have hratio := tendsto_bracketRatio_archimedeanProduct lam μ hlam hσ α hd
    A CA mA ku hCA hku hA B CB mB kv hCB hkv hB
  have hden := tendsto_one_add_polyGrowth_mul_archimedeanProduct_pow lam μ hlam hσ α hd
    B CB mB kv hCB hkv hB
  have hcoef : Tendsto (fun t => (a t / shapeA t) / (b t / shapeB t)) atTop (nhds (ca / cb)) :=
    ha.div hb hcb
  have hmul := hcoef.mul hratio
  rw [mul_one] at hmul
  refine Filter.Tendsto.congr' ?_ hmul
  filter_upwards [hden.eventually_ne one_ne_zero, ha.eventually_ne hca,
    hb.eventually_ne hcb] with t hDen hAt hBt
  have hshapeA : shapeA t ≠ 0 := (div_ne_zero_iff.mp hAt).2
  have hshapeB : shapeB t ≠ 0 := (div_ne_zero_iff.mp hBt).2
  have hbt : b t ≠ 0 := (div_ne_zero_iff.mp hBt).1
  have hP : archimedeanProductLine lam μ α σ t ≠ 0 :=
    archimedeanProductLine_ne_zero lam μ hσ α t
  have hPu : (archimedeanProductLine lam μ α σ t) ^ u0 ≠ 0 := pow_ne_zero _ hP
  have hPv : (archimedeanProductLine lam μ α σ t) ^ v0 ≠ 0 := pow_ne_zero _ hP
  field_simp

end

end GaloisForLFunctions.HTGeometry
