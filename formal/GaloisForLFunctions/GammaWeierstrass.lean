/-
# The Gamma Weierstrass product, and the archimedean factor as a Fredholm determinant

This file builds the **Weierstrass product** for the reciprocal Gamma function,

  `1/Γ(s) = s · e^{γ s} · ∏_{k≥1} (1 + s/k) · e^{-s/k}`,

where `γ` is the Euler–Mascheroni constant.  Mathlib provides the Gauss/Euler limit
`Complex.GammaSeq s n → Γ(s)` with `GammaSeq s n = n^s · n! / ∏_{j=0}^{n}(s+j)`, and the limit
`harmonic n − log n → γ`, but not the Weierstrass product.  The bridge is the finite identity

  `(GammaSeq s n)⁻¹ = s · e^{s(H_n − log n)} · ∏_{k=0}^{n-1} (1 + s/(k+1)) e^{-s/(k+1)}`,

whose `n → ∞` limit turns the Gauss product into the Weierstrass product: the harmonic regulator
`H_n − log n` converges to `γ` and the partial products converge because the regularized factor
`(1 + s/(k+1)) e^{-s/(k+1)} = 1 + O(1/k²)` is multipliable.

The regularized factor is exactly the Hilbert–Carleman factor `(1 − z·gₖ) e^{z·gₖ}` of the diagonal
Hilbert–Schmidt operator with eigenvalues `gₖ = −s/(k+1)` at `z = 1`.  So on the disk of convergence
`‖diagMul(k ↦ −s/(k+1))‖_HS < 1`, the regularized determinant `det₂(1 − diagMul g)` at `z = 1` is the
Weierstrass product, hence the reciprocal `(s · e^{γ s} · Γ(s))⁻¹` of the archimedean factor: the
archimedean `1/Γ` factor realized as the characteristic determinant of an explicit operator, the
archimedean analogue of `ζ(s)⁻¹ = det₁(1 − diagMul(p ↦ p^{−s}))` (`fredholmDet1_eq_inv_riemannZeta`).
-/
import GaloisForLFunctions.FredholmDeterminantZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Summable

open Complex Real Filter Topology Finset
open scoped BigOperators

namespace HilbertSchmidt

/-- The complex cast of the `n`-th harmonic number is the partial sum `∑_{k<n} (k+1)⁻¹`. -/
theorem harmonic_cast_complex (n : ℕ) :
    (harmonic n : ℂ) = ∑ k ∈ Finset.range n, ((k : ℂ) + 1)⁻¹ := by
  rw [harmonic]; push_cast; rfl

/-- The finite product `∏_{k<n} (k+1)` over `ℂ` is `n!`. -/
theorem factorial_cast_prod (n : ℕ) : ∏ k ∈ Finset.range n, ((k : ℂ) + 1) = (n.factorial : ℂ) := by
  rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl

/-- **The finite Gauss–Weierstrass identity.**  The reciprocal of the Gauss approximant `GammaSeq s n`
factors as `s`, the harmonic regulator `e^{s(H_n − log n)}`, and the partial Weierstrass product of the
regularized factors `(1 + s/(k+1)) e^{-s/(k+1)}` over `k < n`.  Holds for every `s` and `n ≥ 1` (both
sides handle the excluded poles by the field's junk convention); proved by reindexing
`∏_{j=0}^{n}(s+j) = s·∏_{k<n}(s+k+1)`, `∏_{k<n}(k+1) = n!`, and collapsing the exponentials against
`n^{-s} = e^{-s log n}`. -/
theorem gammaSeq_inv_weierstrass (s : ℂ) (n : ℕ) (hn : n ≠ 0) :
    (Complex.GammaSeq s n)⁻¹
      = s * Complex.exp (s * (Complex.ofReal ((harmonic n : ℝ) - Real.log n)))
          * ∏ k ∈ Finset.range n, (1 + s / ((k : ℂ) + 1)) * Complex.exp (-(s / ((k : ℂ) + 1))) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hkne : ∀ k : ℕ, ((k : ℂ) + 1) ≠ 0 := fun k => by
    have hp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    intro h; apply hp.ne'; have := congrArg Complex.re h; simpa using this
  set P := ∏ k ∈ Finset.range n, (1 + s / ((k : ℂ) + 1)) * Complex.exp (-(s / ((k : ℂ) + 1))) with hP
  have hexpprod : ∏ k ∈ Finset.range n, Complex.exp (-(s / ((k : ℂ) + 1)))
      = Complex.exp (-(s * (harmonic n : ℂ))) := by
    rw [← Complex.exp_sum]
    congr 1
    have hstep : ∑ k ∈ Finset.range n, -(s / ((k : ℂ) + 1))
        = -(s * ∑ k ∈ Finset.range n, ((k : ℂ) + 1)⁻¹) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro k _; rw [div_eq_mul_inv]
    rw [hstep, ← harmonic_cast_complex]
  have hP2 : P = (∏ k ∈ Finset.range n, (1 + s / ((k : ℂ) + 1)))
      * Complex.exp (-(s * (harmonic n : ℂ))) := by
    rw [hP, Finset.prod_mul_distrib, hexpprod]
  have hprod1 : ∏ k ∈ Finset.range n, (1 + s / ((k : ℂ) + 1))
      = (∏ k ∈ Finset.range n, (s + ((k : ℂ) + 1))) / (n.factorial : ℂ) := by
    rw [← factorial_cast_prod, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl; intro k _
    rw [eq_div_iff (hkne k)]; field_simp; ring
  have hprod2 : (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ)))
      = (∏ k ∈ Finset.range n, (s + ((k : ℂ) + 1))) * s := by
    rw [Finset.prod_range_succ']
    congr 1
    · apply Finset.prod_congr rfl; intro k _; push_cast; ring
    · push_cast; ring
  have hEcomb : Complex.exp (s * (Complex.ofReal ((harmonic n : ℝ) - Real.log n)))
      * Complex.exp (-(s * (harmonic n : ℂ)))
      = Complex.exp (-(s * (Complex.ofReal (Real.log n)))) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hnpow : (n : ℂ) ^ s = Complex.exp (s * (Complex.ofReal (Real.log n))) := by
    rw [Complex.cpow_def_of_ne_zero hnC, Complex.ofReal_log (by positivity)]; push_cast; ring_nf
  rw [Complex.GammaSeq, inv_div, hP2, hprod1]
  rw [show s * Complex.exp (s * (Complex.ofReal ((harmonic n : ℝ) - Real.log n)))
        * ((∏ k ∈ Finset.range n, (s + ((k : ℂ) + 1))) / (n.factorial : ℂ)
            * Complex.exp (-(s * (harmonic n : ℂ))))
      = (s * (∏ k ∈ Finset.range n, (s + ((k : ℂ) + 1))))
          * (Complex.exp (s * (Complex.ofReal ((harmonic n : ℝ) - Real.log n)))
              * Complex.exp (-(s * (harmonic n : ℂ)))) / (n.factorial : ℂ) by ring]
  rw [hEcomb]
  rw [show s * (∏ k ∈ Finset.range n, (s + ((k : ℂ) + 1)))
      = (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) by rw [hprod2]; ring]
  rw [hnpow, Complex.exp_neg]
  field_simp

/-- **The regularized Weierstrass factor is multipliable.**  `∏_{k≥0} (1 + s/(k+1)) e^{-s/(k+1)}`
converges for every `s`, because `(1 + w) e^{-w} − 1 = O(‖w‖²)` and `∑ ‖s/(k+1)‖² < ∞`. -/
theorem multipliable_weierstrassFactor (s : ℂ) :
    Multipliable (fun k : ℕ => (1 + s / ((k : ℂ) + 1)) * Complex.exp (-(s / ((k : ℂ) + 1)))) := by
  have key : (fun k : ℕ => (1 + s / ((k : ℂ) + 1)) * Complex.exp (-(s / ((k : ℂ) + 1))))
      = fun k : ℕ => 1 + ((1 + s / ((k : ℂ) + 1)) * Complex.exp (-(s / ((k : ℂ) + 1))) - 1) := by
    funext k; ring
  rw [key]
  apply multipliable_one_add_of_summable
  apply Summable.of_norm_bounded_eventually_nat
    (g := fun k : ℕ => 3 * ‖s‖ ^ 2 / ((k : ℝ) + 1) ^ 2)
  · have hbase : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
      have h2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      have := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr h2
      simpa using this
    have := hbase.mul_left (3 * ‖s‖ ^ 2)
    apply this.congr; intro k; rw [mul_one_div]
  · filter_upwards [Filter.eventually_ge_atTop (Nat.ceil ‖s‖)] with k hk
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hnorm1 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
      rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hkpos]
    set w := s / ((k : ℂ) + 1) with hw
    have hwn : ‖w‖ = ‖s‖ / ((k : ℝ) + 1) := by rw [hw, norm_div, hnorm1]
    have hwle : ‖w‖ ≤ 1 := by
      rw [hwn, div_le_one hkpos]
      calc ‖s‖ ≤ (Nat.ceil ‖s‖ : ℝ) := Nat.le_ceil _
        _ ≤ (k : ℝ) := by exact_mod_cast hk
        _ ≤ (k : ℝ) + 1 := by linarith
    have hbd : ‖(1 + w) * Complex.exp (-w) - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
      have hnx : ‖(-w)‖ ≤ 1 := by rwa [norm_neg]
      have hdecomp : (1 + w) * Complex.exp (-w) - 1
          = (Complex.exp (-w) - 1 - (-w)) - (-w) * (Complex.exp (-w) - 1) := by ring
      rw [hdecomp]
      calc ‖(Complex.exp (-w) - 1 - (-w)) - (-w) * (Complex.exp (-w) - 1)‖
          ≤ ‖Complex.exp (-w) - 1 - (-w)‖ + ‖(-w) * (Complex.exp (-w) - 1)‖ := norm_sub_le _ _
        _ ≤ ‖(-w)‖ ^ 2 + ‖(-w)‖ * (2 * ‖(-w)‖) := by
            gcongr
            · exact Complex.norm_exp_sub_one_sub_id_le hnx
            · rw [norm_mul]; gcongr; exact Complex.norm_exp_sub_one_le hnx
        _ = 3 * ‖w‖ ^ 2 := by rw [norm_neg]; ring
    rw [norm_norm]; refine hbd.trans ?_; rw [hwn, div_pow]; exact le_of_eq (by ring)

/-- **The Gamma Weierstrass product.**  For `s` off the non-positive integers,

  `1/Γ(s) = s · e^{γ s} · ∏_{k≥0} (1 + s/(k+1)) e^{-s/(k+1)}`  (`= s · e^{γ s} · ∏_{k≥1}(1 + s/k)e^{-s/k}`),

`γ = Real.eulerMascheroniConstant`.  The `n → ∞` limit of the finite identity
`gammaSeq_inv_weierstrass`: `GammaSeq s n → Γ(s)`, `Γ(s) ≠ 0`, `H_n − log n → γ`, and the partial
products converge to the tprod by `multipliable_weierstrassFactor`. -/
theorem Gamma_inv_weierstrass (s : ℂ) (hs : ∀ m : ℕ, s ≠ -↑m) :
    (Complex.Gamma s)⁻¹
      = s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s)
          * ∏' k : ℕ, (1 + s / ((k : ℂ) + 1)) * Complex.exp (-(s / ((k : ℂ) + 1))) := by
  set wf : ℕ → ℂ := fun k => (1 + s / ((k : ℂ) + 1)) * Complex.exp (-(s / ((k : ℂ) + 1))) with hwf
  set W : ℂ := ∏' k, wf k with hW
  have hLHS : Filter.Tendsto (fun n => (Complex.GammaSeq s n)⁻¹) Filter.atTop
      (𝓝 (Complex.Gamma s)⁻¹) := (Complex.GammaSeq_tendsto_Gamma s).inv₀ (Complex.Gamma_ne_zero hs)
  have hExp : Filter.Tendsto
      (fun n : ℕ => Complex.exp (s * (Complex.ofReal ((harmonic n : ℝ) - Real.log n)))) Filter.atTop
      (𝓝 (Complex.exp (s * (Real.eulerMascheroniConstant : ℂ)))) := by
    have hcont : Continuous (fun x : ℝ => Complex.exp (s * (Complex.ofReal x))) := by fun_prop
    exact (hcont.tendsto _).comp tendsto_harmonic_sub_log
  have hProd : Filter.Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n, wf k) Filter.atTop (𝓝 W) :=
    (multipliable_weierstrassFactor s).hasProd.tendsto_prod_nat
  have hRHS : Filter.Tendsto
      (fun n : ℕ => s * Complex.exp (s * (Complex.ofReal ((harmonic n : ℝ) - Real.log n)))
          * ∏ k ∈ Finset.range n, wf k) Filter.atTop
      (𝓝 (s * Complex.exp (s * (Real.eulerMascheroniConstant : ℂ)) * W)) :=
    ((tendsto_const_nhds.mul hExp).mul hProd)
  have heq : ∀ᶠ n in Filter.atTop,
      (fun n => (Complex.GammaSeq s n)⁻¹) n
        = (fun n : ℕ => s * Complex.exp (s * (Complex.ofReal ((harmonic n : ℝ) - Real.log n)))
            * ∏ k ∈ Finset.range n, wf k) n := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact gammaSeq_inv_weierstrass s n (by omega)
  have := tendsto_nhds_unique (hLHS.congr' heq) hRHS
  rw [this, mul_comm s (Real.eulerMascheroniConstant : ℂ)]

/-- **The archimedean factor `(s · e^{γ s} · Γ(s))⁻¹` is a Fredholm determinant.**  On the disk of
convergence `‖diagMul(n ↦ −s/(n+1))‖_HS < 1`, the regularized (Hilbert–Carleman) determinant
`det₂(1 − diagMul g)` at `z = 1` of the diagonal Hilbert–Schmidt operator with eigenvalues `−s/(n+1)`
(`n = 0,1,2,…`, i.e. `−s/k` over `k ≥ 1`) equals the reciprocal of the archimedean Weierstrass factor
`s · e^{γ s} · Γ(s)`.  Its Hilbert–Carleman factors `(1 − z·gₙ) e^{z·gₙ}` at `z = 1` are exactly the
Weierstrass factors `(1 + s/(n+1)) e^{-s/(n+1)}`, so `fredholmDet_tprod_diagMul` identifies the
determinant with the product `Gamma_inv_weierstrass` evaluates.  This is the archimedean analogue of
`ζ(s)⁻¹ = det₁(1 − diagMul(p ↦ p^{−s}))`. -/
theorem fredholmDet_diagMul_eq_inv_gammaFactor (s : ℂ) (hs : ∀ m : ℕ, s ≠ -↑m) (r : ℝ)
    (hr : r * hsNorm (diagMul (fun n : ℕ => -s / ((n : ℂ) + 1))) < 1)
    (hz1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet (diagMul (fun n : ℕ => -s / ((n : ℂ) + 1))) 1
      = (s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) * Complex.Gamma s)⁻¹ := by
  set g : ℕ → ℂ := fun n => -s / ((n : ℂ) + 1) with hg
  have hs2 : Summable (fun i => ‖g i‖ ^ 2) := by
    have hbase : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
      have h2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      have := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr h2
      simpa using this
    have hmul := hbase.mul_left (‖s‖ ^ 2)
    apply hmul.congr; intro k
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hnorm1 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
      rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hkpos]
    simp only [hg]
    rw [show (-s / ((k : ℂ) + 1)) = -(s / ((k : ℂ) + 1)) by ring, norm_neg, norm_div, hnorm1]
    rw [div_pow]; ring
  have hFD : fredholmDet (diagMul g) 1
      = ∏' k : ℕ, (1 + s / ((k : ℂ) + 1)) * Complex.exp (-(s / ((k : ℂ) + 1))) := by
    rw [fredholmDet_tprod_diagMul g hs2 r hr 1 hz1]
    apply tprod_congr; intro k
    simp only [hg]
    rw [show (1 : ℂ) - 1 * (-s / ((k : ℂ) + 1)) = 1 + s / ((k : ℂ) + 1) by ring,
      show (1 : ℂ) * (-s / ((k : ℂ) + 1)) = -(s / ((k : ℂ) + 1)) by ring]
  rw [hFD]
  have hWP := Gamma_inv_weierstrass s hs
  set W : ℂ := ∏' k : ℕ, (1 + s / ((k : ℂ) + 1)) * Complex.exp (-(s / ((k : ℂ) + 1))) with hWdef
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  refine eq_inv_of_mul_eq_one_right ?_
  calc (s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) * Complex.Gamma s) * W
      = Complex.Gamma s * (s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) * W) := by ring
    _ = Complex.Gamma s * (Complex.Gamma s)⁻¹ := by rw [← hWP]
    _ = 1 := mul_inv_cancel₀ hΓ

end HilbertSchmidt
