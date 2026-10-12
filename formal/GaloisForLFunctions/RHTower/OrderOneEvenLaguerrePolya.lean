import GaloisForLFunctions.RHTower.OrderOneHadamardFactorization
import GaloisForLFunctions.HTGeometry.EvenCanonicalProductLaguerrePolya
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect
import GaloisForLFunctions.RHTower.XiLaguerrePolyaRiemannHypothesis

/-!
# Even real-rooted entire functions of order one are Laguerre–Pólya

**Theorem** (`laguerrePolya_of_even_of_realZeros`). Let `f` be entire and even, with `f(0)` real and
nonzero, an order-one growth envelope `|f(z)| ≤ exp(C(1+|z|)log(2+|z|))`, and only real zeros. Then
`f` is a locally uniform limit of real polynomials with only real zeros.

**Proof.** By the even order-one Hadamard factorization, `f = f(0)·∏_q E₁(z/a_q)` over the zero copies
`a_q`. Take the zero copies in the ball of radius `n`. This finite set is invariant under the
reflection `a ↦ −a`, so `Σ 1/a_q = 0` over it and the partial product is `∏(1 − z/a_q)`, a real
polynomial with real zeros. These sets exhaust the zero copies, and the canonical product converges
locally uniformly along every exhaustion.

**Corollary** (`riemannHypothesis_iff_laguerrePolya_XiC`). RH holds iff `Ξ` is in the
Laguerre–Pólya class, i.e. a locally uniform limit of real-rooted real polynomials.
-/

open Complex Filter Topology Set Polynomial

namespace RHTower.OrderOneHadamard

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.EntireZeroDivisor
  GaloisForLFunctions.CountableDivisor

noncomputable section

variable {f : ℂ → ℂ}

/-- Zero copies lie on zeros. -/
theorem eq_zero_at_zeroCopyPoint (hf : AnalyticOnNhd ℂ f univ) (q : ZeroCopy f) :
    f (zeroCopyPoint f q) = 0 := by
  have hmem := q.1.2
  rw [Function.mem_support, divisor_univ_eq_analyticOrder hf] at hmem
  by_contra hne
  apply hmem
  have h0 : analyticOrderAt f (q.1 : ℂ) = 0 := ((hf _ (mem_univ _)).analyticOrderAt_eq_zero).mpr hne
  rw [h0]
  rfl

/-- Finitely many zero copies in every ball. -/
theorem finite_zeroCopy_norm_le (hf : AnalyticOnNhd ℂ f univ) (r : ℝ) :
    {q : ZeroCopy f | ‖zeroCopyPoint f q‖ ≤ r}.Finite := by
  have h := (finite_zeroSupport_ball hf r).biUnion fun w _ =>
    Set.finite_range (fun i : Fin ((MeromorphicOn.divisor f univ) (w : ℂ)).toNat =>
      (⟨w, i⟩ : ZeroCopy f))
  refine h.subset fun q hq => ?_
  exact Set.mem_biUnion (x := q.1) hq ⟨q.2, rfl⟩

/-- The zero copies in the ball of radius `n`. -/
def zeroCopyBall (hf : AnalyticOnNhd ℂ f univ) (n : ℕ) : Finset (ZeroCopy f) :=
  (finite_zeroCopy_norm_le hf n).toFinset

theorem mem_zeroCopyBall (hf : AnalyticOnNhd ℂ f univ) (n : ℕ) (q : ZeroCopy f) :
    q ∈ zeroCopyBall hf n ↔ ‖zeroCopyPoint f q‖ ≤ n := by
  simp [zeroCopyBall]

theorem tendsto_zeroCopyBall (hf : AnalyticOnNhd ℂ f univ) :
    Tendsto (zeroCopyBall hf) atTop atTop := by
  refine Filter.tendsto_atTop_finset_of_monotone (fun m n hmn q hq => ?_) fun q => ?_
  · rw [mem_zeroCopyBall] at hq ⊢
    exact hq.trans (by exact_mod_cast hmn)
  · obtain ⟨n, hn⟩ := exists_nat_ge ‖zeroCopyPoint f q‖
    exact ⟨n, (mem_zeroCopyBall hf n q).mpr hn⟩

/-- On a reflection-invariant finite set of zero copies of an even function the reciprocal zeros
sum to zero. -/
theorem sum_inv_zeroCopyBall_eq_zero (hf : AnalyticOnNhd ℂ f univ) (heven : ∀ z, f (-z) = f z)
    (n : ℕ) : ∑ q ∈ zeroCopyBall hf n, (zeroCopyPoint f q)⁻¹ = 0 := by
  set R := zeroCopyReflect hf heven
  have h : ∑ q ∈ zeroCopyBall hf n, (zeroCopyPoint f q)⁻¹ =
      ∑ q ∈ zeroCopyBall hf n, -(zeroCopyPoint f q)⁻¹ := by
    refine Finset.sum_equiv R (fun q => ?_) fun q _ => ?_
    · rw [mem_zeroCopyBall, mem_zeroCopyBall, zeroCopyPoint_reflect, norm_neg]
    · rw [zeroCopyPoint_reflect, inv_neg, neg_neg]
  rw [Finset.sum_neg_distrib] at h
  have h2 : (2 : ℂ) * ∑ q ∈ zeroCopyBall hf n, (zeroCopyPoint f q)⁻¹ = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The real polynomial `∏_{|a_q| ≤ n} (1 − X/a_q)`. -/
def zeroCopyBallPoly (hf : AnalyticOnNhd ℂ f univ) (n : ℕ) : ℝ[X] :=
  ∏ q ∈ zeroCopyBall hf n, (1 - C ((zeroCopyPoint f q).re)⁻¹ * X)

theorem splits_zeroCopyBallPoly (hf : AnalyticOnNhd ℂ f univ) (n : ℕ) :
    (zeroCopyBallPoly hf n).Splits :=
  Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb)
    (Polynomial.Splits.of_natDegree_le_one (by simp)) fun q _ => splits_one_sub_C_mul_X _

/-- On a ball of zero copies, the genus-one partial product is the real-rooted polynomial. -/
theorem prod_weierstrassE1_eq_polyEvalC (hf : AnalyticOnNhd ℂ f univ) (heven : ∀ z, f (-z) = f z)
    (hreal : ∀ z, f z = 0 → z.im = 0) (n : ℕ) (z : ℂ) :
    ∏ q ∈ zeroCopyBall hf n, weierstrassE1 (z / zeroCopyPoint f q) =
      polyEvalC (zeroCopyBallPoly hf n) z := by
  have hre : ∀ q : ZeroCopy f, ((zeroCopyPoint f q).re : ℂ) = zeroCopyPoint f q := fun q =>
    Complex.ext rfl (by rw [Complex.ofReal_im, hreal _ (eq_zero_at_zeroCopyPoint hf q)])
  simp only [weierstrassE1, Finset.prod_mul_distrib]
  rw [← Complex.exp_sum]
  have hsum : ∑ q ∈ zeroCopyBall hf n, z / zeroCopyPoint f q = 0 := by
    simp only [div_eq_mul_inv]
    rw [← Finset.mul_sum, sum_inv_zeroCopyBall_eq_zero hf heven n, mul_zero]
  rw [hsum, Complex.exp_zero, mul_one, zeroCopyBallPoly, polyEvalC, map_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  simp only [map_sub, map_one, map_mul, aeval_C, aeval_X, Complex.coe_algebraMap,
    Complex.ofReal_inv, hre q]
  ring

/-- **Even real-rooted entire functions of order one are Laguerre–Pólya.** -/
theorem laguerrePolya_of_even_of_realZeros {K : ℝ} (hK : 0 ≤ K)
    (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0) (hf0re : (f 0).im = 0)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤) (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hreal : ∀ z, f z = 0 → z.im = 0) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya f := by
  have hsum := summable_inv_sq_zeroCopyPoint hK hf hf0 hbound
  have hane := zeroCopyPoint_ne_zero hf hf0
  have hfac := eq_const_mul_hadamardProduct_of_even hK hf hf0 hford heven hbound
  have hprod := canonicalProductE1Indexed_hasProdLocallyUniformlyOn (zeroCopyPoint f) hane hsum
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hprod
  have hseq : TendstoLocallyUniformly
      (fun n z => ∏ q ∈ zeroCopyBall hf n, weierstrassE1 (z / zeroCopyPoint f q))
      (hadamardProduct f) atTop := by
    rw [← tendstoLocallyUniformlyOn_univ]
    intro u hu x hx
    obtain ⟨t, ht, hev⟩ := hprod u hu x hx
    exact ⟨t, ht, (tendsto_zeroCopyBall hf).eventually hev⟩
  have hc : ((f 0).re : ℂ) = f 0 := Complex.ext rfl (by rw [Complex.ofReal_im, hf0re])
  refine ⟨fun n => C (f 0).re * zeroCopyBallPoly hf n, fun n =>
    (Polynomial.Splits.C _).mul (splits_zeroCopyBallPoly hf n), ?_⟩
  have hmul : TendstoLocallyUniformly
      (fun n z => f 0 * ∏ q ∈ zeroCopyBall hf n, weierstrassE1 (z / zeroCopyPoint f q))
      (fun z => f 0 * hadamardProduct f z) atTop := by
    rw [Metric.tendstoLocallyUniformly_iff] at hseq ⊢
    intro ε hε x
    obtain ⟨t, ht, hev⟩ := hseq (ε / (‖f 0‖ + 1)) (by positivity) x
    refine ⟨t, ht, ?_⟩
    filter_upwards [hev] with n hn y hy
    have h1 := hn y hy
    rw [dist_eq_norm] at h1 ⊢
    rw [← mul_sub, norm_mul]
    calc ‖f 0‖ * ‖hadamardProduct f y - ∏ q ∈ zeroCopyBall hf n,
          weierstrassE1 (y / zeroCopyPoint f q)‖ ≤ ‖f 0‖ * (ε / (‖f 0‖ + 1)) :=
          mul_le_mul_of_nonneg_left h1.le (norm_nonneg _)
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  refine (hmul.congr fun n z => ?_).congr_right fun z => (hfac z).symm
  rw [prod_weierstrassE1_eq_polyEvalC hf heven hreal]
  simp only [polyEvalC, map_mul, aeval_C, Complex.coe_algebraMap]
  rw [hc]

end

end RHTower.OrderOneHadamard

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- **RH ⟺ `Ξ` is Laguerre–Pólya.** -/
theorem riemannHypothesis_iff_laguerrePolya_XiC :
    RiemannHypothesis ↔ GaloisForLFunctions.HTGeometry.LaguerrePolya XiC := by
  refine ⟨fun hRH => ?_, riemannHypothesis_of_laguerrePolya_XiC⟩
  obtain ⟨C, hC, hbound⟩ := XiC_order
  have hf : AnalyticOnNhd ℂ XiC Set.univ := XiC_analytic
  have hX0re : (XiC 0).im = 0 := by
    have := XiC_ofReal 0
    rw [Complex.ofReal_zero] at this
    rw [this, Complex.ofReal_im]
  refine OrderOneHadamard.laguerrePolya_of_even_of_realZeros hC.le hf XiC_zero_ne hX0re
    XiC_order_ne_top (fun z => ?_) hbound (riemannHypothesis_iff_XiC_zeros_real.mp hRH)
  change xi (1 / 2 + (-z) * Complex.I) = xi (1 / 2 + z * Complex.I)
  rw [show (1 : ℂ) / 2 + (-z) * Complex.I = 1 - (1 / 2 + z * Complex.I) by ring]
  exact xi_one_sub _

end RHTower
