import GaloisForLFunctions.FiniteFreeProbability.BulkBlindness
import GaloisForLFunctions.RHTower.ThetaHalfLinePortOrientation
import GaloisForLFunctions.RHTower.OrderOneHadamardFactorization
import GaloisForLFunctions.RHTower.XiTiltRayGrowth

/-!
# The half transform of `Φ` is not a Hermite–Biehler half of `Ξ`

Let `K(w) = ∫₀^∞ Φ(u) e^{wu} du`, so that `Ξ(u) = K(iu) + K(−iu)`, and let
`E_d(x) = ∫₀^∞ Φ(v)(x + iv)^d dv`, so that `R_d(Ξ) = 2 Re E_d` on the real axis.

**Theorem.** `K` has infinitely many zeros, and all of them lie in `Re w > 0`. Consequently, for every `M` and
all large `d`, `E_d` has at least `M` roots in the open upper half-plane.

So the natural splitting is not Hermite–Biehler: the roots of `E_d` are not all on one side, and the winding of
`E_d` cannot produce every real root of `R_d(Ξ)`. The almost-all statement (R38) is what winding can give.

The zeros in `Re w ≤ 0` are excluded by the positivity `Re(w K(−w)) > 0` in the corpus. If there were
finitely many zeros, the Hadamard factorization at order one would make `K` of exponential type on the real
axis, while `K(σ) + K(−σ) = ξ(1/2 + σ)` grows faster than any exponential.
-/

open Polynomial Filter Topology Complex Metric MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn
open GaloisForLFunctions.EntireZeroDivisor

namespace FiniteFreeProbability

noncomputable section

theorem thetaHalfLaplace_eq_kernel (w : ℂ) :
    thetaHalfLaplace w = ∫ u in Set.Ioi (0 : ℝ), (riemannKernelReal u : ℂ) * Complex.exp (w * u) := by
  rw [thetaHalfLaplace, thetaHalfLaplaceTail]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [thetaCuspFullSource_eq_riemannKernelReal, mul_comm]

/-- `|K(w)| ≤ ξ(1/2 + r)` for `Re w ≤ r`. -/
theorem norm_thetaHalfLaplace_le {w : ℂ} {r : ℝ} (hr : w.re ≤ r) :
    ‖thetaHalfLaplace w‖ ≤ xiMoment (1 / 2 + r) 0 := by
  have hE := hyperbolicKernel_riemann.integrable_exp r
  have hpt : ∀ u ∈ Set.Ioi (0 : ℝ), ‖(riemannKernelReal u : ℂ) * Complex.exp (w * u)‖ ≤
      riemannKernelReal u * Real.exp (r * u) := fun u hu => by
    have hu0 : (0 : ℝ) < u := hu
    have hΦ := riemannKernel_superExp.nonneg u
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΦ, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hΦ
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_right hr hu0.le
  have hbound := norm_integral_le_of_norm_le (μ := volume.restrict (Set.Ioi (0 : ℝ))) hE.restrict
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpt))
  rw [thetaHalfLaplace_eq_kernel]
  refine hbound.trans ?_
  have hmom : xiMoment (1 / 2 + r) 0 = ∫ v, riemannKernelReal v * Real.exp (r * v) := by
    rw [xiMoment]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp
  rw [hmom]
  exact setIntegral_le_integral hE (Eventually.of_forall fun v =>
    mul_nonneg (riemannKernel_superExp.nonneg v) (Real.exp_pos _).le)

/-- The order-one envelope of `K`. -/
theorem exists_order_one_bound_thetaHalfLaplace :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖thetaHalfLaplace z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  set K₀ := Real.log (xiMoment (1 / 2 + 1) 0)
  refine ⟨2 * |K₀| + 7, by positivity, fun z => ?_⟩
  set r := 1 + ‖z‖
  have hr1 : 1 ≤ r := by simp only [r]; linarith [norm_nonneg z]
  have hre : z.re ≤ r := by
    have := Complex.re_le_norm z
    simp only [r]
    linarith
  have h1 := norm_thetaHalfLaplace_le hre
  have hpos := xiMoment_zero_pos (1 / 2 + r)
  have hcap : Real.log (xiMoment (1 / 2 + r) 0) ≤ K₀ + r * (3 + Real.log r / 2) := log_xiMoment_le hr1
  set L := Real.log (2 + ‖z‖)
  have hL : 1 / 2 ≤ L := by
    have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
    have := Real.log_two_gt_d9
    linarith
  have hlogr : Real.log r ≤ L := Real.log_le_log (by linarith) (by simp only [r]; linarith)
  refine h1.trans ?_
  rw [← Real.exp_log hpos]
  refine Real.exp_le_exp.2 (hcap.trans ?_)
  have hrL : 1 / 2 ≤ r * L := by nlinarith
  have hK : K₀ ≤ |K₀| * (2 * (r * L)) := by
    have := le_abs_self K₀
    have h0 := abs_nonneg K₀
    nlinarith
  have h3 : r * (3 + Real.log r / 2) ≤ r * (3 + L / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h4 : r * (3 + L / 2) ≤ 7 * (r * L) := by nlinarith
  calc K₀ + r * (3 + Real.log r / 2) ≤ |K₀| * (2 * (r * L)) + 7 * (r * L) := by linarith
    _ = _ := by ring

theorem analyticOnNhd_thetaHalfLaplace : AnalyticOnNhd ℂ thetaHalfLaplace Set.univ :=
  differentiable_thetaHalfLaplace.differentiableOn.analyticOnNhd isOpen_univ

theorem thetaHalfLaplace_zero_ne : thetaHalfLaplace 0 ≠ 0 := by
  have h := thetaHalfLaplace_neg_ne_zero_of_nonneg (w := 0) (by simp)
  simpa using h

/-- Every zero of `K` lies in `Re w > 0`. -/
theorem re_pos_of_thetaHalfLaplace_eq_zero {w : ℂ} (hw : thetaHalfLaplace w = 0) : 0 < w.re := by
  by_contra h
  push Not at h
  have := thetaHalfLaplace_neg_ne_zero_of_nonneg (w := -w) (by simpa using h)
  rw [neg_neg] at this
  exact this hw

theorem analyticOrderAt_thetaHalfLaplace_ne_top (z : ℂ) : analyticOrderAt thetaHalfLaplace z ≠ ⊤ := by
  intro h
  rw [analyticOrderAt_eq_top] at h
  have hzero := analyticOnNhd_thetaHalfLaplace.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) h
  exact thetaHalfLaplace_zero_ne (hzero (Set.mem_univ 0))

theorem norm_weierstrassE1_le (t : ℂ) : ‖weierstrassE1 t‖ ≤ Real.exp (2 * ‖t‖) := by
  rw [weierstrassE1, norm_mul]
  have h1 : ‖1 - t‖ ≤ Real.exp ‖t‖ := by
    have := norm_sub_le (1 : ℂ) t
    rw [norm_one] at this
    linarith [Real.add_one_le_exp ‖t‖]
  have h2 := Complex.norm_exp_le_exp_norm t
  rw [two_mul, Real.exp_add]
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le

/-- **`K` has infinitely many zeros.** -/
theorem thetaHalfLaplace_zeros_infinite : {w : ℂ | thetaHalfLaplace w = 0}.Infinite := by
  intro hfin
  have hf := analyticOnNhd_thetaHalfLaplace
  have hf0 := thetaHalfLaplace_zero_ne
  obtain ⟨C, hC, hbound⟩ := exists_order_one_bound_thetaHalfLaplace
  obtain ⟨a, b, hfac⟩ := OrderOneHadamard.exists_expAffine_mul_hadamardProduct hC hf hf0
    analyticOrderAt_thetaHalfLaplace_ne_top hbound
  -- finitely many multiplicity copies
  obtain ⟨r₀, hr₀⟩ := hfin.isBounded.subset_closedBall (0 : ℂ)
  have hzero : ∀ p : ZeroCopy thetaHalfLaplace, zeroCopyPoint thetaHalfLaplace p ∈
      {w : ℂ | thetaHalfLaplace w = 0} := fun p => by
    by_contra hne
    have hne' : thetaHalfLaplace (p.1 : ℂ) ≠ 0 := hne
    have h2 : (MeromorphicOn.divisor thetaHalfLaplace Set.univ) ((p.1 : ℂ)) ≠ 0 := p.1.2
    apply h2
    rw [divisor_univ_eq_analyticOrder hf,
      (hf (p.1 : ℂ) (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hne']
    simp
  have hfinite : Finite (ZeroCopy thetaHalfLaplace) := by
    rw [← Set.finite_univ_iff]
    refine (locallyFinite_zeroCopyPoint hf r₀).subset fun p _ => ?_
    have := hr₀ (hzero p)
    simpa [mem_closedBall, dist_eq_norm] using this
  haveI := Fintype.ofFinite (ZeroCopy thetaHalfLaplace)
  set S : ℝ := ∑ q : ZeroCopy thetaHalfLaplace, 1 / ‖zeroCopyPoint thetaHalfLaplace q‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun q _ => by positivity
  -- exponential type on the positive axis
  have hH : ∀ σ : ℝ, 0 ≤ σ → ‖OrderOneHadamard.hadamardProduct thetaHalfLaplace (σ : ℂ)‖ ≤
      Real.exp (2 * S * σ) := fun σ hσ => by
    rw [OrderOneHadamard.hadamardProduct, canonicalProductE1Indexed, tprod_fintype, norm_prod,
      show 2 * S * σ = ∑ q : ZeroCopy thetaHalfLaplace,
        2 * ‖(σ : ℂ) / zeroCopyPoint thetaHalfLaplace q‖ by
        simp only [S, norm_div, Complex.norm_real, Real.norm_of_nonneg hσ, Finset.mul_sum,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring, Real.exp_sum]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun q _ => norm_weierstrassE1_le _
  set c := ‖a‖ + 2 * S
  have hc : 0 ≤ c := by positivity
  have hK : ∀ σ : ℝ, 0 ≤ σ → ‖thetaHalfLaplace (σ : ℂ)‖ ≤ Real.exp (c * σ + ‖b‖) := fun σ hσ => by
    rw [hfac (σ : ℂ), norm_mul]
    have h1 : ‖Complex.exp (a * σ + b)‖ ≤ Real.exp (‖a‖ * σ + ‖b‖) := by
      refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ]
    calc _ ≤ Real.exp (‖a‖ * σ + ‖b‖) * Real.exp (2 * S * σ) :=
          mul_le_mul h1 (hH σ hσ) (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by
          rw [← Real.exp_add]
          congr 1
          simp only [c]
          ring
  set D₀ := xiMoment (1 / 2 + 0) 0
  have hD₀ : 0 < D₀ := xiMoment_zero_pos _
  obtain ⟨s, hs1, hs, hgrow⟩ := xi_superlinear_ray_above (c + Real.log (1 + D₀) + ‖b‖) 1
  set σ := s - 1 / 2
  have hσ : 0 ≤ σ := by simp only [σ]; linarith
  have hxi : xi (s : ℂ) = thetaHalfLaplace (σ : ℂ) + thetaHalfLaplace (-(σ : ℂ)) := by
    rw [thetaHalfLaplace_add_neg, XiC, ← xi_one_sub]
    congr 1
    simp only [σ]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hneg : ‖thetaHalfLaplace (-(σ : ℂ))‖ ≤ D₀ := norm_thetaHalfLaplace_le (by simpa using hσ)
  have hexp1 : 1 ≤ Real.exp (c * σ + ‖b‖) := Real.one_le_exp (by positivity)
  have hnorm : ‖xi (s : ℂ)‖ ≤ (1 + D₀) * Real.exp (c * σ + ‖b‖) := by
    rw [hxi]
    refine (norm_add_le _ _).trans ?_
    nlinarith [hK σ hσ]
  have hxipos : 0 < ‖xi (s : ℂ)‖ := norm_pos_iff.2 (xi_ne_zero_of_real s)
  have hlog := Real.log_le_log hxipos hnorm
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hlog1 : 0 ≤ Real.log (1 + D₀) := Real.log_nonneg (by linarith)
  have hσs : σ ≤ s := by simp only [σ]; linarith
  have hb := norm_nonneg b
  nlinarith [mul_le_mul_of_nonneg_left hσs hc, mul_le_mul_of_nonneg_left hs hlog1,
    mul_le_mul_of_nonneg_left hs hb]

/-! ## The Taylor coefficients of the half transform -/

variable {g : ℝ → ℝ}

theorem HyperbolicKernel.integrable_mul_exp_abs (hg : HyperbolicKernel g) (y : ℝ) :
    Integrable fun v : ℝ => g v * Real.exp (y * |v|) := by
  refine (riemannKernel_superExp.integrable_mul_exp y).mono
    ((hg.continuous.mul (by fun_prop))).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hg.nonneg v),
    abs_of_nonneg (riemannKernel_superExp.nonneg v)]
  exact mul_le_mul_of_nonneg_right (hg.le_kernel v) (abs_nonneg _)

/-- The Taylor coefficients `i^k c⁺_k/k!` of `u ↦ ∫₀^∞ g(v) e^{iuv} dv`. -/
def halfTaylorCoeff (g : ℝ → ℝ) (k : ℕ) : ℂ := I ^ k * (halfMoment g k : ℂ) / (k.factorial : ℂ)

theorem tsum_pow_div_factorial_real (x : ℝ) :
    ∑' k : ℕ, x ^ k / (k.factorial : ℝ) = Real.exp x := by
  rw [Real.exp_eq_exp_ℝ]
  exact (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq

theorem hasSum_pow_div_factorial_complex (z : ℂ) :
    HasSum (fun k : ℕ => z ^ k / (k.factorial : ℂ)) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

/-- The `k`-th term of the exponential series under the half-line integral. -/
def halfTerm (g : ℝ → ℝ) (u : ℂ) (k : ℕ) (v : ℝ) : ℂ :=
  (g v : ℂ) * ((I * u * v) ^ k / (k.factorial : ℂ))

theorem halfTerm_eq (g : ℝ → ℝ) (u : ℂ) (k : ℕ) (v : ℝ) :
    halfTerm g u k v = (I ^ k * u ^ k / (k.factorial : ℂ)) * ((g v * v ^ k : ℝ) : ℂ) := by
  rw [halfTerm, mul_pow, mul_pow]
  push_cast
  ring

theorem HyperbolicKernel.integrable_halfTerm (hg : HyperbolicKernel g) (u : ℂ) (k : ℕ) :
    Integrable (halfTerm g u k) := by
  rw [show halfTerm g u k = fun v => (I ^ k * u ^ k / (k.factorial : ℂ)) * ((g v * v ^ k : ℝ) : ℂ) from
    funext (halfTerm_eq g u k)]
  exact (hg.integrable_ofReal_pow k).const_mul _

theorem HyperbolicKernel.norm_halfTerm (hg : HyperbolicKernel g) (u : ℂ) (k : ℕ) (v : ℝ) :
    ‖halfTerm g u k v‖ = g v * ((‖u‖ * |v|) ^ k / (k.factorial : ℝ)) := by
  rw [halfTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg.nonneg v), norm_div, norm_pow,
    norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_natCast]

theorem HyperbolicKernel.integrable_tsum_halfBound (hg : HyperbolicKernel g) (u : ℂ) :
    Integrable fun v : ℝ => ∑' k : ℕ, g v * ((‖u‖ * |v|) ^ k / (k.factorial : ℝ)) := by
  refine (hg.integrable_mul_exp_abs ‖u‖).congr (Eventually.of_forall fun v => ?_)
  show g v * Real.exp (‖u‖ * |v|) = ∑' k : ℕ, g v * ((‖u‖ * |v|) ^ k / (k.factorial : ℝ))
  rw [tsum_mul_left, tsum_pow_div_factorial_real]

theorem setIntegral_halfTerm (u : ℂ) (k : ℕ) :
    ∫ v in Set.Ioi (0 : ℝ), halfTerm g u k v = halfTaylorCoeff g k * u ^ k := by
  have h : ∀ v, halfTerm g u k v = (I ^ k * u ^ k / (k.factorial : ℂ)) * ((g v * v ^ k : ℝ) : ℂ) :=
    halfTerm_eq g u k
  simp only [h]
  rw [integral_const_mul, integral_complex_ofReal, halfTaylorCoeff, halfMoment]
  ring

theorem HyperbolicKernel.hasSum_halfTaylorCoeff (hg : HyperbolicKernel g) (u : ℂ) :
    HasSum (fun k => halfTaylorCoeff g k * u ^ k)
      (∫ v in Set.Ioi (0 : ℝ), (g v : ℂ) * Complex.exp (I * u * v)) := by
  have h := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := halfTerm g u) (f := fun v : ℝ => (g v : ℂ) * Complex.exp (I * u * v))
    (fun k (v : ℝ) => g v * ((‖u‖ * |v|) ^ k / (k.factorial : ℝ)))
    (fun k => (hg.integrable_halfTerm u k).restrict.aestronglyMeasurable)
    (fun k => Eventually.of_forall fun v => (hg.norm_halfTerm u k v).le)
    (Eventually.of_forall fun v => (Real.summable_pow_div_factorial _).mul_left _)
    (hg.integrable_tsum_halfBound u).restrict
    (Eventually.of_forall fun v => (hasSum_pow_div_factorial_complex (I * u * v)).mul_left (g v : ℂ))
  simpa only [setIntegral_halfTerm] using h

theorem HyperbolicKernel.halfJensen_eq_jensenRev (d : ℕ) :
    halfJensen g d = jensenRev d (PowerSeries.mk (halfTaylorCoeff g)) := by
  rw [jensenRev_eq_sum, halfJensen, momentJensen]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hdesc : (d.descFactorial k : ℂ) = (d.choose k : ℂ) * (k.factorial : ℂ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [PowerSeries.coeff_mk, halfTaylorCoeff, hdesc]
  congr 2
  field_simp

/-- **The half transform is unstable.** For every `M` and all large `d`, `E_d` has at least `M` roots in the
open upper half-plane. -/
theorem eventually_le_card_upper_roots_halfJensen (M : ℕ) :
    ∀ᶠ d : ℕ in atTop, M ≤ Multiset.card
      ((halfJensen riemannKernelReal d).roots.filter fun e => 0 < e.im) := by
  classical
  have hg := hyperbolicKernel_riemann
  obtain ⟨T', hT's, hT'card⟩ := thetaHalfLaplace_zeros_infinite.exists_subset_card_eq M
  set T : Finset ℂ := T'.image fun w => -I * w
  have hinj : Function.Injective fun w : ℂ => -I * w := fun a b h => by
    simpa using h
  have hTcard : T.card = M := by
    rw [Finset.card_image_of_injective _ hinj, hT'card]
  have hsum := hg.hasSum_halfTaylorCoeff
  have hf : ∀ R : ℝ, Summable fun k => ‖halfTaylorCoeff riemannKernelReal k‖ * R ^ k :=
    summable_norm_mul_pow_of_summable fun u => (hsum u).summable
  have hf0 : halfTaylorCoeff riemannKernelReal 0 ≠ 0 := by
    simp only [halfTaylorCoeff, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, div_one]
    exact ofReal_ne_zero.2 hg.halfMoment_zero_pos.ne'
  have him : ∀ z ∈ T, z.im < 0 := fun z hz => by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
    have := re_pos_of_thetaHalfLaplace_eq_zero (hT's hw)
    simpa using this
  have h := eventually_le_card_roots_of_zeros (T := T) hf hf0 (fun z hz => by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
      rw [(hsum _).tsum_eq]
      have hK : thetaHalfLaplace w = 0 := hT's hw
      rw [thetaHalfLaplace_eq_kernel] at hK
      rw [← hK]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      have hI : I * (-I * w) = w := by rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
      simp only [hI])
    (fun z hz => (him z hz).ne) (p := fun e => 0 < e.im) (fun z hz x hx => by
      have := him z hz
      by_contra hneg
      push Not at hneg
      nlinarith)
  rw [hTcard] at h
  filter_upwards [h] with d hd
  rw [HyperbolicKernel.halfJensen_eq_jensenRev]
  exact hd

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.thetaHalfLaplace_zeros_infinite
#print axioms FiniteFreeProbability.eventually_le_card_upper_roots_halfJensen
