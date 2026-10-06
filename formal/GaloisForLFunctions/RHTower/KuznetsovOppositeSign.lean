import GaloisForLFunctions.RHTower.KuznetsovKLWeight

/-!
# Kuznetsov's formula for `S(m, −n)` (Deshouillers–Iwaniec (1.20))

For cusp vectors `v`, `w` of frequencies `μ > 0`, `−ν < 0` (`μ(N+1) = n`, `−ν(N+1) = m`) and a smooth
`φ` with compact support in `(0, ∞)`,

`Σ_{(c,d)} w(c,d) |c|⁻¹ φ(4π√(μν)/|c|)
   = 4 Σ_j ρ_j(v) conj ρ_j(w) φ̌(ν_j) + π⁻¹ ∫ Σ_i η_i(v, r) conj η_i(w, r) φ̌(ir) dr`

with `φ̌(ν) = ∫_0^∞ K_{2ν}(x) φ(x) dx/x` (`kuznetsov_opposite_sign`).

Proof: integrate the identity on the line `σ = 2` (`kuznetsov_bessel`) against the
Kontorovich–Lebedev weight `H(t)` of `f(x) = X³ x⁻⁴ φ(x)`, `X = 4π√(μν)`.  On the geometric side
`∫ H(t) K_{2it}(x) dt = x f(x)`; on the spectral side `∫ H(t) M(t, ν) dt = X³ φ̌(ν)`.  The interchanges
of `∫ dt` with the row sum, the spectral sum and the Eisenstein integral are justified by
`|H(t) K_{2it}(x)| ≪ (|log x| + 1)(1+t²)⁻¹`, `|H(t)Γ(2+it)Γ(2−it)| ≪ (1+t²)⁻¹` and the uniform bounds
for the spectral coefficients on the line.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry MaassWhittaker KontorovichLebedev

noncomputable section

variable {N : ℕ}

/-! ## The test function `f = X³ x⁻⁴ φ` -/

/-- Multiplying a test function by a function smooth on `(0, ∞)` gives a test function. -/
theorem IsKLTest.mul_contDiffOn {φ : ℝ → ℂ} (hφ : IsKLTest φ) {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ ⊤ g (Ioi 0)) : IsKLTest (fun x => g x * φ x) := by
  obtain ⟨a, b, ha, -, hsupp⟩ := hφ.exists_Icc
  refine ⟨?_, hφ.hasCompactSupport.mul_left, tsupport_mul_subset_right.trans hφ.tsupport_subset⟩
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  rcases lt_or_ge 0 x with hx | hx
  · exact ((hg.contDiffAt (Ioi_mem_nhds hx)).of_le le_top).mul hφ.smooth.contDiffAt
  · have hev : (fun x => g x * φ x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show x < a by linarith)] with y hy
      rw [eq_zero_of_tsupport_subset hsupp (fun h => absurd h.1 (not_le.2 hy)), mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem contDiffOn_inv_pow_four (X : ℝ) :
    ContDiffOn ℝ ⊤ (fun x : ℝ => ((X ^ 3 * (x ^ 4)⁻¹ : ℝ) : ℂ)) (Ioi 0) := by
  have h : ContDiffOn ℝ ⊤ (fun x : ℝ => X ^ 3 * (x ^ 4)⁻¹) (Ioi 0) :=
    contDiffOn_const.mul ((contDiffOn_id.pow 4).inv fun x hx =>
      pow_ne_zero 4 (ne_of_gt (show (0 : ℝ) < x from hx)))
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h

/-! ## The row sum -/

theorem two_sqrt_kuzParam {μ ν q : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q) :
    2 * Real.sqrt (Kuznetsov.kuzParam μ ν q) = 4 * Real.pi * Real.sqrt (μ * ν) / Real.sqrt q := by
  unfold Kuznetsov.kuzParam
  rw [show 4 * Real.pi ^ 2 * μ * ν / q = (2 * Real.pi) ^ 2 * (μ * ν) / q by ring,
    Real.sqrt_div' _ hq.le, Real.sqrt_mul' _ (by positivity), Real.sqrt_sq (by positivity)]
  ring

theorem kuzParam_pos {μ ν q : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q) :
    0 < Kuznetsov.kuzParam μ ν q := by
  unfold Kuznetsov.kuzParam; positivity

theorem reducedRow_sq_pos (r : ReducedRow) : (0 : ℝ) < (r.1.1 0 : ℝ) ^ 2 := by
  have : (r.1.1 0 : ℝ) ≠ 0 := by exact_mod_cast r.2.1
  positivity

theorem one_le_abs_reducedRow (r : ReducedRow) : (1 : ℝ) ≤ |(r.1.1 0 : ℝ)| := by
  have h : (r.1.1 0 : ℤ) ≠ 0 := r.2.1
  have : (1 : ℤ) ≤ |r.1.1 0| := Int.one_le_abs h
  exact_mod_cast this

/-- **The geometric side integrated against the weight.** -/
theorem integral_klWeight_mul_rowSum {f : ℝ → ℂ} (hf : IsKLTest f) {μ ν : ℝ} (hμ : 0 < μ)
    (hν : 0 < ν) (v w : DeckSpace N) :
    ∫ t : ℝ, klWeight f t * ∑' r : ReducedRow, rowWeight μ ν v w r.1 *
        (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((2 : ℝ) : ℂ)) *
        modifiedBesselKOrder (2 * Real.sqrt (Kuznetsov.kuzParam μ ν ((r.1.1 0 : ℝ) ^ 2)))
          (2 * t * Complex.I) =
      ∑' r : ReducedRow, rowWeight μ ν v w r.1 * (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((2 : ℝ) : ℂ)) *
        ((2 * Real.sqrt (Kuznetsov.kuzParam μ ν ((r.1.1 0 : ℝ) ^ 2)) : ℝ) *
          f (2 * Real.sqrt (Kuznetsov.kuzParam μ ν ((r.1.1 0 : ℝ) ^ 2)))) := by
  obtain ⟨D, hD, hb⟩ := exists_bound_klWeight_mul_besselK hf
  set x : ReducedRow → ℝ := fun r => 2 * Real.sqrt (Kuznetsov.kuzParam μ ν ((r.1.1 0 : ℝ) ^ 2))
  have hx : ∀ r, 0 < x r := fun r => by
    simp only [x]
    exact mul_pos two_pos (Real.sqrt_pos.2 (kuzParam_pos hμ hν (reducedRow_sq_pos r)))
  set c : ReducedRow → ℂ := fun r => rowWeight μ ν v w r.1 *
    (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((2 : ℝ) : ℂ))
  set F : ReducedRow → ℝ → ℂ := fun r t =>
    c r * (klWeight f t * modifiedBesselKOrder (x r) (2 * t * Complex.I))
  have hnc : ∀ r, ‖c r‖ ≤ ‖v‖ * ‖w‖ * ((r.1.1 0 : ℝ) ^ 2) ^ (-(2 : ℝ)) := fun r => by
    simp only [c]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (reducedRow_sq_pos r)]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (norm_rowWeight_le μ ν v w r.1)
      (Real.rpow_nonneg (reducedRow_sq_pos r).le _)
  have hcont : ∀ r, Continuous fun t : ℝ => klWeight f t * modifiedBesselKOrder (x r) (2 * t * Complex.I) :=
    fun r => (continuous_klWeight hf).mul
      ((differentiable_modifiedBesselKOrder (hx r)).continuous.comp (by fun_prop))
  have hintr : ∀ r, Integrable fun t : ℝ =>
      klWeight f t * modifiedBesselKOrder (x r) (2 * t * Complex.I) := fun r =>
    (integrable_inv_one_add_sq.const_mul (D * (|Real.log (x r)| + 1))).mono'
      (hcont r).aestronglyMeasurable (Eventually.of_forall fun t => by
        rw [norm_mul]; exact hb (x r) (hx r) t)
  have hF : ∀ r, Integrable (F r) := fun r => (hintr r).const_mul (c r)
  -- summability of the norms
  have hlogx : ∀ r, |Real.log (x r)| + 1 ≤
      (|Real.log (4 * Real.pi * Real.sqrt (μ * ν))| + 1) + |(r.1.1 0 : ℝ)| := fun r => by
    have hc1 := one_le_abs_reducedRow r
    have hxr : x r = 4 * Real.pi * Real.sqrt (μ * ν) / |(r.1.1 0 : ℝ)| := by
      simp only [x]; rw [two_sqrt_kuzParam hμ hν (reducedRow_sq_pos r), Real.sqrt_sq_eq_abs]
    have hX : 0 < 4 * Real.pi * Real.sqrt (μ * ν) := by positivity
    rw [hxr, Real.log_div hX.ne' (by positivity)]
    have hl0 : 0 ≤ Real.log |(r.1.1 0 : ℝ)| := Real.log_nonneg hc1
    have hl1 : Real.log |(r.1.1 0 : ℝ)| ≤ |(r.1.1 0 : ℝ)| := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < |(r.1.1 0 : ℝ)| by linarith); linarith
    have := abs_sub (Real.log (4 * Real.pi * Real.sqrt (μ * ν))) (Real.log |(r.1.1 0 : ℝ)|)
    rw [abs_of_nonneg hl0] at this
    linarith
  set L : ℝ := |Real.log (4 * Real.pi * Real.sqrt (μ * ν))| + 2
  have hnorm : ∀ r, ∫ t, ‖F r t‖ ≤ ‖v‖ * ‖w‖ * D * Real.pi * L *
      ((r.1.1 0 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) := fun r => by
    have hq := reducedRow_sq_pos r
    have hc1 := one_le_abs_reducedRow r
    have hq1 : (1 : ℝ) ≤ (r.1.1 0 : ℝ) ^ 2 := by nlinarith [sq_abs (r.1.1 0 : ℝ)]
    calc ∫ t, ‖F r t‖ ≤ ∫ t, ‖c r‖ * (D * (|Real.log (x r)| + 1) * (1 + t ^ 2)⁻¹) := by
          refine integral_mono (hF r).norm ((integrable_inv_one_add_sq.const_mul _).const_mul _)
            fun t => ?_
          simp only [F, norm_mul]
          exact mul_le_mul_of_nonneg_left (hb (x r) (hx r) t) (norm_nonneg _)
      _ = ‖c r‖ * D * (|Real.log (x r)| + 1) * Real.pi := by
          rw [integral_const_mul, integral_const_mul, integral_univ_inv_one_add_sq]; ring
      _ ≤ ‖v‖ * ‖w‖ * ((r.1.1 0 : ℝ) ^ 2) ^ (-(2 : ℝ)) * D *
            ((|Real.log (4 * Real.pi * Real.sqrt (μ * ν))| + 1) + |(r.1.1 0 : ℝ)|) * Real.pi := by
          gcongr ?_ * D * ?_ * Real.pi
          · exact hnc r
          · exact hlogx r
      _ ≤ ‖v‖ * ‖w‖ * D * Real.pi * L * ((r.1.1 0 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) := by
          have habs : |(r.1.1 0 : ℝ)| = ((r.1.1 0 : ℝ) ^ 2) ^ (1 / 2 : ℝ) := by
            rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
          have h2 : ((r.1.1 0 : ℝ) ^ 2) ^ (-(2 : ℝ)) ≤ ((r.1.1 0 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
          have h3 : ((r.1.1 0 : ℝ) ^ 2) ^ (-(2 : ℝ)) * |(r.1.1 0 : ℝ)| =
              ((r.1.1 0 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) := by
            rw [habs, ← Real.rpow_add hq]; norm_num
          have hlg : 0 ≤ |Real.log (4 * Real.pi * Real.sqrt (μ * ν))| + 1 := by positivity
          have hp0 : 0 ≤ ((r.1.1 0 : ℝ) ^ 2) ^ (-(2 : ℝ)) := Real.rpow_nonneg hq.le _
          have hA : 0 ≤ ‖v‖ * ‖w‖ * D * Real.pi := by positivity
          calc ‖v‖ * ‖w‖ * ((r.1.1 0 : ℝ) ^ 2) ^ (-(2 : ℝ)) * D *
                ((|Real.log (4 * Real.pi * Real.sqrt (μ * ν))| + 1) + |(r.1.1 0 : ℝ)|) * Real.pi
              = ‖v‖ * ‖w‖ * D * Real.pi * ((|Real.log (4 * Real.pi * Real.sqrt (μ * ν))| + 1) *
                  ((r.1.1 0 : ℝ) ^ 2) ^ (-(2 : ℝ)) +
                  ((r.1.1 0 : ℝ) ^ 2) ^ (-(2 : ℝ)) * |(r.1.1 0 : ℝ)|) := by ring
            _ ≤ ‖v‖ * ‖w‖ * D * Real.pi * ((|Real.log (4 * Real.pi * Real.sqrt (μ * ν))| + 1) *
                  ((r.1.1 0 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) + ((r.1.1 0 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ))) := by
                rw [h3]; gcongr
            _ = ‖v‖ * ‖w‖ * D * Real.pi * L * ((r.1.1 0 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) := by
                simp only [L]; ring
  have hsum : Summable fun r => ∫ t, ‖F r t‖ :=
    ((summable_reducedRow_rpow (τ := 3 / 2) (by norm_num)).mul_left
      (‖v‖ * ‖w‖ * D * Real.pi * L)).of_nonneg_of_le
      (fun r => integral_nonneg fun t => norm_nonneg _) hnorm
  have hpt : ∀ t, klWeight f t * ∑' r : ReducedRow, rowWeight μ ν v w r.1 *
      (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((2 : ℝ) : ℂ)) *
      modifiedBesselKOrder (2 * Real.sqrt (Kuznetsov.kuzParam μ ν ((r.1.1 0 : ℝ) ^ 2)))
        (2 * t * Complex.I) = ∑' r, F r t := fun t => by
    rw [← tsum_mul_left]
    congr 1; funext r; simp only [F, c, x]; ring
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hF hsum]
  congr 1; funext r
  simp only [F]
  rw [integral_const_mul, integral_klWeight_mul_besselK hf (hx r)]

/-! ## Countability of the spectrum and measurability of spectral sums -/

instance : SecondCountableTopology (DeckL2 N) := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

/-- The cuspidal eigenbasis is countable (the cell `L²` space is separable). -/
instance countable_cuspEigenIndex : Countable (CuspEigenIndex N) := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun j => Metric.ball (cuspEigenBasis N j) (1 / 2))
    (fun i j hij => ?_) (fun _ => Metric.isOpen_ball) (fun _ => Metric.nonempty_ball.2 (by norm_num))
  rw [Function.onFun, Set.disjoint_iff]
  rintro z ⟨hi, hj⟩
  have ho := (cuspEigenBasis N).orthonormal
  have hd : ‖(cuspEigenBasis N i : CuspidalL2 N) - cuspEigenBasis N j‖ ^ 2 = 2 := by
    rw [@norm_sub_sq ℂ, ho.1 i, ho.1 j, ho.2 hij]
    simp; norm_num
  have h1 : ‖(cuspEigenBasis N i : CuspidalL2 N) - cuspEigenBasis N j‖ < 1 := by
    have := dist_triangle_right (cuspEigenBasis N i) (cuspEigenBasis N j) z
    rw [Metric.mem_ball, dist_comm] at hi hj
    rw [← dist_eq_norm]; linarith
  nlinarith [norm_nonneg ((cuspEigenBasis N i : CuspidalL2 N) - cuspEigenBasis N j)]

theorem aestronglyMeasurable_tsum_of_summable {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ}
    (hF : ∀ i, AEStronglyMeasurable (F i) volume) (hs : ∀ t, Summable fun i => F i t) :
    AEStronglyMeasurable (fun t => ∑' i, F i t) volume :=
  aestronglyMeasurable_of_tendsto_ae (u := (atTop : Filter (Finset ι)))
    (f := fun s t => ∑ i ∈ s, F i t) (fun s => Finset.aestronglyMeasurable_fun_sum s fun i _ => hF i)
    (Eventually.of_forall fun t => (hs t).hasSum)

/-! ## The discrete spectrum -/

theorem integrableOn_sq_one_add_inv_sq_exp :
    IntegrableOn (fun x : ℝ => x ^ 2 * ((1 + 1 / x) * Real.exp (-x)) * ((1 + 1 / x) * Real.exp (-x)))
      (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((3 : ℝ) - 1) +
      2 * (Real.exp (-x) * x ^ ((2 : ℝ) - 1)) + Real.exp (-x) * x ^ ((1 : ℝ) - 1)) (Ioi 0) :=
    ((Real.GammaIntegral_convergent (by norm_num)).add
      ((Real.GammaIntegral_convergent (by norm_num)).const_mul 2)).add
      (Real.GammaIntegral_convergent (by norm_num))
  refine hg.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have h1 : ContinuousOn (fun x : ℝ => (1 + 1 / x) * Real.exp (-x)) (Ioi 0) :=
      (continuousOn_const.add (continuousOn_const.div continuousOn_id
        fun x hx => ne_of_gt (show (0 : ℝ) < x from hx))).mul (by fun_prop)
    exact ((by fun_prop : Continuous fun x : ℝ => x ^ 2).continuousOn.mul h1).mul h1
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [show (3 : ℝ) - 1 = (2 : ℕ) by norm_num, show (2 : ℝ) - 1 = (1 : ℕ) by norm_num,
      show (1 : ℝ) - 1 = (0 : ℕ) by norm_num, Real.rpow_natCast]
    have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have he0 := Real.exp_pos (-x)
    calc x ^ 2 * ((1 + 1 / x) * Real.exp (-x)) * ((1 + 1 / x) * Real.exp (-x))
        = (x + 1) ^ 2 * Real.exp (-x) * Real.exp (-x) := by field_simp
      _ ≤ (x + 1) ^ 2 * Real.exp (-x) * 1 := by gcongr
      _ = _ := by ring

/-- `t ↦ M(t, ν)` is continuous for `|Re ν| ≤ ½`. -/
theorem continuous_besselPairMellin_two {ν : ℂ} (hν : |ν.re| ≤ 1 / 2) :
    Continuous fun t : ℝ => besselPairMellin 2 t ν := by
  have h2ν : |(2 * ν).re| ≤ 1 := by
    rw [show (2 * ν).re = 2 * ν.re by simp, abs_mul, abs_two]; linarith
  simp_rw [besselPairMellin_two]
  refine continuous_of_dominated (μ := volume.restrict (Ioi 0))
    (bound := fun x => x ^ 2 * ((1 + 1 / x) * Real.exp (-x)) * ((1 + 1 / x) * Real.exp (-x)))
    (fun t => ?_) (fun t => ?_) integrableOn_sq_one_add_inv_sq_exp ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hK1 := continuousOn_modifiedBesselKOrder.comp
      ((by fun_prop : Continuous fun x : ℝ => ((x, 2 * (t : ℂ) * Complex.I) : ℝ × ℂ)).continuousOn)
      (s := Ioi (0 : ℝ)) fun x hx => ⟨hx, mem_univ _⟩
    have hK2 := continuousOn_modifiedBesselKOrder.comp
      ((by fun_prop : Continuous fun x : ℝ => ((x, 2 * ν) : ℝ × ℂ)).continuousOn)
      (s := Ioi (0 : ℝ)) fun x hx => ⟨hx, mem_univ _⟩
    simp only [Function.comp_def] at hK1 hK2
    exact ((by fun_prop : Continuous fun x : ℝ => (x : ℂ) ^ 2).continuousOn.mul hK1).mul hK2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    have h1 := norm_modifiedBesselKOrder_le_of_abs_re_le_one hx0
      (ν := 2 * t * Complex.I) (by simp)
    have h2 := norm_modifiedBesselKOrder_le_of_abs_re_le_one hx0 h2ν
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    exact continuous_const.mul ((differentiable_modifiedBesselKOrder hx0).continuous.comp
      (by fun_prop)) |>.mul continuous_const

/-- The constant `κ = π 2^{−3} Γ(3)` of the product formula on the line `σ = 2`. -/
def lineConst : ℂ :=
  Real.pi * (2 : ℂ) ^ ((5 - 4 * 2 : ℝ) : ℂ) * Complex.Gamma (2 * ((2 : ℝ) : ℂ) - 1)

theorem lineConst_ne_zero : lineConst ≠ 0 := by
  unfold lineConst
  refine mul_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) ?_)
    (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  rw [two_cpow_eq_exp]; exact Complex.exp_ne_zero _

/-- `M(t, ν) = W(2+it, ν) W(2−it, ν) Γ(2+it)Γ(2−it) / κ`. -/
theorem besselPairMellin_eq (t : ℝ) {ν : ℂ} (hν : |ν.re| ≤ 1 / 2) :
    besselPairMellin 2 t ν = whittMellin (((2 : ℝ) : ℂ) + t * Complex.I) ν *
      whittMellin (((2 : ℝ) : ℂ) - t * Complex.I) ν *
      (Complex.Gamma (((2 : ℝ) : ℂ) + t * Complex.I) * Complex.Gamma (((2 : ℝ) : ℂ) - t * Complex.I)) /
        lineConst := by
  have h := whittMellin_mul_line (σ := 2) (by norm_num) t (ν := ν) (by linarith)
  have hγ : Complex.Gamma (((2 : ℝ) : ℂ) + t * Complex.I) *
      Complex.Gamma (((2 : ℝ) : ℂ) - t * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simp)) (Complex.Gamma_ne_zero_of_re_pos (by simp))
  have hκ := lineConst_ne_zero
  have hA : Complex.Gamma (2 * ((2 : ℝ) : ℂ) - 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have h2 : (2 : ℂ) ^ ((5 - 4 * 2 : ℝ) : ℂ) ≠ 0 := by
    rw [two_cpow_eq_exp]; exact Complex.exp_ne_zero _
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h]
  unfold lineConst
  field_simp
  rw [mul_assoc, mul_div_assoc, div_self hγ, mul_one]

/-- **The discrete spectrum integrated against the weight.** -/
theorem integrable_and_integral_klWeight_mul_discrete {f : ℝ → ℂ} (hf : IsKLTest f) {μ ν : ℝ}
    (hμ : 0 < μ) (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v)
    (hw : IsCuspEigen (-ν) w) :
    Integrable (fun t : ℝ => klWeight f t * ∑' j : CuspEigenIndex N, cuspCoeff j μ v *
        conj (cuspCoeff j (-ν) w) * besselPairMellin 2 t (specParam j.1)) ∧
      ∫ t : ℝ, klWeight f t * ∑' j : CuspEigenIndex N, cuspCoeff j μ v *
          conj (cuspCoeff j (-ν) w) * besselPairMellin 2 t (specParam j.1) =
        ∑' j : CuspEigenIndex N, cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) *
          ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * modifiedBesselKOrder x (2 * specParam j.1) * (x * f x) := by
  obtain ⟨DΓ, hDΓ, hbΓ⟩ := exists_bound_klWeight_mul_Gamma hf
  have hκ := lineConst_ne_zero
  set κ := lineConst
  set a : CuspEigenIndex N → ℝ → ℝ := fun j t => ‖cuspCoeff j μ v‖ * ‖cuspCoeff j (-ν) w‖ *
    ‖whittMellin (((2 : ℝ) : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2
  have ha := fun t => summable_and_tsum_cuspCoeff_line_le (σ := 2) (by norm_num) hμ hν hv hw
    (N := N) t
  set Dl : ℝ := ((‖v‖ * poincMajorantNorm 2 μ) ^ 2 + (‖w‖ * poincMajorantNorm 2 ν) ^ 2) / 2 /
    (4 * (2 * Real.pi * μ) ^ (1 / 2 - (2 : ℝ)) * (2 * Real.pi * ν) ^ (1 / 2 - (2 : ℝ)))
  have ha0 : ∀ j t, 0 ≤ a j t := fun j t => by positivity
  have haj : ∀ j t, a j t ≤ Dl := fun j t =>
    ((ha t).1.le_tsum j fun k _ => ha0 k t).trans (ha t).2
  have hDl : 0 ≤ Dl := by simp only [Dl]; positivity
  set F : CuspEigenIndex N → ℝ → ℂ := fun j t => klWeight f t *
    (cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) * besselPairMellin 2 t (specParam j.1))
  have hF : ∀ j t, ‖F j t‖ ≤ DΓ / ‖κ‖ * (1 + t ^ 2)⁻¹ * a j t := fun j t => by
    have hj : |(specParam j.1).re| ≤ 1 / 2 := abs_re_specParam_le (cuspEigenBasis_lam_nonneg j)
    have hW := norm_whittMellin_conj_line 2 t (specParam j.1) (conj_specParam j.1)
    simp only [F, a]
    rw [besselPairMellin_eq t hj, norm_mul, norm_mul, norm_mul, norm_div, norm_mul, norm_mul,
      Complex.norm_conj, hW]
    have hb := hbΓ t
    have hγc : Complex.Gamma (((2 : ℝ) : ℂ) + t * Complex.I) *
        Complex.Gamma (((2 : ℝ) : ℂ) - t * Complex.I) =
        Complex.Gamma (2 + t * Complex.I) * Complex.Gamma (2 - t * Complex.I) := by push_cast; rfl
    rw [hγc]
    have hκ0 : 0 < ‖κ‖ := norm_pos_iff.2 hκ
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hκ0]
    calc ‖klWeight f t‖ * (‖cuspCoeff j μ v‖ * ‖cuspCoeff j (-ν) w‖ *
          (‖whittMellin (((2 : ℝ) : ℂ) + t * Complex.I) (specParam j.1)‖ *
            ‖whittMellin (((2 : ℝ) : ℂ) + t * Complex.I) (specParam j.1)‖ *
            ‖Complex.Gamma (2 + t * Complex.I) * Complex.Gamma (2 - t * Complex.I)‖ / ‖κ‖)) * ‖κ‖
        = (‖klWeight f t‖ * ‖Complex.Gamma (2 + t * Complex.I) * Complex.Gamma (2 - t * Complex.I)‖) *
            (‖cuspCoeff j μ v‖ * ‖cuspCoeff j (-ν) w‖ *
              ‖whittMellin (((2 : ℝ) : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2) := by
          field_simp
      _ ≤ (DΓ * (1 + t ^ 2)⁻¹) * (‖cuspCoeff j μ v‖ * ‖cuspCoeff j (-ν) w‖ *
              ‖whittMellin (((2 : ℝ) : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2) := by gcongr
      _ = DΓ * (1 + t ^ 2)⁻¹ * (‖cuspCoeff j μ v‖ * ‖cuspCoeff j (-ν) w‖ *
              ‖whittMellin (((2 : ℝ) : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2) := by ring
  have hc0 : 0 ≤ DΓ / ‖κ‖ := by positivity
  have hcont : ∀ j, Continuous (F j) := fun j =>
    (continuous_klWeight hf).mul (continuous_const.mul
      (continuous_besselPairMellin_two (abs_re_specParam_le (cuspEigenBasis_lam_nonneg j))))
  have hdom : Integrable (fun t : ℝ => DΓ / ‖κ‖ * Dl * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hFint : ∀ j, Integrable (F j) := fun j =>
    hdom.mono' (hcont j).aestronglyMeasurable (Eventually.of_forall fun t =>
      (hF j t).trans (by
        calc DΓ / ‖κ‖ * (1 + t ^ 2)⁻¹ * a j t ≤ DΓ / ‖κ‖ * (1 + t ^ 2)⁻¹ * Dl := by
              gcongr; exact haj j t
          _ = DΓ / ‖κ‖ * Dl * (1 + t ^ 2)⁻¹ := by ring))
  have hpsum : ∀ t, Summable fun j => DΓ / ‖κ‖ * (1 + t ^ 2)⁻¹ * a j t := fun t =>
    (ha t).1.mul_left _
  have hptle : ∀ t, ∑' j, DΓ / ‖κ‖ * (1 + t ^ 2)⁻¹ * a j t ≤ DΓ / ‖κ‖ * Dl * (1 + t ^ 2)⁻¹ :=
    fun t => by
      rw [tsum_mul_left]
      calc DΓ / ‖κ‖ * (1 + t ^ 2)⁻¹ * ∑' j, a j t ≤ DΓ / ‖κ‖ * (1 + t ^ 2)⁻¹ * Dl := by
            gcongr; exact (ha t).2
        _ = DΓ / ‖κ‖ * Dl * (1 + t ^ 2)⁻¹ := by ring
  have hsum : Summable fun j => ∫ t, ‖F j t‖ := by
    refine summable_of_sum_le (c := DΓ / ‖κ‖ * Dl * Real.pi)
      (fun j => integral_nonneg fun t => norm_nonneg _) fun S => ?_
    rw [← integral_finsetSum S fun j _ => (hFint j).norm]
    calc ∫ t, ∑ j ∈ S, ‖F j t‖ ≤ ∫ t, DΓ / ‖κ‖ * Dl * (1 + t ^ 2)⁻¹ := by
          refine integral_mono (integrable_finsetSum S fun j _ => (hFint j).norm) hdom fun t => ?_
          calc ∑ j ∈ S, ‖F j t‖ ≤ ∑ j ∈ S, DΓ / ‖κ‖ * (1 + t ^ 2)⁻¹ * a j t :=
                Finset.sum_le_sum fun j _ => hF j t
            _ ≤ ∑' j, DΓ / ‖κ‖ * (1 + t ^ 2)⁻¹ * a j t :=
                (hpsum t).sum_le_tsum S fun j _ => by positivity
            _ ≤ _ := hptle t
      _ = DΓ / ‖κ‖ * Dl * Real.pi := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hpt : ∀ t, klWeight f t * ∑' j : CuspEigenIndex N, cuspCoeff j μ v *
      conj (cuspCoeff j (-ν) w) * besselPairMellin 2 t (specParam j.1) = ∑' j, F j t :=
    fun t => by rw [← tsum_mul_left]
  simp_rw [hpt]
  have hsumt : ∀ t, Summable fun j => F j t := fun t =>
    Summable.of_norm_bounded (hpsum t) fun j => hF j t
  refine ⟨hdom.mono' (aestronglyMeasurable_tsum_of_summable
    (fun j => (hFint j).1) hsumt) (Eventually.of_forall fun t => ?_), ?_⟩
  · exact (norm_tsum_le_tsum_norm (Summable.of_norm_bounded (hpsum t) fun j => by
      rw [norm_norm]; exact hF j t)).trans
      (((Summable.of_norm_bounded (hpsum t) fun j => by rw [norm_norm]; exact hF j t).tsum_le_tsum
        (fun j => hF j t) (hpsum t)).trans (hptle t))
  · rw [← integral_tsum_of_summable_integral_norm hFint hsum]
    congr 1; funext j
    simp only [F]
    have hj : |(specParam j.1).re| ≤ 1 / 2 := abs_re_specParam_le (cuspEigenBasis_lam_nonneg j)
    rw [← integral_klWeight_mul_besselPairMellin hf hj, ← integral_const_mul]
    congr 1; funext t; ring

/-! ## The continuous spectrum -/

/-- `H(t) M(t, ν)` is integrable for `|Re ν| ≤ ½`. -/
theorem integrable_klWeight_mul_besselPairMellin {f : ℝ → ℂ} (hf : IsKLTest f) {ν : ℂ}
    (hν : |ν.re| ≤ 1 / 2) : Integrable fun t : ℝ => klWeight f t * besselPairMellin 2 t ν := by
  obtain ⟨D, hD, hb⟩ := exists_bound_klWeight_mul_besselK hf
  have h2ν : |(2 * ν).re| ≤ 1 := by
    rw [show (2 * ν).re = 2 * ν.re by simp, abs_mul, abs_two]; linarith
  set I₀ : ℝ := ∫ x in Ioi (0 : ℝ), x ^ 2 * (|Real.log x| + 1) * ((1 + 1 / x) * Real.exp (-x))
  refine (integrable_inv_one_add_sq.const_mul (D * I₀)).mono'
    ((continuous_klWeight hf).mul (continuous_besselPairMellin_two hν)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [besselPairMellin_two, norm_mul]
  have hle : ∀ x ∈ Ioi (0 : ℝ), ‖klWeight f t‖ * ‖(x : ℂ) ^ 2 *
      modifiedBesselKOrder x (2 * t * Complex.I) * modifiedBesselKOrder x (2 * ν)‖ ≤
      D * (1 + t ^ 2)⁻¹ * (x ^ 2 * (|Real.log x| + 1) * ((1 + 1 / x) * Real.exp (-x))) :=
    fun x hx => by
      have hx0 : (0 : ℝ) < x := hx
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      have h1 := hb x hx0 t
      have h2 := norm_modifiedBesselKOrder_le_of_abs_re_le_one hx0 h2ν
      calc ‖klWeight f t‖ * (x ^ 2 * ‖modifiedBesselKOrder x (2 * t * Complex.I)‖ *
            ‖modifiedBesselKOrder x (2 * ν)‖)
          = (‖klWeight f t‖ * ‖modifiedBesselKOrder x (2 * t * Complex.I)‖) *
              (x ^ 2 * ‖modifiedBesselKOrder x (2 * ν)‖) := by ring
        _ ≤ (D * (|Real.log x| + 1) * (1 + t ^ 2)⁻¹) * (x ^ 2 * ((1 + 1 / x) * Real.exp (-x))) := by
            gcongr
        _ = _ := by ring
  calc ‖klWeight f t‖ * ‖∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 *
          modifiedBesselKOrder x (2 * t * Complex.I) * modifiedBesselKOrder x (2 * ν)‖
      ≤ ‖klWeight f t‖ * ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ 2 *
          modifiedBesselKOrder x (2 * t * Complex.I) * modifiedBesselKOrder x (2 * ν)‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = ∫ x in Ioi (0 : ℝ), ‖klWeight f t‖ * ‖(x : ℂ) ^ 2 *
          modifiedBesselKOrder x (2 * t * Complex.I) * modifiedBesselKOrder x (2 * ν)‖ := by
        rw [integral_const_mul]
    _ ≤ ∫ x in Ioi (0 : ℝ), D * (1 + t ^ 2)⁻¹ *
          (x ^ 2 * (|Real.log x| + 1) * ((1 + 1 / x) * Real.exp (-x))) := by
        refine setIntegral_mono_on ?_ (integrableOn_besselMellinMajorant.const_mul _)
          measurableSet_Ioi hle
        exact (integrableOn_besselMellinMajorant.const_mul (D * (1 + t ^ 2)⁻¹)).mono'
          (by
            refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
            have hK1 := continuousOn_modifiedBesselKOrder.comp
              ((by fun_prop : Continuous fun x : ℝ =>
                ((x, 2 * (t : ℂ) * Complex.I) : ℝ × ℂ)).continuousOn)
              (s := Ioi (0 : ℝ)) fun x hx => ⟨hx, mem_univ _⟩
            have hK2 := continuousOn_modifiedBesselKOrder.comp
              ((by fun_prop : Continuous fun x : ℝ => ((x, 2 * ν) : ℝ × ℂ)).continuousOn)
              (s := Ioi (0 : ℝ)) fun x hx => ⟨hx, mem_univ _⟩
            simp only [Function.comp_def] at hK1 hK2
            exact continuousOn_const.mul (((by fun_prop : Continuous fun x : ℝ =>
              (x : ℂ) ^ 2).continuousOn.mul hK1).mul hK2).norm)
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            exact hle x hx)
    _ = D * I₀ * (1 + t ^ 2)⁻¹ := by rw [integral_const_mul]; ring

/-- `(t, r) ↦ M(t, ir)` is continuous. -/
theorem continuous_besselPairMellin_line :
    Continuous fun p : ℝ × ℝ => besselPairMellin 2 p.1 (p.2 * Complex.I) := by
  simp_rw [besselPairMellin_two]
  refine continuous_of_dominated (μ := volume.restrict (Ioi 0))
    (bound := fun x => x ^ 2 * ((1 + 1 / x) * Real.exp (-x)) * ((1 + 1 / x) * Real.exp (-x)))
    (fun p => ?_) (fun p => ?_) integrableOn_sq_one_add_inv_sq_exp ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hK1 := continuousOn_modifiedBesselKOrder.comp
      ((by fun_prop : Continuous fun x : ℝ => ((x, 2 * (p.1 : ℂ) * Complex.I) : ℝ × ℂ)).continuousOn)
      (s := Ioi (0 : ℝ)) fun x hx => ⟨hx, mem_univ _⟩
    have hK2 := continuousOn_modifiedBesselKOrder.comp
      ((by fun_prop : Continuous fun x : ℝ =>
        ((x, 2 * ((p.2 : ℂ) * Complex.I)) : ℝ × ℂ)).continuousOn)
      (s := Ioi (0 : ℝ)) fun x hx => ⟨hx, mem_univ _⟩
    simp only [Function.comp_def] at hK1 hK2
    exact ((by fun_prop : Continuous fun x : ℝ => (x : ℂ) ^ 2).continuousOn.mul hK1).mul hK2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    have h1 := norm_modifiedBesselKOrder_le_of_abs_re_le_one hx0
      (ν := 2 * p.1 * Complex.I) (by simp)
    have h2 := norm_modifiedBesselKOrder_le_of_abs_re_le_one hx0
      (ν := 2 * ((p.2 : ℂ) * Complex.I)) (by simp)
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hc := (differentiable_modifiedBesselKOrder hx0).continuous
    exact (continuous_const.mul (hc.comp (by fun_prop))).mul (hc.comp (by fun_prop))

theorem aestronglyMeasurable_eisCoeff_line (v w : DeckSpace N) (n : ℤ) :
    AEStronglyMeasurable (fun r : ℝ => eisCoeff (1 / 2 + r * Complex.I) v w n) volume := by
  have hco : ContinuousOn (fun r : ℝ => eisCoeff (1 / 2 + r * Complex.I) v w n) {r | r ≠ 0} :=
    fun r hr => by
      have hs : (1 / 2 + (r : ℂ) * Complex.I) ≠ 1 / 2 := by
        intro h; apply hr; have := congrArg Complex.im h; simpa using this
      have hd := (differentiableAt_eisCoeff v w n (s := 1 / 2 + (r : ℂ) * Complex.I) (by simp)
        hs).continuousAt
      have hl : ContinuousAt (fun r : ℝ => 1 / 2 + (r : ℂ) * Complex.I) r :=
        (by fun_prop : Continuous fun r : ℝ => 1 / 2 + (r : ℂ) * Complex.I).continuousAt
      exact (ContinuousAt.comp (f := fun r : ℝ => 1 / 2 + (r : ℂ) * Complex.I)
        (g := fun s => eisCoeff s v w n) hd hl).continuousWithinAt
  have h := hco.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℝ)).compl
  have hne : ∀ᵐ t : ℝ ∂volume, t ∈ {t : ℝ | t ≠ 0} := by simp [ae_iff, measure_singleton]
  rwa [Measure.restrict_eq_self_of_ae_mem hne] at h

/-- The integrand `(t, r) ↦ H(t) Σ_i η_i(v, r) conj η_i(w, r) M(t, ir)` of the continuous spectrum. -/
def contIntegrand (f : ℝ → ℂ) (v w : DeckSpace N) (n m : ℤ) (p : ℝ × ℝ) : ℂ :=
  klWeight f p.1 * ∑ i, eisCoeff (1 / 2 + p.2 * Complex.I) v (cuspBasisVec N i) n *
    conj (eisCoeff (1 / 2 + p.2 * Complex.I) w (cuspBasisVec N i) m) *
    besselPairMellin 2 p.1 (p.2 * Complex.I)

/-- The `r`-majorant `Σ_i |η_i(v, r)| |η_i(w, r)| |W(2+it, ir)|²`. -/
def contMajorant (v w : DeckSpace N) (n m : ℤ) (t r : ℝ) : ℝ :=
  ∑ i, ‖eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n‖ *
    ‖eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m‖ *
    ‖whittMellin (((2 : ℝ) : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2

theorem norm_besselPairMellin_line (t r : ℝ) :
    ‖besselPairMellin 2 t ((r : ℂ) * Complex.I)‖ =
      ‖whittMellin (((2 : ℝ) : ℂ) + t * Complex.I) ((r : ℂ) * Complex.I)‖ ^ 2 *
        ‖Complex.Gamma (2 + t * Complex.I) * Complex.Gamma (2 - t * Complex.I)‖ / ‖lineConst‖ := by
  have hr : |((r : ℂ) * Complex.I).re| ≤ 1 / 2 := by simp
  have hW := norm_whittMellin_conj_line 2 t ((r : ℂ) * Complex.I) (Or.inr (by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring))
  have hγc : Complex.Gamma (((2 : ℝ) : ℂ) + t * Complex.I) *
      Complex.Gamma (((2 : ℝ) : ℂ) - t * Complex.I) =
      Complex.Gamma (2 + t * Complex.I) * Complex.Gamma (2 - t * Complex.I) := by push_cast; rfl
  rw [besselPairMellin_eq t hr, hγc, norm_div, norm_mul, norm_mul, hW]; ring

theorem norm_contIntegrand_le {f : ℝ → ℂ} {DΓ : ℝ}
    (hbΓ : ∀ t : ℝ, ‖klWeight f t‖ *
      ‖Complex.Gamma (2 + t * Complex.I) * Complex.Gamma (2 - t * Complex.I)‖ ≤ DΓ * (1 + t ^ 2)⁻¹)
    (v w : DeckSpace N) (n m : ℤ) (t r : ℝ) :
    ‖contIntegrand f v w n m (t, r)‖ ≤
      DΓ / ‖lineConst‖ * (1 + t ^ 2)⁻¹ * contMajorant v w n m t r := by
  have hκ0 : 0 < ‖lineConst‖ := norm_pos_iff.2 lineConst_ne_zero
  unfold contIntegrand contMajorant
  rw [norm_mul]
  calc ‖klWeight f t‖ * ‖∑ i, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
        conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
        besselPairMellin 2 t (r * Complex.I)‖
      ≤ ‖klWeight f t‖ * ∑ i, ‖eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n‖ *
          ‖eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m‖ *
          ‖besselPairMellin 2 t (r * Complex.I)‖ := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        congr 1; funext i; rw [norm_mul, norm_mul, Complex.norm_conj]
    _ = (‖klWeight f t‖ * ‖Complex.Gamma (2 + t * Complex.I) * Complex.Gamma (2 - t * Complex.I)‖) /
          ‖lineConst‖ * ∑ i, ‖eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n‖ *
          ‖eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m‖ *
          ‖whittMellin (((2 : ℝ) : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 := by
        rw [norm_besselPairMellin_line, Finset.mul_sum, Finset.mul_sum]
        congr 1; funext i; ring
    _ ≤ (DΓ * (1 + t ^ 2)⁻¹) / ‖lineConst‖ *
          ∑ i, ‖eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n‖ *
          ‖eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m‖ *
          ‖whittMellin (((2 : ℝ) : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hbΓ t) hκ0.le)
          (Finset.sum_nonneg fun i _ => by positivity)
    _ = _ := by ring

theorem aestronglyMeasurable_eisProduct (v w : DeckSpace N) (n m : ℤ)
    (i : Fin (Module.finrank ℂ (cuspVecSub N))) :
    AEStronglyMeasurable (fun r : ℝ => eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
      conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m)) volume :=
  (aestronglyMeasurable_eisCoeff_line v (cuspBasisVec N i) n).mul
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (aestronglyMeasurable_eisCoeff_line w (cuspBasisVec N i) m))

theorem aestronglyMeasurable_contIntegrand {f : ℝ → ℂ} (hf : IsKLTest f) (v w : DeckSpace N)
    (n m : ℤ) : AEStronglyMeasurable (contIntegrand f v w n m) (volume.prod volume) := by
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => klWeight f p.1) (volume.prod volume) :=
    ((continuous_klWeight hf).comp continuous_fst).aestronglyMeasurable
  have h2 : ∀ i : Fin (Module.finrank ℂ (cuspVecSub N)), AEStronglyMeasurable
      (fun p : ℝ × ℝ => eisCoeff (1 / 2 + p.2 * Complex.I) v (cuspBasisVec N i) n *
        conj (eisCoeff (1 / 2 + p.2 * Complex.I) w (cuspBasisVec N i) m) *
        besselPairMellin 2 p.1 (p.2 * Complex.I)) (volume.prod volume) := fun i =>
    ((aestronglyMeasurable_eisProduct v w n m i).comp_snd).mul
      continuous_besselPairMellin_line.aestronglyMeasurable
  have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => ∑ i,
      eisCoeff (1 / 2 + p.2 * Complex.I) v (cuspBasisVec N i) n *
        conj (eisCoeff (1 / 2 + p.2 * Complex.I) w (cuspBasisVec N i) m) *
        besselPairMellin 2 p.1 (p.2 * Complex.I)) (volume.prod volume) :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => h2 i
  exact h1.mul h3

theorem aestronglyMeasurable_contIntegrand_row {f : ℝ → ℂ} (v w : DeckSpace N) (n m : ℤ) (t : ℝ) :
    AEStronglyMeasurable (fun r => contIntegrand f v w n m (t, r)) volume := by
  have hc' := continuous_besselPairMellin_line.comp (by fun_prop : Continuous fun r : ℝ => (t, r))
  simp only [Function.comp_def] at hc'
  have h3 : AEStronglyMeasurable (fun r : ℝ => ∑ i,
      eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
        conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
        besselPairMellin 2 t (r * Complex.I)) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (aestronglyMeasurable_eisProduct v w n m i).mul hc'.aestronglyMeasurable
  exact (aestronglyMeasurable_const (b := klWeight f t)).mul h3

/-- **The continuous integrand is integrable on `ℝ²`.** -/
theorem integrable_contIntegrand (hN : 2 ≤ N) {f : ℝ → ℂ} (hf : IsKLTest f) {μ ν : ℝ} (hμ : 0 < μ)
    (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v) (hw : IsCuspEigen (-ν) w) {n m : ℤ}
    (hn : μ * ((N + 1 : ℕ) : ℝ) = n) (hm : -ν * ((N + 1 : ℕ) : ℝ) = m) :
    Integrable (contIntegrand f v w n m) (volume.prod volume) := by
  obtain ⟨DΓ, hDΓ, hbΓ⟩ := exists_bound_klWeight_mul_Gamma hf
  have hκ0 : 0 < ‖lineConst‖ := norm_pos_iff.2 lineConst_ne_zero
  have hc := fun t => integrable_and_integral_eisCoeff_line_le hN (σ := 2) (by norm_num) hμ hν hv hw
    hn hm t
  set D' : ℝ := Real.pi * ((‖v‖ * poincMajorantNorm 2 μ) ^ 2 + (‖w‖ * poincMajorantNorm 2 ν) ^ 2) /
    (2 * ((2 * Real.pi * μ) ^ (1 / 2 - (2 : ℝ)) * (2 * Real.pi * ν) ^ (1 / 2 - (2 : ℝ))))
  have hrow : ∀ t, Integrable (fun r => contIntegrand f v w n m (t, r)) := fun t =>
    ((hc t).1.const_mul (DΓ / ‖lineConst‖ * (1 + t ^ 2)⁻¹)).mono'
      (aestronglyMeasurable_contIntegrand_row v w n m t)
      (Eventually.of_forall fun r => norm_contIntegrand_le hbΓ v w n m t r)
  refine (integrable_prod_iff (aestronglyMeasurable_contIntegrand hf v w n m)).2
    ⟨Eventually.of_forall hrow, ?_⟩
  refine (integrable_inv_one_add_sq.const_mul (DΓ / ‖lineConst‖ * D')).mono'
    (aestronglyMeasurable_contIntegrand hf v w n m).norm.integral_prod_right'
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun r => norm_nonneg _)]
  calc ∫ r, ‖contIntegrand f v w n m (t, r)‖
      ≤ ∫ r, DΓ / ‖lineConst‖ * (1 + t ^ 2)⁻¹ * contMajorant v w n m t r :=
        integral_mono (hrow t).norm ((hc t).1.const_mul _) fun r => norm_contIntegrand_le hbΓ v w n m t r
    _ = DΓ / ‖lineConst‖ * (1 + t ^ 2)⁻¹ * ∫ r, contMajorant v w n m t r := integral_const_mul _ _
    _ ≤ DΓ / ‖lineConst‖ * (1 + t ^ 2)⁻¹ * D' := by gcongr; exact (hc t).2
    _ = DΓ / ‖lineConst‖ * D' * (1 + t ^ 2)⁻¹ := by ring

/-- **The continuous spectrum integrated against the weight.** -/
theorem integrable_and_integral_klWeight_mul_continuous (hN : 2 ≤ N) {f : ℝ → ℂ} (hf : IsKLTest f)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v)
    (hw : IsCuspEigen (-ν) w) {n m : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n)
    (hm : -ν * ((N + 1 : ℕ) : ℝ) = m) :
    Integrable (fun t : ℝ => klWeight f t * ∫ r : ℝ, ∑ i,
        eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
        conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
        besselPairMellin 2 t (r * Complex.I)) ∧
      ∫ t : ℝ, klWeight f t * ∫ r : ℝ, ∑ i,
          eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
          conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
          besselPairMellin 2 t (r * Complex.I) =
        ∫ r : ℝ, ∑ i, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
          conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
          ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * modifiedBesselKOrder x (2 * (r * Complex.I)) *
            (x * f x) := by
  have hint := integrable_contIntegrand hN hf hμ hν hv hw hn hm
  have hpt : ∀ t : ℝ, klWeight f t * ∫ r : ℝ, ∑ i,
      eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
      conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
      besselPairMellin 2 t (r * Complex.I) = ∫ r, contIntegrand f v w n m (t, r) := fun t => by
    rw [← integral_const_mul]; rfl
  simp_rw [hpt]
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [integral_integral_swap (f := fun t r => contIntegrand f v w n m (t, r)) hint]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  have hr : |((r : ℂ) * Complex.I).re| ≤ 1 / 2 := by simp
  unfold contIntegrand
  calc ∫ t, klWeight f t * ∑ i, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
        conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
        besselPairMellin 2 t (r * Complex.I)
      = ∫ t, ∑ i, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
          conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
          (klWeight f t * besselPairMellin 2 t (r * Complex.I)) := by
        congr 1; funext t; rw [Finset.mul_sum]; congr 1; funext i; ring
    _ = ∑ i, ∫ t, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
          conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
          (klWeight f t * besselPairMellin 2 t (r * Complex.I)) :=
        integral_finsetSum _ fun i _ => (integrable_klWeight_mul_besselPairMellin hf hr).const_mul _
    _ = _ := by
        congr 1; funext i
        rw [integral_const_mul, integral_klWeight_mul_besselPairMellin hf hr]

/-! ## The formula -/

/-- The Bessel transform `φ̌(ν) = ∫_0^∞ K_{2ν}(x) φ(x) dx/x`. -/
def besselTransform (φ : ℝ → ℂ) (ν : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), modifiedBesselKOrder x (2 * ν) * φ x / x

theorem lineScale_mul_cube {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) :
    ((4 * Real.pi ^ 2 * μ * ν : ℝ) : ℂ) ^ ((1 / 2 - 2 : ℝ) : ℂ) * (2 : ℂ) ^ ((3 - 2 * 2 : ℝ) : ℂ) *
      ((4 * Real.pi * Real.sqrt (μ * ν) : ℝ) : ℂ) ^ 3 = 4 := by
  set Y : ℝ := 2 * Real.pi * Real.sqrt (μ * ν)
  have hY : 0 < Y := by positivity
  have hsq : 4 * Real.pi ^ 2 * μ * ν = Y ^ 2 := by
    simp only [Y]; rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hsq, ← Complex.ofReal_cpow (by positivity), show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by norm_num), show 4 * Real.pi * Real.sqrt (μ * ν) = 2 * Y by
      simp only [Y]; ring]
  have h1 : (Y ^ 2) ^ (1 / 2 - 2 : ℝ) = (Y ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast Y 2, ← Real.rpow_mul hY.le, show ((2 : ℕ) : ℝ) * (1 / 2 - 2) = -(3 : ℕ) by
      norm_num, Real.rpow_neg hY.le, Real.rpow_natCast]
  have h2 : (2 : ℝ) ^ (3 - 2 * 2 : ℝ) = 1 / 2 := by
    rw [show (3 - 2 * 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]; norm_num
  rw [h1, h2]
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  push_cast
  field_simp
  ring

theorem integral_besselK_mul_f_eq {φ : ℝ → ℂ} (X : ℝ) (ν : ℂ) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * modifiedBesselKOrder x (2 * ν) *
        (x * (((X ^ 3 * (x ^ 4)⁻¹ : ℝ) : ℂ) * φ x)) =
      (X : ℂ) ^ 3 * besselTransform φ ν := by
  rw [besselTransform, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0 : ℝ) < x from hx))
  push_cast
  field_simp

/-- **Kuznetsov's formula for `S(m, −n)`** (Deshouillers–Iwaniec (1.20)). -/
theorem kuznetsov_opposite_sign (hN : 2 ≤ N) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    {v w : DeckSpace N} (hv : IsCuspEigen μ v) (hw : IsCuspEigen (-ν) w) {n m : ℤ}
    (hn : μ * ((N + 1 : ℕ) : ℝ) = n) (hm : -ν * ((N + 1 : ℕ) : ℝ) = m) {φ : ℝ → ℂ}
    (hφ : IsKLTest φ) :
    ∑' r : ReducedRow, rowWeight μ ν v w r.1 * ((|(r.1.1 0 : ℝ)| : ℝ) : ℂ)⁻¹ *
        φ (4 * Real.pi * Real.sqrt (μ * ν) / |(r.1.1 0 : ℝ)|) =
      4 * ∑' j : CuspEigenIndex N, cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) *
          besselTransform φ (specParam j.1) +
        (Real.pi : ℂ)⁻¹ * ∫ r : ℝ, ∑ i, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
          conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
          besselTransform φ (r * Complex.I) := by
  set X : ℝ := 4 * Real.pi * Real.sqrt (μ * ν)
  have hX : 0 < X := by positivity
  set f : ℝ → ℂ := fun x => ((X ^ 3 * (x ^ 4)⁻¹ : ℝ) : ℂ) * φ x
  have hf : IsKLTest f := IsKLTest.mul_contDiffOn hφ (contDiffOn_inv_pow_four X)
  -- the identity on the line, integrated against the weight
  have hline : ∀ t : ℝ, klWeight f t * ∑' r : ReducedRow, rowWeight μ ν v w r.1 *
      (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((2 : ℝ) : ℂ)) *
      modifiedBesselKOrder (2 * Real.sqrt (Kuznetsov.kuzParam μ ν ((r.1.1 0 : ℝ) ^ 2)))
        (2 * t * Complex.I) =
      ((4 * Real.pi ^ 2 * μ * ν : ℝ) : ℂ) ^ ((1 / 2 - 2 : ℝ) : ℂ) * (2 : ℂ) ^ ((3 - 2 * 2 : ℝ) : ℂ) *
        (klWeight f t * ∑' j : CuspEigenIndex N, cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) *
          besselPairMellin 2 t (specParam j.1) +
        (4 * Real.pi : ℂ)⁻¹ * (klWeight f t * ∫ r : ℝ, ∑ i,
          eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
          conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
          besselPairMellin 2 t (r * Complex.I))) := fun t => by
    rw [kuznetsov_bessel hN (σ := 2) (by norm_num) t hμ hν hv hw hn hm]
    ring
  obtain ⟨hdi, hdv⟩ := integrable_and_integral_klWeight_mul_discrete hf hμ hν hv hw
  obtain ⟨hci, hcv⟩ := integrable_and_integral_klWeight_mul_continuous hN hf hμ hν hv hw hn hm
  have hgeo := integral_klWeight_mul_rowSum hf hμ hν v w
  rw [integral_congr_ae (Eventually.of_forall hline), integral_const_mul,
    integral_add hdi (hci.const_mul _), integral_const_mul, hdv, hcv] at hgeo
  -- the geometric side
  have hrow : ∀ r : ReducedRow, rowWeight μ ν v w r.1 *
      (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((2 : ℝ) : ℂ)) *
      ((2 * Real.sqrt (Kuznetsov.kuzParam μ ν ((r.1.1 0 : ℝ) ^ 2)) : ℝ) *
        f (2 * Real.sqrt (Kuznetsov.kuzParam μ ν ((r.1.1 0 : ℝ) ^ 2)))) =
      rowWeight μ ν v w r.1 * ((|(r.1.1 0 : ℝ)| : ℝ) : ℂ)⁻¹ *
        φ (4 * Real.pi * Real.sqrt (μ * ν) / |(r.1.1 0 : ℝ)|) := fun r => by
    have hq := reducedRow_sq_pos r
    have hc0 : 0 < |(r.1.1 0 : ℝ)| := by
      have := one_le_abs_reducedRow r; linarith
    rw [two_sqrt_kuzParam hμ hν hq, Real.sqrt_sq_eq_abs]
    simp only [f]
    rw [show (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) = ((|(r.1.1 0 : ℝ)| : ℝ) : ℂ) ^ 2 by
      push_cast; rw [← Complex.ofReal_pow, sq_abs]; push_cast; ring]
    rw [show (-((2 : ℝ) : ℂ)) = ((-2 : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
    have hcC : ((|(r.1.1 0 : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have hs : (Real.sqrt (μ * ν) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (mul_pos hμ hν)).ne'
    have hπC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [X]
    push_cast
    field_simp
  rw [tsum_congr hrow] at hgeo
  rw [← hgeo]
  -- the spectral side
  have hd : ∀ j : CuspEigenIndex N, cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) *
      ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * modifiedBesselKOrder x (2 * specParam j.1) * (x * f x) =
      (X : ℂ) ^ 3 * (cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) *
        besselTransform φ (specParam j.1)) := fun j => by
    rw [integral_besselK_mul_f_eq X]; ring
  have hc : ∀ r : ℝ, ∑ i, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
      conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
      ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * modifiedBesselKOrder x (2 * (r * Complex.I)) * (x * f x) =
      (X : ℂ) ^ 3 * ∑ i, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
        conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
        besselTransform φ (r * Complex.I) := fun r => by
    rw [Finset.mul_sum]; congr 1; funext i; rw [integral_besselK_mul_f_eq X]; ring
  rw [tsum_congr hd, tsum_mul_left, integral_congr_ae (Eventually.of_forall hc), integral_const_mul]
  have hL := lineScale_mul_cube hμ hν
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  linear_combination (∑' j : CuspEigenIndex N, cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) *
      besselTransform φ (specParam j.1) + (4 * Real.pi : ℂ)⁻¹ * ∫ r : ℝ, ∑ i,
      eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
      conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
      besselTransform φ (r * Complex.I)) * hL

end

end GaloisForLFunctions.RHTower.DeckPointPair
