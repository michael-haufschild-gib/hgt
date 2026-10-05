import GaloisForLFunctions.RHTower.RieszFunctionExponentLaw
import GaloisForLFunctions.RHTower.MertensSquareRootOmega

/-!
# The Riesz function is `Ω±(x^{1/4})`

Let `F(x) = x Σ_n μ(n) n^{-2} e^{-x/n²}` be Riesz's function and `Z(w) = (w-1)ζ(w)`.  The trivial
Mertens bound gives `|F(x)| ≤ K x^{3/4}`, and in the logarithmic variable, for `¾ < Re z < 1`,
`∫_0^∞ F(e^t) e^{-zt} dt = Ψ(z) := Γ(1-z)(2z-1)/Z(2z) - ∫_0^1 R(x) x^{-z} dx`.  The right side is
holomorphic on `¼ < Re z < 1` away from the zeros of `Z(2z)`, and real-analytic on `(¼, 1)`.

Suppose `ηF(x) ≤ ε' x^{1/4}` for large `x`, `η = ±1`.  For `ε > ε'` the density
`ε e^{t/4} - ηF(e^t) + K` is at least `(ε - ε')e^{t/4}` on `(0, ∞)`, so its Laplace transform has
abscissa at least `¼`, at most `¾`; its transform is `ε/(z-¼) + K/z - ηΨ(z)`, analytic at every
real point of `(¼, 1)`, so Landau's theorem puts the abscissa at `¼`.  With
`H(z) = ε/(z-¼) + K/z - ∫ e^{-zt} dν` the identity theorem gives on `¼ < Re z < 1`
`H(z) Z(2z) = η(Γ(1-z)(2z-1) - I₀(z) Z(2z))`.

A zero `ρ` with `½ < Re ρ < 1` would make the left side vanish at `z = ρ/2` while the right side
equals `ηΓ(1-ρ/2)(ρ-1) ≠ 0`: a one-sided bound implies RH.  At a zero `ρ = ½ + iγ` (Hardy's
theorem supplies one) write `Z(v) = (v-ρ)^m G(v)`.  Along `z = ρ/2 + r`, `r ↓ 0`, nonnegativity
gives `|∫ e^{-zt} dν| ≤ ε/r + O(1)`, so `r^m|H + ηI₀| ≤ r^{m-1}(ε + O(r))`, while
`(2r)^m|G||H + ηI₀| = |Γ(1-z)||2z-1|`.  Hence `m = 1` and `|Γ(1-ρ/2)||ρ-1| ≤ 2ε'|G(ρ)|`;
choosing `ε'` below this threshold gives `F(x) = Ω±(x^{1/4})`.
-/

open Complex Filter MeasureTheory Set Asymptotics
open scoped Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## A priori growth -/

/-- **A priori decay of the Riesz series.**  From the trivial bound `|M(N)| ≤ N + 1`,
`|R(x)| ≤ K x^{-1/4}` for `x > 0`. -/
theorem exists_abs_rieszSeries_le_rpow :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → |rieszSeries x| ≤ K * x ^ (-(1 / 4 : ℝ)) := by
  have hM : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ 1 * ((N : ℝ) + 1) ^ (1 : ℝ) := by
    intro N
    rw [one_mul, Real.rpow_one, mobiusMertensPartialSum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.range (N + 1), ‖mobiusComplexCoefficient n‖
        ≤ ∑ _n ∈ Finset.range (N + 1), (1 : ℝ) := Finset.sum_le_sum fun n _ => by
          rw [mobiusComplexCoefficient, Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = (N : ℝ) + 1 := by simp
  obtain ⟨K, hK0, hK⟩ := abs_rieszSeries_le_of_mertens_bound (a := 1) (δ := 1 / 2) zero_le_one
    (by norm_num) (by norm_num) zero_le_one hM
  refine ⟨K, hK0, fun x hx => (hK x hx).trans_eq ?_⟩
  norm_num

/-- `|F(e^t)| ≤ K e^{3t/4}`. -/
theorem exists_abs_rieszFunction_exp_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |rieszFunction (Real.exp t)| ≤ K * Real.exp (3 / 4 * t) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_rieszSeries_le_rpow
  refine ⟨K, hK0, fun t => ?_⟩
  have hx := Real.exp_pos t
  rw [rieszFunction, abs_mul, abs_of_pos hx]
  calc Real.exp t * |rieszSeries (Real.exp t)| ≤ Real.exp t * (K * Real.exp t ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hK _ hx) hx.le
    _ = K * Real.exp (3 / 4 * t) := by
        rw [← Real.exp_mul, mul_left_comm, ← Real.exp_add]; ring_nf

theorem continuous_rieszFunction_exp : Continuous fun t : ℝ => rieszFunction (Real.exp t) := by
  unfold rieszFunction
  exact Real.continuous_exp.mul (continuousOn_rieszSeries.comp_continuous Real.continuous_exp
    fun t => (Real.exp_pos t).le)

/-! ## The head of the Mellin transform -/

/-- The part of the Riesz series on `(0, 1]`. -/
def rieszHeadPart (x : ℝ) : ℂ := Set.indicator (Ioc 0 1) (fun y => ((rieszSeries y : ℝ) : ℂ)) x

/-- `I₀(z) = ∫_0^1 R(x) x^{-z} dx`, as a Mellin transform at `1 - z`. -/
def rieszHead (z : ℂ) : ℂ := mellin rieszHeadPart (1 - z)

theorem integrableOn_rieszSeries_Ioc :
    IntegrableOn (fun y => ((rieszSeries y : ℝ) : ℂ)) (Ioc 0 1) := by
  have hc : ContinuousOn (fun y => ((rieszSeries y : ℝ) : ℂ)) (Icc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_rieszSeries.mono Icc_subset_Ici_self)
  exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

theorem norm_rieszHeadPart_le (x : ℝ) : ‖rieszHeadPart x‖ ≤ ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
  unfold rieszHeadPart
  by_cases hx : x ∈ Ioc 0 1
  · rw [indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs]
    exact abs_rieszSeries_le hx.1.le
  · rw [indicator_of_notMem hx, norm_zero]
    exact tsum_nonneg fun n => by positivity

/-- The head transform is holomorphic on `-1 < Re z < 1`. -/
theorem differentiableAt_rieszHead {z : ℂ} (hz1 : z.re < 1) (hz0 : -1 < z.re) :
    DifferentiableAt ℂ rieszHead z := by
  have hm : DifferentiableAt ℂ (mellin rieszHeadPart) (1 - z) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 2) (b := 0) ?_ ?_ ?_ ?_ ?_
    · exact (integrableOn_rieszSeries_Ioc.integrable_indicator measurableSet_Ioc
        ).locallyIntegrable.locallyIntegrableOn _
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [eventually_gt_atTop 1] with x hx
      simp [rieszHeadPart, indicator_of_notMem (show x ∉ Ioc 0 1 from fun h => by
        linarith [h.2])]
    · simp; linarith
    · refine IsBigO.of_bound (∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
      exact norm_rieszHeadPart_le x
    · simp; linarith
  exact hm.comp z ((differentiableAt_const _).sub differentiableAt_id)

/-! ## The transform in the logarithmic variable -/

theorem mellinConvergent_rieszSeries {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 4) :
    MellinConvergent (fun y => ((rieszSeries y : ℝ) : ℂ)) s := by
  obtain ⟨K, _, hK⟩ := exists_abs_rieszSeries_le_rpow
  refine mellinConvergent_of_isBigO_rpow (a := 1 / 4) (b := 0) ?_ ?_ hs1 ?_ hs0
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_rieszSeries.mono Ioi_subset_Ici_self)).locallyIntegrableOn measurableSet_Ioi
  · refine IsBigO.of_bound K ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hx _)]
    exact hK x hx
  · refine IsBigO.of_bound (∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [Complex.norm_real, Real.norm_eq_abs, neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact abs_rieszSeries_le hx0.le

/-- **The Riesz function in the logarithmic variable.**  For `3/4 < Re z < 1`,
`∫_0^∞ F(e^t) e^{-zt} dt = Γ(1-z) Σ_n μ(n) n^{-2z} - ∫_0^1 R(x) x^{-z} dx`. -/
theorem integral_rieszFunction_exp_mul_cexp {z : ℂ} (h1 : 3 / 4 < z.re) (h2 : z.re < 1) :
    ∫ t in Ioi (0 : ℝ), ((rieszFunction (Real.exp t) : ℝ) : ℂ) * cexp (-z * t) =
      Complex.Gamma (1 - z) * LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        (2 * z) - rieszHead z := by
  set f : ℝ → ℂ := fun y => ((rieszSeries y : ℝ) : ℂ) with hf
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (1 - z - 1) • f t with hg
  have hre0 : 0 < (1 - z).re := by simp; linarith
  have hconv : IntegrableOn g (Ioi 0) := mellinConvergent_rieszSeries hre0 (by simp; linarith)
  have hmel := mellin_rieszSeries hre0 (by simp; linarith)
  rw [show 2 - 2 * (1 - z) = 2 * z by ring] at hmel
  have hsplit : mellin f (1 - z) = (∫ t in Ioc (0 : ℝ) 1, g t) + ∫ t in Ioi (1 : ℝ), g t := by
    rw [mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact setIntegral_union (disjoint_left.mpr fun x hx hx' => by
      have : (1 : ℝ) < x := hx'; linarith [hx.2]) measurableSet_Ioi
      (hconv.mono_set Ioc_subset_Ioi_self) (hconv.mono_set (Ioi_subset_Ioi zero_le_one))
  have hhead : rieszHead z = ∫ t in Ioc (0 : ℝ) 1, g t := by
    rw [rieszHead, mellin]
    have : (fun t : ℝ => (t : ℂ) ^ (1 - z - 1) • rieszHeadPart t) =
        Set.indicator (Ioc 0 1) g := by
      funext t
      rw [rieszHeadPart, hg]
      by_cases ht : t ∈ Ioc (0 : ℝ) 1
      · rw [indicator_of_mem ht, indicator_of_mem ht]
      · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
    rw [this, setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr Ioc_subset_Ioi_self]
  have htail : ∫ t in Ioi (1 : ℝ), g t =
      ∫ t in Ioi (0 : ℝ), ((rieszFunction (Real.exp t) : ℝ) : ℂ) * cexp (-z * t) := by
    rw [← image_exp_Ioi_zero, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hcpow : ((Real.exp u : ℝ) : ℂ) ^ (1 - z - 1) = cexp (u * (1 - z - 1)) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
        ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    simp only [hg, hf]
    rw [abs_of_pos (Real.exp_pos u), hcpow, Complex.real_smul, smul_eq_mul, rieszFunction,
      Complex.ofReal_mul, Complex.ofReal_exp]
    rw [show (u : ℂ) * (1 - z - 1) = -z * u by ring]
    ring
  rw [← htail, hhead, ← hmel]
  have := hsplit
  simp only [hf] at this
  rw [this]
  ring

/-! ## The continuation kernel -/

/-- `Ψ(z) = Γ(1-z)(2z-1)/((2z-1)ζ(2z)) - I₀(z)`, the continuation of `∫_0^∞ F(e^t)e^{-zt} dt`. -/
def rieszLogKernel (z : ℂ) : ℂ :=
  Complex.Gamma (1 - z) * (2 * z - 1) / zetaResidueUnit (2 * z) - rieszHead z

theorem LSeries_moebius_eq_div_zetaResidueUnit {w : ℂ} (hw : 1 < w.re) :
    LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) w =
      (w - 1) / zetaResidueUnit w := by
  have hw1 : w ≠ 1 := by intro h; rw [h, Complex.one_re] at hw; exact lt_irrefl _ hw
  have hL := LSeries_moebius_mul_riemannZeta hw
  have hζ : riemannZeta w ≠ 0 := right_ne_zero_of_mul_eq_one hL
  rw [zetaResidueUnit, Function.update_of_ne hw1, eq_div_iff (mul_ne_zero (sub_ne_zero.mpr hw1) hζ)]
  linear_combination (w - 1) * hL

theorem integral_rieszFunction_exp_mul_cexp_eq_rieszLogKernel {z : ℂ} (h1 : 3 / 4 < z.re)
    (h2 : z.re < 1) :
    ∫ t in Ioi (0 : ℝ), ((rieszFunction (Real.exp t) : ℝ) : ℂ) * cexp (-z * t) =
      rieszLogKernel z := by
  rw [integral_rieszFunction_exp_mul_cexp h1 h2, rieszLogKernel,
    LSeries_moebius_eq_div_zetaResidueUnit (by simp; linarith)]
  ring

theorem analyticAt_complexGamma_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ Complex.Gamma w := by
  have hU : IsOpen {v : ℂ | 0 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticAt (s := {v : ℂ | 0 < v.re}) (fun v hv => ?_) (hU.mem_nhds hw)
  refine (Complex.differentiableAt_Gamma v fun m hm => ?_).differentiableWithinAt
  have : v.re = -(m : ℝ) := by rw [hm]; simp
  have hv' : 0 < v.re := hv
  linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

theorem analyticAt_rieszHead {z : ℂ} (hz1 : z.re < 1) (hz0 : -1 < z.re) :
    AnalyticAt ℂ rieszHead z := by
  have hU : IsOpen {v : ℂ | v.re < 1 ∧ -1 < v.re} :=
    (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  exact DifferentiableOn.analyticAt (s := {v : ℂ | v.re < 1 ∧ -1 < v.re})
    (fun v hv => (differentiableAt_rieszHead hv.1 hv.2).differentiableWithinAt)
    (hU.mem_nhds ⟨hz1, hz0⟩)

theorem analyticAt_rieszLogKernel {z : ℂ} (hz1 : z.re < 1) (hz0 : -1 < z.re)
    (hZ : zetaResidueUnit (2 * z) ≠ 0) : AnalyticAt ℂ rieszLogKernel z := by
  have hG : AnalyticAt ℂ (fun v : ℂ => Complex.Gamma (1 - v)) z :=
    (analyticAt_complexGamma_of_re_pos (by simp; linarith)).comp
      (analyticAt_const.sub analyticAt_id)
  have hZa : AnalyticAt ℂ (fun v : ℂ => zetaResidueUnit (2 * v)) z :=
    (analyticAt_zetaResidueUnit _).comp (analyticAt_const.mul analyticAt_id)
  exact ((hG.mul ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)).div hZa hZ).sub
    (analyticAt_rieszHead hz1 hz0)

/-! ## The one-sided measure -/

/-- The clipped density `ε e^{t/4} - ηF(e^t) + K`. -/
def rieszDensity (η ε K : ℝ) (t : ℝ) : NNReal :=
  Real.toNNReal (ε * Real.exp (t / 4) - η * rieszFunction (Real.exp t) + K)

theorem measurable_rieszDensity (η ε K : ℝ) : Measurable (rieszDensity η ε K) := by
  unfold rieszDensity
  refine Measurable.real_toNNReal ?_
  refine Measurable.add (Measurable.sub ?_ ?_) measurable_const
  · exact measurable_const.mul (Real.measurable_exp.comp (measurable_id.div_const 4))
  · exact measurable_const.mul continuous_rieszFunction_exp.measurable

/-- `ν = (ε e^{t/4} - ηF(e^t) + K) dt` on `(0, ∞)`. -/
def rieszOmegaMeasure (η ε K : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun u => (rieszDensity η ε K u : ENNReal))

theorem exists_rieszDensity_le {η ε K : ℝ} (hη : |η| = 1) (hε : 0 ≤ ε) (hK : 0 ≤ K) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ((rieszDensity η ε K t : ℝ)) ≤ C * Real.exp (3 / 4 * t) := by
  obtain ⟨K₀, hK₀, hF⟩ := exists_abs_rieszFunction_exp_le
  refine ⟨ε + K + K₀, fun t ht => ?_⟩
  unfold rieszDensity
  rw [Real.coe_toNNReal']
  have h1 : Real.exp (t / 4) ≤ Real.exp (3 / 4 * t) := Real.exp_le_exp.mpr (by linarith)
  have h2 : -(η * rieszFunction (Real.exp t)) ≤ K₀ * Real.exp (3 / 4 * t) := by
    have h3 : |η * rieszFunction (Real.exp t)| ≤ K₀ * Real.exp (3 / 4 * t) := by
      rw [abs_mul, hη, one_mul]; exact hF t
    linarith [neg_abs_le (η * rieszFunction (Real.exp t))]
  have h4 : 1 ≤ Real.exp (3 / 4 * t) := Real.one_le_exp (by linarith)
  have hE := Real.exp_pos (3 / 4 * t)
  refine max_le ?_ (by positivity)
  nlinarith

theorem rieszDensity_coe {η ε ε' K : ℝ} (hεε' : ε' ≤ ε)
    (hg : ∀ t, 0 < t → η * rieszFunction (Real.exp t) ≤ ε' * Real.exp (t / 4) + K) {t : ℝ}
    (ht : 0 < t) :
    ((rieszDensity η ε K t : ℝ)) = ε * Real.exp (t / 4) - η * rieszFunction (Real.exp t) + K := by
  unfold rieszDensity
  have h := hg t ht
  have hE := Real.exp_pos (t / 4)
  rw [Real.coe_toNNReal _ (by nlinarith)]

theorem laplaceMass_rieszOmegaMeasure_ne_top {η ε K σ : ℝ} (hη : |η| = 1) (hε : 0 ≤ ε)
    (hK : 0 ≤ K) (hσ : 3 / 4 < σ) : laplaceMass (rieszOmegaMeasure η ε K) σ ≠ ⊤ := by
  obtain ⟨C, hC⟩ := exists_rieszDensity_le hη hε hK
  unfold laplaceMass rieszOmegaMeasure
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_rieszDensity η ε K).coe_nnreal_ennreal hg]
  have hmaj : IntegrableOn (fun u : ℝ => C * Real.exp (3 / 4 * u) * Real.exp (-σ * u)) (Ioi 0) := by
    have h := (exp_neg_integrableOn_Ioi 0 (by linarith : (0 : ℝ) < σ - 3 / 4)).const_mul C
    refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  refine ne_top_of_le_ne_top hmaj.lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (hC u hu) (Real.exp_pos _).le

theorem laplaceMass_rieszOmegaMeasure_eq_top {η ε ε' K σ : ℝ} (hεε' : ε' < ε)
    (hg : ∀ t, 0 < t → η * rieszFunction (Real.exp t) ≤ ε' * Real.exp (t / 4) + K)
    (hσ : σ ≤ 1 / 4) : laplaceMass (rieszOmegaMeasure η ε K) σ = ⊤ := by
  unfold laplaceMass rieszOmegaMeasure
  have hg' : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_rieszDensity η ε K).coe_nnreal_ennreal hg', eq_top_iff]
  have hδ : 0 < ε - ε' := by linarith
  calc (⊤ : ENNReal) = ENNReal.ofReal (ε - ε') * volume (Ioi (0 : ℝ)) := by
        rw [Real.volume_Ioi, ENNReal.mul_top (by simpa using hδ)]
    _ = ∫⁻ _ in Ioi (0 : ℝ), ENNReal.ofReal (ε - ε') := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), ((fun u => (rieszDensity η ε K u : ENNReal))
          * fun u => ENNReal.ofReal (Real.exp (-σ * u))) u := by
        refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := hu
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [rieszDensity_coe hεε'.le hg hu0]
        have h1 := hg u hu0
        have h2 : 1 ≤ Real.exp (u / 4) * Real.exp (-σ * u) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        have hE := Real.exp_pos (-σ * u)
        have hE2 := Real.exp_pos (u / 4)
        have h3 : (ε - ε') * Real.exp (u / 4) ≤ ε * Real.exp (u / 4)
            - η * rieszFunction (Real.exp u) + K := by linarith
        calc ε - ε' ≤ (ε - ε') * (Real.exp (u / 4) * Real.exp (-σ * u)) :=
              le_mul_of_one_le_right hδ.le h2
          _ = (ε - ε') * Real.exp (u / 4) * Real.exp (-σ * u) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h3 hE.le

/-- The abscissa of `ν` lies in `[¼, ¾]`. -/
theorem isAbscissa_rieszOmegaMeasure {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε')
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * rieszFunction (Real.exp t) ≤ ε' * Real.exp (t / 4) + K) :
    IsAbscissa (rieszOmegaMeasure η ε K)
        (sInf {σ : ℝ | laplaceMass (rieszOmegaMeasure η ε K) σ ≠ ⊤})
      ∧ 1 / 4 ≤ sInf {σ : ℝ | laplaceMass (rieszOmegaMeasure η ε K) σ ≠ ⊤}
      ∧ sInf {σ : ℝ | laplaceMass (rieszOmegaMeasure η ε K) σ ≠ ⊤} ≤ 3 / 4 := by
  have hε : 0 ≤ ε := by linarith
  set S := {σ : ℝ | laplaceMass (rieszOmegaMeasure η ε K) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, 1 / 4 < σ := by
    intro σ hσ
    by_contra hle
    exact hσ (laplaceMass_rieszOmegaMeasure_eq_top hεε' hg (not_lt.mp hle))
  have hbdd : BddBelow S := ⟨1 / 4, fun σ hσ => (hpos σ hσ).le⟩
  have hmem : ∀ δ : ℝ, 0 < δ → 3 / 4 + δ ∈ S := fun δ hδ =>
    laplaceMass_rieszOmegaMeasure_ne_top hη hε hK (by linarith)
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le,
    le_of_forall_pos_le_add fun δ hδ => csInf_le hbdd (hmem δ hδ)⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The transform and Landau's theorem -/

/-- The continuation `Φ(z) = ε/(z-¼) + K/z - ηΨ(z)`. -/
def rieszContinuation (η ε K : ℝ) (z : ℂ) : ℂ := ε / (z - 1 / 4) + K / z - η * rieszLogKernel z

theorem analyticAt_rieszContinuation (η ε K : ℝ) {z : ℂ} (hzq : z ≠ 1 / 4) (hz0 : z ≠ 0)
    (hz1 : z.re < 1) (hzm : -1 < z.re) (hZ : zetaResidueUnit (2 * z) ≠ 0) :
    AnalyticAt ℂ (rieszContinuation η ε K) z := by
  unfold rieszContinuation
  exact ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzq)).add
    (analyticAt_const.div analyticAt_id hz0)).sub
    (analyticAt_const.mul (analyticAt_rieszLogKernel hz1 hzm hZ))

/-- On `¾ < Re s < 1` the complex transform of `ν` is `Φ(s)`. -/
theorem complexLaplace_rieszOmegaMeasure_eq {η ε ε' K : ℝ} (hεε' : ε' ≤ ε)
    (hg : ∀ t, 0 < t → η * rieszFunction (Real.exp t) ≤ ε' * Real.exp (t / 4) + K)
    {s : ℂ} (hs1 : 3 / 4 < s.re) (hs2 : s.re < 1) :
    complexLaplace (rieszOmegaMeasure η ε K) s = rieszContinuation η ε K s := by
  obtain ⟨K₀, _, hF⟩ := exists_abs_rieszFunction_exp_le
  have hs0 : 0 < s.re := by linarith
  have hsh : 0 < (s - 1 / 4).re := by simp; linarith
  have hcexp : ∀ w : ℂ, Continuous (fun u : ℝ => Complex.exp (-w * (u : ℂ))) := fun w =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hexpInt : ∀ w : ℂ, 0 < w.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-w * (u : ℂ))) (Ioi 0) := fun w hw =>
    (exp_neg_integrableOn_Ioi 0 hw).mono' (hcexp w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  have hFint : IntegrableOn
      (fun u : ℝ => ((rieszFunction (Real.exp u) : ℝ) : ℂ) * Complex.exp (-s * u)) (Ioi 0) := by
    have hmaj : IntegrableOn (fun u : ℝ => K₀ * Real.exp (-(s.re - 3 / 4) * u)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul K₀
    refine hmaj.mono' ?_ ?_
    · exact (Complex.continuous_ofReal.comp continuous_rieszFunction_exp).aestronglyMeasurable.mul
        (hcexp s).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u _
      rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |rieszFunction (Real.exp u)| * Real.exp (-s.re * u)
          ≤ K₀ * Real.exp (3 / 4 * u) * Real.exp (-s.re * u) :=
            mul_le_mul_of_nonneg_right (hF u) (Real.exp_pos _).le
        _ = K₀ * Real.exp (-(s.re - 3 / 4) * u) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
  unfold complexLaplace rieszOmegaMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integral_withDensity_eq_integral_smul (measurable_rieszDensity η ε K)]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), rieszDensity η ε K u • Complex.exp (-s * (u : ℂ))
      = ((ε : ℂ) * Complex.exp (-(s - 1 / 4) * (u : ℂ)) + (K : ℂ) * Complex.exp (-s * (u : ℂ)))
        - (η : ℂ) * (((rieszFunction (Real.exp u) : ℝ) : ℂ) * Complex.exp (-s * u)) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul, rieszDensity_coe hεε' hg hu]
    push_cast
    rw [show Complex.exp (-(s - 1 / 4) * (u : ℂ))
      = Complex.exp ((u : ℂ) / 4) * Complex.exp (-s * (u : ℂ)) by
        rw [← Complex.exp_add]; congr 1; ring]
    ring
  have i1 : IntegrableOn (fun u : ℝ => (ε : ℂ) * Complex.exp (-(s - 1 / 4) * (u : ℂ))) (Ioi 0) :=
    (hexpInt _ hsh).const_mul _
  have i2 : IntegrableOn (fun u : ℝ => (K : ℂ) * Complex.exp (-s * (u : ℂ))) (Ioi 0) :=
    (hexpInt _ hs0).const_mul _
  have i3 : IntegrableOn (fun u : ℝ => (η : ℂ) * (((rieszFunction (Real.exp u) : ℝ) : ℂ)
      * Complex.exp (-s * u))) (Ioi 0) := hFint.const_mul _
  have i12 : IntegrableOn (fun u : ℝ => (ε : ℂ) * Complex.exp (-(s - 1 / 4) * (u : ℂ))
      + (K : ℂ) * Complex.exp (-s * (u : ℂ))) (Ioi 0) := i1.add i2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_cexp_neg_mul_Ioi hsh,
    integral_cexp_neg_mul_Ioi hs0, integral_rieszFunction_exp_mul_cexp_eq_rieszLogKernel hs1 hs2]
  unfold rieszContinuation
  ring

theorem zetaResidueUnit_two_mul_ofReal_ne_zero {t : ℝ} (ht : 0 < t) :
    zetaResidueUnit (2 * (t : ℂ)) ≠ 0 := by
  have := zetaResidueUnit_ofReal_ne_zero (by linarith : 0 < 2 * t)
  push_cast at this
  exact this

/-- **Landau: the abscissa of `ν` is `¼`.** -/
theorem abscissa_rieszOmegaMeasure_eq {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε')
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * rieszFunction (Real.exp t) ≤ ε' * Real.exp (t / 4) + K) :
    IsAbscissa (rieszOmegaMeasure η ε K) (1 / 4) := by
  obtain ⟨hc, hac, hc34⟩ := isAbscissa_rieszOmegaMeasure hη hε' hεε' hK hg
  set c : ℝ := sInf {σ : ℝ | laplaceMass (rieszOmegaMeasure η ε K) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hcpos : 0 < c := by linarith
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hcq : (c : ℂ) ≠ 1 / 4 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hZ : zetaResidueUnit (2 * (c : ℂ)) ≠ 0 := zetaResidueUnit_two_mul_ofReal_ne_zero hcpos
    have hZc : ContinuousAt (fun z : ℂ => zetaResidueUnit (2 * z)) (c : ℂ) :=
      ((analyticAt_zetaResidueUnit _).comp (analyticAt_const.mul analyticAt_id)).continuousAt
    have hre1 : ∀ᶠ z in 𝓝 (c : ℂ), z.re < 1 :=
      Complex.continuous_re.continuousAt.eventually_lt continuousAt_const (by simp; linarith)
    have hrem : ∀ᶠ z in 𝓝 (c : ℂ), -1 < z.re :=
      continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (by simp; linarith)
    have hev : ∀ᶠ z in 𝓝 (c : ℂ), (zetaResidueUnit (2 * z) ≠ 0 ∧ z ≠ 0 ∧ z ≠ 1 / 4) ∧
        (z.re < 1 ∧ -1 < z.re) :=
      ((hZc.eventually_ne hZ).and ((eventually_ne_nhds hc0).and (eventually_ne_nhds hcq))).and
        (hre1.and hrem)
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
    set d' : ℝ := min d (1 / 8) with hd'
    have hd'0 : 0 < d' := lt_min hd (by norm_num)
    refine false_of_analyticAt_abscissa hc hd'0 (Φ := rieszContinuation η ε K) ?_ ?_
    · intro z hz
      obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hball (lt_of_lt_of_le hz (min_le_left _ _))
      exact analyticAt_rieszContinuation η ε K h3 h2 h4 h5 h1
    · intro σ hσc hσd
      have hσ1 : σ < 1 := by
        have : d' ≤ 1 / 8 := min_le_right _ _
        linarith
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (rieszOmegaMeasure η ε K))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ
          (fun t : ℝ => complexLaplace (rieszOmegaMeasure η ε K) (t : ℂ)) (Ioo c 1) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (rieszOmegaMeasure η ε K)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht.1))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => rieszContinuation η ε K (t : ℂ)) (Ioo c 1) := by
        intro t ht
        have htq : 1 / 4 < t := lt_trans hpos ht.1
        have ht0 : 0 < t := by linarith
        have h1 : AnalyticAt ℂ (rieszContinuation η ε K) (t : ℂ) := by
          refine analyticAt_rieszContinuation η ε K ?_ (by exact_mod_cast ht0.ne')
            (by simpa using ht.2) (by simp; linarith)
            (zetaResidueUnit_two_mul_ofReal_ne_zero ht0)
          intro h
          have := congrArg Complex.re h
          simp at this
          linarith
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h78 : (7 / 8 : ℝ) ∈ Ioo c 1 := ⟨by linarith, by norm_num⟩
      have hfg : (fun t : ℝ => complexLaplace (rieszOmegaMeasure η ε K) (t : ℂ)) =ᶠ[𝓝 (7 / 8 : ℝ)]
          (fun t : ℝ => rieszContinuation η ε K (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (13 / 16 : ℝ) < 7 / 8)
            (by norm_num : (7 / 8 : ℝ) < 15 / 16)) fun t ht => ?_
        exact complexLaplace_rieszOmegaMeasure_eq hεε'.le hg (by simp; linarith [ht.1])
          (by simp; linarith [ht.2])
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioo h78 hfg
      have hσ : complexLaplace (rieszOmegaMeasure η ε K) (σ : ℂ)
          = rieszContinuation η ε K (σ : ℂ) := heq (show σ ∈ Ioo c 1 from ⟨hσc, hσ1⟩)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- **The continuation identity on `¼ < Re z < 1`.**  With
`H(z) = ε/(z-¼) + K/z - ∫ e^{-zt} dν`, `H(z)·Z(2z) = η(Γ(1-z)(2z-1) - I₀(z) Z(2z))`, where
`Z(w) = (w-1)ζ(w)`. -/
theorem riesz_continuation_identity {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε')
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * rieszFunction (Real.exp t) ≤ ε' * Real.exp (t / 4) + K)
    {z : ℂ} (hz1 : 1 / 4 < z.re) (hz2 : z.re < 1) :
    (ε / (z - 1 / 4) + K / z - complexLaplace (rieszOmegaMeasure η ε K) z)
      * zetaResidueUnit (2 * z) =
      η * (Complex.Gamma (1 - z) * (2 * z - 1) - rieszHead z * zetaResidueUnit (2 * z)) := by
  have hc := abscissa_rieszOmegaMeasure_eq hη hε' hεε' hK hg
  set U : Set ℂ := {w : ℂ | 1 / 4 < w.re ∧ w.re < 1} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).isPreconnected
  have hne0 : ∀ w ∈ U, w ≠ 0 := fun w hw h => by
    rw [h] at hw; norm_num [hU] at hw
  have hneq : ∀ w ∈ U, w - 1 / 4 ≠ 0 := fun w hw h => by
    have h1 := congrArg Complex.re h
    have h2 : 1 / 4 < w.re := hw.1
    simp at h1; linarith
  set F : ℂ → ℂ := fun w => (ε / (w - 1 / 4) + K / w
    - complexLaplace (rieszOmegaMeasure η ε K) w) * zetaResidueUnit (2 * w) with hF
  set G : ℂ → ℂ := fun w => (η : ℂ) *
    (Complex.Gamma (1 - w) * (2 * w - 1) - rieszHead w * zetaResidueUnit (2 * w)) with hG
  have hZa : ∀ w, AnalyticAt ℂ (fun v : ℂ => zetaResidueUnit (2 * v)) w := fun w =>
    (analyticAt_zetaResidueUnit _).comp (analyticAt_const.mul analyticAt_id)
  have hFa : AnalyticOnNhd ℂ F U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (ε : ℂ) / (w - 1 / 4)) w :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
        (hneq w hw)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (K : ℂ) / w) w :=
      (differentiableAt_const _).div differentiableAt_id (hne0 w hw)
    have h3 := (hasDerivAt_complexLaplace hc hw.1).differentiableAt
    exact (((h1.add h2).sub h3).mul (hZa w).differentiableAt).differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ G U := fun w hw => by
    have hΓ : AnalyticAt ℂ (fun v : ℂ => Complex.Gamma (1 - v)) w :=
      (analyticAt_complexGamma_of_re_pos (by simp; linarith [hw.2])).comp
        (analyticAt_const.sub analyticAt_id)
    exact analyticAt_const.mul ((hΓ.mul ((analyticAt_const.mul analyticAt_id).sub
      analyticAt_const)).sub ((analyticAt_rieszHead hw.2 (by linarith [hw.1])).mul (hZa w)))
  have h78 : ((7 / 8 : ℝ) : ℂ) ∈ U := ⟨by simp; norm_num, by simp; norm_num⟩
  have hev : F =ᶠ[𝓝 ((7 / 8 : ℝ) : ℂ)] G := by
    have hopen : IsOpen {w : ℂ | 3 / 4 < w.re ∧ w.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds (show ((7 / 8 : ℝ) : ℂ) ∈ {w : ℂ | 3 / 4 < w.re ∧ w.re < 1}
      from ⟨by simp; norm_num, by simp; norm_num⟩)] with w hw
    have hw1 : 1 < (2 * w).re := by simp; linarith [hw.1]
    have h2w : 2 * w ≠ 1 := by intro h; rw [h, Complex.one_re] at hw1; linarith
    have hZ : zetaResidueUnit (2 * w) ≠ 0 := by
      rw [zetaResidueUnit, Function.update_of_ne h2w]
      exact mul_ne_zero (sub_ne_zero.mpr h2w) (riemannZeta_ne_zero_of_one_lt_re hw1)
    simp only [hF, hG]
    rw [complexLaplace_rieszOmegaMeasure_eq hεε'.le hg hw.1 hw.2, rieszContinuation, rieszLogKernel]
    have e : Complex.Gamma (1 - w) * (2 * w - 1) / zetaResidueUnit (2 * w) *
        zetaResidueUnit (2 * w) = Complex.Gamma (1 - w) * (2 * w - 1) := div_mul_cancel₀ _ hZ
    linear_combination (η : ℂ) * e
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa hUc h78 hev ⟨hz1, hz2⟩

theorem exists_riesz_oneSided_of_eventually {η c : ℝ} (hη : |η| = 1) (hc : 0 ≤ c)
    (h : ∀ᶠ x : ℝ in atTop, η * rieszFunction x ≤ c * x ^ (1 / 4 : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ t, 0 < t → η * rieszFunction (Real.exp t) ≤ c * Real.exp (t / 4) + K := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp h
  obtain ⟨K₀, hK₀, hF⟩ := exists_abs_rieszFunction_exp_le
  refine ⟨K₀ * |x₀|, by positivity, fun t ht => ?_⟩
  have hE := Real.exp_pos (t / 4)
  by_cases hxt : x₀ ≤ Real.exp t
  · have := hx₀ (Real.exp t) hxt
    rw [← Real.exp_mul, show t * (1 / 4) = t / 4 by ring] at this
    have : 0 ≤ K₀ * |x₀| := by positivity
    linarith
  · have h1 : |η * rieszFunction (Real.exp t)| ≤ K₀ * Real.exp (3 / 4 * t) := by
      rw [abs_mul, hη, one_mul]; exact hF t
    have h2 := le_abs_self (η * rieszFunction (Real.exp t))
    have h3 : Real.exp (3 / 4 * t) ≤ |x₀| := by
      have : Real.exp (3 / 4 * t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
      linarith [not_le.mp hxt, le_abs_self x₀]
    have h5 : 0 ≤ c * Real.exp (t / 4) := mul_nonneg hc hE.le
    nlinarith

/-- **A one-sided quarter-power bound for the Riesz function implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_rieszFunction_oneSided {η c : ℝ} (hη : |η| = 1) (hc : 0 ≤ c)
    (h : ∀ᶠ x : ℝ in atTop, η * rieszFunction x ≤ c * x ^ (1 / 4 : ℝ)) : RiemannHypothesis := by
  obtain ⟨K, hK, hg⟩ := exists_riesz_oneSided_of_eventually hη hc h
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro s hs hzero
  have hs1 : s.re < 1 := by
    by_contra hge
    push Not at hge
    have hs1' : s ≠ 1 := by
      intro h1; rw [h1, zetaResidueUnit_one] at hzero; exact one_ne_zero hzero
    rw [zetaResidueUnit, Function.update_of_ne hs1'] at hzero
    exact mul_ne_zero (sub_ne_zero.mpr hs1') (riemannZeta_ne_zero_of_one_le_re hge) hzero
  have hid := riesz_continuation_identity hη hc (lt_add_one c) hK hg (z := s / 2)
    (by simp; linarith) (by simp; linarith)
  rw [show 2 * (s / 2) = s by ring, hzero, mul_zero, mul_zero, sub_zero] at hid
  have hη0 : (η : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; rw [this] at hη; simp at hη
  have hΓ : Complex.Gamma (1 - s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hs1' : s - 1 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  exact (mul_ne_zero hη0 (mul_ne_zero hΓ hs1')) hid.symm

/-! ## The zero on the line -/

/-- The real transform at `¼ + r`, through the continuation identity. -/
theorem laplaceReal_rieszOmegaMeasure_le {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε')
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * rieszFunction (Real.exp t) ≤ ε' * Real.exp (t / 4) + K)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 3 / 4) :
    laplaceReal (rieszOmegaMeasure η ε K) (1 / 4 + r)
      ≤ ε / r + 4 * K + ‖rieszLogKernel ((1 / 4 + r : ℝ) : ℂ)‖ := by
  have hε : 0 ≤ ε := by linarith
  set w : ℂ := ((1 / 4 + r : ℝ) : ℂ) with hw
  have hwre : w.re = 1 / 4 + r := by simp [hw]
  have hw0 : w ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hwre] at this; simp at this; linarith
  have hZ : zetaResidueUnit (2 * w) ≠ 0 := zetaResidueUnit_two_mul_ofReal_ne_zero (by linarith)
  have hid := riesz_continuation_identity hη hε' hεε' hK hg (z := w) (by rw [hwre]; linarith)
    (by rw [hwre]; linarith)
  have hCL : complexLaplace (rieszOmegaMeasure η ε K) w
      = ε / (w - 1 / 4) + K / w - η * rieszLogKernel w := by
    have hH : ε / (w - 1 / 4) + K / w - complexLaplace (rieszOmegaMeasure η ε K) w
        = η * rieszLogKernel w := by
      unfold rieszLogKernel
      have e : Complex.Gamma (1 - w) * (2 * w - 1) / zetaResidueUnit (2 * w) *
          zetaResidueUnit (2 * w) = Complex.Gamma (1 - w) * (2 * w - 1) := div_mul_cancel₀ _ hZ
      apply mul_right_cancel₀ hZ
      rw [hid]
      linear_combination (-(η : ℂ)) * e
    linear_combination (-1 : ℂ) * hH
  have hnn : 0 ≤ laplaceReal (rieszOmegaMeasure η ε K) (1 / 4 + r) :=
    integral_nonneg fun u => (Real.exp_pos _).le
  have hcl := complexLaplace_ofReal (rieszOmegaMeasure η ε K) (1 / 4 + r)
  rw [← hw] at hcl
  have hnorm : laplaceReal (rieszOmegaMeasure η ε K) (1 / 4 + r)
      = ‖complexLaplace (rieszOmegaMeasure η ε K) w‖ := by
    rw [hcl, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hnorm, hCL]
  have hwq : w - 1 / 4 = (r : ℂ) := by rw [hw]; push_cast; ring
  have h1 : ‖(ε : ℂ) / (w - 1 / 4)‖ = ε / r := by
    rw [hwq, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hr, abs_of_nonneg hε]
  have h2 : ‖(K : ℂ) / w‖ ≤ 4 * K := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK, hw, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : ‖(η : ℂ) * rieszLogKernel w‖ = ‖rieszLogKernel w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hη, one_mul]
  calc ‖(ε : ℂ) / (w - 1 / 4) + K / w - η * rieszLogKernel w‖
      ≤ ‖(ε : ℂ) / (w - 1 / 4)‖ + ‖(K : ℂ) / w‖ + ‖(η : ℂ) * rieszLogKernel w‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _ |>.trans_eq (by ring))
    _ ≤ ε / r + 4 * K + ‖rieszLogKernel w‖ := by rw [h1, h3]; linarith

/-- **The local inequality at a zero.**  Near a zero `ρ = ½ + iγ` with `(v-1)ζ(v) = (v-ρ)^m G(v)`,
with `z = ρ/2 + r`: `|Γ(1-z)||2z-1|/(2^m |G(2z)|) ≤ r^{m-1}(ε + Cr)` for all small `r > 0`. -/
theorem eventually_riesz_local_le {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε')
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * rieszFunction (Real.exp t) ≤ ε' * Real.exp (t / 4) + K)
    {ρ : ℂ} (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) {m : ℕ} (hm : 1 ≤ m) {G : ℂ → ℂ}
    (hGan : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0)
    (hfac : ∀ᶠ v in 𝓝 ρ, zetaResidueUnit v = (v - ρ) ^ m • G v) :
    ∃ C : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖Complex.Gamma (1 - (ρ / 2 + r))‖ * ‖2 * (ρ / 2 + r) - 1‖ /
        (2 ^ m * ‖G (ρ + 2 * r)‖) ≤ r ^ (m - 1) * (ε + r * C) := by
  have hε : 0 ≤ ε := by linarith
  set γ : ℝ := |ρ.im| / 2 with hγ
  have hγ0 : 0 < γ := by have := abs_pos.mpr hρim; rw [hγ]; linarith
  -- continuity of the kernel at the real point `¼`
  have hΨc : ContinuousAt (fun r : ℝ => rieszLogKernel ((1 / 4 + r : ℝ) : ℂ)) 0 := by
    have hf : ContinuousAt (fun r : ℝ => ((1 / 4 + r : ℝ) : ℂ)) 0 := by fun_prop
    have hZ : zetaResidueUnit (2 * (((1 / 4 + 0 : ℝ)) : ℂ)) ≠ 0 :=
      zetaResidueUnit_two_mul_ofReal_ne_zero (by norm_num)
    exact ContinuousAt.comp (g := rieszLogKernel) (f := fun r : ℝ => ((1 / 4 + r : ℝ) : ℂ))
      (analyticAt_rieszLogKernel (by simp; norm_num) (by simp; norm_num) hZ).continuousAt hf
  set B : ℝ := ‖rieszLogKernel ((1 / 4 + 0 : ℝ) : ℂ)‖ + 1 with hB
  have hΨb : ∀ᶠ r in 𝓝 (0 : ℝ), ‖rieszLogKernel ((1 / 4 + r : ℝ) : ℂ)‖ ≤ B := by
    have := hΨc.norm.eventually (gt_mem_nhds (show
      ‖rieszLogKernel ((1 / 4 + 0 : ℝ) : ℂ)‖ < B by rw [hB]; linarith))
    exact this.mono fun r hr => hr.le
  -- continuity of the head at `ρ/2`
  have htz : Tendsto (fun r : ℝ => ρ / 2 + r) (𝓝[>] (0 : ℝ)) (𝓝 (ρ / 2)) := by
    have h : Tendsto (fun r : ℝ => ρ / 2 + r) (𝓝 (0 : ℝ)) (𝓝 (ρ / 2 + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hρ2re : (ρ / 2).re = 1 / 4 := by simp [hρre]; norm_num
  have hIc : ContinuousAt rieszHead (ρ / 2) :=
    (analyticAt_rieszHead (by rw [hρ2re]; norm_num) (by rw [hρ2re]; norm_num)).continuousAt
  set B₂ : ℝ := ‖rieszHead (ρ / 2)‖ + 1 with hB₂
  have hIb : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖rieszHead (ρ / 2 + r)‖ ≤ B₂ := by
    have := (hIc.norm.tendsto.comp htz).eventually (gt_mem_nhds (show
      ‖rieszHead (ρ / 2)‖ < B₂ by rw [hB₂]; linarith))
    exact this.mono fun r hr => hr.le
  -- the factorization along `ρ + 2r`
  have htend : Tendsto (fun r : ℝ => ρ + 2 * r) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    have h : Tendsto (fun r : ℝ => ρ + 2 * r) (𝓝 (0 : ℝ)) (𝓝 (ρ + 2 * ((0 : ℝ) : ℂ))) :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hfac' := htend.eventually hfac
  have hGne : ∀ᶠ r : ℝ in 𝓝[>] 0, G (ρ + 2 * r) ≠ 0 :=
    htend.eventually (hGan.continuousAt.eventually_ne hG0)
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 3 / 4 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
  refine ⟨(ε + K) / γ + 4 * K + B + B₂, ?_⟩
  filter_upwards [hfac', hGne, self_mem_nhdsWithin, nhdsWithin_le_nhds hΨb, hIb, hsmall] with
    r hr hGr hr0 hΨr hIr hr34
  have hr0' : 0 < r := hr0
  set z : ℂ := ρ / 2 + r with hz
  have hzre : z.re = 1 / 4 + r := by simp [hz, hρre]; norm_num
  have hzim : z.im = ρ.im / 2 := by simp [hz]
  have hz0 : z ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hzre] at this; simp at this; linarith
  have hid := riesz_continuation_identity hη hε' hεε' hK hg (z := z) (by rw [hzre]; linarith)
    (by rw [hzre]; linarith)
  set H : ℂ := ε / (z - 1 / 4) + K / z - complexLaplace (rieszOmegaMeasure η ε K) z with hHdef
  have h2z : 2 * z = ρ + 2 * r := by rw [hz]; ring
  rw [h2z, hr, show ρ + 2 * (r : ℂ) - ρ = 2 * (r : ℂ) by ring] at hid
  -- the norm identity
  have hkey : (H + η * rieszHead z) * ((2 * (r : ℂ)) ^ m * G (ρ + 2 * r)) =
      η * (Complex.Gamma (1 - z) * (2 * z - 1)) := by
    rw [smul_eq_mul] at hid
    linear_combination hid
  have hnormid : ‖H + η * rieszHead z‖ * ((2 * r) ^ m * ‖G (ρ + 2 * r)‖) =
      ‖Complex.Gamma (1 - z)‖ * ‖2 * z - 1‖ := by
    have := congrArg norm hkey
    rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0', norm_mul, Complex.norm_real, Real.norm_eq_abs, hη, one_mul,
      norm_mul] at this
    rw [← this]
    norm_num
  have hGz : 0 < ‖G (ρ + 2 * r)‖ := norm_pos_iff.mpr hGr
  have hE : ‖Complex.Gamma (1 - z)‖ * ‖2 * z - 1‖ / (2 ^ m * ‖G (ρ + 2 * r)‖) =
      r ^ m * ‖H + η * rieszHead z‖ := by
    rw [← hnormid, mul_pow]; field_simp
  -- the upper bound for `H`
  have hγle : γ ≤ ‖z - 1 / 4‖ := by
    have := Complex.abs_im_le_norm (z - 1 / 4)
    rw [Complex.sub_im, hzim] at this
    simp only [Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero, abs_div] at this
    rw [hγ]; simpa using this
  have hγle' : γ ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rw [hzim, abs_div] at this
    rw [hγ]; simpa using this
  have hlap := laplaceReal_rieszOmegaMeasure_le hη hε' hεε' hK hg hr0' hr34
  have hCL : ‖complexLaplace (rieszOmegaMeasure η ε K) z‖
      ≤ laplaceReal (rieszOmegaMeasure η ε K) (1 / 4 + r) := by
    have := norm_complexLaplace_le (rieszOmegaMeasure η ε K) z
    rw [hzre] at this
    exact this
  have h1 : ‖(ε : ℂ) / (z - 1 / 4)‖ ≤ ε / γ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
    exact div_le_div_of_nonneg_left hε hγ0 hγle
  have h2 : ‖(K : ℂ) / z‖ ≤ K / γ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
    exact div_le_div_of_nonneg_left hK hγ0 hγle'
  have hHle : ‖H + η * rieszHead z‖ ≤ ε / γ + K / γ + (ε / r + 4 * K + B) + B₂ := by
    have hn1 := norm_sub_le ((ε : ℂ) / (z - 1 / 4) + K / z)
      (complexLaplace (rieszOmegaMeasure η ε K) z)
    have hn2 := norm_add_le ((ε : ℂ) / (z - 1 / 4)) ((K : ℂ) / z)
    have hn3 := norm_add_le H ((η : ℂ) * rieszHead z)
    have hn4 : ‖(η : ℂ) * rieszHead z‖ = ‖rieszHead z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hη, one_mul]
    rw [hHdef] at hn3 ⊢
    linarith
  have hrH : r * ‖H + η * rieszHead z‖ ≤ ε + r * ((ε + K) / γ + 4 * K + B + B₂) := by
    have := mul_le_mul_of_nonneg_left hHle hr0'.le
    have e : r * (ε / γ + K / γ + (ε / r + 4 * K + B) + B₂)
        = ε + r * ((ε + K) / γ + 4 * K + B + B₂) := by field_simp; ring
    linarith
  rw [hE]
  have hpow : r ^ m = r ^ (m - 1) * r := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow, mul_assoc]
  exact mul_le_mul_of_nonneg_left hrH (pow_nonneg hr0'.le _)

/-- **A one-sided bound forces a simple zero with a small residue.**  If `ηF(x) ≤ ε'x^{1/4}`
(in the form `ηF(e^t) ≤ ε'e^{t/4} + K`) and `(v-1)ζ(v) = (v-ρ)^m G(v)` near a zero
`ρ = ½ + iγ`, then `m = 1` and `|Γ(1-ρ/2)||ρ-1|/(2|G(ρ)|) ≤ ε'`. -/
theorem riesz_zero_simple_of_oneSided {η ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε') (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * rieszFunction (Real.exp t) ≤ ε' * Real.exp (t / 4) + K)
    {ρ : ℂ} (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) (hρ0 : zetaResidueUnit ρ = 0) {m : ℕ}
    {G : ℂ → ℂ} (hGan : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0)
    (hfac : ∀ᶠ v in 𝓝 ρ, zetaResidueUnit v = (v - ρ) ^ m • G v) :
    m = 1 ∧ ‖Complex.Gamma (1 - ρ / 2)‖ * ‖ρ - 1‖ / (2 * ‖G ρ‖) ≤ ε' := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      have := hfac.self_of_nhds
      rw [h, pow_zero, one_smul, hρ0] at this
      exact hG0 this.symm
    · exact h
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρre; norm_num at hρre
  have hΓ : Complex.Gamma (1 - ρ / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [hρre]; norm_num)
  set F₀ : ℝ := ‖Complex.Gamma (1 - ρ / 2)‖ * ‖ρ - 1‖ / (2 ^ m * ‖G ρ‖) with hF₀
  have hF₀pos : 0 < F₀ := by
    rw [hF₀]
    exact div_pos (mul_pos (norm_pos_iff.mpr hΓ) (norm_pos_iff.mpr (sub_ne_zero.mpr hρ1)))
      (mul_pos (by positivity) (norm_pos_iff.mpr hG0))
  have htz : Tendsto (fun r : ℝ => ρ / 2 + r) (𝓝[>] (0 : ℝ)) (𝓝 (ρ / 2)) := by
    have h : Tendsto (fun r : ℝ => ρ / 2 + r) (𝓝 (0 : ℝ)) (𝓝 (ρ / 2 + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have htend : Tendsto (fun r : ℝ => ρ + 2 * r) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    have h : Tendsto (fun r : ℝ => ρ + 2 * r) (𝓝 (0 : ℝ)) (𝓝 (ρ + 2 * ((0 : ℝ) : ℂ))) :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hFt : Tendsto (fun r : ℝ => ‖Complex.Gamma (1 - (ρ / 2 + r))‖ * ‖2 * (ρ / 2 + r) - 1‖ /
      (2 ^ m * ‖G (ρ + 2 * r)‖)) (𝓝[>] (0 : ℝ)) (𝓝 F₀) := by
    have hΓc : ContinuousAt (fun v : ℂ => Complex.Gamma (1 - v)) (ρ / 2) :=
      ((analyticAt_complexGamma_of_re_pos (by simp [hρre]; norm_num)).comp
        (analyticAt_const.sub analyticAt_id)).continuousAt
    have h1 : Tendsto (fun r : ℝ => ‖Complex.Gamma (1 - (ρ / 2 + r))‖) (𝓝[>] (0 : ℝ))
        (𝓝 ‖Complex.Gamma (1 - ρ / 2)‖) := (hΓc.tendsto.comp htz).norm
    have h2 : Tendsto (fun r : ℝ => ‖2 * (ρ / 2 + r) - 1‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖ρ - 1‖) := by
      have := ((htz.const_mul 2).sub_const 1).norm
      rwa [show 2 * (ρ / 2) - 1 = ρ - 1 by ring] at this
    have h3 : Tendsto (fun r : ℝ => 2 ^ m * ‖G (ρ + 2 * r)‖) (𝓝[>] (0 : ℝ))
        (𝓝 (2 ^ m * ‖G ρ‖)) := ((hGan.continuousAt.tendsto.comp htend).norm).const_mul _
    exact (h1.mul h2).div h3 (mul_pos (by positivity) (norm_pos_iff.mpr hG0)).ne'
  have hlocal : ∀ ε : ℝ, ε' < ε → (m = 1 ∧ F₀ ≤ ε) := by
    intro ε hεε'
    obtain ⟨C, hC⟩ := eventually_riesz_local_le hη hε' hεε' hK hg hρre hρim hm hGan hG0 hfac
    rcases Nat.lt_or_ge 1 m with hm2 | hm1
    · exfalso
      have hR : Tendsto (fun r : ℝ => r ^ (m - 1) * (ε + r * C)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h0 : Tendsto (fun r : ℝ => r ^ (m - 1) * (ε + r * C)) (𝓝 (0 : ℝ))
            (𝓝 ((0 : ℝ) ^ (m - 1) * (ε + 0 * C))) :=
          ((continuous_pow _).mul
            (continuous_const.add (continuous_id.mul continuous_const))).tendsto 0
        rw [zero_pow (by omega), zero_mul] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      have := le_of_tendsto_of_tendsto hFt hR hC
      linarith
    · have hm1' : m = 1 := le_antisymm hm1 hm
      refine ⟨hm1', ?_⟩
      have hR : Tendsto (fun r : ℝ => r ^ (m - 1) * (ε + r * C)) (𝓝[>] (0 : ℝ)) (𝓝 ε) := by
        have h0 : Tendsto (fun r : ℝ => r ^ (m - 1) * (ε + r * C)) (𝓝 (0 : ℝ))
            (𝓝 ((0 : ℝ) ^ (m - 1) * (ε + 0 * C))) :=
          ((continuous_pow _).mul
            (continuous_const.add (continuous_id.mul continuous_const))).tendsto 0
        rw [hm1', Nat.sub_self, pow_zero, one_mul, zero_mul, add_zero] at h0
        rw [hm1']
        exact h0.mono_left nhdsWithin_le_nhds
      exact le_of_tendsto_of_tendsto hFt hR hC
  have hm1 := (hlocal (ε' + 1) (by linarith)).1
  refine ⟨hm1, ?_⟩
  have hF₀' : F₀ = ‖Complex.Gamma (1 - ρ / 2)‖ * ‖ρ - 1‖ / (2 * ‖G ρ‖) := by
    rw [hF₀, hm1, pow_one]
  rw [← hF₀']
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  have := (hlocal (ε' + δ / 2) (by linarith)).2
  linarith

/-! ## The quarter-power oscillation -/

/-- **The Riesz function is `Ω±(x^{1/4})`.**  There is `c > 0` with `F(x) > c x^{1/4}` and
`F(x) < -c x^{1/4}`, each for arbitrarily large `x`. -/
theorem rieszFunction_omega_pm_quarter :
    ∃ c : ℝ, 0 < c ∧ (∃ᶠ x : ℝ in atTop, c * x ^ (1 / 4 : ℝ) < rieszFunction x)
      ∧ ∃ᶠ x : ℝ in atTop, rieszFunction x < -(c * x ^ (1 / 4 : ℝ)) := by
  obtain ⟨t, ht1, ht0⟩ := exists_Xi_zero_gt 1
  set ρ : ℂ := 1 / 2 + (t : ℂ) * I with hρdef
  have hxi : xi ρ = 0 := by
    rw [xi_eq_XiC_comp]
    have e : ((1 / 2 + (t : ℂ) * I - 1 / 2) * -I) = (t : ℂ) := by
      ring_nf
      simp [Complex.I_sq]
    rw [e, XiC_ofReal, ht0]
    simp
  have hρre : ρ.re = 1 / 2 := by simp [hρdef]
  have hρim : ρ.im ≠ 0 := by simp [hρdef]; linarith
  have hρ0 : zetaResidueUnit ρ = 0 :=
    zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero
      (riemannZeta_eq_zero_iff_xi_or_trivial.mpr (Or.inl hxi))
  have hnot : ¬ ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = 0 := by
    intro hzero
    have hall := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => analyticAt_zetaResidueUnit z) isPreconnected_univ (mem_univ ρ) hzero
    have := hall (mem_univ (1 : ℂ))
    simp at this
  obtain ⟨m, G, hGan, hG0, hfac⟩ :=
    ((analyticAt_zetaResidueUnit ρ).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnot
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρre; norm_num at hρre
  have hΓ : Complex.Gamma (1 - ρ / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [hρre]; norm_num)
  set F₀ : ℝ := ‖Complex.Gamma (1 - ρ / 2)‖ * ‖ρ - 1‖ / (2 * ‖G ρ‖) with hF₀
  have hF₀pos : 0 < F₀ := by
    rw [hF₀]
    exact div_pos (mul_pos (norm_pos_iff.mpr hΓ) (norm_pos_iff.mpr (sub_ne_zero.mpr hρ1)))
      (mul_pos two_pos (norm_pos_iff.mpr hG0))
  refine ⟨F₀ / 2, by positivity, ?_, ?_⟩
  · by_contra hno
    rw [Filter.not_frequently] at hno
    have h' : ∀ᶠ x : ℝ in atTop, (1 : ℝ) * rieszFunction x ≤ F₀ / 2 * x ^ (1 / 4 : ℝ) :=
      hno.mono fun x hx => by rw [one_mul]; exact not_lt.mp hx
    obtain ⟨K, hK, hg⟩ := exists_riesz_oneSided_of_eventually (by simp) (by positivity) h'
    have := (riesz_zero_simple_of_oneSided (by simp) (by positivity) hK hg hρre hρim hρ0 hGan
      hG0 hfac).2
    rw [← hF₀] at this
    linarith
  · by_contra hno
    rw [Filter.not_frequently] at hno
    have h' : ∀ᶠ x : ℝ in atTop, (-1 : ℝ) * rieszFunction x ≤ F₀ / 2 * x ^ (1 / 4 : ℝ) :=
      hno.mono fun x hx => by have := not_lt.mp hx; linarith
    obtain ⟨K, hK, hg⟩ := exists_riesz_oneSided_of_eventually (by simp) (by positivity) h'
    have := (riesz_zero_simple_of_oneSided (by simp) (by positivity) hK hg hρre hρim hρ0 hGan
      hG0 hfac).2
    rw [← hF₀] at this
    linarith

/-- **`F(x)` is not `o(x^{1/4})`.** -/
theorem not_rieszFunction_isLittleO_rpow_quarter :
    ¬ (fun x : ℝ => rieszFunction x) =o[atTop] fun x => x ^ (1 / 4 : ℝ) := by
  intro h
  obtain ⟨c, hc, hfr, -⟩ := rieszFunction_omega_pm_quarter
  have hb := h.bound hc
  have := hfr.and_eventually (hb.and (eventually_gt_atTop 0))
  obtain ⟨x, hx1, hx2, hx0⟩ := this.exists
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hx2
  linarith [le_abs_self (rieszFunction x)]

/-- **A one-sided quarter-power bound for `F` makes every zero on the critical line simple.** -/
theorem deriv_zetaResidueUnit_ne_zero_of_rieszFunction_oneSided {η c : ℝ} (hη : |η| = 1)
    (hc : 0 ≤ c) (h : ∀ᶠ x : ℝ in atTop, η * rieszFunction x ≤ c * x ^ (1 / 4 : ℝ)) {ρ : ℂ}
    (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) (hρ0 : zetaResidueUnit ρ = 0) :
    deriv zetaResidueUnit ρ ≠ 0 := by
  obtain ⟨K, hK, hg⟩ := exists_riesz_oneSided_of_eventually hη hc h
  have hnot : ¬ ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = 0 := by
    intro hzero
    have hall := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => analyticAt_zetaResidueUnit z) isPreconnected_univ (mem_univ ρ) hzero
    have := hall (mem_univ (1 : ℂ))
    simp at this
  obtain ⟨m, G, hGan, hG0, hfac⟩ :=
    ((analyticAt_zetaResidueUnit ρ).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnot
  have hm := (riesz_zero_simple_of_oneSided hη hc hK hg hρre hρim hρ0 hGan hG0 hfac).1
  rw [hm] at hfac
  have hd : HasDerivAt (fun z => (z - ρ) ^ 1 • G z) (G ρ) ρ := by
    have h1 : HasDerivAt (fun z : ℂ => (z - ρ) ^ 1) 1 ρ := by
      simpa using (hasDerivAt_id ρ).sub_const ρ
    have h2 := h1.mul hGan.differentiableAt.hasDerivAt
    refine h2.congr_deriv ?_
    simp
  rw [(hd.congr_of_eventuallyEq hfac).deriv]
  exact hG0

end

end RHTower
