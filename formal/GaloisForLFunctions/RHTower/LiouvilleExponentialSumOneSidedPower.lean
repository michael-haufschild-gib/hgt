import GaloisForLFunctions.RHTower.LiouvilleExponentialSumMultiplicity
import GaloisForLFunctions.RHTower.LiouvilleExponentialSumRH

/-!
# One-sided power bounds for the exponential Liouville sum

Let `J(t) = Σ_{n ≥ 1} λ(n) e^{-nt}/n`.  A one-sided power bound

  `J(t) ≥ -C t^a`   for `0 < t ≤ t₀`,   `0 < a ≤ ½`,

already confines the zeros: `ζ(s) ≠ 0` for `Re s > 1 − a`
(`zetaResidueUnit_ne_zero_of_liouvilleExpSum_lower_rpow`).  Hence RH is equivalent to the
one-sided `ε`-lossy bounds `J(t) ≥ -C_ε t^{½-ε}` (`riemannHypothesis_iff_forall_liouvilleExpSum_lower`),
exactly as to the two-sided ones (`riemannHypothesis_iff_forall_liouvilleExpSum_isBigO`).  Only
the logarithmic forms `J ≥ -C√t log^k(1/t)` see multiplicities.

**Proof.**  In `t = e^{-u}` the density `J(e^{-u}) + C e^{-au}` is nonnegative on `u > 0`.  The
Laplace transform of the weight `e^{-au} du` is `1/(z + a)`, so the transform of the density
continues to `κ(z) − E(z) + C/(z + a)` with `κ(z) = Γ(z+1)Z(2z+2)/((2z+1)Z(z+1))` and
`Z(s) = (s − 1)ζ(s)`.  Landau's theorem places the abscissa at `-a`.  The identity theorem then gives
`(∫ e^{-zu} dν + E(z) − C/(z + a))(2z + 1)Z(z + 1) = Γ(z + 1)Z(2z + 2)` on `Re z > -a`, whose right
side does not vanish at `z = ρ − 1` when `Re ρ > 1 − a ≥ ½`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open scoped LSeries.notation

namespace RHTower

noncomputable section

/-! ## The one-sided measure -/

/-- The density `J(e^{-u}) + C e^{-au}`, clipped at `0`. -/
def liouvilleExpDensityExp (a C : ℝ) (u : ℝ) : NNReal :=
  Real.toNNReal (liouvilleExpLog u + C * Real.exp (-a * u))

theorem measurable_liouvilleExpDensityExp (a C : ℝ) :
    Measurable (liouvilleExpDensityExp a C) :=
  Measurable.real_toNNReal (continuous_liouvilleExpLog.measurable.add
    (measurable_const.mul (by fun_prop : Continuous fun u : ℝ => Real.exp (-a * u)).measurable))

/-- `ν = (J(e^{-u}) + C e^{-au}) du` on `(0, ∞)`. -/
def liouvilleExpMeasureExp (a C : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun u => (liouvilleExpDensityExp a C u : ENNReal))

theorem liouvilleExpDensityExp_coe {a C₀ C : ℝ} (hC : C₀ ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-a * u)) ≤ liouvilleExpLog u) {u : ℝ} (hu : 0 < u) :
    ((liouvilleExpDensityExp a C u : ℝ)) = liouvilleExpLog u + C * Real.exp (-a * u) := by
  unfold liouvilleExpDensityExp
  have h := hg u hu
  have hw := Real.exp_pos (-a * u)
  rw [Real.coe_toNNReal _ (by nlinarith)]

theorem laplaceMass_liouvilleExpMeasureExp_one_ne_top {a : ℝ} (ha : 0 ≤ a) (C : ℝ) :
    laplaceMass (liouvilleExpMeasureExp a C) 1 ≠ ⊤ := by
  unfold laplaceMass liouvilleExpMeasureExp
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-1 * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_liouvilleExpDensityExp a C).coe_nnreal_ennreal hg]
  have hmaj : IntegrableOn (fun u : ℝ => (1 + |C|) * Real.exp (-1 * u) +
      2 * Real.exp (-(1 / 2) * u)) (Ioi 0) :=
    ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul _).add
      ((exp_neg_integrableOn_Ioi 0 (by norm_num)).const_mul _)
  refine ne_top_of_le_ne_top hmaj.lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  have hu0 : 0 < u := hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hE := Real.exp_pos (-1 * u)
  have hd : ((liouvilleExpDensityExp a C u : ℝ)) ≤ 1 + u + |C| := by
    unfold liouvilleExpDensityExp
    rw [Real.coe_toNNReal']
    refine max_le ?_ (by positivity)
    have h1 := abs_liouvilleExpLog_le_of_nonneg hu0.le
    have hw : Real.exp (-a * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hw0 := Real.exp_pos (-a * u)
    have h3 : C * Real.exp (-a * u) ≤ |C| := by
      calc C * Real.exp (-a * u) ≤ |C| * Real.exp (-a * u) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) hw0.le
        _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hw (abs_nonneg C)
        _ = |C| := mul_one _
    linarith [le_abs_self (liouvilleExpLog u)]
  have hu2 : u * Real.exp (-1 * u) ≤ 2 * Real.exp (-(1 / 2) * u) := by
    have := liouville_pow_mul_exp_neg_le 1 one_pos hu0.le
    simpa using this
  calc ((liouvilleExpDensityExp a C u : ℝ)) * Real.exp (-1 * u)
      ≤ (1 + u + |C|) * Real.exp (-1 * u) := mul_le_mul_of_nonneg_right hd hE.le
    _ = (1 + |C|) * Real.exp (-1 * u) + u * Real.exp (-1 * u) := by ring
    _ ≤ (1 + |C|) * Real.exp (-1 * u) + 2 * Real.exp (-(1 / 2) * u) := by gcongr

theorem laplaceMass_liouvilleExpMeasureExp_eq_top {a C₀ C : ℝ} (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-a * u)) ≤ liouvilleExpLog u) {σ : ℝ}
    (hσ : σ ≤ -a) : laplaceMass (liouvilleExpMeasureExp a C) σ = ⊤ := by
  unfold laplaceMass liouvilleExpMeasureExp
  have hg' : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_liouvilleExpDensityExp a C).coe_nnreal_ennreal hg', eq_top_iff]
  calc (⊤ : ENNReal) = ENNReal.ofReal 1 * volume (Ioi (0 : ℝ)) := by
        rw [Real.volume_Ioi, ENNReal.ofReal_one, one_mul]
    _ = ∫⁻ _ in Ioi (0 : ℝ), ENNReal.ofReal 1 := by rw [setLIntegral_const]
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), ((fun u => (liouvilleExpDensityExp a C u : ENNReal))
          * fun u => ENNReal.ofReal (Real.exp (-σ * u))) u := by
        refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := hu
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [liouvilleExpDensityExp_coe (by linarith) hg hu0]
        have h1 := hg u hu0
        have hw := Real.exp_pos (-a * u)
        have hE2 := Real.exp_pos (-σ * u)
        have h2 : 1 ≤ Real.exp (-a * u) * Real.exp (-σ * u) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        have h3 : Real.exp (-a * u) ≤ liouvilleExpLog u + C * Real.exp (-a * u) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right h3 hE2.le]

theorem isAbscissa_liouvilleExpMeasureExp {a C₀ C : ℝ} (ha : 0 ≤ a) (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-a * u)) ≤ liouvilleExpLog u) :
    IsAbscissa (liouvilleExpMeasureExp a C)
        (sInf {σ : ℝ | laplaceMass (liouvilleExpMeasureExp a C) σ ≠ ⊤})
      ∧ -a ≤ sInf {σ : ℝ | laplaceMass (liouvilleExpMeasureExp a C) σ ≠ ⊤}
      ∧ sInf {σ : ℝ | laplaceMass (liouvilleExpMeasureExp a C) σ ≠ ⊤} ≤ 1 := by
  set S := {σ : ℝ | laplaceMass (liouvilleExpMeasureExp a C) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, -a < σ := by
    intro σ hσ
    by_contra hle
    exact hσ (laplaceMass_liouvilleExpMeasureExp_eq_top hC hg (not_lt.mp hle))
  have hbdd : BddBelow S := ⟨-a, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1 : ℝ) ∈ S := laplaceMass_liouvilleExpMeasureExp_one_ne_top ha C
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le,
    csInf_le hbdd h1S⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The continuation -/

/-- The continuation `Φ(z) = κ(z) − E(z) + C/(z + a)`. -/
def liouvilleExpContinuationExp (a C : ℝ) (z : ℂ) : ℂ :=
  liouvilleExpKernel z - liouvilleExpTail z + C / (z + a)

theorem analyticAt_liouvilleExpContinuationExp {a : ℝ} (ha : a ≤ 1 / 2) (C : ℝ) {z : ℂ}
    (hz : -a < z.re) (hZ : zetaResidueUnit (z + 1) ≠ 0) :
    AnalyticAt ℂ (liouvilleExpContinuationExp a C) z := by
  have h2 : 2 * z + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hza : z + a ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold liouvilleExpContinuationExp
  exact ((analyticAt_liouvilleExpKernel (by linarith) h2 hZ).sub
    (differentiable_liouvilleExpTail.analyticAt z)).add
    (analyticAt_const.div (analyticAt_id.add analyticAt_const) hza)

/-- `∫_0^∞ e^{-zu} e^{-au} du = 1/(z + a)` for `Re(z + a) > 0`. -/
theorem integral_Ioi_cexp_mul_exp {a : ℝ} {z : ℂ} (hz : -a < z.re) :
    ∫ u in Ioi (0 : ℝ), cexp (-z * (u : ℂ)) * ((Real.exp (-a * u) : ℝ) : ℂ) = 1 / (z + a) := by
  have hre : (-(z + a)).re < 0 := by simp; linarith
  have hza : z + (a : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hpt : ∀ u : ℝ, cexp (-z * (u : ℂ)) * ((Real.exp (-a * u) : ℝ) : ℂ) =
      cexp (-(z + a) * (u : ℂ)) := by
    intro u
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_exp_mul_complex_Ioi hre 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

/-- On `Re z > 0` the complex transform of `ν` is `Φ(z)`. -/
theorem complexLaplace_liouvilleExpMeasureExp_eq {a C₀ C : ℝ} (ha : 0 ≤ a) (hC : C₀ ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-a * u)) ≤ liouvilleExpLog u) {z : ℂ}
    (hz : 0 < z.re) :
    complexLaplace (liouvilleExpMeasureExp a C) z = liouvilleExpContinuationExp a C z := by
  have hza : -a < z.re := by linarith
  have hWint : IntegrableOn (fun u : ℝ => cexp (-z * (u : ℂ)) * ((Real.exp (-a * u) : ℝ) : ℂ))
      (Ioi 0) := by
    have hre : (-(z + a)).re < 0 := by simp; linarith
    refine (integrableOn_exp_mul_complex_Ioi hre 0).congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    ring_nf
  unfold complexLaplace liouvilleExpMeasureExp
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integral_withDensity_eq_integral_smul (measurable_liouvilleExpDensityExp a C)]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), liouvilleExpDensityExp a C u • Complex.exp (-z * (u : ℂ))
      = cexp (-z * u) * (liouvilleExpLog u : ℂ) +
        (C : ℂ) * (cexp (-z * (u : ℂ)) * ((Real.exp (-a * u) : ℝ) : ℂ)) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul, liouvilleExpDensityExp_coe hC hg hu]
    push_cast
    ring
  have i1 := integrableOn_Ioi_liouvilleExpIntegrand hz
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add i1 (hWint.const_mul _),
    integral_const_mul, integral_Ioi_cexp_mul_exp hza, integral_Ioi_liouvilleExpLog hz,
    Gamma_mul_LSeries_eq_kernel hz]
  unfold liouvilleExpContinuationExp
  ring

/-- **Landau: the abscissa of `ν` is `-a`.** -/
theorem abscissa_liouvilleExpMeasureExp_eq {a C₀ C : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    (hC : C₀ + 1 ≤ C) (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-a * u)) ≤ liouvilleExpLog u) :
    IsAbscissa (liouvilleExpMeasureExp a C) (-a) := by
  obtain ⟨hc, hac, hc2⟩ := isAbscissa_liouvilleExpMeasureExp ha0.le hC hg
  set c : ℝ := sInf {σ : ℝ | laplaceMass (liouvilleExpMeasureExp a C) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hZ : zetaResidueUnit ((c : ℂ) + 1) ≠ 0 := by
      have := zetaResidueUnit_ofReal_ne_zero (t := c + 1) (by linarith)
      simpa using this
    have hcre : -a < ((c : ℂ)).re := by simpa using hpos
    have hev : ∀ᶠ z in 𝓝 (c : ℂ), zetaResidueUnit (z + 1) ≠ 0 ∧ -a < z.re :=
      (((analyticAt_zetaResidueUnit _).comp
        (analyticAt_id.add analyticAt_const)).continuousAt.eventually_ne hZ).and
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hcre)
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine false_of_analyticAt_abscissa hc hd (Φ := liouvilleExpContinuationExp a C) ?_ ?_
    · intro z hz
      obtain ⟨h1, h2⟩ := hball hz
      exact analyticAt_liouvilleExpContinuationExp ha C h2 h1
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (liouvilleExpMeasureExp a C))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ
          (fun t : ℝ => complexLaplace (liouvilleExpMeasureExp a C) (t : ℂ)) (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (liouvilleExpMeasureExp a C)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => liouvilleExpContinuationExp a C (t : ℂ))
          (Ioi c) := by
        intro t ht
        have ht' : c < t := ht
        have h1 : AnalyticAt ℂ (liouvilleExpContinuationExp a C) (t : ℂ) := by
          refine analyticAt_liouvilleExpContinuationExp ha C (by simp; linarith) ?_
          have := zetaResidueUnit_ofReal_ne_zero (t := t + 1) (by linarith)
          simpa using this
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h3mem : (2 : ℝ) ∈ Ioi c := by show c < 2; linarith
      have hfg : (fun t : ℝ => complexLaplace (liouvilleExpMeasureExp a C) (t : ℂ))
          =ᶠ[𝓝 (2 : ℝ)] (fun t : ℝ => liouvilleExpContinuationExp a C (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)) fun t ht => ?_
        have ht1 : 0 < (t : ℂ).re := by simp; linarith [ht.1]
        exact complexLaplace_liouvilleExpMeasureExp_eq ha0.le (by linarith) hg ht1
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h3mem hfg
      have hσ : complexLaplace (liouvilleExpMeasureExp a C) (σ : ℂ)
          = liouvilleExpContinuationExp a C (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- **The continuation identity on `Re z > -a`.** -/
theorem liouvilleExpExp_continuation_identity {a C₀ C : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    (hC : C₀ + 1 ≤ C) (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-a * u)) ≤ liouvilleExpLog u)
    {z : ℂ} (hz : -a < z.re) :
    (complexLaplace (liouvilleExpMeasureExp a C) z + liouvilleExpTail z - C / (z + a)) *
        ((2 * z + 1) * zetaResidueUnit (z + 1)) =
      Gamma (z + 1) * zetaResidueUnit (2 * z + 2) := by
  have hc := abscissa_liouvilleExpMeasureExp_eq ha0 ha hC hg
  set U : Set ℂ := {w : ℂ | -a < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set F : ℂ → ℂ := fun w => (complexLaplace (liouvilleExpMeasureExp a C) w + liouvilleExpTail w
    - C / (w + a)) * ((2 * w + 1) * zetaResidueUnit (w + 1)) with hF
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    have hwa : w + (a : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp [hU] at this hw; linarith
    have h1 := (hasDerivAt_complexLaplace hc hw).differentiableAt
    have h2 := differentiable_liouvilleExpTail w
    have h3 : DifferentiableAt ℂ (fun w : ℂ => (C : ℂ) / (w + a)) w :=
      (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _)) hwa
    have h4 : DifferentiableAt ℂ (fun w => (2 * w + 1) * zetaResidueUnit (w + 1)) w :=
      (((differentiableAt_const _).mul differentiableAt_id).add (differentiableAt_const _)).mul
        ((analyticAt_zetaResidueUnit _).differentiableAt.comp w
          (differentiableAt_id.add (differentiableAt_const _)))
    exact (((h1.add h2).sub h3).mul h4).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F U := hFd.analyticOnNhd hUo
  have hGa : AnalyticOnNhd ℂ (fun w : ℂ => Gamma (w + 1) * zetaResidueUnit (2 * w + 2)) U :=
    fun w hw => ((analyticAt_Gamma_of_pos_re (by simp [hU] at hw ⊢; linarith)).comp
      (analyticAt_id.add analyticAt_const)).mul
      ((analyticAt_zetaResidueUnit _).comp ((analyticAt_const.mul analyticAt_id).add
        analyticAt_const))
  have h1U : (1 : ℂ) ∈ U := by simp [hU]; linarith
  have hev : F =ᶠ[𝓝 (1 : ℂ)] fun w : ℂ => Gamma (w + 1) * zetaResidueUnit (2 * w + 2) := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with w hw
    have hw0 : 0 < w.re := hw
    have h2 : 2 * w + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hZ : zetaResidueUnit (w + 1) ≠ 0 :=
      zetaResidueUnit_ne_zero_of_one_lt_re (by simp; linarith)
    simp only [hF]
    rw [complexLaplace_liouvilleExpMeasureExp_eq ha0.le (by linarith) hg hw0,
      liouvilleExpContinuationExp]
    have hden : (2 * w + 1) * zetaResidueUnit (w + 1) ≠ 0 := mul_ne_zero h2 hZ
    have e : liouvilleExpKernel w * ((2 * w + 1) * zetaResidueUnit (w + 1)) =
        Gamma (w + 1) * zetaResidueUnit (2 * w + 2) := by
      unfold liouvilleExpKernel; exact div_mul_cancel₀ _ hden
    linear_combination e
  have hEq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa
    (convex_halfSpace_re_gt _).isPreconnected h1U hev
  exact hEq hz

/-- **The zero-free half-plane of a one-sided power bound.**  If `J(e^{-u}) ≥ -C₀ e^{-au}` on
`u > 0` with `0 < a ≤ ½`, then `(s − 1)ζ(s) ≠ 0` for `Re s > 1 − a`. -/
theorem zetaResidueUnit_ne_zero_of_liouvilleExpLog_lower_exp {a C₀ : ℝ} (ha0 : 0 < a)
    (ha : a ≤ 1 / 2) (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-a * u)) ≤ liouvilleExpLog u)
    {w : ℂ} (hw : 1 - a < w.re) : zetaResidueUnit w ≠ 0 := by
  intro hzero
  have hz : -a < (w - 1).re := by simp; linarith
  have hid := liouvilleExpExp_continuation_identity ha0 ha (le_refl (C₀ + 1)) hg hz
  rw [show w - 1 + 1 = w by ring, hzero, mul_zero, mul_zero] at hid
  have hG : Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hZ2 : zetaResidueUnit (2 * (w - 1) + 2) ≠ 0 := by
    rw [show 2 * (w - 1) + 2 = 2 * w by ring]
    exact zetaResidueUnit_ne_zero_of_one_lt_re (by simp; linarith)
  exact mul_ne_zero hG hZ2 hid.symm

/-! ## The statement in the variable `t` -/

theorem exists_liouvilleExpLog_lower_exp {a C t₀ : ℝ} (ha : 0 ≤ a) (ht₀ : 0 < t₀)
    (h : ∀ t, 0 < t → t ≤ t₀ → -(C * t ^ a) ≤ liouvilleExpSum t) :
    ∃ C₀ : ℝ, ∀ u, 0 < u → -(C₀ * Real.exp (-a * u)) ≤ liouvilleExpLog u := by
  set B : ℝ := 1 + |Real.log t₀| with hB
  have hta : 0 < t₀ ^ a := Real.rpow_pos_of_pos ht₀ a
  refine ⟨max C 0 + B / t₀ ^ a, fun u hu => ?_⟩
  set t := Real.exp (-u) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpow : t ^ a = Real.exp (-a * u) := by
    rw [ht, ← Real.exp_mul]; ring_nf
  have hlog : Real.log (1 / t) = u := by rw [ht, one_div, ← Real.exp_neg, Real.log_exp, neg_neg]
  have hBn : 0 ≤ B := by positivity
  have hW0 : 0 ≤ Real.exp (-a * u) := (Real.exp_pos _).le
  unfold liouvilleExpLog
  rw [← ht]
  rcases le_or_gt t t₀ with htt | htt
  · have h1 := h t ht0 htt
    rw [hpow] at h1
    have h2 : -(max C 0 * Real.exp (-a * u)) ≤ -(C * Real.exp (-a * u)) := by
      have := mul_le_mul_of_nonneg_right (le_max_left C 0) hW0; linarith
    have h3 : 0 ≤ B / t₀ ^ a * Real.exp (-a * u) := by positivity
    nlinarith
  · have hJ := abs_liouvilleExpSum_le_small ht0 ht1
    have hlog' : Real.log (1 / t) ≤ |Real.log t₀| := by
      rw [one_div, Real.log_inv]
      have := Real.log_le_log ht₀ htt.le
      linarith [neg_abs_le (Real.log t₀), le_abs_self (Real.log t₀)]
    have hJ' : -B ≤ liouvilleExpSum t := by
      have := neg_abs_le (liouvilleExpSum t); rw [hB]; linarith
    have h4 : B ≤ B / t₀ ^ a * Real.exp (-a * u) := by
      have hge : t₀ ^ a ≤ Real.exp (-a * u) := by
        rw [← hpow]; exact Real.rpow_le_rpow ht₀.le htt.le ha
      rw [div_mul_eq_mul_div, le_div_iff₀ hta]
      exact mul_le_mul_of_nonneg_left hge hBn
    have h5 : 0 ≤ max C 0 * Real.exp (-a * u) := mul_nonneg (le_max_right C 0) hW0
    nlinarith

/-- **A one-sided power bound confines the zeros.**  If `J(t) ≥ -C t^a` for `0 < t ≤ t₀`, with
`0 < a ≤ ½`, then `ζ` has no zero with `Re s > 1 − a`. -/
theorem zetaResidueUnit_ne_zero_of_liouvilleExpSum_lower_rpow {a C t₀ : ℝ} (ha0 : 0 < a)
    (ha : a ≤ 1 / 2) (ht₀ : 0 < t₀) (h : ∀ t, 0 < t → t ≤ t₀ → -(C * t ^ a) ≤ liouvilleExpSum t)
    {w : ℂ} (hw : 1 - a < w.re) : zetaResidueUnit w ≠ 0 := by
  obtain ⟨C₀, hg⟩ := exists_liouvilleExpLog_lower_exp ha0.le ht₀ h
  exact zetaResidueUnit_ne_zero_of_liouvilleExpLog_lower_exp ha0 ha hg hw

/-- **The one-sided `ε`-lossy Liouville law is equivalent to RH.**  RH holds iff for every
`ε > 0` there are `C, t₀ > 0` with `J(t) ≥ -C t^{½-ε}` on `(0, t₀]`. -/
theorem riemannHypothesis_iff_forall_liouvilleExpSum_lower :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C t₀ : ℝ, 0 < t₀ ∧
      ∀ t, 0 < t → t ≤ t₀ → -(C * t ^ (1 / 2 - ε)) ≤ liouvilleExpSum t := by
  constructor
  · intro hRH ε hε _
    obtain ⟨C, hC⟩ := (liouvilleExpSum_isBigO_of_riemannHypothesis hRH hε).bound
    rw [Filter.Eventually, nhdsWithin, Filter.mem_inf_principal] at hC
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hC
    refine ⟨C, r / 2, by positivity, fun t ht htr => ?_⟩
    have hmem : t ∈ Metric.ball (0 : ℝ) r := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]; linarith
    have hb := hball hmem ht
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at hb
    rw [abs_of_nonneg (Real.rpow_nonneg ht.le _)] at hb
    linarith [neg_abs_le (liouvilleExpSum t)]
  · intro h
    rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
    intro w hw
    set ε : ℝ := min ((w.re - 1 / 2) / 2) (1 / 4) with hεdef
    have hε : 0 < ε := lt_min (by linarith) (by norm_num)
    have hε2 : ε < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    obtain ⟨C, t₀, ht₀, hJ⟩ := h ε hε hε2
    refine zetaResidueUnit_ne_zero_of_liouvilleExpSum_lower_rpow (by linarith) (by linarith) ht₀
      hJ ?_
    have : ε ≤ (w.re - 1 / 2) / 2 := min_le_left _ _
    linarith

end

end RHTower
