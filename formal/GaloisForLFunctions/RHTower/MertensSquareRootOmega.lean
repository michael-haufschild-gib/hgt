import GaloisForLFunctions.RHTower.PrimeCountingLiLandau
import GaloisForLFunctions.RHTower.Sieve.PartialSumMellinBridge
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.CriticalChebyshevBoostChargeInjection

/-!
# The Mertens function is `Ω±(√x)`

Let `M(x) = Σ_{k ≤ x} μ(k)`.  In the logarithmic variable `∫_0^∞ M(e^u) e^{-su} du = 1/(sζ(s))`
for `Re s > 1`.  Suppose `ηM(x) ≤ ε'√x` for all large `x`, with `η = ±1`.  For `ε > ε'` the density
`ε e^{t/2} - ηM(e^t) + K` is at least `(ε - ε')e^{t/2}` on `(0, ∞)`, so its Laplace transform has
abscissa at least `½`; its transform is `ε/(s-½) + K/s - η/(sζ(s))`, analytic at every real point
of `(½, ∞)`, so Landau's theorem puts the abscissa at `½`.  The function
`H(z) = ε/(z-½) + K/z - ∫ e^{-zt} dν` is then holomorphic on `Re z > ½` with
`H(z)·z·(z-1)ζ(z) = η(z-1)`.

At a zero `ρ = ½ + iγ` (Hardy's theorem supplies one) write `(z-1)ζ(z) = (z-ρ)^m g(z)`.  Along
`z = ρ + r`, `r ↓ 0`, nonnegativity gives `|∫ e^{-zt} dν| ≤ ∫ e^{-(½+r)t} dν = ε/r + O(1)`, so
`r|H(ρ+r)| ≤ ε + O(r)`, while `r^m|H(ρ+r)| → |ρ-1|/(|ρ||g(ρ)|) > 0`.  Hence `m = 1` and
`|ρ-1| ≤ ε'|ρ||g(ρ)|`.  Choosing `ε'` below this threshold gives the contradiction.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The Mertens function and its Mellin transform -/

/-- `M(x) = Σ_{1 ≤ k ≤ x} μ(k)`. -/
def mertensFunctionReal (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℝ)

theorem abs_mertensFunctionReal_le (x : ℝ) : |mertensFunctionReal x| ≤ ⌊x⌋₊ := by
  unfold mertensFunctionReal
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |((ArithmeticFunction.moebius k : ℤ) : ℝ)|
      ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = ⌊x⌋₊ := by simp

theorem abs_mertensFunctionReal_exp_le (t : ℝ) : |mertensFunctionReal (Real.exp t)| ≤ Real.exp t :=
  (abs_mertensFunctionReal_le _).trans (Nat.floor_le (Real.exp_pos t).le)

theorem measurable_mertensFunctionReal : Measurable mertensFunctionReal := by
  have : mertensFunctionReal = (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
      ((ArithmeticFunction.moebius k : ℤ) : ℝ)) ∘ Nat.floor := rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

/-- **The Mellin transform of `M` in the logarithmic variable.** -/
theorem integral_mertensFunctionReal_exp_mul_cexp {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), (mertensFunctionReal (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = 1 / (s * riemannZeta s) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; linarith
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hM := Sieve.inv_riemannZeta_eq_mul_integral_mertens hs
  rw [← image_exp_Ioi_zero, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn] at hM
  have hcongr : ∫ u in Ioi (0 : ℝ), |Real.exp u| • ((∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊,
        ((ArithmeticFunction.moebius k : ℤ) : ℂ)) * ((Real.exp u : ℝ) : ℂ) ^ (-(s + 1)))
      = ∫ u in Ioi (0 : ℝ), (mertensFunctionReal (Real.exp u) : ℂ) * Complex.exp (-s * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hcpow : ((Real.exp u : ℝ) : ℂ) ^ (-(s + 1)) = Complex.exp (u * (-(s + 1))) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
        ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    rw [abs_of_pos (Real.exp_pos u), hcpow, Complex.real_smul, Complex.ofReal_exp]
    unfold mertensFunctionReal
    push_cast
    rw [mul_comm (Complex.exp (u : ℂ)), mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hcongr] at hM
  rw [one_div, mul_inv, hM, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]

/-! ## The one-sided measure -/

/-- The clipped density `ε e^{t/2} - ηM(e^t) + K`. -/
def mertensDensity (η ε K : ℝ) (t : ℝ) : NNReal :=
  Real.toNNReal (ε * Real.exp (t / 2) - η * mertensFunctionReal (Real.exp t) + K)

theorem measurable_mertensDensity (η ε K : ℝ) : Measurable (mertensDensity η ε K) := by
  unfold mertensDensity
  refine Measurable.real_toNNReal ?_
  refine Measurable.add (Measurable.sub ?_ ?_) measurable_const
  · exact measurable_const.mul (Real.measurable_exp.comp (measurable_id.div_const 2))
  · exact measurable_const.mul (measurable_mertensFunctionReal.comp Real.measurable_exp)

/-- `ν = (ε e^{t/2} - ηM(e^t) + K) dt` on `(0, ∞)`. -/
def mertensMeasure (η ε K : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (mertensDensity η ε K u : ENNReal))

theorem mertensDensity_le {η ε K : ℝ} (hη : |η| = 1) (hε : 0 ≤ ε) (hK : 0 ≤ K) {t : ℝ}
    (ht : 0 < t) : ((mertensDensity η ε K t : ℝ)) ≤ (ε + K + 1) * Real.exp t := by
  unfold mertensDensity
  rw [Real.coe_toNNReal']
  have h1 : Real.exp (t / 2) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
  have h2 : -(η * mertensFunctionReal (Real.exp t)) ≤ Real.exp t := by
    have := abs_mertensFunctionReal_exp_le t
    have h3 : |η * mertensFunctionReal (Real.exp t)| ≤ Real.exp t := by
      rw [abs_mul, hη, one_mul]; exact this
    linarith [neg_abs_le (η * mertensFunctionReal (Real.exp t))]
  have h4 : 1 ≤ Real.exp t := Real.one_le_exp ht.le
  have hE := Real.exp_pos t
  refine max_le ?_ (by positivity)
  nlinarith

theorem mertensDensity_coe {η ε ε' K : ℝ} (hεε' : ε' ≤ ε)
    (hg : ∀ t, 0 < t → η * mertensFunctionReal (Real.exp t) ≤ ε' * Real.exp (t / 2) + K) {t : ℝ}
    (ht : 0 < t) :
    ((mertensDensity η ε K t : ℝ))
      = ε * Real.exp (t / 2) - η * mertensFunctionReal (Real.exp t) + K := by
  unfold mertensDensity
  have h := hg t ht
  have hE := Real.exp_pos (t / 2)
  rw [Real.coe_toNNReal _ (by nlinarith)]

theorem laplaceMass_mertensMeasure_ne_top {η ε K σ : ℝ} (hη : |η| = 1) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hσ : 1 < σ) : laplaceMass (mertensMeasure η ε K) σ ≠ ⊤ := by
  unfold laplaceMass mertensMeasure
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_mertensDensity η ε K).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top
    (integrableOn_exp_majorant (C := ε + K + 1) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (mertensDensity_le hη hε hK hu) (Real.exp_pos _).le

theorem laplaceMass_mertensMeasure_eq_top {η ε ε' K σ : ℝ} (hεε' : ε' < ε)
    (hg : ∀ t, 0 < t → η * mertensFunctionReal (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    (hσ : σ ≤ 1 / 2) : laplaceMass (mertensMeasure η ε K) σ = ⊤ := by
  unfold laplaceMass mertensMeasure
  have hg' : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_mertensDensity η ε K).coe_nnreal_ennreal hg', eq_top_iff]
  have hδ : 0 < ε - ε' := by linarith
  calc (⊤ : ENNReal) = ENNReal.ofReal (ε - ε') * volume (Ioi (0 : ℝ)) := by
        rw [Real.volume_Ioi, ENNReal.mul_top (by simpa using hδ)]
    _ = ∫⁻ _ in Ioi (0 : ℝ), ENNReal.ofReal (ε - ε') := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), ((fun u => (mertensDensity η ε K u : ENNReal))
          * fun u => ENNReal.ofReal (Real.exp (-σ * u))) u := by
        refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := hu
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [mertensDensity_coe hεε'.le hg hu0]
        have h1 := hg u hu0
        have h2 : 1 ≤ Real.exp (u / 2) * Real.exp (-σ * u) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        have hE := Real.exp_pos (-σ * u)
        have hE2 := Real.exp_pos (u / 2)
        have h3 : (ε - ε') * Real.exp (u / 2) ≤ ε * Real.exp (u / 2)
            - η * mertensFunctionReal (Real.exp u) + K := by linarith
        calc ε - ε' ≤ (ε - ε') * (Real.exp (u / 2) * Real.exp (-σ * u)) :=
              le_mul_of_one_le_right hδ.le h2
          _ = (ε - ε') * Real.exp (u / 2) * Real.exp (-σ * u) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h3 hE.le

/-- The abscissa of `ν` lies in `[½, 2]`. -/
theorem isAbscissa_mertensMeasure {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε') (hεε' : ε' < ε)
    (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * mertensFunctionReal (Real.exp t) ≤ ε' * Real.exp (t / 2) + K) :
    IsAbscissa (mertensMeasure η ε K) (sInf {σ : ℝ | laplaceMass (mertensMeasure η ε K) σ ≠ ⊤})
      ∧ 1 / 2 ≤ sInf {σ : ℝ | laplaceMass (mertensMeasure η ε K) σ ≠ ⊤}
      ∧ sInf {σ : ℝ | laplaceMass (mertensMeasure η ε K) σ ≠ ⊤} ≤ 2 := by
  have hε : 0 ≤ ε := by linarith
  set S := {σ : ℝ | laplaceMass (mertensMeasure η ε K) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, 1 / 2 < σ := by
    intro σ hσ
    by_contra hle
    exact hσ (laplaceMass_mertensMeasure_eq_top hεε' hg (not_lt.mp hle))
  have hbdd : BddBelow S := ⟨1 / 2, fun σ hσ => (hpos σ hσ).le⟩
  have h2S : (2:ℝ) ∈ S := laplaceMass_mertensMeasure_ne_top hη hε hK (by norm_num)
  have hne : S.Nonempty := ⟨2, h2S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le,
    csInf_le hbdd h2S⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)


/-! ## The transform and Landau's theorem -/

/-- `Q(z) = (z-1)/(z·(z-1)ζ(z)) = 1/(zζ(z))`, holomorphic wherever `z(z-1)ζ(z) ≠ 0`. -/
def mertensKernel (z : ℂ) : ℂ := (z - 1) / (z * zetaResidueUnit z)

theorem mertensKernel_eq {s : ℂ} (hs : s ≠ 1) : mertensKernel s = 1 / (s * riemannZeta s) := by
  unfold mertensKernel
  rw [zetaResidueUnit, Function.update_of_ne hs]
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  by_cases hs0 : s = 0
  · rw [hs0]; simp
  by_cases hz : riemannZeta s = 0
  · rw [hz]; simp
  field_simp

theorem analyticAt_mertensKernel {z : ℂ} (hz0 : z ≠ 0) (hz : zetaResidueUnit z ≠ 0) :
    AnalyticAt ℂ mertensKernel z := by
  unfold mertensKernel
  exact (analyticAt_id.sub analyticAt_const).div (analyticAt_id.mul (analyticAt_zetaResidueUnit z))
    (mul_ne_zero hz0 hz)

theorem zetaResidueUnit_ofReal_ne_zero {t : ℝ} (ht : 0 < t) : zetaResidueUnit (t : ℂ) ≠ 0 := by
  obtain ⟨r, hr, hzr⟩ := exists_zetaResidueUnit_ofReal_eq_pos ht
  rw [hzr]; exact_mod_cast hr.ne'

/-- The continuation `Φ(z) = ε/(z-½) + K/z - ηQ(z)`. -/
def mertensContinuation (η ε K : ℝ) (z : ℂ) : ℂ :=
  ε / (z - 1 / 2) + K / z - η * mertensKernel z

theorem analyticAt_mertensContinuation (η ε K : ℝ) {z : ℂ} (hzh : z ≠ 1 / 2) (hz0 : z ≠ 0)
    (hz : zetaResidueUnit z ≠ 0) : AnalyticAt ℂ (mertensContinuation η ε K) z := by
  unfold mertensContinuation
  exact ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzh)).add
    (analyticAt_const.div analyticAt_id hz0)).sub
    (analyticAt_const.mul (analyticAt_mertensKernel hz0 hz))

/-- On `Re s > 1` the complex transform of `ν` is `Φ(s)`. -/
theorem complexLaplace_mertensMeasure_eq {η ε ε' K : ℝ} (hε' : 0 ≤ ε') (hεε' : ε' ≤ ε)
    (hg : ∀ t, 0 < t → η * mertensFunctionReal (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    {s : ℂ} (hs : 1 < s.re) :
    complexLaplace (mertensMeasure η ε K) s = mertensContinuation η ε K s := by
  have hε : 0 ≤ ε := le_trans hε' hεε'
  have hs0 : 0 < s.re := by linarith
  have hsh : 0 < (s - 1 / 2).re := by simp; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs; linarith
  have hcexp : ∀ w : ℂ, Continuous (fun u : ℝ => Complex.exp (-w * (u : ℂ))) := fun w =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hexpInt : ∀ w : ℂ, 0 < w.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-w * (u : ℂ))) (Ioi 0) := fun w hw =>
    (exp_neg_integrableOn_Ioi 0 hw).mono' (hcexp w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  have hMint : IntegrableOn
      (fun u : ℝ => (mertensFunctionReal (Real.exp u) : ℂ) * Complex.exp (-s * u))
      (Ioi 0) := by
    have hmaj : IntegrableOn (fun u : ℝ => Real.exp (-(s.re - 1) * u)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 (by linarith)
    refine hmaj.mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.measurable.comp
        (measurable_mertensFunctionReal.comp Real.measurable_exp)).aestronglyMeasurable.mul
        (hcexp s).aestronglyMeasurable)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u _
      rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |mertensFunctionReal (Real.exp u)| * Real.exp (-s.re * u)
          ≤ Real.exp u * Real.exp (-s.re * u) :=
            mul_le_mul_of_nonneg_right (abs_mertensFunctionReal_exp_le u) (Real.exp_pos _).le
        _ = Real.exp (-(s.re - 1) * u) := by rw [← Real.exp_add]; ring_nf
  unfold complexLaplace mertensMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integral_withDensity_eq_integral_smul (measurable_mertensDensity η ε K)]
  have hpt : ∀ u ∈ Ioi (0:ℝ), mertensDensity η ε K u • Complex.exp (-s * (u : ℂ))
      = ((ε : ℂ) * Complex.exp (-(s - 1 / 2) * (u : ℂ)) + (K : ℂ) * Complex.exp (-s * (u : ℂ)))
        - (η : ℂ) * ((mertensFunctionReal (Real.exp u) : ℂ) * Complex.exp (-s * u)) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul, mertensDensity_coe hεε' hg hu]
    push_cast
    rw [show Complex.exp (-(s - 1 / 2) * (u : ℂ))
      = Complex.exp ((u : ℂ) / 2) * Complex.exp (-s * (u : ℂ)) by
        rw [← Complex.exp_add]; congr 1; ring]
    ring
  have i1 : IntegrableOn (fun u : ℝ => (ε : ℂ) * Complex.exp (-(s - 1 / 2) * (u : ℂ))) (Ioi 0) :=
    (hexpInt _ hsh).const_mul _
  have i2 : IntegrableOn (fun u : ℝ => (K : ℂ) * Complex.exp (-s * (u : ℂ))) (Ioi 0) :=
    (hexpInt _ hs0).const_mul _
  have i3 : IntegrableOn (fun u : ℝ => (η : ℂ) * ((mertensFunctionReal (Real.exp u) : ℂ)
      * Complex.exp (-s * u))) (Ioi 0) := hMint.const_mul _
  have i12 : IntegrableOn (fun u : ℝ => (ε : ℂ) * Complex.exp (-(s - 1 / 2) * (u : ℂ))
      + (K : ℂ) * Complex.exp (-s * (u : ℂ))) (Ioi 0) := i1.add i2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_cexp_neg_mul_Ioi hsh,
    integral_cexp_neg_mul_Ioi hs0, integral_mertensFunctionReal_exp_mul_cexp hs]
  unfold mertensContinuation
  rw [mertensKernel_eq hs1]
  ring

/-- **Landau: the abscissa of `ν` is `½`.** -/
theorem abscissa_mertensMeasure_eq {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε') (hεε' : ε' < ε)
    (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * mertensFunctionReal (Real.exp t) ≤ ε' * Real.exp (t / 2) + K) :
    IsAbscissa (mertensMeasure η ε K) (1 / 2) := by
  obtain ⟨hc, hac, hc2⟩ := isAbscissa_mertensMeasure hη hε' hεε' hK hg
  set c : ℝ := sInf {σ : ℝ | laplaceMass (mertensMeasure η ε K) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hcpos : 0 < c := by linarith
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hch : (c : ℂ) ≠ 1 / 2 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hZ : zetaResidueUnit (c : ℂ) ≠ 0 := zetaResidueUnit_ofReal_ne_zero hcpos
    have hev : ∀ᶠ z in 𝓝 (c : ℂ), zetaResidueUnit z ≠ 0 ∧ z ≠ 0 ∧ z ≠ 1 / 2 :=
      ((analyticAt_zetaResidueUnit _).continuousAt.eventually_ne hZ).and
        ((eventually_ne_nhds hc0).and (eventually_ne_nhds hch))
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine false_of_analyticAt_abscissa hc hd (Φ := mertensContinuation η ε K) ?_ ?_
    · intro z hz
      obtain ⟨h1, h2, h3⟩ := hball hz
      exact analyticAt_mertensContinuation η ε K h3 h2 h1
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (mertensMeasure η ε K))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (mertensMeasure η ε K) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (mertensMeasure η ε K)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => mertensContinuation η ε K (t : ℂ)) (Ioi c) := by
        intro t ht
        have hth : 1 / 2 < t := lt_trans hpos ht
        have ht0 : 0 < t := by linarith
        have h1 : AnalyticAt ℂ (mertensContinuation η ε K) (t : ℂ) := by
          refine analyticAt_mertensContinuation η ε K ?_ (by exact_mod_cast ht0.ne')
            (zetaResidueUnit_ofReal_ne_zero ht0)
          intro h
          have := congrArg Complex.re h
          simp at this
          linarith
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h3mem : (3 : ℝ) ∈ Ioi c := by show c < 3; linarith
      have hfg : (fun t : ℝ => complexLaplace (mertensMeasure η ε K) (t : ℂ)) =ᶠ[𝓝 (3:ℝ)]
          (fun t : ℝ => mertensContinuation η ε K (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (2 : ℝ) < 3) (by norm_num : (3:ℝ) < 4)) fun t ht => ?_
        have ht1 : 1 < (t : ℂ).re := by simp; linarith [ht.1]
        exact complexLaplace_mertensMeasure_eq hε' hεε'.le hg ht1
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h3mem hfg
      have hσ : complexLaplace (mertensMeasure η ε K) (σ : ℂ)
          = mertensContinuation η ε K (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- **The continuation identity on `Re z > ½`.**  `H(z)·z·(z-1)ζ(z) = η(z-1)` with
`H(z) = ε/(z-½) + K/z - ∫ e^{-zt} dν`. -/
theorem mertens_continuation_identity {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε')
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * mertensFunctionReal (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    {z : ℂ} (hz : 1 / 2 < z.re) :
    (ε / (z - 1 / 2) + K / z - complexLaplace (mertensMeasure η ε K) z)
      * (z * zetaResidueUnit z) = η * (z - 1) := by
  have hc := abscissa_mertensMeasure_eq hη hε' hεε' hK hg
  set U : Set ℂ := {w : ℂ | 1 / 2 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hne0 : ∀ w ∈ U, w ≠ 0 := fun w hw h => by
    rw [h] at hw; simp [hU] at hw; linarith
  have hneh : ∀ w ∈ U, w - 1 / 2 ≠ 0 := fun w hw h => by
    have := congrArg Complex.re h; simp [hU] at this hw; linarith
  set F : ℂ → ℂ := fun w => (ε / (w - 1 / 2) + K / w
    - complexLaplace (mertensMeasure η ε K) w) * (w * zetaResidueUnit w) with hF
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (ε : ℂ) / (w - 1 / 2)) w :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
        (hneh w hw)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (K : ℂ) / w) w :=
      (differentiableAt_const _).div differentiableAt_id (hne0 w hw)
    have h3 := (hasDerivAt_complexLaplace hc hw).differentiableAt
    have h4 : DifferentiableAt ℂ (fun w => w * zetaResidueUnit w) w :=
      differentiableAt_id.mul (analyticAt_zetaResidueUnit w).differentiableAt
    exact (((h1.add h2).sub h3).mul h4).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F U := hFd.analyticOnNhd hUo
  have hGa : AnalyticOnNhd ℂ (fun w : ℂ => (η : ℂ) * (w - 1)) U := fun w _ =>
    analyticAt_const.mul (analyticAt_id.sub analyticAt_const)
  have h2U : (2 : ℂ) ∈ U := by simp [hU]; norm_num
  have hev : F =ᶠ[𝓝 (2 : ℂ)] fun w : ℂ => (η : ℂ) * (w - 1) := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    have hw1 : 1 < w.re := hw
    have hw0 : w ≠ 0 := by intro h; rw [h, Complex.zero_re] at hw1; linarith
    have hZ : zetaResidueUnit w ≠ 0 := by
      have hw1' : w ≠ 1 := by intro h; rw [h, Complex.one_re] at hw1; linarith
      rw [zetaResidueUnit, Function.update_of_ne hw1']
      exact mul_ne_zero (sub_ne_zero.mpr hw1') (riemannZeta_ne_zero_of_one_lt_re hw1)
    simp only [hF]
    rw [complexLaplace_mertensMeasure_eq hε' hεε'.le hg hw1]
    unfold mertensContinuation mertensKernel
    field_simp
    ring
  have hEq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa (convex_halfSpace_re_gt _).isPreconnected
    h2U hev
  exact hEq hz


/-! ## The zero on the line -/

/-- The real transform at a real point of `(½, ∞)`, through the continuation identity. -/
theorem laplaceReal_mertensMeasure_le {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε')
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * mertensFunctionReal (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    {r : ℝ} (hr : 0 < r) :
    laplaceReal (mertensMeasure η ε K) (1 / 2 + r)
      ≤ ε / r + 2 * K + ‖mertensKernel ((1 / 2 + r : ℝ) : ℂ)‖ := by
  set w : ℂ := ((1 / 2 + r : ℝ) : ℂ) with hw
  have hwre : 1 / 2 < w.re := by simp [hw]; linarith
  have hw0 : w ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hw] at this; linarith
  have hZ : zetaResidueUnit w ≠ 0 := zetaResidueUnit_ofReal_ne_zero (by linarith)
  have hid := mertens_continuation_identity hη hε' hεε' hK hg hwre
  have hCL : complexLaplace (mertensMeasure η ε K) w
      = ε / (w - 1 / 2) + K / w - η * mertensKernel w := by
    have hwz : w * zetaResidueUnit w ≠ 0 := mul_ne_zero hw0 hZ
    have hH : ε / (w - 1 / 2) + K / w - complexLaplace (mertensMeasure η ε K) w
        = η * mertensKernel w := by
      unfold mertensKernel
      rw [← mul_div_assoc, eq_div_iff hwz]
      exact hid
    linear_combination (-1 : ℂ) * hH
  have hnn : 0 ≤ laplaceReal (mertensMeasure η ε K) (1 / 2 + r) :=
    integral_nonneg fun u => (Real.exp_pos _).le
  have hcl := complexLaplace_ofReal (mertensMeasure η ε K) (1 / 2 + r)
  rw [← hw] at hcl
  have hnorm : laplaceReal (mertensMeasure η ε K) (1 / 2 + r)
      = ‖complexLaplace (mertensMeasure η ε K) w‖ := by
    rw [hcl, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hnorm, hCL]
  have hwh : w - 1 / 2 = (r : ℂ) := by rw [hw]; push_cast; ring
  have h1 : ‖(ε : ℂ) / (w - 1 / 2)‖ = ε / r := by
    rw [hwh, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hr, abs_of_nonneg (by linarith)]
  have h2 : ‖(K : ℂ) / w‖ ≤ 2 * K := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK, hw, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : ‖(η : ℂ) * mertensKernel w‖ = ‖mertensKernel w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hη, one_mul]
  calc ‖(ε : ℂ) / (w - 1 / 2) + K / w - η * mertensKernel w‖
      ≤ ‖(ε : ℂ) / (w - 1 / 2)‖ + ‖(K : ℂ) / w‖ + ‖(η : ℂ) * mertensKernel w‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _ |>.trans_eq (by ring))
    _ ≤ ε / r + 2 * K + ‖mertensKernel w‖ := by rw [h1, h3]; linarith

/-- **The local inequality at a zero.**  Near a zero `ρ = ½ + iγ` with `(z-1)ζ(z) = (z-ρ)^m g(z)`,
`|ρ+r-1|/(|ρ+r||g(ρ+r)|) ≤ r^{m-1}(ε + Cr)` for all small `r > 0`. -/
theorem eventually_mertens_local_le {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε')
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * mertensFunctionReal (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    {ρ : ℂ} (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) {m : ℕ} (hm : 1 ≤ m) {G : ℂ → ℂ}
    (hGan : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0)
    (hfac : ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = (z - ρ) ^ m • G z) :
    ∃ C : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖ρ + r - 1‖ / (‖ρ + r‖ * ‖G (ρ + r)‖) ≤ r ^ (m - 1) * (ε + r * C) := by
  have hε : 0 ≤ ε := by linarith
  set γ : ℝ := |ρ.im| with hγ
  have hγ0 : 0 < γ := abs_pos.mpr hρim
  have hQc : ContinuousAt (fun r : ℝ => mertensKernel ((1 / 2 + r : ℝ) : ℂ)) 0 := by
    have hh : ((1 / 2 + 0 : ℝ) : ℂ) ≠ 0 := by norm_num
    have hZ : zetaResidueUnit ((1 / 2 + 0 : ℝ) : ℂ) ≠ 0 :=
      zetaResidueUnit_ofReal_ne_zero (by norm_num)
    have hf : ContinuousAt (fun r : ℝ => ((1 / 2 + r : ℝ) : ℂ)) 0 := by fun_prop
    exact ContinuousAt.comp (g := mertensKernel) (f := fun r : ℝ => ((1 / 2 + r : ℝ) : ℂ))
      (analyticAt_mertensKernel hh hZ).continuousAt hf
  set B : ℝ := ‖mertensKernel ((1 / 2 + 0 : ℝ) : ℂ)‖ + 1 with hB
  have hQb : ∀ᶠ r in 𝓝 (0 : ℝ), ‖mertensKernel ((1 / 2 + r : ℝ) : ℂ)‖ ≤ B := by
    have := hQc.norm.eventually (gt_mem_nhds (show
      ‖mertensKernel ((1 / 2 + 0 : ℝ) : ℂ)‖ < B by rw [hB]; linarith))
    exact this.mono fun r hr => hr.le
  have htend : Tendsto (fun r : ℝ => ρ + r) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    have h : Tendsto (fun r : ℝ => ρ + r) (𝓝 (0 : ℝ)) (𝓝 (ρ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hfac' := htend.eventually hfac
  have hGne : ∀ᶠ r : ℝ in 𝓝[>] 0, G (ρ + r) ≠ 0 :=
    htend.eventually (hGan.continuousAt.eventually_ne hG0)
  refine ⟨(ε + K) / γ + 2 * K + B, ?_⟩
  filter_upwards [hfac', hGne, self_mem_nhdsWithin, nhdsWithin_le_nhds hQb] with r hr hGr hr0 hQr
  have hr0' : 0 < r := hr0
  set z : ℂ := ρ + r with hz
  have hzre : z.re = 1 / 2 + r := by simp [hz, hρre]
  have hzim : z.im = ρ.im := by simp [hz]
  have hzre' : 1 / 2 < z.re := by rw [hzre]; linarith
  have hz0 : z ≠ 0 := by intro h; rw [h] at hzre; simp at hzre; linarith
  have hid := mertens_continuation_identity hη hε' hεε' hK hg hzre'
  set H : ℂ := ε / (z - 1 / 2) + K / z - complexLaplace (mertensMeasure η ε K) z with hHdef
  rw [hr] at hid
  have hzr : z - ρ = (r : ℂ) := by rw [hz]; ring
  rw [hzr] at hid
  -- the norm identity
  have hnormid : ‖H‖ * (‖z‖ * (r ^ m * ‖G z‖)) = ‖z - 1‖ := by
    have := congrArg norm hid
    rw [norm_mul, norm_mul, smul_eq_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0', norm_mul, Complex.norm_real, Real.norm_eq_abs, hη, one_mul] at this
    exact this
  have hGz : 0 < ‖G z‖ := norm_pos_iff.mpr hGr
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hF : ‖z - 1‖ / (‖z‖ * ‖G z‖) = r ^ m * ‖H‖ := by
    rw [← hnormid]; field_simp
  -- the upper bound for `H`
  have hγle : γ ≤ ‖z - 1 / 2‖ := by
    have := Complex.abs_im_le_norm (z - 1 / 2)
    rw [Complex.sub_im, hzim] at this
    simpa using this
  have hγle' : γ ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rw [hzim] at this
    exact this
  have hlap := laplaceReal_mertensMeasure_le hη hε' hεε' hK hg hr0'
  have hCL : ‖complexLaplace (mertensMeasure η ε K) z‖
      ≤ laplaceReal (mertensMeasure η ε K) (1 / 2 + r) := by
    have := norm_complexLaplace_le (mertensMeasure η ε K) z
    rw [hzre] at this
    exact this
  have h1 : ‖(ε : ℂ) / (z - 1 / 2)‖ ≤ ε / γ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
    exact div_le_div_of_nonneg_left hε hγ0 hγle
  have h2 : ‖(K : ℂ) / z‖ ≤ K / γ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
    exact div_le_div_of_nonneg_left hK hγ0 hγle'
  have hHle : ‖H‖ ≤ ε / γ + K / γ + (ε / r + 2 * K + B) := by
    have hn1 := norm_sub_le ((ε : ℂ) / (z - 1 / 2) + K / z)
      (complexLaplace (mertensMeasure η ε K) z)
    have hn2 := norm_add_le ((ε : ℂ) / (z - 1 / 2)) ((K : ℂ) / z)
    rw [hHdef]
    linarith
  have hrH : r * ‖H‖ ≤ ε + r * ((ε + K) / γ + 2 * K + B) := by
    have := mul_le_mul_of_nonneg_left hHle hr0'.le
    have e : r * (ε / γ + K / γ + (ε / r + 2 * K + B))
        = ε + r * ((ε + K) / γ + 2 * K + B) := by field_simp; ring
    linarith
  rw [hF]
  have hpow : r ^ m = r ^ (m - 1) * r := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow, mul_assoc]
  exact mul_le_mul_of_nonneg_left hrH (pow_nonneg hr0'.le _)


/-- **A one-sided bound forces a simple zero with a small residue.**  If `ηM(x) ≤ ε'√x`
(in the form `ηM(e^t) ≤ ε'e^{t/2} + K`) and `(z-1)ζ(z) = (z-ρ)^m G(z)` near a zero
`ρ = ½ + iγ`, then `m = 1` and `|ρ-1|/(|ρ||G(ρ)|) ≤ ε'`. -/
theorem mertens_zero_simple_of_oneSided {η ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε') (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * mertensFunctionReal (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    {ρ : ℂ} (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) (hρ0 : zetaResidueUnit ρ = 0) {m : ℕ}
    {G : ℂ → ℂ} (hGan : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0)
    (hfac : ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = (z - ρ) ^ m • G z) :
    m = 1 ∧ ‖ρ - 1‖ / (‖ρ‖ * ‖G ρ‖) ≤ ε' := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      have := hfac.self_of_nhds
      rw [h, pow_zero, one_smul, hρ0] at this
      exact hG0 this.symm
    · exact h
  have hρ0' : ρ ≠ 0 := by intro h; rw [h, Complex.zero_re] at hρre; norm_num at hρre
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρre; norm_num at hρre
  set F₀ : ℝ := ‖ρ - 1‖ / (‖ρ‖ * ‖G ρ‖) with hF₀
  have hF₀pos : 0 < F₀ := by
    rw [hF₀]
    exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hρ1))
      (mul_pos (norm_pos_iff.mpr hρ0') (norm_pos_iff.mpr hG0))
  have htend : Tendsto (fun r : ℝ => ρ + r) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    have h : Tendsto (fun r : ℝ => ρ + r) (𝓝 (0 : ℝ)) (𝓝 (ρ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hFt : Tendsto (fun r : ℝ => ‖ρ + r - 1‖ / (‖ρ + r‖ * ‖G (ρ + r)‖)) (𝓝[>] (0 : ℝ))
      (𝓝 F₀) := by
    have h1 : Tendsto (fun r : ℝ => ‖ρ + r - 1‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖ρ - 1‖) :=
      (htend.sub_const 1).norm
    have h2 : Tendsto (fun r : ℝ => ‖ρ + r‖ * ‖G (ρ + r)‖) (𝓝[>] (0 : ℝ))
        (𝓝 (‖ρ‖ * ‖G ρ‖)) :=
      htend.norm.mul ((hGan.continuousAt.tendsto.comp htend).norm)
    exact h1.div h2 (mul_pos (norm_pos_iff.mpr hρ0') (norm_pos_iff.mpr hG0)).ne'
  -- for every `ε > ε'`, the local inequality
  have hlocal : ∀ ε : ℝ, ε' < ε → (m = 1 ∧ F₀ ≤ ε) := by
    intro ε hεε'
    have hε : 0 ≤ ε := by linarith
    obtain ⟨C, hC⟩ := eventually_mertens_local_le hη hε' hεε' hK hg hρre hρim hm hGan hG0 hfac
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
  refine ⟨(hlocal (ε' + 1) (by linarith)).1, ?_⟩
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  have := (hlocal (ε' + δ / 2) (by linarith)).2
  linarith

/-! ## The square-root oscillation -/

theorem exists_mertens_oneSided_of_eventually {η c : ℝ} (hη : |η| = 1) (hc : 0 ≤ c)
    (h : ∀ᶠ x : ℝ in atTop, η * mertensFunctionReal x ≤ c * Real.sqrt x) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ t, 0 < t → η * mertensFunctionReal (Real.exp t) ≤ c * Real.exp (t / 2) + K := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp h
  refine ⟨|x₀|, abs_nonneg _, fun t ht => ?_⟩
  have hE := Real.exp_pos (t / 2)
  by_cases hxt : x₀ ≤ Real.exp t
  · have := hx₀ (Real.exp t) hxt
    rw [sqrt_exp_eq_exp_half_mul, show 1 / 2 * t = t / 2 by ring] at this
    have : 0 ≤ |x₀| := abs_nonneg _
    linarith
  · have h1 : |η * mertensFunctionReal (Real.exp t)| ≤ Real.exp t := by
      rw [abs_mul, hη, one_mul]; exact abs_mertensFunctionReal_exp_le t
    have h2 := le_abs_self (η * mertensFunctionReal (Real.exp t))
    have h3 : Real.exp t < x₀ := not_le.mp hxt
    have h4 := le_abs_self x₀
    have h5 : 0 ≤ c * Real.exp (t / 2) := mul_nonneg hc hE.le
    linarith

/-- **The Mertens function is `Ω±(√x)`.**  There is `c > 0` with `M(x) > c√x` and `M(x) < -c√x`,
each for arbitrarily large `x`. -/
theorem mertens_omega_pm_sqrt :
    ∃ c : ℝ, 0 < c ∧ (∃ᶠ x : ℝ in atTop, c * Real.sqrt x < mertensFunctionReal x)
      ∧ ∃ᶠ x : ℝ in atTop, mertensFunctionReal x < -(c * Real.sqrt x) := by
  -- a zero on the critical line (Hardy)
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
  -- the local factorization
  have hnot : ¬ ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = 0 := by
    intro hzero
    have hall := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => analyticAt_zetaResidueUnit z) isPreconnected_univ (mem_univ ρ) hzero
    have := hall (mem_univ (1 : ℂ))
    simp at this
  obtain ⟨m, G, hGan, hG0, hfac⟩ :=
    ((analyticAt_zetaResidueUnit ρ).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnot
  set F₀ : ℝ := ‖ρ - 1‖ / (‖ρ‖ * ‖G ρ‖) with hF₀
  have hρ0' : ρ ≠ 0 := by intro h; rw [h, Complex.zero_re] at hρre; norm_num at hρre
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρre; norm_num at hρre
  have hF₀pos : 0 < F₀ := by
    rw [hF₀]
    exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hρ1))
      (mul_pos (norm_pos_iff.mpr hρ0') (norm_pos_iff.mpr hG0))
  refine ⟨F₀ / 2, by positivity, ?_, ?_⟩
  · by_contra hno
    rw [Filter.not_frequently] at hno
    have h' : ∀ᶠ x : ℝ in atTop, (1 : ℝ) * mertensFunctionReal x ≤ F₀ / 2 * Real.sqrt x :=
      hno.mono fun x hx => by rw [one_mul]; exact not_lt.mp hx
    obtain ⟨K, hK, hg⟩ := exists_mertens_oneSided_of_eventually (by simp) (by positivity) h'
    have := (mertens_zero_simple_of_oneSided (by simp) (by positivity) hK hg hρre hρim hρ0 hGan
      hG0 hfac).2
    rw [← hF₀] at this
    linarith
  · by_contra hno
    rw [Filter.not_frequently] at hno
    have h' : ∀ᶠ x : ℝ in atTop, (-1 : ℝ) * mertensFunctionReal x ≤ F₀ / 2 * Real.sqrt x :=
      hno.mono fun x hx => by have := not_lt.mp hx; linarith
    obtain ⟨K, hK, hg⟩ := exists_mertens_oneSided_of_eventually (by simp) (by positivity) h'
    have := (mertens_zero_simple_of_oneSided (by simp) (by positivity) hK hg hρre hρim hρ0 hGan
      hG0 hfac).2
    rw [← hF₀] at this
    linarith

/-- **`M(x)` is not `o(√x)`.** -/
theorem not_mertensFunctionReal_isLittleO_sqrt :
    ¬ (fun x : ℝ => mertensFunctionReal x) =o[atTop] fun x => Real.sqrt x := by
  intro h
  obtain ⟨c, hc, hfr, -⟩ := mertens_omega_pm_sqrt
  have hb := h.bound hc
  have := hfr.and_eventually hb
  obtain ⟨x, hx1, hx2⟩ := this.exists
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)] at hx2
  linarith [le_abs_self (mertensFunctionReal x)]


/-- **A one-sided square-root bound for `M` implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_mertens_oneSided {η c : ℝ} (hη : |η| = 1) (hc : 0 ≤ c)
    (h : ∀ᶠ x : ℝ in atTop, η * mertensFunctionReal x ≤ c * Real.sqrt x) : RiemannHypothesis := by
  obtain ⟨K, hK, hg⟩ := exists_mertens_oneSided_of_eventually hη hc h
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro z hz hzero
  have hid := mertens_continuation_identity hη hc (lt_add_one c) hK hg hz
  rw [hzero, mul_zero, mul_zero] at hid
  have hη0 : (η : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; rw [this] at hη; simp at hη
  have hz1 : z = 1 := by
    have := (mul_eq_zero.mp hid.symm).resolve_left hη0
    exact sub_eq_zero.mp this
  rw [hz1, zetaResidueUnit_one] at hzero
  exact one_ne_zero hzero

/-- **A one-sided square-root bound for `M` makes every zero on the critical line simple.** -/
theorem deriv_zetaResidueUnit_ne_zero_of_mertens_oneSided {η c : ℝ} (hη : |η| = 1) (hc : 0 ≤ c)
    (h : ∀ᶠ x : ℝ in atTop, η * mertensFunctionReal x ≤ c * Real.sqrt x) {ρ : ℂ}
    (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) (hρ0 : zetaResidueUnit ρ = 0) :
    deriv zetaResidueUnit ρ ≠ 0 := by
  obtain ⟨K, hK, hg⟩ := exists_mertens_oneSided_of_eventually hη hc h
  have hnot : ¬ ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = 0 := by
    intro hzero
    have hall := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => analyticAt_zetaResidueUnit z) isPreconnected_univ (mem_univ ρ) hzero
    have := hall (mem_univ (1 : ℂ))
    simp at this
  obtain ⟨m, G, hGan, hG0, hfac⟩ :=
    ((analyticAt_zetaResidueUnit ρ).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnot
  have hm := (mertens_zero_simple_of_oneSided hη hc hK hg hρre hρim hρ0 hGan hG0 hfac).1
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
