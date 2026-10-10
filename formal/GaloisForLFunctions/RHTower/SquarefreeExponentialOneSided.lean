import GaloisForLFunctions.RHTower.SquarefreeExponentialRH
import GaloisForLFunctions.RHTower.LiouvilleExponentialSumSimplicity

/-!
# One-sided bounds for the exponentially weighted squarefree count

Let `A(t) = Σ_{n ≥ 1} μ(n)² e^{-nt}`, `c = 6/π²` and `e(t) = A(t) - c/t`.

**Theorem** (`riemannHypothesis_iff_sqfError_upper`, `riemannHypothesis_iff_sqfError_lower`).
RH holds iff `e(t) ≤ C_ε t^{-1/4-ε}` on `(0, 1]` for every `ε > 0`, iff `-e(t) ≤ C_ε t^{-1/4-ε}`
on `(0, 1]` for every `ε > 0`. An upper-bound sieve for squarefree numbers with exponential weights
and error `t^{-1/4-ε}` is equivalent to RH, and so is the corresponding lower bound.

More generally (`riemannZeta_ne_zero_of_sqfError_oneSided`), a one-sided bound
`η e(t) ≤ C t^{-α}` (`η = ±1`, `0 ≤ α < 1`) makes `ζ` zero-free on the band
`2α < Re s < 2 - 4α`.

**Proof.** In the variable `u = -log t` the density `C e^{αu} - η e(e^{-u})` is nonnegative on
`u > 0`, and its Laplace transform is `C/(z - α) - η 𝓜K(z)` on `Re z > 1`, where `𝓜K` is the
error Mellin transform. Its continuation
`𝓜K = dslope N 1 - 𝓜P`, with `N(z) = (2z-1)Γ(z)Z(z)/Z(2z) - c` and `N(1) = 0`, is holomorphic near
every real point of `(0, ∞)` because `Z(2σ) ≠ 0`. Landau's theorem puts the abscissa at `α`, so
`𝓜K` continues holomorphically to `Re z > α`. The pole-cleared identity and the halving cascade then
finish as in the two-sided case.
-/

open Filter Topology MeasureTheory Set Complex
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open scoped ArithmeticFunction.Moebius

namespace RHTower.SquarefreeExponential

noncomputable section

/-! ## The real error -/

/-- `A(t) = Σ_n μ(n)² e^{-nt}` as a real series. -/
def sqfExpSum (t : ℝ) : ℝ := ∑' n : ℕ, (((μ n : ℤ) : ℝ) * ((μ n : ℤ) : ℝ)) * Real.exp (-((n : ℝ) * t))

theorem profile_eq_ofReal (t : ℝ) : profile t = ((sqfExpSum t : ℝ) : ℂ) := by
  rw [profile, coeffLaplaceProfile, sqfExpSum, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [sqfCoeff, ArithmeticFunction.pmul_apply]
  push_cast
  ring_nf

/-- The real error `e(t) = A(t) - c/t`. -/
def sqfError (t : ℝ) : ℝ := sqfExpSum t - Sieve.squarefreeDensity / t

theorem ofReal_sqfError (t : ℝ) : ((sqfError t : ℝ) : ℂ) = profile t - density / t := by
  rw [sqfError, profile_eq_ofReal, density]
  push_cast
  ring

theorem squarefreeDensity_pos : 0 < Sieve.squarefreeDensity := by
  rw [Sieve.squarefreeDensity_eq]; positivity

theorem squarefreeDensity_le_one : Sieve.squarefreeDensity ≤ 1 := by
  rw [Sieve.squarefreeDensity_eq, div_le_one (by positivity)]
  nlinarith [Real.pi_gt_three]

theorem sqfExpSum_nonneg_le {t : ℝ} (ht : 0 < t) : 0 ≤ sqfExpSum t ∧ sqfExpSum t ≤ 1 / t := by
  have hterm : ∀ n : ℕ, 0 ≤ (((μ n : ℤ) : ℝ) * ((μ n : ℤ) : ℝ)) * Real.exp (-((n : ℝ) * t)) :=
    fun n => mul_nonneg (mul_self_nonneg _) (Real.exp_pos _).le
  have hle : ∀ n : ℕ, (((μ n : ℤ) : ℝ) * ((μ n : ℤ) : ℝ)) * Real.exp (-((n : ℝ) * t)) ≤
      Real.exp (-((n : ℝ) * t)) := by
    intro n
    have hm : |((μ n : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have : ((μ n : ℤ) : ℝ) * ((μ n : ℤ) : ℝ) ≤ 1 := by
      rw [← abs_mul_abs_self]; nlinarith [abs_nonneg ((μ n : ℤ) : ℝ)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le this
  have hsum : Summable fun n : ℕ => Real.exp (-((n : ℝ) * t)) := summable_exp_neg_nat_mul ht
  have hs : Summable fun n : ℕ => (((μ n : ℤ) : ℝ) * ((μ n : ℤ) : ℝ)) * Real.exp (-((n : ℝ) * t)) :=
    Summable.of_nonneg_of_le hterm hle hsum
  refine ⟨tsum_nonneg hterm, ?_⟩
  -- drop the vanishing term `n = 0` and compare with a geometric series
  have hshift : sqfExpSum t = ∑' n : ℕ,
      (((μ (n + 1) : ℤ) : ℝ) * ((μ (n + 1) : ℤ) : ℝ)) * Real.exp (-(((n + 1 : ℕ) : ℝ) * t)) := by
    rw [sqfExpSum, hs.tsum_eq_zero_add]
    simp
  have hr0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable fun n : ℕ => Real.exp (-t) * Real.exp (-t) ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hcmp : ∀ n : ℕ, (((μ (n + 1) : ℤ) : ℝ) * ((μ (n + 1) : ℤ) : ℝ)) *
      Real.exp (-(((n + 1 : ℕ) : ℝ) * t)) ≤ Real.exp (-t) * Real.exp (-t) ^ n := by
    intro n
    refine (hle (n + 1)).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    push_cast
    ring_nf
  have hle2 := Summable.tsum_le_tsum hcmp ((summable_nat_add_iff 1).mpr hs) hgeom
  rw [hshift]
  refine hle2.trans ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hexp : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hkey : t ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  have hpos : 0 < 1 - Real.exp (-t) := by linarith
  rw [← div_eq_mul_inv, div_le_div_iff₀ hpos ht]
  nlinarith [Real.exp_pos t, Real.exp_pos (-t)]

/-- `|e(t)| ≤ 1/t` for `t > 0`. -/
theorem abs_sqfError_le {t : ℝ} (ht : 0 < t) : |sqfError t| ≤ 1 / t := by
  obtain ⟨h0, h1⟩ := sqfExpSum_nonneg_le ht
  have hc0 : 0 ≤ Sieve.squarefreeDensity / t := div_nonneg squarefreeDensity_pos.le ht.le
  have hc1 : Sieve.squarefreeDensity / t ≤ 1 / t :=
    div_le_div_of_nonneg_right squarefreeDensity_le_one ht.le
  rw [sqfError, abs_le]
  constructor <;> linarith

/-- The unconditional `t^{-1}` bound in the form used by the decomposition. -/
theorem errorBound_one :
    ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ 1 * t ^ (-(1 : ℝ)) := by
  intro t ht
  rw [← ofReal_sqfError, Complex.norm_real, Real.norm_eq_abs, one_mul, Real.rpow_neg_one,
    ← one_div]
  exact abs_sqfError_le ht.1

theorem continuousOn_sqfError : ContinuousOn sqfError (Ioi 0) := by
  have h1 : ContinuousOn sqfExpSum (Ioi 0) := by
    have : sqfExpSum = fun t => (profile t).re := by
      funext t; rw [profile_eq_ofReal, Complex.ofReal_re]
    rw [this]
    exact Complex.continuous_re.comp_continuousOn continuousOn_profile
  exact h1.sub (continuousOn_const.div continuousOn_id fun t ht => (mem_Ioi.mp ht).ne')

/-- The error in the logarithmic variable, `F(u) = e(e^{-u})`. -/
def logError (u : ℝ) : ℝ := sqfError (Real.exp (-u))

theorem continuous_logError : Continuous logError :=
  continuousOn_sqfError.comp_continuous (Real.continuous_exp.comp continuous_neg)
    fun _ => Real.exp_pos _

theorem abs_logError_le (u : ℝ) : |logError u| ≤ Real.exp u := by
  have h := abs_sqfError_le (Real.exp_pos (-u))
  rw [logError]
  rwa [one_div, ← Real.exp_neg, neg_neg] at h

/-! ## The continuation of the error transform -/

/-- `N(z) = (2z - 1) Γ(z) Z(z)/Z(2z) - c`, with `Z(w) = (w - 1)ζ(w)`. -/
def numer (z : ℂ) : ℂ :=
  (2 * z - 1) * Complex.Gamma z * zetaResidueUnit z / zetaResidueUnit (2 * z) - density

/-- The continuation `dslope N 1 - 𝓜P` of the error transform. -/
def errorCont (z : ℂ) : ℂ := dslope numer 1 z - mellin tailPiece z

/-- The open region where the continuation is holomorphic. -/
def contRegion : Set ℂ := {z : ℂ | 0 < z.re ∧ zetaResidueUnit (2 * z) ≠ 0}

theorem isOpen_contRegion : IsOpen contRegion := by
  refine (isOpen_lt continuous_const Complex.continuous_re).inter ?_
  exact isOpen_ne_fun
    ((Differentiable.continuous fun w => (analyticAt_zetaResidueUnit w).differentiableAt).comp
      (continuous_const.mul continuous_id)) continuous_const

theorem ofReal_mem_contRegion {σ : ℝ} (hσ : 0 < σ) : (σ : ℂ) ∈ contRegion := by
  refine ⟨by simpa using hσ, ?_⟩
  have := zetaResidueUnit_ofReal_ne_zero (t := 2 * σ) (by linarith)
  simpa using this

theorem numer_one : numer 1 = 0 := by
  have h2 : zetaResidueUnit (2 * 1) = (Real.pi : ℂ) ^ 2 / 6 := by
    rw [mul_one, zetaResidueUnit, Function.update_of_ne (by norm_num : (2 : ℂ) ≠ 1),
      riemannZeta_two]
    norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [numer, h2, zetaResidueUnit_one, Complex.Gamma_one, density, Sieve.squarefreeDensity_eq]
  push_cast
  field_simp
  ring

theorem differentiableOn_numer : DifferentiableOn ℂ numer contRegion := by
  intro z hz
  have hΓ : DifferentiableAt ℂ Complex.Gamma z := by
    refine Complex.differentiableAt_Gamma z fun m hm => ?_
    have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [hz.1]
  have hZ2 : DifferentiableAt ℂ (fun w : ℂ => zetaResidueUnit (2 * w)) z :=
    ((analyticAt_zetaResidueUnit (2 * z)).comp (by fun_prop)).differentiableAt
  exact (((((differentiableAt_const _).mul differentiableAt_id).sub
    (differentiableAt_const _)).mul hΓ).mul
      (analyticAt_zetaResidueUnit z).differentiableAt).div hZ2 hz.2 |>.sub
        (differentiableAt_const _) |>.differentiableWithinAt

theorem analyticOnNhd_errorCont : AnalyticOnNhd ℂ errorCont contRegion := by
  have h1 : (1 : ℂ) ∈ contRegion := by simpa using ofReal_mem_contRegion (σ := 1) one_pos
  have hd : DifferentiableOn ℂ (dslope numer 1) contRegion :=
    (Complex.differentiableOn_dslope (isOpen_contRegion.mem_nhds h1)).mpr differentiableOn_numer
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_contRegion
  exact (hd z hz).sub (differentiableAt_mellin_tailPiece z).differentiableWithinAt

/-- On `Re z > 1` the continuation is the error transform. -/
theorem errorCont_eq_mellin {z : ℂ} (hz : 1 < z.re) : errorCont z = mellin errorPiece z := by
  have hz1 : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz; linarith
  have hz2 : 2 * z ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.one_re] at this
    norm_num at this
    linarith
  have hζ2 : riemannZeta (2 * z) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp only [Complex.mul_re]; norm_num; linarith)
  have hdec := gamma_zeta_div_eq_of_expBound le_rfl errorBound_one hz
  have hd : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have h2z : 2 * z - 1 ≠ 0 := sub_ne_zero.mpr hz2
  rw [errorCont, dslope_of_ne _ hz1, slope_def_field, numer_one, sub_zero]
  have hnum : numer z = (z - 1) *
      (Complex.Gamma z * (riemannZeta z / riemannZeta (2 * z)) - density / (z - 1)) := by
    rw [numer, zetaResidueUnit, Function.update_of_ne hz1, Function.update_of_ne hz2]
    field_simp
  rw [hnum, hdec]
  field_simp
  ring

/-! ## The one-sided measure -/

/-- The density `C e^{αu} + K - η F(u)`, clipped at `0`. -/
def osDensity (η C α K : ℝ) (u : ℝ) : NNReal :=
  Real.toNNReal (C * Real.exp (α * u) + K - η * logError u)

theorem measurable_osDensity (η C α K : ℝ) : Measurable (osDensity η C α K) :=
  Measurable.real_toNNReal (((measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul measurable_id))).add measurable_const).sub (measurable_const.mul
      continuous_logError.measurable))

/-- `ν = (C e^{αu} + K - η F(u)) du` on `(0, ∞)`. -/
def osMeasure (η C α K : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun u => (osDensity η C α K u : ENNReal))

theorem osDensity_coe {η C₀ C α K : ℝ} (hC : C₀ ≤ C)
    (hg : ∀ u, 0 < u → η * logError u ≤ C₀ * Real.exp (α * u) + K) {u : ℝ} (hu : 0 < u) :
    ((osDensity η C α K u : ℝ)) = C * Real.exp (α * u) + K - η * logError u := by
  unfold osDensity
  have h := hg u hu
  have hE := Real.exp_pos (α * u)
  rw [Real.coe_toNNReal _ (by nlinarith)]

theorem osDensity_le {η C α K : ℝ} (hη : |η| = 1) (hα1 : α ≤ 1) (hK : 0 ≤ K) {u : ℝ}
    (hu : 0 < u) : ((osDensity η C α K u : ℝ)) ≤ (|C| + K + 1) * Real.exp u := by
  unfold osDensity
  rw [Real.coe_toNNReal']
  have h1 : Real.exp (α * u) ≤ Real.exp u := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : C * Real.exp (α * u) ≤ |C| * Real.exp u :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg C))
  have h3 : -(η * logError u) ≤ Real.exp u := by
    have := abs_logError_le u
    have h4 : |η * logError u| ≤ Real.exp u := by rw [abs_mul, hη, one_mul]; exact this
    linarith [neg_abs_le (η * logError u)]
  have h5 : K ≤ K * Real.exp u := le_mul_of_one_le_right hK (Real.one_le_exp hu.le)
  refine max_le ?_ (by positivity)
  nlinarith [Real.exp_pos u]

theorem laplaceMass_osMeasure_ne_top {η C α K σ : ℝ} (hη : |η| = 1) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hσ : 1 < σ) : laplaceMass (osMeasure η C α K) σ ≠ ⊤ := by
  unfold laplaceMass osMeasure
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_osDensity η C α K).coe_nnreal_ennreal hg]
  have hmaj : IntegrableOn (fun u : ℝ => (|C| + K + 1) * Real.exp (-(σ - 1) * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
  refine ne_top_of_le_ne_top hmaj.lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := osDensity_le (C := C) hη hα1 hK hu
  calc ((osDensity η C α K u : ℝ)) * Real.exp (-σ * u)
      ≤ (|C| + K + 1) * Real.exp u * Real.exp (-σ * u) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (|C| + K + 1) * Real.exp (-(σ - 1) * u) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

theorem laplaceMass_osMeasure_eq_top {η C₀ C α K σ : ℝ} (hC : C₀ < C)
    (hg : ∀ u, 0 < u → η * logError u ≤ C₀ * Real.exp (α * u) + K) (hσ : σ ≤ α) :
    laplaceMass (osMeasure η C α K) σ = ⊤ := by
  unfold laplaceMass osMeasure
  have hg' : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_osDensity η C α K).coe_nnreal_ennreal hg', eq_top_iff]
  have hδ : 0 < C - C₀ := by linarith
  calc (⊤ : ENNReal) = ENNReal.ofReal (C - C₀) * volume (Ioi (0 : ℝ)) := by
        rw [Real.volume_Ioi, ENNReal.mul_top (by simpa using hδ)]
    _ = ∫⁻ _ in Ioi (0 : ℝ), ENNReal.ofReal (C - C₀) := by rw [setLIntegral_const]
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), ((fun u => (osDensity η C α K u : ENNReal))
          * fun u => ENNReal.ofReal (Real.exp (-σ * u))) u := by
        refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := hu
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [osDensity_coe hC.le hg hu0]
        have h1 := hg u hu0
        have hE := Real.exp_pos (α * u)
        have hE2 := Real.exp_pos (-σ * u)
        have h2 : 1 ≤ Real.exp (α * u) * Real.exp (-σ * u) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        have h3 : (C - C₀) * Real.exp (α * u) ≤ C * Real.exp (α * u) + K - η * logError u := by
          nlinarith
        calc C - C₀ ≤ (C - C₀) * (Real.exp (α * u) * Real.exp (-σ * u)) :=
              le_mul_of_one_le_right hδ.le h2
          _ = (C - C₀) * Real.exp (α * u) * Real.exp (-σ * u) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h3 hE2.le

theorem isAbscissa_osMeasure {η C₀ C α K : ℝ} (hη : |η| = 1) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hC : C₀ < C) (hg : ∀ u, 0 < u → η * logError u ≤ C₀ * Real.exp (α * u) + K) :
    IsAbscissa (osMeasure η C α K) (sInf {σ : ℝ | laplaceMass (osMeasure η C α K) σ ≠ ⊤})
      ∧ α ≤ sInf {σ : ℝ | laplaceMass (osMeasure η C α K) σ ≠ ⊤}
      ∧ sInf {σ : ℝ | laplaceMass (osMeasure η C α K) σ ≠ ⊤} ≤ 2 := by
  set S := {σ : ℝ | laplaceMass (osMeasure η C α K) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, α < σ := by
    intro σ hσ
    by_contra hle
    exact hσ (laplaceMass_osMeasure_eq_top hC hg (not_lt.mp hle))
  have hbdd : BddBelow S := ⟨α, fun σ hσ => (hpos σ hσ).le⟩
  have h2S : (2 : ℝ) ∈ S := laplaceMass_osMeasure_ne_top hη hα1 hK (by norm_num)
  have hne : S.Nonempty := ⟨2, h2S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le,
    csInf_le hbdd h2S⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-- On `Re z > 1` the transform of `ν` is `C/(z - α) + K/z - η 𝓜K(z)`. -/
theorem complexLaplace_osMeasure_eq {η C₀ C α K : ℝ} (hC : C₀ ≤ C) (hα1 : α ≤ 1)
    (hg : ∀ u, 0 < u → η * logError u ≤ C₀ * Real.exp (α * u) + K) {z : ℂ} (hz : 1 < z.re) :
    complexLaplace (osMeasure η C α K) z = C / (z - α) + K / z - η * mellin errorPiece z := by
  have hzα : 0 < (z - α).re := by simp; linarith
  have hz0 : 0 < z.re := by linarith
  have hz1 : 0 < (z - 1).re := by simp; linarith
  have hcexp : ∀ w : ℂ, Continuous (fun u : ℝ => Complex.exp (-w * (u : ℂ))) := fun w =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hnormexp : ∀ (w : ℂ) (u : ℝ), ‖Complex.exp (-w * (u : ℂ))‖ = Real.exp (-w.re * u) := by
    intro w u
    rw [Complex.norm_exp]
    congr 1
    simp
  -- the error integrand on the half-line
  have hFint : IntegrableOn (fun u : ℝ => Complex.exp (-z * u) * (logError u : ℂ)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hz1).mono' ?_ ?_
    · exact ((hcexp z).mul (Complex.continuous_ofReal.comp continuous_logError)).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      rw [norm_mul, hnormexp, Complex.norm_real, Real.norm_eq_abs]
      have h := abs_logError_le u
      calc Real.exp (-z.re * u) * |logError u| ≤ Real.exp (-z.re * u) * Real.exp u :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = Real.exp (-(z - 1).re * u) := by
            rw [← Real.exp_add]; congr 1; simp; ring
  have hmellin : mellin errorPiece z = ∫ u in Ioi (0 : ℝ), Complex.exp (-z * u) * (logError u : ℂ) := by
    rw [RHTower.mellin_eq_integral_cexp]
    have hind : (fun u : ℝ => Complex.exp (-z * u) * errorPiece (Real.exp (-u))) =
        (Ici (0 : ℝ)).indicator (fun u => Complex.exp (-z * u) * (logError u : ℂ)) := by
      funext u
      by_cases hu : 0 ≤ u
      · have hmem : Real.exp (-u) ∈ Ioc (0 : ℝ) 1 :=
          ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith)⟩
        rw [indicator_of_mem (show u ∈ Ici (0 : ℝ) from hu), errorPiece, indicator_of_mem hmem,
          logError, ofReal_sqfError]
      · have hmem : Real.exp (-u) ∉ Ioc (0 : ℝ) 1 := fun h =>
          hu (by linarith [Real.exp_le_one_iff.mp h.2])
        rw [indicator_of_notMem (show u ∉ Ici (0 : ℝ) from hu), errorPiece,
          indicator_of_notMem hmem, mul_zero]
    rw [hind, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  unfold complexLaplace osMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integral_withDensity_eq_integral_smul (measurable_osDensity η C α K)]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), osDensity η C α K u • Complex.exp (-z * (u : ℂ))
      = ((C : ℂ) * Complex.exp (-(z - α) * (u : ℂ)) + (K : ℂ) * Complex.exp (-z * (u : ℂ))) -
          (η : ℂ) * (Complex.exp (-z * u) * (logError u : ℂ)) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul, osDensity_coe hC hg hu]
    push_cast
    rw [show Complex.exp (-(z - α) * (u : ℂ)) = Complex.exp ((α : ℂ) * u) *
        Complex.exp (-z * (u : ℂ)) by rw [← Complex.exp_add]; congr 1; ring]
    ring
  have i1 : IntegrableOn (fun u : ℝ => (C : ℂ) * Complex.exp (-(z - α) * (u : ℂ))) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 hzα).mono' (hcexp _).aestronglyMeasurable ?_).const_mul _
    exact Eventually.of_forall fun u => le_of_eq (hnormexp _ u)
  have i1' : IntegrableOn (fun u : ℝ => (K : ℂ) * Complex.exp (-z * (u : ℂ))) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 hz0).mono' (hcexp _).aestronglyMeasurable ?_).const_mul _
    exact Eventually.of_forall fun u => le_of_eq (hnormexp _ u)
  have i2 : IntegrableOn (fun u : ℝ => (η : ℂ) * (Complex.exp (-z * u) * (logError u : ℂ)))
      (Ioi 0) := hFint.const_mul _
  have i12 : IntegrableOn (fun u : ℝ => (C : ℂ) * Complex.exp (-(z - α) * (u : ℂ)) +
      (K : ℂ) * Complex.exp (-z * (u : ℂ))) (Ioi 0) := i1.add i1'
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub i12 i2,
    integral_add i1 i1', integral_const_mul, integral_const_mul, integral_const_mul,
    integral_cexp_neg_mul_Ioi hzα, integral_cexp_neg_mul_Ioi hz0, ← hmellin]
  ring

/-- The continuation `Φ(z) = C/(z - α) + K/z - η·errorCont(z)`. -/
def osContinuation (η C α K : ℝ) (z : ℂ) : ℂ := C / (z - α) + K / z - η * errorCont z

/-- **Landau: the abscissa of `ν` is `α`.** -/
theorem abscissa_osMeasure_eq {η C₀ C α K : ℝ} (hη : |η| = 1) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hK : 0 ≤ K) (hC : C₀ < C)
    (hg : ∀ u, 0 < u → η * logError u ≤ C₀ * Real.exp (α * u) + K) :
    IsAbscissa (osMeasure η C α K) α := by
  obtain ⟨hc, hac, hc2⟩ := isAbscissa_osMeasure hη hα1 hK hC hg
  set c : ℝ := sInf {σ : ℝ | laplaceMass (osMeasure η C α K) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hc0 : 0 < c := by linarith
    have hreg : ∀ᶠ z in 𝓝 (c : ℂ), z ∈ contRegion :=
      isOpen_contRegion.mem_nhds (ofReal_mem_contRegion hc0)
    have hev : ∀ᶠ z in 𝓝 (c : ℂ), z ∈ contRegion ∧ z ≠ (α : ℂ) :=
      hreg.and (eventually_ne_nhds (by exact_mod_cast hpos.ne'))
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hanal : ∀ z : ℂ, z ∈ contRegion → z ≠ (α : ℂ) →
        AnalyticAt ℂ (osContinuation η C α K) z := fun z hz hzα => by
      have hz0 : z ≠ 0 := by
        intro h; have := hz.1; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this
      exact ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzα)).add
        (analyticAt_const.div analyticAt_id hz0)).sub
          (analyticAt_const.mul (analyticOnNhd_errorCont z hz))
    refine false_of_analyticAt_abscissa hc hd (Φ := osContinuation η C α K) ?_ ?_
    · intro z hz
      obtain ⟨h1, h2⟩ := hball hz
      exact hanal z h1 h2
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (osMeasure η C α K))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (osMeasure η C α K) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (osMeasure η C α K)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => osContinuation η C α K (t : ℂ)) (Ioi c) := by
        intro t ht
        have ht' : c < t := ht
        have h1 : AnalyticAt ℂ (osContinuation η C α K) (t : ℂ) :=
          hanal _ (ofReal_mem_contRegion (by linarith))
            (by exact_mod_cast (show t ≠ α by linarith))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h3mem : (3 : ℝ) ∈ Ioi c := by show c < 3; linarith
      have hfg : (fun t : ℝ => complexLaplace (osMeasure η C α K) (t : ℂ)) =ᶠ[𝓝 (3 : ℝ)]
          (fun t : ℝ => osContinuation η C α K (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (2 : ℝ) < 3) (by norm_num : (3 : ℝ) < 4)) fun t ht => ?_
        have ht1 : 1 < (t : ℂ).re := by simp; linarith [ht.1]
        rw [complexLaplace_osMeasure_eq hC.le hα1 hg ht1, osContinuation,
          errorCont_eq_mellin ht1]
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h3mem hfg
      have hσ : complexLaplace (osMeasure η C α K) (σ : ℂ) = osContinuation η C α K (σ : ℂ) :=
        heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, RHTower.complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-! ## The halving law from a one-sided bound -/

/-- The continued error transform `G(z) = η (C/(z - α) + K/z - 𝓛ν(z))`. -/
def osTransform (η C α K : ℝ) (z : ℂ) : ℂ :=
  η * (C / (z - α) + K / z - complexLaplace (osMeasure η C α K) z)

theorem osTransform_eq_mellin {η C₀ C α K : ℝ} (hη : |η| = 1) (hC : C₀ ≤ C) (hα1 : α ≤ 1)
    (hg : ∀ u, 0 < u → η * logError u ≤ C₀ * Real.exp (α * u) + K) {z : ℂ} (hz : 1 < z.re) :
    osTransform η C α K z = mellin errorPiece z := by
  have hη2 : (η : ℂ) * η = 1 := by
    have := sq_abs η
    rw [hη] at this
    exact_mod_cast (by nlinarith : η * η = 1)
  rw [osTransform, complexLaplace_osMeasure_eq hC hα1 hg hz]
  linear_combination (mellin errorPiece z) * hη2

/-- **Pole-cleared identity from a one-sided bound.** -/
theorem os_pole_cleared_identity {η C₀ C α K : ℝ} (hη : |η| = 1) (hα : 0 ≤ α) (hα1 : α < 1)
    (hK : 0 ≤ K) (hC : C₀ < C)
    (hg : ∀ u, 0 < u → η * logError u ≤ C₀ * Real.exp (α * u) + K) {s : ℂ}
    (hs : α < s.re) :
    (s - 1) * zetaResidueUnit (2 * s) * (osTransform η C α K s + mellin tailPiece s) +
        density * zetaResidueUnit (2 * s) =
      (2 * s - 1) * Complex.Gamma s * zetaResidueUnit s := by
  have hc := abscissa_osMeasure_eq hη hα hα1.le hK hC hg
  set U : Set ℂ := {z : ℂ | α < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hz2 : ∀ z : ℂ, AnalyticAt ℂ (fun w : ℂ => zetaResidueUnit (2 * w)) z := fun z =>
    (analyticAt_zetaResidueUnit (2 * z)).comp (by fun_prop)
  have hG : AnalyticOnNhd ℂ (osTransform η C α K) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hw' : α < w.re := hw
    have hwα : w - α ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hw0 : w ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hw'; linarith
    have h1a : DifferentiableAt ℂ (fun z : ℂ => (C : ℂ) / (z - α)) w :=
      (differentiableAt_const _).div (differentiableAt_id.sub_const _) hwα
    have h1b : DifferentiableAt ℂ (fun z : ℂ => (K : ℂ) / z) w :=
      (differentiableAt_const _).div differentiableAt_id hw0
    have h1 := h1a.add h1b
    have h2 := (hasDerivAt_complexLaplace hc hw').differentiableAt
    exact ((h1.sub h2).const_mul (η : ℂ)).differentiableWithinAt
  have hP : AnalyticOnNhd ℂ (mellin tailPiece) U :=
    DifferentiableOn.analyticOnNhd
      (fun w _ => (differentiableAt_mellin_tailPiece w).differentiableWithinAt) hUo
  have hΓ : AnalyticOnNhd ℂ Complex.Gamma U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    refine (Complex.differentiableAt_Gamma w fun m hm => ?_).differentiableWithinAt
    have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have : α < w.re := hw
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hl : AnalyticOnNhd ℂ (fun z => (z - 1) * zetaResidueUnit (2 * z) *
      (osTransform η C α K z + mellin tailPiece z) + density * zetaResidueUnit (2 * z)) U :=
    fun z hz => (((analyticAt_id.sub analyticAt_const).mul (hz2 z)).mul
      ((hG z hz).add (hP z hz))).add (analyticAt_const.mul (hz2 z))
  have hr : AnalyticOnNhd ℂ (fun z => (2 * z - 1) * Complex.Gamma z * zetaResidueUnit z) U :=
    fun z hz => (((analyticAt_const.mul analyticAt_id).sub analyticAt_const).mul
      (hΓ z hz)).mul (analyticAt_zetaResidueUnit z)
  have hev : (fun z => (z - 1) * zetaResidueUnit (2 * z) *
      (osTransform η C α K z + mellin tailPiece z) + density * zetaResidueUnit (2 * z)) =ᶠ[𝓝 2]
      (fun z => (2 * z - 1) * Complex.Gamma z * zetaResidueUnit z) := by
    have hgt : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with z hz1
    rw [osTransform_eq_mellin hη hC.le hα1.le hg hz1]
    exact pole_cleared_identity (α := 1) (C := 1) zero_le_one le_rfl errorBound_one
      (by linarith)
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr (convex_halfSpace_re_gt α).isPreconnected
    (show (2 : ℂ) ∈ U by simp [hU]; linarith) hev hs

/-- **Zero-free band from a one-sided bound.** If `η e(t) ≤ C₀ t^{-α}` on `(0, 1]` with `η = ±1`
and `0 ≤ α < 1`, then `ζ(s) ≠ 0` whenever `2α < Re s` and `2α < 1 - Re s/2`. -/
theorem riemannZeta_ne_zero_of_sqfError_oneSided {η C₀ α : ℝ} (hη : |η| = 1) (hα : 0 ≤ α)
    (hα1 : α < 1) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, η * sqfError t ≤ C₀ * t ^ (-α)) {s : ℂ}
    (h1 : 2 * α < s.re) (h2 : 2 * α < 1 - s.re / 2) :
    riemannZeta s ≠ 0 := by
  have hg : ∀ u, 0 < u → η * logError u ≤ C₀ * Real.exp (α * u) + 0 := by
    intro u hu
    have hmem : Real.exp (-u) ∈ Ioc (0 : ℝ) 1 :=
      ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith)⟩
    have h := hB _ hmem
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at h
    rw [logError, add_zero]
    convert h using 3
    ring
  refine SquarefreeDiscrepancy.riemannZeta_ne_zero_of_halving hα (fun ρ hz hre1 hre2 => ?_) h1 h2
  -- the halving law
  set C : ℝ := |C₀| + 1 with hCdef
  have hC : C₀ < C := by rw [hCdef]; linarith [le_abs_self C₀]
  have hs : α < (ρ / 2).re := by
    rw [Complex.div_re]; simp; nlinarith [Complex.normSq_nonneg ρ]
  have hid := os_pole_cleared_identity hη hα hα1 le_rfl hC hg hs
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hre2; linarith
  have hZρ : zetaResidueUnit ρ = 0 := by
    rw [zetaResidueUnit, Function.update_of_ne hρ1, hz, mul_zero]
  rw [show 2 * (ρ / 2) = ρ by ring, hZρ, mul_zero, zero_mul, mul_zero, add_zero] at hid
  have hΓ : Complex.Gamma (ρ / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hne : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hZ : zetaResidueUnit (ρ / 2) = 0 := by
    rcases mul_eq_zero.mp hid.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hne
      · exact absurd h' hΓ
    · exact h
  have hhalf1 : ρ / 2 ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.div_re] at this
    simp at this
    nlinarith [Complex.normSq_nonneg ρ]
  rw [zetaResidueUnit, Function.update_of_ne hhalf1] at hZ
  rcases mul_eq_zero.mp hZ with h | h
  · exact absurd (sub_eq_zero.mp h) hhalf1
  · exact h

/-- **One-sided receiver.** If `η e(t) ≤ C_ε t^{-1/4-ε}` on `(0, 1]` for every `ε > 0`, RH holds. -/
theorem riemannHypothesis_of_sqfError_oneSided {η : ℝ} (hη : |η| = 1)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
      η * sqfError t ≤ C * t ^ (-(1 / 4 + ε))) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro s hs hz
  have hs1 : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  set ε : ℝ := min ((s.re - 1 / 2) / 4) ((1 - s.re) / 8) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := hB ε hε0
  have hε1 : ε ≤ (s.re - 1 / 2) / 4 := min_le_left _ _
  have hε2 : ε ≤ (1 - s.re) / 8 := min_le_right _ _
  exact riemannZeta_ne_zero_of_sqfError_oneSided hη (by linarith) (by linarith) hC (by linarith)
    (by linarith) hz

/-- The two-sided law under RH, in the real form. -/
theorem abs_sqfError_le_of_riemannHypothesis (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, |sqfError t| ≤ C * t ^ (-(1 / 4 + ε)) := by
  obtain ⟨C, hC⟩ := expBound_quarter_of_riemannHypothesis hRH hε
  refine ⟨C, fun t ht => ?_⟩
  have h := hC t ht
  rwa [← ofReal_sqfError, Complex.norm_real, Real.norm_eq_abs] at h

/-- **RH ⟺ the upper squarefree law.** -/
theorem riemannHypothesis_iff_sqfError_upper :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
      sqfError t ≤ C * t ^ (-(1 / 4 + ε)) := by
  refine ⟨fun hRH ε hε => ?_, fun h => riemannHypothesis_of_sqfError_oneSided (η := 1)
    (by norm_num) fun ε hε => by simpa using h ε hε⟩
  obtain ⟨C, hC⟩ := abs_sqfError_le_of_riemannHypothesis hRH hε
  exact ⟨C, fun t ht => (le_abs_self _).trans (hC t ht)⟩

/-- **RH ⟺ the lower squarefree law.** -/
theorem riemannHypothesis_iff_sqfError_lower :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
      -sqfError t ≤ C * t ^ (-(1 / 4 + ε)) := by
  refine ⟨fun hRH ε hε => ?_, fun h => riemannHypothesis_of_sqfError_oneSided (η := -1)
    (by norm_num) fun ε hε => by simpa using h ε hε⟩
  obtain ⟨C, hC⟩ := abs_sqfError_le_of_riemannHypothesis hRH hε
  exact ⟨C, fun t ht => (neg_le_abs _).trans (hC t ht)⟩

end

end RHTower.SquarefreeExponential
