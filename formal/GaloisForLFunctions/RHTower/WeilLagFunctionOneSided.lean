import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.LandauSingularAtAbscissa
import GaloisForLFunctions.RHTower.ComplexLaplaceHolomorphy
import GaloisForLFunctions.RHTower.LandauAbscissaWitnesses
import GaloisForLFunctions.RHTower.XiRealAnchorPositive

/-!
# The one-sided lag criterion: `RH ⟺ Φ is bounded above ⟺ Φ is bounded below`

The lag function `Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))` is real.  If `Φ ≤ M` (or `Φ ≥ −M`) on `ℝ`, then
`M − Φ` (or `M + Φ`) is a nonnegative density on `(0,∞)`, and Landau's theorem applies to the
Laplace transform of the measure `(M ∓ Φ)du + du`: its abscissa of convergence is a genuine
singularity, while the transform agrees to the right of `½` with `(M+1)/s ∓ G(s)`, `G` the
Mittag-Leffler series of the zeros, which is analytic at every real point `> 0` because `ξ` has no
real zeros.  Hence the abscissa is `0`, the transform is holomorphic on `Re s > 0`, and the
analytic-extension theorem of the two-sided criterion forces RH.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## `Φ` is real -/

theorem trivialZeroSeries_eq_ofReal (X : ℝ) :
    trivialZeroSeries X =
      ((∑' k : ℕ, (X ^ (2 * (k + 1)))⁻¹ / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) : ℝ) : ℂ) := by
  unfold trivialZeroSeries trivialZeroSeriesTerm
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun k => by push_cast; ring

theorem weilLagFunction_im_eq_zero (L : ℝ) : (weilLagFunction L).im = 0 := by
  have hpos : ∀ L : ℝ, 0 < L → (weilLagFunction L).im = 0 := by
    intro L hL
    rw [weilLagFunction_eq_prime_side hL, trivialZeroSeries_eq_ofReal]
    have : (Real.exp (-L / 2) : ℂ) *
        (((Real.exp L - Chebyshev.psi (Real.exp L) : ℝ) : ℂ) +
          Real.exp L * (((∑ n ∈ Finset.Icc 1 ⌊Real.exp L⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) : ℝ) : ℂ)
            - L + Real.eulerMascheroniConstant) - Real.log (2 * Real.pi) +
          ((∑' k : ℕ, (Real.exp L ^ (2 * (k + 1)))⁻¹ / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) : ℝ) : ℂ))
        = ((Real.exp (-L / 2) *
        ((Real.exp L - Chebyshev.psi (Real.exp L)) +
          Real.exp L * ((∑ n ∈ Finset.Icc 1 ⌊Real.exp L⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ))
            - L + Real.eulerMascheroniConstant) - Real.log (2 * Real.pi) +
          (∑' k : ℕ, (Real.exp L ^ (2 * (k + 1)))⁻¹ / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)))) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [this, Complex.ofReal_im]
  rcases lt_trichotomy L 0 with hL | rfl | hL
  · have h := weilLagFunction_neg (-L)
    rw [neg_neg] at h
    rw [h]
    exact hpos (-L) (by linarith)
  · rw [weilLagFunction_zero]; exact Complex.ofReal_im _
  · exact hpos L hL

/-- The real lag function. -/
def weilLagFunctionReal (L : ℝ) : ℝ := (weilLagFunction L).re

theorem weilLagFunction_eq_ofReal (L : ℝ) : weilLagFunction L = (weilLagFunctionReal L : ℂ) := by
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im, weilLagFunction_im_eq_zero]

theorem measurable_weilLagFunctionReal : Measurable weilLagFunctionReal :=
  Complex.measurable_re.comp measurable_weilLagFunction

/-- The total weight `W = Σ_ρ 1/|ρ(1−ρ)|`. -/
def lagWeightTotal : ℝ := ∑' q : XiZeroCopy, ‖lagWeight q‖

theorem abs_weilLagFunctionReal_le (L : ℝ) :
    |weilLagFunctionReal L| ≤ Real.exp (|L| / 2) * lagWeightTotal := by
  have h1 : |weilLagFunctionReal L| = ‖weilLagFunction L‖ := by
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rw [h1]
  unfold weilLagFunction lagWeightTotal
  have hs : Summable (fun q : XiZeroCopy =>
      ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_weilLagTerm_le L)
      (summable_norm_lagWeight.mul_left _)
  calc ‖∑' q : XiZeroCopy, Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
      ≤ ∑' q : XiZeroCopy, ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' q : XiZeroCopy, Real.exp (|L| / 2) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
        hs.tsum_le_tsum (norm_weilLagTerm_le L) (summable_norm_lagWeight.mul_left _)
    _ = Real.exp (|L| / 2) * ∑' q : XiZeroCopy, ‖lagWeight q‖ := by rw [tsum_mul_left]; rfl

theorem lagWeightTotal_nonneg : 0 ≤ lagWeightTotal :=
  tsum_nonneg fun _ => norm_nonneg _

/-! ## Elementary Laplace integrals -/

/-- `∫_0^∞ e^{−zu} du = 1/z` for `Re z > 0`. -/
theorem integral_cexp_neg_mul_Ioi {z : ℂ} (hz : 0 < z.re) :
    ∫ u in Ioi (0:ℝ), Complex.exp (-z * (u : ℂ)) = 1 / z := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hderiv : ∀ u ∈ Ioi (0:ℝ), HasDerivAt (fun u : ℝ => -(Complex.exp (-z * (u : ℂ))) / z)
      (Complex.exp (-z * (u : ℂ))) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => -z * (u : ℂ)) (-z * 1) u :=
      (hasDerivAt_id u).ofReal_comp.const_mul (-z)
    have h2 := (h1.cexp).neg.div_const z
    have e : -(Complex.exp (-z * (u : ℂ)) * (-z * 1)) / z = Complex.exp (-z * (u : ℂ)) := by
      field_simp
    rw [e] at h2
    exact h2
  have hcont : Continuous (fun u : ℝ => Complex.exp (-z * (u : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hint : IntegrableOn (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (Ioi 0) := by
    have hre : IntegrableOn (fun u : ℝ => Real.exp (-z.re * u)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 hz
    exact hre.mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul z u))
  have hlim : Tendsto (fun u : ℝ => -(Complex.exp (-z * (u : ℂ))) / z) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun u : ℝ => Real.exp (-(z.re * u))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hz)
    have h2 := h1.div_const ‖z‖
    simp only [zero_div] at h2
    refine h2.congr fun u => ?_
    rw [norm_div, norm_neg, norm_cexp_neg_mul, neg_mul]
  have := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (f := fun u : ℝ => -(Complex.exp (-z * (u : ℂ))) / z)
    (f' := fun u : ℝ => Complex.exp (-z * (u : ℂ))) (m := 0)
    (hcont.neg.div_const z).continuousWithinAt hderiv hint hlim
  rw [this]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_sub, neg_div, neg_neg, one_div]

theorem integral_exp_neg_mul_Ioi_real {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi (0:ℝ), Real.exp (-a * u) = 1 / a := by
  have hderiv : ∀ u ∈ Ioi (0:ℝ), HasDerivAt (fun u : ℝ => -(Real.exp (-a * u)) / a)
      (Real.exp (-a * u)) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => -a * u) (-a * 1) u := (hasDerivAt_id u).const_mul (-a)
    have h2 := (h1.exp).neg.div_const a
    have e : -(Real.exp (-a * u) * (-a * 1)) / a = Real.exp (-a * u) := by field_simp
    rw [e] at h2
    exact h2
  have hcont : Continuous (fun u : ℝ => Real.exp (-a * u)) := by fun_prop
  have hlim : Tendsto (fun u : ℝ => -(Real.exp (-a * u)) / a) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => Real.exp (-(a * u))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
    have h2 := (h1.neg).div_const a
    simp only [neg_zero, zero_div] at h2
    refine h2.congr fun u => ?_
    rw [neg_mul]
  have := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (f := fun u : ℝ => -(Real.exp (-a * u)) / a)
    (f' := fun u : ℝ => Real.exp (-a * u)) (m := 0)
    (hcont.neg.div_const a).continuousWithinAt hderiv (exp_neg_integrableOn_Ioi 0 ha) hlim
  rw [this]
  simp only [mul_zero, Real.exp_zero, zero_sub, neg_div, neg_neg, one_div]

/-- The Laplace transform of `Φ` on `Re s > ½` is the Mittag-Leffler series. -/
theorem integral_weilLagFunction_mul_cexp {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫ u in Ioi (0:ℝ), weilLagFunction u * Complex.exp (-s * (u : ℂ)) = lagPoleSeries s := by
  unfold weilLagFunction lagPoleSeries
  have hterm : ∀ (u : ℝ) (q : XiZeroCopy),
      Complex.exp (u * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) * Complex.exp (-s * (u : ℂ))
        = lagWeight q * Complex.exp (-(s - lagPole q) * (u : ℂ)) := by
    intro u q
    unfold lagWeight lagPole
    rw [div_mul_eq_mul_div, ← Complex.exp_add, div_eq_mul_one_div, mul_comm]
    congr 2
    ring
  have hre : ∀ q : XiZeroCopy, 0 < (s - lagPole q).re := by
    intro q; rw [Complex.sub_re]; linarith [lagPole_re_lt_half q]
  have hint : ∀ q : XiZeroCopy, Integrable (fun u : ℝ => lagWeight q * Complex.exp (-(s - lagPole q) * (u : ℂ)))
      (volume.restrict (Ioi (0:ℝ))) := by
    intro q
    have hc : Continuous (fun u : ℝ => Complex.exp (-(s - lagPole q) * (u : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact ((exp_neg_integrableOn_Ioi 0 (hre q)).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))).const_mul _
  have hnorm : Summable (fun q : XiZeroCopy =>
      ∫ u in Ioi (0:ℝ), ‖lagWeight q * Complex.exp (-(s - lagPole q) * (u : ℂ))‖) := by
    have hK : ∀ q : XiZeroCopy, ∫ u in Ioi (0:ℝ), ‖lagWeight q * Complex.exp (-(s - lagPole q) * (u : ℂ))‖
        ≤ ‖lagWeight q‖ * (1 / (s.re - 1 / 2)) := by
      intro q
      rw [← integral_exp_neg_mul_Ioi_real (by linarith : (0:ℝ) < s.re - 1 / 2), ← integral_const_mul]
      refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi fun u hu => ?_
      · exact (hint q).norm
      · exact (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
      · rw [norm_mul, norm_cexp_neg_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        have := lagPole_re_lt_half q
        have hu' : (0:ℝ) < u := hu
        rw [Complex.sub_re]
        nlinarith
    exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hK
      (summable_norm_lagWeight.mul_right _)
  have hfun : (fun u : ℝ => (∑' q : XiZeroCopy,
      Complex.exp (u * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) * Complex.exp (-s * (u : ℂ)))
      = fun u : ℝ => ∑' q : XiZeroCopy, lagWeight q * Complex.exp (-(s - lagPole q) * (u : ℂ)) := by
    funext u
    rw [← tsum_mul_right]
    exact tsum_congr fun q => hterm u q
  rw [hfun, ← integral_tsum_of_summable_integral_norm hint hnorm]
  refine tsum_congr fun q => ?_
  rw [integral_const_mul, integral_cexp_neg_mul_Ioi (hre q), mul_one_div]

/-! ## The one-sided measure -/

/-- The clipped density `max(M − εΦ, 0)`. -/
def oneSidedDensity (ε M : ℝ) (u : ℝ) : NNReal := Real.toNNReal (M - ε * weilLagFunctionReal u)

theorem measurable_oneSidedDensity (ε M : ℝ) : Measurable (oneSidedDensity ε M) :=
  (measurable_const.sub (measurable_weilLagFunctionReal.const_mul ε)).real_toNNReal

/-- `(M − εΦ) du` on `(0,∞)` plus Lebesgue measure. -/
def oneSidedMeasure (ε M : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (oneSidedDensity ε M u : ENNReal)) + volume

/-- The density is at most `|M| + W e^{u/2}` for `u > 0`, when `|ε| ≤ 1`. -/
theorem oneSidedDensity_le {ε M : ℝ} (hε : |ε| ≤ 1) {u : ℝ} (hu : 0 < u) :
    ((oneSidedDensity ε M u : ℝ)) ≤ |M| + Real.exp (u / 2) * lagWeightTotal := by
  unfold oneSidedDensity
  rw [Real.coe_toNNReal']
  have h1 := abs_weilLagFunctionReal_le u
  rw [abs_of_pos hu] at h1
  have h2 : |ε * weilLagFunctionReal u| ≤ |weilLagFunctionReal u| := by
    rw [abs_mul]
    calc |ε| * |weilLagFunctionReal u| ≤ 1 * |weilLagFunctionReal u| := by gcongr
      _ = _ := one_mul _
  have h3 := le_abs_self M
  have h4 := neg_abs_le (ε * weilLagFunctionReal u)
  have h5 := abs_nonneg M
  have hW := lagWeightTotal_nonneg
  rcases le_or_gt (M - ε * weilLagFunctionReal u) 0 with h | h
  · rw [max_eq_right h]; positivity
  · rw [max_eq_left h.le]; linarith

/-- The exponential majorant is integrable for `σ > ½`. -/
theorem integrableOn_majorant {σ M : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun u : ℝ => (|M| + Real.exp (u / 2) * lagWeightTotal) * Real.exp (-σ * u)) (Ioi 0) := by
  have h1 := (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < σ)).const_mul |M|
  have h2 := (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < σ - 1 / 2)).const_mul lagWeightTotal
  refine IntegrableOn.congr_fun (h1.add h2) (fun u _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [show Real.exp (-(σ - 1 / 2) * u) = Real.exp (u / 2) * Real.exp (-σ * u) by
    rw [← Real.exp_add]; ring_nf]
  ring

theorem laplaceMass_oneSided_density_ne_top {ε M σ : ℝ} (hε : |ε| ≤ 1) (hσ : 1 / 2 < σ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (oneSidedDensity ε M u : ENNReal))) σ
      ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_oneSidedDensity ε M).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top (integrableOn_majorant (M := M) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (oneSidedDensity_le hε hu) (Real.exp_pos _).le

theorem laplaceMass_oneSided_eq (ε M σ : ℝ) :
    laplaceMass (oneSidedMeasure ε M) σ =
      laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (oneSidedDensity ε M u : ENNReal))) σ
        + laplaceMass volume σ := by
  unfold laplaceMass oneSidedMeasure
  rw [Measure.restrict_add, lintegral_add_measure]

theorem laplaceMass_volume_zero_eq_top : laplaceMass volume 0 = ⊤ := by
  unfold laplaceMass
  simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, lintegral_one,
    Measure.restrict_apply_univ, Real.volume_Ioi]

/-- The set of real points where the transform converges lies in `(0,∞)`, contains `1`, and is an
up-set; its infimum is the abscissa. -/
theorem isAbscissa_oneSided {ε M : ℝ} (hε : |ε| ≤ 1) :
    IsAbscissa (oneSidedMeasure ε M) (sInf {σ : ℝ | laplaceMass (oneSidedMeasure ε M) σ ≠ ⊤}) ∧
      0 ≤ sInf {σ : ℝ | laplaceMass (oneSidedMeasure ε M) σ ≠ ⊤} := by
  set S := {σ : ℝ | laplaceMass (oneSidedMeasure ε M) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, 0 < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_oneSided_eq]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top h, add_top]
    · rw [h, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨0, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1:ℝ) ∈ S := by
    show laplaceMass (oneSidedMeasure ε M) 1 ≠ ⊤
    rw [laplaceMass_oneSided_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_oneSided_density_ne_top hε (by norm_num),
      laplaceMass_volume_ne_top one_pos⟩
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, Real.sInf_nonneg fun σ hσ => (hpos σ hσ).le⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The complex transform on `Re s > ½` -/

theorem xi_ofReal_add_half_ne_zero {t : ℝ} (ht : 0 < t) : xi ((t : ℂ) + 1 / 2) ≠ 0 := by
  rcases lt_or_ge (t + 1 / 2) 1 with h | h
  · have := xi_pos_on_real_anchor (σ := t + 1 / 2) (by linarith) h
    intro h0
    rw [show ((t + 1 / 2 : ℝ) : ℂ) = (t : ℂ) + 1 / 2 by push_cast; ring, h0] at this
    simp at this
  · exact xi_ne_zero_of_one_le_re (by simp; linarith)

theorem analyticAt_lagPoleSeries {z : ℂ} (hz : xi (z + 1 / 2) ≠ 0) : AnalyticAt ℂ lagPoleSeries z := by
  have hopen : IsOpen {w : ℂ | xi (w + 1 / 2) ≠ 0} :=
    isOpen_ne_fun (xi_differentiable.continuous.comp (continuous_id.add continuous_const))
      continuous_const
  refine DifferentiableOn.analyticAt (s := {w : ℂ | xi (w + 1 / 2) ≠ 0}) ?_ (hopen.mem_nhds hz)
  exact fun w hw => (differentiableAt_lagPoleSeries hw).differentiableWithinAt

/-- The candidate analytic continuation `H(z) = (M+1)/z − ε G(z)`. -/
def oneSidedContinuation (ε M : ℝ) (z : ℂ) : ℂ := (M + 1) / z - ε * lagPoleSeries z

theorem analyticAt_oneSidedContinuation (ε M : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz : xi (z + 1 / 2) ≠ 0) :
    AnalyticAt ℂ (oneSidedContinuation ε M) z := by
  unfold oneSidedContinuation
  exact (analyticAt_const.div analyticAt_id hz0).sub (analyticAt_const.mul (analyticAt_lagPoleSeries hz))

theorem integrable_cexp_oneSided_density {ε M : ℝ} (hε : |ε| ≤ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (fun u : ℝ => Complex.exp (-s * (u : ℂ)))
      (((volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (oneSidedDensity ε M u : ENNReal))).restrict
        (Ioi 0)) := by
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    integrable_withDensity_iff_integrable_smul (measurable_oneSidedDensity ε M)]
  refine (integrableOn_majorant (M := M) (by exact hs)).mono' ?_ ?_
  · exact ((measurable_oneSidedDensity ε M).coe_nnreal_real.aestronglyMeasurable.smul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
      norm_cexp_neg_mul]
    exact mul_le_mul_of_nonneg_right (oneSidedDensity_le hε hu) (Real.exp_pos _).le

theorem integrable_weilLag_mul_cexp {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun u : ℝ => (weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ))) (Ioi 0) := by
  have hmaj : IntegrableOn (fun u : ℝ => (0 + Real.exp (u / 2) * lagWeightTotal) * Real.exp (-s.re * u))
      (Ioi 0) := by
    have := integrableOn_majorant (M := (0:ℝ)) hs
    simpa using this
  refine hmaj.mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      measurable_weilLagFunctionReal.aestronglyMeasurable).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_neg_mul, zero_add]
    have := abs_weilLagFunctionReal_le u
    rw [abs_of_pos (show (0:ℝ) < u from hu)] at this
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

/-- On `Re s > ½` the complex Laplace transform of the one-sided measure is `H(s)`. -/
theorem complexLaplace_oneSided_eq {ε M : ℝ} (hε : |ε| ≤ 1)
    (hM : ∀ L, ε * weilLagFunctionReal L ≤ M) {s : ℂ} (hs : 1 / 2 < s.re) :
    complexLaplace (oneSidedMeasure ε M) s = oneSidedContinuation ε M s := by
  have hs0 : 0 < s.re := by linarith
  have hcexp : Continuous (fun u : ℝ => Complex.exp (-s * (u : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hexpInt : IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ))) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hs0).mono' hcexp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  unfold complexLaplace oneSidedMeasure oneSidedContinuation
  rw [Measure.restrict_add, integral_add_measure (integrable_cexp_oneSided_density hε hs) hexpInt,
    integral_cexp_neg_mul_Ioi hs0]
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    integral_withDensity_eq_integral_smul (measurable_oneSidedDensity ε M)]
  have hpt : ∀ u ∈ Ioi (0:ℝ), oneSidedDensity ε M u • Complex.exp (-s * (u : ℂ)) =
      (M : ℂ) * Complex.exp (-s * (u : ℂ)) -
        (ε : ℂ) * ((weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ))) := by
    intro u _
    rw [NNReal.smul_def, Complex.real_smul]
    unfold oneSidedDensity
    rw [Real.coe_toNNReal _ (by linarith [hM u])]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_sub (hexpInt.const_mul _) ((integrable_weilLag_mul_cexp hs).const_mul _),
    integral_const_mul, integral_const_mul, integral_cexp_neg_mul_Ioi hs0]
  have hΦ : ∫ u in Ioi (0:ℝ), (weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ)) =
      lagPoleSeries s := by
    rw [← integral_weilLagFunction_mul_cexp hs]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
      beta_reduce; rw [weilLagFunction_eq_ofReal])
  rw [hΦ]
  have hs' : s ≠ 0 := fun h => by rw [h] at hs0; simp at hs0
  field_simp
  ring

theorem complexLaplace_ofReal (ν : Measure ℝ) (σ : ℝ) :
    complexLaplace ν (σ : ℂ) = (laplaceReal ν σ : ℂ) := by
  unfold complexLaplace laplaceReal
  have h : ∫ u in Ioi (0:ℝ), ((Real.exp (-σ * u) : ℝ) : ℂ) ∂ν =
      ((∫ u in Ioi (0:ℝ), Real.exp (-σ * u) ∂ν : ℝ) : ℂ) := integral_ofReal
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  push_cast
  ring_nf

/-! ## Landau: the abscissa is zero -/

theorem abscissa_oneSided_eq_zero {ε M : ℝ} (hε : |ε| ≤ 1)
    (hM : ∀ L, ε * weilLagFunctionReal L ≤ M) : IsAbscissa (oneSidedMeasure ε M) 0 := by
  obtain ⟨hc, hc0⟩ := isAbscissa_oneSided (M := M) hε
  set c : ℝ := sInf {σ : ℝ | laplaceMass (oneSidedMeasure ε M) σ ≠ ⊤} with hcdef
  rcases hc0.lt_or_eq with hpos | hzero
  · exfalso
    have hc34 : c ≤ 3 / 4 := by
      refine csInf_le ⟨0, fun σ hσ => ?_⟩ ?_
      · by_contra hlt
        apply hσ
        rw [laplaceMass_oneSided_eq, laplaceMass_volume_eq_top (not_le.mp hlt), add_top]
      · show laplaceMass (oneSidedMeasure ε M) (3 / 4) ≠ ⊤
        rw [laplaceMass_oneSided_eq]
        exact ENNReal.add_ne_top.mpr ⟨laplaceMass_oneSided_density_ne_top hε (by norm_num),
          laplaceMass_volume_ne_top (by norm_num)⟩
    have hne : xi ((c : ℂ) + 1 / 2) ≠ 0 := xi_ofReal_add_half_ne_zero hpos
    have hopen : IsOpen {z : ℂ | xi z ≠ 0} := isOpen_ne_fun xi_differentiable.continuous continuous_const
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hopen _ hne
    set δ : ℝ := min c d / 2 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; exact half_pos (lt_min hpos hd)
    have hδc : δ ≤ c / 2 := by rw [hδdef]; linarith [min_le_left c d]
    have hδd : δ ≤ d / 2 := by rw [hδdef]; linarith [min_le_right c d]
    refine false_of_analyticAt_abscissa hc hδ (Φ := oneSidedContinuation ε M) ?_ ?_
    · intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : c / 2 < z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        have := abs_le.mp this
        linarith
      have hz0 : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre; linarith
      have hzxi : xi (z + 1 / 2) ≠ 0 := by
        apply hball
        rw [Metric.mem_ball, Complex.dist_eq]
        calc ‖z + 1 / 2 - ((c : ℂ) + 1 / 2)‖ = ‖z - c‖ := by congr 1; ring
          _ < δ := hz
          _ ≤ d / 2 := hδd
          _ < d := by linarith
      exact analyticAt_oneSidedContinuation ε M hz0 hzxi
    · intro σ hσc _
      -- both sides are real-analytic on `(c, ∞)` and agree on `(½, ∞)`
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (oneSidedMeasure ε M)) {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (oneSidedMeasure ε M) (t : ℂ)) (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (oneSidedMeasure ε M)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => oneSidedContinuation ε M (t : ℂ)) (Ioi c) := by
        intro t ht
        have ht0 : 0 < t := lt_trans hpos ht
        have h1 : AnalyticAt ℂ (oneSidedContinuation ε M) (t : ℂ) :=
          analyticAt_oneSidedContinuation ε M (by exact_mod_cast ht0.ne')
            (xi_ofReal_add_half_ne_zero ht0)
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h1mem : (1 : ℝ) ∈ Ioi c := by show c < 1; linarith
      have hfg : (fun t : ℝ => complexLaplace (oneSidedMeasure ε M) (t : ℂ)) =ᶠ[𝓝 (1:ℝ)]
          (fun t : ℝ => oneSidedContinuation ε M (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
        exact complexLaplace_oneSided_eq hε hM (by simpa using ht.1)
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h1mem hfg
      have hσ : complexLaplace (oneSidedMeasure ε M) (σ : ℂ) = oneSidedContinuation ε M (σ : ℂ) :=
        heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-! ## The one-sided criterion -/

/-- **A one-sided bound on the lag function implies RH.** -/
theorem riemannHypothesis_of_weilLagFunctionReal_oneSided {ε M : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hM : ∀ L, ε * weilLagFunctionReal L ≤ M) : RiemannHypothesis := by
  have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  have hεsq : (ε : ℂ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hc := abscissa_oneSided_eq_zero hε1 hM
  refine riemannHypothesis_of_lagPoleSeries_extension
    (F := fun z => (ε : ℂ) * (((M : ℂ) + 1) / z - complexLaplace (oneSidedMeasure ε M) z)) ?_ ?_
  · intro z hz0 _
    have hz : z ≠ 0 := fun h => by rw [h] at hz0; simp at hz0
    exact (differentiableAt_const _).mul
      (((differentiableAt_const _).div differentiableAt_id hz).sub
        (hasDerivAt_complexLaplace hc (by simpa using hz0)).differentiableAt)
  · intro s hs
    beta_reduce
    rw [complexLaplace_oneSided_eq hε1 hM hs]
    unfold oneSidedContinuation
    linear_combination (lagPoleSeries s) * hεsq

theorem riemannHypothesis_of_weilLagFunctionReal_le {M : ℝ}
    (hM : ∀ L, weilLagFunctionReal L ≤ M) : RiemannHypothesis :=
  riemannHypothesis_of_weilLagFunctionReal_oneSided (Or.inl rfl) (fun L => by simpa using hM L)

theorem riemannHypothesis_of_le_weilLagFunctionReal {M : ℝ}
    (hM : ∀ L, -M ≤ weilLagFunctionReal L) : RiemannHypothesis :=
  riemannHypothesis_of_weilLagFunctionReal_oneSided (Or.inr rfl) (fun L => by linarith [hM L])

/-- **The one-sided lag criterion.**  RH holds iff the real lag function is bounded above, iff it is
bounded below; under RH the bounds are `±(2 + γ − log 4π)`. -/
theorem riemannHypothesis_iff_weilLagFunctionReal_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ L : ℝ, weilLagFunctionReal L ≤ M := by
  constructor
  · intro h
    refine ⟨poleSharpConstant, fun L => ?_⟩
    have := norm_weilLagFunction_le_of_riemannHypothesis h L
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  · rintro ⟨M, hM⟩
    exact riemannHypothesis_of_weilLagFunctionReal_le hM

theorem riemannHypothesis_iff_weilLagFunctionReal_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ L : ℝ, -M ≤ weilLagFunctionReal L := by
  constructor
  · intro h
    refine ⟨poleSharpConstant, fun L => ?_⟩
    have := norm_weilLagFunction_le_of_riemannHypothesis h L
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
    linarith [neg_abs_le (weilLagFunctionReal L)]
  · rintro ⟨M, hM⟩
    exact riemannHypothesis_of_le_weilLagFunctionReal hM

end

end RHTower
