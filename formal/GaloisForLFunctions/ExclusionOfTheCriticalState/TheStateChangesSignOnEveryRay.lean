import GaloisForLFunctions.ExclusionOfTheCriticalState.TheDecayOfTheStateReadsTheZeros
import GaloisForLFunctions.RHTower.LaplaceTransformMomentDerivative
import GaloisForLFunctions.HTGeometry.HolomorphicRealTaylor
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleLogDeriv
import GaloisForLFunctions.RHTower.ZetaHalfPlaneDiscJensen
import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion
import GaloisForLFunctions.RHTower.LevinsonEntireDetector

/-!
# The critical state changes sign on every ray

Suppose the critical state `F` had one sign on a ray `u < -T`. By Landau's theorem the transform of
the tail `∫_{u<-T} F(u) e^{wu} du` is singular at the real point of its abscissa `c`. The state
equation continues `L F(w)` holomorphically across every real point `w > -8`: the probe exponent
`p = w + 8` stays in `Re p > 0`, `ζ(½ + p)` has no real zero there, and the pole of `ζ'/ζ` at `1`
cancels against the pole charge `L F(½)/(p - ½)` (the remainder is written with `(s-1)ζ(s)` and a
divided difference of `L F`). Hence `c ≤ -8`: the transform is holomorphic on `Re w > -8`, and the
decay law puts every zero of `ζ` on `Re s ≤ ½`. Off RH this is impossible, so the state has one sign
on no ray.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
open scoped ComplexConjugate ENNReal

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower
open GaloisForLFunctions.RHTower (laplaceMass laplaceReal IsAbscissa laplaceMass_antitone
  not_summable_iteratedDeriv_beyond_abscissa)

/-! ### Holomorphy from absolute convergence -/

/-- A half-line profile with `∫ |F| e^{cu} < ∞` for every `c > κ` has a transform holomorphic on
`Re w > κ`. -/
theorem differentiableOn_laplace_of_abs {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {κ : ℝ}
    (habs : ∀ c, κ < c → Integrable fun u => |F u| * Real.exp (c * u)) :
    DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {p : ℂ | κ < p.re} := by
  have hU : IsOpen {p : ℂ | κ < p.re} := isOpen_lt continuous_const Complex.continuous_re
  refine differentiableOn_integral_of_locally_bounded (ν := volume)
    (F := fun (u : ℝ) (z : ℂ) => cexp (z * u) * cx F u) hU
    (fun u => (by fun_prop : Differentiable ℂ fun z : ℂ => cexp (z * u) * cx F u).differentiableOn)
    (fun z _ => ((by fun_prop : Continuous fun u : ℝ => cexp (z * u)).measurable.mul
      (Complex.measurable_ofReal.comp hFm)).aestronglyMeasurable) ?_
  intro z₀ hz₀
  have hz₀' : κ < z₀.re := hz₀
  set r := (z₀.re - κ) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  refine ⟨r, hrpos, fun z hz => ?_, fun u => |F u| * Real.exp ((z₀.re - r) * u),
    habs _ (by rw [hr]; linarith), fun u z hz => ?_⟩
  · have hd := Complex.abs_re_le_norm (z - z₀)
    rw [mem_closedBall, dist_eq_norm] at hz
    have : |z.re - z₀.re| ≤ r := by simpa using hd.trans hz
    show κ < z.re
    rw [hr] at this
    linarith [(abs_le.mp this).1]
  · have hd := Complex.abs_re_le_norm (z - z₀)
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre : z₀.re - r ≤ z.re := by
      have : |z.re - z₀.re| ≤ r := by simpa using hd.trans hz
      linarith [(abs_le.mp this).1]
    rw [norm_mul, norm_cexp_mul_ofReal]
    rcases lt_or_ge u 0 with hu | hu
    · have he : Real.exp (z.re * u) ≤ Real.exp ((z₀.re - r) * u) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hn : ‖cx F u‖ = |F u| := by simp [cx]
      rw [hn, mul_comm]
      exact mul_le_mul_of_nonneg_left he (abs_nonneg _)
    · simp [cx, hsupp u hu]

/-- A profile supported on `[-T, 0]` has an entire transform. -/
theorem differentiable_laplace_of_head {F : ℝ → ℝ} (hFm : Measurable F) (hFi : Integrable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {T : ℝ} (hhead : ∀ u, u < -T → F u = 0) :
    Differentiable ℂ (negativeHalfLineLaplace (cx F)) := by
  intro w
  have habs : ∀ c, (w.re - 1) < c → Integrable fun u => |F u| * Real.exp (c * u) := by
    intro c _
    refine (hFi.abs.mul_const (Real.exp (|c| * |T|))).mono'
      ((hFm.abs.mul (by fun_prop : Measurable fun u : ℝ => Real.exp (c * u))).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    rcases lt_or_ge u (-T) with h1 | h1
    · simp [hhead u h1]
    rcases lt_or_ge u 0 with h2 | h2
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
      have : |u| ≤ |T| := by rw [abs_of_neg h2]; exact (neg_le.mpr h1).trans (le_abs_self T)
      calc c * u ≤ |c * u| := le_abs_self _
        _ = |c| * |u| := abs_mul c u
        _ ≤ |c| * |T| := mul_le_mul_of_nonneg_left this (abs_nonneg c)
    · simp [hsupp u h2]
  exact (differentiableOn_laplace_of_abs hFm hsupp habs).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by show w.re - 1 < w.re; linarith))

/-! ### The tail measure and Landau's theorem -/

/-- The reflected tail of a profile: the measure `g(-v) dv` on `v > T`. -/
def tailMeasure (g : ℝ → ℝ) (T : ℝ) : Measure ℝ :=
  Measure.map (fun u : ℝ => -u)
    ((volume.restrict (Iio (-T))).withDensity fun u => ENNReal.ofReal (g u))

theorem preimage_neg_Ioi_zero : (fun u : ℝ => -u) ⁻¹' Ioi 0 = Iio 0 := by
  ext u; simp

theorem restrict_Iio_restrict_Iio_zero {T : ℝ} (hT : 0 ≤ T) :
    (volume.restrict (Iio (-T))).restrict (Iio (0 : ℝ)) = volume.restrict (Iio (-T)) := by
  rw [Measure.restrict_restrict measurableSet_Iio, Iio_inter_Iio,
    show (0 : ℝ) ⊓ -T = -T from inf_eq_right.mpr (by linarith)]

theorem laplaceMass_tailMeasure {g : ℝ → ℝ} (hg : Measurable g) {T : ℝ} (hT : 0 ≤ T) (σ : ℝ) :
    laplaceMass (tailMeasure g T) σ =
      ∫⁻ u in Iio (-T), ENNReal.ofReal (g u) * ENNReal.ofReal (Real.exp (σ * u)) := by
  unfold laplaceMass tailMeasure
  rw [setLIntegral_map measurableSet_Ioi
      (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun v : ℝ => Real.exp (-σ * v)))
      measurable_neg, preimage_neg_Ioi_zero,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (ENNReal.measurable_ofReal.comp hg)
      (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun u : ℝ => Real.exp (-σ * -u)))
      measurableSet_Iio, restrict_Iio_restrict_Iio_zero hT]
  refine lintegral_congr fun u => ?_
  simp only [Pi.mul_apply, neg_mul_neg]

theorem laplaceMass_tailMeasure_ne_top_iff {g : ℝ → ℝ} (hg : Measurable g) {T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ᵐ u ∂(volume.restrict (Iio (-T))), 0 ≤ g u) (σ : ℝ) :
    laplaceMass (tailMeasure g T) σ ≠ ⊤ ↔
      IntegrableOn (fun u => g u * Real.exp (σ * u)) (Iio (-T)) := by
  rw [laplaceMass_tailMeasure hg hT]
  have heq : (fun u => ENNReal.ofReal (g u) * ENNReal.ofReal (Real.exp (σ * u))) =ᵐ[volume.restrict
      (Iio (-T))] fun u => ENNReal.ofReal (g u * Real.exp (σ * u)) := by
    filter_upwards [hpos] with u hu
    exact (ENNReal.ofReal_mul hu).symm
  rw [lintegral_congr_ae heq]
  exact lintegral_ofReal_ne_top_iff_integrable
    ((hg.mul (by fun_prop : Measurable fun u : ℝ => Real.exp (σ * u))).aestronglyMeasurable)
    (by filter_upwards [hpos] with u hu; positivity)

theorem laplaceReal_tailMeasure {g : ℝ → ℝ} (hg : Measurable g) {T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ᵐ u ∂(volume.restrict (Iio (-T))), 0 ≤ g u) (σ : ℝ) :
    laplaceReal (tailMeasure g T) σ = ∫ u in Iio (-T), g u * Real.exp (σ * u) := by
  unfold laplaceReal tailMeasure
  rw [setIntegral_map measurableSet_Ioi
      (by fun_prop : Continuous fun v : ℝ => Real.exp (-σ * v)).aestronglyMeasurable
      measurable_neg.aemeasurable, preimage_neg_Ioi_zero,
    setIntegral_withDensity_eq_setIntegral_toReal_smul (ENNReal.measurable_ofReal.comp hg)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ measurableSet_Iio,
    restrict_Iio_restrict_Iio_zero hT]
  refine integral_congr_ae ?_
  filter_upwards [hpos] with u hu
  simp only [smul_eq_mul, ENNReal.toReal_ofReal hu, neg_mul_neg]

/-- The infimum of the convergent exponents is an abscissa. -/
theorem isAbscissa_sInf {ν : Measure ℝ} {σ₀ σ₁ : ℝ} (h0 : laplaceMass ν σ₀ = ⊤)
    (h1 : laplaceMass ν σ₁ ≠ ⊤) :
    IsAbscissa ν (sInf {σ | laplaceMass ν σ ≠ ⊤}) ∧ σ₀ ≤ sInf {σ | laplaceMass ν σ ≠ ⊤} := by
  set S := {σ | laplaceMass ν σ ≠ ⊤} with hS
  have hne : S.Nonempty := ⟨σ₁, h1⟩
  have hlow : ∀ σ ∈ S, σ₀ ≤ σ := fun σ hσ => by
    by_contra h
    have := laplaceMass_antitone ν (le_of_lt (lt_of_not_ge h))
    rw [h0, top_le_iff] at this
    exact hσ this
  have hbdd : BddBelow S := ⟨σ₀, hlow⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne hlow⟩
  · obtain ⟨σ', hσ'S, hσ'σ⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone ν hσ'σ.le)
  · by_contra h
    exact (not_le.mpr hσ) (csInf_le hbdd h)

/-- **Landau.** The Laplace transform of a positive measure has no holomorphic extension to a disc
around a real point `a` reaching past the abscissa. -/
theorem landau_no_holomorphic_extension {ν : Measure ℝ} {c a R : ℝ} (hc : IsAbscissa ν c)
    (ha : c < a) (hR : a - c < R) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball (a : ℂ) R))
    {V : Set ℝ} (hV : IsOpen V) (haV : a ∈ V) (hVsub : ∀ y ∈ V, (y : ℂ) ∈ ball (a : ℂ) R)
    (hGV : ∀ y ∈ V, laplaceReal ν y = (G y).re) : False := by
  obtain ⟨t, ht1, ht2⟩ := exists_between hR
  obtain ⟨r, hr1, hr2⟩ := exists_between ht2
  have ht0 : 0 ≤ t := by linarith
  have hr0 : 0 < r := by linarith
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedDeriv_le_of_differentiableOn_ball hG hr0 hr2
  apply not_summable_iteratedDeriv_beyond_abscissa hc ha ht0 ht1
  have hq : t / r < 1 := (div_lt_one hr0).mpr hr1
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one (by positivity) hq).mul_left C)
  rw [iteratedDeriv_eq_re_of_differentiableOn isOpen_ball hG hV hVsub hGV k haV]
  have hk := hC k
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  calc t ^ k / (k.factorial : ℝ) * |(iteratedDeriv k G (a : ℂ)).re|
      ≤ t ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k G (a : ℂ)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ t ^ k / (k.factorial : ℝ) * ((k.factorial : ℝ) * C / r ^ k) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
    _ = C * (t / r) ^ k := by
        rw [div_pow]; field_simp

/-! ### The remainder with the pole at `1` removed -/

/-- `(s-1)ζ(s)` has no zero at a real point `s > ½`. -/
theorem zetaEntire_ofReal_ne_zero {x : ℝ} (hx : 1 / 2 < x) : zetaEntire (x : ℂ) ≠ 0 := by
  rcases lt_trichotomy x 1 with h | h | h
  · have hne : (x : ℂ) ≠ 1 := by intro e; have := congrArg Complex.re e; simp at this; linarith
    rw [zetaEntire_eq hne]
    refine mul_ne_zero (sub_ne_zero.mpr hne) (riemannZeta_ne_zero_of_ofReal_mem_Ioo (by linarith) h)
  · subst h; simp [zetaEntire_eval_one]
  · have hne : (x : ℂ) ≠ 1 := by intro e; have := congrArg Complex.re e; simp at this; linarith
    rw [zetaEntire_eq hne]
    exact mul_ne_zero (sub_ne_zero.mpr hne) (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))

/-- The state remainder written with `(s-1)ζ(s)` and the divided difference of the transform at
`½`; it is holomorphic across `p = ½`. -/
def stateRemainder (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  stateGamma F p + negativeHalfLineLaplace (cx F) p * logDeriv zetaEntire (1 / 2 + p) -
    dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p - stateTail F p +
    negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)

/-- Off `½` and off the zeros of `ζ(½ + ·)`, the state equation is the confinement term plus the
remainder. -/
theorem stateEquation_eq_remainder {W₀ : ℝ} {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : p ≠ 1 / 2) (hζ : riemannZeta (1 / 2 + p) ≠ 0) :
    stateEquation W₀ F p = criticalAliasCoefficient W₀ * negativeHalfLineLaplace (cx F) (p - 8) +
      stateRemainder F p := by
  have hs1 : (1 : ℂ) / 2 + p ≠ 1 := by intro h; apply hp; linear_combination h
  have hlog := Sieve.logDeriv_riemannZeta_eq hs1 hζ
  rw [logDeriv_apply] at hlog
  obtain ⟨hplus, hminus⟩ := negativeHalfLineLaplace_halfPole_real hF.weighted
  have hds : dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p =
      (negativeHalfLineLaplace (cx F) p - negativeHalfLineLaplace (cx F) (1 / 2)) / (p - 1 / 2) := by
    rw [dslope_of_ne _ hp, slope_def_field]
  have hpm : p - 1 / 2 ≠ 0 := sub_ne_zero.mpr hp
  have hh : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rw [hh] at hplus
  rw [show (-((1 / 2 : ℝ) : ℂ)) = -(1 / 2) by push_cast; ring] at hminus
  unfold stateEquation stateRemainder
  rw [hlog, hds, hplus, hminus]
  have e1 : (1 : ℂ) / 2 + p - 1 = p - 1 / 2 := by ring
  rw [e1]
  push_cast
  field_simp
  ring

/-- The remainder is holomorphic wherever `Re p > 0` and `(s-1)ζ(s)` has no zero at `s = ½ + p`. -/
theorem differentiableAt_stateRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : 0 < p.re) (hz : zetaEntire (1 / 2 + p) ≠ 0) :
    DifferentiableAt ℂ (stateRemainder F) p := by
  have hopen0 : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hopen4 : IsOpen {p : ℂ | -(8 / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLap := differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
  have hL : DifferentiableAt ℂ (negativeHalfLineLaplace (cx F)) p :=
    hLap.differentiableAt (hopen4.mem_nhds (by show -(8 / 2) < p.re; linarith))
  have hG := (differentiableOn_stateGamma hF).differentiableAt (hopen0.mem_nhds hp)
  have hT := (differentiableOn_stateTail hF).differentiableAt (hopen0.mem_nhds hp)
  have hZ : DifferentiableAt ℂ (fun p : ℂ => logDeriv zetaEntire (1 / 2 + p)) p := by
    have hd1 : DifferentiableAt ℂ (fun p : ℂ => deriv zetaEntire (1 / 2 + p)) p :=
      (differentiable_deriv_zetaEntire _).comp p ((differentiableAt_const _).add differentiableAt_id)
    have hd2 : DifferentiableAt ℂ (fun p : ℂ => zetaEntire (1 / 2 + p)) p :=
      (differentiable_zetaEntire _).comp p ((differentiableAt_const _).add differentiableAt_id)
    simp only [logDeriv_apply]
    exact hd1.div hd2 hz
  have hD : DifferentiableAt ℂ (dslope (negativeHalfLineLaplace (cx F)) (1 / 2)) p := by
    have hhalf : {p : ℂ | -(8 / 2) < p.re} ∈ 𝓝 ((1 : ℂ) / 2) :=
      hopen4.mem_nhds (by show -(8 / 2) < ((1 : ℂ) / 2).re; norm_num)
    exact ((differentiableOn_dslope hhalf).mpr hLap).differentiableAt
      (hopen4.mem_nhds (by show -(8 / 2) < p.re; linarith))
  have hP : DifferentiableAt ℂ (fun p : ℂ => negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)) p :=
    (differentiableAt_const _).div (differentiableAt_id.add_const _)
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)
  exact ((((hG.add (hL.mul hZ)).sub hD).sub hT).add hP)

end GaloisForLFunctions.ExclusionOfTheCriticalState
