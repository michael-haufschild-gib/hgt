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
  rw [setLIntegral_map (f := fun v : ℝ => ENNReal.ofReal (Real.exp (-σ * v)))
      (g := fun u : ℝ => -u) measurableSet_Ioi (ENNReal.measurable_ofReal.comp (by fun_prop))
      (by fun_prop), preimage_neg_Ioi_zero,
    setLIntegral_withDensity_eq_setLIntegral_mul (f := fun u => ENNReal.ofReal (g u))
      (g := fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * -u))) _
      (ENNReal.measurable_ofReal.comp hg) (ENNReal.measurable_ofReal.comp (by fun_prop))
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
      (measurable_neg : Measurable fun u : ℝ => -u).aemeasurable, preimage_neg_Ioi_zero,
    setIntegral_withDensity_eq_setIntegral_toReal_smul (f := fun u => ENNReal.ofReal (g u))
      (ENNReal.measurable_ofReal.comp hg)
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

/-! ### The sign law -/

/-- Confinement makes `|F| e^{cu}` integrable for every `c > -4`. -/
theorem integrable_abs_mul_exp_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {c : ℝ}
    (hc : -4 < c) : Integrable fun u => |F u| * Real.exp (c * u) :=
  integrable_abs_mul_exp_of_sq hF.meas hF.support hF.exponential (by linarith)

/-- The tail controls the whole profile: the head `[-T, 0]` is always integrable. -/
theorem integrable_abs_mul_exp_of_tail {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {T c : ℝ}
    (htail : IntegrableOn (fun u => |F u| * Real.exp (c * u)) (Iio (-T))) :
    Integrable fun u => |F u| * Real.exp (c * u) := by
  have hhead : IntegrableOn (fun u => |F u| * Real.exp (c * u)) (Ici (-T)) := by
    refine (hF.integrable.abs.mul_const (Real.exp (|c| * |T|))).integrableOn.mono'
      ((hF.meas.abs.mul (by fun_prop : Measurable fun u : ℝ => Real.exp (c * u))).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    rcases lt_or_ge u 0 with h2 | h2
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
      have hu' : -T ≤ u := hu
      have : |u| ≤ |T| := by rw [abs_of_neg h2]; exact (neg_le.mpr hu').trans (le_abs_self T)
      calc c * u ≤ |c * u| := le_abs_self _
        _ = |c| * |u| := abs_mul c u
        _ ≤ |c| * |T| := mul_le_mul_of_nonneg_left this (abs_nonneg c)
    · simp [hF.support u h2]
  have h := htail.union hhead
  rw [Iio_union_Ici, integrableOn_univ] at h
  exact h

/-- RH fails whenever the window threshold is finite. -/
theorem not_riemannHypothesis_of_threshold {W₀ : ℝ}
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) :
    ¬ RiemannHypothesis := by
  intro hRH
  have h := riemannHypothesis_iff_windowThreshold_eq_top.mp hRH
  have htop : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = ⊤ :=
    iInf_eq_top.mpr fun A => iInf_eq_top.mpr fun hA => h A hA
  rw [hthreshold] at htop
  exact EReal.coe_ne_top _ htop

/-- **Landau step.** If the critical state has one sign on a ray, its transform converges
absolutely on `Re w > -8`. -/
theorem criticalState_integrable_of_sign {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {s T : ℝ} (hs : s = 1 ∨ s = -1)
    (hT : 0 ≤ T) (hsign : ∀ᵐ u ∂(volume.restrict (Iio (-T))), 0 ≤ s * F u) {σ : ℝ}
    (hσ : -8 < σ) : Integrable fun u => |F u| * Real.exp (σ * u) := by
  by_contra hnot
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  set g : ℝ → ℝ := fun u => s * F u with hgdef
  have hgm : Measurable g := measurable_const.mul hd.meas
  have habs_s : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hgabs : ∀ c u, ‖g u * Real.exp (c * u)‖ = |F u| * Real.exp (c * u) := fun c u => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    simp [g, abs_mul, habs_s]
  have htail_iff : ∀ c, IntegrableOn (fun u => g u * Real.exp (c * u)) (Iio (-T)) →
      Integrable fun u => |F u| * Real.exp (c * u) := fun c h =>
    integrable_abs_mul_exp_of_tail hd (T := T)
      (h.norm.congr (Eventually.of_forall fun u => hgabs c u))
  have hto_tail : ∀ c, (Integrable fun u => |F u| * Real.exp (c * u)) →
      IntegrableOn (fun u => g u * Real.exp (c * u)) (Iio (-T)) := fun c h =>
    (h.integrableOn).mono' ((hgm.mul (by fun_prop : Measurable fun u : ℝ => Real.exp (c * u))).aestronglyMeasurable)
      (Eventually.of_forall fun u => (hgabs c u).le)
  set ν := tailMeasure g T with hν
  have hmass : ∀ c, laplaceMass ν c ≠ ⊤ ↔
      IntegrableOn (fun u => g u * Real.exp (c * u)) (Iio (-T)) :=
    laplaceMass_tailMeasure_ne_top_iff hgm hT hsign
  have h0 : laplaceMass ν σ = ⊤ := by
    by_contra h
    exact hnot (htail_iff σ ((hmass σ).mp h))
  have h1 : laplaceMass ν (-3) ≠ ⊤ :=
    (hmass _).mpr (hto_tail _ (integrable_abs_mul_exp_of_domain hd (by norm_num)))
  obtain ⟨hc, hσc⟩ := isAbscissa_sInf h0 h1
  set c := sInf {τ | laplaceMass ν τ ≠ ⊤} with hcdef
  have hc4 : c ≤ -4 := by
    by_contra h
    have h' : -4 < c := lt_of_not_ge h
    have hτ : laplaceMass ν ((c - 4) / 2) ≠ ⊤ :=
      (hmass _).mpr (hto_tail _ (integrable_abs_mul_exp_of_domain hd (by linarith)))
    have : c ≤ (c - 4) / 2 := not_lt.mp fun hlt => hτ (hc.2 _ hlt)
    linarith
  have habsc : ∀ τ, c < τ → Integrable fun u => |F u| * Real.exp (τ * u) := fun τ hτ =>
    htail_iff τ ((hmass τ).mp (hc.1 τ hτ))
  have hLapc := differentiableOn_laplace_of_abs hd.meas hd.support habsc
  set p₀ := c + 8 with hp₀def
  have hp₀ : 0 < p₀ := by rw [hp₀def]; linarith
  have hp₀4 : p₀ ≤ 4 := by rw [hp₀def]; linarith
  -- a zero-free neighbourhood of the real segment `[p₀/2, p₀ + 6]`
  set U : Set ℂ := {p : ℂ | 0 < p.re} ∩ {p : ℂ | zetaEntire (1 / 2 + p) ≠ 0} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_ne_fun (differentiable_zetaEntire.continuous.comp (continuous_const.add continuous_id))
        continuous_const)
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc (p₀ / 2) (p₀ + 6) with hKdef
  have hKc : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKU : K ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨show 0 < (x : ℂ).re by simp; linarith [hx.1], ?_⟩
    show zetaEntire (1 / 2 + (x : ℂ)) ≠ 0
    rw [show (1 : ℂ) / 2 + (x : ℂ) = ((1 / 2 + x : ℝ) : ℂ) by push_cast; ring]
    exact zetaEntire_ofReal_ne_zero (by linarith [hx.1])
  obtain ⟨η, hη, hηU⟩ := hKc.exists_thickening_subset_open hUo hKU
  set S : Set ℂ := (({p : ℂ | p₀ / 2 < p.re} ∩ {p : ℂ | p.re < p₀ + 6}) ∩
    {p : ℂ | p.im < η}) ∩ {p : ℂ | -η < p.im} with hSdef
  have hSU : S ⊆ U := by
    intro p hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    apply hηU
    rw [Metric.mem_thickening_iff]
    refine ⟨(p.re : ℂ), ⟨p.re, ⟨le_of_lt h1, le_of_lt h2⟩, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have : p - (p.re : ℂ) = (p.im : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨h4, h3⟩
  set D : Set ℂ := S ∩ {p : ℂ | p₀ < p.re} with hDdef
  have hSo : IsOpen S :=
    (((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).inter
      (isOpen_lt Complex.continuous_im continuous_const)).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hDo : IsOpen D := hSo.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hDconv : Convex ℝ D :=
    ((((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter
      (convex_halfSpace_im_lt _)).inter (convex_halfSpace_im_gt _)).inter (convex_halfSpace_re_gt _)
  -- the continuation identity on `D`
  set α : ℝ := criticalAliasCoefficient W₀ with hα
  have hαpos : 0 < α := criticalAliasCoefficient_positive hW
  have hEq : EqOn (fun p : ℂ => (α : ℂ) * negativeHalfLineLaplace (cx F) (p - 8) +
      stateRemainder F p) 0 D := by
    have hdiff : DifferentiableOn ℂ (fun p : ℂ => (α : ℂ) * negativeHalfLineLaplace (cx F) (p - 8) +
        stateRemainder F p) D := by
      intro p hp
      have hpU := hSU hp.1
      have hL8 := differentiableAt_laplace_sub_eight hLapc (p := p)
        (by have : p₀ < p.re := hp.2; rw [hp₀def] at this; linarith)
      exact ((hL8.const_mul _).add (differentiableAt_stateRemainder hd hpU.1 hpU.2)).differentiableWithinAt
    have hz₁ : ((p₀ + 5 : ℝ) : ℂ) ∈ D := by
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> simp <;> linarith
    have hev : (fun p : ℂ => (α : ℂ) * negativeHalfLineLaplace (cx F) (p - 8) +
        stateRemainder F p) =ᶠ[𝓝 ((p₀ + 5 : ℝ) : ℂ)] 0 := by
      have hO : IsOpen (D ∩ {p : ℂ | max 1 (c + 8) < p.re}) :=
        hDo.inter (isOpen_lt continuous_const Complex.continuous_re)
      have hmem : ((p₀ + 5 : ℝ) : ℂ) ∈ D ∩ {p : ℂ | max 1 (c + 8) < p.re} :=
        ⟨hz₁, show max 1 (c + 8) < ((p₀ + 5 : ℝ) : ℂ).re by
          rw [max_lt_iff]; simp; constructor <;> linarith⟩
      filter_upwards [hO.mem_nhds hmem] with p hp
      have hp1 : 1 < p.re := lt_of_le_of_lt (le_max_left _ _) (show max 1 (c + 8) < p.re from hp.2)
      have hzero := stateEquation_eqOn_zero hW hthreshold hF hc4 hLapc hp.2
      have hne : p ≠ 1 / 2 := by
        intro h; rw [h] at hp1; norm_num at hp1
      have hζ : riemannZeta (1 / 2 + p) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
      rw [stateEquation_eq_remainder hd hne hζ] at hzero
      simpa using hzero
    exact (hdiff.analyticOnNhd hDo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hDconv.isPreconnected hz₁ hev
  -- Landau's contradiction at the abscissa
  set ε := min (η / 4) (p₀ / 8) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεη : ε ≤ η / 4 := min_le_left _ _
  have hεp : ε ≤ p₀ / 8 := min_le_right _ _
  set a := c + ε with hadef
  set F' : ℝ → ℝ := (Ici (-T)).indicator F with hF'def
  have hF'm : Measurable F' := hd.meas.indicator measurableSet_Ici
  have hF'supp : ∀ u, 0 ≤ u → F' u = 0 := fun u hu => by
    simp [F', Set.indicator, hd.support u hu]
  have hF'head : ∀ u, u < -T → F' u = 0 := fun u hu => by
    simp [F', not_le.mpr hu]
  have hHead := differentiable_laplace_of_head hF'm (hd.integrable.indicator measurableSet_Ici)
    hF'supp hF'head
  set G : ℂ → ℂ := fun w => (s : ℂ) * (-(stateRemainder F (w + 8)) / (α : ℂ) -
    negativeHalfLineLaplace (cx F') w) with hGdef
  have hball : ∀ w ∈ ball (a : ℂ) (2 * ε), w + 8 ∈ S := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw.le))
    have him := (abs_le.mp ((Complex.abs_im_le_norm _).trans hw.le))
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hre him
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> simp <;> linarith
  have hG : DifferentiableOn ℂ G (ball (a : ℂ) (2 * ε)) := by
    intro w hw
    have hpU := hSU (hball w hw)
    have hR : DifferentiableAt ℂ (fun w : ℂ => stateRemainder F (w + 8)) w :=
      (differentiableAt_stateRemainder hd hpU.1 hpU.2).comp w (differentiableAt_id.add_const _)
    exact (((hR.neg.div_const _).sub (hHead w)).const_mul _).differentiableWithinAt
  have hV : ∀ y ∈ Ioo c (c + 2 * ε), (y : ℂ) ∈ ball (a : ℂ) (2 * ε) := by
    intro y hy
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hGV : ∀ y ∈ Ioo c (c + 2 * ε), laplaceReal ν y = (G y).re := by
    intro y hy
    have hyc : c < y := hy.1
    have hint : Integrable fun u => F u * Real.exp (y * u) :=
      (habsc y hyc).mono' ((hd.meas.mul (by fun_prop : Measurable fun u : ℝ => Real.exp (y * u))).aestronglyMeasurable)
        (Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)])
    have hsplit : (∫ u, F u * Real.exp (y * u)) =
        (∫ u in Iio (-T), F u * Real.exp (y * u)) + ∫ u, F' u * Real.exp (y * u) := by
      rw [← integral_add_compl measurableSet_Iio hint, compl_Iio, ← integral_indicator measurableSet_Ici]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [F', Set.indicator]
      split_ifs <;> simp
    have hD8 : (y : ℂ) + 8 ∈ D := by
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> simp <;> linarith [hy.1, hy.2]
    have hrel := hEq hD8
    simp only [Pi.zero_apply, add_sub_cancel_right] at hrel
    have hRem : stateRemainder F ((y : ℂ) + 8) = -((α : ℂ) * negativeHalfLineLaplace (cx F) y) := by
      linear_combination hrel
    have hαne : (α : ℂ) ≠ 0 := by exact_mod_cast hαpos.ne'
    have hGy : G y = (((s * ((∫ u, F u * Real.exp (y * u)) -
        ∫ u, F' u * Real.exp (y * u)) : ℝ)) : ℂ) := by
      simp only [hGdef, hRem, negativeHalfLineLaplace_ofReal]
      field_simp
      push_cast
      ring
    rw [hGy, Complex.ofReal_re, laplaceReal_tailMeasure hgm hT hsign, hsplit]
    have : (∫ u in Iio (-T), g u * Real.exp (y * u)) = s * ∫ u in Iio (-T), F u * Real.exp (y * u) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp [g, mul_assoc]
    rw [this]
    ring
  exact landau_no_holomorphic_extension hc (show c < a by rw [hadef]; linarith)
    (show a - c < 2 * ε by rw [hadef]; linarith) hG isOpen_Ioo
    (show a ∈ Ioo c (c + 2 * ε) by rw [hadef]; constructor <;> linarith) hV hGV

/-- **The sign law.** The critical state has one sign on no ray `u < -T`. -/
theorem criticalState_not_eventually_signed {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {s : ℝ} (hs : s = 1 ∨ s = -1) (T : ℝ) :
    ¬ ∀ᵐ u ∂(volume.restrict (Iio (-T))), 0 ≤ s * F u := by
  intro hsign
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  set T' := max T 0 with hT'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  have hsign' : ∀ᵐ u ∂(volume.restrict (Iio (-T'))), 0 ≤ s * F u :=
    ae_restrict_of_ae_restrict_of_subset (Iio_subset_Iio (by simp [T'])) hsign
  have hLap := differentiableOn_laplace_of_abs hd.meas hd.support fun σ hσ =>
    criticalState_integrable_of_sign hW hthreshold hF hs hT'0 hsign' hσ
  obtain ⟨ρ, hζ, hρ, -⟩ :=
    exists_zetaZero_re_gt_half_of_not_riemannHypothesis (not_riemannHypothesis_of_threshold hthreshold)
  have := zero_re_le_of_laplace_holomorphic hW hthreshold hF (κ := -8) (by norm_num) hLap hζ hρ
  linarith

/-- **The critical state changes sign on every ray** `u < -T`. -/
theorem criticalState_changes_sign_on_every_ray {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (T : ℝ) :
    (¬ ∀ᵐ u ∂(volume.restrict (Iio (-T))), 0 ≤ F u) ∧
      ¬ ∀ᵐ u ∂(volume.restrict (Iio (-T))), F u ≤ 0 := by
  refine ⟨fun h => criticalState_not_eventually_signed hW hthreshold hF (s := 1) (Or.inl rfl) T ?_,
    fun h => criticalState_not_eventually_signed hW hthreshold hF (s := -1) (Or.inr rfl) T ?_⟩
  · filter_upwards [h] with u hu; linarith
  · filter_upwards [h] with u hu; linarith

/-- Either RH holds, or the critical state exists and has one sign on no ray. -/
theorem riemannHypothesis_or_criticalState_changes_sign :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧
        ∀ T : ℝ, (¬ ∀ᵐ u ∂(volume.restrict (Iio (-T))), 0 ≤ F u) ∧
          ¬ ∀ᵐ u ∂(volume.restrict (Iio (-T))), F u ≤ 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, criticalState_changes_sign_on_every_ray hW ht hF⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
