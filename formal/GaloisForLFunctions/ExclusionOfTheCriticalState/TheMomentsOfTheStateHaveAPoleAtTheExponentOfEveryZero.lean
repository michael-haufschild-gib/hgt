import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateDecaysExactlyAtTheRateOfTheZeros

/-!
# The moments of the state have a pole at the exponent of every zero

Let `ρ` be a zero of `ζ` right of the critical line, `z₀ = ρ - 1/2`, of multiplicity `m`, and
`b_ρ = 17 - 2 Re ρ` its exponent. The square moments `M(b) = ∫ F² e^{-bu} du` of the critical
state `F` are infinite for `b > b_ρ`. This file treats the endpoint and the approach to it:

  `liminf_{η → 0⁺} η · M(b_ρ - η) ≥ (m |L F(z₀)| / a)² > 0`.

So `M` grows at `b_ρ` at least like a simple pole whose residue is the squared residue of
`L F` at the transported zero `z₀ - 8`, and `M(b_ρ) = ∞`. A finite moment `M(b)` therefore
puts every zero strictly left of `(17 - b)/2`; when the supremum `Θ` of the real parts of the
zeros is attained, the finite moments are exactly those with `b < 17 - 2Θ`.

Mechanism. If `M(b_ρ - η) < ∞`, the transform converges on `Re w > Re z₀ - 8 + η/2` and the
cleared state equation holds at `p = z₀ + η`:

  `a L F(p - 8) = -L F(p) ζ'/ζ(1/2 + p) - (Gamma term - prime tail + pole part)(p)`.

Multiplied by `η` the right side tends to `-m L F(z₀)`, which is not zero because the transform
of the state has no zero on `Re w ≥ 0`. On the left Cauchy–Schwarz gives
`η |L F(p - 8)|² ≤ M(b_ρ - η)`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Cauchy–Schwarz for the transform -/

theorem integrableOn_exp_mul_Iio_zero {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Real.exp (c * u)) (Iio 0) :=
  (integrableOn_exp_mul_Iic hc 0).mono_set Iio_subset_Iic_self

theorem integral_exp_mul_Iio_zero {c : ℝ} (hc : 0 < c) :
    (∫ u in Iio (0 : ℝ), Real.exp (c * u)) = 1 / c := by
  rw [← integral_Iic_eq_integral_Iio, integral_exp_mul_Iic hc, mul_zero, Real.exp_zero]

/-- **Cauchy–Schwarz on the half-line.** With `c = 2σ + b > 0`,
`c (∫ |F| e^{σu})² ≤ ∫ F² e^{-bu}`: the square of `|F| e^{-bu/2} - λ e^{cu/2}` is integrated
at `λ = c ∫ |F| e^{σu}`. -/
theorem mul_sq_integral_abs_mul_exp_le {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {b σ c : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) (hc : 0 < c)
    (hcσ : c = 2 * σ + b) :
    c * (∫ u, |F u| * Real.exp (-(-σ * u))) ^ 2 ≤ ∫ u, F u ^ 2 * Real.exp (-(b * u)) := by
  have hB := integrable_abs_mul_exp_neg_of_decay hFm hsupp hb (m := -σ) (by linarith)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∫ u, |F u| * Real.exp (-(-σ * u)) := ⟨_, rfl⟩
  rw [← hBdef]
  have hE := (integrableOn_exp_mul_Iio_zero hc).integrable_indicator measurableSet_Iio
  have hpt : ∀ u : ℝ, 2 * (c * B) * (|F u| * Real.exp (-(-σ * u))) ≤
      F u ^ 2 * Real.exp (-(b * u)) +
        (c * B) ^ 2 * (Iio (0 : ℝ)).indicator (fun u => Real.exp (c * u)) u := by
    intro u
    rcases le_or_gt 0 u with hu | hu
    · rw [hsupp u hu, Set.indicator_of_notMem (show u ∉ Iio (0 : ℝ) from not_lt.mpr hu)]
      simp
    · rw [Set.indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu)]
      have e1 : Real.exp (-(b * u)) = Real.exp (-(b / 2 * u)) ^ 2 := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      have e2 : Real.exp (c * u) = Real.exp (c / 2 * u) ^ 2 := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      have e3 : Real.exp (-(-σ * u)) = Real.exp (-(b / 2 * u)) * Real.exp (c / 2 * u) := by
        rw [← Real.exp_add, hcσ]
        congr 1
        ring
      show 2 * (c * B) * (|F u| * Real.exp (-(-σ * u))) ≤
        F u ^ 2 * Real.exp (-(b * u)) + (c * B) ^ 2 * Real.exp (c * u)
      rw [e1, e2, e3, ← sq_abs (F u)]
      linarith [sq_nonneg (|F u| * Real.exp (-(b / 2 * u)) - c * B * Real.exp (c / 2 * u))]
  have hI : (∫ u, 2 * (c * B) * (|F u| * Real.exp (-(-σ * u)))) ≤
      ∫ u, (F u ^ 2 * Real.exp (-(b * u)) +
        (c * B) ^ 2 * (Iio (0 : ℝ)).indicator (fun u => Real.exp (c * u)) u) :=
    integral_mono (hB.const_mul _) (hb.add (hE.const_mul _)) hpt
  rw [integral_const_mul, integral_add hb (hE.const_mul _), integral_const_mul,
    integral_indicator measurableSet_Iio, integral_exp_mul_Iio_zero hc, ← hBdef,
    show (c * B) ^ 2 * (1 / c) = c * B ^ 2 * (c * (1 / c)) by ring,
    mul_one_div_cancel hc.ne', mul_one] at hI
  linarith

/-- **Cauchy–Schwarz for the transform.** For `-2 Re w < b`,
`(2 Re w + b) |L F(w)|² ≤ ∫ F² e^{-bu} du`. -/
theorem mul_norm_sq_laplace_le_of_decay {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {b : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) {w : ℂ} (hw : -(2 * w.re) < b) :
    (2 * w.re + b) * ‖negativeHalfLineLaplace (cx F) w‖ ^ 2 ≤
      ∫ u, F u ^ 2 * Real.exp (-(b * u)) := by
  have hc : 0 < 2 * w.re + b := by linarith
  have hLB : ‖negativeHalfLineLaplace (cx F) w‖ ≤ ∫ u, |F u| * Real.exp (-(-w.re * u)) := by
    unfold negativeHalfLineLaplace
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun u => ?_)))
    show ‖cexp (w * (u : ℂ)) * ((F u : ℝ) : ℂ)‖ = |F u| * Real.exp (-(-w.re * u))
    have hre : (w * (u : ℂ)).re = -(-w.re * u) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, hre, mul_comm]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hLB 2
  exact (mul_le_mul_of_nonneg_left h2 hc.le).trans
    (mul_sq_integral_abs_mul_exp_le hFm hsupp hb hc rfl)

/-! ### The state equation at the edge of convergence -/

/-- The Gamma term, the prime tail and the pole part of the state equation: the part that stays
continuous at the centred zeros off the real axis. -/
def stateRegularPart (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  stateGamma F p - stateTail F p +
    ((coshHalfMoment F : ℂ) * (1 / (p + 1 / 2) + 1 / (p - 1 / 2)) -
      (sinhHalfMoment F : ℂ) * (1 / (p + 1 / 2) - 1 / (p - 1 / 2)))

theorem continuousAt_stateRegularPart {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hre : 0 < p.re) (him : 0 < p.im) : ContinuousAt (stateRegularPart F) p := by
  have hopen0 : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG := (differentiableOn_stateGamma hd).differentiableAt (hopen0.mem_nhds hre)
  have hT := (differentiableOn_stateTail hd).differentiableAt (hopen0.mem_nhds hre)
  have hP := differentiableAt_polePart (coshHalfMoment F) (sinhHalfMoment F) (p := p)
    (by intro h; have := congrArg Complex.im h; simp at this; linarith)
    (by intro h; have := congrArg Complex.im h; simp at this; linarith)
  exact ((hG.sub hT).add hP).continuousAt

/-- **The residue of `ζ'/ζ` at a centred zero**: `(p - z₀) ζ'/ζ(1/2 + p) → m` as `p → z₀`. -/
theorem tendsto_sub_mul_logDeriv_zeta_centred {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) :
    Tendsto (fun p : ℂ => (p - (ρ - 1 / 2)) *
        (deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p))) (𝓝[≠] (ρ - 1 / 2))
      (𝓝 (((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ)) := by
  have hres := logDeriv_iteratedDeriv_residue_of_zero (HTGeometry.analyticAt_riemannZeta hρ1)
    (RHTower.analyticOrderAt_riemannZeta_ne_top hρ1) hζ 0
  simp only [zero_add, pow_one, iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one] at hres
  have hshift : Tendsto (fun p : ℂ => 1 / 2 + p) (𝓝[≠] (ρ - 1 / 2)) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun p : ℂ => 1 / 2 + p) (𝓝 (ρ - 1 / 2)) (𝓝 (1 / 2 + (ρ - 1 / 2))) :=
        tendsto_const_nhds.add tendsto_id
      rw [show (1 : ℂ) / 2 + (ρ - 1 / 2) = ρ by ring] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with p hp h
      apply hp
      rw [Set.mem_singleton_iff] at h ⊢
      linear_combination h
  refine (hres.comp hshift).congr fun p => ?_
  simp only [Function.comp]
  ring_nf

/-- **The state equation at the edge of convergence.** Let `ρ` be a zero of `ζ` in the upper
half-plane right of the critical line and `p = ρ - 1/2 + η`, `0 < η ≤ 1`. If the moment
`∫ F² e^{-(17 - 2 Re ρ - η)u}` is finite, then `ζ(1/2 + p) ≠ 0` and
`a L F(p - 8) = -(regular part)(p) - L F(p) ζ'/ζ(1/2 + p)`. -/
theorem alias_mul_laplace_shift_eq_of_decay {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hρ : 1 / 2 < ρ.re) (him : 0 < ρ.im) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hint : Integrable fun u => F u ^ 2 * Real.exp (-((17 - 2 * ρ.re - η) * u))) :
    riemannZeta (1 / 2 + (ρ - 1 / 2 + (η : ℂ))) ≠ 0 ∧
      (criticalAliasCoefficient W₀ : ℂ) *
          negativeHalfLineLaplace (cx F) (ρ - 1 / 2 + (η : ℂ) - 8) =
        -stateRegularPart F (ρ - 1 / 2 + (η : ℂ)) -
          negativeHalfLineLaplace (cx F) (ρ - 1 / 2 + (η : ℂ)) *
            (deriv riemannZeta (1 / 2 + (ρ - 1 / 2 + (η : ℂ))) /
              riemannZeta (1 / 2 + (ρ - 1 / 2 + (η : ℂ)))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hρ1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ
  have hpre : (ρ - 1 / 2 + (η : ℂ)).re = ρ.re - 1 / 2 + η := by simp
  have hpim : (ρ - 1 / 2 + (η : ℂ)).im = ρ.im := by simp
  have hLap := differentiableOn_laplace_of_sq hd.meas hd.support hint
  have hmem : ρ - 1 / 2 + (η : ℂ) ∈ clearedRegion (-((17 - 2 * ρ.re - η) / 2)) := by
    refine ⟨show max 0 (8 + -((17 - 2 * ρ.re - η) / 2)) < (ρ - 1 / 2 + (η : ℂ)).re from ?_,
      show 0 < (ρ - 1 / 2 + (η : ℂ)).im from ?_⟩
    · rw [hpre, max_lt_iff]
      constructor <;> linarith
    · rw [hpim]
      exact him
  have hne : riemannZeta (1 / 2 + (ρ - 1 / 2 + (η : ℂ))) ≠ 0 := by
    intro hz
    have hre : (1 / 2 + (ρ - 1 / 2 + (η : ℂ))).re = ρ.re + η := by
      simp
      ring
    exact criticalState_not_integrable_of_zero hW hthreshold hF hz (by rw [hre]; linarith)
      (by rw [hre]; linarith) hint
  refine ⟨hne, ?_⟩
  have h1 : stateEquationCleared W₀ F (ρ - 1 / 2 + (η : ℂ)) = 0 :=
    stateEquationCleared_eqOn_zero hW hthreshold hF (by linarith) hLap hmem
  have key : (criticalAliasCoefficient W₀ : ℂ) *
        negativeHalfLineLaplace (cx F) (ρ - 1 / 2 + (η : ℂ) - 8) +
      stateRegularPart F (ρ - 1 / 2 + (η : ℂ)) =
      -(negativeHalfLineLaplace (cx F) (ρ - 1 / 2 + (η : ℂ)) *
        deriv riemannZeta (1 / 2 + (ρ - 1 / 2 + (η : ℂ)))) /
          riemannZeta (1 / 2 + (ρ - 1 / 2 + (η : ℂ))) := by
    rw [eq_div_iff hne]
    unfold stateEquationCleared at h1
    unfold stateRegularPart
    linear_combination h1
  linear_combination key

/-! ### The pole of the moments -/

/-- **The moments of the state have a pole at the exponent of every zero.** Let `ρ` be a zero of
`ζ` in the upper half-plane right of the critical line, of multiplicity `m`. For every
`c < (m |L F(ρ - 1/2)| / a)²` and all small `η > 0`, a finite moment satisfies
`c ≤ η ∫ F² e^{-(17 - 2 Re ρ - η)u} du`. -/
theorem criticalState_eventually_le_mul_moment_of_zero {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hρ : 1 / 2 < ρ.re) (him : 0 < ρ.im) {c : ℝ}
    (hc : c < (((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
      ‖negativeHalfLineLaplace (cx F) (ρ - 1 / 2)‖ / criticalAliasCoefficient W₀) ^ 2) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (Integrable fun u => F u ^ 2 * Real.exp (-((17 - 2 * ρ.re - η) * u))) →
        c ≤ η * ∫ u, F u ^ 2 * Real.exp (-((17 - 2 * ρ.re - η) * u)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at him
    simp at him
  have hz0re : 0 < (ρ - 1 / 2 : ℂ).re := by
    simp
    linarith
  have hz0im : 0 < (ρ - 1 / 2 : ℂ).im := by simpa using him
  -- the right side of the equation, multiplied by `p - z₀`
  have hLc : ContinuousAt (negativeHalfLineLaplace (cx F)) (ρ - 1 / 2) :=
    ((differentiableOn_laplace_of_sq hd.meas hd.support hd.exponential).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show -((8 : ℝ) / 2) < (ρ - 1 / 2 : ℂ).re by linarith))).continuousAt
  have hsub : Tendsto (fun p : ℂ => p - (ρ - 1 / 2)) (𝓝 (ρ - 1 / 2)) (𝓝 0) := by
    have h : Tendsto (fun p : ℂ => p - (ρ - 1 / 2)) (𝓝 (ρ - 1 / 2))
        (𝓝 ((ρ - 1 / 2) - (ρ - 1 / 2))) := (continuous_id.sub continuous_const).tendsto _
    rwa [sub_self] at h
  have hreg : Tendsto (fun p : ℂ => (p - (ρ - 1 / 2)) * stateRegularPart F p)
      (𝓝[≠] (ρ - 1 / 2)) (𝓝 0) := by
    have h := hsub.mul (continuousAt_stateRegularPart hd hz0re hz0im).tendsto
    rw [zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hΨ : Tendsto (fun p : ℂ => -((p - (ρ - 1 / 2)) * stateRegularPart F p) -
        negativeHalfLineLaplace (cx F) p * ((p - (ρ - 1 / 2)) *
          (deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p)))) (𝓝[≠] (ρ - 1 / 2))
      (𝓝 (-0 - negativeHalfLineLaplace (cx F) (ρ - 1 / 2) *
        (((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ))) :=
    hreg.neg.sub ((hLc.tendsto.mono_left nhdsWithin_le_nhds).mul
      (tendsto_sub_mul_logDeriv_zeta_centred hζ hρ1))
  have hray : Tendsto (fun η : ℝ => ρ - 1 / 2 + (η : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (ρ - 1 / 2)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun η : ℝ => ρ - 1 / 2 + (η : ℂ)) (𝓝 (0 : ℝ))
          (𝓝 (ρ - 1 / 2 + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      rw [Complex.ofReal_zero, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη h
      rw [Set.mem_singleton_iff, add_eq_left, Complex.ofReal_eq_zero] at h
      exact (ne_of_gt hη) h
  have hN := ((hΨ.comp hray).norm).pow 2
  have hlim : c * criticalAliasCoefficient W₀ ^ 2 <
      ‖-0 - negativeHalfLineLaplace (cx F) (ρ - 1 / 2) *
        (((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ)‖ ^ 2 := by
    have h := mul_lt_mul_of_pos_right hc (pow_pos ha 2)
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 ha.ne')] at h
    rw [neg_zero, zero_sub, norm_neg, norm_mul, Complex.norm_natCast,
      mul_comm ‖negativeHalfLineLaplace (cx F) (ρ - 1 / 2)‖]
    exact h
  filter_upwards [hN.eventually_const_lt hlim, Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with η hη hη01 hint
  have hη0 : 0 < η := hη01.1
  obtain ⟨-, heq⟩ := alias_mul_laplace_shift_eq_of_decay hW hthreshold hF hζ hρ him hη0
    hη01.2 hint
  have hwre : (ρ - 1 / 2 + (η : ℂ) - 8).re = ρ.re - 1 / 2 + η - 8 := by simp
  have hCS := mul_norm_sq_laplace_le_of_decay hd.meas hd.support hint
    (w := ρ - 1 / 2 + (η : ℂ) - 8) (by rw [hwre]; linarith)
  rw [hwre, show 2 * (ρ.re - 1 / 2 + η - 8) + (17 - 2 * ρ.re - η) = η by ring] at hCS
  have hval : ‖(-((ρ - 1 / 2 + (η : ℂ) - (ρ - 1 / 2)) * stateRegularPart F (ρ - 1 / 2 + (η : ℂ))) -
        negativeHalfLineLaplace (cx F) (ρ - 1 / 2 + (η : ℂ)) *
          ((ρ - 1 / 2 + (η : ℂ) - (ρ - 1 / 2)) *
            (deriv riemannZeta (1 / 2 + (ρ - 1 / 2 + (η : ℂ))) /
              riemannZeta (1 / 2 + (ρ - 1 / 2 + (η : ℂ))))))‖ ^ 2 =
      criticalAliasCoefficient W₀ ^ 2 * (η * (η *
        ‖negativeHalfLineLaplace (cx F) (ρ - 1 / 2 + (η : ℂ) - 8)‖ ^ 2)) := by
    rw [show (-((ρ - 1 / 2 + (η : ℂ) - (ρ - 1 / 2)) * stateRegularPart F (ρ - 1 / 2 + (η : ℂ))) -
        negativeHalfLineLaplace (cx F) (ρ - 1 / 2 + (η : ℂ)) *
          ((ρ - 1 / 2 + (η : ℂ) - (ρ - 1 / 2)) *
            (deriv riemannZeta (1 / 2 + (ρ - 1 / 2 + (η : ℂ))) /
              riemannZeta (1 / 2 + (ρ - 1 / 2 + (η : ℂ)))))) =
        (η : ℂ) * ((criticalAliasCoefficient W₀ : ℂ) *
          negativeHalfLineLaplace (cx F) (ρ - 1 / 2 + (η : ℂ) - 8)) by
      rw [heq]
      ring,
      norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hη0.le,
      Real.norm_of_nonneg ha.le]
    ring
  have hη' : c * criticalAliasCoefficient W₀ ^ 2 <
      criticalAliasCoefficient W₀ ^ 2 * (η * (η *
        ‖negativeHalfLineLaplace (cx F) (ρ - 1 / 2 + (η : ℂ) - 8)‖ ^ 2)) := by
    rw [← hval]
    exact hη
  have hle : criticalAliasCoefficient W₀ ^ 2 * (η * (η *
        ‖negativeHalfLineLaplace (cx F) (ρ - 1 / 2 + (η : ℂ) - 8)‖ ^ 2)) ≤
      criticalAliasCoefficient W₀ ^ 2 *
        (η * ∫ u, F u ^ 2 * Real.exp (-((17 - 2 * ρ.re - η) * u))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCS hη0.le) (sq_nonneg _)
  have hfin := lt_of_lt_of_le hη' hle
  rw [mul_comm c] at hfin
  exact (lt_of_mul_lt_mul_left hfin (sq_nonneg _)).le

/-- **The moment at the exponent of a zero is infinite.** For every zero `ρ` of `ζ` right of the
critical line, `∫ F² e^{-(17 - 2 Re ρ)u} du = ∞`. -/
theorem criticalState_not_integrable_at_zero_exponent {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hρ : 1 / 2 < ρ.re) :
    ¬ Integrable fun u => F u ^ 2 * Real.exp (-((17 - 2 * ρ.re) * u)) := by
  intro hint
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hρlt : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ
  have him : ρ.im ≠ 0 :=
    LiouvilleHyperbolaCutoffOscillation.im_ne_zero_of_zero_mem_strip hζ (by linarith)
  -- move to the upper half-plane by conjugation
  obtain ⟨σ, hσζ, hσre, hσim⟩ : ∃ σ : ℂ, riemannZeta σ = 0 ∧ σ.re = ρ.re ∧ 0 < σ.im := by
    rcases lt_or_gt_of_ne him with h | h
    · refine ⟨conj ρ, ?_, by simp, by simp; linarith⟩
      rw [_root_.riemannZeta_conj, hζ, map_zero]
    · exact ⟨ρ, hζ, rfl, h⟩
  rw [← hσre] at hint hρ
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h] at hσim
    simp at hσim
  have hL0 : negativeHalfLineLaplace (cx F) (σ - 1 / 2) ≠ 0 :=
    criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF
      (by simp only [Complex.sub_re]; norm_num; linarith)
  have hm : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta σ).toNat : ℝ) := by
    exact_mod_cast _root_.RHTower.one_le_toNat_analyticOrderAt_riemannZeta hσ1 hσζ
  have hpos : 0 < (((analyticOrderAt riemannZeta σ).toNat : ℝ) *
      ‖negativeHalfLineLaplace (cx F) (σ - 1 / 2)‖ / criticalAliasCoefficient W₀) ^ 2 :=
    pow_pos (div_pos (mul_pos (by linarith) (norm_pos_iff.mpr hL0)) ha) 2
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (((analyticOrderAt riemannZeta σ).toNat : ℝ) *
      ‖negativeHalfLineLaplace (cx F) (σ - 1 / 2)‖ / criticalAliasCoefficient W₀) ^ 2 / 2 :=
    ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∫ u, F u ^ 2 * Real.exp (-((17 - 2 * σ.re) * u)) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hev := criticalState_eventually_le_mul_moment_of_zero hW hthreshold hF hσζ hρ hσim
    (c := c) (by rw [hcdef]; linarith)
  have hsmall : Ioo (0 : ℝ) (c / (M + 1)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  obtain ⟨η, hη, hη2⟩ := (hev.and hsmall).exists
  have hη0 : 0 < η := hη2.1
  have hintη := integrable_sq_mul_exp_of_le hd.meas hd.support hint
    (b' := 17 - 2 * σ.re - η) (by linarith)
  have hmono : (∫ u, F u ^ 2 * Real.exp (-((17 - 2 * σ.re - η) * u))) ≤ M := by
    rw [hMdef]
    refine integral_mono hintη hint fun u => ?_
    rcases le_or_gt 0 u with hu | hu
    · show F u ^ 2 * Real.exp (-((17 - 2 * σ.re - η) * u)) ≤
        F u ^ 2 * Real.exp (-((17 - 2 * σ.re) * u))
      rw [hd.support u hu]
      simp
    · have hprod := mul_neg_of_pos_of_neg hη0 hu
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg _)
  have h1 := hη hintη
  have h2 : η * M < c := by
    have h3 : η * (M + 1) < c := (lt_div_iff₀ (by linarith)).mp hη2.2
    linarith
  have h4 := mul_le_mul_of_nonneg_left hmono hη0.le
  linarith

/-- **The ruler is strict.** If `∫ F² e^{-bu} du < ∞` for the critical state, every zero of `ζ`
right of the critical line satisfies `Re ρ < (17 - b)/2`. -/
theorem zero_re_lt_of_integrable_sq_mul_exp {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {b : ℝ}
    (hint : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (hρ : 1 / 2 < ρ.re) : ρ.re < (17 - b) / 2 := by
  by_contra h
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  exact criticalState_not_integrable_at_zero_exponent hW hthreshold hF hζ hρ
    (integrable_sq_mul_exp_of_le hd.meas hd.support hint (by linarith [not_lt.mp h]))

/-- **When the abscissa of the zeros is attained, the finite moments are exactly those below the
decay rate**: if some zero has `Re ρ = Θ`, then `∫ F² e^{-bu} du < ∞` iff `b < 17 - 2Θ`. -/
theorem integrable_sq_mul_exp_iff_of_attained {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hΘ : ρ.re = zetaZeroAbscissa) (b : ℝ) :
    (Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) ↔ b < 17 - 2 * zetaZeroAbscissa := by
  obtain ⟨ρ₀, hζ₀, hρ₀⟩ := exists_riemannZeta_zero_right_of_threshold hthreshold
  have hρ : 1 / 2 < ρ.re := by
    rw [hΘ]
    exact lt_of_lt_of_le hρ₀ (re_le_zetaZeroAbscissa hζ₀)
  refine ⟨fun hint => ?_, fun hb => integrable_sq_mul_exp_of_lt_decayRate hW hthreshold hF hb⟩
  have h := zero_re_lt_of_integrable_sq_mul_exp hW hthreshold hF hint hζ hρ
  rw [hΘ] at h
  linarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
