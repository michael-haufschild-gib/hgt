import GaloisForLFunctions.ExclusionOfTheCriticalState.TheGammaPairingInLevyForm
import GaloisForLFunctions.RHTower.ZetaMultipleLandauZeroFree

/-!
# The state continues across the critical line

The state equation continues the transform `L F` of the critical state by `L F(w) = -R(w + 8)/a`.
With the Gamma pairing in Lévy form (holomorphic on `Re p > -½`) and the prime tail bounded by the
confinement mass (holomorphic on `Re p > -4`), the remainder `R` is holomorphic on `Re p > -½` off
the zeros of `ζ(½ + p)`. Hence `L F` continues to `Re w > -17/2`, the image of the whole critical
strip, and at every zero `ρ` with `Re ρ > 0` the continuation has residue

  `-m_ρ · L F(ρ - ½) / a` at `ρ - 17/2`.

For `Re ρ ≥ ½` this residue is nonzero (the transform of the state has no zero on `Re w ≥ 0`): every
zero on the critical line is a pole of the state on the line `Re w = -8`. A zero left of the line is
a pole exactly when the transform of the state does not vanish at `ρ - ½`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The prime tail on `Re p > -4` -/

/-- Confinement bounds the weighted tail mass: for `σ > -4`,
`∫_{u<-L} |F| e^{σ(u+L)} ≤ e^{-4L} (W₈ + 1/(2σ+8))/2`. -/
theorem setIntegral_abs_mul_exp_le_confinement {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {σ : ℝ} (hσ : -4 < σ) (L : ℝ) :
    (∫ u in Iio (-L), |F u| * Real.exp (σ * (u + L))) ≤
      Real.exp (-(4 * L)) * ((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / (2 * σ + 8)) / 2 := by
  have hW := hF.exponential
  have hk : 0 < 2 * σ + 8 := by linarith
  have hE : IntegrableOn (fun u : ℝ => Real.exp ((4 + 2 * σ) * L) * Real.exp ((2 * σ + 8) * u))
      (Iio (-L)) :=
    ((integrableOn_exp_mul_Iic hk (-L)).mono_set Iio_subset_Iic_self).const_mul _
  -- AM-GM: `|F| e^{σ(u+L)} = XY ≤ (X² + Y²)/2` with `X² = e^{-4L} F² e^{-8u}`
  have hpt : ∀ u ∈ Iio (-L), |F u| * Real.exp (σ * (u + L)) ≤
      (Real.exp (-(4 * L)) * (F u ^ 2 * Real.exp (-(8 * u))) +
        Real.exp ((4 + 2 * σ) * L) * Real.exp ((2 * σ + 8) * u)) / 2 := by
    intro u _
    set X := Real.exp (-(2 * L)) * |F u| * Real.exp (-(4 * u))
    set Y := Real.exp (2 * L) * Real.exp (4 * u) * Real.exp (σ * (u + L))
    have hXY : |F u| * Real.exp (σ * (u + L)) = X * Y := by
      simp only [X, Y]
      have h1 : Real.exp (-(2 * L)) * Real.exp (2 * L) *
          (Real.exp (-(4 * u)) * Real.exp (4 * u)) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; simp
      calc |F u| * Real.exp (σ * (u + L)) = |F u| * Real.exp (σ * (u + L)) *
            (Real.exp (-(2 * L)) * Real.exp (2 * L) * (Real.exp (-(4 * u)) * Real.exp (4 * u))) := by
            rw [h1, mul_one]
        _ = _ := by ring
    have hX2 : Real.exp (-(4 * L)) * (F u ^ 2 * Real.exp (-(8 * u))) = X ^ 2 := by
      simp only [X, mul_pow, sq_abs, ← Real.exp_nat_mul]; ring_nf
    have hY2 : Real.exp ((4 + 2 * σ) * L) * Real.exp ((2 * σ + 8) * u) = Y ^ 2 := by
      simp only [Y, sq, ← Real.exp_add]; congr 1; ring
    rw [hXY, hX2, hY2]
    nlinarith [sq_nonneg (X - Y)]
  have hint : IntegrableOn (fun u => (Real.exp (-(4 * L)) * (F u ^ 2 * Real.exp (-(8 * u))) +
      Real.exp ((4 + 2 * σ) * L) * Real.exp ((2 * σ + 8) * u)) / 2) (Iio (-L)) :=
    ((hW.integrableOn.const_mul _).add hE).div_const 2
  have habs : IntegrableOn (fun u => |F u| * Real.exp (σ * (u + L))) (Iio (-L)) := by
    refine ((integrable_abs_mul_exp_of_domain hF hσ).const_mul
      (Real.exp (σ * L))).integrableOn.congr_fun (fun u _ => ?_) measurableSet_Iio
    simp only; rw [mul_add, Real.exp_add]; ring
  calc (∫ u in Iio (-L), |F u| * Real.exp (σ * (u + L)))
      ≤ ∫ u in Iio (-L), (Real.exp (-(4 * L)) * (F u ^ 2 * Real.exp (-(8 * u))) +
          Real.exp ((4 + 2 * σ) * L) * Real.exp ((2 * σ + 8) * u)) / 2 :=
        setIntegral_mono_on habs hint measurableSet_Iio hpt
    _ = (Real.exp (-(4 * L)) * (∫ u in Iio (-L), F u ^ 2 * Real.exp (-(8 * u))) +
          Real.exp ((4 + 2 * σ) * L) * (Real.exp ((2 * σ + 8) * (-L)) / (2 * σ + 8))) / 2 := by
        have hexp : (∫ a in Iio (-L), Real.exp ((2 * σ + 8) * a)) =
            Real.exp ((2 * σ + 8) * (-L)) / (2 * σ + 8) := by
          rw [← integral_Iic_eq_integral_Iio, integral_exp_mul_Iic hk]
        rw [integral_div, integral_add (hW.integrableOn.const_mul _) hE, integral_const_mul,
          integral_const_mul, hexp]
    _ ≤ Real.exp (-(4 * L)) * ((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / (2 * σ + 8)) / 2 := by
        have hle : (∫ u in Iio (-L), F u ^ 2 * Real.exp (-(8 * u))) ≤
            ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
          setIntegral_le_integral hW (Eventually.of_forall fun u => by positivity)
        have he : Real.exp ((4 + 2 * σ) * L) * (Real.exp ((2 * σ + 8) * (-L)) / (2 * σ + 8)) =
            Real.exp (-(4 * L)) * (1 / (2 * σ + 8)) := by
          rw [mul_div_assoc', ← Real.exp_add, mul_one_div]; congr 2; ring
        rw [he]
        have := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-(4 * L))).le
        nlinarith

/-- One term of the prime tail is bounded uniformly on `Re p ≥ σ`, for any `σ > -4`. -/
theorem norm_stateTail_term_le_of {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {σ : ℝ}
    (hσ : -4 < σ) {p : ℂ} (hp : σ ≤ p.re) (n : ℕ) :
    ‖(vonMangoldtAtom n : ℂ) * (cexp (p * Real.log n) *
        ∫ u in Iio (-Real.log n), (F u : ℂ) * cexp (p * u))‖ ≤
      vonMangoldtAtom n * (Real.exp (-(4 * Real.log n)) *
        (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / (2 * σ + 8)) / 2)) := by
  set L := Real.log n with _hLdef
  have hatom : 0 ≤ vonMangoldtAtom n := by
    unfold vonMangoldtAtom; split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  have habs : IntegrableOn (fun u => |F u| * Real.exp (σ * (u + L))) (Iio (-L)) := by
    refine ((integrable_abs_mul_exp_of_domain hF hσ).const_mul
      (Real.exp (σ * L))).integrableOn.congr_fun (fun u _ => ?_) measurableSet_Iio
    simp only; rw [mul_add, Real.exp_add]; ring
  have hint : ‖cexp (p * L) * ∫ u in Iio (-L), (F u : ℂ) * cexp (p * u)‖ ≤
      ∫ u in Iio (-L), |F u| * Real.exp (σ * (u + L)) := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le habs
      ((ae_restrict_iff' measurableSet_Iio).mpr (Eventually.of_forall fun u hu => ?_))
    have hu' : u < -L := hu
    rw [norm_mul, norm_mul, norm_cexp_mul_ofReal, norm_cexp_mul_ofReal, Complex.norm_real,
      Real.norm_eq_abs, mul_left_comm, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hatom]
  exact mul_le_mul_of_nonneg_left
    (hint.trans ((setIntegral_abs_mul_exp_le_confinement hF hσ L).trans_eq (by ring))) hatom

/-- The prime tail is holomorphic on `Re p > σ` for every `σ > -4`. -/
theorem differentiableOn_stateTail_of {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {σ : ℝ}
    (hσ : -4 < σ) : DifferentiableOn ℂ (stateTail F) {p : ℂ | σ < p.re} := by
  have hU : IsOpen {p : ℂ | σ < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsum : Summable fun n : ℕ => vonMangoldtAtom n * (Real.exp (-(4 * Real.log n)) *
      (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / (2 * σ + 8)) / 2)) := by
    have h := (summable_vonMangoldt_div_rpow (σ := 1 / 2 + 4) (by norm_num)).mul_right
      (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / (2 * σ + 8)) / 2)
    refine h.congr fun n => ?_
    rw [← vonMangoldtAtom_mul_exp_eq]
    ring
  refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun n => ?_) hU
    (fun n p hp => norm_stateTail_term_le_of hF hσ (le_of_lt hp) n)
  refine DifferentiableOn.const_mul (DifferentiableOn.mul
    (by fun_prop : Differentiable ℂ fun p : ℂ => cexp (p * Real.log n)).differentiableOn ?_) _
  -- the inner integral is the Lévy tail at jump length `log n`
  refine ((differentiableOn_levyTail hF (Real.log n)).mono fun p hp => ?_).congr fun p _ => ?_
  · show -4 < p.re; have : σ < p.re := hp; linarith
  · unfold levyTail
    exact integral_congr_ae (Eventually.of_forall fun u => mul_comm _ _)

/-- **The prime tail is holomorphic on `Re p > -4`.** -/
theorem differentiableOn_stateTail_strip {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    DifferentiableOn ℂ (stateTail F) {p : ℂ | -4 < p.re} := by
  intro p hp
  have hp' : -4 < p.re := hp
  have hU : IsOpen {q : ℂ | (p.re - 4) / 2 < q.re} := isOpen_lt continuous_const Complex.continuous_re
  exact ((differentiableOn_stateTail_of hF (σ := (p.re - 4) / 2) (by linarith)).differentiableAt
    (hU.mem_nhds (by show (p.re - 4) / 2 < p.re; linarith))).differentiableWithinAt

/-! ### The remainder across the critical line -/

/-- The pole-free remainder with the Gamma pairing in Lévy form. -/
def levyRemainder (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  levyGamma F p + negativeHalfLineLaplace (cx F) p * logDeriv zetaEntire (1 / 2 + p) -
    dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p - stateTail F p +
    negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)

theorem levyRemainder_eq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} (hp : 0 < p.re) :
    levyRemainder F p = stateRemainder F p := by
  unfold levyRemainder stateRemainder
  rw [levyGamma_eq_stateGamma hF hp]

/-- The Lévy remainder splits into a part holomorphic on `Re p > -½` and the Euler part. -/
def levyRegularPart (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  levyGamma F p - dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p - stateTail F p +
    negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)

theorem levyRemainder_eq_add (F : ℝ → ℝ) (p : ℂ) :
    levyRemainder F p = levyRegularPart F p +
      negativeHalfLineLaplace (cx F) p * logDeriv zetaEntire (1 / 2 + p) := by
  unfold levyRemainder levyRegularPart; ring

theorem differentiableAt_levyRegularPart {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -(1 / 2) < p.re) : DifferentiableAt ℂ (levyRegularPart F) p := by
  have hopenH : IsOpen {p : ℂ | -(1 / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hopen4 : IsOpen {p : ℂ | -4 < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hopen4' : IsOpen {p : ℂ | -(8 / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLap := differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
  have hG := (differentiableOn_levyGamma hF).differentiableAt (hopenH.mem_nhds hp)
  have hT := (differentiableOn_stateTail_strip hF).differentiableAt
    (hopen4.mem_nhds (by show -4 < p.re; linarith))
  have hD : DifferentiableAt ℂ (dslope (negativeHalfLineLaplace (cx F)) (1 / 2)) p := by
    have hhalf : {p : ℂ | -(8 / 2) < p.re} ∈ 𝓝 ((1 : ℂ) / 2) :=
      hopen4'.mem_nhds (by show -(8 / 2) < ((1 : ℂ) / 2).re; norm_num)
    exact ((differentiableOn_dslope hhalf).mpr hLap).differentiableAt
      (hopen4'.mem_nhds (by show -(8 / 2) < p.re; linarith))
  have hP : DifferentiableAt ℂ
      (fun p : ℂ => negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)) p :=
    (differentiableAt_const _).div (differentiableAt_id.add_const _)
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)
  exact ((hG.sub hD).sub hT).add hP

/-- **The remainder is holomorphic on `Re p > -½` off the zeros of `ζ(½ + p)`.** -/
theorem differentiableAt_levyRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -(1 / 2) < p.re) (hz : zetaEntire (1 / 2 + p) ≠ 0) :
    DifferentiableAt ℂ (levyRemainder F) p := by
  have hopen4 : IsOpen {p : ℂ | -(8 / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLap := differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
  have hL : DifferentiableAt ℂ (negativeHalfLineLaplace (cx F)) p :=
    hLap.differentiableAt (hopen4.mem_nhds (by show -(8 / 2) < p.re; linarith))
  have hZ : DifferentiableAt ℂ (fun p : ℂ => logDeriv zetaEntire (1 / 2 + p)) p := by
    have hd1 : DifferentiableAt ℂ (fun p : ℂ => deriv zetaEntire (1 / 2 + p)) p :=
      (differentiable_deriv_zetaEntire _).comp p ((differentiableAt_const _).add differentiableAt_id)
    have hd2 : DifferentiableAt ℂ (fun p : ℂ => zetaEntire (1 / 2 + p)) p :=
      (differentiable_zetaEntire _).comp p ((differentiableAt_const _).add differentiableAt_id)
    simp only [logDeriv_apply]
    exact hd1.div hd2 hz
  have h := (differentiableAt_levyRegularPart hF hp).add (hL.mul hZ)
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun q => levyRemainder_eq_add F q)

/-! ### The continuation to `Re w > -17/2` -/

/-- The continuation of the state's transform through the state equation, with the Gamma pairing in
Lévy form. -/
def levyContinuation (W₀ : ℝ) (F : ℝ → ℝ) (w : ℂ) : ℂ :=
  -levyRemainder F (w + 8) / criticalAliasCoefficient W₀

theorem levyContinuation_eq_stateContinuation {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {w : ℂ} (hw : -8 < w.re) :
    levyContinuation W₀ F w = stateContinuation W₀ F w := by
  unfold levyContinuation stateContinuation
  rw [levyRemainder_eq hF (by simp; linarith)]

/-- **Agreement.** On `Re w > -4` the continuation is the transform of the state. -/
theorem levyContinuation_eq_laplace {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ} (hw : -4 < w.re) :
    levyContinuation W₀ F w = negativeHalfLineLaplace (cx F) w :=
  (levyContinuation_eq_stateContinuation (criticalHalfLineEnergyDomain_of_groundState hF)
    (by linarith)).trans (stateContinuation_eq_laplace hW hthreshold hF hw)

/-- **Holomorphy.** On `Re w > -17/2` the continuation is holomorphic wherever `ζ(w + 17/2) ≠ 0`. -/
theorem differentiableAt_levyContinuation {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {w : ℂ} (hw : -(17 / 2) < w.re)
    (hζ : riemannZeta (w + 17 / 2) ≠ 0) : DifferentiableAt ℂ (levyContinuation W₀ F) w := by
  have hz : zetaEntire (1 / 2 + (w + 8)) ≠ 0 := by
    rw [show (1 : ℂ) / 2 + (w + 8) = w + 17 / 2 by ring]
    exact zetaEntire_ne_zero_of_riemannZeta_ne_zero hζ
  have hR := (differentiableAt_levyRemainder hF (p := w + 8) (by simp; linarith) hz).comp w
    (differentiableAt_id.add_const (8 : ℂ))
  exact hR.neg.div_const _

/-- **Residue law across the line.** At `ρ - 17/2`, `ρ` any zero with `Re ρ > 0`, the continuation
has a simple pole with residue `-m_ρ L F(ρ - ½)/a`. -/
theorem tendsto_levyContinuation_residue {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ : 0 < ρ.re) :
    Tendsto (fun w => (w - (ρ - 17 / 2)) * levyContinuation W₀ F w) (𝓝[≠] (ρ - 17 / 2))
      (𝓝 (-(((analyticOrderAt riemannZeta ρ).toNat : ℂ) *
        negativeHalfLineLaplace (cx F) (ρ - 1 / 2)) / criticalAliasCoefficient W₀)) := by
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at hζ; exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hζ
  set z₀ := ρ - 1 / 2 with hz₀
  have hz₀re : -(1 / 2) < z₀.re := by rw [hz₀]; simp; linarith
  -- residue of the logarithmic derivative of `(s-1)ζ(s)` at `ρ`
  have hzE : zetaEntire ρ = 0 := by rw [zetaEntire_eq hρ1, hζ, mul_zero]
  have hord : analyticOrderAt zetaEntire ρ = analyticOrderAt riemannZeta ρ :=
    analyticOrderAt_zetaEntire_of_ne_one hρ1
  have hres := logDeriv_iteratedDeriv_residue_of_zero (differentiable_zetaEntire.analyticAt ρ)
    (by rw [hord]; exact RHTower.analyticOrderAt_riemannZeta_ne_top hρ1) hzE 0
  simp only [zero_add, pow_one, iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, hord] at hres
  have hopen4 : IsOpen {p : ℂ | -(8 / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLap := differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
  have hLc : ContinuousAt (negativeHalfLineLaplace (cx F)) z₀ :=
    (hLap.differentiableAt (hopen4.mem_nhds (by show -(8 / 2) < z₀.re; linarith))).continuousAt
  have hAc : ContinuousAt (levyRegularPart F) z₀ :=
    (differentiableAt_levyRegularPart hF hz₀re).continuousAt
  -- shift to the zero
  have hshift : Tendsto (fun w : ℂ => 1 / 2 + (w + 8)) (𝓝[≠] (ρ - 17 / 2)) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun w : ℂ => 1 / 2 + (w + 8)) (𝓝 (ρ - 17 / 2))
          (𝓝 (1 / 2 + (ρ - 17 / 2 + 8))) :=
        tendsto_const_nhds.add (tendsto_id.add tendsto_const_nhds)
      rw [show (1 : ℂ) / 2 + (ρ - 17 / 2 + 8) = ρ by ring] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw h
      apply hw
      rw [Set.mem_singleton_iff] at h ⊢
      linear_combination h
  have hp8 : Tendsto (fun w : ℂ => w + 8) (𝓝[≠] (ρ - 17 / 2)) (𝓝 z₀) := by
    have h : Tendsto (fun w : ℂ => w + 8) (𝓝 (ρ - 17 / 2)) (𝓝 (ρ - 17 / 2 + 8)) :=
      tendsto_id.add tendsto_const_nhds
    rw [show ρ - 17 / 2 + 8 = z₀ by rw [hz₀]; ring] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlogres : Tendsto (fun w : ℂ => (w - (ρ - 17 / 2)) * logDeriv zetaEntire (1 / 2 + (w + 8)))
      (𝓝[≠] (ρ - 17 / 2)) (𝓝 ((analyticOrderAt riemannZeta ρ).toNat : ℂ)) := by
    refine (hres.comp hshift).congr fun w => ?_
    simp only [Function.comp, logDeriv_apply]
    ring_nf
  have hzero : Tendsto (fun w : ℂ => w - (ρ - 17 / 2)) (𝓝[≠] (ρ - 17 / 2)) (𝓝 0) := by
    have h : Tendsto (fun w : ℂ => w - (ρ - 17 / 2)) (𝓝 (ρ - 17 / 2))
        (𝓝 (ρ - 17 / 2 - (ρ - 17 / 2))) := tendsto_id.sub tendsto_const_nhds
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have htot : Tendsto (fun w : ℂ => (w - (ρ - 17 / 2)) * levyRegularPart F (w + 8) +
      negativeHalfLineLaplace (cx F) (w + 8) *
        ((w - (ρ - 17 / 2)) * logDeriv zetaEntire (1 / 2 + (w + 8)))) (𝓝[≠] (ρ - 17 / 2))
      (𝓝 (0 * levyRegularPart F z₀ + negativeHalfLineLaplace (cx F) z₀ *
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ))) :=
    (hzero.mul (hAc.tendsto.comp hp8)).add ((hLc.tendsto.comp hp8).mul hlogres)
  rw [zero_mul, zero_add] at htot
  have hlim := (htot.div_const (criticalAliasCoefficient W₀ : ℂ)).neg
  have hfun : (fun w : ℂ => (w - (ρ - 17 / 2)) * levyContinuation W₀ F w) = fun w : ℂ =>
      -(((w - (ρ - 17 / 2)) * levyRegularPart F (w + 8) + negativeHalfLineLaplace (cx F) (w + 8) *
        ((w - (ρ - 17 / 2)) * logDeriv zetaEntire (1 / 2 + (w + 8)))) /
          (criticalAliasCoefficient W₀ : ℂ)) := by
    funext w
    unfold levyContinuation
    rw [levyRemainder_eq_add]
    ring
  rw [hfun, show -(((analyticOrderAt riemannZeta ρ).toNat : ℂ) *
      negativeHalfLineLaplace (cx F) (ρ - 1 / 2)) / (criticalAliasCoefficient W₀ : ℂ) =
      -(negativeHalfLineLaplace (cx F) z₀ * ((analyticOrderAt riemannZeta ρ).toNat : ℂ) /
        (criticalAliasCoefficient W₀ : ℂ)) by rw [hz₀]; ring]
  exact hlim

/-- The residue at `ρ - 17/2` vanishes exactly when the transform of the state vanishes at `ρ - ½`. -/
theorem levyResidue_ne_zero_iff {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ} {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) :
    -(((analyticOrderAt riemannZeta ρ).toNat : ℂ) * negativeHalfLineLaplace (cx F) (ρ - 1 / 2)) /
        (criticalAliasCoefficient W₀ : ℂ) ≠ 0 ↔ negativeHalfLineLaplace (cx F) (ρ - 1 / 2) ≠ 0 := by
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at hζ; exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hζ
  have hm : ((analyticOrderAt riemannZeta ρ).toNat : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := one_le_toNat_analyticOrderAt_riemannZeta hρ1 hζ; omega)
  have hα : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  rw [neg_div, neg_ne_zero, div_ne_zero_iff, mul_ne_zero_iff]
  tauto

/-- A function with a nonzero residue at a point is not holomorphic there. -/
theorem not_differentiableAt_of_residue {f : ℂ → ℂ} {w₀ c : ℂ}
    (h : Tendsto (fun w => (w - w₀) * f w) (𝓝[≠] w₀) (𝓝 c)) (hc : c ≠ 0) :
    ¬ DifferentiableAt ℂ f w₀ := by
  intro hdiff
  have h0 : Tendsto (fun w => (w - w₀) * f w) (𝓝[≠] w₀) (𝓝 0) := by
    have h' := (tendsto_id.sub (tendsto_const_nhds (x := w₀))).mul hdiff.continuousAt.tendsto
    simp only [id, sub_self, zero_mul] at h'
    exact h'.mono_left nhdsWithin_le_nhds
  exact hc (tendsto_nhds_unique h h0)

/-- **Every zero on or right of the critical line is a pole of the state.** -/
theorem not_differentiableAt_levyContinuation {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hρ : 1 / 2 ≤ ρ.re) : ¬ DifferentiableAt ℂ (levyContinuation W₀ F) (ρ - 17 / 2) := by
  have hL : negativeHalfLineLaplace (cx F) (ρ - 1 / 2) ≠ 0 :=
    criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF
      (by simp; linarith)
  exact not_differentiableAt_of_residue
    (tendsto_levyContinuation_residue (W₀ := W₀) (criticalHalfLineEnergyDomain_of_groundState hF)
      hζ (by linarith)) ((levyResidue_ne_zero_iff hW hζ).mpr hL)

/-- **Meromorphic continuation across the critical line.** Either RH holds, or the critical state
exists, its transform continues from `Re w > -4` to `Re w > -17/2` holomorphically off the points
`ρ - 17/2`, at each zero with `Re ρ > 0` with residue `-m_ρ L F(ρ - ½)/a`; every zero with
`Re ρ ≥ ½` is a pole, and the line `Re w = -8` carries a pole. -/
theorem riemannHypothesis_or_criticalState_poles_across_line :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧
        (∀ w : ℂ, -4 < w.re → levyContinuation W₀ F w = negativeHalfLineLaplace (cx F) w) ∧
        (∀ w : ℂ, -(17 / 2) < w.re → riemannZeta (w + 17 / 2) ≠ 0 →
          DifferentiableAt ℂ (levyContinuation W₀ F) w) ∧
        (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re →
          Tendsto (fun w => (w - (ρ - 17 / 2)) * levyContinuation W₀ F w) (𝓝[≠] (ρ - 17 / 2))
            (𝓝 (-(((analyticOrderAt riemannZeta ρ).toNat : ℂ) *
              negativeHalfLineLaplace (cx F) (ρ - 1 / 2)) / criticalAliasCoefficient W₀))) ∧
        (∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re →
          ¬ DifferentiableAt ℂ (levyContinuation W₀ F) (ρ - 17 / 2)) ∧
        ∃ w : ℂ, w.re = -8 ∧ ¬ DifferentiableAt ℂ (levyContinuation W₀ F) w := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · have hd := criticalHalfLineEnergyDomain_of_groundState hF
    obtain ⟨s, hs, hζs⟩ := ZetaMultiple.exists_riemannZeta_zero_re_half
    refine Or.inr ⟨W₀, F, hW, ht, hF, fun w hw => levyContinuation_eq_laplace hW ht hF hw,
      fun w hw hz => differentiableAt_levyContinuation hd hw hz,
      fun ρ hζ hρ => tendsto_levyContinuation_residue hd hζ hρ,
      fun ρ hζ hρ => not_differentiableAt_levyContinuation hW ht hF hζ hρ,
      s - 17 / 2, by simp [hs]; norm_num,
      not_differentiableAt_levyContinuation hW ht hF hζs hs.ge⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
