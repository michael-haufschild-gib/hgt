import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateDecaysPastTheBarrierAtTheRateOfTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLevyHeadResolvesTheWallCharges

/-!
# The state equation holds on the zero-free part of the strip

The transform `L F` of the critical state continues from `Re w > -4` through the state equation
`a L F(p - 8) + R F(p) = 0`. Where the state decays, `∫ F² e^{-bu} < ∞`, the transform itself is
holomorphic on `Re w > -b/2`, so the two agree on the part of that half-plane free of the points
`ρ - 17/2`: there the state equation is an identity between honest transforms.

On the strip `κ < Re p < 1/2` to the right of the centred zeros the equation takes the form

`L F(p) · A(p) = -a L F(p - 8) - J G(p - 2) + T F(p) - L F(-1/2)/(p + 1/2)`,

with the multiplier `A(p) = 2θ'(0) + g(p) + N(1/2 + p) - 1/(p - 1/2)` (Gamma symbol, regular part
of `ζ'/ζ`, pole), `G = e^{2u} F` and `T` the prime tail. The first mode of the head term `J F`
is the half-charge `L F(1/2)/(1/2 - p)`; it cancels the pole of the difference quotient, and the
remaining modes are the head term of `e^{2u} F` at `p - 2`, a Hardy function of `Re p < 2`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The continuation is the transform wherever the state decays -/

/-- `ζ(1/2 + p) ≠ 0` to the right of the centred zeros. -/
theorem riemannZeta_half_add_ne_zero_of_right_of_zeros {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {p : ℂ} (hp : κ < p.re) :
    riemannZeta (1 / 2 + p) ≠ 0 := by
  rcases eq_or_ne ((1 : ℂ) / 2 + p) 1 with h1 | h1
  · rw [h1]
    exact riemannZeta_one_ne_zero
  · have h := zetaResidueUnit_ne_zero_of_right_of_zeros hκ hzero (s := 1 / 2 + p)
      (by rw [re_one_half_add]; linarith)
    rw [zetaResidueUnit_of_ne h1] at h
    exact right_ne_zero_of_mul h

/-- **The continuation is the transform wherever the state decays.** If `∫ F² e^{-bu} < ∞` and
every centred zero has `Re z ≤ κ`, then on `Re w > max(κ - 8, -b/2)` the continuation through the
state equation is the Laplace transform of the state: both are holomorphic there and agree on
`Re w > -4`. -/
theorem levyContinuation_eq_laplace_of_decay {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {b : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) {w : ℂ}
    (hw1 : κ - 8 < w.re) (hw2 : -(b / 2) < w.re) :
    levyContinuation W₀ F w = negativeHalfLineLaplace (cx F) w := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max (κ - 8) (-(b / 2)) := ⟨_, rfl⟩
  have hm1 : κ - 8 ≤ m := by
    rw [hm]
    exact le_max_left _ _
  have hm2 : -(b / 2) ≤ m := by
    rw [hm]
    exact le_max_right _ _
  have hmw : m < w.re := by
    rw [hm]
    exact max_lt hw1 hw2
  have hUo : IsOpen {z : ℂ | m < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (levyContinuation W₀ F) {z : ℂ | m < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz => by
      have hz' : m < z.re := hz
      have h8 : (z + 8).re = z.re + 8 := by simp
      refine (differentiableAt_levyContinuation hd (by linarith) ?_).differentiableWithinAt
      rw [show z + 17 / 2 = 1 / 2 + (z + 8) by ring]
      exact riemannZeta_half_add_ne_zero_of_right_of_zeros hκ hzero (by rw [h8]; linarith)) hUo
  have hg : AnalyticOnNhd ℂ (negativeHalfLineLaplace (cx F)) {z : ℂ | m < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz => by
      have hz' : m < z.re := hz
      exact (differentiableAt_laplace_of_sq hd hb (by linarith)).differentiableWithinAt) hUo
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ = max m (-4) + 1 := ⟨_, rfl⟩
  have hx1 : m < x₀ := by
    rw [hx₀]
    linarith [le_max_left m (-4)]
  have hx2 : -4 < x₀ := by
    rw [hx₀]
    linarith [le_max_right m (-4)]
  have hev : levyContinuation W₀ F =ᶠ[𝓝 (x₀ : ℂ)] negativeHalfLineLaplace (cx F) := by
    have hO : IsOpen {z : ℂ | -4 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hO.mem_nhds (show (x₀ : ℂ) ∈ {z : ℂ | -4 < z.re} by simpa using hx2)]
      with z hz
    exact levyContinuation_eq_laplace hW hthreshold hF hz
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg
    (convex_halfSpace_re_gt m).isPreconnected
    (show (x₀ : ℂ) ∈ {z : ℂ | m < z.re} by simpa using hx1) hev hmw

/-! ### The head term sheds its first mode -/

/-- The damped copy `e^{σu} F` shifts the transform. -/
theorem laplace_exp_min_mul {F : ℝ → ℝ} (hsupp : ∀ u, 0 ≤ u → F u = 0) (σ : ℝ) (z : ℂ) :
    negativeHalfLineLaplace (cx fun u => Real.exp (σ * min u 0) * F u) z =
      negativeHalfLineLaplace (cx F) (z + (σ : ℂ)) := by
  show (∫ u : ℝ, cexp (z * (u : ℂ)) * cx (fun u => Real.exp (σ * min u 0) * F u) u) =
    ∫ u : ℝ, cexp ((z + (σ : ℂ)) * (u : ℂ)) * cx F u
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show cexp (z * (u : ℂ)) * ((Real.exp (σ * min u 0) * F u : ℝ) : ℂ) =
    cexp ((z + (σ : ℂ)) * (u : ℂ)) * ((F u : ℝ) : ℂ)
  rcases le_or_gt 0 u with hu | hu
  · rw [hsupp u hu]
    simp
  · rw [min_eq_left hu.le, Complex.ofReal_mul, Complex.ofReal_exp, add_mul, Complex.exp_add]
    push_cast
    ring

/-- **The head term sheds its first mode.** For `Re p < 1/2` the head term is the half-charge
`L F(1/2)/(1/2 - p)` plus the head term of `e^{2u} F` at `p - 2`: the resolvent sum over the
archimedean frequencies `2k + 1/2` loses its first term and is reindexed. -/
theorem levyHeadTerm_eq_half_charge_add_shift {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : p.re < 1 / 2) :
    levyHeadTerm F p = negativeHalfLineLaplace (cx F) (1 / 2) / (1 / 2 - p) +
      levyHeadTerm (fun u => Real.exp (2 * min u 0) * F u) (p - 2) := by
  have hG := criticalHalfLineEnergyDomain_exp_min_mul hF (σ := 2) (by norm_num)
  have h1 := hasSum_levyHead_resolvents hF hp
  have hp2 : (p - 2).re < 1 / 2 := by
    have h : (p - 2).re = p.re - 2 := by simp
    rw [h]
    linarith
  have h2 := hasSum_levyHead_resolvents hG hp2
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℂ, f = fun k : ℕ =>
      negativeHalfLineLaplace (cx F) (2*k+1/2) / ((2*k+1/2 : ℂ)-p) := ⟨_, rfl⟩
  have h1' : HasSum f (levyHeadTerm F p) := by
    rw [hf]
    exact h1
  have h3 : HasSum (fun k : ℕ => f (k + 1))
      (levyHeadTerm (fun u => Real.exp (2 * min u 0) * F u) (p - 2)) := by
    have e : (fun k : ℕ => f (k + 1)) = fun k : ℕ =>
        negativeHalfLineLaplace (cx fun u => Real.exp (2 * min u 0) * F u) (2*k+1/2) /
          ((2*k+1/2 : ℂ)-(p - 2)) := by
      funext k
      simp only [hf]
      rw [laplace_exp_min_mul hF.support,
        show (2 * (k : ℂ) + 1 / 2 + ((2 : ℝ) : ℂ)) = 2 * ((k + 1 : ℕ) : ℂ) + 1 / 2 by
          push_cast
          ring,
        show (2 * (k : ℂ) + 1 / 2 - (p - 2)) = 2 * ((k + 1 : ℕ) : ℂ) + 1 / 2 - p by
          push_cast
          ring]
    rw [e]
    exact h2
  have h5 := h1'.unique ((hasSum_nat_add_iff 1).mp h3)
  rw [h5]
  simp only [hf, Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add]
  ring

/-! ### The state equation on the strip -/

/-- The multiplier of the state on the strip: the Gamma symbol, the regular part of `ζ'/ζ` and
the pole of the difference quotient. -/
def stripMultiplier (p : ℂ) : ℂ :=
  2 * (gammaHardyPhaseRate 0 : ℂ) + levySymbol p + zetaRegularLogDeriv (1 / 2 + p) -
    (p - 1 / 2)⁻¹

theorem logDeriv_zetaEntire_half_add_eq {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {p : ℂ} (hp1 : κ < p.re)
    (hp2 : p.re < 1 / 2) :
    logDeriv zetaEntire (1 / 2 + p) = zetaRegularLogDeriv (1 / 2 + p) := by
  have hs : (1 : ℂ) / 2 + p ≠ 1 := fun h => by
    have h' := congrArg Complex.re h
    rw [re_one_half_add, Complex.one_re] at h'
    linarith
  have hζ := riemannZeta_half_add_ne_zero_of_right_of_zeros hκ hzero hp1
  have hG := zetaResidueUnit_ne_zero_of_right_of_zeros hκ hzero (s := 1 / 2 + p)
    (by rw [re_one_half_add]; linarith)
  rw [logDeriv_zetaEntire_add hs hζ, zetaRegularLogDeriv_eq hs hG, logDeriv_apply,
    show (1 : ℂ) / 2 + p - 1 = p - 1 / 2 by ring]
  ring

/-- **The state equation on the zero-free part of the strip.** If every centred zero has
`Re z ≤ κ` and `∫ F² e^{-bu} < ∞`, then for `κ < Re p < 1/2` with `16 - b < 2 Re p`,
`L F(p) A(p) = -a L F(p - 8) - J G(p - 2) + T F(p) - L F(-1/2)/(p + 1/2)`, `G = e^{2u} F`. -/
theorem laplace_mul_stripMultiplier_eq {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {b : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) {p : ℂ} (hp1 : κ < p.re)
    (hp2 : p.re < 1 / 2) (hpb : 16 - b < 2 * p.re) :
    negativeHalfLineLaplace (cx F) p * stripMultiplier p =
      -((criticalAliasCoefficient W₀ : ℂ) * negativeHalfLineLaplace (cx F) (p - 8)) -
        levyHeadTerm (fun u => Real.exp (2 * min u 0) * F u) (p - 2) + stateTail F p -
        negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h8 : (p - 8).re = p.re - 8 := by simp
  have hcont := levyContinuation_eq_laplace_of_decay hκ hzero hW hthreshold hF hb (w := p - 8)
    (by rw [h8]; linarith) (by rw [h8]; linarith)
  have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive hW).ne'
  unfold levyContinuation at hcont
  rw [sub_add_cancel, div_eq_iff ha] at hcont
  have hstrip : |p.re| < 1 / 2 := abs_lt.mpr ⟨by linarith, hp2⟩
  have hp12 : p ≠ 1 / 2 := fun h => by
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hΓ := levyGamma_eq_symbol_add_head hd hstrip
  have hN := logDeriv_zetaEntire_half_add_eq hκ hzero hp1 hp2
  have hds : dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p =
      negativeHalfLineLaplace (cx F) p * (p - 1 / 2)⁻¹ -
        negativeHalfLineLaplace (cx F) (1 / 2) * (p - 1 / 2)⁻¹ := by
    rw [dslope_of_ne _ hp12, slope_def_field, div_eq_mul_inv, sub_mul]
  have hJ := levyHeadTerm_eq_half_charge_add_shift hd hp2
  have hJ' : negativeHalfLineLaplace (cx F) (1 / 2) / (1 / 2 - p) =
      -(negativeHalfLineLaplace (cx F) (1 / 2) * (p - 1 / 2)⁻¹) := by
    rw [show (1 : ℂ) / 2 - p = -(p - 1 / 2) by ring, div_neg, div_eq_mul_inv]
  unfold levyRemainder at hcont
  rw [hΓ, hN, hds, hJ, hJ'] at hcont
  unfold stripMultiplier
  linear_combination -hcont

end GaloisForLFunctions.ExclusionOfTheCriticalState
