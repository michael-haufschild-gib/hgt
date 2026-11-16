import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateEquationIsHolomorphicInTheProbeExponent
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoBoundaryLaplaceZero
import GaloisForLFunctions.RHTower.XiLogDerivNotHolonomic
import GaloisForLFunctions.RHTower.PrimeShiftResidueClosability
import GaloisForLFunctions.RHTower.SpeiserEventualEquivalence
import GaloisForLFunctions.RHTower.LiouvilleHyperbolaCutoffOscillation

/-!
# The decay of the critical state reads the zeros

If the Laplace transform of the critical state `F` is holomorphic on `Re w > κ` (for instance
`κ = -b/2` when `∫ F² e^{-bu} < ∞`), the holomorphic state equation holds on the half-plane
`Re p > max(0, 8 + κ)` off the real axis, after clearing `ζ(½ + p)`. At a zero `ρ` of `ζ` the cleared equation reads
`L F(ρ - ½) · m_ρ = 0` (`m_ρ` the multiplicity), which is impossible: the transform of the state has no
zero on `Re w ≥ 0`. Hence

  `∫ F² e^{-bu} < ∞  ⟹  Re ρ ≤ (17 - b)/2` for every zero `ρ` with `Re ρ > ½`.

The decay exponent of the state is a ruler for the abscissa of the zeros: proving that the state
decays like `e^{(17/2 - θ)u}` in mean square is proving that `ζ` has no zero on `Re s > θ`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- Real exponents above `4` accumulate at `5` from the punctured neighbourhood. -/
theorem frequently_eq_zero_of_real {E : ℂ → ℂ} (h : ∀ x : ℝ, 4 < x → E x = 0) :
    ∃ᶠ z in 𝓝[≠] (5 : ℂ), E z = 0 := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have ht : Tendsto (fun n : ℕ => ((5 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (5 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h0 := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (5 : ℝ)
      have h1 := (Complex.continuous_ofReal.tendsto _).comp h0
      rw [add_zero, Complex.ofReal_ofNat] at h1
      exact h1
    · intro he
      have he' : ((5 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) = ((5 : ℝ) : ℂ) := by
        rw [he]; norm_num
      have := Complex.ofReal_injective he'
      linarith [hpos n]
  exact ht.frequently (Frequently.of_forall fun n => h _ (by linarith [hpos n]))

theorem differentiableAt_zeta_shift {p : ℂ} (h1 : 1 / 2 + p ≠ 1) :
    DifferentiableAt ℂ (fun p : ℂ => riemannZeta (1 / 2 + p)) p :=
  (HTGeometry.analyticAt_riemannZeta h1).differentiableAt.comp p
    ((differentiableAt_const _).add differentiableAt_id)

theorem differentiableAt_deriv_zeta_shift {p : ℂ} (h1 : 1 / 2 + p ≠ 1) :
    DifferentiableAt ℂ (fun p : ℂ => deriv riemannZeta (1 / 2 + p)) p :=
  (HTGeometry.analyticAt_riemannZeta h1).deriv.differentiableAt.comp p
    ((differentiableAt_const _).add differentiableAt_id)

theorem differentiableAt_polePart (C S : ℝ) {p : ℂ} (h1 : p + 1 / 2 ≠ 0) (h2 : p - 1 / 2 ≠ 0) :
    DifferentiableAt ℂ (fun p : ℂ => (C : ℂ) * (1 / (p + 1 / 2) + 1 / (p - 1 / 2)) -
      (S : ℂ) * (1 / (p + 1 / 2) - 1 / (p - 1 / 2))) p := by
  have d1 : DifferentiableAt ℂ (fun p : ℂ => 1 / (p + 1 / 2)) p :=
    (differentiableAt_const _).div (differentiableAt_id.add_const _) h1
  have d2 : DifferentiableAt ℂ (fun p : ℂ => 1 / (p - 1 / 2)) p :=
    (differentiableAt_const _).div (differentiableAt_id.sub_const _) h2
  exact ((d1.add d2).const_mul _).sub ((d1.sub d2).const_mul _)

/-- The square moment makes the Laplace transform holomorphic at every point of `Re w > -b/2`. -/
theorem differentiableAt_laplace_of_sq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {b : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) {w : ℂ} (hw : -(b / 2) < w.re) :
    DifferentiableAt ℂ (negativeHalfLineLaplace (cx F)) w :=
  (differentiableOn_laplace_of_sq hF.meas hF.support hb).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)

/-- Holomorphy of the transform on `Re w > κ`, at a point. -/
theorem differentiableAt_laplace_of_on {F : ℝ → ℝ} {κ : ℝ}
    (hLap : DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {w : ℂ | κ < w.re}) {w : ℂ}
    (hw : κ < w.re) : DifferentiableAt ℂ (negativeHalfLineLaplace (cx F)) w :=
  hLap.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)

/-- The confinement term `L F(p - 8)` is holomorphic wherever `Re (p - 8) > κ`. -/
theorem differentiableAt_laplace_sub_eight {F : ℝ → ℝ} {κ : ℝ}
    (hLap : DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {w : ℂ | κ < w.re}) {p : ℂ}
    (hp : κ < p.re - 8) :
    DifferentiableAt ℂ (fun p : ℂ => negativeHalfLineLaplace (cx F) (p - 8)) p := by
  have hg := differentiableAt_laplace_of_on hLap (w := p - 8) (by simpa using hp)
  have hf : DifferentiableAt ℂ (fun p : ℂ => p - 8) p := differentiableAt_id.sub_const (8 : ℂ)
  exact DifferentiableAt.comp (g := negativeHalfLineLaplace (cx F)) (f := fun p : ℂ => p - 8) p hg hf

/-- **The state equation holds on the Euler half-plane** `Re p > max 1 (κ + 8)` whenever the transform
is holomorphic on `Re w > κ`, `κ ≤ -4`. -/
theorem stateEquation_eqOn_zero {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {κ : ℝ} (hκ : κ ≤ -4)
    (hLap : DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {w : ℂ | κ < w.re}) :
    EqOn (stateEquation W₀ F) 0 {p : ℂ | max 1 (κ + 8) < p.re} := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hU : IsOpen {p : ℂ | max 1 (κ + 8) < p.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (stateEquation W₀ F) {p : ℂ | max 1 (κ + 8) < p.re} := by
    intro p hp
    have hp1 : max 1 (κ + 8) < p.re := hp
    have hp' : 1 < p.re := lt_of_le_of_lt (le_max_left _ _) hp1
    have hp8 : κ + 8 < p.re := lt_of_le_of_lt (le_max_right _ _) hp1
    have hpos : p ∈ {p : ℂ | 0 < p.re} := show 0 < p.re by linarith
    have hopen0 : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const Complex.continuous_re
    have hL := differentiableAt_laplace_of_on hLap (w := p) (by linarith)
    have hL8 := differentiableAt_laplace_sub_eight hLap (p := p) (by linarith)
    have hG := (differentiableOn_stateGamma hd).differentiableAt (hopen0.mem_nhds hpos)
    have hT := (differentiableOn_stateTail hd).differentiableAt (hopen0.mem_nhds hpos)
    have h1 : 1 / 2 + p ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hζ : riemannZeta (1 / 2 + p) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
    have hZ := (differentiableAt_deriv_zeta_shift h1).div (differentiableAt_zeta_shift h1) hζ
    have hP := differentiableAt_polePart (coshHalfMoment F) (sinhHalfMoment F) (p := p)
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    exact (((((hL8.const_mul _).add hG).add (hL.mul hZ)).sub hT).add hP).differentiableWithinAt
  exact (hdiff.analyticOnNhd hU).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt _).isPreconnected
    (show max 1 (κ + 8) < (5 : ℂ).re by rw [max_lt_iff]; norm_num; linarith)
    (frequently_eq_zero_of_real fun x hx => stateEquation_ofReal_eq_zero hW hthreshold hF hx)

/-- The state equation with the Euler denominator `ζ(½ + p)` cleared. -/
def stateEquationCleared (W₀ : ℝ) (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  riemannZeta (1 / 2 + p) * (criticalAliasCoefficient W₀ * negativeHalfLineLaplace (cx F) (p - 8) +
      stateGamma F p - stateTail F p +
      (coshHalfMoment F * (1 / (p + 1 / 2) + 1 / (p - 1 / 2)) -
        sinhHalfMoment F * (1 / (p + 1 / 2) - 1 / (p - 1 / 2)))) +
    negativeHalfLineLaplace (cx F) p * deriv riemannZeta (1 / 2 + p)

theorem stateEquationCleared_eq_mul {W₀ : ℝ} {F : ℝ → ℝ} {p : ℂ}
    (hζ : riemannZeta (1 / 2 + p) ≠ 0) :
    stateEquationCleared W₀ F p = riemannZeta (1 / 2 + p) * stateEquation W₀ F p := by
  unfold stateEquationCleared stateEquation
  have key : ∀ z L d : ℂ, z ≠ 0 → z * (L * (d / z)) = L * d := fun z L d hz => by
    field_simp
  linear_combination -(key _ (negativeHalfLineLaplace (cx F) p) (deriv riemannZeta (1 / 2 + p)) hζ)

/-- The cleared region for transforms holomorphic on `Re w > κ`: right of `max 0 (8 + κ)` and
strictly above the real axis. -/
def clearedRegion (κ : ℝ) : Set ℂ := {p : ℂ | max 0 (8 + κ) < p.re} ∩ {p : ℂ | 0 < p.im}

theorem isOpen_clearedRegion (κ : ℝ) : IsOpen (clearedRegion κ) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

/-- **The cleared state equation vanishes on the cleared region.** -/
theorem stateEquationCleared_eqOn_zero {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {κ : ℝ} (hκ : κ ≤ -7)
    (hLap : DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {w : ℂ | κ < w.re}) :
    EqOn (stateEquationCleared W₀ F) 0 (clearedRegion κ) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hdiff : DifferentiableOn ℂ (stateEquationCleared W₀ F) (clearedRegion κ) := by
    intro p hp
    obtain ⟨hre, him⟩ := hp
    have hre' : max 0 (8 + κ) < p.re := hre
    have him' : 0 < p.im := him
    have h0 : 0 < p.re := lt_of_le_of_lt (le_max_left _ _) hre'
    have h8 : 8 + κ < p.re := lt_of_le_of_lt (le_max_right _ _) hre'
    have hopen0 : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const Complex.continuous_re
    have hL := differentiableAt_laplace_of_on hLap (w := p) (by linarith)
    have hL8 := differentiableAt_laplace_sub_eight hLap (p := p) (by linarith)
    have hG := (differentiableOn_stateGamma hd).differentiableAt (hopen0.mem_nhds h0)
    have hT := (differentiableOn_stateTail hd).differentiableAt (hopen0.mem_nhds h0)
    have h1 : 1 / 2 + p ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    have hP := differentiableAt_polePart (coshHalfMoment F) (sinhHalfMoment F) (p := p)
      (by intro h; have := congrArg Complex.im h; simp at this; linarith)
      (by intro h; have := congrArg Complex.im h; simp at this; linarith)
    exact ((differentiableAt_zeta_shift h1).mul ((((hL8.const_mul _).add hG).sub hT).add hP)).add
      (hL.mul (differentiableAt_deriv_zeta_shift h1)) |>.differentiableWithinAt
  have hconv : Convex ℝ (clearedRegion κ) :=
    (convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt 0)
  have hmem : (2 + I : ℂ) ∈ clearedRegion κ :=
    ⟨show max 0 (8 + κ) < (2 + I : ℂ).re by
        rw [show (2 + I : ℂ).re = 2 by simp, max_lt_iff]; exact ⟨by norm_num, by linarith⟩,
      show 0 < (2 + I : ℂ).im by simp⟩
  have hev : stateEquationCleared W₀ F =ᶠ[𝓝 (2 + I)] 0 := by
    have hO : IsOpen ({p : ℂ | 1 < p.re} ∩ clearedRegion κ) :=
      (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_clearedRegion κ)
    filter_upwards [hO.mem_nhds ⟨show 1 < (2 + I : ℂ).re by simp, hmem⟩] with p hp
    have hζ : riemannZeta (1 / 2 + p) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp; linarith [show 1 < p.re from hp.1])
    rw [stateEquationCleared_eq_mul hζ,
      stateEquation_eqOn_zero hW hthreshold hF (by linarith) hLap
        (show max 1 (κ + 8) < p.re by rw [max_eq_left (by linarith)]; exact hp.1)]
    simp
  exact (hdiff.analyticOnNhd (isOpen_clearedRegion κ)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hconv.isPreconnected hmem hev

/-- **At a zero of `ζ` in the cleared region the state's transform vanishes.** The cleared equation
gives `L F(p) · (p - z₀) ζ'/ζ(½ + p) = -(p - z₀) A(p)` near `z₀ = ρ - ½`; the left side tends to
`m_ρ L F(z₀)` and the right side to `0`. -/
theorem laplace_eq_zero_of_zeta_zero {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {κ : ℝ} (hκ : κ ≤ -7)
    (hLap : DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {w : ℂ | κ < w.re}) {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (hmem : ρ - 1 / 2 ∈ clearedRegion κ) :
    negativeHalfLineLaplace (cx F) (ρ - 1 / 2) = 0 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  set z₀ := ρ - 1 / 2 with hz₀
  have hρ1 : ρ ≠ 1 := by
    intro h; have := hmem.2; rw [hz₀, h] at this; simp at this
  -- the analytic remainder `A`
  set A : ℂ → ℂ := fun p => criticalAliasCoefficient W₀ * negativeHalfLineLaplace (cx F) (p - 8) +
      stateGamma F p - stateTail F p +
      (coshHalfMoment F * (1 / (p + 1 / 2) + 1 / (p - 1 / 2)) -
        sinhHalfMoment F * (1 / (p + 1 / 2) - 1 / (p - 1 / 2))) with hA
  have hAc : ContinuousAt A z₀ := by
    obtain ⟨hre, him⟩ := hmem
    have hre' : max 0 (8 + κ) < z₀.re := hre
    have h0 : 0 < z₀.re := lt_of_le_of_lt (le_max_left _ _) hre'
    have h8 : 8 + κ < z₀.re := lt_of_le_of_lt (le_max_right _ _) hre'
    have hopen0 : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const Complex.continuous_re
    have hL8 := differentiableAt_laplace_sub_eight hLap (p := z₀) (by linarith)
    have hG := (differentiableOn_stateGamma hd).differentiableAt (hopen0.mem_nhds h0)
    have hT := (differentiableOn_stateTail hd).differentiableAt (hopen0.mem_nhds h0)
    have hP := differentiableAt_polePart (coshHalfMoment F) (sinhHalfMoment F) (p := z₀)
      (by intro h; have := congrArg Complex.im h; simp at this; linarith [show 0 < z₀.im from him])
      (by intro h; have := congrArg Complex.im h; simp at this; linarith [show 0 < z₀.im from him])
    exact ((((hL8.const_mul _).add hG).sub hT).add hP).continuousAt
  have hLc : ContinuousAt (negativeHalfLineLaplace (cx F)) z₀ :=
    (differentiableAt_laplace_of_on hLap (w := z₀) (by
      have := lt_of_le_of_lt (le_max_left _ _) (show max 0 (8 + κ) < z₀.re from hmem.1)
      linarith)).continuousAt
  -- the cleared equation near `z₀`
  have hEq : ∀ᶠ p in 𝓝 z₀, riemannZeta (1 / 2 + p) * A p +
      negativeHalfLineLaplace (cx F) p * deriv riemannZeta (1 / 2 + p) = 0 := by
    filter_upwards [(isOpen_clearedRegion κ).mem_nhds hmem] with p hp
    have := stateEquationCleared_eqOn_zero hW hthreshold hF hκ hLap hp
    simpa [stateEquationCleared, hA] using this
  -- the residue of `ζ'/ζ` at `ρ`
  set m : ℕ := (analyticOrderAt riemannZeta ρ).toNat with hm
  have hm1 : 1 ≤ m := one_le_toNat_analyticOrderAt_riemannZeta hρ1 hζ
  have hres := logDeriv_iteratedDeriv_residue_of_zero (HTGeometry.analyticAt_riemannZeta hρ1)
    (RHTower.analyticOrderAt_riemannZeta_ne_top hρ1) hζ 0
  simp only [zero_add, pow_one, iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one] at hres
  have hshift : Tendsto (fun p : ℂ => 1 / 2 + p) (𝓝[≠] z₀) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun p : ℂ => 1 / 2 + p) (𝓝 z₀) (𝓝 (1 / 2 + z₀)) :=
        tendsto_const_nhds.add tendsto_id
      have e : (1 : ℂ) / 2 + z₀ = ρ := by rw [hz₀]; ring
      rw [e] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with p hp h
      apply hp
      rw [Set.mem_singleton_iff] at h ⊢
      rw [hz₀]
      linear_combination h
  have hR : Tendsto (fun p : ℂ => (p - z₀) * (deriv riemannZeta (1 / 2 + p) /
      riemannZeta (1 / 2 + p))) (𝓝[≠] z₀) (𝓝 (m : ℂ)) := by
    have h := hres.comp hshift
    refine h.congr fun p => ?_
    simp only [Function.comp]
    rw [hz₀]
    ring_nf
  have hlim1 : Tendsto (fun p : ℂ => negativeHalfLineLaplace (cx F) p * ((p - z₀) *
      (deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p)))) (𝓝[≠] z₀)
      (𝓝 (negativeHalfLineLaplace (cx F) z₀ * m)) :=
    (hLc.tendsto.mono_left nhdsWithin_le_nhds).mul hR
  have hlim0 : Tendsto (fun p : ℂ => negativeHalfLineLaplace (cx F) p * ((p - z₀) *
      (deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p)))) (𝓝[≠] z₀) (𝓝 0) := by
    have hbound : Tendsto (fun p : ℂ => ‖p - z₀‖ * ‖A p‖) (𝓝[≠] z₀) (𝓝 0) := by
      have h := (tendsto_norm_sub_self z₀).mul hAc.norm
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [nhdsWithin_le_nhds hEq] with p hp
    by_cases hz : riemannZeta (1 / 2 + p) = 0
    · rw [hz, div_zero, mul_zero, mul_zero, norm_zero]
      positivity
    · have hq : negativeHalfLineLaplace (cx F) p * deriv riemannZeta (1 / 2 + p) /
          riemannZeta (1 / 2 + p) = -A p := by
        rw [div_eq_iff hz]; linear_combination hp
      calc ‖negativeHalfLineLaplace (cx F) p * ((p - z₀) *
            (deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p)))‖
          = ‖(p - z₀) * (negativeHalfLineLaplace (cx F) p * deriv riemannZeta (1 / 2 + p) /
              riemannZeta (1 / 2 + p))‖ := by ring_nf
        _ = ‖p - z₀‖ * ‖A p‖ := by rw [hq, norm_mul, norm_neg]
        _ ≤ ‖p - z₀‖ * ‖A p‖ := le_rfl
  have hprod := tendsto_nhds_unique hlim1 hlim0
  have hmne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_eq_zero.mp hprod).resolve_right hmne

/-- **Holomorphy reads the zeros.** If the transform of the critical state is holomorphic on
`Re w > κ` (`κ ≤ -7`), every zero of `ζ` right of the critical line satisfies `Re ρ ≤ κ + 17/2`. -/
theorem zero_re_le_of_laplace_holomorphic {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {κ : ℝ} (hκ : κ ≤ -7)
    (hLap : DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {w : ℂ | κ < w.re}) {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (hρ : 1 / 2 < ρ.re) : ρ.re ≤ κ + 17 / 2 := by
  by_contra hlt
  have hlt : κ + 17 / 2 < ρ.re := lt_of_not_ge hlt
  have him : ρ.im ≠ 0 :=
    LiouvilleHyperbolaCutoffOscillation.im_ne_zero_of_zero_mem_strip hζ (by linarith)
  -- move to the upper half-plane by conjugation
  obtain ⟨σ, hσζ, hσre, hσim⟩ : ∃ σ : ℂ, riemannZeta σ = 0 ∧ σ.re = ρ.re ∧ 0 < σ.im := by
    rcases lt_or_gt_of_ne him with h | h
    · refine ⟨conj ρ, ?_, by simp, by simp; linarith⟩
      rw [_root_.riemannZeta_conj, hζ, map_zero]
    · exact ⟨ρ, hζ, rfl, h⟩
  have hmem : σ - 1 / 2 ∈ clearedRegion κ := by
    refine ⟨show max 0 (8 + κ) < (σ - 1 / 2).re from ?_, show 0 < (σ - 1 / 2).im from ?_⟩
    · rw [show (σ - 1 / 2 : ℂ).re = ρ.re - 1 / 2 by simp [hσre], max_lt_iff]
      exact ⟨by linarith, by linarith⟩
    · simpa using hσim
  have h0 := laplace_eq_zero_of_zeta_zero hW hthreshold hF hκ hLap hσζ hmem
  exact criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF
    (by simp only [Complex.sub_re, hσre]; norm_num; linarith) h0

/-- **Decay law, divergent half.** If `∫ F² e^{-bu} < ∞` for the critical state, every zero of `ζ`
right of the critical line satisfies `Re ρ ≤ (17 - b)/2`. -/
theorem criticalState_not_integrable_of_zero {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hρ : 1 / 2 < ρ.re) {b : ℝ} (hb : 17 - 2 * ρ.re < b) :
    ¬ Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) := by
  intro hint
  have hρ1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hle := zero_re_le_of_laplace_holomorphic hW hthreshold hF (κ := -(b / 2)) (by linarith)
    (differentiableOn_laplace_of_sq hd.meas hd.support hint) hζ hρ
  linarith

/-- **The state is a ruler for the zeros.** Either RH holds, or a critical state exists whose every
finite square moment `∫ F² e^{-bu}` bounds the real parts of all zeros right of the line by
`(17 - b)/2`. -/
theorem riemannHypothesis_or_criticalState_decay_ruler :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧
        ∀ b : ℝ, (Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) →
          ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re ≤ (17 - b) / 2 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · refine Or.inr ⟨W₀, F, hW, ht, hF, fun b hint ρ hζ hρ => ?_⟩
    by_contra h
    exact criticalState_not_integrable_of_zero hW ht hF hζ hρ (by linarith) hint

end GaloisForLFunctions.ExclusionOfTheCriticalState
