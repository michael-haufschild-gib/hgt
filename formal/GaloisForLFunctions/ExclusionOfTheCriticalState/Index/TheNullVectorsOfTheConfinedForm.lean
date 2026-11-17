import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateIsMeromorphicInThePlane

/-!
# The null vectors of the confined form

A **null vector** of the confined form `Q_R = B + a(R) W₈` is a nonzero profile `F` of the energy
domain with `Q_R(F, G) = 0` for every profile `G` (`IsConfinedNullVector`). The critical state is the
null vector at the threshold `W₀`; the higher critical states are null vectors at larger ratios.

* **Orthogonality** (`confinedNullVectors_orthogonal`). Null vectors at different ratios are
  orthogonal for the confinement mass and for Weil's bare form: `B(F, G) = −a(R) W₈(F, G)` and
  `B(G, F) = −a(S) W₈(G, F)`, with `a(R) ≠ a(S)`.
* **Zero pairing** (`criticalState_tendsto_zeroPairing_nullVector`). The zero values of the critical
  state and of a null vector at another ratio are orthogonal for the Gaussian-summed zero pairing.
* **The state equation for every null vector** (`nullVector_probeEquation`,
  `nullVector_stateMeromorphic_eq_laplace`, `nullVector_starEquation`). The weak equation tested on
  probes is the probe equation with coefficient `a(R)`; it continues holomorphically, the meromorphic
  continuation `stateMeromorphic R F` is the transform of `F` on `Re w > −4`, and (★) holds:
  `a(R)(L F(w) − L F(v)) = −Σ_z L F(z)(1/(w+8−z) − 1/(v+8−z))`. Every ECS statement about
  `stateMeromorphic` that only uses the energy domain (residues, left formula, bounds) applies.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- A nonzero profile of the energy domain annihilating the confined form at ratio `R`. -/
def IsConfinedNullVector (R : ℝ) (F : ℝ → ℝ) : Prop :=
  CriticalHalfLineEnergyDomain F ∧ (∫ u, F u ^ 2) ≠ 0 ∧
    ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → criticalHalfLineMixedEnergy R F G = 0

/-- The critical state is the null vector at the threshold. -/
theorem isConfinedNullVector_of_groundState {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) : IsConfinedNullVector W₀ F :=
  ⟨criticalHalfLineEnergyDomain_of_groundState hF, by rw [hF.2.2.2.1]; norm_num,
    fun _ hG => criticalHalfLineMixedEnergy_groundState_eq_zero hW ht hF hG⟩

/-! ### Orthogonality -/

theorem gammaMixedForm_comm (F G : ℝ → ℝ) : gammaMixedForm F G = gammaMixedForm G F := by
  unfold gammaMixedForm gammaFourierPair
  congr 2
  funext r
  ring

theorem bareMixedEnergy_comm (F G : ℝ → ℝ) : bareMixedEnergy F G = bareMixedEnergy G F := by
  unfold bareMixedEnergy
  rw [gammaMixedForm_comm]
  ring

/-- **Null vectors at different ratios are orthogonal** for the confinement mass and for Weil's bare
form. -/
theorem confinedNullVectors_orthogonal {R S : ℝ} (hR : 0 < R) (hS : 0 < S) (hRS : R ≠ S)
    {F G : ℝ → ℝ} (hF : IsConfinedNullVector R F) (hG : IsConfinedNullVector S G) :
    (∫ u in Iio 0, F u * G u * Real.exp (-(8 * u))) = 0 ∧ bareMixedEnergy F G = 0 := by
  have h1 := hF.2.2 G hG.1
  have h2 := hG.2.2 F hF.1
  rw [criticalHalfLineMixedEnergy_eq_bare_add] at h1 h2
  rw [bareMixedEnergy_comm G F] at h2
  have hc : (∫ u in Iio 0, G u * F u * Real.exp (-(8 * u))) =
      ∫ u in Iio 0, F u * G u * Real.exp (-(8 * u)) :=
    setIntegral_congr_fun measurableSet_Iio fun u _ => by ring
  rw [hc] at h2
  have ha : criticalAliasCoefficient R ≠ criticalAliasCoefficient S := fun h =>
    hRS (criticalAliasCoefficient_injective_positive hR hS h)
  have hC : (criticalAliasCoefficient R - criticalAliasCoefficient S) *
      (∫ u in Iio 0, F u * G u * Real.exp (-(8 * u))) = 0 := by linarith
  have hC0 := (mul_eq_zero.mp hC).resolve_left (sub_ne_zero.mpr ha)
  refine ⟨hC0, ?_⟩
  rw [hC0, mul_zero, add_zero] at h1
  exact h1

/-- **The zero values of the critical state and of a null vector at another ratio are orthogonal**
for the Gaussian-summed zero pairing. -/
theorem criticalState_tendsto_zeroPairing_nullVector {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) {S : ℝ} (hS : 0 < S) (hSW : S ≠ W₀) {G : ℝ → ℝ}
    (hG : IsConfinedNullVector S G) :
    Tendsto (fun ε : ℝ => ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) * Complex.exp ((ε : ℂ) * centredZero q ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  have h := criticalState_tendsto_zeroPairing hW ht hF hG.1
  rwa [(confinedNullVectors_orthogonal hW hS (Ne.symm hSW)
    (isConfinedNullVector_of_groundState hW ht hF) hG).2, Complex.ofReal_zero] at h

/-! ### The state equation of a null vector -/

variable {R : ℝ} {F : ℝ → ℝ}

/-- The weak equation of a null vector tested on the probe `e_p`, `p > 4`. -/
theorem nullVector_probeEquation (hF : IsConfinedNullVector R F) {p : ℝ} (hp : 4 < p) :
    criticalAliasCoefficient R * (∫ u, F u * Real.exp ((p - 8) * u)) +
      1 / (2 * Real.pi) *
        (∫ r : ℝ, (paperFT (cx F) (r : ℂ) / ((p : ℂ) - I * r)).re * EF.gammaBracket r) -
      ((∫ t, F t * Real.exp (p * t)) *
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p)) +
        primeTail F p) +
      (coshHalfMoment F * (1 / (p + 1 / 2) + 1 / (p - 1 / 2)) -
        sinhHalfMoment F * (1 / (p + 1 / 2) - 1 / (p - 1 / 2))) = 0 := by
  have hd := hF.1
  have he := hF.2.2 _ (criticalHalfLineEnergyDomain_probe hp)
  rw [criticalHalfLineMixedEnergy_eq_bare_add, confinement_probe_right hd.support] at he
  unfold bareMixedEnergy gammaMixedForm at he
  rw [primeMixedForm_symm (probe p) F, polePart_probe_right F (by linarith),
    primeMixedForm_probe_right hd hp] at he
  simp_rw [gammaFourierPair_probe_right F (by linarith : (0 : ℝ) < p)] at he
  linarith only [he]

/-- The holomorphic state equation of a null vector vanishes at real `p > 4`. -/
theorem nullVector_stateEquation_ofReal_eq_zero (hF : IsConfinedNullVector R F) {p : ℝ}
    (hp : 4 < p) : stateEquation R F p = 0 := by
  have he := nullVector_probeEquation hF hp
  have hs : (1 : ℂ) / 2 + p = ((1 / 2 + p : ℝ) : ℂ) := by push_cast; ring
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (1 : ℂ) / 2 + p) (by rw [hs, Complex.ofReal_re]; linarith)
  have hζ : deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p) =
      -((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p) : ℝ) : ℂ) := by
    rw [← LSeries_vonMangoldt_ofReal, ← hs, hL, neg_div, neg_neg]
  have h8 : (p : ℂ) - 8 = ((p - 8 : ℝ) : ℂ) := by push_cast; ring
  unfold stateEquation
  rw [hζ, h8, negativeHalfLineLaplace_ofReal, negativeHalfLineLaplace_ofReal, stateGamma_ofReal,
    stateTail_ofReal]
  have hc : (((0 : ℝ)) : ℂ) = 0 := by simp
  rw [← hc, ← he]
  push_cast
  ring

/-- The holomorphic state equation of a null vector vanishes on `Re p > 4`. -/
theorem nullVector_stateEquation_eqOn_zero (hF : IsConfinedNullVector R F) :
    EqOn (stateEquation R F) 0 {p : ℂ | max 1 (-(8 / 2) + 8) < p.re} := by
  have hd := hF.1
  have hLap := differentiableOn_laplace_of_sq hd.meas hd.support hd.exponential
  have hU : IsOpen {p : ℂ | max 1 (-(8 / 2) + 8) < p.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (stateEquation R F) {p : ℂ | max 1 (-(8 / 2) + 8) < p.re} := by
    intro p hp
    have hp1 : max 1 (-(8 / 2) + 8) < p.re := hp
    have hp' : 1 < p.re := lt_of_le_of_lt (le_max_left _ _) hp1
    have hp8 : -(8 / 2) + 8 < p.re := lt_of_le_of_lt (le_max_right _ _) hp1
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
    (show max 1 (-(8 / 2) + 8) < (5 : ℂ).re by rw [max_lt_iff]; norm_num)
    (frequently_eq_zero_of_real fun x hx => nullVector_stateEquation_ofReal_eq_zero hF hx)

/-- **The continuation of a null vector is its transform** on `Re w > −4`:
`a(R) L F(w) = −B F(w + 8)`. -/
theorem nullVector_alias_mul_laplace (hR : 0 < R) (hF : IsConfinedNullVector R F) {w : ℂ}
    (hw : -4 < w.re) :
    (criticalAliasCoefficient R : ℂ) * negativeHalfLineLaplace (cx F) w =
      -globalRemainder F (w + 8) := by
  have hd := hF.1
  have hp : max 1 (-(8 / 2) + 8) < (w + 8).re := by
    rw [max_lt_iff]; simp; constructor <;> linarith
  have h0 := nullVector_stateEquation_eqOn_zero hF hp
  have hne : w + 8 ≠ 1 / 2 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hζ : riemannZeta (1 / 2 + (w + 8)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  rw [stateEquation_eq_remainder hd hne hζ, add_sub_cancel_right] at h0
  simp only [Pi.zero_apply] at h0
  have hlev := levyContinuation_eq_stateContinuation (W₀ := R) hd (w := w) (by linarith)
  have hmer := stateMeromorphic_eq_levyContinuation (W₀ := R) (F := F) (w := w) (by linarith)
  have hα : (criticalAliasCoefficient R : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hR).ne'
  have hcont : stateContinuation R F w = negativeHalfLineLaplace (cx F) w := by
    unfold stateContinuation
    rw [div_eq_iff hα]
    linear_combination -h0
  have hsm : stateMeromorphic R F w = negativeHalfLineLaplace (cx F) w := by
    rw [hmer, hlev, hcont]
  unfold stateMeromorphic at hsm
  rw [← hsm]
  field_simp

/-- The meromorphic continuation of a null vector agrees with its transform on `Re w > −4`. -/
theorem nullVector_stateMeromorphic_eq_laplace (hR : 0 < R) (hF : IsConfinedNullVector R F)
    {w : ℂ} (hw : -4 < w.re) : stateMeromorphic R F w = negativeHalfLineLaplace (cx F) w := by
  have hα : (criticalAliasCoefficient R : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hR).ne'
  have h := nullVector_alias_mul_laplace hR hF hw
  unfold stateMeromorphic
  rw [div_eq_iff hα, ← h]
  ring

/-- **(★) for every null vector.** For `Re w, Re v > −4`,
`a(R)(L F(w) − L F(v)) = −Σ_z L F(z)(1/(w+8−z) − 1/(v+8−z))`. -/
theorem nullVector_starEquation (hR : 0 < R) (hF : IsConfinedNullVector R F) {w v : ℂ}
    (hw : -4 < w.re) (hv : -4 < v.re) :
    (criticalAliasCoefficient R : ℂ) *
        (negativeHalfLineLaplace (cx F) w - negativeHalfLineLaplace (cx F) v) =
      -∑' c : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero c) *
        ((w + 8 - centredZero c)⁻¹ - (v + 8 - centredZero c)⁻¹) := by
  have hxi : ∀ u : ℂ, -4 < u.re → xi (1 / 2 + (u + 8)) ≠ 0 := fun u hu =>
    xi_ne_zero_of_half_le_abs_re (by
      have h8 : (u + 8).re = u.re + 8 := by simp
      rw [h8]
      have := le_abs_self (u.re + 8)
      linarith)
  have hmain := globalRemainder_sub_eq_tsum hF.1 (hxi w hw) (hxi v hv)
  have k1 := nullVector_alias_mul_laplace hR hF hw
  have k2 := nullVector_alias_mul_laplace hR hF hv
  linear_combination k1 - k2 - hmain

end GaloisForLFunctions.ExclusionOfTheCriticalState
