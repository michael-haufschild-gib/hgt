import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateDecaysExactlyAtTheRateOfTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateIsTheCauchyTransformOfItsZeroValues

/-!
# The transform of the state converges exactly right of the transported zeros

Let every centred zero have `Re z ≤ κ`. By the decay law `∫ F² e^{2σu} du < ∞` for every
`σ > κ - 8`, so on the half-plane `Re w > κ - 8` right of the transported zeros:

* the transform `L F` converges, is holomorphic and equals the continuation; conversely
  holomorphy of `L F` on `Re w > κ - 8` puts every centred zero in `Re z ≤ κ`;
* `(★)` holds at every point: `a L F(w) = -Σ_z L F(z)/(w + 8 - z)`, absolutely convergent;
* Plancherel: `∫ |L F(σ + it)|² dt = 2π ∫ F² e^{2σu} du`. The Cauchy transform of the zero
  values of the state is square integrable on every line right of the transported zeros, without
  a logarithmic weight;
* the state equation holds on the whole zero-free part `κ < Re p < 1/2` of the strip, and the
  transform carries two logarithms on each of its lines.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- Right of the transported zeros there is room for a square moment of the state. -/
theorem exists_decay_of_right_of_zeros {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {x : ℝ} (hx : κ - 8 < x) :
    ∃ b : ℝ, -(2 * x) < b ∧ Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) :=
  ⟨8 - κ - x, by linarith,
    integrable_sq_mul_exp_of_zero_abscissa_sharp hκ hzero hW hthreshold hF (by linarith)⟩

/-- **The continuation is the transform right of the transported zeros.** -/
theorem stateMeromorphic_eq_laplace_right_of_zeros {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ} (hw : κ - 8 < w.re) :
    stateMeromorphic W₀ F w = negativeHalfLineLaplace (cx F) w := by
  obtain ⟨b, hb1, hb⟩ := exists_decay_of_right_of_zeros hκ hzero hW hthreshold hF hw
  rw [stateMeromorphic_eq_levyContinuation (by linarith)]
  exact levyContinuation_eq_laplace_of_decay hκ hzero hW hthreshold hF hb hw (by linarith)

/-- **The abscissa of holomorphy of the transform is the abscissa of the transported zeros.**
For `0 ≤ κ ≤ 1`, every centred zero has `Re z ≤ κ` if and only if `L F` is holomorphic on
`Re w > κ - 8`. -/
theorem forall_re_centredZero_le_iff_differentiableOn_laplace {κ : ℝ} (hκ : 0 ≤ κ)
    (hκ1 : κ ≤ 1) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    (∀ q : XiZeroCopy, (centredZero q).re ≤ κ) ↔
      DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {w : ℂ | κ - 8 < w.re} := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  constructor
  · intro hzero w hw
    obtain ⟨b, hb1, hb⟩ := exists_decay_of_right_of_zeros hκ hzero hW hthreshold hF
      (show κ - 8 < w.re from hw)
    exact ((differentiableOn_laplace_of_sq hd.meas hd.support hb).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show -(b / 2) < w.re by linarith))).differentiableWithinAt
  · intro hdiff q
    by_contra hq
    have hlt : κ < (centredZero q).re := not_le.mp hq
    have h3 : (centredZero q).re = ((q.1 : ℂ)).re - 1 / 2 := by simp [centredZero]
    have h := zero_re_le_of_laplace_holomorphic hW hthreshold hF (κ := κ - 8) (by linarith)
      hdiff (riemannZeta_xiZeroCopy_eq_zero q) (by linarith)
    linarith

/-- **(★) right of the transported zeros.** If every centred zero has `Re z ≤ κ`, then for
`Re w > κ - 8`, `a L F(w) = -Σ_z L F(z)/(w + 8 - z)`, absolutely convergent. -/
theorem criticalState_hasSum_starEquation_right_of_zeros {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ} (hw : κ - 8 < w.re) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) * (w + 8 - centredZero q)⁻¹)
      (-((criticalAliasCoefficient W₀ : ℂ) * negativeHalfLineLaplace (cx F) w)) := by
  have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive hW).ne'
  have hxi : xi (1 / 2 + (w + 8)) ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h0
    have h1 := hzero q
    have h2 : (centredZero q).re = w.re + 8 := by
      unfold centredZero
      rw [hq]
      simp
    linarith
  have h := hasSum_zeroValues_cauchy (criticalHalfLineEnergyDomain_of_groundState hF)
    (criticalState_summable_norm_sq_zeroValues hW hthreshold hF) hxi
  have hsm := stateMeromorphic_eq_laplace_right_of_zeros hκ hzero hW hthreshold hF hw
  have hg : globalRemainder F (w + 8) =
      -((criticalAliasCoefficient W₀ : ℂ) * negativeHalfLineLaplace (cx F) w) := by
    unfold stateMeromorphic at hsm
    rw [div_eq_iff ha] at hsm
    linear_combination -hsm
  rw [← hg]
  exact h

/-! ### Plancherel on the lines of decay -/

/-- **Plancherel on a line of decay.** If `∫ F² e^{-bu} < ∞` and `-2σ < b`, then
`∫ |L F(σ + it)|² dt = 2π ∫ F² e^{2σu} du`. -/
theorem integral_norm_sq_laplace_line_of_decay {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {b σ : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) (hσ : -(2 * σ) < b) :
    (∫ t : ℝ, ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      2 * Real.pi * ∫ u : ℝ, F u ^ 2 * Real.exp (2 * σ * u) := by
  obtain ⟨hi, h2⟩ := integrable_exp_min_mul_of_decay hFm hsupp hb hσ
  have h := KernelStrip.integral_norm_sq_paperFT_of_memLp (hi.ofReal (𝕜 := ℂ))
    (memLp_cx_of_sq hi h2)
  have h' : (∫ r : ℝ, ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) r‖ ^ 2) =
      2 * Real.pi * ∫ u : ℝ, ‖((Real.exp (σ * min u 0) * F u : ℝ) : ℂ)‖ ^ 2 := h
  have e1 : (∫ t : ℝ, ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      ∫ r : ℝ, ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) r‖ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun t => by
      show ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 =
        ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ)‖ ^ 2
      rw [negativeHalfLineLaplace_add_mul_I_eq_paperFT hsupp σ t])
  rw [e1, h']
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show ‖((Real.exp (σ * min u 0) * F u : ℝ) : ℂ)‖ ^ 2 = F u ^ 2 * Real.exp (2 * σ * u)
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rcases le_or_gt 0 u with hu | hu
  · rw [hsupp u hu]
    simp
  · have e : Real.exp (σ * u) ^ 2 = Real.exp (2 * σ * u) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [min_eq_left hu.le, mul_pow, e]
    ring

/-- **The continuation is square integrable on every line right of the transported zeros**,
with `∫ |L F(σ + it)|² dt = 2π ∫ F² e^{2σu} du`: no logarithmic weight is lost. -/
theorem integral_norm_sq_stateMeromorphic_line_right_of_zeros {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {σ : ℝ} (hσ : κ - 8 < σ) :
    (Integrable fun t : ℝ => ‖stateMeromorphic W₀ F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ∧
      (∫ t : ℝ, ‖stateMeromorphic W₀ F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) =
        2 * Real.pi * ∫ u : ℝ, F u ^ 2 * Real.exp (2 * σ * u) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨b, hb1, hb⟩ := exists_decay_of_right_of_zeros hκ hzero hW hthreshold hF hσ
  have e : (fun t : ℝ => ‖stateMeromorphic W₀ F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      fun t : ℝ => ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    funext fun t => by
      have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
      rw [stateMeromorphic_eq_laplace_right_of_zeros hκ hzero hW hthreshold hF
        (by rw [hre]; exact hσ)]
  rw [e]
  exact ⟨integrable_norm_sq_laplace_line_of_decay hd.meas hd.support hb hb1,
    integral_norm_sq_laplace_line_of_decay hd.meas hd.support hb hb1⟩

/-! ### The zero-free part of the strip -/

/-- **The state equation on the whole zero-free part of the strip.** If every centred zero has
`Re z ≤ κ`, then for `κ < Re p < 1/2`,
`L F(p) A(p) = -a L F(p - 8) - J_G(p - 2) + T_F(p) - L F(-1/2)/(p + 1/2)`, `G = e^{2 min(u,0)} F`. -/
theorem laplace_mul_stripMultiplier_eq_right_of_zeros {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {p : ℂ} (hp1 : κ < p.re)
    (hp2 : p.re < 1 / 2) :
    negativeHalfLineLaplace (cx F) p * stripMultiplier p =
      -((criticalAliasCoefficient W₀ : ℂ) * negativeHalfLineLaplace (cx F) (p - 8)) -
        levyHeadTerm (fun u => Real.exp (2 * min u 0) * F u) (p - 2) + stateTail F p -
        negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2) :=
  laplace_mul_stripMultiplier_eq hκ hzero hW hthreshold hF
    (integrable_sq_mul_exp_of_zero_abscissa_sharp hκ hzero hW hthreshold hF
      (b := 16 - κ - p.re) (by linarith)) hp1 hp2 (by linarith)

/-- **Two logarithms on every line of the zero-free part of the strip.** If every centred zero
has `Re z ≤ κ` and `κ < s < 1/2`, then `∫ log(|t| + 4)² |L F(s + it)|² dt < ∞`. -/
theorem integrable_log_sq_mul_norm_sq_laplace_line_right_of_zeros {κ s : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκs : κ < s) (hs : s < 1 / 2)
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Integrable fun t : ℝ => Real.log (|t| + 4) ^ 2 *
      ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
  integrable_log_sq_mul_norm_sq_laplace_line hκ hzero hκs hs hW hthreshold hF
    (integrable_sq_mul_exp_of_zero_abscissa_sharp hκ hzero hW hthreshold hF
      (b := 16 - κ - s) (by linarith)) (by linarith)

end GaloisForLFunctions.ExclusionOfTheCriticalState
