import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTiltedStateLiesInTheEnergyDomain
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyNormControlsTheValuesAtTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheZeroParsevalIdentityOfTheState

/-!
# The zero pairing of the state converges absolutely

The zero values of the critical state `F` are square-summable over the centred zeros `z = ρ - 1/2`
of `ξ`, with multiplicity: `Σ_z |L F(z)|² < ∞` and `Σ_z |L F(-z)|² < ∞`. The explicit formula at
the state therefore needs no summation method. For every profile `G` of the domain whose unit tilt
`e^{-u} G` lies in the domain (the state itself, every profile of bounded support),

  `Σ_z L F(z) L G(-z) = W(F, G)`, absolutely convergent,

and for `G = F`

  `Σ_z L F(z) L F(-z) = -a ∫ F² e^{-8u} < 0`.

The vector `c = (L F(z))_z` is a square-summable negative vector of the pairing
`β(c, d) = Σ_z c_z d_{-z}`. A zero on the line contributes `|L F(z)|² ≥ 0`, so the zero Parseval
identity

  `Σ_{on} |L F(z)|² + Σ_{off} L F(z) L F(-z) = -a ∫ F² e^{-8u}`

holds with both sums absolutely convergent and no hypothesis on the zeros off the line: these
carry the whole negative mass.

Mechanism. The unit tilt of the state lies in the domain, and the energy norm controls the values
at the zeros at unit depth: both families of zero values are square-summable. The products are
then absolutely summable, and dominated convergence removes the Gaussian weights
`|e^{εz²}| ≤ e^{ε/4}` from the heated formula.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Removing the Gaussian weights -/

theorem norm_cexp_mul_sq_centredZero_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (q : XiZeroCopy) :
    ‖cexp ((ε : ℂ) * centredZero q ^ 2)‖ ≤ Real.exp 1 := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have h1 : ((ε : ℂ) * centredZero q ^ 2).re =
      ε * ((centredZero q).re ^ 2 - (centredZero q).im ^ 2) := by
    rw [Complex.re_ofReal_mul, sq, Complex.mul_re]
    ring
  rw [h1]
  have hx := abs_lt.mp (abs_re_centredZero_lt q)
  have h2 : 0 ≤ 1 / 4 - (centredZero q).re ^ 2 := by nlinarith [hx.1, hx.2]
  nlinarith [mul_nonneg hε0.le h2, mul_nonneg hε0.le (sq_nonneg (centredZero q).im)]

/-- Two square-summable families on the zeros whose Gaussian-weighted pairing has a limit: the
pairing converges absolutely to that limit. -/
theorem hasSum_mul_of_tendsto_gaussian {a b : XiZeroCopy → ℂ}
    (ha : Summable fun q => ‖a q‖ ^ 2) (hb : Summable fun q => ‖b q‖ ^ 2) {L : ℂ}
    (hL : Tendsto (fun ε : ℝ => ∑' q : XiZeroCopy,
      a q * b q * cexp ((ε : ℂ) * centredZero q ^ 2)) (𝓝[>] 0) (𝓝 L)) :
    HasSum (fun q => a q * b q) L := by
  have hab : Summable fun q => ‖a q * b q‖ := by
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
      ((ha.add hb).div_const 2)
    rw [norm_mul]
    nlinarith [sq_nonneg (‖a q‖ - ‖b q‖)]
  have hsum : Summable fun q => a q * b q := hab.of_norm
  have hbound : Summable fun q => ‖a q * b q‖ * Real.exp 1 := hab.mul_right _
  have hpt : ∀ q : XiZeroCopy, Tendsto
      (fun ε : ℝ => a q * b q * cexp ((ε : ℂ) * centredZero q ^ 2)) (𝓝[>] 0)
      (𝓝 (a q * b q)) := by
    intro q
    have hc : Continuous fun ε : ℝ => a q * b q * cexp ((ε : ℂ) * centredZero q ^ 2) := by
      fun_prop
    have h0 : Tendsto (fun ε : ℝ => a q * b q * cexp ((ε : ℂ) * centredZero q ^ 2)) (𝓝 0)
        (𝓝 (a q * b q * cexp (((0 : ℝ) : ℂ) * centredZero q ^ 2))) := hc.tendsto 0
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ q : XiZeroCopy,
      ‖a q * b q * cexp ((ε : ℂ) * centredZero q ^ 2)‖ ≤ ‖a q * b q‖ * Real.exp 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with ε hε0 hε1 q
    rw [norm_mul (a q * b q)]
    exact mul_le_mul_of_nonneg_left (norm_cexp_mul_sq_centredZero_le hε0 hε1 q) (norm_nonneg _)
  have hlim := tendsto_tsum_of_dominated_convergence hbound hpt hev
  have heq := tendsto_nhds_unique hlim hL
  rw [← heq]
  exact hsum.hasSum

/-! ### The zero values of the state -/

/-- The unit tilt of the state lies in the energy domain. -/
theorem criticalState_unitTilt_domain {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    CriticalHalfLineEnergyDomain (fun u => Real.exp (-(1 * u)) * F u) :=
  criticalHalfLineEnergyDomain_exp_mul_groundState hW hthreshold hF zero_le_one le_rfl

/-- **The zero values of the state are square-summable.** -/
theorem criticalState_summable_norm_sq_zeroValues {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Summable fun q : XiZeroCopy => ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ ^ 2 :=
  summable_norm_sq_laplace_centredZero (criticalState_unitTilt_domain hW hthreshold hF)

/-- The values of the state at the reflected zeros are square-summable. -/
theorem criticalState_summable_norm_sq_reflectedZeroValues {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Summable fun q : XiZeroCopy => ‖negativeHalfLineLaplace (cx F) (-centredZero q)‖ ^ 2 :=
  summable_norm_sq_laplace_neg_centredZero (criticalState_unitTilt_domain hW hthreshold hF)

/-- A profile of the domain with bounded support has every tilt in the domain. -/
theorem criticalHalfLineEnergyDomain_exp_mul_of_bounded {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {T : ℝ} (hT : ∀ u, u < -T → G u = 0) {c : ℝ}
    (hc : 0 ≤ c) : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * G u) := by
  have e : (fun u => Real.exp (-(c * u)) * G u) = fun u => truncatedTilt c T u * G u := by
    funext u
    rcases lt_or_ge u (-T) with h | h
    · rw [hT u h, mul_zero, mul_zero]
    · rw [truncatedTilt_eq_exp_neg h]
  rw [e]
  exact criticalHalfLineEnergyDomain_truncatedTilt_mul hG hc T

/-! ### The explicit formula at the state, absolutely convergent -/

/-- **The zero pairing at the state converges absolutely.** For the critical state `F` and a
profile `G` of the domain whose unit tilt lies in the domain, `Σ_z L F(z) L G(-z) = W(F, G)`. -/
theorem criticalState_hasSum_zeroPairing {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G)
    (hG1 : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(1 * u)) * G u)) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) * negativeHalfLineLaplace (cx G) (-centredZero q))
      ((bareMixedEnergy F G : ℝ) : ℂ) :=
  hasSum_mul_of_tendsto_gaussian
    (a := fun q => negativeHalfLineLaplace (cx F) (centredZero q))
    (b := fun q => negativeHalfLineLaplace (cx G) (-centredZero q))
    (criticalState_summable_norm_sq_zeroValues hW hthreshold hF)
    (summable_norm_sq_laplace_neg_centredZero hG1)
    (criticalState_tendsto_zeroPairing hW hthreshold hF hG)

/-- The explicit formula at the state against a profile of bounded support. -/
theorem criticalState_hasSum_zeroPairing_of_bounded {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {T : ℝ} (hT : ∀ u, u < -T → G u = 0) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) * negativeHalfLineLaplace (cx G) (-centredZero q))
      ((bareMixedEnergy F G : ℝ) : ℂ) :=
  criticalState_hasSum_zeroPairing hW hthreshold hF hG
    (criticalHalfLineEnergyDomain_exp_mul_of_bounded hG hT zero_le_one)

/-- **Parseval at the state on the zeros.** `Σ_z L F(z) L F(-z) = -a ∫ F² e^{-8u}`, absolutely
convergent: the zero values are a square-summable negative vector of the zero pairing. -/
theorem criticalState_hasSum_zeroNorm {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) * negativeHalfLineLaplace (cx F) (-centredZero q))
      ((-(criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) : ℝ) : ℂ) :=
  hasSum_mul_of_tendsto_gaussian
    (a := fun q => negativeHalfLineLaplace (cx F) (centredZero q))
    (b := fun q => negativeHalfLineLaplace (cx F) (-centredZero q))
    (criticalState_summable_norm_sq_zeroValues hW hthreshold hF)
    (criticalState_summable_norm_sq_reflectedZeroValues hW hthreshold hF)
    (criticalState_tendsto_zeroNorm hW hthreshold hF)

/-! ### The zero Parseval identity -/

/-- The zero values on the line are square-summable. -/
theorem criticalState_summable_onLine_zeroValueMass {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Summable fun q : onLineCopies => zeroValueMass F q :=
  (criticalState_summable_norm_sq_zeroValues hW hthreshold hF).subtype onLineCopies

/-- **The zero Parseval identity of the state.**
`Σ_{on} |L F(z)|² + Σ_{off} L F(z) L F(-z) = -a ∫ F² e^{-8u}`, both sums absolutely convergent, with
no hypothesis on the zeros off the line. -/
theorem criticalState_zeroParseval {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ((∑' q : onLineCopies, zeroValueMass F q : ℝ) : ℂ) +
      ∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q) =
      ((stateZeroNormLimit W₀ F : ℝ) : ℂ) := by
  have hs := criticalState_hasSum_zeroNorm hW hthreshold hF
  have hsplit : (∑' q : onLineCopies, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q)) +
      ∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q) =
      ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q) :=
    hs.summable.tsum_subtype_add_tsum_subtype_compl onLineCopies
  have hon : (∑' q : onLineCopies, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q)) =
      ((∑' q : onLineCopies, zeroValueMass F q : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun q => ?_
    have h := laplace_mul_laplace_neg_of_re_eq_zero F
      (show (centredZero (q : XiZeroCopy)).re = 0 from q.2) 0
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, neg_zero,
      Real.exp_zero] at h
    exact h
  rw [← hon, hsplit]
  exact hs.tsum_eq

/-- **The zeros off the line carry the negative mass.**
`Σ_{off} L F(z) L F(-z) = -a ∫ F² e^{-8u} - Σ_{on} |L F(z)|²`. -/
theorem criticalState_offLine_zeroNorm {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    (∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q)) =
      ((stateZeroNormLimit W₀ F - ∑' q : onLineCopies, zeroValueMass F q : ℝ) : ℂ) := by
  have h := criticalState_zeroParseval hW hthreshold hF
  rw [Complex.ofReal_sub]
  linear_combination h

/-- The mass of the zeros off the line is negative. -/
theorem criticalState_offLine_zeroNorm_re_neg {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    (∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q)).re < 0 := by
  rw [criticalState_offLine_zeroNorm hW hthreshold hF, Complex.ofReal_re]
  have h0 : 0 ≤ ∑' q : onLineCopies, zeroValueMass F q :=
    tsum_nonneg fun q => zeroValueMass_nonneg F q
  have h1 : stateZeroNormLimit W₀ F < 0 := criticalState_zeroNorm_limit_neg hW hF
  linarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
