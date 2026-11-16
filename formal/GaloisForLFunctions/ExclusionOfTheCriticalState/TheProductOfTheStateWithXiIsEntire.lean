import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes

/-!
# The product of the state with ξ is entire

For a profile `F` of the energy domain the explicit formula splits the bare pairing with a probe:

  `B F(p) = (B F(1) + Δ F(p)) + L F(p) ξ'/ξ(½ + p)`   off the zeros,

and `B F(1) + Δ F` is holomorphic on `Re p > -2`. Hence `ξ(½ + p) · B F(p)` extends to an entire
function, with value `L F(z) ξ'(½ + z)` at a centred zero `z`.

For the critical state `B F(p) = -a L F(p - 8)`. So `ξ(w + 17/2) · L F(w)` is entire; at `w = z - 8`
it equals `-L F(z) ξ'(½ + z)/a`, which for `Re z ≥ 0` vanishes exactly when the zero is multiple.
The difference equation `a L F(p - 8) + ξ'/ξ(½ + p) L F(p) = -(B F(1) + Δ F(p))` has a right side
without poles.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The pole-free part of the pairing -/

/-- The pole-free part of the pairing with a probe: `B F(1) + Δ F(p)`. -/
def regularRemainder (F : ℝ → ℝ) (p : ℂ) : ℂ := globalRemainder F 1 + dividedSum F p

theorem differentiableAt_regularRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : -2 < p.re) : DifferentiableAt ℂ (regularRemainder F) p := by
  show DifferentiableAt ℂ (fun p => globalRemainder F 1 + dividedSum F p) p
  exact (differentiableAt_const _).add (differentiableAt_dividedSum hF hp)

/-- **The pairing is its pole-free part plus `L F · ξ'/ξ`.** -/
theorem globalRemainder_eq_regularRemainder_add {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : xi (1 / 2 + p) ≠ 0) :
    globalRemainder F p =
      regularRemainder F p + negativeHalfLineLaplace (cx F) p * logDeriv xi (1 / 2 + p) := by
  have h := globalRemainder_sub_eq_zeroSum hF hp
  rw [zeroSum_eq_dividedSum_add hF hp] at h
  unfold regularRemainder
  linear_combination h

/-! ### The cleared pairing -/

/-- The pairing multiplied by `ξ(½ + p)`, written without poles: on `Re p > -2` through the
pole-free part, further left through the left remainder. -/
def clearedRemainder (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  if -2 < p.re then
    xi (1 / 2 + p) * regularRemainder F p + negativeHalfLineLaplace (cx F) p * deriv xi (1 / 2 + p)
  else xi (1 / 2 + p) * leftRemainder F p

theorem clearedRemainder_of_gt {F : ℝ → ℝ} {p : ℂ} (h : -2 < p.re) :
    clearedRemainder F p = xi (1 / 2 + p) * regularRemainder F p +
      negativeHalfLineLaplace (cx F) p * deriv xi (1 / 2 + p) := by
  rw [clearedRemainder, if_pos h]

/-- Off the zeros the cleared pairing is `ξ(½ + p) · B F(p)`. -/
theorem clearedRemainder_eq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hxi : xi (1 / 2 + p) ≠ 0) : clearedRemainder F p = xi (1 / 2 + p) * globalRemainder F p := by
  by_cases h : -2 < p.re
  · have e : ∀ x L d : ℂ, x ≠ 0 → x * (L * (d / x)) = L * d := fun x L d hx => by
      field_simp
    rw [clearedRemainder_of_gt h, globalRemainder_eq_regularRemainder_add hF hxi, logDeriv_apply,
      mul_add, e _ _ _ hxi]
  · have hlt : p.re < -(1 / 2) := by linarith [not_lt.mp h]
    rw [clearedRemainder, if_neg h, globalRemainder, if_neg (not_lt.mpr hlt.le), if_pos hlt]

theorem abs_re_lt_of_xi_eq_zero {p : ℂ} (h : xi (1 / 2 + p) = 0) : |p.re| < 1 / 2 := by
  by_contra hc
  exact xi_ne_zero_of_half_le_abs_re (not_lt.mp hc) h

/-- At a zero the cleared pairing is `L F(z) ξ'(½ + z)`. -/
theorem clearedRemainder_of_zero (F : ℝ → ℝ) {p : ℂ} (hxi : xi (1 / 2 + p) = 0) :
    clearedRemainder F p = negativeHalfLineLaplace (cx F) p * deriv xi (1 / 2 + p) := by
  have h : -2 < p.re := by
    have := (abs_lt.mp (abs_re_lt_of_xi_eq_zero hxi)).1
    linarith
  rw [clearedRemainder_of_gt h, hxi, zero_mul, zero_add]

theorem differentiable_xi_half_add : Differentiable ℂ fun p : ℂ => xi (1 / 2 + p) :=
  xi_differentiable.comp ((differentiable_const _).add differentiable_id)

theorem differentiable_deriv_xi_half_add : Differentiable ℂ fun p : ℂ => deriv xi (1 / 2 + p) :=
  xi_differentiable.deriv.comp ((differentiable_const _).add differentiable_id)

/-- **`ξ(½ + p) · B F(p)` extends to an entire function**, for every profile of the domain. -/
theorem differentiable_clearedRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Differentiable ℂ (clearedRemainder F) := by
  intro p
  by_cases h : -2 < p.re
  · have ho : IsOpen {w : ℂ | -2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hd : DifferentiableAt ℂ (fun p : ℂ => xi (1 / 2 + p) * regularRemainder F p +
        negativeHalfLineLaplace (cx F) p * deriv xi (1 / 2 + p)) p :=
      ((differentiable_xi_half_add p).mul (differentiableAt_regularRemainder hF h)).add
        ((differentiableAt_laplace hF (by linarith)).mul (differentiable_deriv_xi_half_add p))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [ho.mem_nhds h] with w hw
    exact clearedRemainder_of_gt hw
  · have hlt : p.re < -(1 / 2) := by linarith [not_lt.mp h]
    have ho : IsOpen {w : ℂ | w.re < -(1 / 2)} := isOpen_lt Complex.continuous_re continuous_const
    have hd : DifferentiableAt ℂ (fun p : ℂ => xi (1 / 2 + p) * globalRemainder F p) p :=
      (differentiable_xi_half_add p).mul
        (differentiableAt_globalRemainder hF fun h' => absurd h' (by linarith))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [ho.mem_nhds hlt] with w hw
    have hw' : w.re < -(1 / 2) := hw
    exact clearedRemainder_eq hF (xi_ne_zero_of_half_le_abs_re (by
      have := neg_le_abs w.re
      linarith))

/-! ### The state -/

/-- The entire function carrying `ξ(w + 17/2) · L F(w)`. -/
def stateXiProduct (W₀ : ℝ) (F : ℝ → ℝ) (w : ℂ) : ℂ :=
  -clearedRemainder F (w + 8) / criticalAliasCoefficient W₀

theorem differentiable_stateXiProduct {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) : Differentiable ℂ (stateXiProduct W₀ F) := by
  have h : Differentiable ℂ fun w : ℂ => clearedRemainder F (w + 8) :=
    (differentiable_clearedRemainder hF).comp (differentiable_id.add (differentiable_const _))
  exact h.neg.div_const _

theorem xi_half_add_shift (w : ℂ) : xi (1 / 2 + (w + 8)) = xi (w + 17 / 2) := by
  rw [show (1 : ℂ) / 2 + (w + 8) = w + 17 / 2 by ring]

/-- Off the shifted zeros the entire function is `ξ(w + 17/2)` times the continuation. -/
theorem stateXiProduct_eq {W₀ : ℝ} {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {w : ℂ}
    (hw : xi (w + 17 / 2) ≠ 0) :
    stateXiProduct W₀ F w = xi (w + 17 / 2) * stateMeromorphic W₀ F w := by
  have hw' : xi (1 / 2 + (w + 8)) ≠ 0 := by rwa [xi_half_add_shift]
  unfold stateXiProduct stateMeromorphic
  rw [clearedRemainder_eq hF hw', xi_half_add_shift]
  ring

/-- **For the critical state the entire function is `ξ(w + 17/2) · L F(w)` on `Re w > -4`.** -/
theorem stateXiProduct_eq_laplace {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ} (hw : -4 < w.re) :
    stateXiProduct W₀ F w = xi (w + 17 / 2) * negativeHalfLineLaplace (cx F) w := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hxi : xi (w + 17 / 2) ≠ 0 := by
    rw [← xi_half_add_shift]
    exact xi_ne_zero_of_half_le_abs_re (by
      have h8 : (w + 8).re = w.re + 8 := by simp
      rw [h8]
      have := le_abs_self (w.re + 8)
      linarith)
  rw [stateXiProduct_eq hd hxi, stateMeromorphic_eq_levyContinuation (by linarith),
    levyContinuation_eq_laplace hW hthreshold hF hw]

/-- At the shifted zero `z - 8` the entire function is `-L F(z) ξ'(½ + z)/a`. -/
theorem stateXiProduct_centredZero_sub (W₀ : ℝ) (F : ℝ → ℝ) (c : XiZeroCopy) :
    stateXiProduct W₀ F (centredZero c - 8) =
      -(negativeHalfLineLaplace (cx F) (centredZero c) * deriv xi (1 / 2 + centredZero c)) /
        criticalAliasCoefficient W₀ := by
  unfold stateXiProduct
  rw [show centredZero c - 8 + 8 = centredZero c by ring,
    clearedRemainder_of_zero F (xi_centredZero c)]

/-- **On and right of the line the entire function vanishes at `z - 8` exactly when the zero is
multiple**: the state's transform is zero-free on the closed right half-plane. -/
theorem stateXiProduct_centredZero_sub_eq_zero_iff {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : XiZeroCopy}
    (hc : 0 ≤ (centredZero c).re) :
    stateXiProduct W₀ F (centredZero c - 8) = 0 ↔ deriv xi (1 / 2 + centredZero c) = 0 := by
  have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  have hL : negativeHalfLineLaplace (cx F) (centredZero c) ≠ 0 :=
    criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF hc
  rw [stateXiProduct_centredZero_sub, div_eq_zero_iff, neg_eq_zero, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h hL
    · exact h
    · exact absurd h ha
  · exact fun h => Or.inl (Or.inr h)

/-! ### The difference equation -/

/-- **The difference equation of a continuation.** Off the zeros,
`a · M(p - 8) + L F(p) ξ'/ξ(½ + p) = -(B F(1) + Δ F(p))` for the continuation `M`; the right side is
holomorphic on `Re p > -2`, so the left side has no pole at the zeros. -/
theorem stateMeromorphic_differenceEquation {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} (hp : xi (1 / 2 + p) ≠ 0) :
    (criticalAliasCoefficient W₀ : ℂ) * stateMeromorphic W₀ F (p - 8) +
        negativeHalfLineLaplace (cx F) p * logDeriv xi (1 / 2 + p) = -regularRemainder F p := by
  have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  have e : ∀ X : ℂ, (criticalAliasCoefficient W₀ : ℂ) * (-X / criticalAliasCoefficient W₀) = -X :=
    fun X => by field_simp
  unfold stateMeromorphic
  rw [show p - 8 + 8 = p by ring, e, globalRemainder_eq_regularRemainder_add hF hp]
  ring

/-- **The difference equation of the critical state**: for `Re p > 4`,
`a L F(p - 8) + ξ'/ξ(½ + p) L F(p) = -(B F(1) + Δ F(p))`. -/
theorem criticalState_differenceEquation {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {p : ℂ} (hp : 4 < p.re) :
    (criticalAliasCoefficient W₀ : ℂ) * negativeHalfLineLaplace (cx F) (p - 8) +
        negativeHalfLineLaplace (cx F) p * logDeriv xi (1 / 2 + p) = -regularRemainder F p := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hxi : xi (1 / 2 + p) ≠ 0 := xi_ne_zero_of_half_le_abs_re (by
    have := le_abs_self p.re
    linarith)
  have h8 : (p - 8).re = p.re - 8 := by simp
  have hre : -4 < (p - 8).re := by rw [h8]; linarith
  have h := stateMeromorphic_differenceEquation hW hd hxi
  rwa [stateMeromorphic_eq_levyContinuation (by linarith),
    levyContinuation_eq_laplace hW hthreshold hF hre] at h

/-- **Either RH holds, or the critical state exists and its transform times `ξ(w + 17/2)` is
entire**, with value `-L F(z) ξ'(½ + z)/a` at every shifted zero `z - 8`. -/
theorem riemannHypothesis_or_criticalState_xi_mul_entire :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧
        ∃ E : ℂ → ℂ, Differentiable ℂ E ∧
          (∀ w : ℂ, -4 < w.re → E w = xi (w + 17 / 2) * negativeHalfLineLaplace (cx F) w) ∧
          ∀ c : XiZeroCopy, E (centredZero c - 8) =
            -(negativeHalfLineLaplace (cx F) (centredZero c) * deriv xi (1 / 2 + centredZero c)) /
              criticalAliasCoefficient W₀ := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, stateXiProduct W₀ F,
      differentiable_stateXiProduct (criticalHalfLineEnergyDomain_of_groundState hF),
      fun w hw => stateXiProduct_eq_laplace hW ht hF hw,
      fun c => stateXiProduct_centredZero_sub W₀ F c⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
