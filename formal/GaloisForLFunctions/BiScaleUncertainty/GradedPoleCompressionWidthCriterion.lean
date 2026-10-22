import GaloisForLFunctions.BiScaleUncertainty.DeficitPrimitiveOneSidedWidth
import GaloisForLFunctions.BiScaleUncertainty.BandSpectrumZeroWidthLaw
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompressionRHCriterion
import GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH

/-!
# The two-by-two pole criterion is graded by the zero width, and reads a size, not a sign

The literal two-exponential pole matrix of the restricted Weil form gives an exact RH test:
`RiemannHypothesis` holds iff `|ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a` at every aperture
(`RHTower.riemannHypothesis_iff_weilPoleCompression_nonneg`), and the mechanism is that the cross
entry *is* the integrated Chebyshev deficit `D(2a) = ∫_0^{2a}(e^t − ψ(e^t))dt` up to its Gamma
boundary mass and an explicit linear radius correction
(`RHTower.abs_integratedChebyshevDeficit_sub_weilPoleCross_le`).

Two consequences of that identification are proved here.

* **Size, not sign** (`riemannHypothesis_of_abs_ccmWeilPoleCross_le`).  Only the *order of
  magnitude* of the cross entry is needed: a bound `|ccmWeilPoleCross a| ≤ C e^{a}` at every
  aperture already gives RH, with no reference to the diagonal and no sign.  Since the diagonal
  itself obeys `|ccmWeilPoleDiagonal a| ≤ C₀ e^{a}`
  (`RHTower.abs_ccmWeilPoleDiagonal_le`), the published positivity criterion is the special case in
  which the bound happens to be realised by the diagonal
  (`xiZeroHalfPlaneBound_of_poleCompression_slack`): the compression may fail, by as much as the
  square-root scale `e^{a}`, and still decide the line.  So no sign mechanism is required of the
  two-by-two inequality; what is required is a square-root-scale estimate.
* **Graded by the width** (`xiZeroHalfPlaneBound_of_abs_ccmWeilPoleCross_le`).  For every
  `0 ≤ α < 1/2`, a bound `|ccmWeilPoleCross a| ≤ C e^{(1+2α)a}` gives the zero-free half-plane
  `Re ρ ≤ 1/2 + α`.  Partial progress on the two-by-two inequality is therefore an explicit
  exponent in the shared width unit, not an all-or-nothing demand: the criterion is a one-parameter
  family whose endpoint `α = 0` is RH.

The transport is the one-sided width criterion of `DeficitPrimitiveOneSidedWidth`
(`xiZeroHalfPlaneBound_of_deficitPrimitive_oneSided`), which needs the deficit primitive bounded on
*one* side only, so even the sign of the cross entry is free.
-/

open Set Filter
open scoped Real

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

open _root_.RHTower

/-! ### The deficit primitive against the cross entry -/

/-- The explicit allowance by which the integrated Chebyshev deficit can exceed the cross entry of
the literal pole matrix: the Gamma boundary mass, the linear radius correction, and the endpoint. -/
def poleCrossDeficitAllowance : ℝ :=
  (2 * Real.log 2 + Real.pi + 1) +
    2 * (|-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)| + Real.log 4 + 5) + 1

theorem poleCrossDeficitAllowance_nonneg : 0 ≤ poleCrossDeficitAllowance := by
  unfold poleCrossDeficitAllowance
  positivity

/-- **The deficit primitive is the cross entry up to the square-root scale.** -/
theorem abs_ccmLogChebyshevDeficitPrimitive_le_abs_ccmWeilPoleCross_add
    (a : SuzukiPositiveAperture) :
    |ccmLogChebyshevDeficitPrimitive (2 * a.1)|
      ≤ |ccmWeilPoleCross a| + poleCrossDeficitAllowance * Real.exp a.1 := by
  have ha := a.property
  have he1 : (1 : ℝ) ≤ Real.exp a.1 := Real.one_le_exp ha.le
  have hae : a.1 ≤ Real.exp a.1 := by linarith [Real.add_one_le_exp a.1]
  have hd := abs_le.mp (abs_integratedChebyshevDeficit_sub_weilPoleCross_le a)
  have hΓ := ccmGammaPoleCrossBoundaryMass_le a
  have hc := abs_le.mp (le_refl |ccmWeilPoleCross a|)
  have hK : 0 ≤ |-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)| + Real.log 4 + 5 := by
    positivity
  have hcst : 0 ≤ 2 * Real.log 2 + Real.pi + 1 := by positivity
  rw [← ccmPoleIntegratedChebyshevDeficit_eq_logPrimitive a, poleCrossDeficitAllowance]
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith

/-! ### The graded criterion -/

/-- **The two-by-two pole criterion, graded by the width.** For `0 ≤ α < 1/2`, a square-root-scale
bound `|ccmWeilPoleCross a| ≤ C e^{(1+2α)a}` on the cross entry of the literal pole matrix at every
aperture forces every zero of `Ξ` into the half-plane `Re ρ ≤ 1/2 + α`.  Neither the diagonal nor
the sign of the cross entry enters. -/
theorem xiZeroHalfPlaneBound_of_abs_ccmWeilPoleCross_le {α C : ℝ} (hα : 0 ≤ α) (hα' : α < 1 / 2)
    (hC : 0 ≤ C)
    (h : ∀ a : SuzukiPositiveAperture,
      |ccmWeilPoleCross a| ≤ C * Real.exp ((1 + 2 * α) * a.1)) :
    XiZeroHalfPlaneBound α := by
  have hB0 : 0 ≤ C + poleCrossDeficitAllowance := by
    linarith [poleCrossDeficitAllowance_nonneg]
  refine xiZeroHalfPlaneBound_of_deficitPrimitive_oneSided (B := C + poleCrossDeficitAllowance)
    hα hα' (Or.inl rfl) ?_
  intro T hT
  rcases eq_or_lt_of_le hT with hzero | hpos
  · -- at `T = 0` the deficit primitive vanishes
    rw [← hzero, ccmLogChebyshevDeficitPrimitive, intervalIntegral.integral_same]
    simp
    linarith
  · set a : SuzukiPositiveAperture := ⟨T / 2, by linarith⟩ with hadef
    have h2a : 2 * a.1 = T := by rw [hadef]; ring
    have hexp : ((1 + 2 * α) * a.1) = (1 / 2 + α) * T := by rw [hadef]; ring
    -- the deficit primitive is bounded at the graded rate
    have hbound : |ccmLogChebyshevDeficitPrimitive T|
        ≤ (C + poleCrossDeficitAllowance) * Real.exp ((1 / 2 + α) * T) := by
      have hstep := abs_ccmLogChebyshevDeficitPrimitive_le_abs_ccmWeilPoleCross_add a
      rw [h2a] at hstep
      have hcross : |ccmWeilPoleCross a| ≤ C * Real.exp ((1 / 2 + α) * T) := by
        rw [← hexp]; exact h a
      have hhalf : Real.exp a.1 ≤ Real.exp ((1 / 2 + α) * T) := by
        refine Real.exp_le_exp.mpr ?_
        rw [hadef]
        nlinarith
      nlinarith [poleCrossDeficitAllowance_nonneg, Real.exp_pos ((1 / 2 + α) * T)]
    -- transport it through the negative exponential weight
    have hcancel : Real.exp (-(1 / 2 + α) * T) * Real.exp ((1 / 2 + α) * T) = 1 := by
      rw [← Real.exp_add, show -(1 / 2 + α) * T + (1 / 2 + α) * T = 0 by ring, Real.exp_zero]
    have hwpos : 0 < Real.exp (-(1 / 2 + α) * T) := Real.exp_pos _
    have hlow : -(C + poleCrossDeficitAllowance)
        ≤ Real.exp (-(1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T := by
      have hge : -((C + poleCrossDeficitAllowance) * Real.exp ((1 / 2 + α) * T))
          ≤ ccmLogChebyshevDeficitPrimitive T := (abs_le.mp hbound).1
      have := mul_le_mul_of_nonneg_left hge hwpos.le
      nlinarith
    nlinarith

/-- **The published positivity criterion is the special case of a square-root-scale slack.** The
compression may fail by as much as `C e^{(1+2α)a}` and still give the half-plane `Re ρ ≤ 1/2 + α`;
at `α = 0` the allowed failure is already of the size of the diagonal itself. -/
theorem xiZeroHalfPlaneBound_of_poleCompression_slack {α C : ℝ} (hα : 0 ≤ α) (hα' : α < 1 / 2)
    (hC : 0 ≤ C)
    (h : ∀ a : SuzukiPositiveAperture,
      |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a + C * Real.exp ((1 + 2 * α) * a.1)) :
    XiZeroHalfPlaneBound α := by
  refine xiZeroHalfPlaneBound_of_abs_ccmWeilPoleCross_le (C := ccmWeilPoleUniformDiagonalBound + C)
    hα hα' (by linarith [ccmWeilPoleUniformDiagonalBound_pos]) ?_
  intro a
  have ha := a.property
  have hdiag := le_trans (le_abs_self (ccmWeilPoleDiagonal a)) (abs_ccmWeilPoleDiagonal_le a)
  have hone : Real.exp a.1 ≤ Real.exp ((1 + 2 * α) * a.1) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hD0 : 0 ≤ ccmWeilPoleUniformDiagonalBound := ccmWeilPoleUniformDiagonalBound_pos.le
  nlinarith [h a, Real.exp_pos ((1 + 2 * α) * a.1)]

/-- **Size, not sign: RH from one square-root-scale bound on the cross entry.** -/
theorem riemannHypothesis_of_abs_ccmWeilPoleCross_le {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ C * Real.exp a.1) :
    RiemannHypothesis := by
  refine xiZeroHalfPlaneBound_zero_iff_rh.mp ?_
  refine xiZeroHalfPlaneBound_of_abs_ccmWeilPoleCross_le le_rfl (by norm_num) hC ?_
  intro a
  simpa using h a

/-! ### The converse: the width bounds the cross entry at the matching rate -/

/-- The cross entry of the pole matrix exceeds the deficit primitive by at most the square-root
scale. -/
theorem abs_ccmWeilPoleCross_le_abs_ccmLogChebyshevDeficitPrimitive_add
    (a : SuzukiPositiveAperture) :
    |ccmWeilPoleCross a|
      ≤ |ccmLogChebyshevDeficitPrimitive (2 * a.1)| + poleCrossDeficitAllowance * Real.exp a.1 := by
  have ha := a.property
  have he1 : (1 : ℝ) ≤ Real.exp a.1 := Real.one_le_exp ha.le
  have hae : a.1 ≤ Real.exp a.1 := by linarith [Real.add_one_le_exp a.1]
  have hd := abs_le.mp (abs_integratedChebyshevDeficit_sub_weilPoleCross_le a)
  have hΓ := ccmGammaPoleCrossBoundaryMass_le a
  have hc := abs_le.mp (le_refl |ccmLogChebyshevDeficitPrimitive (2 * a.1)|)
  have hK : 0 ≤ |-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)| + Real.log 4 + 5 := by
    positivity
  have hcst : 0 ≤ 2 * Real.log 2 + Real.pi + 1 := by positivity
  rw [← ccmPoleIntegratedChebyshevDeficit_eq_logPrimitive a] at hc ⊢
  rw [poleCrossDeficitAllowance]
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith

/-- **A zero width bounds the deficit primitive at every rate above `1/2 + α`.** Generalized
von Koch in the gauge, integrated. -/
theorem exists_abs_ccmLogChebyshevDeficitPrimitive_le_of_xiZeroHalfPlaneBound {α β : ℝ}
    (hα : 0 ≤ α) (hαβ : α < β) (hXi : XiZeroHalfPlaneBound α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      |ccmLogChebyshevDeficitPrimitive T| ≤ C * Real.exp ((1 / 2 + β) * T) := by
  set β' : ℝ := (α + β) / 2 with hβ'def
  have hαβ' : α < β' := by rw [hβ'def]; linarith
  have hβ'0 : 0 ≤ β' := le_trans hα hαβ'.le
  set δ : ℝ := β - β' with hδdef
  have hδ0 : 0 < δ := by rw [hδdef, hβ'def]; linarith
  obtain ⟨C₀, hC₀, hC⟩ :=
    ChebyshevGauge.exists_abs_normalizedLogError_le_of_xiZeroHalfPlaneBound hα hαβ' hXi
  refine ⟨C₀ / δ, by positivity, fun T hT => ?_⟩
  have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) T, ‖Real.exp t - Chebyshev.psi (Real.exp t)‖
      ≤ C₀ * Real.exp ((1 / 2 + β') * T) := by
    intro t ht
    rw [Set.uIoc_of_le hT] at ht
    have ht0 : (0 : ℝ) ≤ t := ht.1.le
    have hsplit : SignedPrimePolar.logError t
        = Real.exp (t / 2) * ChebyshevGauge.normalizedLogError t := by
      rw [ChebyshevGauge.normalizedLogError, ← mul_assoc, ← Real.exp_add,
        show t / 2 + -t / 2 = 0 by ring, Real.exp_zero, one_mul]
    have hneg : Real.exp t - Chebyshev.psi (Real.exp t) = -SignedPrimePolar.logError t := by
      rw [SignedPrimePolar.logError]; ring
    rw [Real.norm_eq_abs, hneg, abs_neg, hsplit, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (t / 2) * |ChebyshevGauge.normalizedLogError t|
        ≤ Real.exp (t / 2) * (C₀ * Real.exp (β' * t)) :=
          mul_le_mul_of_nonneg_left (hC t ht0) (Real.exp_pos _).le
      _ = C₀ * Real.exp ((1 / 2 + β') * t) := by
          rw [mul_left_comm, ← Real.exp_add]
          ring_nf
      _ ≤ C₀ * Real.exp ((1 / 2 + β') * T) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left ht.2 (by linarith))) hC₀
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => Real.exp t - Chebyshev.psi (Real.exp t)) hpt
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at hbd
  have hTexp : T ≤ Real.exp (δ * T) / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith [Real.add_one_le_exp (δ * T)]
  have hexpsum : Real.exp ((1 / 2 + β') * T) * Real.exp (δ * T) = Real.exp ((1 / 2 + β) * T) := by
    rw [← Real.exp_add, hδdef]
    ring_nf
  rw [ccmLogChebyshevDeficitPrimitive]
  calc |∫ t in (0 : ℝ)..T, Real.exp t - Chebyshev.psi (Real.exp t)|
      ≤ C₀ * Real.exp ((1 / 2 + β') * T) * T := hbd
    _ ≤ C₀ * Real.exp ((1 / 2 + β') * T) * (Real.exp (δ * T) / δ) := by
        refine mul_le_mul_of_nonneg_left hTexp (by positivity)
    _ = C₀ / δ * (Real.exp ((1 / 2 + β') * T) * Real.exp (δ * T)) := by ring
    _ = C₀ / δ * Real.exp ((1 / 2 + β) * T) := by rw [hexpsum]

/-- **A zero width bounds the cross entry at the matching rate.** -/
theorem exists_abs_ccmWeilPoleCross_le_of_xiZeroHalfPlaneBound {α β : ℝ} (hα : 0 ≤ α)
    (hαβ : α < β) (hXi : XiZeroHalfPlaneBound α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : SuzukiPositiveAperture,
      |ccmWeilPoleCross a| ≤ C * Real.exp ((1 + 2 * β) * a.1) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_abs_ccmLogChebyshevDeficitPrimitive_le_of_xiZeroHalfPlaneBound hα hαβ hXi
  refine ⟨C + poleCrossDeficitAllowance,
    by linarith [poleCrossDeficitAllowance_nonneg], fun a => ?_⟩
  have ha := a.property
  have hstep := abs_ccmWeilPoleCross_le_abs_ccmLogChebyshevDeficitPrimitive_add a
  have hdef := hC (2 * a.1) (by linarith)
  have hrate : (1 / 2 + β) * (2 * a.1) = (1 + 2 * β) * a.1 := by ring
  rw [hrate] at hdef
  have hone : Real.exp a.1 ≤ Real.exp ((1 + 2 * β) * a.1) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hα.trans hαβ.le]
  nlinarith [poleCrossDeficitAllowance_nonneg]

/-- **The cross entry of the literal pole matrix is a faithful reading of the zero width.** For
every `0 ≤ α < 1/2`, every zero of `Ξ` lies in `Re ρ ≤ 1/2 + α` if and only if the cross entry is
`O(e^{(1+2β)a})` at every rate `β` above `α`.  The exponential growth rate of one explicit
function of one real variable is therefore exactly `1 + 2 · (zero width)`: the two-by-two pole
compression loses nothing about the width. -/
theorem xiZeroHalfPlaneBound_iff_forall_exists_abs_ccmWeilPoleCross_le {α : ℝ} (hα : 0 ≤ α)
    (hα' : α < 1 / 2) :
    XiZeroHalfPlaneBound α ↔
      ∀ β : ℝ, α < β → β < 1 / 2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ a : SuzukiPositiveAperture,
        |ccmWeilPoleCross a| ≤ C * Real.exp ((1 + 2 * β) * a.1) := by
  constructor
  · intro hXi β hβ _
    exact exists_abs_ccmWeilPoleCross_le_of_xiZeroHalfPlaneBound hα hβ hXi
  · intro h ρ hρ
    refine not_lt.mp fun hlt => ?_
    set ε : ℝ := min ((ρ.re - 1 / 2 - α) / 2) ((1 / 2 - α) / 2) with hεdef
    have hεl : ε ≤ (ρ.re - 1 / 2 - α) / 2 := min_le_left _ _
    have hεr : ε ≤ (1 / 2 - α) / 2 := min_le_right _ _
    have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
    obtain ⟨C, hC0, hCb⟩ := h (α + ε) (by linarith) (by linarith)
    have hXi := xiZeroHalfPlaneBound_of_abs_ccmWeilPoleCross_le (α := α + ε)
      (by linarith) (by linarith) hC0 hCb
    have := hXi ρ hρ
    linarith

end GaloisForLFunctions.BiScaleUncertainty

end
