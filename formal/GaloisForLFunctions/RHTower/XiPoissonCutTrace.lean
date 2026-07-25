import GaloisForLFunctions.RHTower.XiPoissonBottomOnLine

/-!
# The Poisson trace above a height cut

The peeling induction runs the bottom-shell argument on the divisor restricted to heights at least
`g`.  Everything that argument consumes is inherited by the restriction: shells stay finite, a least
height still exists, the weight stays summable, the vertical envelope is the same order-one bound,
and the restricted trace is again analytic on the right half-plane.

Nothing here is new mathematics; it is the same content indexed by a cut, so that the induction has
an object to recurse on.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The copies at or above a height cut. -/
def xiPoissonCut (g : ℝ) : Set XiZeroCopy := {q : XiZeroCopy | g ≤ (xiPoissonPoint q).re}

theorem mem_xiPoissonCut {g : ℝ} {q : XiZeroCopy} :
    q ∈ xiPoissonCut g ↔ g ≤ (xiPoissonPoint q).re := Iff.rfl

/-- Shells of a cut divisor are finite. -/
theorem finite_xiPoissonCut_shell (g R : ℝ) :
    {q : XiZeroCopy | q ∈ xiPoissonCut g ∧ (xiPoissonPoint q).re ≤ R}.Finite :=
  (finite_xiPoissonShell R).subset fun _ hq => hq.2

/-- The weight is summable over any cut. -/
theorem summable_xiPoissonCutWeight {σ : ℝ} (hσ : 0 < σ) (g : ℝ) :
    Summable (fun q : xiPoissonCut g => xiPoissonWeight σ (q : XiZeroCopy)) :=
  (summable_xiPoissonWeight hσ).subtype _

theorem summable_norm_xiPoissonCutTerm {τ : ℂ} (hτ : 0 < τ.re) (g : ℝ) :
    Summable (fun q : xiPoissonCut g => ‖xiPoissonTerm τ (q : XiZeroCopy)‖) :=
  (summable_norm_xiPoissonTerm hτ).subtype _

/-- The real-time trace of a cut divisor. -/
def xiPoissonCutTraceReal (g σ : ℝ) : ℝ :=
  ∑' q : xiPoissonCut g, xiPoissonWeight σ (q : XiZeroCopy)

/-- The complex-time trace of a cut divisor. -/
def xiPoissonCutTraceC (g : ℝ) (τ : ℂ) : ℂ :=
  ∑' q : xiPoissonCut g, xiPoissonTerm τ (q : XiZeroCopy)

theorem xiPoissonCutTraceReal_nonneg (g σ : ℝ) : 0 ≤ xiPoissonCutTraceReal g σ := by
  rw [xiPoissonCutTraceReal]
  exact tsum_nonneg fun q => (xiPoissonWeight_pos σ (q : XiZeroCopy)).le

/-- **The unconditional envelope for a cut trace**: exponential type at most `1/2`. -/
theorem norm_xiPoissonCutTraceC_le {g : ℝ} {τ : ℂ} (hτ : 0 < τ.re) :
    ‖xiPoissonCutTraceC g τ‖ ≤ Real.exp (|τ.im| / 2) * xiPoissonCutTraceReal g τ.re := by
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_xiPoissonCutTerm hτ g)) ?_
  rw [xiPoissonCutTraceReal, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun q => norm_xiPoissonTerm_le τ (q : XiZeroCopy))
    (summable_norm_xiPoissonCutTerm hτ g)
    ((summable_xiPoissonCutWeight hτ g).mul_left _)

/-- Under RH the cut envelope collapses to boundedness. -/
theorem norm_xiPoissonCutTraceC_le_of_rh (hRH : RiemannHypothesis) {g : ℝ} {τ : ℂ}
    (hτ : 0 < τ.re) :
    ‖xiPoissonCutTraceC g τ‖ ≤ xiPoissonCutTraceReal g τ.re := by
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_xiPoissonCutTerm hτ g)) ?_
  rw [xiPoissonCutTraceReal]
  exact le_of_eq
    (tsum_congr fun q => norm_xiPoissonTerm_eq_of_rh hRH τ (q : XiZeroCopy))

/-- The real-time cut trace is antitone. -/
theorem xiPoissonCutTraceReal_antitone {g σ v : ℝ} (hσ : 0 < σ) (hv : 0 ≤ v) :
    xiPoissonCutTraceReal g (σ + v) ≤ xiPoissonCutTraceReal g σ := by
  have hterm : ∀ q : xiPoissonCut g,
      xiPoissonWeight (σ + v) (q : XiZeroCopy) ≤ xiPoissonWeight σ (q : XiZeroCopy) := by
    intro q
    rw [xiPoissonWeight, xiPoissonWeight]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [xiPoissonPoint_re_nonneg (q : XiZeroCopy), hv]
  exact Summable.tsum_le_tsum hterm (summable_xiPoissonCutWeight (by linarith) g)
    (summable_xiPoissonCutWeight hσ g)

/-! ## Analyticity of the cut trace -/

theorem differentiableOn_xiPoissonCutTraceC_box {σ₀ M : ℝ} (hσ₀ : 0 < σ₀) (g : ℝ) :
    DifferentiableOn ℂ (xiPoissonCutTraceC g) (xiPoissonBox σ₀ M) :=
  Complex.differentiableOn_tsum_of_summable_norm
    (u := fun q : xiPoissonCut g => Real.exp (M / 2) * xiPoissonWeight σ₀ (q : XiZeroCopy))
    ((summable_xiPoissonCutWeight hσ₀ g).mul_left _)
    (fun q => (differentiable_xiPoissonTerm (q : XiZeroCopy)).differentiableOn)
    (isOpen_xiPoissonBox σ₀ M)
    (fun q _ ht => norm_xiPoissonTerm_le_on_box (q : XiZeroCopy) ht)

theorem differentiableAt_xiPoissonCutTraceC {g : ℝ} {t : ℂ} (ht : 0 < t.re) :
    DifferentiableAt ℂ (xiPoissonCutTraceC g) t := by
  have hmem : t ∈ xiPoissonBox (t.re / 2) (|t.im| + 1) := ⟨by linarith, by linarith⟩
  refine (differentiableOn_xiPoissonCutTraceC_box (M := |t.im| + 1)
    (by linarith : (0 : ℝ) < t.re / 2) g).differentiableAt ?_
  exact (isOpen_xiPoissonBox _ _).mem_nhds hmem

/-- **The cut trace is analytic on the open right half-plane.** -/
theorem analyticOnNhd_xiPoissonCutTraceC (g : ℝ) :
    AnalyticOnNhd ℂ (xiPoissonCutTraceC g) {t : ℂ | 0 < t.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  intro t ht
  exact (differentiableAt_xiPoissonCutTraceC ht).differentiableWithinAt

end

end RHTower
