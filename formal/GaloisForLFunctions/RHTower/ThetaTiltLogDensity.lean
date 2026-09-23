import GaloisForLFunctions.HTGeometry.OneDimBrascampLieb
import GaloisForLFunctions.RHTower.ThetaCuspKernelLogConcavity
import GaloisForLFunctions.RHTower.ThetaCuspGlobalReflectedRiccati
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSeamJets

/-!
# The size-biased theta measure in the logarithmic variable

The dispersions of the Xi Taylor coefficients are variances of `s = x²` under the tilted measures
`π_κ ∝ x^{2κ} Φ(x) dx` on `(0,∞)`, `Φ = thetaCuspFullSource`. In the logarithmic variable
`w = log x` the density becomes

```text
ρ_κ(w) = exp((2κ+1) w) · Φ(e^w) = exp(G_κ(w)),     G_κ(w) = (2κ+1) w + ℓ(e^w),  ℓ = log Φ,
```

a positive smooth density on all of `ℝ` whose potential `V_κ = −G_κ` has score and curvature

```text
V_κ'(w) = −(2κ+1) − e^w ℓ'(e^w),        V_κ''(w) = −e^w ℓ'(e^w) − e^{2w} ℓ''(e^w) .
```

The tilt is linear in `w`, so the curvature is independent of `κ`; it is strictly positive because
`Φ` is even and strictly log-concave (`ℓ' < 0` on `(0,∞)`, `ℓ'' < 0`). This module sets up these
objects and the derivative identities feeding `HTGeometry.OneDimBrascampLieb`.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

theorem deriv_thetaCuspLogSource_eq (x : ℝ) :
    deriv thetaCuspLogSource x = iteratedDeriv 1 thetaCuspFullSource x / thetaCuspFullSource x :=
  (hasDerivAt_thetaCuspLogSource x).deriv

theorem hasDerivAt_deriv_thetaCuspLogSource (x : ℝ) :
    HasDerivAt (deriv thetaCuspLogSource) (iteratedDeriv 2 thetaCuspLogSource x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv 1 thetaCuspLogSource) x := by
    have := contDiff_thetaCuspLogSource.differentiable_iteratedDeriv 1 (by simp)
    exact this.differentiableAt
  have h := hd.hasDerivAt
  rw [iteratedDeriv_one] at h
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact h

theorem continuous_deriv_thetaCuspLogSource : Continuous (deriv thetaCuspLogSource) := by
  have := contDiff_thetaCuspLogSource.continuous_iteratedDeriv 1 (WithTop.coe_le_coe.mpr le_top)
  simpa [iteratedDeriv_one] using this

theorem continuous_iteratedDeriv_two_thetaCuspLogSource :
    Continuous (iteratedDeriv 2 thetaCuspLogSource) :=
  contDiff_thetaCuspLogSource.continuous_iteratedDeriv 2 (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

/-- `ℓ'' < 0` everywhere (strict log-concavity of the theta source). -/
theorem iteratedDeriv_two_thetaCuspLogSource_neg (x : ℝ) :
    iteratedDeriv 2 thetaCuspLogSource x < 0 := by
  rw [iteratedDeriv_two_thetaCuspLogSource_eq]
  exact div_neg_of_neg_of_pos (thetaCuspLogConcavityNumerator_neg_all x)
    (sq_pos_of_pos (thetaCuspFullSource_pos_all x))

theorem strictAnti_deriv_thetaCuspLogSource : StrictAnti (deriv thetaCuspLogSource) :=
  strictAnti_of_deriv_neg fun x => by
    rw [(hasDerivAt_deriv_thetaCuspLogSource x).deriv]
    exact iteratedDeriv_two_thetaCuspLogSource_neg x

/-- `ℓ'(0) = 0` by evenness. -/
theorem deriv_thetaCuspLogSource_zero : deriv thetaCuspLogSource 0 = 0 := by
  rw [deriv_thetaCuspLogSource_eq, iteratedDeriv_thetaCuspFullSource_zero_of_odd odd_one, zero_div]

/-- `ℓ' < 0` on `(0, ∞)`. -/
theorem deriv_thetaCuspLogSource_neg_of_pos {x : ℝ} (hx : 0 < x) :
    deriv thetaCuspLogSource x < 0 := by
  have := strictAnti_deriv_thetaCuspLogSource hx
  rwa [deriv_thetaCuspLogSource_zero] at this

/-! ### The tilted density in the log variable -/

/-- Log-density `G_κ(w) = (2κ+1) w + ℓ(e^w)`. -/
def thetaTiltLogDensity (κ w : ℝ) : ℝ :=
  (2 * κ + 1) * w + thetaCuspLogSource (Real.exp w)

/-- The unnormalised tilted density `ρ_κ(w) = e^{(2κ+1)w} Φ(e^w)`. -/
def thetaTiltDensity_thetaTiltLogDensity (κ w : ℝ) : ℝ :=
  Real.exp ((2 * κ + 1) * w) * thetaCuspFullSource (Real.exp w)

/-- The score `V_κ'(w) = −(2κ+1) − e^w ℓ'(e^w)`. -/
def thetaTiltScore (κ w : ℝ) : ℝ :=
  -((2 * κ + 1) + Real.exp w * deriv thetaCuspLogSource (Real.exp w))

/-- The curvature `V''(w) = −e^w ℓ'(e^w) − e^{2w} ℓ''(e^w)` (independent of the tilt). -/
def thetaTiltCurvature (w : ℝ) : ℝ :=
  -(Real.exp w * deriv thetaCuspLogSource (Real.exp w) +
    Real.exp w ^ (2 : ℕ) * iteratedDeriv 2 thetaCuspLogSource (Real.exp w))

theorem thetaTiltDensity_pos_thetaTiltLogDensity (κ w : ℝ) : 0 < thetaTiltDensity_thetaTiltLogDensity κ w :=
  mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all _)

theorem thetaTiltDensity_eq_exp (κ w : ℝ) :
    thetaTiltDensity_thetaTiltLogDensity κ w = Real.exp (thetaTiltLogDensity κ w) := by
  unfold thetaTiltDensity_thetaTiltLogDensity thetaTiltLogDensity thetaCuspLogSource
  rw [Real.exp_add, Real.exp_log (thetaCuspFullSource_pos_all _)]

theorem hasDerivAt_thetaTiltLogDensity (κ w : ℝ) :
    HasDerivAt (thetaTiltLogDensity κ) (-thetaTiltScore κ w) w := by
  unfold thetaTiltLogDensity thetaTiltScore
  have h1 : HasDerivAt (fun w : ℝ => (2 * κ + 1) * w) (2 * κ + 1) w := by
    simpa using (hasDerivAt_id w).const_mul (2 * κ + 1)
  have h2 : HasDerivAt (fun w : ℝ => thetaCuspLogSource (Real.exp w))
      (deriv thetaCuspLogSource (Real.exp w) * Real.exp w) w := by
    have := (hasDerivAt_thetaCuspLogSource (Real.exp w)).comp w (Real.hasDerivAt_exp w)
    rw [deriv_thetaCuspLogSource_eq]
    exact this
  have := h1.add h2
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_thetaTiltDensity (κ w : ℝ) :
    HasDerivAt (thetaTiltDensity_thetaTiltLogDensity κ) (-(thetaTiltScore κ w * thetaTiltDensity_thetaTiltLogDensity κ w)) w := by
  have h := (hasDerivAt_thetaTiltLogDensity κ w).exp
  have e : (fun x => Real.exp (thetaTiltLogDensity κ x)) = thetaTiltDensity_thetaTiltLogDensity κ := by
    funext x; exact (thetaTiltDensity_eq_exp κ x).symm
  rw [e] at h
  refine h.congr_deriv ?_
  rw [← thetaTiltDensity_eq_exp]
  ring

theorem hasDerivAt_thetaTiltScore (κ w : ℝ) :
    HasDerivAt (thetaTiltScore κ) (thetaTiltCurvature w) w := by
  unfold thetaTiltScore thetaTiltCurvature
  have h2 : HasDerivAt (fun w : ℝ => Real.exp w * deriv thetaCuspLogSource (Real.exp w))
      (Real.exp w * deriv thetaCuspLogSource (Real.exp w) +
        Real.exp w * (iteratedDeriv 2 thetaCuspLogSource (Real.exp w) * Real.exp w)) w := by
    have ha := Real.hasDerivAt_exp w
    have hb := (hasDerivAt_deriv_thetaCuspLogSource (Real.exp w)).comp w (Real.hasDerivAt_exp w)
    exact ha.mul hb
  have := ((hasDerivAt_const w (2 * κ + 1)).add h2).neg
  refine this.congr_deriv ?_
  ring

theorem continuous_thetaTiltCurvature : Continuous thetaTiltCurvature := by
  unfold thetaTiltCurvature
  exact ((Real.continuous_exp.mul
    (continuous_deriv_thetaCuspLogSource.comp Real.continuous_exp)).add
    ((Real.continuous_exp.pow 2).mul
      (continuous_iteratedDeriv_two_thetaCuspLogSource.comp Real.continuous_exp))).neg

theorem thetaTiltCurvature_pos (w : ℝ) : 0 < thetaTiltCurvature w := by
  unfold thetaTiltCurvature
  have hx : 0 < Real.exp w := Real.exp_pos w
  have h1 := deriv_thetaCuspLogSource_neg_of_pos hx
  have h2 := iteratedDeriv_two_thetaCuspLogSource_neg (Real.exp w)
  have : Real.exp w * deriv thetaCuspLogSource (Real.exp w) < 0 := mul_neg_of_pos_of_neg hx h1
  have : Real.exp w ^ (2 : ℕ) * iteratedDeriv 2 thetaCuspLogSource (Real.exp w) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) h2
  linarith

/-- Continuity of the score. -/
theorem continuous_thetaTiltScore (κ : ℝ) : Continuous (thetaTiltScore κ) :=
  continuous_iff_continuousAt.mpr fun w => (hasDerivAt_thetaTiltScore κ w).continuousAt

end

end RHTower
