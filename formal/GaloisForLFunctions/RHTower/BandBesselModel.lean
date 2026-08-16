import GaloisForLFunctions.RHTower.BesselIZeroModel
import GaloisForLFunctions.RHTower.BandComparisonDefect

/-!
# The modified-Bessel model of the prolate band

The band side of the prolate endpoint is the forbidden region, so its uniform comparison model is

```text
V_s,c(y) = I₀(c Ξ_s(y)) ,      Ξ_s(y) = ∫_y^1 sqrt((t²-s)/(1-t²)) dt .
```

It solves the drift-form equation

```text
V'' + B V' - c² (Ξ')² V = 0 ,      B = Ξ'/Ξ - Ξ''/Ξ' ,
```

exactly and for every aperture, with the *same* first-order coefficient and the *same* aperture term
as the true band equation; the two differ only by the potential `bandComparisonDefect`, which carries
no `c` at all.

The model is positive, antitone (the phase decreases towards the endpoint and `I₀` increases), and
equals `1` at the endpoint.  Those three facts are what the comparison estimate consumes.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- The derivative of the band phase. -/
def bandPhaseDeriv (s y : ℝ) : ℝ := -(prolateWKBProfile s y)

/-- Its second derivative, `Ξ'' = Ξ' · (Ξ''/Ξ')`. -/
def bandPhaseSecondDeriv (s y : ℝ) : ℝ := -(prolateWKBProfile s y) * bandModelDrift s y

/-- The band comparison model `V = I₀(c Ξ)`. -/
def bandModel (s c : ℝ) : ℝ → ℝ := besselIModel c (bandEndpointPhase s)

/-- Its derivative. -/
def bandModelDerivFn (s c : ℝ) : ℝ → ℝ :=
  besselIModelDeriv c (bandEndpointPhase s) (bandPhaseDeriv s)

/-- Its second derivative. -/
def bandModelSecondDerivFn (s c : ℝ) : ℝ → ℝ :=
  besselIModelSecondDeriv c (bandEndpointPhase s) (bandPhaseDeriv s) (bandPhaseSecondDeriv s)

section

variable {s c y : ℝ}

theorem hasDerivAt_bandPhase (hy1 : -1 < y) (hy2 : y < 1) (hsy : s ≤ y ^ 2) :
    HasDerivAt (bandEndpointPhase s) (bandPhaseDeriv s y) y :=
  hasDerivAt_bandEndpointPhase hy1 hy2 hsy

theorem hasDerivAt_bandPhaseDeriv (hy : (0 : ℝ) < 1 - y ^ 2) (hys : s < y ^ 2) :
    HasDerivAt (bandPhaseDeriv s) (bandPhaseSecondDeriv s y) y := by
  have hR : (y ^ 2 - s) / (1 - y ^ 2) ≠ 0 := by
    have h1 : (0 : ℝ) < y ^ 2 - s := by linarith
    positivity
  have hPpos : 0 < prolateWKBProfile s y := by
    rw [prolateWKBProfile]
    exact Real.sqrt_pos.2 (lt_of_le_of_ne (le_of_lt (by positivity)) (Ne.symm hR))
  have h := (hasDerivAt_prolateWKBProfile hy.ne' hR).neg
  have hfun : bandPhaseDeriv s = fun t : ℝ => -(prolateWKBProfile s t) := by
    funext t
    rw [bandPhaseDeriv]
  rw [hfun]
  refine h.congr_deriv ?_
  have hkey := secondDeriv_div_deriv_bandEndpointPhase (s := s) (y := y) hy hys
  rw [bandPhaseSecondDeriv, ← hkey]
  field_simp

theorem hasDerivAt_bandModel (hy1 : -1 < y) (hy2 : y < 1) (hsy : s ≤ y ^ 2) :
    HasDerivAt (bandModel s c) (bandModelDerivFn s c y) y :=
  hasDerivAt_besselIModel (hasDerivAt_bandPhase hy1 hy2 hsy)

theorem hasDerivAt_bandModelDerivFn (hy1 : -1 < y) (hy2 : y < 1) (hys : s < y ^ 2) :
    HasDerivAt (bandModelDerivFn s c) (bandModelSecondDerivFn s c y) y := by
  have hy : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  exact hasDerivAt_besselIModelDeriv (hasDerivAt_bandPhase hy1 hy2 hys.le)
    (hasDerivAt_bandPhaseDeriv hy hys)

theorem bandModel_pos : 0 < bandModel s c y := besselI0_pos _

theorem bandModel_one : bandModel s c 1 = 1 := by
  rw [bandModel, besselIModel, bandEndpointPhase_one, mul_zero, besselI0_zero]

/-- **The model equation.**  The model solves the drift form exactly, with the band's own first-order
coefficient and the band's own aperture term. -/
theorem bandModel_ode (hc : 0 < c) (hy1 : 0 < y) (hy2 : y < 1) (hys : s < y ^ 2) :
    bandModelSecondDerivFn s c y
        + bandFirstOrderCoeff s y * bandModelDerivFn s c y
        - c ^ 2 * prolateWKBProfile s y ^ 2 * bandModel s c y = 0 := by
  have hy : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  have hRpos : (0 : ℝ) < (y ^ 2 - s) / (1 - y ^ 2) := by
    have h1 : (0 : ℝ) < y ^ 2 - s := by linarith
    positivity
  have hPpos : 0 < prolateWKBProfile s y := by
    rw [prolateWKBProfile]
    exact Real.sqrt_pos.2 hRpos
  have hXi : 0 < bandEndpointPhase s y := bandEndpointPhase_pos hy2 hys hy1
  have hcxi : c * bandEndpointPhase s y ≠ 0 := (mul_pos hc hXi).ne'
  have hxi'0 : bandPhaseDeriv s y ≠ 0 := by
    rw [bandPhaseDeriv]
    exact neg_ne_zero.2 hPpos.ne'
  have hode := besselIModel_ode (c := c) (x := y) (ξ := bandEndpointPhase s)
    (ξ' := bandPhaseDeriv s) (ξ'' := bandPhaseSecondDeriv s) hcxi hxi'0 hXi.ne'
  have hcoeff : bandPhaseDeriv s y / bandEndpointPhase s y
      - bandPhaseSecondDeriv s y / bandPhaseDeriv s y = bandFirstOrderCoeff s y := by
    rw [bandPhaseDeriv, bandPhaseSecondDeriv, bandFirstOrderCoeff]
    field_simp
  have hsq : bandPhaseDeriv s y ^ 2 = prolateWKBProfile s y ^ 2 := by
    rw [bandPhaseDeriv]
    ring
  rw [bandModelSecondDerivFn, bandModelDerivFn, bandModel, ← hcoeff, ← hsq]
  exact hode

/-- The model is antitone: the phase falls to zero at the endpoint and `I₀` is increasing. -/
theorem bandModelDerivFn_nonpos (hc : 0 ≤ c) : bandModelDerivFn s c y ≤ 0 := by
  have hXi : 0 ≤ bandEndpointPhase s y := bandEndpointPhase_nonneg s y
  have h1 : 0 ≤ besselI0Deriv (c * bandEndpointPhase s y) :=
    besselI0Deriv_nonneg (mul_nonneg hc hXi)
  have h2 : c * bandPhaseDeriv s y ≤ 0 := by
    rw [bandPhaseDeriv]
    have : 0 ≤ prolateWKBProfile s y := Real.sqrt_nonneg _
    nlinarith
  rw [bandModelDerivFn, besselIModelDeriv]
  exact mul_nonpos_of_nonneg_of_nonpos h1 h2

/-- The band phase is continuous everywhere, including at the endpoint where its derivative blows
up: the angular representation has no singularity. -/
theorem continuous_bandEndpointPhase (s : ℝ) : Continuous (bandEndpointPhase s) := by
  have hf : Continuous fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 - s) :=
    Real.continuous_sqrt.comp ((Real.continuous_sin.pow 2).sub continuous_const)
  have hprim : Continuous fun a : ℝ =>
      ∫ θ in a..(Real.pi / 2), Real.sqrt (Real.sin θ ^ 2 - s) := by
    have hd : ∀ a : ℝ, HasDerivAt
        (fun z : ℝ => ∫ θ in z..(Real.pi / 2), Real.sqrt (Real.sin θ ^ 2 - s))
        (-(Real.sqrt (Real.sin a ^ 2 - s))) a := fun a =>
      intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable a _)
        (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
    exact continuous_iff_continuousAt.2 fun a => (hd a).continuousAt
  have hfun : bandEndpointPhase s
      = (fun a : ℝ => ∫ θ in a..(Real.pi / 2), Real.sqrt (Real.sin θ ^ 2 - s)) ∘ Real.arcsin := by
    funext y
    rw [bandEndpointPhase]
    rfl
  rw [hfun]
  exact hprim.comp Real.continuous_arcsin

/-- The phase falls monotonically to zero at the endpoint. -/
theorem antitone_bandEndpointPhase (s : ℝ) : Antitone (bandEndpointPhase s) := by
  intro y₁ y₂ h
  have hf : Continuous fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 - s) :=
    Real.continuous_sqrt.comp ((Real.continuous_sin.pow 2).sub continuous_const)
  have harc : Real.arcsin y₁ ≤ Real.arcsin y₂ := Real.monotone_arcsin h
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (f := fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 - s)) (μ := MeasureTheory.volume)
    (a := Real.arcsin y₁) (b := Real.arcsin y₂) (c := Real.pi / 2)
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hnn : (0 : ℝ) ≤ ∫ θ in Real.arcsin y₁..Real.arcsin y₂, Real.sqrt (Real.sin θ ^ 2 - s) :=
    intervalIntegral.integral_nonneg harc fun _ _ => Real.sqrt_nonneg _
  rw [bandEndpointPhase, bandEndpointPhase]
  linarith [hadd, hnn]

/-- The model falls monotonically to `1` at the endpoint. -/
theorem antitone_bandModel (hc : 0 ≤ c) : Antitone (bandModel s c) := by
  intro y₁ y₂ h
  have h1 : (0 : ℝ) ≤ c * bandEndpointPhase s y₂ :=
    mul_nonneg hc (bandEndpointPhase_nonneg s y₂)
  have h2 : (0 : ℝ) ≤ c * bandEndpointPhase s y₁ :=
    mul_nonneg hc (bandEndpointPhase_nonneg s y₁)
  have hle : c * bandEndpointPhase s y₂ ≤ c * bandEndpointPhase s y₁ :=
    mul_le_mul_of_nonneg_left (antitone_bandEndpointPhase s h) hc
  exact monotoneOn_besselI0 h1 h2 hle

theorem continuous_bandModel (s c : ℝ) : Continuous (bandModel s c) := by
  have hfun : bandModel s c = besselI0 ∘ fun y : ℝ => c * bandEndpointPhase s y := by
    funext y
    rw [bandModel, besselIModel]
    rfl
  rw [hfun]
  exact (continuous_besselI0).comp (continuous_const.mul (continuous_bandEndpointPhase s))

end

end GaloisForLFunctions.RHTower

end
