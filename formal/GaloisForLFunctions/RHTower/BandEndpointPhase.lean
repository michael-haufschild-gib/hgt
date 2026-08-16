import GaloisForLFunctions.RHTower.ProlateWKBSharpAction

/-!
# The band-side Liouville variable at the prolate endpoint

The Liouville variable of the prolate band, measured from the singular endpoint, is

```text
Ξ_s(y) = ∫_y^1 √((t² − s)/(1 − t²)) dt ,
```

the improper integral of the WKB profile.  Writing it in the angular variable removes the
singularity outright:

```text
Ξ_s(y) = ∫_{arcsin y}^{π/2} √(sin²θ − s) dθ ,
```

a continuous integrand on a compact interval.  Its `y`-derivative is `−√((y²−s)/(1−y²))`, so

```text
c² (Ξ_s')² = (χ + c² y²)/(1 − y²)
```

exactly, with `χ = −s c²`: this is the phase for which the modified-Bessel model `I₀(c Ξ_s)` has the
right leading potential.  It vanishes at `y = 1` and behaves like `√(1−s)·√(2(1−y))` there, so
`c Ξ_s ≍ 1` precisely when `1 − y ≍ c^{−2}` — the scale at which the Liouville–Green window must
stop and the endpoint model take over.
-/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- The band-side Liouville variable, measured from the singular endpoint. -/
def bandEndpointPhase (s y : ℝ) : ℝ :=
  ∫ θ in Real.arcsin y..(Real.pi / 2), Real.sqrt (Real.sin θ ^ 2 - s)

theorem bandEndpointPhase_one (s : ℝ) : bandEndpointPhase s 1 = 0 := by
  rw [bandEndpointPhase, Real.arcsin_one]
  simp

/-- The profile is the quotient of the two square roots. -/
theorem prolateWKBProfile_eq_div {s y : ℝ} (hsy : s ≤ y ^ 2) :
    prolateWKBProfile s y = Real.sqrt (y ^ 2 - s) / Real.sqrt (1 - y ^ 2) := by
  rw [prolateWKBProfile, Real.sqrt_div (by linarith)]

/-- **The derivative of the band phase is minus the WKB profile.** -/
theorem hasDerivAt_bandEndpointPhase {s y : ℝ} (hy1 : -1 < y) (hy2 : y < 1)
    (hsy : s ≤ y ^ 2) :
    HasDerivAt (bandEndpointPhase s) (-(prolateWKBProfile s y)) y := by
  have hcont : Continuous fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 - s) :=
    Real.continuous_sqrt.comp ((Real.continuous_sin.pow 2).sub continuous_const)
  have htail : ∀ u : ℝ, HasDerivAt (fun v : ℝ => ∫ θ in v..(Real.pi / 2), Real.sqrt (Real.sin θ ^ 2 - s))
      (-Real.sqrt (Real.sin u ^ 2 - s)) u := by
    intro u
    exact intervalIntegral.integral_hasDerivAt_left (hcont.intervalIntegrable u (Real.pi / 2))
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have harc : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - y ^ 2)) y :=
    Real.hasDerivAt_arcsin hy1.ne' hy2.ne
  have hcomp := (htail (Real.arcsin y)).comp y harc
  have hsin : Real.sin (Real.arcsin y) = y := Real.sin_arcsin hy1.le hy2.le
  rw [hsin] at hcomp
  refine hcomp.congr_deriv ?_
  rw [prolateWKBProfile_eq_div hsy]
  ring

/-- The band phase is nonnegative on the band. -/
theorem bandEndpointPhase_nonneg (s y : ℝ) : 0 ≤ bandEndpointPhase s y := by
  have hle : Real.arcsin y ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two y
  rw [bandEndpointPhase]
  exact intervalIntegral.integral_nonneg hle fun _ _ => Real.sqrt_nonneg _

/-- **The phase realizes the prolate potential.**  With `χ = −s c²` the squared speed is exactly the
Riccati potential. -/
theorem sq_prolateWKBProfile {s y : ℝ} (hsy : s ≤ y ^ 2) (hy : y ^ 2 < 1) :
    prolateWKBProfile s y ^ 2 = (y ^ 2 - s) / (1 - y ^ 2) := by
  rw [prolateWKBProfile]
  refine Real.sq_sqrt ?_
  have h1 : (0 : ℝ) ≤ y ^ 2 - s := by linarith
  have h2 : (0 : ℝ) < 1 - y ^ 2 := by linarith
  positivity

/-- The band phase is strictly positive strictly inside the band. -/
theorem bandEndpointPhase_pos {s y : ℝ} (hy2 : y < 1) (hsy : s < y ^ 2)
    (hy1 : 0 < y) : 0 < bandEndpointPhase s y := by
  have hlt : Real.arcsin y < Real.pi / 2 := (Real.arcsin_lt_pi_div_two).2 hy2
  have hcont : ContinuousOn (fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 - s))
      (uIcc (Real.arcsin y) (Real.pi / 2)) :=
    (Real.continuous_sqrt.comp ((Real.continuous_sin.pow 2).sub continuous_const)).continuousOn
  rw [bandEndpointPhase]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((Real.continuous_sqrt.comp
      ((Real.continuous_sin.pow 2).sub continuous_const)).intervalIntegrable _ _)
    (fun θ hθ => ?_) hlt
  have hmem1 : Real.arcsin y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
  have hmemθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_trans hmem1.1 hθ.1.le, hθ.2.le⟩
  have hmono := Real.strictMonoOn_sin.monotoneOn hmem1 hmemθ hθ.1.le
  rw [Real.sin_arcsin (by linarith) hy2.le] at hmono
  refine Real.sqrt_pos.2 ?_
  nlinarith [hmono, hy1, hsy]

/-! ## The second derivative of the phase, and the model drift -/

theorem hasDerivAt_prolateWKBArg {s y : ℝ} (hy : (1 : ℝ) - y ^ 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => (t ^ 2 - s) / (1 - t ^ 2))
      (2 * y * (1 - s) / (1 - y ^ 2) ^ 2) y := by
  have hnum : HasDerivAt (fun t : ℝ => t ^ 2 - s) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).sub_const s
  have hden : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * y)) y := by
    have h := (hasDerivAt_pow 2 y).const_sub (1 : ℝ)
    refine h.congr_deriv ?_
    norm_num
  have h := HasDerivAt.fun_div hnum hden hy
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **The derivative of the WKB profile.** -/
theorem hasDerivAt_prolateWKBProfile {s y : ℝ} (hy : (1 : ℝ) - y ^ 2 ≠ 0)
    (hR : (y ^ 2 - s) / (1 - y ^ 2) ≠ 0) :
    HasDerivAt (prolateWKBProfile s)
      (2 * y * (1 - s) / (1 - y ^ 2) ^ 2 / (2 * prolateWKBProfile s y)) y :=
  (hasDerivAt_prolateWKBArg hy).sqrt hR

/-- The second term of the first-order coefficient of the comparison equation. -/
def bandModelDrift (s y : ℝ) : ℝ := y * (1 - s) / ((1 - y ^ 2) * (y ^ 2 - s))

/-- **The ratio `Ξ''/Ξ'` is an elementary rational function.**  The square root cancels. -/
theorem secondDeriv_div_deriv_bandEndpointPhase {s y : ℝ}
    (hy : (0 : ℝ) < 1 - y ^ 2) (hys : s < y ^ 2) :
    (2 * y * (1 - s) / (1 - y ^ 2) ^ 2 / (2 * prolateWKBProfile s y)) / prolateWKBProfile s y
      = bandModelDrift s y := by
  have hR : (0 : ℝ) < (y ^ 2 - s) / (1 - y ^ 2) := by
    have h1 : (0 : ℝ) < y ^ 2 - s := by linarith
    positivity
  have hPpos : 0 < prolateWKBProfile s y := by
    rw [prolateWKBProfile]
    exact Real.sqrt_pos.2 hR
  have hPsq : prolateWKBProfile s y ^ 2 = (y ^ 2 - s) / (1 - y ^ 2) :=
    sq_prolateWKBProfile (le_of_lt hys) (by linarith)
  have hne : prolateWKBProfile s y ≠ 0 := hPpos.ne'
  have hstep : (2 * y * (1 - s) / (1 - y ^ 2) ^ 2 / (2 * prolateWKBProfile s y))
      / prolateWKBProfile s y
      = (2 * y * (1 - s) / (1 - y ^ 2) ^ 2) / (2 * prolateWKBProfile s y ^ 2) := by
    field_simp
  rw [hstep, hPsq, bandModelDrift]
  have h1 : (0 : ℝ) < y ^ 2 - s := by linarith
  field_simp

/-! ## Two-sided endpoint expansion of the phase -/

theorem sin_mem_of_mem_arcsin {y θ : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 1)
    (hθ : θ ∈ Icc (Real.arcsin y) (Real.pi / 2)) : y ≤ Real.sin θ ∧ Real.sin θ ≤ 1 := by
  have hmem1 : Real.arcsin y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
  have hmemθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_trans hmem1.1 hθ.1, hθ.2⟩
  have hmono := Real.strictMonoOn_sin.monotoneOn hmem1 hmemθ hθ.1
  rw [Real.sin_arcsin (by linarith) hy2] at hmono
  exact ⟨hmono, Real.sin_le_one θ⟩

/-- **The phase is at most `√(1−s)` times the endpoint angle.** -/
theorem bandEndpointPhase_le_sqrt_mul_arccos {s y : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 1) :
    bandEndpointPhase s y ≤ Real.sqrt (1 - s) * Real.arccos y := by
  have hle : Real.arcsin y ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two y
  have hcont : Continuous fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 - s) :=
    Real.continuous_sqrt.comp ((Real.continuous_sin.pow 2).sub continuous_const)
  have hmono : (∫ θ in Real.arcsin y..(Real.pi / 2), Real.sqrt (Real.sin θ ^ 2 - s))
      ≤ ∫ _θ in Real.arcsin y..(Real.pi / 2), Real.sqrt (1 - s) := by
    refine intervalIntegral.integral_mono_on hle (hcont.intervalIntegrable _ _)
      ((continuous_const : Continuous fun _ : ℝ => Real.sqrt (1 - s)).intervalIntegrable _ _)
      fun θ hθ => ?_
    obtain ⟨_, h2⟩ := sin_mem_of_mem_arcsin hy0 hy2 hθ
    refine Real.sqrt_le_sqrt ?_
    nlinarith [Real.neg_one_le_sin θ, h2]
  rw [bandEndpointPhase]
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, Real.arccos, smul_eq_mul]
  ring

/-- **The phase is at least `√(y²−s)` times the endpoint angle.** -/
theorem sqrt_mul_arccos_le_bandEndpointPhase {s y : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 1) :
    Real.sqrt (y ^ 2 - s) * Real.arccos y ≤ bandEndpointPhase s y := by
  have hle : Real.arcsin y ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two y
  have hcont : Continuous fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 - s) :=
    Real.continuous_sqrt.comp ((Real.continuous_sin.pow 2).sub continuous_const)
  have hmono : (∫ _θ in Real.arcsin y..(Real.pi / 2), Real.sqrt (y ^ 2 - s))
      ≤ ∫ θ in Real.arcsin y..(Real.pi / 2), Real.sqrt (Real.sin θ ^ 2 - s) := by
    refine intervalIntegral.integral_mono_on hle
      ((continuous_const : Continuous fun _ : ℝ => Real.sqrt (y ^ 2 - s)).intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) fun θ hθ => ?_
    obtain ⟨h1, _⟩ := sin_mem_of_mem_arcsin hy0 hy2 hθ
    refine Real.sqrt_le_sqrt ?_
    nlinarith [h1, hy0]
  rw [bandEndpointPhase]
  refine le_trans (le_of_eq ?_) hmono
  rw [intervalIntegral.integral_const, Real.arccos, smul_eq_mul]
  ring

end GaloisForLFunctions.RHTower
