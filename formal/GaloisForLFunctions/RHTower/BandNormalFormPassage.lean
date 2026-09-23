import GaloisForLFunctions.RHTower.BandComparisonVolterra

/-!
# From the prolate angular equation to the band comparison equation

The prolate angular equation on the band,

```text
(1-y²) Φ'' - 2y Φ' + (chi - c²y²) Φ = 0 ,      chi = s c² ,
```

reaches the drift form of the modified-Bessel comparison in two standard steps.

The substitution `u = sqrt(1-y²) Φ` removes the first-order term — the two contributions
`2 w' Φ'` and `w · 2y/(1-y²) · Φ'` cancel identically — leaving the normal form `u'' + Q u = 0` with

```text
Q = 1/(1-y²)² - c² P² ,      P² = (y²-s)/(1-y²) .
```

Dividing by the amplitude `g = sqrt(m̃)` of the Liouville weight then produces the drift form with
first-order coefficient `B` and potential `Q + B²/4 + B'/2 = -c²P² + a`, `a` the comparison defect.
Both steps are instances of the abstract passage in `HTGeometry.AbstractComparisonTransport`; the
only band-specific input is that `bandFirstOrderCoeffDeriv` really is the derivative of
`bandFirstOrderCoeff`.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The normal-form weight of the band. -/
def bandNfWeight (y : ℝ) : ℝ := Real.sqrt (1 - y ^ (2 : ℕ))

/-- Its derivative. -/
def bandNfWeightDeriv (y : ℝ) : ℝ := -(y / Real.sqrt (1 - y ^ (2 : ℕ)))

/-- Its second derivative. -/
def bandNfWeightSecondDeriv (y : ℝ) : ℝ := -(1 / ((1 - y ^ (2 : ℕ)) * Real.sqrt (1 - y ^ (2 : ℕ))))

/-- The normal-form solution `u = sqrt(1-y²) Φ`. -/
def bandNormalFormSol (Φ : ℝ → ℝ) (y : ℝ) : ℝ := bandNfWeight y * Φ y

/-- Its derivative. -/
def bandNormalFormSolDeriv (Φ DΦ : ℝ → ℝ) (y : ℝ) : ℝ :=
  bandNfWeightDeriv y * Φ y + bandNfWeight y * DΦ y

/-- Its second derivative. -/
def bandNormalFormSolSecondDeriv (Φ DΦ DDΦ : ℝ → ℝ) (y : ℝ) : ℝ :=
  bandNfWeightSecondDeriv y * Φ y + 2 * bandNfWeightDeriv y * DΦ y + bandNfWeight y * DDΦ y

/-- The normal-form potential of the band. -/
def bandNormalFormPotential (s c : ℝ) (y : ℝ) : ℝ :=
  1 / (1 - y ^ (2 : ℕ)) ^ (2 : ℕ) - c ^ (2 : ℕ) * prolateWKBProfile s y ^ (2 : ℕ)

section

variable {s c y : ℝ} {Φ DΦ DDΦ : ℝ → ℝ}

/-- The derivative of the first-order coefficient. -/
theorem hasDerivAt_bandFirstOrderCoeff (hy1 : 0 < y) (hy2 : y < 1) (hys : s < y ^ (2 : ℕ)) :
    HasDerivAt (bandFirstOrderCoeff s) (bandFirstOrderCoeffDeriv s y) y := by
  have hy : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hP : 0 < prolateWKBProfile s y := prolateWKBProfile_pos hy hys
  have hXi : 0 < bandEndpointPhase s y := bandEndpointPhase_pos hy2 hys hy1
  have hR : (y ^ (2 : ℕ) - s) / (1 - y ^ (2 : ℕ)) ≠ 0 := by
    have h1 : (0 : ℝ) < y ^ (2 : ℕ) - s := by linarith
    positivity
  have hXid : HasDerivAt (bandEndpointPhase s) (-(prolateWKBProfile s y)) y :=
    hasDerivAt_bandEndpointPhase (by linarith) hy2 hys.le
  have hPd : HasDerivAt (prolateWKBProfile s)
      (prolateWKBProfile s y * bandModelDrift s y) y := by
    have h := hasDerivAt_prolateWKBProfile hy.ne' hR
    have hkey : 2 * y * (1 - s) / (1 - y ^ (2 : ℕ)) ^ (2 : ℕ) / (2 * prolateWKBProfile s y)
        = prolateWKBProfile s y * bandModelDrift s y := by
      have hk := secondDeriv_div_deriv_bandEndpointPhase (s := s) (y := y) hy hys
      field_simp at hk ⊢
      linarith [hk]
    rw [hkey] at h
    exact h
  have hDd : HasDerivAt (bandModelDrift s) (bandModelDriftDeriv s y) y :=
    hasDerivAt_bandModelDrift hy.ne' (by linarith)
  have h1 := (hPd.neg).fun_div hXid hXi.ne'
  have h := h1.sub hDd
  have hval : (-(prolateWKBProfile s y * bandModelDrift s y) * bandEndpointPhase s y
        - -(prolateWKBProfile s y) * -(prolateWKBProfile s y)) / bandEndpointPhase s y ^ (2 : ℕ)
        - bandModelDriftDeriv s y
      = bandFirstOrderCoeffDeriv s y := by
    rw [bandFirstOrderCoeffDeriv]
    field_simp
  exact h.congr_deriv hval

/-! ## The normal form -/

theorem hasDerivAt_bandNfWeight (hy : (0 : ℝ) < 1 - y ^ (2 : ℕ)) :
    HasDerivAt bandNfWeight (bandNfWeightDeriv y) y := by
  have hin : HasDerivAt (fun t : ℝ => 1 - t ^ (2 : ℕ)) (-(2 * y)) y := by
    refine ((hasDerivAt_pow 2 y).const_sub 1).congr_deriv ?_
    ring
  have h := (Real.hasDerivAt_sqrt hy.ne').comp y hin
  have hs : (0 : ℝ) < Real.sqrt (1 - y ^ (2 : ℕ)) := Real.sqrt_pos.2 hy
  refine h.congr_deriv ?_
  rw [bandNfWeightDeriv]
  field_simp

theorem hasDerivAt_bandNfWeightDeriv (hy : (0 : ℝ) < 1 - y ^ (2 : ℕ)) :
    HasDerivAt bandNfWeightDeriv (bandNfWeightSecondDeriv y) y := by
  have hs : (0 : ℝ) < Real.sqrt (1 - y ^ (2 : ℕ)) := Real.sqrt_pos.2 hy
  have hsq : Real.sqrt (1 - y ^ (2 : ℕ)) ^ (2 : ℕ) = 1 - y ^ (2 : ℕ) := Real.sq_sqrt hy.le
  have hw := hasDerivAt_bandNfWeight (y := y) hy
  have hfun : bandNfWeight = fun t : ℝ => Real.sqrt (1 - t ^ (2 : ℕ)) := by
    funext t
    rw [bandNfWeight]
  rw [hfun] at hw
  have h := ((hasDerivAt_id y).fun_div hw hs.ne').neg
  refine h.congr_deriv ?_
  rw [bandNfWeightSecondDeriv, bandNfWeightDeriv]
  field_simp
  simp only [id_eq]
  rw [hsq]
  ring

theorem hasDerivAt_bandNormalFormSol (hy : (0 : ℝ) < 1 - y ^ (2 : ℕ)) (hΦ : HasDerivAt Φ (DΦ y) y) :
    HasDerivAt (bandNormalFormSol Φ) (bandNormalFormSolDeriv Φ DΦ y) y := by
  have hw := hasDerivAt_bandNfWeight (y := y) hy
  exact hw.fun_mul hΦ

theorem hasDerivAt_bandNormalFormSolDeriv (hy : (0 : ℝ) < 1 - y ^ (2 : ℕ))
    (hΦ : HasDerivAt Φ (DΦ y) y) (hDΦ : HasDerivAt DΦ (DDΦ y) y) :
    HasDerivAt (bandNormalFormSolDeriv Φ DΦ) (bandNormalFormSolSecondDeriv Φ DΦ DDΦ y) y := by
  have hw := hasDerivAt_bandNfWeight (y := y) hy
  have hw' := hasDerivAt_bandNfWeightDeriv (y := y) hy
  have h := (hw'.fun_mul hΦ).add (hw.fun_mul hDΦ)
  refine h.congr_deriv ?_
  rw [bandNormalFormSolSecondDeriv]
  ring

/-- **The normal form of the band equation.**  The substitution removes the first-order term
identically. -/
theorem band_normalForm_ode (hy1 : 0 < y) (hy2 : y < 1) (hys : s < y ^ (2 : ℕ))
    (hode : (1 - y ^ (2 : ℕ)) * DDΦ y - 2 * y * DΦ y + (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * y ^ (2 : ℕ)) * Φ y = 0) :
    bandNormalFormSolSecondDeriv Φ DΦ DDΦ y
      + bandNormalFormPotential s c y * bandNormalFormSol Φ y = 0 := by
  have hy : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt (1 - y ^ (2 : ℕ)) := Real.sqrt_pos.2 hy
  have hsq : Real.sqrt (1 - y ^ (2 : ℕ)) ^ (2 : ℕ) = 1 - y ^ (2 : ℕ) := Real.sq_sqrt hy.le
  have hPsq : prolateWKBProfile s y ^ (2 : ℕ) = (y ^ (2 : ℕ) - s) / (1 - y ^ (2 : ℕ)) :=
    sq_prolateWKBProfile hys.le (by linarith)
  have hDD : DDΦ y = (2 * y * DΦ y + c ^ (2 : ℕ) * (y ^ (2 : ℕ) - s) * Φ y) / (1 - y ^ (2 : ℕ)) := by
    field_simp
    nlinarith [hode]
  rw [bandNormalFormSolSecondDeriv, bandNormalFormPotential, bandNormalFormSol,
    bandNfWeightSecondDeriv, bandNfWeightDeriv, bandNfWeight, hPsq, hDD]
  field_simp
  rw [hsq]
  ring

/-! ## The drift form -/

/-- **The band solution in comparison form.**  The prolate angular mode, normalised and divided by
the Liouville amplitude, solves exactly the equation the modified-Bessel model solves, perturbed by
the comparison defect. -/
theorem prolateBand_comparison (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 < y) (hy1 : y < 1)
    (hΦ : HasDerivAt Φ (DΦ y) y) (hDΦ : HasDerivAt DΦ (DDΦ y) y)
    (hode : (1 - y ^ (2 : ℕ)) * DDΦ y - 2 * y * DΦ y + (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * y ^ (2 : ℕ)) * Φ y = 0) :
    HasDerivAt
        (comparisonQuotient (driftAmplitude (bandLiouvilleWeight s)) (bandNormalFormSol Φ))
        (comparisonQuotientDeriv (driftAmplitude (bandLiouvilleWeight s))
          (driftAmplitudeDeriv (bandLiouvilleWeight s) (bandFirstOrderCoeff s))
          (bandNormalFormSol Φ) (bandNormalFormSolDeriv Φ DΦ) y) y
      ∧ HasDerivAt
        (comparisonQuotientDeriv (driftAmplitude (bandLiouvilleWeight s))
          (driftAmplitudeDeriv (bandLiouvilleWeight s) (bandFirstOrderCoeff s))
          (bandNormalFormSol Φ) (bandNormalFormSolDeriv Φ DΦ))
        (-(bandFirstOrderCoeff s y) *
            comparisonQuotientDeriv (driftAmplitude (bandLiouvilleWeight s))
              (driftAmplitudeDeriv (bandLiouvilleWeight s) (bandFirstOrderCoeff s))
              (bandNormalFormSol Φ) (bandNormalFormSolDeriv Φ DΦ) y
          - (-(c ^ (2 : ℕ) * prolateWKBProfile s y ^ (2 : ℕ)) + bandComparisonDefect s y) *
              comparisonQuotient (driftAmplitude (bandLiouvilleWeight s))
                (bandNormalFormSol Φ) y) y := by
  have hys : s < y ^ (2 : ℕ) := by nlinarith
  have hy : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hm := hasDerivAt_bandLiouvilleWeight (s := s) (by linarith) hy1 hys
  have hm0 : bandLiouvilleWeight s y ≠ 0 :=
    (bandLiouvilleWeight_pos (by linarith) hy1 hys).ne'
  have hB := hasDerivAt_bandFirstOrderCoeff (s := s) (by linarith) hy1 hys
  have hu := hasDerivAt_bandNormalFormSol (Φ := Φ) (DΦ := DΦ) hy hΦ
  have hDu := hasDerivAt_bandNormalFormSolDeriv (Φ := Φ) (DΦ := DΦ) (DDΦ := DDΦ) hy hΦ hDΦ
  have hnf := band_normalForm_ode (s := s) (c := c) (by linarith) hy1 hys hode
  have h := hasDerivAt_comparisonQuotientDeriv_driftAmplitude
    (m := bandLiouvilleWeight s) (B := bandFirstOrderCoeff s)
    (B' := bandFirstOrderCoeffDeriv s) (u := bandNormalFormSol Φ)
    (Du := bandNormalFormSolDeriv Φ DΦ) (DDu := bandNormalFormSolSecondDeriv Φ DΦ DDΦ)
    (Q := bandNormalFormPotential s c) hm hm0 hB hu hDu hnf
  refine ⟨h.1, h.2.congr_deriv ?_⟩
  have hdef : bandNormalFormPotential s c y
      + (bandFirstOrderCoeff s y ^ (2 : ℕ) / 4 + bandFirstOrderCoeffDeriv s y / 2)
      = -(c ^ (2 : ℕ) * prolateWKBProfile s y ^ (2 : ℕ)) + bandComparisonDefect s y := by
    rw [bandNormalFormPotential, bandComparisonDefect]
    ring
  rw [hdef]

end

end GaloisForLFunctions.RHTower

end
