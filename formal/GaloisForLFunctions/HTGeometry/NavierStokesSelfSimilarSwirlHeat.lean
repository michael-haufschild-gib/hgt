import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

/-!
# Self-similar swirl heat profiles

This file formalizes the differential conjugacy in Lemma A.6 of the supplied Navier--Stokes paper.
For `s = r²/2`, `τ = 1-t`, and `Z = 2τ/s`, it certifies the time and first two radial derivatives of
`c s⁻ᴬ H(Z)`. The profile ODE (A.37) then implies the cylindrical swirl heat equation
`∂ₜK = (∂ᵣᵣ + r⁻¹∂ᵣ - r⁻²)K` at every positive radius.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesSelfSimilarSwirlHeat

noncomputable section

/-- Similarity variable `Z = 2τ/s` from Lemma A.6. -/
def swirlSimilarityVariable (τ s : ℝ) : ℝ := 2 * τ / s

/-- Self-similar swirl profile before substituting `s = r²/2` and `τ = 1-t`. -/
def selfSimilarSwirlProfile (c A : ℝ) (H : ℝ → ℝ) (τ s : ℝ) : ℝ :=
  c * s ^ (-A) * H (swirlSimilarityVariable τ s)

def selfSimilarSwirlScaleFirst (c A : ℝ) (H H₁ : ℝ → ℝ) (τ s : ℝ) : ℝ :=
  c * s ^ (-A - 1) *
    (-A * H (swirlSimilarityVariable τ s) -
      swirlSimilarityVariable τ s * H₁ (swirlSimilarityVariable τ s))

def selfSimilarSwirlScaleSecond (c A : ℝ) (H H₁ H₂ : ℝ → ℝ) (τ s : ℝ) : ℝ :=
  c * s ^ ((-A - 1) - 1) *
    (A * (A + 1) * H (swirlSimilarityVariable τ s) +
      2 * (A + 1) * swirlSimilarityVariable τ s * H₁ (swirlSimilarityVariable τ s) +
      swirlSimilarityVariable τ s ^ 2 * H₂ (swirlSimilarityVariable τ s))

def selfSimilarSwirlTimeFirst (c A : ℝ) (H₁ : ℝ → ℝ) (τ s : ℝ) : ℝ :=
  -2 * c * s ^ (-A - 1) * H₁ (swirlSimilarityVariable τ s)

/-- ODE (A.37), written with `aK = A + 1/2`. -/
def swirlHeatProfileODE (A Z h h₁ h₂ : ℝ) : ℝ :=
  Z ^ 2 * h₂ + (1 + 2 * (A + 1 / 2) * Z) * h₁ +
    (A + 1 / 2) * (A - 1 / 2) * h

theorem hasDerivAt_swirlSimilarityVariable_tau {τ s : ℝ} :
    HasDerivAt (fun u ↦ swirlSimilarityVariable u s) (2 / s) τ := by
  simpa [swirlSimilarityVariable] using
    ((hasDerivAt_id τ).const_mul 2).div_const s

theorem hasDerivAt_swirlSimilarityVariable_scale {τ s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (swirlSimilarityVariable τ)
      (-swirlSimilarityVariable τ s / s) s := by
  have h := (hasDerivAt_const s (2 * τ)).div (hasDerivAt_id s) hs
  have h' : HasDerivAt (swirlSimilarityVariable τ) (-(2 * τ) / s ^ 2) s := by
    convert! h using 1
    all_goals simp
  exact h'.congr_deriv (by
    simp only [swirlSimilarityVariable]
    field_simp [hs])

theorem hasDerivAt_selfSimilarSwirlProfile_tau
    {c A τ s : ℝ} {H H₁ : ℝ → ℝ}
    (hs : 0 < s)
    (hH : HasDerivAt H (H₁ (swirlSimilarityVariable τ s))
      (swirlSimilarityVariable τ s)) :
    HasDerivAt (fun u ↦ selfSimilarSwirlProfile c A H u s)
      (-selfSimilarSwirlTimeFirst c A H₁ τ s) τ := by
  have hcomp := hH.comp τ hasDerivAt_swirlSimilarityVariable_tau
  have hscaled := hcomp.const_mul (c * s ^ (-A))
  have hscaled' : HasDerivAt (fun u ↦ selfSimilarSwirlProfile c A H u s)
      (c * s ^ (-A) * (H₁ (swirlSimilarityVariable τ s) * (2 / s))) τ := by
    convert! hscaled using 1
  exact hscaled'.congr_deriv (by
    unfold selfSimilarSwirlTimeFirst
    have hpow01 : s ^ (-A) = s ^ (-A - 1) * s := by
      calc
        s ^ (-A) = s ^ ((-A - 1) + 1) := by
          congr 1
          ring
        _ = s ^ (-A - 1) * s ^ (1 : ℝ) := Real.rpow_add hs _ _
        _ = s ^ (-A - 1) * s := by rw [Real.rpow_one]
    rw [hpow01]
    field_simp [hs.ne'])

theorem hasDerivAt_selfSimilarSwirlProfile_scale
    {c A τ s : ℝ} {H H₁ : ℝ → ℝ}
    (hs : 0 < s)
    (hH : HasDerivAt H (H₁ (swirlSimilarityVariable τ s))
      (swirlSimilarityVariable τ s)) :
    HasDerivAt (selfSimilarSwirlProfile c A H τ)
      (selfSimilarSwirlScaleFirst c A H H₁ τ s) s := by
  have hpow := Real.hasDerivAt_rpow_const (x := s) (p := -A) (Or.inl hs.ne')
  have hcomp := hH.comp s (hasDerivAt_swirlSimilarityVariable_scale hs.ne')
  have hscaled := (hpow.mul hcomp).const_mul c
  have hscaled' : HasDerivAt (selfSimilarSwirlProfile c A H τ)
      (c * (-A * s ^ (-A - 1) * H (swirlSimilarityVariable τ s) +
        s ^ (-A) * (H₁ (swirlSimilarityVariable τ s) *
          (-swirlSimilarityVariable τ s / s)))) s := by
    convert! hscaled using 1
    funext u
    simp [selfSimilarSwirlProfile]
    ring
  exact hscaled'.congr_deriv (by
    unfold selfSimilarSwirlScaleFirst
    have hpow01 : s ^ (-A) = s ^ (-A - 1) * s := by
      calc
        s ^ (-A) = s ^ ((-A - 1) + 1) := by
          congr 1
          ring
        _ = s ^ (-A - 1) * s ^ (1 : ℝ) := Real.rpow_add hs _ _
        _ = s ^ (-A - 1) * s := by rw [Real.rpow_one]
    rw [hpow01]
    field_simp [hs.ne']
    ring)

theorem hasDerivAt_selfSimilarSwirlScaleFirst_scale
    {c A τ s : ℝ} {H H₁ H₂ : ℝ → ℝ}
    (hs : 0 < s)
    (hH : HasDerivAt H (H₁ (swirlSimilarityVariable τ s))
      (swirlSimilarityVariable τ s))
    (hH₁ : HasDerivAt H₁ (H₂ (swirlSimilarityVariable τ s))
      (swirlSimilarityVariable τ s)) :
    HasDerivAt (selfSimilarSwirlScaleFirst c A H H₁ τ)
      (selfSimilarSwirlScaleSecond c A H H₁ H₂ τ s) s := by
  let Z := swirlSimilarityVariable τ s
  have hZ : HasDerivAt (swirlSimilarityVariable τ) (-Z / s) s := by
    simpa [Z] using hasDerivAt_swirlSimilarityVariable_scale (τ := τ) hs.ne'
  have hHZ : HasDerivAt (fun u ↦ H (swirlSimilarityVariable τ u))
      (H₁ Z * (-Z / s)) s := hH.comp s hZ
  have hH₁Z : HasDerivAt (fun u ↦ H₁ (swirlSimilarityVariable τ u))
      (H₂ Z * (-Z / s)) s := hH₁.comp s hZ
  have hbracket : HasDerivAt
      (fun u ↦ -A * H (swirlSimilarityVariable τ u) -
        swirlSimilarityVariable τ u * H₁ (swirlSimilarityVariable τ u))
      (-A * (H₁ Z * (-Z / s)) -
        ((-Z / s) * H₁ Z + Z * (H₂ Z * (-Z / s)))) s :=
    (hHZ.const_mul (-A)).sub (hZ.mul hH₁Z)
  have hpow := Real.hasDerivAt_rpow_const
    (x := s) (p := -A - 1) (Or.inl hs.ne')
  have hscaled := (hpow.mul hbracket).const_mul c
  have hscaled' : HasDerivAt (selfSimilarSwirlScaleFirst c A H H₁ τ)
      (c * ((-A - 1) * s ^ ((-A - 1) - 1) *
          (-A * H (swirlSimilarityVariable τ s) -
            swirlSimilarityVariable τ s * H₁ (swirlSimilarityVariable τ s)) +
        s ^ (-A - 1) *
          (-A * (H₁ (swirlSimilarityVariable τ s) *
              (-swirlSimilarityVariable τ s / s)) -
            ((-swirlSimilarityVariable τ s / s) * H₁ (swirlSimilarityVariable τ s) +
              swirlSimilarityVariable τ s *
                (H₂ (swirlSimilarityVariable τ s) *
                  (-swirlSimilarityVariable τ s / s)))))) s := by
    convert! hscaled using 1
    funext u
    simp [selfSimilarSwirlScaleFirst]
    ring_nf
  exact hscaled'.congr_deriv (by
    unfold selfSimilarSwirlScaleSecond
    have hpow12 : s ^ (-A - 1) = s ^ ((-A - 1) - 1) * s := by
      calc
        s ^ (-A - 1) = s ^ (((-A - 1) - 1) + 1) := by
          congr 1
          ring
        _ = s ^ ((-A - 1) - 1) * s ^ (1 : ℝ) := Real.rpow_add hs _ _
        _ = s ^ ((-A - 1) - 1) * s := by rw [Real.rpow_one]
    rw [hpow12]
    field_simp [hs.ne']
    ring)

/-- Radial substitution `s = r²/2`. -/
def radialSwirlProfile (c A : ℝ) (H : ℝ → ℝ) (τ r : ℝ) : ℝ :=
  selfSimilarSwirlProfile c A H τ (r ^ 2 / 2)

def radialSwirlFirst (c A : ℝ) (H H₁ : ℝ → ℝ) (τ r : ℝ) : ℝ :=
  r * selfSimilarSwirlScaleFirst c A H H₁ τ (r ^ 2 / 2)

def radialSwirlSecond (c A : ℝ) (H H₁ H₂ : ℝ → ℝ) (τ r : ℝ) : ℝ :=
  selfSimilarSwirlScaleFirst c A H H₁ τ (r ^ 2 / 2) +
    r ^ 2 * selfSimilarSwirlScaleSecond c A H H₁ H₂ τ (r ^ 2 / 2)

theorem hasDerivAt_radialScale (r : ℝ) :
    HasDerivAt (fun ρ : ℝ ↦ ρ ^ 2 / 2) r r := by
  have h := ((hasDerivAt_id r).pow 2).div_const 2
  have h' : HasDerivAt (fun ρ : ℝ ↦ ρ ^ 2 / 2)
      ((2 : ℝ) * r ^ (2 - 1) * 1 / 2) r := by
    convert! h using 1
  exact h'.congr_deriv (by norm_num)

theorem hasDerivAt_radialSwirlProfile
    {c A τ r : ℝ} {H H₁ : ℝ → ℝ} (hr : 0 < r)
    (hH : HasDerivAt H
      (H₁ (swirlSimilarityVariable τ (r ^ 2 / 2)))
      (swirlSimilarityVariable τ (r ^ 2 / 2))) :
    HasDerivAt (radialSwirlProfile c A H τ)
      (radialSwirlFirst c A H H₁ τ r) r := by
  have hs : 0 < r ^ 2 / 2 := by positivity
  have hscale := hasDerivAt_selfSimilarSwirlProfile_scale (c := c) (A := A)
    (τ := τ) hs hH
  have hcomp := hscale.comp r (hasDerivAt_radialScale r)
  have hcomp' : HasDerivAt (radialSwirlProfile c A H τ)
      (selfSimilarSwirlScaleFirst c A H H₁ τ (r ^ 2 / 2) * r) r := by
    convert! hcomp using 1
  exact hcomp'.congr_deriv (by unfold radialSwirlFirst; ring)

theorem hasDerivAt_radialSwirlFirst
    {c A τ r : ℝ} {H H₁ H₂ : ℝ → ℝ} (hr : 0 < r)
    (hH : HasDerivAt H
      (H₁ (swirlSimilarityVariable τ (r ^ 2 / 2)))
      (swirlSimilarityVariable τ (r ^ 2 / 2)))
    (hH₁ : HasDerivAt H₁
      (H₂ (swirlSimilarityVariable τ (r ^ 2 / 2)))
      (swirlSimilarityVariable τ (r ^ 2 / 2))) :
    HasDerivAt (radialSwirlFirst c A H H₁ τ)
      (radialSwirlSecond c A H H₁ H₂ τ r) r := by
  have hs : 0 < r ^ 2 / 2 := by positivity
  have hsecond := hasDerivAt_selfSimilarSwirlScaleFirst_scale (c := c) (A := A)
    (τ := τ) hs hH hH₁
  have hcomp := hsecond.comp r (hasDerivAt_radialScale r)
  have hprod := (hasDerivAt_id r).mul hcomp
  have hprod' : HasDerivAt (radialSwirlFirst c A H H₁ τ)
      (selfSimilarSwirlScaleFirst c A H H₁ τ (r ^ 2 / 2) +
        r * (selfSimilarSwirlScaleSecond c A H H₁ H₂ τ (r ^ 2 / 2) * r)) r := by
    convert! hprod using 1
    all_goals simp
  exact hprod'.congr_deriv (by unfold radialSwirlSecond; ring)

/-- Physical substitution `τ = 1-t`. -/
def physicalSwirlProfile (c A : ℝ) (H : ℝ → ℝ) (r t : ℝ) : ℝ :=
  radialSwirlProfile c A H (1 - t) r

theorem hasDerivAt_physicalSwirlProfile_time
    {c A r t : ℝ} {H H₁ : ℝ → ℝ} (hr : 0 < r)
    (hH : HasDerivAt H
      (H₁ (swirlSimilarityVariable (1 - t) (r ^ 2 / 2)))
      (swirlSimilarityVariable (1 - t) (r ^ 2 / 2))) :
    HasDerivAt (physicalSwirlProfile c A H r)
      (selfSimilarSwirlTimeFirst c A H₁ (1 - t) (r ^ 2 / 2)) t := by
  have hs : 0 < r ^ 2 / 2 := by positivity
  have htau := hasDerivAt_selfSimilarSwirlProfile_tau (c := c) (A := A)
    (τ := 1 - t) hs hH
  have hsub : HasDerivAt (fun u : ℝ ↦ 1 - u) (-1) t := by
    convert! (hasDerivAt_const t 1).sub (hasDerivAt_id t) using 1
    all_goals norm_num
  have hcomp := htau.comp t hsub
  have hcomp' : HasDerivAt (physicalSwirlProfile c A H r)
      ((-selfSimilarSwirlTimeFirst c A H₁ (1 - t) (r ^ 2 / 2)) * (-1)) t := by
    convert! hcomp using 1
  exact hcomp'.congr_deriv (by ring)

/-- Radial second-order operator after the substitution `s = r²/2`. -/
theorem radialSwirlOperator_eq_scaleOperator
    {c A τ r : ℝ} {H H₁ H₂ : ℝ → ℝ} (hr : r ≠ 0) :
    radialSwirlSecond c A H H₁ H₂ τ r +
        r⁻¹ * radialSwirlFirst c A H H₁ τ r -
        r⁻¹ ^ 2 * radialSwirlProfile c A H τ r =
      2 * (r ^ 2 / 2) * selfSimilarSwirlScaleSecond c A H H₁ H₂ τ (r ^ 2 / 2) +
        2 * selfSimilarSwirlScaleFirst c A H H₁ τ (r ^ 2 / 2) -
        selfSimilarSwirlProfile c A H τ (r ^ 2 / 2) / (2 * (r ^ 2 / 2)) := by
  simp [radialSwirlSecond, radialSwirlFirst, radialSwirlProfile]
  field_simp [hr]
  ring

theorem selfSimilarSwirl_scaleOperator_eq
    {c A τ s : ℝ} {H H₁ H₂ : ℝ → ℝ} (hs : 0 < s) :
    2 * s * selfSimilarSwirlScaleSecond c A H H₁ H₂ τ s +
        2 * selfSimilarSwirlScaleFirst c A H H₁ τ s -
        selfSimilarSwirlProfile c A H τ s / (2 * s) =
      2 * c * s ^ (-A - 1) *
        (swirlSimilarityVariable τ s ^ 2 * H₂ (swirlSimilarityVariable τ s) +
          (2 * A + 1) * swirlSimilarityVariable τ s * H₁ (swirlSimilarityVariable τ s) +
          (A ^ 2 - 1 / 4) * H (swirlSimilarityVariable τ s)) := by
  simp [selfSimilarSwirlScaleSecond, selfSimilarSwirlScaleFirst,
    selfSimilarSwirlProfile]
  have hpow01 : s ^ (-A) = s ^ (-A - 1) * s := by
    calc
      s ^ (-A) = s ^ ((-A - 1) + 1) := by
        congr 1
        ring
      _ = s ^ (-A - 1) * s ^ (1 : ℝ) := Real.rpow_add hs _ _
      _ = s ^ (-A - 1) * s := by rw [Real.rpow_one]
  have hpow12 : s ^ (-A - 1) = s ^ ((-A - 1) - 1) * s := by
    calc
      s ^ (-A - 1) = s ^ (((-A - 1) - 1) + 1) := by
        congr 1
        ring
      _ = s ^ ((-A - 1) - 1) * s ^ (1 : ℝ) := Real.rpow_add hs _ _
      _ = s ^ ((-A - 1) - 1) * s := by rw [Real.rpow_one]
  rw [hpow01, hpow12]
  field_simp [hs.ne']
  ring

/-- Lemma A.6 cancellation: profile ODE implies the self-similar swirl heat equation. -/
theorem selfSimilarSwirl_time_eq_scaleOperator_of_ode
    {c A τ s : ℝ} {H H₁ H₂ : ℝ → ℝ} (hs : 0 < s)
    (hODE : swirlHeatProfileODE A (swirlSimilarityVariable τ s)
      (H (swirlSimilarityVariable τ s)) (H₁ (swirlSimilarityVariable τ s))
      (H₂ (swirlSimilarityVariable τ s)) = 0) :
    selfSimilarSwirlTimeFirst c A H₁ τ s =
      2 * s * selfSimilarSwirlScaleSecond c A H H₁ H₂ τ s +
        2 * selfSimilarSwirlScaleFirst c A H H₁ τ s -
        selfSimilarSwirlProfile c A H τ s / (2 * s) := by
  rw [selfSimilarSwirl_scaleOperator_eq hs]
  simp [selfSimilarSwirlTimeFirst, swirlHeatProfileODE] at hODE ⊢
  linear_combination
    (-2 * c * s ^ (-A - 1)) * hODE

/-- Pointwise physical radial heat equation, expressed through certified derivative values. -/
theorem physicalSwirl_time_eq_radialOperator_of_ode
    {c A r t : ℝ} {H H₁ H₂ : ℝ → ℝ} (hr : 0 < r)
    (hODE : swirlHeatProfileODE A
      (swirlSimilarityVariable (1 - t) (r ^ 2 / 2))
      (H (swirlSimilarityVariable (1 - t) (r ^ 2 / 2)))
      (H₁ (swirlSimilarityVariable (1 - t) (r ^ 2 / 2)))
      (H₂ (swirlSimilarityVariable (1 - t) (r ^ 2 / 2))) = 0) :
    selfSimilarSwirlTimeFirst c A H₁ (1 - t) (r ^ 2 / 2) =
      radialSwirlSecond c A H H₁ H₂ (1 - t) r +
        r⁻¹ * radialSwirlFirst c A H H₁ (1 - t) r -
        r⁻¹ ^ 2 * physicalSwirlProfile c A H r t := by
  have hs : 0 < r ^ 2 / 2 := by positivity
  rw [physicalSwirlProfile, radialSwirlOperator_eq_scaleOperator hr.ne']
  exact selfSimilarSwirl_time_eq_scaleOperator_of_ode hs hODE

end

end GaloisForLFunctions.HTGeometry.NavierStokesSelfSimilarSwirlHeat
