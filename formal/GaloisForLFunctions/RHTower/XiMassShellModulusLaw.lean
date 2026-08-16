import GaloisForLFunctions.RHTower.XiMassShellExteriorTail

/-!
# The shell modulus law

The damped shell modulus is antitone in the shell coordinate and, after multiplication by the
cutoff mass `e^{κu}`, is exactly

`K · u^{-1/2} · e^{γ u}`,  `γ = κ/2 − a√(κ²−1)`,  `K = √(2πa) e^{-(1/2 + aκ/q)}/(q√q)`.

These two facts turn the shell prime mass into the leading term of the subthreshold annulus.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

theorem shellModulus_antitone {a kappa u s t : ℝ} (ha : 0 < a) (hkappa : 1 < kappa) (hu : 0 < u)
    (hst : s ≤ t) : shellModulus a kappa u t ≤ shellModulus a kappa u s := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hqu : (0 : ℝ) < shellQ kappa * u := mul_pos hq hu
  have hroot : (0 : ℝ) < Real.sqrt (shellQ kappa * u) := Real.sqrt_pos.2 hqu
  have hden : (0 : ℝ) < shellQ kappa * u * Real.sqrt (shellQ kappa * u) := by positivity
  have hamp : (0 : ℝ) < Real.sqrt (2 * Real.pi * a) * u := by
    have : (0 : ℝ) < Real.sqrt (2 * Real.pi * a) := Real.sqrt_pos.2 (by positivity)
    positivity
  rw [shellModulus, shellModulus, div_le_div_iff₀ hden hden]
  have hexp1 : Real.exp (-((kappa * u + t) / 2)) ≤ Real.exp (-((kappa * u + s) / 2)) :=
    Real.exp_le_exp.2 (by linarith)
  have hexp2 : Real.exp (-(a * (shellQ kappa * u + kappa * t / shellQ kappa)))
      ≤ Real.exp (-(a * (shellQ kappa * u + kappa * s / shellQ kappa))) := by
    refine Real.exp_le_exp.2 ?_
    have hdiv : kappa * s / shellQ kappa ≤ kappa * t / shellQ kappa :=
      div_le_div_of_nonneg_right (by nlinarith) hq.le
    nlinarith [hdiv, ha]
  have hprod : Real.exp (-((kappa * u + t) / 2))
      * Real.exp (-(a * (shellQ kappa * u + kappa * t / shellQ kappa)))
      ≤ Real.exp (-((kappa * u + s) / 2))
        * Real.exp (-(a * (shellQ kappa * u + kappa * s / shellQ kappa))) :=
    mul_le_mul hexp1 hexp2 (Real.exp_pos _).le (Real.exp_pos _).le
  have h1 : Real.sqrt (2 * Real.pi * a) * u
      * (Real.exp (-((kappa * u + t) / 2))
        * Real.exp (-(a * (shellQ kappa * u + kappa * t / shellQ kappa))))
      ≤ Real.sqrt (2 * Real.pi * a) * u
        * (Real.exp (-((kappa * u + s) / 2))
          * Real.exp (-(a * (shellQ kappa * u + kappa * s / shellQ kappa)))) :=
    mul_le_mul_of_nonneg_left hprod hamp.le
  have h2 := mul_le_mul_of_nonneg_right h1 hden.le
  nlinarith [h2]

theorem xiMassBesselConeExponent_eq_shellQ (a kappa : ℝ) :
    xiMassBesselConeExponent a kappa = a * shellQ kappa - kappa / 2 := rfl

/-- The amplitude constant of the shell modulus law. -/
def shellAmplitude (a kappa s : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * a) * Real.exp (-(s / 2 + a * kappa * s / shellQ kappa))
    / (shellQ kappa * Real.sqrt (shellQ kappa))

theorem shellAmplitude_pos {a kappa s : ℝ} (ha : 0 < a) (hkappa : 1 < kappa) :
    0 < shellAmplitude a kappa s := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hroot : (0 : ℝ) < Real.sqrt (shellQ kappa) := Real.sqrt_pos.2 hq
  have hamp : (0 : ℝ) < Real.sqrt (2 * Real.pi * a) := Real.sqrt_pos.2 (by positivity)
  rw [shellAmplitude]
  positivity

/-- **The shell modulus law.**  Multiplied by the cutoff mass, the shell modulus is exactly the
stationary-phase amplitude times `u^{-1/2} e^{γu}`. -/
theorem shellModulus_mul_exp {a kappa u s : ℝ} (ha : 0 < a) (hkappa : 1 < kappa) (hu : 0 < u) :
    shellModulus a kappa u s * Real.exp (kappa * u)
      = shellAmplitude a kappa s
        * (Real.exp (-(xiMassBesselConeExponent a kappa) * u) / Real.sqrt u) := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hqroot : Real.sqrt (shellQ kappa * u) = Real.sqrt (shellQ kappa) * Real.sqrt u :=
    Real.sqrt_mul hq.le u
  have hrootq : (0 : ℝ) < Real.sqrt (shellQ kappa) := Real.sqrt_pos.2 hq
  have hrootu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu
  have hqsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  have hexpcomb : Real.exp (-((kappa * u + s) / 2))
      * Real.exp (-(a * (shellQ kappa * u + kappa * s / shellQ kappa)))
      * Real.exp (kappa * u)
      = Real.exp (-(s / 2 + a * kappa * s / shellQ kappa))
        * Real.exp (-(xiMassBesselConeExponent a kappa) * u) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, xiMassBesselConeExponent_eq_shellQ]
    congr 1
    field_simp
    ring
  have hkey : Real.sqrt (2 * Real.pi * a) * u
      * Real.exp (-((kappa * u + s) / 2))
      * Real.exp (-(a * (shellQ kappa * u + kappa * s / shellQ kappa)))
      / (shellQ kappa * u * (Real.sqrt (shellQ kappa) * Real.sqrt u))
      * Real.exp (kappa * u)
      = Real.sqrt (2 * Real.pi * a) * u
        * (Real.exp (-((kappa * u + s) / 2))
          * Real.exp (-(a * (shellQ kappa * u + kappa * s / shellQ kappa)))
          * Real.exp (kappa * u))
        / (shellQ kappa * u * (Real.sqrt (shellQ kappa) * Real.sqrt u)) := by ring
  rw [shellModulus, shellAmplitude, hqroot, hkey, hexpcomb]
  field_simp

end

end RHTower
