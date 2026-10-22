import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerPairLogSpectrum

/-!
# The orientation current of an ordered theta pair

The Hedenmalm centre weight `r sinh (a r)` becomes, after `r = 2u`, the antisymmetric combination
`u (e^(2au) - e^(-2au))`.  Since the exponential weight `e^((2σ-1)u)` of the pair currents
corresponds to `σ = a + 1/2`, the two halves are the centre-weighted current at `σ` and at
`1 - σ`: **the `sinh` is exactly antisymmetrisation under `σ ↔ 1 - σ`.**

On the critical aperture `0 < a < 1/2` both exponents are positive, so both closed forms apply and
the ordered-pair orientation current is an explicit antisymmetric combination of the two universal
kernels.  This fixes the shape any positivity argument for the route must have: a single-`σ`
positivity statement cannot suffice.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

theorem integrable_center_mul_exp_mul_thetaCuspSourceTerm_pair {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    Integrable (fun u : ℝ => u * Real.exp ((2 * σ - 1) * u) *
      (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) := by
  have hI1 := integrable_log_scale_mul_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t
  have hI2 := integrable_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t
  have hsum : Integrable (fun u : ℝ =>
      (1 / 2) * (Real.log (thetaCuspWignerAtomScale n m u) * Real.exp ((2 * σ - 1) * u) *
          (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) -
        (Real.log (2 * Real.pi * n * m) / 2) * (Real.exp ((2 * σ - 1) * u) *
          (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m))) :=
    (hI1.const_mul _).sub (hI2.const_mul _)
  refine hsum.congr (Filter.Eventually.of_forall fun u => ?_)
  show (1 / 2) * (Real.log (thetaCuspWignerAtomScale n m u) * Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) -
      (Real.log (2 * Real.pi * n * m) / 2) * (Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) =
    u * Real.exp ((2 * σ - 1) * u) *
      (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)
  rw [log_thetaCuspWignerAtomScale hn hm u]
  ring

/-- The ordered-pair orientation current: the centre weight antisymmetrised by `sinh`, which is
the weight of the Hedenmalm center-mixed density after `r = 2u`. -/
def thetaCuspPairOrientationCurrent (a : ℝ) (n m : ℕ) (t : ℝ) : ℝ :=
  ∫ u : ℝ, u * (Real.exp (2 * a * u) - Real.exp (-(2 * a * u))) *
    (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)

/-- **The Hedenmalm centre weight is the `σ ↔ 1−σ` antisymmetrisation.**  On the critical aperture
`0 < a < 1/2` the ordered-pair orientation current is the difference of the centre-weighted
currents at `σ = a + 1/2` and at `1 − σ = 1/2 − a`. -/
theorem thetaCuspPairOrientationCurrent_eq_sub {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    thetaCuspPairOrientationCurrent a n m t =
      (∫ u : ℝ, u * Real.exp ((2 * (a + 1 / 2) - 1) * u) *
          (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) -
        ∫ u : ℝ, u * Real.exp ((2 * (1 / 2 - a) - 1) * u) *
          (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m) := by
  have hp : (0 : ℝ) < a + 1 / 2 := by linarith
  have hq : (0 : ℝ) < 1 / 2 - a := by linarith
  have h1 := integrable_center_mul_exp_mul_thetaCuspSourceTerm_pair hp hn hm t
  have h2 := integrable_center_mul_exp_mul_thetaCuspSourceTerm_pair hq hn hm t
  rw [thetaCuspPairOrientationCurrent, ← integral_sub h1 h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show u * (Real.exp (2 * a * u) - Real.exp (-(2 * a * u))) *
      (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m) =
    u * Real.exp ((2 * (a + 1 / 2) - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m) -
      u * Real.exp ((2 * (1 / 2 - a) - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)
  rw [show (2 * (a + 1 / 2) - 1) * u = 2 * a * u by ring,
    show (2 * (1 / 2 - a) - 1) * u = -(2 * a * u) by ring]
  ring

/-- The orientation current of an ordered pair in closed form: an antisymmetric combination of the
two universal kernels at `σ` and `1 − σ`. -/
theorem thetaCuspPairOrientationCurrent_eq_kernels {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    thetaCuspPairOrientationCurrent a n m t =
      (1 / 2) * ((n : ℝ) ^ (-(a + 1 / 2)) * (m : ℝ) ^ (-(a + 1 / 2))) *
          (thetaCuspWignerPairLogKernel (a + 1 / 2) (2 * t + Real.log n - Real.log m) -
            Real.log (2 * Real.pi * n * m) *
              thetaCuspWignerPairKernel (a + 1 / 2)
                (2 * t + Real.log n - Real.log m)) -
        (1 / 2) * ((n : ℝ) ^ (-(1 / 2 - a)) * (m : ℝ) ^ (-(1 / 2 - a))) *
          (thetaCuspWignerPairLogKernel (1 / 2 - a) (2 * t + Real.log n - Real.log m) -
            Real.log (2 * Real.pi * n * m) *
              thetaCuspWignerPairKernel (1 / 2 - a)
                (2 * t + Real.log n - Real.log m)) := by
  have hp : (0 : ℝ) < a + 1 / 2 := by linarith
  have hq : (0 : ℝ) < 1 / 2 - a := by linarith
  rw [thetaCuspPairOrientationCurrent_eq_sub ha0 ha hn hm t,
    integral_center_mul_exp_mul_thetaCuspSourceTerm_pair_factor hp hn hm t,
    integral_center_mul_exp_mul_thetaCuspSourceTerm_pair_factor hq hn hm t]

/-- **The Hedenmalm radial weight in centre coordinates.**  Substituting `r = 2u` turns the
half-line weight `r sinh (a r)` into `4 u sinh (2 a u)`; no integrability hypothesis is needed. -/
theorem integral_Ioi_radial_sinh_eq (a : ℝ) (f : ℝ → ℝ) :
    (∫ r : ℝ in Ioi 0, r * Real.sinh (a * r) * f (r / 2)) =
      4 * ∫ u : ℝ in Ioi 0, u * Real.sinh (2 * a * u) * f u := by
  have h := integral_comp_mul_left_Ioi
    (fun r : ℝ => r * Real.sinh (a * r) * f (r / 2)) 0 (by norm_num : (0 : ℝ) < 2)
  rw [mul_zero] at h
  have hpt : (∫ u : ℝ in Ioi 0, (2 * u) * Real.sinh (a * (2 * u)) * f ((2 * u) / 2)) =
      2 * ∫ u : ℝ in Ioi 0, u * Real.sinh (2 * a * u) * f u := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [show a * (2 * u) = 2 * a * u by ring, show (2 * u) / 2 = u by ring]
    ring
  rw [hpt, smul_eq_mul] at h
  linarith [h]

end

end RHTower
