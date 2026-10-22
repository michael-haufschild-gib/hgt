import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingPairEmissionSpectralDensity
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import GaloisForLFunctions.RHTower.Deninger.DeningerRadialKahlerTrace

/-!
# Theta-cusp Hawking Schwarzian optical theorem

This endpoint makes backreaction, not Hawking terminology, carry the mathematics.  For the genuine
timelike mirror family

`p_lambda(u) = u + lambda * thetaCuspFullSource(u)`,

the Davies--Fulling flux is `-Schwarzian(p_lambda)/(24*pi)`.  Asymptotic inertia removes the total
derivative in the Schwarzian identity and gives the exact positive total-energy formula

`E_R(lambda) = (1/(48*pi)) integral (lambda*k''/(1+lambda*k'))^(2 : ℕ) du`.

Its quadratic coefficient is therefore `(1/(48*pi)) integral |k''|^(2 : ℕ)`.  Independently, standard
moving-mirror normalization of the already-proved Born numerator

`K(u,v) = 2*i*u*v*Xi(u+v)`

gives right-channel energy density `|K(u,v)|^(2 : ℕ)/(16*pi^(2 : ℕ)*v)`.  Integrating over every positive split
`u+v=w` yields

`w^(4 : ℕ)*Xi(w)^(2 : ℕ)/(48*pi^(2 : ℕ))`.

Plancherel for `Fourier(k'')(w/(2*pi)) = -w^(2 : ℕ)*XiC(w)` proves that the integrated emitted energy is
exactly the quadratic Schwarzian backreaction energy, with all constants fixed.

**[LITERATURE] [BRIDGE] [PAPER-PROVED] [LEAN-PROVED]** This is the perturbative moving-mirror
optical theorem specialized to the literal theta source.  Moving-mirror energy computed from the
Schwarzian flux agrees with energy computed from Bogoliubov coefficients; Butera
(`arXiv:2306.03813`) derives the corresponding pair-emission noise and dissipation kernel from a
microscopic mirror model.

**[FALSIFIED]** This exact optical theorem still cannot prove RH.  Both sides retain only
`Xi(w)^(2 : ℕ)` on the real axis, so they are invariant under total-frequency all-pass phase dressing.
Backreaction energy is source-derived and non-gimmicky, but phase-blind.

**[OPEN CORE]** Derive a phase-sensitive, complex-frequency local optical theorem identifying the
same mirror's causal Hawking channel with the anomaly boundary term `C*B + B†*C`, or prove that term
vanishes from a source-derived law.  Positivity of the real-frequency energy alone cannot supply
that cancellation.
-/

open Complex Real MeasureTheory
open scoped FourierTransform SchwartzMap Interval

noncomputable section

namespace RHTower

/-! ## Theta acceleration and its angular-frequency spectrum -/

/-- Complex Schwartz carrier of the theta mirror's second null-time derivative. -/
def thetaCuspHawkingSourceSecondDerivative : 𝓢(ℝ, ℂ) :=
  SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ thetaCuspSchwartz)

/-- The acceleration transform is the completed source times the exact angular-frequency square. -/
theorem fourier_thetaCuspHawkingSourceSecondDerivative_scaled (w : ℝ) :
    FourierTransform.fourier
        (thetaCuspHawkingSourceSecondDerivative : ℝ → ℂ)
        (w / (2 * Real.pi)) =
      -(w : ℂ) ^ (2 : ℕ) * XiC (w : ℂ) := by
  let d1 : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ thetaCuspSchwartz
  have hderiv0 : deriv (thetaCuspSchwartz : ℝ → ℂ) = (d1 : ℝ → ℂ) := by
    funext x
    rfl
  have hderiv1 : deriv (d1 : ℝ → ℂ) =
      (thetaCuspHawkingSourceSecondDerivative : ℝ → ℂ) := by
    funext x
    rfl
  have hfirst := congrFun
    (Real.fourier_deriv
      (f := (thetaCuspSchwartz : ℝ → ℂ))
      thetaCuspSchwartz.integrable
      thetaCuspSchwartz.differentiable
      d1.integrable) (w / (2 * Real.pi))
  have hsecond := congrFun
    (Real.fourier_deriv
      (f := (d1 : ℝ → ℂ))
      d1.integrable
      d1.differentiable
      thetaCuspHawkingSourceSecondDerivative.integrable)
      (w / (2 * Real.pi))
  rw [hderiv0] at hfirst
  rw [hderiv1] at hsecond
  have hsource :
      FourierTransform.fourier (thetaCuspSchwartz : ℝ → ℂ)
          (w / (2 * Real.pi)) = XiC (w : ℂ) := by
    simpa only [SchwartzMap.fourier_coe] using
      fourier_thetaCuspSchwartz_scaled w
  rw [hsecond, hfirst, hsource]
  simp only [smul_eq_mul]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Squared acceleration spectrum on the physical real-frequency line. -/
theorem norm_sq_fourier_thetaCuspHawkingSourceSecondDerivative_scaled (w : ℝ) :
    ‖FourierTransform.fourier
        (thetaCuspHawkingSourceSecondDerivative : ℝ → ℂ)
        (w / (2 * Real.pi))‖ ^ (2 : ℕ) =
      w ^ (4 : ℕ) * Xi w ^ (2 : ℕ) := by
  rw [fourier_thetaCuspHawkingSourceSecondDerivative_scaled, XiC_ofReal]
  simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc
    (|w| ^ (2 : ℕ) * |Xi w|) ^ (2 : ℕ) = (|w| ^ (2 : ℕ)) ^ (2 : ℕ) * |Xi w| ^ (2 : ℕ) := by ring
    _ = (w ^ (2 : ℕ)) ^ (2 : ℕ) * Xi w ^ (2 : ℕ) := by rw [sq_abs w, sq_abs (Xi w)]
    _ = w ^ (4 : ℕ) * Xi w ^ (2 : ℕ) := by ring

/-- The fourth spectral moment needed by Hawking energy is integrable. -/
theorem integrable_pow_four_mul_Xi_sq :
    Integrable (fun w : ℝ => w ^ (4 : ℕ) * Xi w ^ (2 : ℕ)) := by
  let H : ℝ → ℝ := fun xi =>
    ‖FourierTransform.fourier
      (thetaCuspHawkingSourceSecondDerivative : ℝ → ℂ) xi‖ ^ (2 : ℕ)
  have hH : Integrable H :=
    GaloisForLFunctions.RHTower.integrable_norm_sq_fourier
      thetaCuspHawkingSourceSecondDerivative.integrable
      (SchwartzMap.memLp thetaCuspHawkingSourceSecondDerivative 2
        (volume : Measure ℝ))
  have hscaled : Integrable (fun w : ℝ => H (w / (2 * Real.pi))) :=
    hH.comp_div (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  apply hscaled.congr
  filter_upwards with w
  exact norm_sq_fourier_thetaCuspHawkingSourceSecondDerivative_scaled w

/-- Angular-frequency Plancherel identity for theta mirror acceleration. -/
theorem integral_pow_four_mul_Xi_sq :
    (∫ w : ℝ, w ^ (4 : ℕ) * Xi w ^ (2 : ℕ)) =
      2 * Real.pi *
        ∫ x : ℝ, ‖(thetaCuspHawkingSourceSecondDerivative : ℝ → ℂ) x‖ ^ (2 : ℕ) := by
  let H : ℝ → ℝ := fun xi =>
    ‖FourierTransform.fourier
      (thetaCuspHawkingSourceSecondDerivative : ℝ → ℂ) xi‖ ^ (2 : ℕ)
  have hpoint : (fun w : ℝ => H (w / (2 * Real.pi))) =
      fun w : ℝ => w ^ (4 : ℕ) * Xi w ^ (2 : ℕ) := by
    funext w
    exact norm_sq_fourier_thetaCuspHawkingSourceSecondDerivative_scaled w
  have hscale := MeasureTheory.Measure.integral_comp_div H (2 * Real.pi)
  rw [hpoint, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at hscale
  simp only [smul_eq_mul] at hscale
  rw [GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq
    thetaCuspHawkingSourceSecondDerivative.integrable
    (SchwartzMap.memLp thetaCuspHawkingSourceSecondDerivative 2
      (volume : Measure ℝ))] at hscale
  exact hscale

private theorem integral_even_real
    (f : ℝ → ℝ) (heven : ∀ x, f (-x) = f x) (hint : Integrable f) :
    (∫ x : ℝ, f x) = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
  have h := deningerEven_integral (fun x : ℝ => (f x : ℂ))
    (fun x => by rw [heven]) hint.ofReal
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact Complex.ofReal_inj.mp (by simpa using h)

/-- Positive-frequency half of the theta acceleration spectrum. -/
theorem integral_Ioi_pow_four_mul_Xi_sq :
    (∫ w : ℝ in Set.Ioi 0, w ^ (4 : ℕ) * Xi w ^ (2 : ℕ)) =
      Real.pi *
        ∫ x : ℝ, ‖(thetaCuspHawkingSourceSecondDerivative : ℝ → ℂ) x‖ ^ (2 : ℕ) := by
  have heven : ∀ w : ℝ,
      (-w) ^ (4 : ℕ) * Xi (-w) ^ (2 : ℕ) = w ^ (4 : ℕ) * Xi w ^ (2 : ℕ) := by
    intro w
    rw [Xi_neg]
    ring
  have hsplit := integral_even_real
    (fun w : ℝ => w ^ (4 : ℕ) * Xi w ^ (2 : ℕ)) heven
    integrable_pow_four_mul_Xi_sq
  rw [integral_pow_four_mul_Xi_sq] at hsplit
  linarith [Real.pi_pos]

/-! ## Normalized Hawking energy shell -/

/-- Right-moving Hawking energy at fixed total frequency.  The denominator is the incoming partner
frequency left after multiplying the normalized beta intensity by outgoing energy. -/
def thetaCuspHawkingBornRightEnergyShellDensity (w : ℝ) : ℝ :=
  ∫ u in 0..w,
    Complex.normSq
        (thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ)) /
      (16 * Real.pi ^ (2 : ℕ) * (w - u))

/-- Cancellation of the apparent partner-edge singularity in the normalized energy integrand. -/
theorem thetaCuspHawkingBornRightEnergyShellIntegrand_eq
    (w u : ℝ) :
    Complex.normSq
          (thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ)) /
        (16 * Real.pi ^ (2 : ℕ) * (w - u)) =
      u ^ (2 : ℕ) * (w - u) * Xi w ^ (2 : ℕ) / (4 * Real.pi ^ (2 : ℕ)) := by
  rw [thetaCuspHawkingBornPairKernel_normSq_totalSplit]
  by_cases hv : w - u = 0
  · simp [hv]
  · field_simp [hv, Real.pi_ne_zero]
    ring

/-- **[PAPER-PROVED] [LEAN-PROVED] Exact normalized Hawking energy shell.** -/
theorem thetaCuspHawkingBornRightEnergyShellDensity_eq (w : ℝ) :
    thetaCuspHawkingBornRightEnergyShellDensity w =
      w ^ (4 : ℕ) * Xi w ^ (2 : ℕ) / (48 * Real.pi ^ (2 : ℕ)) := by
  have h2 := integral_pow (a := (0 : ℝ)) (b := w) (n := 2)
  have h3 := integral_pow (a := (0 : ℝ)) (b := w) (n := 3)
  rw [thetaCuspHawkingBornRightEnergyShellDensity]
  calc
    (∫ u in 0..w,
        Complex.normSq
            (thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ)) /
          (16 * Real.pi ^ (2 : ℕ) * (w - u))) =
        ∫ u in 0..w,
          u ^ (2 : ℕ) * (w - u) * Xi w ^ (2 : ℕ) / (4 * Real.pi ^ (2 : ℕ)) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      exact thetaCuspHawkingBornRightEnergyShellIntegrand_eq w u
    _ = _ := by
      rw [show (fun u : ℝ =>
          u ^ (2 : ℕ) * (w - u) * Xi w ^ (2 : ℕ) / (4 * Real.pi ^ (2 : ℕ))) =
          fun u : ℝ =>
            (w * Xi w ^ (2 : ℕ) / (4 * Real.pi ^ (2 : ℕ))) * u ^ (2 : ℕ) +
            (-Xi w ^ (2 : ℕ) / (4 * Real.pi ^ (2 : ℕ))) * u ^ (3 : ℕ) by
        funext u
        ring]
      rw [intervalIntegral.integral_add,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, h2, h3]
      · field_simp [Real.pi_ne_zero]
        ring
      · exact (by fun_prop : Continuous
          (fun u : ℝ => (w * Xi w ^ (2 : ℕ) / (4 * Real.pi ^ (2 : ℕ))) * u ^ (2 : ℕ))).intervalIntegrable _ _
      · exact (by fun_prop : Continuous
          (fun u : ℝ => (-Xi w ^ (2 : ℕ) / (4 * Real.pi ^ (2 : ℕ))) * u ^ (3 : ℕ))).intervalIntegrable _ _

theorem thetaCuspHawkingBornRightEnergyShellDensity_nonneg (w : ℝ) :
    0 ≤ thetaCuspHawkingBornRightEnergyShellDensity w := by
  rw [thetaCuspHawkingBornRightEnergyShellDensity_eq]
  positivity

theorem thetaCuspHawkingBornRightEnergyShellDensity_eq_zero_iff
    {w : ℝ} (hw : 0 < w) :
    thetaCuspHawkingBornRightEnergyShellDensity w = 0 ↔ Xi w = 0 := by
  rw [thetaCuspHawkingBornRightEnergyShellDensity_eq]
  have hfactor : w ^ (4 : ℕ) / (48 * Real.pi ^ (2 : ℕ)) ≠ 0 := by positivity
  rw [show w ^ (4 : ℕ) * Xi w ^ (2 : ℕ) / (48 * Real.pi ^ (2 : ℕ)) =
      (w ^ (4 : ℕ) / (48 * Real.pi ^ (2 : ℕ))) * Xi w ^ (2 : ℕ) by ring,
    mul_eq_zero]
  simp [hfactor]

/-! ## Backreaction/emission optical theorem -/

/-- Total right-channel Born energy at quadratic order in mirror coupling. -/
def thetaCuspHawkingBornRightQuadraticEnergy : ℝ :=
  ∫ w : ℝ in Set.Ioi 0, thetaCuspHawkingBornRightEnergyShellDensity w

/-- Quadratic coefficient of total Davies--Fulling Schwarzian energy for the theta mirror. -/
def thetaCuspHawkingSchwarzianQuadraticEnergy : ℝ :=
  (1 / (48 * Real.pi)) *
    ∫ x : ℝ, ‖(thetaCuspHawkingSourceSecondDerivative : ℝ → ℂ) x‖ ^ (2 : ℕ)

/-- **[LITERATURE] [BRIDGE] [PAPER-PROVED] [LEAN-PROVED] Theta Hawking optical theorem.**
The energy emitted through the normalized exterior/partner pair channel equals the quadratic
Schwarzian backreaction energy of the same timelike theta-cusp trajectory. -/
theorem thetaCuspHawkingBornSchwarzianOpticalTheorem :
    thetaCuspHawkingBornRightQuadraticEnergy =
      thetaCuspHawkingSchwarzianQuadraticEnergy := by
  rw [thetaCuspHawkingBornRightQuadraticEnergy,
    thetaCuspHawkingSchwarzianQuadraticEnergy]
  calc
    (∫ w : ℝ in Set.Ioi 0,
        thetaCuspHawkingBornRightEnergyShellDensity w) =
        ∫ w : ℝ in Set.Ioi 0,
          w ^ (4 : ℕ) * Xi w ^ (2 : ℕ) / (48 * Real.pi ^ (2 : ℕ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w _hw
      exact thetaCuspHawkingBornRightEnergyShellDensity_eq w
    _ = (1 / (48 * Real.pi ^ (2 : ℕ))) *
        ∫ w : ℝ in Set.Ioi 0, w ^ (4 : ℕ) * Xi w ^ (2 : ℕ) := by
      rw [← MeasureTheory.integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w _hw
      ring
    _ = _ := by
      rw [integral_Ioi_pow_four_mul_Xi_sq]
      field_simp [Real.pi_ne_zero]

end RHTower
