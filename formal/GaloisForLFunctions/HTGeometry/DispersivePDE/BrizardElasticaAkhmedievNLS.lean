import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaBreatherMaxima
import Mathlib.Tactic

/-!
# Certified Akhmediev breather jet

The printed Akhmediev quotient is differentiated in time and twice in space.  This supplies the
calculus-bearing `ComplexEvolutionJet2` needed to test the formula against focusing cubic NLS.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def akhmedievCore (φ : BreatherAngle) (ξ τ : ℝ) : ℂ :=
  -(akhmedievNumerator φ ξ τ / (akhmedievDenominator φ ξ τ : ℂ))

noncomputable def akhmedievDenominatorT (φ : BreatherAngle) (τ : ℝ) : ℝ :=
  akhmedievOmega φ * Real.sinh (akhmedievOmega φ * τ)

noncomputable def akhmedievDenominatorX (φ : BreatherAngle) (ξ : ℝ) : ℝ :=
  Real.cos (φ : ℝ) * akhmedievWaveNumber φ *
    Real.sin (akhmedievWaveNumber φ * ξ)

noncomputable def akhmedievDenominatorXX (φ : BreatherAngle) (ξ : ℝ) : ℝ :=
  Real.cos (φ : ℝ) * akhmedievWaveNumber φ ^ (2 : ℕ) *
    Real.cos (akhmedievWaveNumber φ * ξ)

noncomputable def akhmedievNumeratorT (φ : BreatherAngle) (τ : ℝ) : ℂ :=
  ((akhmedievOmega φ * Real.sinh (akhmedievOmega φ * τ) *
      Real.cos (2 * (φ : ℝ)) : ℝ) : ℂ) -
    Complex.I *
      ((akhmedievOmega φ * Real.cosh (akhmedievOmega φ * τ) *
        Real.sin (2 * (φ : ℝ)) : ℝ) : ℂ)

noncomputable def akhmedievNumeratorX (φ : BreatherAngle) (ξ : ℝ) : ℂ :=
  (akhmedievDenominatorX φ ξ : ℂ)

noncomputable def akhmedievNumeratorXX (φ : BreatherAngle) (ξ : ℝ) : ℂ :=
  (akhmedievDenominatorXX φ ξ : ℂ)

noncomputable def akhmedievCoreT (φ : BreatherAngle) (ξ τ : ℝ) : ℂ :=
  -((akhmedievNumeratorT φ τ * (akhmedievDenominator φ ξ τ : ℂ) -
      akhmedievNumerator φ ξ τ * (akhmedievDenominatorT φ τ : ℂ)) /
    (akhmedievDenominator φ ξ τ : ℂ) ^ (2 : ℕ))

noncomputable def akhmedievCoreX (φ : BreatherAngle) (ξ τ : ℝ) : ℂ :=
  -((akhmedievNumeratorX φ ξ * (akhmedievDenominator φ ξ τ : ℂ) -
      akhmedievNumerator φ ξ τ * (akhmedievDenominatorX φ ξ : ℂ)) /
    (akhmedievDenominator φ ξ τ : ℂ) ^ (2 : ℕ))

noncomputable def akhmedievCoreXX (φ : BreatherAngle) (ξ τ : ℝ) : ℂ :=
  -(((akhmedievNumeratorXX φ ξ * (akhmedievDenominator φ ξ τ : ℂ) -
        akhmedievNumerator φ ξ τ * (akhmedievDenominatorXX φ ξ : ℂ)) *
        (akhmedievDenominator φ ξ τ : ℂ) ^ (2 : ℕ) -
      (akhmedievNumeratorX φ ξ * (akhmedievDenominator φ ξ τ : ℂ) -
        akhmedievNumerator φ ξ τ * (akhmedievDenominatorX φ ξ : ℂ)) *
        (2 * (akhmedievDenominator φ ξ τ : ℂ) *
          (akhmedievDenominatorX φ ξ : ℂ))) /
    ((akhmedievDenominator φ ξ τ : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ))

theorem hasDerivAt_akhmedievDenominator_time (φ : BreatherAngle) (ξ τ : ℝ) :
    HasDerivAt (fun r => akhmedievDenominator φ ξ r) (akhmedievDenominatorT φ τ) τ := by
  have h := ((Real.hasDerivAt_cosh (akhmedievOmega φ * τ)).comp τ
    ((hasDerivAt_id τ).const_mul (akhmedievOmega φ))).sub_const
      (Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ))
  apply h.congr_deriv
  rw [akhmedievDenominatorT]
  ring

theorem hasDerivAt_akhmedievDenominator_space (φ : BreatherAngle) (ξ τ : ℝ) :
    HasDerivAt (fun y => akhmedievDenominator φ y τ) (akhmedievDenominatorX φ ξ) ξ := by
  have hcos := (Real.hasDerivAt_cos (akhmedievWaveNumber φ * ξ)).comp ξ
    ((hasDerivAt_id ξ).const_mul (akhmedievWaveNumber φ))
  have h := (hasDerivAt_const ξ (Real.cosh (akhmedievOmega φ * τ))).sub
    (hcos.const_mul (Real.cos (φ : ℝ)))
  apply h.congr_deriv
  rw [akhmedievDenominatorX]
  ring

theorem hasDerivAt_akhmedievDenominator_space_one (φ : BreatherAngle) (ξ _τ : ℝ) :
    HasDerivAt (akhmedievDenominatorX φ) (akhmedievDenominatorXX φ ξ) ξ := by
  have h := ((Real.hasDerivAt_sin (akhmedievWaveNumber φ * ξ)).comp ξ
    ((hasDerivAt_id ξ).const_mul (akhmedievWaveNumber φ))).const_mul
      (Real.cos (φ : ℝ) * akhmedievWaveNumber φ)
  apply h.congr_deriv
  rw [akhmedievDenominatorXX]
  ring

theorem hasDerivAt_akhmedievNumerator_time (φ : BreatherAngle) (ξ τ : ℝ) :
    HasDerivAt (fun r => akhmedievNumerator φ ξ r) (akhmedievNumeratorT φ τ) τ := by
  have hcosh := (Real.hasDerivAt_cosh (akhmedievOmega φ * τ)).comp τ
    ((hasDerivAt_id τ).const_mul (akhmedievOmega φ))
  have hsinh := (Real.hasDerivAt_sinh (akhmedievOmega φ * τ)).comp τ
    ((hasDerivAt_id τ).const_mul (akhmedievOmega φ))
  have hreal := (hcosh.const_mul (Real.cos (2 * (φ : ℝ)))).sub_const
    (Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ))
  have himag := hsinh.const_mul (Real.sin (2 * (φ : ℝ)))
  have h := hreal.ofReal_comp.sub (himag.ofReal_comp.const_mul Complex.I)
  have heq : (fun r => akhmedievNumerator φ ξ r) =ᶠ[nhds τ]
      ((fun r => ((Real.cos (2 * (φ : ℝ)) * Real.cosh (akhmedievOmega φ * r) -
          Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ) : ℝ) : ℂ)) -
        fun r => Complex.I *
          ((Real.sin (2 * (φ : ℝ)) * Real.sinh (akhmedievOmega φ * r) : ℝ) : ℂ)) := by
    filter_upwards with r
    simp only [akhmedievNumerator]
    congr 1 <;> push_cast <;> ring
  have hsource := h.congr_of_eventuallyEq heq
  apply hsource.congr_deriv
  simp only [akhmedievNumeratorT]
  push_cast
  ring

theorem hasDerivAt_akhmedievNumerator_space (φ : BreatherAngle) (ξ τ : ℝ) :
    HasDerivAt (fun y => akhmedievNumerator φ y τ) (akhmedievNumeratorX φ ξ) ξ := by
  have hcos := (Real.hasDerivAt_cos (akhmedievWaveNumber φ * ξ)).comp ξ
    ((hasDerivAt_id ξ).const_mul (akhmedievWaveNumber φ))
  have hreal := (hasDerivAt_const ξ
    (Real.cosh (akhmedievOmega φ * τ) * Real.cos (2 * (φ : ℝ)))).sub
      (hcos.const_mul (Real.cos (φ : ℝ)))
  have h := hreal.ofReal_comp.sub
    (hasDerivAt_const ξ
      (Complex.I * ((Real.sinh (akhmedievOmega φ * τ) *
        Real.sin (2 * (φ : ℝ)) : ℝ) : ℂ)))
  apply h.congr_deriv
  rw [akhmedievNumeratorX, akhmedievDenominatorX]
  push_cast
  ring

theorem hasDerivAt_akhmedievNumerator_space_one (φ : BreatherAngle) (ξ _τ : ℝ) :
    HasDerivAt (akhmedievNumeratorX φ) (akhmedievNumeratorXX φ ξ) ξ := by
  exact (hasDerivAt_akhmedievDenominator_space_one φ ξ _τ).ofReal_comp

theorem hasDerivAt_akhmedievCore_time (φ : BreatherAngle) (ξ τ : ℝ) :
    HasDerivAt (fun r => akhmedievCore φ ξ r) (akhmedievCoreT φ ξ τ) τ := by
  have hden := (hasDerivAt_akhmedievDenominator_time φ ξ τ).ofReal_comp
  have h := (hasDerivAt_akhmedievNumerator_time φ ξ τ).div hden
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (akhmedievDenominator_pos φ ξ τ)))
  exact h.neg

theorem hasDerivAt_akhmedievCore_space (φ : BreatherAngle) (ξ τ : ℝ) :
    HasDerivAt (fun y => akhmedievCore φ y τ) (akhmedievCoreX φ ξ τ) ξ := by
  have hden := (hasDerivAt_akhmedievDenominator_space φ ξ τ).ofReal_comp
  have h := (hasDerivAt_akhmedievNumerator_space φ ξ τ).div hden
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (akhmedievDenominator_pos φ ξ τ)))
  exact h.neg

theorem hasDerivAt_akhmedievCore_space_one (φ : BreatherAngle) (ξ τ : ℝ) :
    HasDerivAt (fun y => akhmedievCoreX φ y τ) (akhmedievCoreXX φ ξ τ) ξ := by
  have hn := hasDerivAt_akhmedievNumerator_space φ ξ τ
  have hnn := hasDerivAt_akhmedievNumerator_space_one φ ξ τ
  have hd := (hasDerivAt_akhmedievDenominator_space φ ξ τ).ofReal_comp
  have hdd := (hasDerivAt_akhmedievDenominator_space_one φ ξ τ).ofReal_comp
  have htop := (hnn.mul hd).sub (hn.mul hdd)
  have hdenSq := hd.pow 2
  have hquot := htop.div hdenSq (pow_ne_zero 2
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (akhmedievDenominator_pos φ ξ τ))))
  have hquot' : HasDerivAt
      (fun y => -((akhmedievNumeratorX φ y * (akhmedievDenominator φ y τ : ℂ) -
          akhmedievNumerator φ y τ * (akhmedievDenominatorX φ y : ℂ)) /
        (akhmedievDenominator φ y τ : ℂ) ^ (2 : ℕ)))
      (akhmedievCoreXX φ ξ τ) ξ := by
    apply hquot.neg.congr_deriv
    simp only [akhmedievCoreXX, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply,
      Nat.cast_ofNat]
    field_simp [Complex.ofReal_ne_zero.mpr
      (ne_of_gt (akhmedievDenominator_pos φ ξ τ))]
    ring
  apply hquot'.congr_of_eventuallyEq
  filter_upwards with y
  rw [akhmedievCoreX]

noncomputable def akhmedievBreatherJet (φ : BreatherAngle) : ComplexEvolutionJet2 where
  u := fun τ ξ => akhmedievBreather φ ξ τ
  ut := fun τ ξ =>
    (akhmedievCoreT φ ξ τ * linearPhase 1 0 τ ξ +
      akhmedievCore φ ξ τ * (linearPhase 1 0 τ ξ * Complex.I)) /
        (Real.sqrt 2 : ℂ)
  ux := fun τ ξ =>
    akhmedievCoreX φ ξ τ * linearPhase 1 0 τ ξ / (Real.sqrt 2 : ℂ)
  uxx := fun τ ξ =>
    akhmedievCoreXX φ ξ τ * linearPhase 1 0 τ ξ / (Real.sqrt 2 : ℂ)
  hasDerivAt_time := by
    intro τ ξ
    have h := (hasDerivAt_akhmedievCore_time φ ξ τ).mul
      (hasDerivAt_linearPhase_time 1 0 τ ξ) |>.div_const (Real.sqrt 2 : ℂ)
    have h' : HasDerivAt
        (fun r => akhmedievCore φ ξ r * linearPhase 1 0 r ξ / (Real.sqrt 2 : ℂ))
        ((akhmedievCoreT φ ξ τ * linearPhase 1 0 τ ξ +
          akhmedievCore φ ξ τ * (linearPhase 1 0 τ ξ * Complex.I)) /
            (Real.sqrt 2 : ℂ)) τ := by
      apply h.congr_deriv
      simp
    apply h'.congr_of_eventuallyEq
    filter_upwards with r
    rw [akhmedievBreather, akhmedievCore]
  hasDerivAt_space := by
    intro τ ξ
    have h := (hasDerivAt_akhmedievCore_space φ ξ τ).mul
      (hasDerivAt_linearPhase_space 1 0 τ ξ) |>.div_const (Real.sqrt 2 : ℂ)
    have h' : HasDerivAt
        (fun y => akhmedievCore φ y τ * linearPhase 1 0 τ y / (Real.sqrt 2 : ℂ))
        (akhmedievCoreX φ ξ τ * linearPhase 1 0 τ ξ / (Real.sqrt 2 : ℂ)) ξ := by
      apply h.congr_deriv
      simp
    apply h'.congr_of_eventuallyEq
    filter_upwards with y
    rw [akhmedievBreather, akhmedievCore]
  hasDerivAt_space_one := by
    intro τ ξ
    have h := (hasDerivAt_akhmedievCore_space_one φ ξ τ).mul
      (hasDerivAt_linearPhase_space 1 0 τ ξ) |>.div_const (Real.sqrt 2 : ℂ)
    apply h.congr_deriv
    simp

/-- The quotient core satisfies the carrier-reduced focusing-NLS identity. -/
theorem akhmedievCore_nls_residual (φ : BreatherAngle) (ξ τ : ℝ) :
    Complex.I * akhmedievCoreT φ ξ τ - akhmedievCore φ ξ τ +
        akhmedievCoreXX φ ξ τ +
        ((akhmedievNumeratorSq φ ξ τ /
          akhmedievDenominator φ ξ τ ^ (2 : ℕ) : ℝ) : ℂ) *
          akhmedievCore φ ξ τ = 0 := by
  let d : ℂ := (akhmedievDenominator φ ξ τ : ℂ)
  let n : ℂ := akhmedievNumerator φ ξ τ
  let nt : ℂ := akhmedievNumeratorT φ τ
  let dt : ℂ := (akhmedievDenominatorT φ τ : ℂ)
  let nx : ℂ := akhmedievNumeratorX φ ξ
  let nxx : ℂ := akhmedievNumeratorXX φ ξ
  let dx : ℂ := (akhmedievDenominatorX φ ξ : ℂ)
  let dxx : ℂ := (akhmedievDenominatorXX φ ξ : ℂ)
  let nsq : ℂ := (akhmedievNumeratorSq φ ξ τ : ℂ)
  have hd : d ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (akhmedievDenominator_pos φ ξ τ))
  have halgebra :
      Complex.I * (-((nt * d - n * dt) / d ^ (2 : ℕ))) - (-n / d) +
          (-(((nxx * d - n * dxx) * d ^ (2 : ℕ) -
            (nx * d - n * dx) * (2 * d * dx)) / (d ^ (2 : ℕ)) ^ (2 : ℕ))) +
          (nsq / d ^ (2 : ℕ)) * (-n / d) = 0 := by
    field_simp [hd]
    dsimp [d, n, nt, dt, nx, nxx, dx, dxx, nsq]
    rw [akhmedievNumeratorT, akhmedievNumeratorX, akhmedievNumeratorXX,
      akhmedievDenominatorT, akhmedievDenominatorX, akhmedievDenominatorXX,
      akhmedievNumerator, akhmedievNumeratorSq, akhmedievDenominator,
      akhmedievOmega, akhmedievWaveNumber]
    push_cast
    rw [Complex.cos_two_mul, Complex.sin_two_mul]
    ring_nf
    simp only [Complex.I_sq]
    have hsinh : Complex.sinh
        (Complex.sin ((φ : ℝ) : ℂ) * Complex.cos ((φ : ℝ) : ℂ) * (τ : ℂ) * 2) ^ (2 : ℕ) =
        Complex.cosh
          (Complex.sin ((φ : ℝ) : ℂ) * Complex.cos ((φ : ℝ) : ℂ) * (τ : ℂ) * 2) ^ (2 : ℕ) - 1 := by
      linear_combination -(Complex.cosh_sq_sub_sinh_sq
        (Complex.sin ((φ : ℝ) : ℂ) * Complex.cos ((φ : ℝ) : ℂ) * (τ : ℂ) * 2))
    have hsin : Complex.sin ((φ : ℝ) : ℂ) ^ (2 : ℕ) =
        1 - Complex.cos ((φ : ℝ) : ℂ) ^ (2 : ℕ) := by
      linear_combination Complex.sin_sq_add_cos_sq (((φ : ℝ) : ℂ))
    have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ^ (2 : ℕ) = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hspace :
        Complex.sin
            (Complex.sin ((φ : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) * (ξ : ℂ)) ^ (2 : ℕ) =
          1 - Complex.cos
            (Complex.sin ((φ : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) * (ξ : ℂ)) ^ (2 : ℕ) := by
      linear_combination Complex.sin_sq_add_cos_sq
        (Complex.sin ((φ : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) * (ξ : ℂ))
    have hsinCube : Complex.sin ((φ : ℝ) : ℂ) ^ (3 : ℕ) =
        Complex.sin ((φ : ℝ) : ℂ) *
          (1 - Complex.cos ((φ : ℝ) : ℂ) ^ (2 : ℕ)) := by
      calc
        Complex.sin ((φ : ℝ) : ℂ) ^ (3 : ℕ) =
            Complex.sin ((φ : ℝ) : ℂ) *
              Complex.sin ((φ : ℝ) : ℂ) ^ (2 : ℕ) := by ring
        _ = _ := by rw [hsin]
    have hsinhCube : Complex.sinh
          (Complex.sin ((φ : ℝ) : ℂ) * Complex.cos ((φ : ℝ) : ℂ) * (τ : ℂ) * 2) ^ (3 : ℕ) =
        Complex.sinh
            (Complex.sin ((φ : ℝ) : ℂ) * Complex.cos ((φ : ℝ) : ℂ) * (τ : ℂ) * 2) *
          (Complex.cosh
              (Complex.sin ((φ : ℝ) : ℂ) * Complex.cos ((φ : ℝ) : ℂ) * (τ : ℂ) * 2) ^ (2 : ℕ) - 1) := by
      calc
        Complex.sinh
            (Complex.sin ((φ : ℝ) : ℂ) * Complex.cos ((φ : ℝ) : ℂ) * (τ : ℂ) * 2) ^ (3 : ℕ) =
          Complex.sinh
              (Complex.sin ((φ : ℝ) : ℂ) * Complex.cos ((φ : ℝ) : ℂ) * (τ : ℂ) * 2) *
            Complex.sinh
              (Complex.sin ((φ : ℝ) : ℂ) * Complex.cos ((φ : ℝ) : ℂ) * (τ : ℂ) * 2) ^ (2 : ℕ) := by ring
        _ = _ := by rw [hsinh]
    rw [hspace, hsqrt, hsin, hsinh, hsinCube, hsinhCube]
    ring
  rw [akhmedievCoreT, akhmedievCore, akhmedievCoreXX,
    Complex.ofReal_div, Complex.ofReal_pow]
  simpa only [d, n, nt, dt, nx, nxx, dx, dxx, nsq, neg_div] using halgebra

/-- Paper equation (35), including its `1/sqrt 2` background, solves focusing cubic NLS. -/
theorem akhmedievBreather_solves (φ : BreatherAngle) :
    SolvesFocusingNLS (akhmedievBreatherJet φ) := by
  intro τ ξ
  simp only [akhmedievBreatherJet]
  rw [norm_akhmedievBreather_sq, akhmedievBreather]
  have hcore := akhmedievCore_nls_residual φ ξ τ
  let P := linearPhase 1 0 τ ξ
  let a : ℂ := ((akhmedievNumeratorSq φ ξ τ /
    akhmedievDenominator φ ξ τ ^ (2 : ℕ) : ℝ) : ℂ)
  have hcarrier :
      Complex.I * (akhmedievCoreT φ ξ τ * P +
          akhmedievCore φ ξ τ * (P * Complex.I)) +
        akhmedievCoreXX φ ξ τ * P +
        a * (akhmedievCore φ ξ τ * P) = 0 := by
    calc
      _ = P * (Complex.I * akhmedievCoreT φ ξ τ +
          (Complex.I * Complex.I) * akhmedievCore φ ξ τ +
          akhmedievCoreXX φ ξ τ +
          a * akhmedievCore φ ξ τ) := by ring
      _ = P * (Complex.I * akhmedievCoreT φ ξ τ -
          akhmedievCore φ ξ τ + akhmedievCoreXX φ ξ τ +
          a * akhmedievCore φ ξ τ) := by rw [Complex.I_mul_I]; ring
      _ = 0 := mul_eq_zero_of_right P (by simpa only [a] using hcore)
  rw [← akhmedievCore]
  change Complex.I *
        ((akhmedievCoreT φ ξ τ * P +
          akhmedievCore φ ξ τ * (P * Complex.I)) / (Real.sqrt 2 : ℂ)) +
      akhmedievCoreXX φ ξ τ * P / (Real.sqrt 2 : ℂ) +
      (((2 * (akhmedievNumeratorSq φ ξ τ /
        (2 * akhmedievDenominator φ ξ τ ^ (2 : ℕ))) : ℝ) : ℂ) *
        (akhmedievCore φ ξ τ * P / (Real.sqrt 2 : ℂ))) = 0
  calc
    _ = (Complex.I * (akhmedievCoreT φ ξ τ * P +
            akhmedievCore φ ξ τ * (P * Complex.I)) +
          akhmedievCoreXX φ ξ τ * P +
          a * (akhmedievCore φ ξ τ * P)) / (Real.sqrt 2 : ℂ) := by
        dsimp only [a]
        push_cast
        ring
    _ = 0 := by rw [hcarrier, zero_div]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
