import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAkhmedievNLS
import Mathlib.Tactic

/-!
# Certified Ma breather solution

The printed Ma quotient is differentiated in time and twice in space, then checked against
focusing cubic NLS.  All denominator side conditions are discharged by global positivity.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def maDenominatorT (φ : MaAngle) (τ : ℝ) : ℝ :=
  maOmega φ * Real.sin (maOmega φ * τ)

noncomputable def maDenominatorX (φ : MaAngle) (ξ : ℝ) : ℝ :=
  Real.cosh (φ : ℝ) * maWaveNumber φ * Real.sinh (maWaveNumber φ * ξ)

noncomputable def maDenominatorXX (φ : MaAngle) (ξ : ℝ) : ℝ :=
  Real.cosh (φ : ℝ) * maWaveNumber φ ^ 2 * Real.cosh (maWaveNumber φ * ξ)

noncomputable def maNumeratorT (φ : MaAngle) (τ : ℝ) : ℂ :=
  ((maOmega φ * Real.sin (maOmega φ * τ) * Real.cosh (2 * (φ : ℝ)) : ℝ) : ℂ) -
    Complex.I *
      ((maOmega φ * Real.cos (maOmega φ * τ) * Real.sinh (2 * (φ : ℝ)) : ℝ) : ℂ)

noncomputable def maNumeratorX (φ : MaAngle) (ξ : ℝ) : ℂ :=
  (maDenominatorX φ ξ : ℂ)

noncomputable def maNumeratorXX (φ : MaAngle) (ξ : ℝ) : ℂ :=
  (maDenominatorXX φ ξ : ℂ)

noncomputable def maCoreT (φ : MaAngle) (ξ τ : ℝ) : ℂ :=
  -((maNumeratorT φ τ * (maDenominator φ ξ τ : ℂ) -
      maNumerator φ ξ τ * (maDenominatorT φ τ : ℂ)) /
    (maDenominator φ ξ τ : ℂ) ^ 2)

noncomputable def maCoreX (φ : MaAngle) (ξ τ : ℝ) : ℂ :=
  -((maNumeratorX φ ξ * (maDenominator φ ξ τ : ℂ) -
      maNumerator φ ξ τ * (maDenominatorX φ ξ : ℂ)) /
    (maDenominator φ ξ τ : ℂ) ^ 2)

noncomputable def maCoreXX (φ : MaAngle) (ξ τ : ℝ) : ℂ :=
  -(((maNumeratorXX φ ξ * (maDenominator φ ξ τ : ℂ) -
        maNumerator φ ξ τ * (maDenominatorXX φ ξ : ℂ)) *
        (maDenominator φ ξ τ : ℂ) ^ 2 -
      (maNumeratorX φ ξ * (maDenominator φ ξ τ : ℂ) -
        maNumerator φ ξ τ * (maDenominatorX φ ξ : ℂ)) *
        (2 * (maDenominator φ ξ τ : ℂ) * (maDenominatorX φ ξ : ℂ))) /
    ((maDenominator φ ξ τ : ℂ) ^ 2) ^ 2)

theorem hasDerivAt_maDenominator_time (φ : MaAngle) (ξ τ : ℝ) :
    HasDerivAt (fun r => maDenominator φ ξ r) (maDenominatorT φ τ) τ := by
  have hcos := (Real.hasDerivAt_cos (maOmega φ * τ)).comp τ
    ((hasDerivAt_id τ).const_mul (maOmega φ))
  have h := (hasDerivAt_const τ
    (Real.cosh (φ : ℝ) * Real.cosh (maWaveNumber φ * ξ))).sub hcos
  apply h.congr_deriv
  rw [maDenominatorT]
  ring

theorem hasDerivAt_maDenominator_space (φ : MaAngle) (ξ τ : ℝ) :
    HasDerivAt (fun y => maDenominator φ y τ) (maDenominatorX φ ξ) ξ := by
  have hcosh := (Real.hasDerivAt_cosh (maWaveNumber φ * ξ)).comp ξ
    ((hasDerivAt_id ξ).const_mul (maWaveNumber φ))
  have h := (hcosh.const_mul (Real.cosh (φ : ℝ))).sub_const
    (Real.cos (maOmega φ * τ))
  apply h.congr_deriv
  rw [maDenominatorX]
  ring

theorem hasDerivAt_maDenominator_space_one (φ : MaAngle) (ξ _τ : ℝ) :
    HasDerivAt (maDenominatorX φ) (maDenominatorXX φ ξ) ξ := by
  have h := ((Real.hasDerivAt_sinh (maWaveNumber φ * ξ)).comp ξ
    ((hasDerivAt_id ξ).const_mul (maWaveNumber φ))).const_mul
      (Real.cosh (φ : ℝ) * maWaveNumber φ)
  apply h.congr_deriv
  rw [maDenominatorXX]
  ring

theorem hasDerivAt_maNumerator_time (φ : MaAngle) (ξ τ : ℝ) :
    HasDerivAt (fun r => maNumerator φ ξ r) (maNumeratorT φ τ) τ := by
  have hcos := (Real.hasDerivAt_cos (maOmega φ * τ)).comp τ
    ((hasDerivAt_id τ).const_mul (maOmega φ))
  have hsin := (Real.hasDerivAt_sin (maOmega φ * τ)).comp τ
    ((hasDerivAt_id τ).const_mul (maOmega φ))
  have hreal := (hasDerivAt_const τ
    (Real.cosh (φ : ℝ) * Real.cosh (maWaveNumber φ * ξ))).sub
      (hcos.const_mul (Real.cosh (2 * (φ : ℝ))))
  have himag := hsin.const_mul (Real.sinh (2 * (φ : ℝ)))
  have h := hreal.ofReal_comp.sub (himag.ofReal_comp.const_mul Complex.I)
  have heq : (fun r => maNumerator φ ξ r) =ᶠ[nhds τ]
      ((fun r => ((Real.cosh (φ : ℝ) * Real.cosh (maWaveNumber φ * ξ) -
          Real.cosh (2 * (φ : ℝ)) * Real.cos (maOmega φ * r) : ℝ) : ℂ)) -
        fun r => Complex.I *
          ((Real.sinh (2 * (φ : ℝ)) * Real.sin (maOmega φ * r) : ℝ) : ℂ)) := by
    filter_upwards with r
    simp only [maNumerator]
    congr 1 <;> push_cast <;> ring
  have hsource := h.congr_of_eventuallyEq heq
  apply hsource.congr_deriv
  simp only [maNumeratorT]
  push_cast
  ring

theorem hasDerivAt_maNumerator_space (φ : MaAngle) (ξ τ : ℝ) :
    HasDerivAt (fun y => maNumerator φ y τ) (maNumeratorX φ ξ) ξ := by
  have hcosh := (Real.hasDerivAt_cosh (maWaveNumber φ * ξ)).comp ξ
    ((hasDerivAt_id ξ).const_mul (maWaveNumber φ))
  have hreal := (hcosh.const_mul (Real.cosh (φ : ℝ))).sub_const
    (Real.cos (maOmega φ * τ) * Real.cosh (2 * (φ : ℝ)))
  have h := hreal.ofReal_comp.sub
    (hasDerivAt_const ξ
      (Complex.I * ((Real.sin (maOmega φ * τ) *
        Real.sinh (2 * (φ : ℝ)) : ℝ) : ℂ)))
  apply h.congr_deriv
  rw [maNumeratorX, maDenominatorX]
  push_cast
  ring

theorem hasDerivAt_maNumerator_space_one (φ : MaAngle) (ξ _τ : ℝ) :
    HasDerivAt (maNumeratorX φ) (maNumeratorXX φ ξ) ξ := by
  exact (hasDerivAt_maDenominator_space_one φ ξ _τ).ofReal_comp

theorem hasDerivAt_maCore_time (φ : MaAngle) (ξ τ : ℝ) :
    HasDerivAt (fun r => maCore φ ξ r) (maCoreT φ ξ τ) τ := by
  have hden := (hasDerivAt_maDenominator_time φ ξ τ).ofReal_comp
  have h := (hasDerivAt_maNumerator_time φ ξ τ).div hden
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (maDenominator_pos φ ξ τ)))
  exact h.neg

theorem hasDerivAt_maCore_space (φ : MaAngle) (ξ τ : ℝ) :
    HasDerivAt (fun y => maCore φ y τ) (maCoreX φ ξ τ) ξ := by
  have hden := (hasDerivAt_maDenominator_space φ ξ τ).ofReal_comp
  have h := (hasDerivAt_maNumerator_space φ ξ τ).div hden
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (maDenominator_pos φ ξ τ)))
  exact h.neg

theorem hasDerivAt_maCore_space_one (φ : MaAngle) (ξ τ : ℝ) :
    HasDerivAt (fun y => maCoreX φ y τ) (maCoreXX φ ξ τ) ξ := by
  have hn := hasDerivAt_maNumerator_space φ ξ τ
  have hnn := hasDerivAt_maNumerator_space_one φ ξ τ
  have hd := (hasDerivAt_maDenominator_space φ ξ τ).ofReal_comp
  have hdd := (hasDerivAt_maDenominator_space_one φ ξ τ).ofReal_comp
  have htop := (hnn.mul hd).sub (hn.mul hdd)
  have hdenSq := hd.pow 2
  have hquot := htop.div hdenSq (pow_ne_zero 2
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (maDenominator_pos φ ξ τ))))
  have hquot' : HasDerivAt
      (fun y => -((maNumeratorX φ y * (maDenominator φ y τ : ℂ) -
          maNumerator φ y τ * (maDenominatorX φ y : ℂ)) /
        (maDenominator φ y τ : ℂ) ^ 2))
      (maCoreXX φ ξ τ) ξ := by
    apply hquot.neg.congr_deriv
    simp only [maCoreXX, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat]
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt (maDenominator_pos φ ξ τ))]
    ring
  apply hquot'.congr_of_eventuallyEq
  filter_upwards with y
  rw [maCoreX]

noncomputable def maBreatherJet (φ : MaAngle) : ComplexEvolutionJet2 where
  u := fun τ ξ => maBreather φ ξ τ
  ut := fun τ ξ =>
    (maCoreT φ ξ τ * linearPhase 1 0 τ ξ +
      maCore φ ξ τ * (linearPhase 1 0 τ ξ * Complex.I)) / (Real.sqrt 2 : ℂ)
  ux := fun τ ξ => maCoreX φ ξ τ * linearPhase 1 0 τ ξ / (Real.sqrt 2 : ℂ)
  uxx := fun τ ξ => maCoreXX φ ξ τ * linearPhase 1 0 τ ξ / (Real.sqrt 2 : ℂ)
  hasDerivAt_time := by
    intro τ ξ
    have h := (hasDerivAt_maCore_time φ ξ τ).mul
      (hasDerivAt_linearPhase_time 1 0 τ ξ) |>.div_const (Real.sqrt 2 : ℂ)
    apply h.congr_deriv
    simp
  hasDerivAt_space := by
    intro τ ξ
    have h := (hasDerivAt_maCore_space φ ξ τ).mul
      (hasDerivAt_linearPhase_space 1 0 τ ξ) |>.div_const (Real.sqrt 2 : ℂ)
    apply h.congr_deriv
    simp
  hasDerivAt_space_one := by
    intro τ ξ
    have h := (hasDerivAt_maCore_space_one φ ξ τ).mul
      (hasDerivAt_linearPhase_space 1 0 τ ξ) |>.div_const (Real.sqrt 2 : ℂ)
    apply h.congr_deriv
    simp

/-- The Ma quotient core satisfies the carrier-reduced focusing-NLS identity. -/
theorem maCore_nls_residual (φ : MaAngle) (ξ τ : ℝ) :
    Complex.I * maCoreT φ ξ τ - maCore φ ξ τ + maCoreXX φ ξ τ +
        ((maNumeratorSq φ ξ τ / maDenominator φ ξ τ ^ 2 : ℝ) : ℂ) *
          maCore φ ξ τ = 0 := by
  let d : ℂ := (maDenominator φ ξ τ : ℂ)
  let n : ℂ := maNumerator φ ξ τ
  let nt : ℂ := maNumeratorT φ τ
  let dt : ℂ := (maDenominatorT φ τ : ℂ)
  let nx : ℂ := maNumeratorX φ ξ
  let nxx : ℂ := maNumeratorXX φ ξ
  let dx : ℂ := (maDenominatorX φ ξ : ℂ)
  let dxx : ℂ := (maDenominatorXX φ ξ : ℂ)
  let nsq : ℂ := (maNumeratorSq φ ξ τ : ℂ)
  have hd : d ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (maDenominator_pos φ ξ τ))
  have halgebra :
      Complex.I * (-((nt * d - n * dt) / d ^ 2)) - (-n / d) +
          (-(((nxx * d - n * dxx) * d ^ 2 -
            (nx * d - n * dx) * (2 * d * dx)) / (d ^ 2) ^ 2)) +
          (nsq / d ^ 2) * (-n / d) = 0 := by
    field_simp [hd]
    dsimp [d, n, nt, dt, nx, nxx, dx, dxx, nsq]
    rw [maNumeratorT, maNumeratorX, maNumeratorXX, maDenominatorT,
      maDenominatorX, maDenominatorXX, maNumerator, maNumeratorSq,
      maDenominator, maOmega, maWaveNumber]
    push_cast
    rw [Complex.cosh_two_mul, Complex.sinh_two_mul]
    ring_nf
    simp only [Complex.I_sq]
    let zt : ℂ := Complex.cosh ((φ : ℝ) : ℂ) *
      Complex.sinh ((φ : ℝ) : ℂ) * (τ : ℂ) * 2
    let zx : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) *
      Complex.sinh ((φ : ℝ) : ℂ) * (ξ : ℂ)
    have hparam : Complex.sinh ((φ : ℝ) : ℂ) ^ 2 =
        Complex.cosh ((φ : ℝ) : ℂ) ^ 2 - 1 := by
      linear_combination -(Complex.cosh_sq_sub_sinh_sq (((φ : ℝ) : ℂ)))
    have htime : Complex.sin zt ^ 2 = 1 - Complex.cos zt ^ 2 := by
      linear_combination Complex.sin_sq_add_cos_sq zt
    have hspace : Complex.sinh zx ^ 2 = Complex.cosh zx ^ 2 - 1 := by
      linear_combination -(Complex.cosh_sq_sub_sinh_sq zx)
    have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hparamCube : Complex.sinh ((φ : ℝ) : ℂ) ^ 3 =
        Complex.sinh ((φ : ℝ) : ℂ) *
          (Complex.cosh ((φ : ℝ) : ℂ) ^ 2 - 1) := by
      calc
        Complex.sinh ((φ : ℝ) : ℂ) ^ 3 =
            Complex.sinh ((φ : ℝ) : ℂ) *
              Complex.sinh ((φ : ℝ) : ℂ) ^ 2 := by ring
        _ = _ := by rw [hparam]
    have hparamFour : Complex.sinh ((φ : ℝ) : ℂ) ^ 4 =
        (Complex.cosh ((φ : ℝ) : ℂ) ^ 2 - 1) ^ 2 := by
      calc
        Complex.sinh ((φ : ℝ) : ℂ) ^ 4 =
            (Complex.sinh ((φ : ℝ) : ℂ) ^ 2) ^ 2 := by ring
        _ = _ := by rw [hparam]
    have hparamFive : Complex.sinh ((φ : ℝ) : ℂ) ^ 5 =
        Complex.sinh ((φ : ℝ) : ℂ) *
          (Complex.cosh ((φ : ℝ) : ℂ) ^ 2 - 1) ^ 2 := by
      calc
        Complex.sinh ((φ : ℝ) : ℂ) ^ 5 =
            Complex.sinh ((φ : ℝ) : ℂ) *
              (Complex.sinh ((φ : ℝ) : ℂ) ^ 2) ^ 2 := by ring
        _ = _ := by rw [hparam]
    have hparamSix : Complex.sinh ((φ : ℝ) : ℂ) ^ 6 =
        (Complex.cosh ((φ : ℝ) : ℂ) ^ 2 - 1) ^ 3 := by
      calc
        Complex.sinh ((φ : ℝ) : ℂ) ^ 6 =
            (Complex.sinh ((φ : ℝ) : ℂ) ^ 2) ^ 3 := by ring
        _ = _ := by rw [hparam]
    have htimeCube : Complex.sin zt ^ 3 =
        Complex.sin zt * (1 - Complex.cos zt ^ 2) := by
      calc
        Complex.sin zt ^ 3 = Complex.sin zt * Complex.sin zt ^ 2 := by ring
        _ = _ := by rw [htime]
    dsimp only [zt, zx] at htime hspace htimeCube
    rw [hparam, htime, hspace, hsqrt, hparamCube, hparamFour, hparamFive,
      hparamSix, htimeCube]
    ring
  rw [maCoreT, maCore, maCoreXX, Complex.ofReal_div, Complex.ofReal_pow]
  simpa only [d, n, nt, dt, nx, nxx, dx, dxx, nsq, neg_div] using halgebra

/-- Paper equation (36), including its `1/sqrt 2` background, solves focusing cubic NLS. -/
theorem maBreather_solves (φ : MaAngle) : SolvesFocusingNLS (maBreatherJet φ) := by
  intro τ ξ
  simp only [maBreatherJet]
  rw [norm_maBreather_sq, maBreather]
  have hcore := maCore_nls_residual φ ξ τ
  let P := linearPhase 1 0 τ ξ
  let a : ℂ := ((maNumeratorSq φ ξ τ / maDenominator φ ξ τ ^ 2 : ℝ) : ℂ)
  have hcarrier :
      Complex.I * (maCoreT φ ξ τ * P + maCore φ ξ τ * (P * Complex.I)) +
        maCoreXX φ ξ τ * P + a * (maCore φ ξ τ * P) = 0 := by
    calc
      _ = P * (Complex.I * maCoreT φ ξ τ +
          (Complex.I * Complex.I) * maCore φ ξ τ + maCoreXX φ ξ τ +
          a * maCore φ ξ τ) := by ring
      _ = P * (Complex.I * maCoreT φ ξ τ - maCore φ ξ τ + maCoreXX φ ξ τ +
          a * maCore φ ξ τ) := by rw [Complex.I_mul_I]; ring
      _ = 0 := mul_eq_zero_of_right P (by simpa only [a] using hcore)
  change Complex.I *
        ((maCoreT φ ξ τ * P + maCore φ ξ τ * (P * Complex.I)) /
          (Real.sqrt 2 : ℂ)) +
      maCoreXX φ ξ τ * P / (Real.sqrt 2 : ℂ) +
      (((2 * (maNumeratorSq φ ξ τ /
        (2 * maDenominator φ ξ τ ^ 2)) : ℝ) : ℂ) *
        (maCore φ ξ τ * P / (Real.sqrt 2 : ℂ))) = 0
  calc
    _ = (Complex.I * (maCoreT φ ξ τ * P + maCore φ ξ τ * (P * Complex.I)) +
          maCoreXX φ ξ τ * P + a * (maCore φ ξ τ * P)) /
        (Real.sqrt 2 : ℂ) := by
      dsimp only [a]
      push_cast
      ring
    _ = 0 := by rw [hcarrier, zero_div]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
