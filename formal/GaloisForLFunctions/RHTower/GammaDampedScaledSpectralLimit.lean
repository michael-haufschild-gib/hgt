import GaloisForLFunctions.RHTower.GammaDampedLaurentAtOne
import GaloisForLFunctions.RHTower.MobiusCriticalClockMoments
import GaloisForLFunctions.RHTower.CentredPoleProfile

/-!
# The scaled critical limit of the damped spectral symbol

Along the critical scaling `z_ε = 1 + ε w`, `w = 1/2 - i y`, the two Laurent scalings of the damped
squarefree series and the critical first logarithmic moment `ε m_(1+ε) → 1` combine into the exact
local limit of the card's spectral symbol

```text
D_ε = -F'(z_ε) - m_(1+ε) F(z_ε),
ε² D_ε → (1/ζ(2)) [w^(-2) - w^(-1)] .
```

The imaginary part of the limit is `(6/π²)` times the centred-pole profile, whose energy is `π`.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ### The scaled critical point -/

/-- The centred critical direction `w = 1/2 - i y`. -/
def criticalDirection (y : ℝ) : ℂ := (1 : ℂ) / 2 - (y : ℂ) * Complex.I

theorem criticalDirection_re (y : ℝ) : (criticalDirection y).re = 1 / 2 := by
  simp [criticalDirection]

theorem criticalDirection_ne_zero (y : ℝ) : criticalDirection y ≠ 0 := by
  intro h
  have hre := criticalDirection_re y
  rw [h] at hre
  norm_num at hre

/-- The scaled critical point `z_ε = 1 + ε w`. -/
def criticalScaledPoint (ε y : ℝ) : ℂ := 1 + (ε : ℂ) * criticalDirection y

theorem criticalScaledPoint_sub_one (ε y : ℝ) :
    criticalScaledPoint ε y - 1 = (ε : ℂ) * criticalDirection y := by
  rw [criticalScaledPoint]
  ring

theorem criticalScaledPoint_re (ε y : ℝ) : (criticalScaledPoint ε y).re = 1 + ε / 2 := by
  simp [criticalScaledPoint, criticalDirection]
  ring

theorem tendsto_criticalScaledPoint (y : ℝ) :
    Tendsto (fun ε : ℝ => criticalScaledPoint ε y) (nhdsWithin 0 (Ioi 0))
      (nhdsWithin 1 {s : ℂ | 1 < s.re}) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : Continuous fun ε : ℝ => criticalScaledPoint ε y := by
      unfold criticalScaledPoint
      fun_prop
    have h0 : criticalScaledPoint 0 y = 1 := by simp [criticalScaledPoint]
    have := hcont.tendsto (0 : ℝ)
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hpos : (0 : ℝ) < ε := hε
    simp only [criticalScaledPoint_re]
    linarith

/-! ### The two scaled Laurent limits -/

theorem tendsto_mul_lSeries_gammaDampedCoeff (y : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * LSeries gammaDampedCoeff (criticalScaledPoint ε y))
      (nhdsWithin 0 (Ioi 0)) (nhds ((1 / riemannZeta 2) / criticalDirection y)) := by
  have hw : criticalDirection y ≠ 0 := criticalDirection_ne_zero y
  have hcomp := tendsto_sub_one_mul_lSeries_gammaDampedCoeff.comp (tendsto_criticalScaledPoint y)
  refine ((hcomp.div_const (criticalDirection y)).congr fun ε => ?_)
  simp only [Function.comp_apply, criticalScaledPoint_sub_one]
  field_simp

theorem tendsto_sq_mul_deriv_lSeries_gammaDampedCoeff (y : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * deriv (LSeries gammaDampedCoeff) (criticalScaledPoint ε y))
      (nhdsWithin 0 (Ioi 0))
      (nhds (-(1 / riemannZeta 2) / criticalDirection y ^ 2)) := by
  have hw : criticalDirection y ≠ 0 := criticalDirection_ne_zero y
  have hcomp := tendsto_sub_one_sq_mul_deriv_lSeries_gammaDampedCoeff.comp
    (tendsto_criticalScaledPoint y)
  refine ((hcomp.div_const (criticalDirection y ^ 2)).congr fun ε => ?_)
  simp only [Function.comp_apply, criticalScaledPoint_sub_one, mul_pow]
  field_simp

/-! ### The critical first logarithmic moment -/

theorem tendsto_mul_squarefreeMobiusLogMoment :
    Tendsto (fun ε : ℝ => ε * squarefreeMobiusLogMoment 1 (1 + ε))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hmap : Tendsto (fun ε : ℝ => 1 + ε) (nhdsWithin 0 (Ioi 0)) (nhdsWithin 1 (Ioi 1)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Tendsto (fun ε : ℝ => 1 + ε) (nhds 0) (nhds 1) := by
        simpa only [Pi.add_apply, id_eq, add_zero] using!
          ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).add
            continuous_id).tendsto (0 : ℝ)
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hpos : (0 : ℝ) < ε := hε
      simp only [Set.mem_Ioi]
      linarith
  refine (tendsto_squarefreeMobiusLogMoment_one_critical.comp hmap).congr fun ε => ?_
  simp only [Function.comp_apply]
  ring_nf

/-! ### The scaled local limit -/

/-- The card's spectral symbol `D_ε` evaluated at `x = ε y`. -/
def gammaDampedSpectralSymbol (ε y : ℝ) : ℂ :=
  -deriv (LSeries gammaDampedCoeff) (criticalScaledPoint ε y) -
    (squarefreeMobiusLogMoment 1 (1 + ε) : ℂ) * LSeries gammaDampedCoeff (criticalScaledPoint ε y)

/-- **The scaled local limit.**  `ε² D_ε(εy) → (1/ζ(2)) [w^(-2) - w^(-1)]`. -/
theorem tendsto_sq_mul_gammaDampedSpectralSymbol (y : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * gammaDampedSpectralSymbol ε y) (nhdsWithin 0 (Ioi 0))
      (nhds ((1 / riemannZeta 2) *
        ((criticalDirection y)⁻¹ ^ 2 - (criticalDirection y)⁻¹))) := by
  have hw : criticalDirection y ≠ 0 := criticalDirection_ne_zero y
  have hderiv := tendsto_sq_mul_deriv_lSeries_gammaDampedCoeff y
  have hval := tendsto_mul_lSeries_gammaDampedCoeff y
  have hmom : Tendsto (fun ε : ℝ => ((squarefreeMobiusLogMoment 1 (1 + ε) : ℂ) * (ε : ℂ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have h := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp tendsto_mul_squarefreeMobiusLogMoment
    refine h.congr fun ε => ?_
    simp only [Function.comp_apply, Complex.ofReal_mul]
    ring
  have hmain := hderiv.neg.sub (hmom.mul hval)
  have hw2 : criticalDirection y ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hval_eq : -(-(1 / riemannZeta 2) / criticalDirection y ^ 2) -
      1 * (1 / riemannZeta 2 / criticalDirection y)
      = (1 / riemannZeta 2) * ((criticalDirection y)⁻¹ ^ 2 - (criticalDirection y)⁻¹) := by
    field_simp
  rw [hval_eq] at hmain
  refine hmain.congr fun ε => ?_
  rw [gammaDampedSpectralSymbol]
  ring

/-! ### The imaginary part is the centred-pole profile -/

theorem criticalPoleProfile_eq_im (y : ℝ) :
    criticalPoleProfile y = ((criticalDirection y)⁻¹ ^ 2 - (criticalDirection y)⁻¹).im := rfl

theorem one_div_riemannZeta_two_ofReal :
    1 / riemannZeta 2 = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
  rw [riemannZeta_two]
  have hπ : ((Real.pi : ℂ)) ^ 2 ≠ 0 := by
    simp [Real.pi_ne_zero]
  push_cast
  field_simp

/-- **The scaled limit carries exactly the centred-pole profile.** -/
theorem im_gammaDampedSpectralLimit (y : ℝ) :
    ((1 / riemannZeta 2) *
        ((criticalDirection y)⁻¹ ^ 2 - (criticalDirection y)⁻¹)).im
      = 6 / Real.pi ^ 2 * criticalPoleProfile y := by
  rw [one_div_riemannZeta_two_ofReal, criticalPoleProfile_eq_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

end

end RHTower
