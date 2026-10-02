import GaloisForLFunctions.RHTower.ZetaChiNormalizedShiftBound
import GaloisForLFunctions.RHTower.BourgainPhasePerturbation

open Complex
noncomputable section
namespace RHTower

/-- Canonical unweighted dual coefficient times the actual chi-shift
saddle amplitude. Smoothing and cofactor masks are not included here. -/
def zetaChiCanonicalSaddleCoefficient (s : ℂ) (x : ℝ) : ℂ :=
  (zetaChi (s + ((2 * Real.pi * x : ℝ) : ℂ) * I) /
      zetaChi (linePt (2 * Real.pi * x))) * (x : ℂ) ^ (s - 1) *
    (Real.sqrt (2 * Real.pi * (2 * Real.pi * x)) : ℂ) *
      bourgainOscillation (2 * Real.pi * x)

private theorem cpow_mul_sqrt_eq_conductor_exp (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (s - 1) * (Real.sqrt x : ℂ) =
      Complex.exp ((s - (1 / 2 : ℂ)) * (Real.log x : ℂ)) := by
  have hsqrt : (Real.sqrt x : ℂ) = Complex.exp ((Real.log x : ℂ) / 2) := by
    have he : Real.exp (Real.log x / 2) = Real.sqrt x := by
      rw [← Real.log_sqrt hx.le, Real.exp_log (Real.sqrt_pos.mpr hx)]
    rw [← he, Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, hsqrt, ← Complex.exp_add]
  congr 1
  ring

/-- Exact cancellation of the canonical complex power against the
stationary square root leaves only the normalized actual chi ratio. -/
theorem zetaChiCanonicalSaddleCoefficient_eq (s : ℂ) {x : ℝ} (hx : 0 < x) :
    zetaChiCanonicalSaddleCoefficient s x =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((zetaChi (s + ((2 * Real.pi * x : ℝ) : ℂ) * I) /
            zetaChi (linePt (2 * Real.pi * x))) *
          Complex.exp ((s - (1 / 2 : ℂ)) * (Real.log x : ℂ))) *
        bourgainOscillation (2 * Real.pi * x) := by
  have hsqrt : Real.sqrt (2 * Real.pi * (2 * Real.pi * x)) =
      (2 * Real.pi) * Real.sqrt x := by
    rw [show 2 * Real.pi * (2 * Real.pi * x) = (2 * Real.pi) ^ 2 * x by ring,
      Real.sqrt_mul (sq_nonneg (2 * Real.pi)), Real.sqrt_sq (by positivity)]
  unfold zetaChiCanonicalSaddleCoefficient
  rw [hsqrt, Complex.ofReal_mul]
  calc
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        ((zetaChi (s + ((2 * Real.pi * x : ℝ) : ℂ) * I) /
            zetaChi (linePt (2 * Real.pi * x))) *
          ((x : ℂ) ^ (s - 1) * (Real.sqrt x : ℂ))) *
        bourgainOscillation (2 * Real.pi * x) := by push_cast; ring
    _ = _ := by rw [cpow_mul_sqrt_eq_conductor_exp s hx]; push_cast; rfl

/-- The canonical coefficient has universal leading magnitude and keeps
the rational or real-frequency saddle phase. -/
theorem norm_zetaChiCanonicalSaddleCoefficient_sub_phase_le {s : ℂ} {x : ℝ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hx : 0 < x)
    (ht : 4 ≤ 2 * Real.pi * x) (him : 2 * |s.im| ≤ 2 * Real.pi * x)
    (hsize : 26 * ‖s - (1 / 2 : ℂ)‖ + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ 2 * Real.pi * x) :
    ‖zetaChiCanonicalSaddleCoefficient s x -
      ((2 * Real.pi : ℝ) : ℂ) * bourgainOscillation (2 * Real.pi * x)‖ ≤
      (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2) / x := by
  have hb := norm_zetaChi_normalized_shift_sub_one_le hs0 hs1 ht him hsize
  have he : (2 * Real.pi * x) / (2 * Real.pi) = x := by field_simp
  rw [he] at hb
  let Q : ℂ := (zetaChi (s + ((2 * Real.pi * x : ℝ) : ℂ) * I) /
    zetaChi (linePt (2 * Real.pi * x))) *
      Complex.exp ((s - (1 / 2 : ℂ)) * (Real.log x : ℂ))
  rw [zetaChiCanonicalSaddleCoefficient_eq s hx]
  change ‖((2 * Real.pi : ℝ) : ℂ) * Q * bourgainOscillation (2 * Real.pi * x) -
    ((2 * Real.pi : ℝ) : ℂ) * bourgainOscillation (2 * Real.pi * x)‖ ≤ _
  have heq : ((2 * Real.pi : ℝ) : ℂ) * Q * bourgainOscillation (2 * Real.pi * x) -
      ((2 * Real.pi : ℝ) : ℂ) * bourgainOscillation (2 * Real.pi * x) =
      ((2 * Real.pi : ℝ) : ℂ) * (Q - 1) * bourgainOscillation (2 * Real.pi * x) := by ring
  rw [heq, norm_mul, norm_mul, norm_bourgainOscillation, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  calc
    _ ≤ (2 * Real.pi) *
        ((52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2) / (2 * Real.pi * x)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

/-- Integer saddles have the universal positive value `2*pi`, up to the
explicit reciprocal-integer compact-shift error. -/
theorem norm_zetaChiCanonicalSaddleCoefficient_nat_sub_two_pi_le {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (n : ℕ) (hn : 0 < n)
    (ht : 4 ≤ 2 * Real.pi * (n : ℝ)) (him : 2 * |s.im| ≤ 2 * Real.pi * (n : ℝ))
    (hsize : 26 * ‖s - (1 / 2 : ℂ)‖ + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ 2 * Real.pi * (n : ℝ)) :
    ‖zetaChiCanonicalSaddleCoefficient s n - ((2 * Real.pi : ℝ) : ℂ)‖ ≤
      (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2) / n := by
  have hb := norm_zetaChiCanonicalSaddleCoefficient_sub_phase_le hs0 hs1
    (show (0 : ℝ) < n by exact_mod_cast hn) ht him hsize
  have hp : bourgainOscillation (2 * Real.pi * (n : ℝ)) = 1 := by
    unfold bourgainOscillation
    have he : I * ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) =
        (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by push_cast; ring
    rw [he]
    exact Complex.exp_nat_mul_two_pi_mul_I n
  simpa only [hp, mul_one] using hb

end RHTower
