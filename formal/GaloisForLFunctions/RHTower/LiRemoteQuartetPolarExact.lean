import GaloisForLFunctions.RHTower.LiRemoteQuartetAsymptotics
import GaloisForLFunctions.HTGeometry.SectorPowerMassLower

/-!
# Exact polar coordinates of a remote Li quartet

The card's logarithmic radial and principal angular coordinates recover the literal Möbius
coordinate of its off-critical zero.  This closes the exact bridge between divisor geometry and
the already formalized cosh--cos quartet profile.
-/

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exact argument identity in card equation `(4)`. -/
theorem arg_liMobiusCoordinate_remoteQuartetZero
    {a T : ℝ} (ha : 0 < a) (ha' : a < 1 / 2) (hT : 1 / 2 < T) :
    Complex.arg (liMobiusCoordinate (liRemoteQuartetZero a T)) =
      liRemoteAngularCoordinate a T := by
  let q := liMobiusCoordinate (liRemoteQuartetZero a T)
  have hden : 0 < T ^ 2 + (1 / 2 - a) ^ 2 := by
    nlinarith [sq_pos_of_pos (by linarith : 0 < T)]
  have hnum : 0 < T ^ 2 - (1 / 2 - a) * (1 - (1 / 2 - a)) := by
    nlinarith [sq_pos_of_pos (by linarith : 0 < T), sq_nonneg a]
  have hqre : 0 < q.re := by
    dsimp [q]
    rw [liMobiusCoordinate_remoteQuartetZero (ne_of_gt (by linarith : 0 < T))]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
    simpa using div_pos hnum hden
  rw [complexArg_eq_arctan_of_re_pos hqre]
  congr 1
  dsimp [q]
  rw [liMobiusCoordinate_remoteQuartetZero (ne_of_gt (by linarith : 0 < T))]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, zero_add]
  unfold liRemoteAngularSmallParameter
  have hnum0 : T ^ 2 - (1 / 2 - a) * (1 - (1 / 2 - a)) ≠ 0 := ne_of_gt hnum
  field_simp [hden.ne', hnum0]
  ring

/-- Exact modulus identity in card equations `(1)` and `(3)`. -/
theorem norm_liMobiusCoordinate_remoteQuartetZero
    {a T : ℝ} (ha : 0 < a) (hT : T ≠ 0) :
    ‖liMobiusCoordinate (liRemoteQuartetZero a T)‖ =
      Real.exp (liRemoteRadialCoordinate a T) := by
  let q := liMobiusCoordinate (liRemoteQuartetZero a T)
  have hsqexp : Real.exp (liRemoteRadialCoordinate a T) ^ 2 = Complex.normSq q := by
    rw [← Real.exp_nat_mul]
    norm_num
    exact exp_two_mul_liRemoteRadialCoordinate ha hT
  have hsqnorm : ‖q‖ ^ 2 = Complex.normSq q := Complex.sq_norm q
  have hexpPos : 0 < Real.exp (liRemoteRadialCoordinate a T) := Real.exp_pos _
  have hnormNonneg : 0 ≤ ‖q‖ := norm_nonneg _
  nlinarith

/-- Card equation `(1)`: the actual remote-zero Möbius coordinate is exactly the polar
coordinate determined by equations `(3)` and `(4)`. -/
theorem liMobiusCoordinate_remoteQuartetZero_eq_polar
    {a T : ℝ} (ha : 0 < a) (ha' : a < 1 / 2) (hT : 1 / 2 < T) :
    liMobiusCoordinate (liRemoteQuartetZero a T) =
      liQuartetPolarCoordinate
        (liRemoteRadialCoordinate a T) (liRemoteAngularCoordinate a T) := by
  let q := liMobiusCoordinate (liRemoteQuartetZero a T)
  calc
    q = (‖q‖ : ℂ) * Complex.exp ((q.arg : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I q).symm
    _ = (Real.exp (liRemoteRadialCoordinate a T) : ℂ) *
        Complex.exp ((liRemoteAngularCoordinate a T : ℂ) * Complex.I) := by
      rw [norm_liMobiusCoordinate_remoteQuartetZero ha (ne_of_gt (by linarith : 0 < T)),
        arg_liMobiusCoordinate_remoteQuartetZero ha ha' hT]
    _ = liQuartetPolarCoordinate
        (liRemoteRadialCoordinate a T) (liRemoteAngularCoordinate a T) := by
      rw [liQuartetPolarCoordinate, Complex.ofReal_exp, Complex.exp_add]

end
end RHTower
