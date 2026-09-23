import GaloisForLFunctions.HTGeometry.CoppoJosephsonPotential
import GaloisForLFunctions.RHTower.PrimeArchThetaMorseGroundState

/-!
# Josephson deformation of the theta-Morse zero mode

The explicit supersymmetric mode from arXiv:2405.03454 can multiply every
existing theta-Morse zero mode. The product has an exact first-order factor,
a new Schrödinger potential, and a prescribed positive Gibbs-density tilt.
No spectral or differential equation hypothesis is supplied by the caller.
-/

noncomputable section
namespace RHTower
open HTGeometry

/-- Multiply a corpus Morse zero mode by the positive periodic Josephson mode. -/
def coppoMorseJosephsonAmplitude (A a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspMorseZeroMode A n x * coppoJosephsonGroundState a x

/-- Superpotentials add under the explicit product of the two zero modes. -/
def coppoMorseJosephsonSuperpotential (A a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspMorseSuperpotential A n x + coppoSineSuperpotential a x

/-- Exact curvature of the combined superpotential. -/
def coppoMorseJosephsonCurvature (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  2 * thetaCuspMorseScale n x + a * Real.cos x

/-- Lower partner potential for the periodically deformed Morse family. -/
def coppoMorseJosephsonPotentialMinus (A a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  coppoMorseJosephsonSuperpotential A a n x ^ (2 : ℕ) - coppoMorseJosephsonCurvature a n x

/-- Upper partner potential for the same exact factorization. -/
def coppoMorseJosephsonPotentialPlus (A a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  coppoMorseJosephsonSuperpotential A a n x ^ (2 : ℕ) + coppoMorseJosephsonCurvature a n x

/-- The periodic deformation preserves strict positivity for every positive theta atom. -/
theorem coppoMorseJosephsonAmplitude_pos (A a : ℝ) (n : ℕ) (x : ℝ) :
    0 < coppoMorseJosephsonAmplitude A a (n + 1) x := by
  dsimp [coppoMorseJosephsonAmplitude, thetaCuspMorseZeroMode, coppoJosephsonGroundState]
  positivity

/-- Every deformed theta-Morse atom satisfies its first-order Witten equation. -/
theorem hasDerivAt_coppoMorseJosephsonAmplitude (A a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (coppoMorseJosephsonAmplitude A a n)
      (-coppoMorseJosephsonSuperpotential A a n x * coppoMorseJosephsonAmplitude A a n x) x := by
  simpa only [coppoMorseJosephsonAmplitude, Pi.mul_apply] using!
    ((hasDerivAt_thetaCuspMorseZeroMode A n x).mul
      (hasDerivAt_coppoJosephsonGroundState a x)).congr_deriv (by
        dsimp [coppoMorseJosephsonSuperpotential, coppoMorseJosephsonAmplitude]; ring)

/-- The combined superpotential has no unproved derivative input. -/
theorem hasDerivAt_coppoMorseJosephsonSuperpotential (A a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (coppoMorseJosephsonSuperpotential A a n)
      (coppoMorseJosephsonCurvature a n x) x := by
  simpa only [coppoMorseJosephsonSuperpotential, coppoMorseJosephsonCurvature,
    coppoSineSuperpotential, Pi.add_apply] using!
      (hasDerivAt_thetaCuspMorseSuperpotential A n x).add
        ((Real.hasDerivAt_sin x).const_mul a)

/-- The lower potential is the sum of the old potentials plus an explicit interaction term. -/
theorem coppoMorseJosephsonPotentialMinus_decomposition (A a : ℝ) (n : ℕ) (x : ℝ) :
    coppoMorseJosephsonPotentialMinus A a n x =
      thetaCuspMorsePotentialMinus A n x + coppoSinePotentialMinus a x +
        2 * thetaCuspMorseSuperpotential A n x * coppoSineSuperpotential a x := by
  dsimp [coppoMorseJosephsonPotentialMinus, coppoMorseJosephsonSuperpotential,
    coppoMorseJosephsonCurvature, thetaCuspMorsePotentialMinus,
    coppoSinePotentialMinus, coppoSineSuperpotential]
  ring

/-- The upper partner has exactly the same interaction term. -/
theorem coppoMorseJosephsonPotentialPlus_decomposition (A a : ℝ) (n : ℕ) (x : ℝ) :
    coppoMorseJosephsonPotentialPlus A a n x =
      thetaCuspMorsePotentialPlus A n x + coppoSinePotentialPlus a x +
        2 * thetaCuspMorseSuperpotential A n x * coppoSineSuperpotential a x := by
  dsimp [coppoMorseJosephsonPotentialPlus, coppoMorseJosephsonSuperpotential,
    coppoMorseJosephsonCurvature, thetaCuspMorsePotentialPlus,
    coppoSinePotentialPlus, coppoSineSuperpotential]
  ring

/-- The partner split is four times the Morse scale plus the Josephson curvature. -/
theorem coppoMorseJosephson_partner_gap (A a : ℝ) (n : ℕ) (x : ℝ) :
    coppoMorseJosephsonPotentialPlus A a n x - coppoMorseJosephsonPotentialMinus A a n x =
      4 * thetaCuspMorseScale n x + 2 * a * Real.cos x := by
  dsimp [coppoMorseJosephsonPotentialPlus, coppoMorseJosephsonPotentialMinus,
    coppoMorseJosephsonCurvature]
  ring

/-- The deformed amplitude satisfies the exact second-order equation. -/
theorem hasDerivAt_coppoMorseJosephsonAmplitude_deriv (A a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (deriv (coppoMorseJosephsonAmplitude A a n))
      (coppoMorseJosephsonPotentialMinus A a n x * coppoMorseJosephsonAmplitude A a n x) x := by
  have heq : deriv (coppoMorseJosephsonAmplitude A a n) = fun y =>
      -coppoMorseJosephsonSuperpotential A a n y * coppoMorseJosephsonAmplitude A a n y :=
    funext fun y => (hasDerivAt_coppoMorseJosephsonAmplitude A a n y).deriv
  rw [heq]
  simpa only [Pi.mul_apply, Pi.neg_apply] using!
    (((hasDerivAt_coppoMorseJosephsonSuperpotential A a n x).neg.mul
      (hasDerivAt_coppoMorseJosephsonAmplitude A a n x)).congr_deriv (by
        dsimp [coppoMorseJosephsonPotentialMinus]; ring))

/-- An unconditional Schrödinger zero mode for the combined potential. -/
theorem coppoMorseJosephson_schrodinger_zero (A a : ℝ) (n : ℕ) (x : ℝ) :
    -deriv (deriv (coppoMorseJosephsonAmplitude A a n)) x +
      coppoMorseJosephsonPotentialMinus A a n x * coppoMorseJosephsonAmplitude A a n x = 0 := by
  rw [(hasDerivAt_coppoMorseJosephsonAmplitude_deriv A a n x).deriv]
  ring

/-- The original theta Gibbs atom receives exactly a positive periodic density tilt. -/
theorem coppoMorseJosephsonAmplitude_theta_density (a : ℝ) (n : ℕ) (x : ℝ) :
    coppoMorseJosephsonAmplitude (5 / 4) a n x ^ (2 : ℕ) =
      thetaCuspLiouvilleGibbsAtom n x * coppoJosephsonGroundState (2 * a) x := by
  change (thetaCuspMorseGroundState n x * coppoJosephsonGroundState a x) ^ (2 : ℕ) = _
  rw [mul_pow, thetaCuspMorseGroundState_sq, coppoJosephsonGroundState_sq]

/-- The periodic deformation preserves the original Morse Robin boundary coefficient. -/
theorem coppoMorseJosephson_robin (A a : ℝ) (n : ℕ) :
    deriv (coppoMorseJosephsonAmplitude A a n) 0 +
      thetaCuspMorseSuperpotential A n 0 * coppoMorseJosephsonAmplitude A a n 0 = 0 := by
  rw [(hasDerivAt_coppoMorseJosephsonAmplitude A a n 0).deriv]
  simp [coppoMorseJosephsonSuperpotential, coppoSineSuperpotential]

/-- The boundary density acquires a known, strictly positive scalar factor. -/
theorem coppoMorseJosephson_boundary_density (A a : ℝ) (n : ℕ) :
    coppoMorseJosephsonAmplitude A a n 0 ^ (2 : ℕ) =
      (n : ℝ) ^ (2 : ℕ) * Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ) + 2 * a) := by
  simp only [coppoMorseJosephsonAmplitude, thetaCuspMorseZeroMode, thetaCuspMorseScale,
    coppoJosephsonGroundState, Real.cos_zero, mul_zero, Real.exp_zero, mul_one]
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  ring

end RHTower
