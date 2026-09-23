import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Exact Josephson and supersymmetric potentials

The first two Josephson harmonics in arXiv:2405.03454 admit exact square
certificates for global minima. At the supersymmetric parameter relation, their
shifted potential is a Witten square with an explicit positive zero mode.
-/

noncomputable section
namespace HTGeometry

/-- The two-harmonic Josephson potential, with signed effective couplings. -/
def coppoJosephsonPotential (j k x : ℝ) : ℝ :=
  -j * Real.cos x + k * Real.cos (2 * x)

/-- Combining identical junctions gives the flux-dependent effective couplings. -/
theorem coppoJosephsonPotential_identical_junctions (j k x flux : ℝ) :
    coppoJosephsonPotential j k (x - flux) +
      coppoJosephsonPotential j k (x + flux) =
      coppoJosephsonPotential (2 * j * Real.cos flux) (2 * k * Real.cos (2 * flux)) x := by
  simp only [coppoJosephsonPotential, mul_add, mul_sub, Real.cos_add, Real.cos_sub]
  ring

/-- Reflection preserves the Josephson potential. -/
theorem coppoJosephsonPotential_reflection (j k x : ℝ) :
    coppoJosephsonPotential j k (-x) = coppoJosephsonPotential j k x := by
  simp [coppoJosephsonPotential]

/-- A half-turn flips only the first harmonic. -/
theorem coppoJosephsonPotential_halfTurn (j k x : ℝ) :
    coppoJosephsonPotential j k (x + Real.pi) = coppoJosephsonPotential (-j) k x := by
  simp [coppoJosephsonPotential, Real.cos_two_mul]

/-- A quarter-turn exchanges the pure second-harmonic qubits. -/
theorem coppoJosephsonPotential_quarterTurn (k x : ℝ) :
    coppoJosephsonPotential 0 k (x + Real.pi / 2) = coppoJosephsonPotential 0 (-k) x := by
  simp only [coppoJosephsonPotential, zero_mul, neg_zero, zero_add]
  rw [show 2 * (x + Real.pi / 2) = 2 * x + Real.pi by ring, Real.cos_add_pi]
  ring

/-- Exact first derivative, including both critical branches. -/
theorem hasDerivAt_coppoJosephsonPotential (j k x : ℝ) :
    HasDerivAt (coppoJosephsonPotential j k)
      (Real.sin x * (j - 4 * k * Real.cos x)) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (-j)).add
    (((Real.hasDerivAt_cos (2 * x)).comp x ((hasDerivAt_id x).const_mul 2)).const_mul k)
  simpa only [coppoJosephsonPotential, Pi.add_apply, Function.comp_apply] using!
    h.congr_deriv (by rw [Real.sin_two_mul]; ring)

/-- Exact energy difference from any proposed twist angle. -/
theorem coppoJosephsonPotential_twist_square (k theta x : ℝ) :
    coppoJosephsonPotential (4 * k * Real.cos theta) k x -
      coppoJosephsonPotential (4 * k * Real.cos theta) k theta =
      2 * k * (Real.cos x - Real.cos theta) ^ (2 : ℕ) := by
  simp only [coppoJosephsonPotential, Real.cos_two_mul]
  ring

/-- Every chosen twist angle is a global minimum at its constructed positive coupling. -/
theorem coppoJosephsonPotential_twist_global_min (t theta x : ℝ) :
    coppoJosephsonPotential (4 * Real.exp t * Real.cos theta) (Real.exp t) theta ≤
      coppoJosephsonPotential (4 * Real.exp t * Real.cos theta) (Real.exp t) x := by
  have h := coppoJosephsonPotential_twist_square (Real.exp t) theta x
  have hp : 0 ≤ 2 * Real.exp t * (Real.cos x - Real.cos theta) ^ (2 : ℕ) := by positivity
  linarith

/-- The complete set of twist minima is the cosine fibre of the chosen angle. -/
theorem coppoJosephsonPotential_twist_min_iff (t theta x : ℝ) :
    coppoJosephsonPotential (4 * Real.exp t * Real.cos theta) (Real.exp t) x =
      coppoJosephsonPotential (4 * Real.exp t * Real.cos theta) (Real.exp t) theta ↔
      Real.cos x = Real.cos theta := by
  rw [← sub_eq_zero, coppoJosephsonPotential_twist_square]
  have hp : 2 * Real.exp t ≠ 0 := by positivity
  simp [mul_eq_zero, hp, sub_eq_zero]

/-- Above the plasmonic threshold, the energy difference has two positive summands. -/
theorem coppoJosephsonPotential_plasmonic_square (k d x : ℝ) :
    coppoJosephsonPotential (4 * k + d) k x -
      coppoJosephsonPotential (4 * k + d) k 0 =
      2 * k * (1 - Real.cos x) ^ (2 : ℕ) + d * (1 - Real.cos x) := by
  simp only [coppoJosephsonPotential, Real.cos_two_mul, Real.cos_zero, mul_zero]
  ring

/-- A parameterized open plasmonic chamber has its global minimum at zero. -/
theorem coppoJosephsonPotential_plasmonic_global_min (t s x : ℝ) :
    coppoJosephsonPotential (4 * Real.exp t + Real.exp s) (Real.exp t) 0 ≤
      coppoJosephsonPotential (4 * Real.exp t + Real.exp s) (Real.exp t) x := by
  have h := coppoJosephsonPotential_plasmonic_square (Real.exp t) (Real.exp s) x
  have hc : 0 ≤ 1 - Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
  have hp : 0 ≤ 2 * Real.exp t * (1 - Real.cos x) ^ (2 : ℕ) + Real.exp s * (1 - Real.cos x) := by positivity
  linarith

/-- In the flux-biased chamber both contributions to the zero-well energy difference are positive. -/
theorem coppoJosephsonPotential_flux_square (j k x : ℝ) :
    coppoJosephsonPotential j (-k) x - coppoJosephsonPotential j (-k) 0 =
      j * (1 - Real.cos x) + 2 * k * Real.sin x ^ (2 : ℕ) := by
  simp only [coppoJosephsonPotential, Real.cos_two_mul, Real.cos_zero, mul_zero]
  rw [show Real.sin x ^ (2 : ℕ) = 1 - Real.cos x ^ (2 : ℕ) by nlinarith [Real.sin_sq_add_cos_sq x]]
  ring

/-- Positive first-harmonic bias selects the zero well globally. -/
theorem coppoJosephsonPotential_flux_global_min (t s x : ℝ) :
    coppoJosephsonPotential (Real.exp t) (-Real.exp s) 0 ≤
      coppoJosephsonPotential (Real.exp t) (-Real.exp s) x := by
  have h := coppoJosephsonPotential_flux_square (Real.exp t) (Real.exp s) x
  have hc : 0 ≤ 1 - Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
  have hp : 0 ≤ Real.exp t * (1 - Real.cos x) + 2 * Real.exp s * Real.sin x ^ (2 : ℕ) := by positivity
  linarith

/-- The circuit's sinusoidal Witten superpotential. -/
def coppoSineSuperpotential (a x : ℝ) : ℝ := a * Real.sin x

/-- The positive analytic zero mode at the supersymmetric parameter relation. -/
def coppoJosephsonGroundState (a x : ℝ) : ℝ := Real.exp (a * Real.cos x)

/-- The lower Witten potential. -/
def coppoSinePotentialMinus (a x : ℝ) : ℝ :=
  (a * Real.sin x) ^ (2 : ℕ) - a * Real.cos x

/-- The upper Witten potential. -/
def coppoSinePotentialPlus (a x : ℝ) : ℝ :=
  (a * Real.sin x) ^ (2 : ℕ) + a * Real.cos x

/-- Exact circuit-to-Witten conversion, including the energy offset. -/
theorem coppoSinePotentialMinus_eq_josephson (a x : ℝ) :
    coppoSinePotentialMinus a x = coppoJosephsonPotential a (-a ^ (2 : ℕ) / 2) x + a ^ (2 : ℕ) / 2 := by
  simp only [coppoSinePotentialMinus, coppoJosephsonPotential, Real.cos_two_mul, mul_pow]
  rw [show Real.sin x ^ (2 : ℕ) = 1 - Real.cos x ^ (2 : ℕ) by nlinarith [Real.sin_sq_add_cos_sq x]]
  ring

/-- The partner is the circuit with opposite first-harmonic bias. -/
theorem coppoSinePotentialPlus_eq_josephson (a x : ℝ) :
    coppoSinePotentialPlus a x = coppoJosephsonPotential (-a) (-a ^ (2 : ℕ) / 2) x + a ^ (2 : ℕ) / 2 := by
  simp only [coppoSinePotentialPlus, coppoJosephsonPotential, Real.cos_two_mul, mul_pow]
  rw [show Real.sin x ^ (2 : ℕ) = 1 - Real.cos x ^ (2 : ℕ) by nlinarith [Real.sin_sq_add_cos_sq x]]
  ring

/-- Half-period translation exchanges the two Witten partners. -/
theorem coppoSinePotentialMinus_halfTurn (a x : ℝ) :
    coppoSinePotentialMinus a (x + Real.pi) = coppoSinePotentialPlus a x := by
  simp [coppoSinePotentialMinus, coppoSinePotentialPlus]

/-- Partner splitting is exactly twice the superpotential derivative. -/
theorem coppoSinePotential_partner_gap (a x : ℝ) :
    coppoSinePotentialPlus a x - coppoSinePotentialMinus a x = 2 * a * Real.cos x := by
  dsimp [coppoSinePotentialPlus, coppoSinePotentialMinus]; ring

/-- The explicit circuit ground state has no zeros. -/
theorem coppoJosephsonGroundState_pos (a x : ℝ) : 0 < coppoJosephsonGroundState a x :=
  Real.exp_pos _

/-- Reflection leaves the ground state even. -/
theorem coppoJosephsonGroundState_even (a x : ℝ) :
    coppoJosephsonGroundState a (-x) = coppoJosephsonGroundState a x := by
  simp [coppoJosephsonGroundState]

/-- The first-order factor annihilates the explicit ground state. -/
theorem hasDerivAt_coppoJosephsonGroundState (a x : ℝ) :
    HasDerivAt (coppoJosephsonGroundState a)
      (-coppoSineSuperpotential a x * coppoJosephsonGroundState a x) x := by
  simpa only [coppoJosephsonGroundState, Function.comp_apply] using!
    (((Real.hasDerivAt_exp (a * Real.cos x)).comp x
      ((Real.hasDerivAt_cos x).const_mul a)).congr_deriv (by
        dsimp [coppoSineSuperpotential, coppoJosephsonGroundState]; ring))

/-- The ground state satisfies the exact first-order supersymmetric equation. -/
theorem coppoJosephsonGroundState_supercharge_zero (a x : ℝ) :
    deriv (coppoJosephsonGroundState a) x +
      coppoSineSuperpotential a x * coppoJosephsonGroundState a x = 0 := by
  rw [(hasDerivAt_coppoJosephsonGroundState a x).deriv]; ring

/-- The explicit second derivative proves the Schrödinger equation without a spectral assumption. -/
theorem hasDerivAt_coppoJosephsonGroundState_deriv (a x : ℝ) :
    HasDerivAt (deriv (coppoJosephsonGroundState a))
      (coppoSinePotentialMinus a x * coppoJosephsonGroundState a x) x := by
  have heq : deriv (coppoJosephsonGroundState a) = fun y =>
      -coppoSineSuperpotential a y * coppoJosephsonGroundState a y :=
    funext fun y => (hasDerivAt_coppoJosephsonGroundState a y).deriv
  rw [heq]
  simpa only [coppoSineSuperpotential, Pi.mul_apply, Pi.neg_apply] using!
    ((((Real.hasDerivAt_sin x).const_mul a).neg.mul
      (hasDerivAt_coppoJosephsonGroundState a x)).congr_deriv (by
        dsimp [coppoSineSuperpotential, coppoSinePotentialMinus]; ring))

/-- Exact Josephson eigenfunction and eigenvalue at every supersymmetric coupling. -/
theorem coppoJosephsonGroundState_schrodinger (a x : ℝ) :
    -deriv (deriv (coppoJosephsonGroundState a)) x +
      coppoJosephsonPotential a (-a ^ (2 : ℕ) / 2) x * coppoJosephsonGroundState a x =
      (-a ^ (2 : ℕ) / 2) * coppoJosephsonGroundState a x := by
  rw [(hasDerivAt_coppoJosephsonGroundState_deriv a x).deriv,
    coppoSinePotentialMinus_eq_josephson]
  ring

/-- Ground-state densities have the same analytic family, with doubled coupling. -/
theorem coppoJosephsonGroundState_sq (a x : ℝ) :
    coppoJosephsonGroundState a x ^ (2 : ℕ) = coppoJosephsonGroundState (2 * a) x := by
  rw [coppoJosephsonGroundState, pow_two, ← Real.exp_add, coppoJosephsonGroundState]
  congr 1; ring

end HTGeometry
