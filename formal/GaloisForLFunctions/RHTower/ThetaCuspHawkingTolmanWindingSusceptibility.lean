import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeSource

/-!
# Hawking--Tolman winding susceptibility of the theta cusp source

This file derives the theta-cusp seed from a black-hole thermal observable before using any
zeta or Xi identity.  In Euclidean Rindler coordinates, smoothness at the horizon fixes the
thermal-circle period by `beta * kappa = 2*pi`.  An `m`-winding worldsheet sector at fixed
proper time therefore carries the dimensionless Gaussian profile

`W_m(Theta) = exp (-pi * (m / Theta)^(2 : ℕ))`,

where `Theta` is local Tolman temperature and `1 / Theta` is proper thermal-circle radius.
The scaled second temperature response is exactly

`Theta^(2 : ℕ) * d^(2 : ℕ) W_m / dTheta^(2 : ℕ) = thetaCuspSeed (m / Theta)`.

Worldsheet proper time and `alpha'` have been absorbed into the dimensionless radius.  We retain
one winding orientation: the zero-winding response vanishes, while adjoining the opposite
orientation doubles every nonzero term and hence changes no Fourier zero.

Thus the polynomial multiplying the theta Gaussian is not a KMS ansatz: it is the literal
local-temperature susceptibility of the Hawking winding gas.  Removing the Rindler
`sqrt(G_00)` measure gives the half-line thermal-scalar operator and its singular
`-1/(4*rho^(2 : ℕ))` horizon potential.  The subsequent unitary change to logarithmic redshift
`x = log (1 / Theta)` supplies the half-density `exp(x/2)`.  The result is exactly
`thetaCuspSourceTerm`; summing all windings gives `thetaCuspFullSource`.

The seed has a genuine negative chamber.  This agrees with the Euclidean Schwarzschild
negative mode/negative heat capacity and rules out any proof that tries to obtain RH by declaring
the Hawking susceptibility positive from generic passivity.

Physics sources:

* Mertens--Verschelde--Zakharov, *Random Walks in Rindler Spacetime and String Theory at the
  Tip of the Cigar*, arXiv:1307.3491, especially equations (2), (16), (55)--(58).
* Brustein--Zigdon, *Black Hole Entropy Sourced by String Winding Condensate*,
  arXiv:2107.09001, for backreaction of the near-horizon winding condensate on the thermal cycle.
* Halder--Jafferis, *Stretched horizon, replica trick and off-shell winding condensate, and all
  that*, arXiv:2402.00932, for fractional winding and the stringy area response.
* Hirayama, *Negative mode of Schwarzschild black hole from the thermodynamic instability*,
  arXiv:1012.0441.

No generic no-dark-mode RH equivalence is added here.  The black-hole-specific speculative endpoint
is sharper: derive that any nonzero conical/redshift tilt at which this susceptibility becomes dark
creates an additional normalizable negative direction of the coupled metric--dilaton--winding
Euclidean Hessian.  A theorem that the full cigar/worldsheet Hessian has only the Schwarzschild size
mode would then force the tilt to vanish.  Neither generic KMS/passivity nor the identities below
prove that Morse-index statement.
-/

open Filter Set

noncomputable section

namespace RHTower

/-- Fixed-winding Euclidean Hawking-circle profile as a function of local Tolman temperature. -/
def thetaCuspHawkingTolmanWindingProfile (m Theta : ℝ) : ℝ :=
  thetaCuspGaussian (m / Theta)

/-- Closed first Tolman-temperature response of one winding sector. -/
def thetaCuspHawkingTolmanWindingSlope (m Theta : ℝ) : ℝ :=
  2 * Real.pi * m ^ (2 : ℕ) / Theta ^ (3 : ℕ) *
    thetaCuspHawkingTolmanWindingProfile m Theta

/-- Closed second Tolman-temperature response of one winding sector. -/
def thetaCuspHawkingTolmanWindingCurvature (m Theta : ℝ) : ℝ :=
  (4 * Real.pi ^ (2 : ℕ) * m ^ (4 : ℕ) / Theta ^ (6 : ℕ) -
      6 * Real.pi * m ^ (2 : ℕ) / Theta ^ (4 : ℕ)) *
    thetaCuspHawkingTolmanWindingProfile m Theta

theorem hasDerivAt_thetaCuspHawkingTolmanWindingProfile
    {m Theta : ℝ} (hTheta : Theta ≠ 0) :
    HasDerivAt (thetaCuspHawkingTolmanWindingProfile m)
      (thetaCuspHawkingTolmanWindingSlope m Theta) Theta := by
  have hquot : HasDerivAt (fun T : ℝ => m / T)
      ((0 * Theta - m * 1) / Theta ^ (2 : ℕ)) Theta :=
    (hasDerivAt_const Theta m).div (hasDerivAt_id Theta) hTheta
  have hcomp := (hasDerivAt_thetaCuspGaussian (m / Theta)).comp Theta hquot
  change HasDerivAt (fun T : ℝ => thetaCuspGaussian (m / T)) _ Theta at hcomp
  change HasDerivAt (thetaCuspHawkingTolmanWindingProfile m) _ Theta
  apply hcomp.congr_deriv
  rw [thetaCuspHawkingTolmanWindingSlope,
    thetaCuspHawkingTolmanWindingProfile, thetaCuspGaussian]
  field_simp [hTheta]
  ring

theorem deriv_thetaCuspHawkingTolmanWindingProfile
    {m Theta : ℝ} (hTheta : Theta ≠ 0) :
    deriv (thetaCuspHawkingTolmanWindingProfile m) Theta =
      thetaCuspHawkingTolmanWindingSlope m Theta :=
  (hasDerivAt_thetaCuspHawkingTolmanWindingProfile hTheta).deriv

theorem hasDerivAt_thetaCuspHawkingTolmanWindingSlope
    {m Theta : ℝ} (hTheta : Theta ≠ 0) :
    HasDerivAt (thetaCuspHawkingTolmanWindingSlope m)
      (thetaCuspHawkingTolmanWindingCurvature m Theta) Theta := by
  have hden : HasDerivAt (fun T : ℝ => T ^ (3 : ℕ)) (3 * Theta ^ (2 : ℕ)) Theta := by
    simpa using hasDerivAt_pow 3 Theta
  have hcoef : HasDerivAt (fun T : ℝ => 2 * Real.pi * m ^ (2 : ℕ) / T ^ (3 : ℕ))
      ((0 * Theta ^ (3 : ℕ) - (2 * Real.pi * m ^ (2 : ℕ)) * (3 * Theta ^ (2 : ℕ))) /
        (Theta ^ (3 : ℕ)) ^ (2 : ℕ)) Theta :=
    (hasDerivAt_const Theta (2 * Real.pi * m ^ (2 : ℕ))).div hden (pow_ne_zero 3 hTheta)
  have hprod := hcoef.mul
    (hasDerivAt_thetaCuspHawkingTolmanWindingProfile (m := m) hTheta)
  change HasDerivAt
    (fun T : ℝ => (2 * Real.pi * m ^ (2 : ℕ) / T ^ (3 : ℕ)) *
      thetaCuspHawkingTolmanWindingProfile m T) _ Theta at hprod
  change HasDerivAt (thetaCuspHawkingTolmanWindingSlope m) _ Theta
  apply hprod.congr_deriv
  rw [thetaCuspHawkingTolmanWindingCurvature,
    thetaCuspHawkingTolmanWindingSlope]
  field_simp [hTheta]
  ring

theorem eventuallyEq_deriv_thetaCuspHawkingTolmanWindingProfile
    {m Theta : ℝ} (hTheta : Theta ≠ 0) :
    deriv (thetaCuspHawkingTolmanWindingProfile m) =ᶠ[nhds Theta]
      thetaCuspHawkingTolmanWindingSlope m := by
  filter_upwards [isOpen_compl_singleton.mem_nhds
    (by simpa using hTheta : Theta ∈ ({0}ᶜ : Set ℝ))] with T hT
  exact deriv_thetaCuspHawkingTolmanWindingProfile (by simpa using hT)

theorem hasDerivAt_deriv_thetaCuspHawkingTolmanWindingProfile
    {m Theta : ℝ} (hTheta : Theta ≠ 0) :
    HasDerivAt (deriv (thetaCuspHawkingTolmanWindingProfile m))
      (thetaCuspHawkingTolmanWindingCurvature m Theta) Theta :=
  (hasDerivAt_thetaCuspHawkingTolmanWindingSlope hTheta).congr_of_eventuallyEq
    (eventuallyEq_deriv_thetaCuspHawkingTolmanWindingProfile hTheta)

theorem deriv_deriv_thetaCuspHawkingTolmanWindingProfile
    {m Theta : ℝ} (hTheta : Theta ≠ 0) :
    deriv (deriv (thetaCuspHawkingTolmanWindingProfile m)) Theta =
      thetaCuspHawkingTolmanWindingCurvature m Theta :=
  (hasDerivAt_deriv_thetaCuspHawkingTolmanWindingProfile hTheta).deriv

/-- Scaled local-temperature susceptibility of one Hawking winding sector. -/
def thetaCuspHawkingTolmanWindingSusceptibility (m Theta : ℝ) : ℝ :=
  Theta ^ (2 : ℕ) * deriv (deriv (thetaCuspHawkingTolmanWindingProfile m)) Theta

/-- Exact Hawking--Tolman origin of the theta-cusp polynomial Gaussian. -/
theorem thetaCuspHawkingTolmanWindingSusceptibility_eq_thetaCuspSeed
    {m Theta : ℝ} (hTheta : Theta ≠ 0) :
    thetaCuspHawkingTolmanWindingSusceptibility m Theta =
      thetaCuspSeed (m / Theta) := by
  rw [thetaCuspHawkingTolmanWindingSusceptibility,
    deriv_deriv_thetaCuspHawkingTolmanWindingProfile hTheta,
    thetaCuspHawkingTolmanWindingCurvature,
    thetaCuspHawkingTolmanWindingProfile, thetaCuspSeed, thetaCuspGaussian]
  field_simp [hTheta]
  ring

/-- Same response written as the exact scaling Hamiltonian `D^(2 : ℕ) + D`. -/
theorem thetaCuspHawkingTolmanWindingSusceptibility_eq_multiplicativeDeriv
    {m Theta : ℝ} (hTheta : Theta ≠ 0) :
    thetaCuspHawkingTolmanWindingSusceptibility m Theta =
      multiplicativeDeriv (multiplicativeDeriv thetaCuspGaussian) (m / Theta) +
        multiplicativeDeriv thetaCuspGaussian (m / Theta) := by
  rw [thetaCuspHawkingTolmanWindingSusceptibility_eq_thetaCuspSeed hTheta,
    multiplicativeDeriv_sq_add_apply_thetaCuspGaussian]

/-- Tolman temperature along logarithmic horizon redshift `x`. -/
def thetaCuspHawkingTolmanTemperature (x : ℝ) : ℝ :=
  Real.exp (-x)

/-- Canonical log-redshift half-density of one winding susceptibility. -/
def thetaCuspHawkingTolmanWindingSourceTerm (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (x / 2) * thetaCuspHawkingTolmanWindingSusceptibility n
    (thetaCuspHawkingTolmanTemperature x)

/-- Every theta-cusp source atom is exactly one Hawking--Tolman winding susceptibility. -/
theorem thetaCuspHawkingTolmanWindingSourceTerm_eq_thetaCuspSourceTerm
    (x : ℝ) (n : ℕ) :
    thetaCuspHawkingTolmanWindingSourceTerm x n = thetaCuspSourceTerm x n := by
  rw [thetaCuspHawkingTolmanWindingSourceTerm,
    thetaCuspHawkingTolmanTemperature,
    thetaCuspHawkingTolmanWindingSusceptibility_eq_thetaCuspSeed
      (Real.exp_ne_zero (-x))]
  simp only [thetaCuspSourceTerm]
  congr 2
  rw [div_eq_mul_inv, ← Real.exp_neg]
  ring_nf

/-- Full multiwinding Hawking susceptibility in logarithmic redshift. -/
def thetaCuspHawkingTolmanFullWindingSource (x : ℝ) : ℝ :=
  ∑' n : ℕ, thetaCuspHawkingTolmanWindingSourceTerm x n

/-- The full Hawking winding susceptibility is the exact theta-cusp source. -/
theorem thetaCuspHawkingTolmanFullWindingSource_eq_thetaCuspFullSource (x : ℝ) :
    thetaCuspHawkingTolmanFullWindingSource x = thetaCuspFullSource x := by
  apply tsum_congr
  exact thetaCuspHawkingTolmanWindingSourceTerm_eq_thetaCuspSourceTerm x

/-- The polynomial Gaussian has an unavoidable negative Tolman-response chamber. -/
theorem thetaCuspSeed_neg_thetaCuspHawkingTolmanWindingSusceptibility {t : ℝ} (ht0 : t ≠ 0)
    (ht : 2 * Real.pi * t ^ (2 : ℕ) < 3) :
    thetaCuspSeed t < 0 := by
  have ht2 : 0 < t ^ (2 : ℕ) := sq_pos_of_ne_zero ht0
  have hpoly : 2 * Real.pi * t ^ (4 : ℕ) - 3 * t ^ (2 : ℕ) < 0 := by
    rw [show 2 * Real.pi * t ^ (4 : ℕ) - 3 * t ^ (2 : ℕ) =
      t ^ (2 : ℕ) * (2 * Real.pi * t ^ (2 : ℕ) - 3) by ring]
    exact mul_neg_of_pos_of_neg ht2 (sub_neg.mpr ht)
  rw [thetaCuspSeed]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos (by norm_num) Real.pi_pos) hpoly)
    (Real.exp_pos _)

/-- Actual Hawking winding susceptibility is negative in that chamber; generic passivity cannot
make this statement disappear. -/
theorem thetaCuspHawkingTolmanWindingSusceptibility_neg
    {m Theta : ℝ} (hTheta : Theta ≠ 0) (hscale : m / Theta ≠ 0)
    (hchamber : 2 * Real.pi * (m / Theta) ^ (2 : ℕ) < 3) :
    thetaCuspHawkingTolmanWindingSusceptibility m Theta < 0 := by
  rw [thetaCuspHawkingTolmanWindingSusceptibility_eq_thetaCuspSeed hTheta]
  exact thetaCuspSeed_neg_thetaCuspHawkingTolmanWindingSusceptibility hscale hchamber

end RHTower
