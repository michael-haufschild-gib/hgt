import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPositiveChamber

/-!
# Gamma-sewn Euler current on the complex positive half-plane

The Kummer phase is a norm-one height multiplier.  Composing it with the full positive-chamber
Stokes operator sends the physical sewn dual feature exactly to the complex von Mangoldt current
at every parameter with positive real part.  Rapid tests make this current continuous even below
the half-plane of absolute convergence of its total mass.

This is a source-native continuation: no zeta continuation, Xi divisor, or RH-equivalent premise
is used.
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Unit-modulus Kummer phase at vertical frequency `t`. -/
def gammaSewnMobiusApertureStokesKummerPhaseMultiplier
    (t : ℝ) (m : DeningerPrimeLattice) : ℂ :=
  Complex.exp (-((t : ℂ) * Complex.I) * ((deningerFreq m : ℝ) : ℂ))

theorem norm_gammaSewnMobiusApertureStokesKummerPhaseMultiplier
    (t : ℝ) (m : DeningerPrimeLattice) :
    ‖gammaSewnMobiusApertureStokesKummerPhaseMultiplier t m‖ = 1 := by
  rw [gammaSewnMobiusApertureStokesKummerPhaseMultiplier, Complex.norm_exp]
  simp [Complex.mul_re]

theorem norm_gammaSewnMobiusApertureStokesKummerPhaseMultiplier_le
    (t : ℝ) (m : DeningerPrimeLattice) :
    ‖gammaSewnMobiusApertureStokesKummerPhaseMultiplier t m‖ ≤
      deningerHeight m ^ 0 := by
  rw [norm_gammaSewnMobiusApertureStokesKummerPhaseMultiplier, pow_zero]

/-- Norm-preserving vertical phase action on rapid Kummer tests. -/
def gammaSewnMobiusApertureStokesKummerPhaseOperator (t : ℝ) :
    DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  deningerHeightMul
    (gammaSewnMobiusApertureStokesKummerPhaseMultiplier t) 0
    (norm_gammaSewnMobiusApertureStokesKummerPhaseMultiplier_le t)

@[simp] theorem gammaSewnMobiusApertureStokesKummerPhaseOperator_coe
    (t : ℝ) (a : DeningerHeightKothe) (m : DeningerPrimeLattice) :
    ((gammaSewnMobiusApertureStokesKummerPhaseOperator t a :
        DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m =
      gammaSewnMobiusApertureStokesKummerPhaseMultiplier t m *
        (a : DeningerPrimeLattice → ℂ) m :=
  rfl

theorem deningerHeightSeminorm_gammaSewnMobiusApertureStokesKummerPhaseOperator
    (t : ℝ) (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k
        (gammaSewnMobiusApertureStokesKummerPhaseOperator t a) =
      deningerHeightSeminorm k a := by
  rw [deningerHeightSeminorm_apply, deningerHeightSeminorm_apply]
  refine tsum_congr fun m => ?_
  rw [gammaSewnMobiusApertureStokesKummerPhaseOperator_coe, norm_mul,
    norm_gammaSewnMobiusApertureStokesKummerPhaseMultiplier, one_mul]

theorem deningerFreq_gammaSewnMobiusApertureStokesPrimePowerAxis
    (pk : Nat.Primes × ℕ) :
    deningerFreq (gammaSewnMobiusApertureStokesPrimePowerAxis pk) =
      (pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ) := by
  rcases pk with ⟨p, e⟩
  rw [deningerFreq, gammaSewnMobiusApertureStokesPrimePowerAxis,
    Finsupp.sum_single_index]
  · norm_cast
  · simp

theorem gammaSewnMobiusApertureStokesKummerPhaseMultiplier_primePowerAxis
    (t : ℝ) (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesKummerPhaseMultiplier t
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk) =
      Complex.exp (-((t : ℂ) * Complex.I) *
        (((pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ) : ℝ) : ℂ)) := by
  rw [gammaSewnMobiusApertureStokesKummerPhaseMultiplier,
    deningerFreq_gammaSewnMobiusApertureStokesPrimePowerAxis]

/-- One real Euler coefficient times Kummer phase is exactly the complex Euler coefficient. -/
theorem primePowerFluxTerm_ofReal_add_imaginary
    (sigma t : ℝ) (pk : Nat.Primes × ℕ) :
    primePowerFluxTerm (sigma : ℂ) pk *
        Complex.exp (-((t : ℂ) * Complex.I) *
          (((pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ) : ℝ) : ℂ)) =
      primePowerFluxTerm ((sigma : ℂ) + (t : ℂ) * Complex.I) pk := by
  have hp0 : 0 < ((pk.1 : ℕ) : ℝ) := by
    exact_mod_cast pk.1.2.pos
  have hx0 : (((pk.1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast pk.1.2.ne_zero
  have hsplit :
      (((pk.1 : ℕ) : ℂ)) ^ (-((sigma : ℂ) + (t : ℂ) * Complex.I)) =
        (((pk.1 : ℕ) : ℂ)) ^ (-(sigma : ℂ)) *
          (((pk.1 : ℕ) : ℂ)) ^ (-((t : ℂ) * Complex.I)) := by
    rw [show -((sigma : ℂ) + (t : ℂ) * Complex.I) =
      -(sigma : ℂ) + -((t : ℂ) * Complex.I) by ring]
    exact Complex.cpow_add _ _ hx0
  have himag :
      (((pk.1 : ℕ) : ℂ)) ^ (-((t : ℂ) * Complex.I)) =
        Complex.exp (-((t : ℂ) * Complex.I) *
          ((Real.log (pk.1 : ℕ) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hx0]
    rw [← Complex.natCast_log]
    congr 1
    ring
  have hphase :
      Complex.exp (-((t : ℂ) * Complex.I) *
          (((pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ) : ℝ) : ℂ)) =
        Complex.exp (-((t : ℂ) * Complex.I) *
          ((Real.log (pk.1 : ℕ) : ℝ) : ℂ)) ^ (pk.2 + 1) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [primePowerFluxTerm, primePowerFluxTerm]
  rw [hsplit, mul_pow, himag, hphase]
  ring

/-- Complex Euler current evaluated on rapid Kummer tests. -/
def gammaSewnMobiusApertureStokesComplexEulerDualPairing
    (s : ℂ) (a : DeningerHeightKothe) : ℂ :=
  ∑' pk : Nat.Primes × ℕ,
    primePowerFluxTerm s pk *
      (a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk)

/-- **Complex positive-half-plane transpose law.** Vertical Kummer phase plus real-aperture Stokes
connection produces every complex Euler coefficient with `Re(s)>0`. -/
theorem gammaSewnMobiusApertureStokesDualFeaturePairing_phase_positiveChamber_eq_complexEuler
    {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) (a : DeningerHeightKothe) :
    gammaSewnMobiusApertureStokesDualFeaturePairing sigma
        (gammaSewnMobiusApertureStokesPositiveChamberOperator sigma hsigma
          (gammaSewnMobiusApertureStokesKummerPhaseOperator t a)) =
      gammaSewnMobiusApertureStokesComplexEulerDualPairing
        ((sigma : ℂ) + (t : ℂ) * Complex.I) a := by
  rw [gammaSewnMobiusApertureStokesDualFeaturePairing_positiveChamberOperator_eq_euler]
  rw [gammaSewnMobiusApertureStokesEulerDualPairing,
    gammaSewnMobiusApertureStokesComplexEulerDualPairing]
  refine tsum_congr fun pk => ?_
  rw [gammaSewnMobiusApertureStokesKummerPhaseOperator_coe,
    gammaSewnMobiusApertureStokesKummerPhaseMultiplier_primePowerAxis,
    ← mul_assoc, primePowerFluxTerm_ofReal_add_imaginary]

/-- Complex Euler current is continuous on rapid tests throughout `Re(s)>0`, with the same
two-step source loss as the real chamber. -/
theorem norm_gammaSewnMobiusApertureStokesComplexEulerDualPairing_le
    {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) (a : DeningerHeightKothe) :
    ‖gammaSewnMobiusApertureStokesComplexEulerDualPairing
        ((sigma : ℂ) + (t : ℂ) * Complex.I) a‖ ≤
      gammaSewnMobiusApertureStokesPositiveChamberConstant sigma *
        deningerHeightSeminorm 2 a := by
  rw [← gammaSewnMobiusApertureStokesDualFeaturePairing_phase_positiveChamber_eq_complexEuler
    hsigma]
  rw [gammaSewnMobiusApertureStokesDualFeaturePairing_positiveChamberOperator_eq_euler]
  have h :=
    norm_gammaSewnMobiusApertureStokesEulerDualPairing_le_positiveChamber hsigma
      (gammaSewnMobiusApertureStokesKummerPhaseOperator t a)
  rwa [deningerHeightSeminorm_gammaSewnMobiusApertureStokesKummerPhaseOperator] at h

end RHTower
