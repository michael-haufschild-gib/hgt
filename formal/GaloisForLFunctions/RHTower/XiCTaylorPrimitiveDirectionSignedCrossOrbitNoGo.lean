import GaloisForLFunctions.RHTower.XiCTaylorPrimitiveDirectionTranspositionSuperselection
import GaloisForLFunctions.RHTower.XiSourceSpinThinningCoherence

/-!
# Signed cross-orbit incidence no-go for XST

The complete primitive-direction source current is fixed by coordinate transposition.  Therefore
every transposition-odd reporter on the whole current family vanishes, without linearity,
continuity, boundedness, finite support, or an orbitwise decomposition assumption.

Consequently a signed cross-orbit incidence can land on the centered Hurwitz spin defect exactly
when that defect already vanishes.  On every Xi divisor this is ambient-spin inheritance; globally
it is RH.  A pre-divisor coefficient-faithful signed incidence is impossible, witnessed already
by the half exponent.

This closes the stated XST producer based on signed incidence between transpose orbits.  A successor
would have to add source data which itself breaks primitive-coordinate transposition symmetry.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Pullback of a complete primitive-direction family by coordinate transposition. -/
def thetaCuspPrimitiveDirectionCurrentFamilyTranspose
    (F : ThetaCuspPrimitiveDirection → ℝ) :
    ThetaCuspPrimitiveDirection → ℝ :=
  fun q => F (thetaCuspPrimitiveDirectionTranspose q)

/-- Complete primitive-direction source current as one family over all coprime directions. -/
def xiCTaylorThetaTailPrimitiveDirectionCurrentFamily
    (d : ℕ) (z : ℂ) : ThetaCuspPrimitiveDirection → ℝ :=
  fun q => xiCTaylorThetaTailPrimitiveDirectionCurrent q d z

/-- The full primitive-direction current family is fixed by transposition. -/
theorem xiCTaylorThetaTailPrimitiveDirectionCurrentFamily_transpose
    (d : ℕ) (z : ℂ) :
    thetaCuspPrimitiveDirectionCurrentFamilyTranspose
        (xiCTaylorThetaTailPrimitiveDirectionCurrentFamily d z) =
      xiCTaylorThetaTailPrimitiveDirectionCurrentFamily d z := by
  funext q
  exact xiCTaylorThetaTailPrimitiveDirectionCurrent_transpose q d z

/-- Arbitrary, possibly nonlinear, reporter transforming by the sign character under simultaneous
transposition of the entire primitive-direction family.  Its input includes all transpose orbits,
so cross-orbit couplings and infinite-support constructions are inside this interface. -/
structure XSTSignedCrossOrbitIncidence where
  incidence : (ThetaCuspPrimitiveDirection → ℝ) → ℂ
  transpose_odd : ∀ F,
    incidence (thetaCuspPrimitiveDirectionCurrentFamilyTranspose F) =
      -incidence F

/-- Every signed full-family incidence vanishes on the actual complete source current. -/
theorem XSTSignedCrossOrbitIncidence.current_eq_zero
    (I : XSTSignedCrossOrbitIncidence) (d : ℕ) (z : ℂ) :
    I.incidence (xiCTaylorThetaTailPrimitiveDirectionCurrentFamily d z) = 0 := by
  have h := I.transpose_odd
    (xiCTaylorThetaTailPrimitiveDirectionCurrentFamily d z)
  rw [xiCTaylorThetaTailPrimitiveDirectionCurrentFamily_transpose] at h
  have htwo :
      I.incidence (xiCTaylorThetaTailPrimitiveDirectionCurrentFamily d z) +
          I.incidence (xiCTaylorThetaTailPrimitiveDirectionCurrentFamily d z) = 0 := by
    have hadd := congrArg
      (fun w => w + I.incidence
        (xiCTaylorThetaTailPrimitiveDirectionCurrentFamily d z)) h
    simpa using hadd
  have htwo' : (2 : ℂ) *
      I.incidence (xiCTaylorThetaTailPrimitiveDirectionCurrentFamily d z) = 0 := by
    simpa [two_mul] using htwo
  exact (mul_eq_zero.mp htwo').resolve_left (by norm_num)

/-- Divisor-specialized claim that one signed source incidence lands on the actual centered spin
defect. -/
def XSTSignedCrossOrbitSpinLandingAt
    (I : XSTSignedCrossOrbitIncidence) (rho : XiDivisorSupport) (d : ℕ) : Prop :=
  I.incidence
      (xiCTaylorThetaTailPrimitiveDirectionCurrentFamily d (rho : ℂ)) =
    HurwitzOrbit.monoScalar (primeDepthBVWoldXiCenteredRate rho : ℂ) - 1

/-- A signed cross-orbit landing does not produce spin inheritance: it is exactly the already
vanishing centered monodromy condition. -/
theorem xstSignedCrossOrbitSpinLandingAt_iff_spinThinningCoherent
    (I : XSTSignedCrossOrbitIncidence) (rho : XiDivisorSupport) (d : ℕ) :
    XSTSignedCrossOrbitSpinLandingAt I rho d ↔
      XiCenteredThetaSpinThinningCoherent rho := by
  rw [XSTSignedCrossOrbitSpinLandingAt,
    I.current_eq_zero d (rho : ℂ),
    xiCenteredThetaSpinThinningCoherent_iff_monoScalar_eq_one]
  constructor
  · intro h
    exact sub_eq_zero.mp h.symm
  · intro h
    rw [h]
    norm_num

/-- Universal signed-incidence landing on all Xi divisor copies. -/
def EveryXSTSignedCrossOrbitSpinLanding
    (I : XSTSignedCrossOrbitIncidence) (d : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport, XSTSignedCrossOrbitSpinLandingAt I rho d

/-- For every signed full-family incidence, its claimed global XST landing is exactly RH rather
than an upstream source theorem. -/
theorem everyXSTSignedCrossOrbitSpinLanding_iff_riemannHypothesis
    (I : XSTSignedCrossOrbitIncidence) (d : ℕ) :
    EveryXSTSignedCrossOrbitSpinLanding I d ↔ RiemannHypothesis := by
  rw [← everyXiCenteredThetaSpinThinningCoherent_iff_riemannHypothesis]
  unfold EveryXSTSignedCrossOrbitSpinLanding EveryXiCenteredThetaSpinThinningCoherent
  apply forall_congr'
  intro rho
  exact xstSignedCrossOrbitSpinLandingAt_iff_spinThinningCoherent I rho d

/-- Proposed pre-divisor XST producer: one signed reporter must retain every real monodromy
coefficient from the corresponding complete source family. -/
structure XSTCoefficientFaithfulSignedCrossOrbitIncidence extends
    XSTSignedCrossOrbitIncidence where
  coefficientFaithful : ∀ a : ℝ,
    incidence
        (xiCTaylorThetaTailPrimitiveDirectionCurrentFamily 0 (a : ℂ)) =
      HurwitzOrbit.monoScalar (a : ℂ) - 1

/-- No signed, coefficient-faithful cross-orbit incidence exists, even with arbitrary nonlinear
dependence on the full infinite direction family. -/
theorem not_nonempty_XSTCoefficientFaithfulSignedCrossOrbitIncidence :
    ¬ Nonempty XSTCoefficientFaithfulSignedCrossOrbitIncidence := by
  rintro ⟨I⟩
  have hzero := I.toXSTSignedCrossOrbitIncidence.current_eq_zero 0 ((1 / 2 : ℝ) : ℂ)
  have hfaith := I.coefficientFaithful (1 / 2)
  have hmonoReal : HurwitzOrbit.monoScalar (((1 / 2 : ℝ) : ℂ)) = 1 := by
    rw [hzero] at hfaith
    exact sub_eq_zero.mp hfaith.symm
  have hmono : HurwitzOrbit.monoScalar (1 / 2 : ℂ) = 1 := by
    simpa using hmonoReal
  obtain ⟨m, hm⟩ := (HurwitzOrbit.monoScalar_eq_one_iff (1 / 2 : ℂ)).mp hmono
  have hre := congrArg Complex.re hm
  norm_num at hre
  have hmposR : (0 : ℝ) < (m : ℝ) := by rw [← hre]; norm_num
  have hmltR : (m : ℝ) < 1 := by rw [← hre]; norm_num
  have hmpos : (0 : ℤ) < m := by exact_mod_cast hmposR
  have hmlt : m < (1 : ℤ) := by exact_mod_cast hmltR
  omega

/-- Closed XST route verdict for the signed cross-orbit architecture. -/
theorem xst_signedCrossOrbitIncidence_noGo :
    (∀ I : XSTSignedCrossOrbitIncidence, ∀ d : ℕ,
        EveryXSTSignedCrossOrbitSpinLanding I d ↔ RiemannHypothesis) ∧
      ¬ Nonempty XSTCoefficientFaithfulSignedCrossOrbitIncidence := by
  exact ⟨everyXSTSignedCrossOrbitSpinLanding_iff_riemannHypothesis,
    not_nonempty_XSTCoefficientFaithfulSignedCrossOrbitIncidence⟩

end

end RHTower
