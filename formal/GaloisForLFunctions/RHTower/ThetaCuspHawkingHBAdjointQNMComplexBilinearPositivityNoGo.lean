import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTotalCokernelClockDefectTransduction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingHBFullCokernelKMSPassivityPolarityNoGo

/-!
# Complex-bilinear adjoint-QNM phase/positivity no-go for HB

The Teukolsky QNM adjoint pairing is complex-linear in both entries, rather than Hermitian.  Its
diagonal therefore has phase weight two:

`B (z x) (z x) = z^(2 : ℕ) B x x`.

In particular `B (I x) (I x) = -B x x`.  A diagonal value cannot consequently descend through
the common phase of one physical source ray unless it vanishes.  The same rotation proves the
stronger positivity obstruction: if one fixed nonzero calibration makes every diagonal value a
nonnegative real, every diagonal value is zero; for a symmetric pairing, polarization makes the
whole pairing zero.

Applied to the complete target-independent HB full-cokernel orbit, existence of a phase-descended
complex-bilinear diagonal landing is pointwise exactly the critical wall and globally exactly RH.
It is therefore an RH receiver, not a producer of the missing physical sign.  Together with the
existing finite-KMS/Hermitian wrong-polarity theorem, this kills both diagonal possibilities:
complex-bilinear diagonals retain phase but do not descend, while Hermitian diagonals descend but
have the already-known passive polarity.

The sharp survivor is off-diagonal polarization: source and left-QNM legs must transform
independently, so their combined value can have phase weight zero without replacing the physical
adjoint period by a positive Hermitian norm.

`[NEW] [HB ROUTE KILL] [ADJOINT QNM] [COMPLEX BILINEAR] [PHASE DESCENT] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- A complex-bilinear diagonal is claimed to represent the same physical scalar on the source
representatives `x` and `I x`. -/
def d4HBAdjointQNMComplexBilinearDiagonalRayLanding
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ) (x : X) (value : ℂ) : Prop :=
  B x x = value ∧ B (Complex.I • x) (Complex.I • x) = value

/-- Exact positive survivor: a complex-bilinear diagonal has phase weight two. -/
theorem d4HBAdjointQNMComplexBilinearDiagonal_phaseWeightTwo
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ) (z : ℂ) (x : X) :
    B (z • x) (z • x) = z ^ (2 : ℕ) * B x x := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Quarter-turn phase reverses every complex-bilinear diagonal value. -/
theorem d4HBAdjointQNMComplexBilinearDiagonal_I_smul
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ) (x : X) :
    B (Complex.I • x) (Complex.I • x) = -B x x := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I]
  simp

/-- A complex-bilinear diagonal that descends through the common phase of one source ray has zero
value. -/
theorem d4HBAdjointQNMComplexBilinearDiagonalRayLanding_value_eq_zero
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ) (x : X) (value : ℂ)
    (hlanding : d4HBAdjointQNMComplexBilinearDiagonalRayLanding B x value) :
    value = 0 := by
  rcases hlanding with ⟨hx, hIx⟩
  rw [d4HBAdjointQNMComplexBilinearDiagonal_I_smul, hx] at hIx
  exact neg_eq_self.mp hIx

/-- One fixed calibration is claimed to turn every complex-bilinear diagonal into a nonnegative
real energy. -/
def D4HBAdjointQNMComplexBilinearFixedPhasePositiveDiagonal
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (phase : ℂ) (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ) : Prop :=
  ∀ x : X, ∃ energy : ℝ, 0 ≤ energy ∧ phase * B x x = energy

/-- Fixed-phase positivity annihilates the diagonal of every complex-bilinear QNM pairing. -/
theorem d4HBAdjointQNMComplexBilinearFixedPhasePositiveDiagonal_eq_zero
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    {phase : ℂ} (hphase : phase ≠ 0)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ)
    (hpositive : D4HBAdjointQNMComplexBilinearFixedPhasePositiveDiagonal phase B) :
    ∀ x : X, B x x = 0 := by
  intro x
  obtain ⟨r, hr, hxr⟩ := hpositive x
  obtain ⟨s, hs, hIs⟩ := hpositive (Complex.I • x)
  rw [d4HBAdjointQNMComplexBilinearDiagonal_I_smul] at hIs
  have hrs : r + s = 0 := by
    have hz : (r : ℂ) + (s : ℂ) = 0 := by
      rw [← hxr, ← hIs]
      ring
    exact_mod_cast congrArg Complex.re hz
  have hr0 : r = 0 := by linarith
  have hproduct : phase * B x x = 0 := by simpa [hr0] using hxr
  exact (mul_eq_zero.mp hproduct).resolve_left hphase

/-- For a symmetric adjoint-QNM pairing, fixed-phase positivity annihilates the whole form, not
only its diagonal. -/
theorem d4HBAdjointQNMSymmetricComplexBilinearFixedPhasePositive_eq_zero
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    {phase : ℂ} (hphase : phase ≠ 0)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ)
    (hsymmetric : ∀ x y : X, B x y = B y x)
    (hpositive : D4HBAdjointQNMComplexBilinearFixedPhasePositiveDiagonal phase B) :
    B = 0 := by
  have hdiagonal :=
    d4HBAdjointQNMComplexBilinearFixedPhasePositiveDiagonal_eq_zero
      hphase B hpositive
  ext x y
  have hxy := hdiagonal (x + y)
  simp only [map_add, LinearMap.add_apply] at hxy
  rw [hdiagonal x, hdiagonal y, hsymmetric y x] at hxy
  simp only [zero_add, add_zero] at hxy
  have htwo : (2 : ℂ) * B x y = 0 := by
    linear_combination hxy
  simpa using (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Existential scalar model of a projectively descended complex-bilinear QNM diagonal. -/
def D4HBExistsAdjointQNMComplexBilinearDiagonalRayLanding (value : ℂ) : Prop :=
  ∃ (B : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) (x : ℂ),
    d4HBAdjointQNMComplexBilinearDiagonalRayLanding B x value

/-- Exact classification: a projectively descended complex-bilinear diagonal exists precisely for
the zero scalar. -/
theorem d4HBExistsAdjointQNMComplexBilinearDiagonalRayLanding_iff
    (value : ℂ) :
    D4HBExistsAdjointQNMComplexBilinearDiagonalRayLanding value ↔ value = 0 := by
  constructor
  · rintro ⟨B, x, hlanding⟩
    exact d4HBAdjointQNMComplexBilinearDiagonalRayLanding_value_eq_zero
      B x value hlanding
  · intro hvalue
    subst value
    refine ⟨0, 0, ?_⟩
    simp [d4HBAdjointQNMComplexBilinearDiagonalRayLanding]

/-- Projective diagonal landing for the complete target-independent HB full-cokernel orbit. -/
def D4HBAdjointQNMComplexBilinearFullCokernelOrbitLandingAt
    (n : ℕ) (q : XiZeroCopy) : Prop :=
  D4HBExistsAdjointQNMComplexBilinearDiagonalRayLanding
    (hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q)

/-- Fibrewise classification: the forbidden diagonal landing occurs exactly after the HB orbit has
already vanished on the critical wall. -/
theorem d4HBAdjointQNMComplexBilinearFullCokernelOrbitLandingAt_iff
    (n : ℕ) (q : XiZeroCopy) :
    D4HBAdjointQNMComplexBilinearFullCokernelOrbitLandingAt n q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [D4HBAdjointQNMComplexBilinearFullCokernelOrbitLandingAt,
    d4HBExistsAdjointQNMComplexBilinearDiagonalRayLanding_iff,
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_clockDefect,
    hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff]

/-- Global classification: universal complex-bilinear diagonal phase descent is RH itself, so it
cannot serve as an independent proof producer. -/
theorem forall_d4HBAdjointQNMComplexBilinearFullCokernelOrbitLandingAt_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      D4HBAdjointQNMComplexBilinearFullCokernelOrbitLandingAt n q) ↔
        RiemannHypothesis := by
  constructor
  · intro hlanding
    apply
      (forall_hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_rh n).mp
    intro q
    exact (d4HBExistsAdjointQNMComplexBilinearDiagonalRayLanding_iff _).mp
      (hlanding q)
  · intro hRH q
    apply (d4HBExistsAdjointQNMComplexBilinearDiagonalRayLanding_iff _).mpr
    exact
      (forall_hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_rh n).mpr
        hRH q

/-- Closed diagonal-route certificate.  Complex-bilinear phase descent is possible only at zero
and is globally RH; the complementary Hermitian/KMS diagonal class has the wrong polarity. -/
def D4HBAdjointQNMDiagonalPositivityRouteKilled : Prop :=
  (∀ value : ℂ,
      D4HBExistsAdjointQNMComplexBilinearDiagonalRayLanding value ↔ value = 0) ∧
    (∀ (n : ℕ) (q : XiZeroCopy),
      D4HBAdjointQNMComplexBilinearFullCokernelOrbitLandingAt n q ↔
        (q.1 : ℂ).re = 1 / 2) ∧
    (∀ n : ℕ,
      (∀ q : XiZeroCopy,
        D4HBAdjointQNMComplexBilinearFullCokernelOrbitLandingAt n q) ↔
          RiemannHypothesis) ∧
    D4HBFullCokernelFiniteKMSPassivityPolarityRouteKilled

/-- Premise-free Lean certificate killing every diagonal adjoint-QNM positivity route to the
missing HB full-cokernel sign. -/
theorem d4HBAdjointQNMDiagonalPositivityRouteKilled :
    D4HBAdjointQNMDiagonalPositivityRouteKilled := by
  exact ⟨d4HBExistsAdjointQNMComplexBilinearDiagonalRayLanding_iff,
    d4HBAdjointQNMComplexBilinearFullCokernelOrbitLandingAt_iff,
    forall_d4HBAdjointQNMComplexBilinearFullCokernelOrbitLandingAt_iff_rh,
    d4HBFullCokernelFiniteKMSPassivityPolarityRouteKilled⟩

end

end RHTower
