import GaloisForLFunctions.RHTower.ThetaCuspHawkingSelfDualEinsteinDilationCarrier

/-!
# HB self-dual Plebanski local-Jacobi no-go

The surviving HB causal-cut core asks the radiative `++` quadratic-response jump to vanish.
Self-dual gravity suggests a tempting source-local mechanism: cyclically combine the three
Plebanski exchange channels and invoke the Jacobi identity of the underlying kinematic bracket.

The corpus's literal AdS4 plane-wave vertex gives an exact obstruction on the physical
same-transverse-charge sector.  Curvature cancels there and each channel is

`V(p,q;h) = h^2 (p-q)^2 / 2`.

Consequently the complete local cyclic vertex is the translation-invariant graph-Laplacian
energy

`h^2 ((p-q)^2 + (q-r)^2 + (r-p)^2) / 2`.

For real physical affine momenta and nonzero charge this vanishes exactly on the diagonal
`p=q=r`.  Double-copy squaring therefore converts the alternating kinematic Jacobi mechanism
into positive rigidity; neither flat nor AdS curvature can make a nontrivial same-charge packet
locally dark.

This kills the source-local Jacobi branch of HB.  It does not kill a cancellation using the
complete retarded-minus-advanced propagator.  The sharp survivor must obtain an orientation or
phase from the nonlocal causal Green discontinuity (including threshold/continuum data) before
the left projection.

`[PROVED HERE] [LEAN-PROVED] [HB] [ROUTE KILL] [NOVELTY AUDITED 2026-08-31]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Real graph-Laplacian energy exposed by the cyclic same-charge Plebanski vertex. -/
def d4HBSelfDualSameChargeCyclicVertexEnergy
    (p q r h : ℝ) : ℝ :=
  (h ^ 2 / 2) * ((p - q) ^ 2 + (q - r) ^ 2 + (r - p) ^ 2)

/-- Three local self-dual gravity channels on one physical transverse-charge fibre. -/
def d4HBSelfDualSameChargeCyclicVertex
    (curvature : ℂ) (p q r h : ℝ) : ℂ :=
  ads4SelfDualPlaneWaveVertex curvature p h q h +
    ads4SelfDualPlaneWaveVertex curvature q h r h +
    ads4SelfDualPlaneWaveVertex curvature r h p h

/-- Exact positive survivor: the cyclic local gravity vertex is the same graph energy for every
AdS curvature. -/
theorem d4HBSelfDualSameChargeCyclicVertex_eq_energy
    (curvature : ℂ) (p q r h : ℝ) :
    d4HBSelfDualSameChargeCyclicVertex curvature p q r h =
      d4HBSelfDualSameChargeCyclicVertexEnergy p q r h := by
  rw [d4HBSelfDualSameChargeCyclicVertex,
    ads4SelfDualPlaneWaveVertex_sameTransverseCharge,
    ads4SelfDualPlaneWaveVertex_sameTransverseCharge,
    ads4SelfDualPlaneWaveVertex_sameTransverseCharge]
  simp only [d4HBSelfDualSameChargeCyclicVertexEnergy]
  push_cast
  ring

/-- Sharp real zero-set classification of the exposed graph-Laplacian energy. -/
theorem d4HBSelfDualSameChargeCyclicVertexEnergy_eq_zero_iff
    (p q r h : ℝ) (hh : h ≠ 0) :
    d4HBSelfDualSameChargeCyclicVertexEnergy p q r h = 0 ↔
      p = q ∧ q = r := by
  have hh2 : 0 < h ^ 2 := sq_pos_of_ne_zero hh
  constructor
  · intro hzero
    have hsum : (p - q) ^ 2 + (q - r) ^ 2 + (r - p) ^ 2 = 0 := by
      rw [d4HBSelfDualSameChargeCyclicVertexEnergy] at hzero
      nlinarith
    have hpq : (p - q) ^ 2 = 0 := by
      nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (r - p)]
    have hqr : (q - r) ^ 2 = 0 := by
      nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (r - p)]
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    simp [d4HBSelfDualSameChargeCyclicVertexEnergy]

/-- The literal complex Plebanski cyclic vertex is dark only for a momentum-diagonal packet. -/
theorem d4HBSelfDualSameChargeCyclicVertex_eq_zero_iff
    (curvature : ℂ) (p q r h : ℝ) (hh : h ≠ 0) :
    d4HBSelfDualSameChargeCyclicVertex curvature p q r h = 0 ↔
      p = q ∧ q = r := by
  rw [d4HBSelfDualSameChargeCyclicVertex_eq_energy]
  exact_mod_cast d4HBSelfDualSameChargeCyclicVertexEnergy_eq_zero_iff p q r h hh

/-- Closed proposition for the local-Jacobi HB route class. -/
def D4HBSelfDualSameChargeLocalJacobiCancellationRouteKilled : Prop :=
  ∀ (curvature : ℂ) (p q r h : ℝ), h ≠ 0 →
    (d4HBSelfDualSameChargeCyclicVertex curvature p q r h = 0 ↔
      p = q ∧ q = r)

/-- Premise-free certificate: no nontrivial real same-charge Plebanski packet is extinguished by
local cyclic/Jacobi assembly. -/
theorem d4HBSelfDualSameChargeLocalJacobiCancellationRouteKilled :
    D4HBSelfDualSameChargeLocalJacobiCancellationRouteKilled := by
  intro curvature p q r h hh
  exact d4HBSelfDualSameChargeCyclicVertex_eq_zero_iff curvature p q r h hh

end

end RHTower
