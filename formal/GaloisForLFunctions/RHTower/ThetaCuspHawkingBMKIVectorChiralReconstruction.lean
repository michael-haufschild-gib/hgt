import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMKIScalarMetricReconstruction

/-!
# Vector KI reconstruction and the scalar--vector chiral carrier

For source-free vector perturbations, Kodama--Ishibashi Eq. (117) gives

`epsilon^{ab} D_b OmegaTilde = r^(n-1) F^a`.

In four dimensions `n=2`, and their Schrödinger master is
`Phi = r^-1 OmegaTilde`.  On the massless topological black hole, with time dependence
`exp(-i omega t)`, orientation `epsilon^{tr}=1`, `rho=r^-1`, and `z=1-rho^(2 : ℕ)`, the exact
reconstruction is

`F^t = rho Phi + 2 rho^(3 : ℕ) Phi'`, `F^r = i omega Phi`,

`rho F_t = -z Phi - 2 rho^(2 : ℕ) z Phi'`, `z F_r = i omega rho^(2 : ℕ) Phi`.

The last two are the polynomially regularized covariant invariants and remain meaningful at both
coordinate edges without inverse-coordinate assumptions.

Combining the vector time invariant with the scalar KI invariant from the preceding module gives

`rho^(2 : ℕ) Ztilde_scalar - rho F_t_vector = Phi`

whenever both sectors carry the same master jet.  This is an exact scalar--vector cancellation:
all first-radial-jet terms disappear and the master field is recovered with unit coefficient.  A
more general mismatch law identifies the only obstruction as the difference of the two first
jets.  The result supplies a canonical gauge-invariant chiral carrier for the physical Xi mode.
The remaining hard step is its harmonic/light-cone lift to the Plebanski scalar.

`[NEW CONSEQUENCE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [CHIRAL CARRIER]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Source-free vector-type KI orbit, including polynomially regularized covariant components. -/
structure D4KIVectorGaugeInvariantOrbit where
  FtContravariant : ℂ
  FrContravariant : ℂ
  rhoFtCovariant : ℂ
  zFrCovariant : ℂ

/-- Value and first three BM derivatives.  A third derivative is temporarily needed when the
reconstructed scalar/vector metric components are differentiated twice. -/
structure D4ComplexRadialThreeJet where
  value : ℂ
  first : ℂ
  second : ℂ
  third : ℂ

/-- Forget the top derivative of a BM three-jet. -/
def D4ComplexRadialThreeJet.toTwoJet
    (J : D4ComplexRadialThreeJet) : D4ComplexRadialTwoJet where
  value := J.value
  first := J.first
  second := J.second

/-- Exact four-dimensional vector KI reconstruction from a BM master two-jet. -/
def d4KIVectorGaugeInvariantOrbitOfBMMaster
    (rho omega : ℂ) (J : D4ComplexRadialTwoJet) : D4KIVectorGaugeInvariantOrbit :=
  { FtContravariant := rho * J.value + 2 * rho ^ (3 : ℕ) * J.first
    FrContravariant := Complex.I * omega * J.value
    rhoFtCovariant :=
      -(1 - rho ^ (2 : ℕ)) * J.value - 2 * rho ^ (2 : ℕ) * (1 - rho ^ (2 : ℕ)) * J.first
    zFrCovariant := Complex.I * omega * rho ^ (2 : ℕ) * J.value }

/-- The regularized covariant radial component is the metric-lowered contravariant component with
the blackening denominator cleared. -/
theorem d4KIVectorGaugeInvariantOrbitOfBMMaster_zFr_eq
    (rho omega : ℂ) (J : D4ComplexRadialTwoJet) :
    (d4KIVectorGaugeInvariantOrbitOfBMMaster rho omega J).zFrCovariant =
      rho ^ (2 : ℕ) *
        (d4KIVectorGaugeInvariantOrbitOfBMMaster rho omega J).FrContravariant := by
  simp [d4KIVectorGaugeInvariantOrbitOfBMMaster]
  ring

/-- Scalar--vector chiral master carrier formed from gauge-invariant reconstructed components. -/
def d4KIScalarVectorChiralCarrier
    (rho zInv omega kSq : ℂ)
    (scalarJet vectorJet : D4ComplexRadialTwoJet) : ℂ :=
  rho ^ (2 : ℕ) *
      (d4KIScalarGaugeInvariantOrbitOfBMMaster
        rho zInv omega kSq scalarJet).Ztilde -
    (d4KIVectorGaugeInvariantOrbitOfBMMaster rho omega vectorJet).rhoFtCovariant

/-- Exact mismatch law.  Apart from the weighted values, the only obstruction to scalar--vector
chiral matching is the difference of their BM first jets. -/
theorem d4KIScalarVectorChiralCarrier_eq_mismatch
    (rho zInv omega kSq : ℂ)
    (scalarJet vectorJet : D4ComplexRadialTwoJet) :
    d4KIScalarVectorChiralCarrier rho zInv omega kSq scalarJet vectorJet =
      rho ^ (2 : ℕ) * scalarJet.value + (1 - rho ^ (2 : ℕ)) * vectorJet.value +
        2 * rho ^ (2 : ℕ) * (1 - rho ^ (2 : ℕ)) * (vectorJet.first - scalarJet.first) := by
  simp [d4KIScalarVectorChiralCarrier,
    d4KIScalarGaugeInvariantOrbitOfBMMaster,
    d4KIScalarMasslessTopologicalZtilde,
    d4KIVectorGaugeInvariantOrbitOfBMMaster]
  ring

/-- Unit-coefficient chiral recovery: matched scalar and vector KI sectors reconstruct their
common master field exactly, without a chart or harmonic nonvanishing premise. -/
theorem d4KIScalarVectorChiralCarrier_matched_eq_value
    (rho zInv omega kSq : ℂ) (J : D4ComplexRadialTwoJet) :
    d4KIScalarVectorChiralCarrier rho zInv omega kSq J J = J.value := by
  rw [d4KIScalarVectorChiralCarrier_eq_mismatch]
  ring

/-- First three BM jets of the reconstructed scalar invariant `Ztilde = Phi-2z Phi'`. -/
def d4KIScalarZtildeThreeJetOfBMMaster
    (z : ℂ) (J : D4ComplexRadialThreeJet) : D4ComplexRadialThreeJet where
  value := J.value - 2 * z * J.first
  first := -J.first - 2 * z * J.second
  second := -3 * J.second - 2 * z * J.third
  third := 0

/-- First three BM jets of the regularized vector invariant
`rho F_t = -z Phi-2(1-z)z Phi'`. -/
def d4KIVectorRhoFtThreeJetOfBMMaster
    (z : ℂ) (J : D4ComplexRadialThreeJet) : D4ComplexRadialThreeJet where
  value := -z * J.value - 2 * (1 - z) * z * J.first
  first := -J.value + (3 * z - 2) * J.first -
    2 * z * (1 - z) * J.second
  second := 2 * J.first + (7 * z - 4) * J.second -
    2 * z * (1 - z) * J.third
  third := 0

/-- BM two-jet of the scalar--vector chiral carrier, obtained by differentiating the reconstructed
metric components rather than inserting the master field. -/
def d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet
    (z : ℂ) (J : D4ComplexRadialThreeJet) : D4ComplexRadialTwoJet :=
  let S := d4KIScalarZtildeThreeJetOfBMMaster z J
  let V := d4KIVectorRhoFtThreeJetOfBMMaster z J
  { value := (1 - z) * S.value - V.value
    first := -S.value + (1 - z) * S.first - V.first
    second := -2 * S.first + (1 - z) * S.second - V.second }

/-- Full jet-level chiral cancellation.  Although separate metric components require the third
BM derivative, it cancels from the chiral carrier, which recovers the master value and its first
two derivatives exactly. -/
theorem d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet_eq_masterTwoJet
    (z : ℂ) (J : D4ComplexRadialThreeJet) :
    d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet z J = J.toTwoJet := by
  rcases J with ⟨value, first, second, third⟩
  simp only [d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet,
    d4KIScalarZtildeThreeJetOfBMMaster,
    d4KIVectorRhoFtThreeJetOfBMMaster,
    D4ComplexRadialThreeJet.toTwoJet]
  congr 1 <;> ring

/-- The exact Poincare-pulled Plebanski two-jet constructed from the reconstructed KI metric
components equals the direct Poincare pullback of the BM master two-jet. -/
theorem d4PoincareRadialTwoJetOfKIScalarVectorChiral_eq_master
    (rho sigmaInv : ℂ) (J : D4ComplexRadialThreeJet) :
    d4PoincareRadialTwoJetOfBMInv rho sigmaInv
        (d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet (1 - rho ^ (2 : ℕ)) J) =
      d4PoincareRadialTwoJetOfBMInv rho sigmaInv J.toTwoJet := by
  rw [d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet_eq_masterTwoJet]

/-- Consequently the full deformed two-leg AdS self-dual vertex is unchanged when each BM master
two-jet is supplied through its independently reconstructed scalar--vector KI metric carrier. -/
theorem ads4SelfDualDeformedVertexOnKIScalarVectorChiralTwoJets_eq_master
    (rho sigmaInv xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialThreeJet) :
    ads4SelfDualDeformedVertexOnTwoJets (rho⁻¹ * sigmaInv)
        xBracket q1 q2 q1w q2w
        (d4PoincareRadialTwoJetOfBMInv rho sigmaInv
          (d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet (1 - rho ^ (2 : ℕ)) P))
        (d4PoincareRadialTwoJetOfBMInv rho sigmaInv
          (d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet (1 - rho ^ (2 : ℕ)) Q)) =
      ads4SelfDualDeformedVertexOnTwoJets (rho⁻¹ * sigmaInv)
        xBracket q1 q2 q1w q2w
        (d4PoincareRadialTwoJetOfBMInv rho sigmaInv P.toTwoJet)
        (d4PoincareRadialTwoJetOfBMInv rho sigmaInv Q.toTwoJet) := by
  rw [d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet_eq_masterTwoJet,
    d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet_eq_masterTwoJet]

/-- Actual Xi-fibre chiral carrier. -/
def d4KIXiScalarVectorChiralCarrier
    (rho zInv omega : ℂ) (n k : ℕ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  d4KIScalarVectorChiralCarrier rho zInv omega
    (thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue (xiSpectralPoint q))
    (d4BMXiMixedHorizonExactMonodromyTwoJet n k q z)
    (d4BMXiMixedHorizonExactMonodromyTwoJet n k q z)

/-- The physical Xi chiral carrier is exactly the corpus's nonzero-monodromy radial mode, with no
fitted normalization and no auxiliary premise. -/
theorem d4KIXiScalarVectorChiralCarrier_eq_exactMonodromyMode
    (rho zInv omega : ℂ) (n k : ℕ) (q : XiZeroCopy) (z : ℂ) :
    d4KIXiScalarVectorChiralCarrier rho zInv omega n k q z =
      d4BMXiMixedHorizonExactMonodromyMode n k q z := by
  exact d4KIScalarVectorChiralCarrier_matched_eq_value
    rho zInv omega
      (thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue (xiSpectralPoint q))
      (d4BMXiMixedHorizonExactMonodromyTwoJet n k q z)

/-- Arbitrary third-jet extension of the actual Xi master two-jet.  The chiral cancellation below
is independent of the extension value, so no unproved third-derivative formula is introduced. -/
def d4BMXiMixedHorizonExactMonodromyThreeJetExtension
    (n k : ℕ) (q : XiZeroCopy) (z third : ℂ) : D4ComplexRadialThreeJet where
  value := d4BMXiMixedHorizonExactMonodromyMode n k q z
  first := d4BMXiMixedHorizonExactMonodromyModeDerivative n k q z
  second := d4BMXiMixedHorizonExactMonodromyModeSecondDerivative n k q z
  third := third

/-- Every third-jet extension of the actual Xi mode gives the same reconstructed chiral two-jet:
the exact corpus value, first derivative, and second derivative. -/
theorem d4KIXiScalarVectorChiralCarrierTwoJet_extension_independent
    (n k : ℕ) (q : XiZeroCopy) (z third : ℂ) :
    d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet z
        (d4BMXiMixedHorizonExactMonodromyThreeJetExtension n k q z third) =
      d4BMXiMixedHorizonExactMonodromyTwoJet n k q z := by
  rw [d4KIScalarVectorChiralCarrierTwoJetOfBMThreeJet_eq_masterTwoJet]
  rfl

end

end RHTower
