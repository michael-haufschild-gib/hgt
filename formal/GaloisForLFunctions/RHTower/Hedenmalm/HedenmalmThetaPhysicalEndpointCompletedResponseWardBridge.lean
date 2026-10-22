import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalHalfDensityDomainNoGo
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalWardContract
import GaloisForLFunctions.RHTower.XiCompletedBalancedResponseDirichletDecomposition

/-!
# Route P through the completed physical-endpoint response

The diagonal unit-double counterterm has wrong Route P polarity, but the corpus already supplies
its unique valuation-corrected off-diagonal completion.  Its finite balanced coupling has physical
marginal `log p / p`.

Rescale the literal Möbius half-density by `sqrt(p / log p)`.  The marginal energy of this rescaled
profile is exactly the Route P local polarization.  The generic pointed-coupling identity then
rewrites every Route P packet as the completed response pairing plus one half of its signed
prime-ratio Dirichlet energy.  This is a coefficient-exact weld to an existing non-diagonal source
object, not a fitted counterterm.

Uniform boundedness of that completed response budget is exactly the finite Route P Ward contract,
hence globally RH.  The still-open theorem is a source estimate for this explicit signed pairing
and Dirichlet term.
-/

open scoped BigOperators RealInnerProductSpace

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Physical-endpoint normalization forced by marginal `log p / p`. -/
def thetaPhysicalEndpointNormalizedHalfDensity
    (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  Real.sqrt ((p : ℝ) / Real.log (p : ℝ)) *
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q

/-- The physical endpoint marginal of the normalized profile is exactly Route P local energy. -/
theorem physicalPrimeEndpointWeight_mul_normalizedHalfDensity_sq
    (p : Nat.Primes) (q : XiZeroCopy) :
    physicalPrimeEndpointWeight p *
        thetaPhysicalEndpointNormalizedHalfDensity p q ^ (2 : ℕ) =
      thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ^ (2 : ℕ) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  have hratio : 0 ≤ (p : ℝ) / Real.log (p : ℝ) :=
    div_nonneg (by positivity) hlog.le
  rw [physicalPrimeEndpointWeight, thetaPhysicalEndpointNormalizedHalfDensity,
    mul_pow, Real.sq_sqrt hratio]
  field_simp [hlog.ne']

/-- Quadratic pairing of the unique corrected completed endpoint coupling with the normalized
physical Route P profile. -/
def thetaPhysicalEndpointCompletedResponsePairing
    (P : Finset Nat.Primes) (q : XiZeroCopy) : ℝ :=
  ∑ p ∈ P, ∑ r ∈ P,
    xiPhysicalEndpointCompletedBalancedCoupling P p r *
      thetaPhysicalEndpointNormalizedHalfDensity p q *
      thetaPhysicalEndpointNormalizedHalfDensity r q

/-- Signed prime-ratio Dirichlet energy of the same completed response and Route P profile. -/
def thetaPhysicalEndpointCompletedResponseDirichletEnergy
    (P : Finset Nat.Primes) (q : XiZeroCopy) : ℝ :=
  ∑ p ∈ P, ∑ r ∈ P,
    xiPhysicalEndpointCompletedBalancedCoupling P p r *
      (thetaPhysicalEndpointNormalizedHalfDensity p q -
        thetaPhysicalEndpointNormalizedHalfDensity r q) ^ (2 : ℕ)

/-- Forced diagonal completion disappears from the Dirichlet term; only actual off-diagonal
completed source response remains. -/
theorem thetaPhysicalEndpointCompletedResponseDirichletEnergy_eq_pairResponse
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointCompletedResponseDirichletEnergy P q =
      ∑ p ∈ P, ∑ r ∈ P,
        xiPhysicalEndpointCompletedPairResponse p r *
          (thetaPhysicalEndpointNormalizedHalfDensity p q -
            thetaPhysicalEndpointNormalizedHalfDensity r q) ^ (2 : ℕ) := by
  rw [thetaPhysicalEndpointCompletedResponseDirichletEnergy]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hpr : p = r
  · subst r
    simp
  · rw [xiPhysicalEndpointCompletedBalancedCoupling, if_neg hpr]

/-- Source-only kernel form of the Route P signed Dirichlet term. -/
theorem thetaPhysicalEndpointCompletedResponseDirichletEnergy_eq_kernel
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointCompletedResponseDirichletEnergy P q =
      ∑ p ∈ P, ∑ r ∈ P,
        physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight r *
          xiPhysicalEndpointCompletedPrimeRatioRealKernel p r *
            (thetaPhysicalEndpointNormalizedHalfDensity p q -
              thetaPhysicalEndpointNormalizedHalfDensity r q) ^ (2 : ℕ) := by
  rw [thetaPhysicalEndpointCompletedResponseDirichletEnergy_eq_pairResponse]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro r hr
  rw [xiPhysicalEndpointCompletedPairResponse]

/-- **Completed-response Route P decomposition.**  Every physical Route P packet is exactly the
existing corrected completed response pairing plus one half of its signed off-diagonal energy. -/
theorem thetaPhysicalEndpointCompletedResponsePairing_eq_packetEnergy_sub_half_dirichlet
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointCompletedResponsePairing P q =
      thetaMobiusPrimeNormalProfilePacketEnergy q P -
        (1 / 2 : ℝ) * thetaPhysicalEndpointCompletedResponseDirichletEnergy P q := by
  have hgeneric := finite_symmetric_coupling_inner_eq_marginal_sub_half_dirichlet
    P (xiPhysicalEndpointCompletedBalancedCoupling P)
    (fun p : Nat.Primes => physicalPrimeEndpointWeight p)
    (fun p : Nat.Primes => thetaPhysicalEndpointNormalizedHalfDensity p q)
    (fun p _hp r _hr => xiPhysicalEndpointCompletedBalancedCoupling_symm P p r)
    (sum_xiPhysicalEndpointCompletedBalancedCoupling P)
  rw [show (∑ p ∈ P, physicalPrimeEndpointWeight p *
      ‖thetaPhysicalEndpointNormalizedHalfDensity p q‖ ^ (2 : ℕ)) =
      thetaMobiusPrimeNormalProfilePacketEnergy q P by
    rw [thetaMobiusPrimeNormalProfilePacketEnergy]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Real.norm_eq_abs, sq_abs,
      physicalPrimeEndpointWeight_mul_normalizedHalfDensity_sq,
      thetaMobiusPrimeNormalProfileHalfDensityAmplitude_sq]] at hgeneric
  simpa [thetaPhysicalEndpointCompletedResponsePairing,
    thetaPhysicalEndpointCompletedResponseDirichletEnergy,
    real_inner_comm, Real.norm_eq_abs, sq_abs,
    mul_comm, mul_left_comm, mul_assoc] using hgeneric

/-- Rearranged Ward identity: completed response budget is exactly Route P packet energy. -/
theorem thetaMobiusPrimeNormalProfilePacketEnergy_eq_completedResponseBudget
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    thetaMobiusPrimeNormalProfilePacketEnergy q P =
      thetaPhysicalEndpointCompletedResponsePairing P q +
        (1 / 2 : ℝ) * thetaPhysicalEndpointCompletedResponseDirichletEnergy P q := by
  rw [thetaPhysicalEndpointCompletedResponsePairing_eq_packetEnergy_sub_half_dirichlet]
  ring

/-- Uniform completed off-diagonal source-response budget at one divisor copy. -/
def ThetaPhysicalEndpointCompletedResponseWardBoundAt (q : XiZeroCopy) : Prop :=
  ∃ C : ℝ, ∀ P : Finset Nat.Primes,
    thetaPhysicalEndpointCompletedResponsePairing P q +
        (1 / 2 : ℝ) * thetaPhysicalEndpointCompletedResponseDirichletEnergy P q ≤ C

/-- The completed non-diagonal response budget is exactly the physical finite Route P contract. -/
theorem thetaPhysicalEndpointCompletedResponseWardBoundAt_iff_mobiusWardBoundAt
    (q : XiZeroCopy) :
    ThetaPhysicalEndpointCompletedResponseWardBoundAt q ↔
      ThetaMobiusPrimeNormalWardBoundAt q := by
  constructor <;> rintro ⟨C, hC⟩ <;> refine ⟨C, fun P => ?_⟩
  · rw [thetaMobiusPrimeNormalProfilePacketEnergy_eq_completedResponseBudget]
    exact hC P
  · rw [← thetaMobiusPrimeNormalProfilePacketEnergy_eq_completedResponseBudget]
    exact hC P

/-- Pointwise completed response Ward bound is exactly positivity of the Route P squared node. -/
theorem thetaPhysicalEndpointCompletedResponseWardBoundAt_iff_reciprocalEigenvalue_sq_positiveReal
    (q : XiZeroCopy) :
    ThetaPhysicalEndpointCompletedResponseWardBoundAt q ↔
      ∃ r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ (2 : ℕ) = (r : ℂ) := by
  rw [thetaPhysicalEndpointCompletedResponseWardBoundAt_iff_mobiusWardBoundAt,
    thetaMobiusPrimeNormalWardBoundAt_iff_reciprocalEigenvalue_sq_positiveReal]

/-- Global completed physical-endpoint response Ward contract. -/
def ThetaPhysicalEndpointCompletedResponseWardBound : Prop :=
  ∀ q : XiZeroCopy, ThetaPhysicalEndpointCompletedResponseWardBoundAt q

/-- Global uniform control of the coefficient-exact completed response budget is equivalent to RH. -/
theorem thetaPhysicalEndpointCompletedResponseWardBound_iff_riemannHypothesis :
    ThetaPhysicalEndpointCompletedResponseWardBound ↔ RiemannHypothesis := by
  rw [show ThetaPhysicalEndpointCompletedResponseWardBound =
      ThetaMobiusPrimeNormalWardBound by
    apply propext
    exact forall_congr' thetaPhysicalEndpointCompletedResponseWardBoundAt_iff_mobiusWardBoundAt]
  exact thetaMobiusPrimeNormalWardBound_iff_riemannHypothesis

end

end RHTower.HedenmalmThetaSource
